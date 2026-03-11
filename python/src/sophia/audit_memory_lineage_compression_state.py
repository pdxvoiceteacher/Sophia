from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

COHERENCE_MEMORY_TRACE_PATH = BRIDGE_DIR / "coherence_memory_trace.json"
PHASE_LINEAGE_REGISTRY_PATH = BRIDGE_DIR / "phase_lineage_registry.json"

MEMORY_COMPRESSION_AUDIT_OUT = BRIDGE_DIR / "memory_compression_audit.json"
LINEAGE_INTEGRITY_REPORT_OUT = BRIDGE_DIR / "lineage_integrity_report.json"
COMPRESSION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "compression_recommendations.json"

MEMORY_COMPRESSION_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "memory_compression_audit_v1.schema.json"
LINEAGE_INTEGRITY_REPORT_SCHEMA_PATH = SCHEMA_DIR / "lineage_integrity_report_v1.schema.json"
COMPRESSION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "compression_recommendations_v1.schema.json"

TIERS = {"hot", "warm", "cold"}


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _phase_default_tier(phase_id: str) -> str:
    if phase_id >= "BL":
        return "hot"
    if phase_id >= "BG":
        return "warm"
    return "cold"


def _expected_hashes(phase: dict[str, Any]) -> list[str]:
    phase_id = str(phase.get("phaseId", ""))
    downstream = [str(x) for x in phase.get("downstreamArtifacts", []) if isinstance(x, str)]
    statuses = [str(x) for x in phase.get("keyStatuses", []) if isinstance(x, str)]
    seed = f"{phase_id}|{','.join(downstream)}|{','.join(statuses)}"
    digest = hashlib.sha256(seed.encode()).hexdigest()
    return [f"sha256:{digest[:16]}", f"sha256:{digest[16:32]}"]


def _validate_trace_hashes(trace_rows: list[dict[str, Any]], phase_index: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    mismatches: list[dict[str, Any]] = []
    for row in trace_rows:
        phase_id = str(row.get("phaseId", ""))
        expected_phase = phase_index.get(phase_id)
        if expected_phase is None:
            mismatches.append({"memoryId": phase_id, "issue": "phase-not-found-in-lineage", "expected": [], "actual": row.get("artifactLineageHashes", [])})
            continue
        expected = _expected_hashes(expected_phase)
        actual = [str(x) for x in row.get("artifactLineageHashes", []) if isinstance(x, str)]
        if actual != expected:
            mismatches.append({"memoryId": phase_id, "issue": "lineage-hash-mismatch", "expected": expected, "actual": actual})
    return sorted(mismatches, key=lambda x: (x.get("memoryId", ""), x.get("issue", "")))


def _build_memory_compression_audit(trace_rows: list[dict[str, Any]], hash_mismatches: list[dict[str, Any]]) -> dict[str, Any]:
    counts = {"hot": 0, "warm": 0, "cold": 0}
    issues: list[str] = []

    for row in trace_rows:
        phase_id = str(row.get("phaseId", ""))
        tier = str(row.get("memoryTier") or _phase_default_tier(phase_id))
        if tier not in TIERS:
            issues.append(f"{phase_id}:invalid-tier:{tier}")
            tier = "warm"
        counts[tier] += 1

    recommendations: list[str] = []
    if hash_mismatches:
        recommendations.append("Keep-open: review lineage hash mismatches before any memory-tier changes.")
    if issues:
        recommendations.append("Plurality-protect: normalize invalid memory tiers to bounded hot/warm/cold labels with human review.")
    if not recommendations:
        recommendations.append("Background coherence is legible; retain current tiers with periodic bounded review.")
    recommendations.append("No automatic promotion, automatic deletion, governance transfer, or canon closure is authorized by this report.")

    return {
        "hotMemoryUsage": counts["hot"],
        "warmMemoryUsage": counts["warm"],
        "coldMemoryUsage": counts["cold"],
        "totalMemoryEntries": len(trace_rows),
        "invariantHashChecks": hash_mismatches,
        "recommendations": recommendations,
    }


def _build_lineage_integrity_report(registry: dict[str, Any]) -> dict[str, Any]:
    phases = [p for p in registry.get("phases", []) if isinstance(p, dict)]
    downstream = {str(a) for p in phases for a in p.get("downstreamArtifacts", []) if isinstance(a, str)}

    missing_links: list[str] = []
    for p in phases:
        for upstream in [str(a) for a in p.get("upstreamArtifacts", []) if isinstance(a, str)]:
            upstream_path = REPO_ROOT / upstream
            if upstream not in downstream and not upstream_path.exists():
                missing_links.append(upstream)

    missing_links = sorted(set(missing_links))
    issues: list[str] = []
    if missing_links:
        issues.append("missing-upstream-artifacts")

    recommendations = [
        "Keep-open: unresolved lineage links require human follow-up before downstream compression decisions.",
        "No governance transfer, settlement authorization, or centralized authority claim is implied.",
    ]
    if not missing_links:
        recommendations.insert(0, "Lineage chains are complete for available artifacts; continue bounded periodic verification.")

    return {
        "lineageComplete": not missing_links,
        "missingLinks": missing_links,
        "issuesDetected": sorted(set(issues)),
        "recommendations": recommendations,
    }


def _build_compression_recommendations(trace_rows: list[dict[str, Any]], hash_mismatches: list[dict[str, Any]]) -> dict[str, Any]:
    mismatch_ids = {str(m.get("memoryId")) for m in hash_mismatches}
    actions: list[dict[str, str]] = []

    for row in sorted(trace_rows, key=lambda r: str(r.get("phaseId", ""))):
        phase_id = str(row.get("phaseId", "unknown"))
        tier = str(row.get("memoryTier") or _phase_default_tier(phase_id))
        if phase_id in mismatch_ids:
            actions.append({"memoryId": phase_id, "recommendedTier": "hot", "reason": "lineage mismatch present; keep-open and re-verify before compression."})
            continue
        if tier not in TIERS:
            actions.append({"memoryId": phase_id, "recommendedTier": "warm", "reason": "invalid tier label normalized for bounded stewardship review."})
            continue
        if tier == "hot" and phase_id < "BL":
            actions.append({"memoryId": phase_id, "recommendedTier": "warm", "reason": "older phase can be compressed one step while preserving queryability."})
        elif tier == "warm" and phase_id < "BG":
            actions.append({"memoryId": phase_id, "recommendedTier": "cold", "reason": "historical phase suitable for archival compression (non-destructive)."})

    if not actions:
        actions.append({"memoryId": "none", "recommendedTier": "watch", "reason": "No tier changes recommended; retain current bounded memory layout."})

    return {"actionItems": actions}


def build_outputs() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    trace_doc = _load_json(COHERENCE_MEMORY_TRACE_PATH)
    registry_doc = _load_json(PHASE_LINEAGE_REGISTRY_PATH)

    trace_rows = [r for r in trace_doc.get("trace", []) if isinstance(r, dict)]
    phases = [p for p in registry_doc.get("phases", []) if isinstance(p, dict)]
    phase_index = {str(p.get("phaseId")): p for p in phases if isinstance(p.get("phaseId"), str)}

    hash_mismatches = _validate_trace_hashes(trace_rows, phase_index)
    memory_audit = _build_memory_compression_audit(trace_rows, hash_mismatches)
    lineage_report = _build_lineage_integrity_report(registry_doc)
    compression_rec = _build_compression_recommendations(trace_rows, hash_mismatches)

    Draft202012Validator(_load_json(MEMORY_COMPRESSION_AUDIT_SCHEMA_PATH)).validate(memory_audit)
    Draft202012Validator(_load_json(LINEAGE_INTEGRITY_REPORT_SCHEMA_PATH)).validate(lineage_report)
    Draft202012Validator(_load_json(COMPRESSION_RECOMMENDATIONS_SCHEMA_PATH)).validate(compression_rec)
    return memory_audit, lineage_report, compression_rec


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit LRQ compressed memory and lineage integrity")
    parser.parse_args(argv)

    memory_audit, lineage_report, compression_rec = build_outputs()
    MEMORY_COMPRESSION_AUDIT_OUT.write_text(json.dumps(memory_audit, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    LINEAGE_INTEGRITY_REPORT_OUT.write_text(json.dumps(lineage_report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    COMPRESSION_RECOMMENDATIONS_OUT.write_text(json.dumps(compression_rec, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {MEMORY_COMPRESSION_AUDIT_OUT}")
    print(f"Wrote {LINEAGE_INTEGRITY_REPORT_OUT}")
    print(f"Wrote {COMPRESSION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
