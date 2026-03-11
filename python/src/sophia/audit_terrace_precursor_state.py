from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

TERRACE_PRECURSOR_MAP_PATH = BRIDGE_DIR / "terrace_precursor_map.json"
TERRACE_PRECURSOR_AUDIT_OUT = BRIDGE_DIR / "terrace_precursor_audit.json"
TERRACE_PRECURSOR_RECOMMENDATIONS_OUT = BRIDGE_DIR / "terrace_precursor_recommendations.json"

TERRACE_PRECURSOR_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "terrace_precursor_audit_v1.schema.json"
TERRACE_PRECURSOR_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "terrace_precursor_recommendations_v1.schema.json"

THRESH_HIGH_THETA = 0.78
MIN_CONTINUITY = 0.55
MIN_PLURALITY = 0.60


class TerracePrecursorInputError(RuntimeError):
    pass


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _save_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _clamp01(value: Any, default: float = 0.0) -> float:
    if not isinstance(value, (int, float)):
        return default
    return max(0.0, min(1.0, float(value)))


def _parse_targets(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows = payload.get("targets")
    return [row for row in rows if isinstance(row, dict)] if isinstance(rows, list) else []


def _target_action(severity: str) -> str:
    return "docket" if severity == "warn" else "watch"


def _has_sign_mismatch(delta_s: float, lambda_value: float) -> bool:
    # Expected regimes are either both supportive (>= 0) or both destabilizing (< 0).
    return (delta_s >= 0.0) != (lambda_value >= 0.0)


def evaluate_target(target: dict[str, Any]) -> list[dict[str, Any]]:
    target_id = str(target.get("targetId") or "target:unknown")
    theta = _clamp01(target.get("terracePrecursorScore"), 0.0)
    memory_continuity = _clamp01(target.get("memoryContinuity"), 0.0)
    plurality_retention = _clamp01(target.get("pluralityRetention"), 0.0)
    delta_s = float(target.get("deltaS", 0.0)) if isinstance(target.get("deltaS"), (int, float)) else 0.0
    lambda_value = float(target.get("lambda", 0.0)) if isinstance(target.get("lambda"), (int, float)) else 0.0

    findings: list[dict[str, Any]] = []

    if theta >= THRESH_HIGH_THETA and (memory_continuity < MIN_CONTINUITY or plurality_retention < MIN_PLURALITY):
        findings.append(
            {
                "targetId": target_id,
                "severity": "warn",
                "type": "false-terrace-risk",
                "message": "High terrace precursor score with weak continuity/plurality suggests premature convergence risk.",
                "targetPublisherAction": "docket",
                "data": {
                    "Theta": round(theta, 6),
                    "memoryContinuity": round(memory_continuity, 6),
                    "pluralityRetention": round(plurality_retention, 6),
                },
            }
        )

    if _has_sign_mismatch(delta_s, lambda_value):
        findings.append(
            {
                "targetId": target_id,
                "severity": "warn",
                "type": "regime-sign-mismatch",
                "message": "ΔS and Λ signs diverge from expected aligned regimes; keep-open review before advancing terrace claims.",
                "targetPublisherAction": "docket",
                "data": {"deltaS": round(delta_s, 6), "lambda": round(lambda_value, 6)},
            }
        )

    if theta >= 0.70 and (memory_continuity < 0.65 or plurality_retention < 0.65):
        findings.append(
            {
                "targetId": target_id,
                "severity": "info",
                "type": "terrace-not-ready",
                "message": "Terrace precursor remains unstable under bounded compression checks; continue watch-state instrumentation.",
                "targetPublisherAction": "watch",
                "data": {
                    "Theta": round(theta, 6),
                    "memoryContinuity": round(memory_continuity, 6),
                    "pluralityRetention": round(plurality_retention, 6),
                },
            }
        )

    if not findings:
        findings.append(
            {
                "targetId": target_id,
                "severity": "info",
                "type": "within-bounds",
                "message": "Terrace precursor indicators are within bounded watch ranges; retain plurality-protect monitoring.",
                "targetPublisherAction": "watch",
                "data": {
                    "Theta": round(theta, 6),
                    "memoryContinuity": round(memory_continuity, 6),
                    "pluralityRetention": round(plurality_retention, 6),
                    "deltaS": round(delta_s, 6),
                    "lambda": round(lambda_value, 6),
                },
            }
        )

    return findings


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    if not TERRACE_PRECURSOR_MAP_PATH.exists():
        raise TerracePrecursorInputError(f"Missing required artifact: {TERRACE_PRECURSOR_MAP_PATH}")

    source = _load_json(TERRACE_PRECURSOR_MAP_PATH)
    targets = _parse_targets(source)
    if not targets:
        raise TerracePrecursorInputError("terrace_precursor_map.json must contain a non-empty targets list")

    findings = [f for t in targets for f in evaluate_target(t)]
    findings = sorted(findings, key=lambda item: (item["targetId"], item["severity"], item["type"]))

    decision = "warn" if any(f["severity"] == "warn" for f in findings) else "pass"
    created_at = str(source.get("generatedAt") or source.get("created_at") or "1970-01-01T00:00:00Z")
    phaselock = (
        "CoherenceLattice terrace precursor map -> Sophia bounded precursor audit -> "
        "publisher watch/docket overlays -> human/community/scientific stewardship"
    )
    caution = (
        "This audit provides bounded advisory guidance only. It does not authorize suppression orders, "
        "governance transfer, epochal closure, or canon settlement."
    )

    metadata = {
        "inputArtifact": "bridge/terrace_precursor_map.json",
        "targetCount": len(targets),
        "warningCount": sum(1 for f in findings if f["severity"] == "warn"),
        "infoCount": sum(1 for f in findings if f["severity"] == "info"),
    }

    audit_payload = {
        "schema": "terrace_precursor_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "decision": decision,
        "findings": findings,
    }
    recommendations_payload = {
        "schema": "terrace_precursor_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [
            {
                "targetId": finding["targetId"],
                "type": finding["type"],
                "recommendation": finding["message"],
                "targetPublisherAction": _target_action(finding["severity"]),
            }
            for finding in findings
        ],
    }

    Draft202012Validator(_load_json(TERRACE_PRECURSOR_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(TERRACE_PRECURSOR_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia terrace precursor state audit")
    parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs()
    _save_json(TERRACE_PRECURSOR_AUDIT_OUT, audit_payload)
    _save_json(TERRACE_PRECURSOR_RECOMMENDATIONS_OUT, recommendations_payload)
    print(f"Wrote {TERRACE_PRECURSOR_AUDIT_OUT}")
    print(f"Wrote {TERRACE_PRECURSOR_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
