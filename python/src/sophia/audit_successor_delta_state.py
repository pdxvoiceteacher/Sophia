from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

RENEWAL_BRAID_MAP_PATH = BRIDGE_DIR / "renewal_braid_map.json"
SUCCESSOR_DELTA_SEED_REPORT_PATH = BRIDGE_DIR / "successor_delta_seed_report.json"
PLURALITY_RECOVERY_REGISTRY_PATH = BRIDGE_DIR / "plurality_recovery_registry.json"
TRANSITION_COUPLING_REPORT_PATH = BRIDGE_DIR / "transition_coupling_report.json"

TERRACE_EROSION_AUDIT_PATH = BRIDGE_DIR / "terrace_erosion_audit.json"
EPOCHAL_TERRACE_AUDIT_PATH = BRIDGE_DIR / "epochal_terrace_audit.json"
CIVILIZATIONAL_DELTA_AUDIT_PATH = BRIDGE_DIR / "civilizational_delta_audit.json"
KNOWLEDGE_RIVER_AUDIT_PATH = BRIDGE_DIR / "knowledge_river_audit.json"
TRUST_SURFACE_AUDIT_PATH = BRIDGE_DIR / "trust_surface_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"

SUCCESSOR_DELTA_AUDIT_OUT = BRIDGE_DIR / "successor_delta_audit.json"
SUCCESSOR_DELTA_RECOMMENDATIONS_OUT = BRIDGE_DIR / "successor_delta_recommendations.json"

SUCCESSOR_DELTA_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "successor_delta_audit_v1.schema.json"
SUCCESSOR_DELTA_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "successor_delta_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "successor_delta_v1"
EXPECTED_PRODUCER_REPOS = {"Sophia", "Sophia-Fixtures"}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")
CANONICAL_INTEGRITY_FIELDS = (
    "originProject",
    "canonicalPhaselock",
    "modificationDisclosureRequired",
    "ethicalBoundaryNotice",
    "commonsIntegrityNotice",
    "constraintSignatureVersion",
    "constraintSignatureSha256",
)
IMMUTABLE_SAFETY_FIELDS = (
    "canonicalPhaselock",
    "ethicalBoundaryNotice",
    "commonsIntegrityNotice",
    "constraintSignatureVersion",
)


class SuccessorDeltaInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class SuccessorDeltaDecision:
    target_id: str
    target_type: str
    successor_status: str
    coherence_score: float
    risk_score: float
    renewal_context: str
    seed_context: str
    plurality_context: str
    coupling_context: str
    commons_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_rows(payload: dict[str, Any], key: str = "targets") -> list[dict[str, Any]]:
    rows = payload.get(key)
    return [r for r in rows if isinstance(r, dict)] if isinstance(rows, list) else []


def _safe_mean(values: list[float], default: float = 0.0) -> float:
    return sum(values) / len(values) if values else default


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _display_path(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)) if path.is_relative_to(REPO_ROOT) else str(path)


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for doc in docs:
        for key in ("generatedAt", "created_at"):
            value = doc.get(key)
            if isinstance(value, str) and value:
                return value
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str, risk_score: float) -> str:
    if status == "successor-capture-risk":
        return "suppress" if risk_score >= 0.82 else "watch"
    if status in {"renewal-braiding", "successor-seed-visible", "plurality-recovering", "phase-transition-watch"}:
        return "watch"
    return {"require-human-review": "docket"}[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise SuccessorDeltaInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise SuccessorDeltaInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise SuccessorDeltaInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path) -> LoadedArtifact:
    if not path.exists():
        raise SuccessorDeltaInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SuccessorDeltaInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise SuccessorDeltaInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise SuccessorDeltaInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise SuccessorDeltaInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise SuccessorDeltaInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise SuccessorDeltaInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
    return manifest


def _build_canonical_integrity_metadata(artifacts: list[LoadedArtifact]) -> dict[str, Any]:
    manifests: list[dict[str, Any]] = []
    for artifact in artifacts:
        manifest = _extract_integrity_manifest(artifact.payload, path=artifact.path)
        if manifest is None:
            continue
        manifests.append({"path": _display_path(artifact.path), **manifest})
    if not manifests:
        return {"status": "absent", "warning": "No canonical integrity manifest fields found on successor-delta artifacts.", "divergenceReasons": [], "manifests": []}
    baseline = manifests[0]
    reasons: list[str] = []
    for candidate in manifests[1:]:
        if any(candidate[f] != baseline[f] for f in IMMUTABLE_SAFETY_FIELDS) and candidate["constraintSignatureSha256"] == baseline["constraintSignatureSha256"]:
            reasons.append(f"{candidate['path']} changes immutable safety constraints without changing constraint signature")
    status = "divergent" if reasons else "canonical"
    warning = "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical successor-delta constraints." if reasons else "Canonical integrity manifest present and internally consistent across successor-delta artifacts."
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def evaluate_target(
    row: dict[str, Any],
    *,
    seed_rows: dict[str, dict[str, Any]],
    plurality_rows: dict[str, dict[str, Any]],
    coupling_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> SuccessorDeltaDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "renewal")

    renewal_strength = _clamp01(float(row.get("renewalCorridorStrengthScore", 0.5)))
    braid_support = _clamp01(float(row.get("braidSupportScore", 0.5)))

    seed = seed_rows.get(target_id, {})
    successor_seed_strength = _clamp01(float(seed.get("successorSeedStrengthScore", 0.5)))
    capture_risk = _clamp01(float(seed.get("successorCaptureRiskScore", 0.5)))

    plurality = plurality_rows.get(target_id, {})
    plurality_recovery = _clamp01(float(plurality.get("pluralityRecoveryScore", 0.5)))
    suppressed_pathways_reopened = _clamp01(float(plurality.get("suppressedPathwayReopeningScore", 0.5)))

    coupling = coupling_rows.get(target_id, {})
    transition_coupling = _clamp01(float(coupling.get("transitionCouplingScore", 0.5)))
    multiterrace_sync = _clamp01(float(coupling.get("multiTerraceSynchronizationScore", 0.5)))

    coherence_score = _clamp01(
        0.16 * renewal_strength
        + 0.16 * braid_support
        + 0.14 * successor_seed_strength
        + 0.18 * plurality_recovery
        + 0.14 * suppressed_pathways_reopened
        + 0.12 * transition_coupling
        + 0.10 * (1.0 - support_risk)
    )
    risk_score = _clamp01(
        0.14 * (1.0 - braid_support)
        + 0.16 * capture_risk
        + 0.14 * (1.0 - plurality_recovery)
        + 0.10 * (1.0 - suppressed_pathways_reopened)
        + 0.12 * transition_coupling
        + 0.12 * multiterrace_sync
        + 0.10 * trust_surface_risk
        + 0.12 * support_risk
    )

    if capture_risk >= 0.70:
        status = "successor-capture-risk"
        rule = "successor-capture-suppresses-enthusiasm"
    elif transition_coupling >= 0.72 and multiterrace_sync >= 0.68 and trust_surface_risk < 0.70:
        status = "phase-transition-watch"
        rule = "multiterrace-coupling-transition-watch"
    elif successor_seed_strength >= 0.70 and braid_support >= 0.64 and plurality_recovery >= 0.62:
        status = "successor-seed-visible"
        rule = "seed-visible-under-braid-and-plurality-recovery"
    elif renewal_strength >= 0.66 and braid_support >= 0.62 and suppressed_pathways_reopened >= 0.62:
        status = "renewal-braiding"
        rule = "renewal-braid-strengthening"
    elif plurality_recovery >= 0.66 and suppressed_pathways_reopened >= 0.66:
        status = "plurality-recovering"
        rule = "plurality-recovery-required-for-successor-health"
    else:
        status = "require-human-review"
        rule = "insufficient-successor-legibility"

    renewal_context = (
        f"renewalCorridorStrengthScore={renewal_strength:.3f}, braidSupportScore={braid_support:.3f}; isolated renewal does not uplift to successor-seed-visible without braid support."
    )
    seed_context = (
        f"successorSeedStrengthScore={successor_seed_strength:.3f}, successorCaptureRiskScore={capture_risk:.3f}; successor-capture-risk suppresses successor enthusiasm even when convergence appears strong."
    )
    plurality_context = (
        f"pluralityRecoveryScore={plurality_recovery:.3f}, suppressedPathwayReopeningScore={suppressed_pathways_reopened:.3f}; healthy successor formation requires plurality recovery and reopening suppressed pathways."
    )
    coupling_context = (
        f"transitionCouplingScore={transition_coupling:.3f}, multiTerraceSynchronizationScore={multiterrace_sync:.3f}, trustSurfaceRisk={trust_surface_risk:.3f}; strong coupling across terraces may route to bounded phase-transition watch."
    )
    commons_context = (
        f"supportRisk={support_risk:.3f}; recommendations remain non-coercive and non-centralizing across erosion, terrace, delta, river, sovereignty, and value context."
    )
    explanation = (
        "Recommendations are bounded successor-renewal guidance only and do not declare new epochs, authorize regime replacement, or canonize successor systems. "
        "Recommendations do not authorize institutional overthrow, centralized succession, canon closure, or governance transfer. "
        f"targetId={target_id}, successorStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return SuccessorDeltaDecision(
        target_id=target_id,
        target_type=target_type,
        successor_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        renewal_context=renewal_context,
        seed_context=seed_context,
        plurality_context=plurality_context,
        coupling_context=coupling_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: SuccessorDeltaDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "successorStatus": d.successor_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "renewalContext": d.renewal_context,
        "seedContext": d.seed_context,
        "pluralityContext": d.plurality_context,
        "couplingContext": d.coupling_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    renewal_braid_map = _load_required_artifact(RENEWAL_BRAID_MAP_PATH)
    successor_seed_report = _load_required_artifact(SUCCESSOR_DELTA_SEED_REPORT_PATH)
    plurality_registry = _load_required_artifact(PLURALITY_RECOVERY_REGISTRY_PATH)
    coupling_report = _load_required_artifact(TRANSITION_COUPLING_REPORT_PATH)

    supporting = [
        ("terrace erosion", _load_supporting_audit(TERRACE_EROSION_AUDIT_PATH)),
        ("epochal terrace", _load_supporting_audit(EPOCHAL_TERRACE_AUDIT_PATH)),
        ("civilizational delta", _load_supporting_audit(CIVILIZATIONAL_DELTA_AUDIT_PATH)),
        ("knowledge river", _load_supporting_audit(KNOWLEDGE_RIVER_AUDIT_PATH)),
        ("trust surface", _load_supporting_audit(TRUST_SURFACE_AUDIT_PATH)),
        ("civilizational memory", _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)),
        ("commons sovereignty", _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)),
        ("value alignment", _load_supporting_audit(VALUE_ALIGNMENT_AUDIT_PATH)),
    ]
    supporting_risks = [_safe_mean([float(r.get("riskScore")) for r in _parse_rows(p, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45) for _, p in supporting]
    support_risk = _clamp01(_safe_mean(supporting_risks, 0.45))
    trust_surface_risk = _clamp01(supporting_risks[4])

    seed_rows = {str(r.get("targetId")): r for r in _parse_rows(successor_seed_report.payload) if isinstance(r.get("targetId"), str)}
    plurality_rows = {str(r.get("targetId")): r for r in _parse_rows(plurality_registry.payload) if isinstance(r.get("targetId"), str)}
    coupling_rows = {str(r.get("targetId")): r for r in _parse_rows(coupling_report.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            seed_rows=seed_rows,
            plurality_rows=plurality_rows,
            coupling_rows=coupling_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(renewal_braid_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [renewal_braid_map, successor_seed_report, plurality_registry, coupling_report]
    metadata = {
        "supportRisk": round(support_risk, 6),
        "trustSurfaceRisk": round(trust_surface_risk, 6),
        "inputArtifacts": [
            {
                "path": _display_path(a.path),
                "schemaVersion": str(a.payload.get("schemaVersion")),
                "producerRepo": str(a.payload.get("producerRepo")),
                "producerModule": str(a.payload.get("producerModule")),
                "producerCommit": str(a.payload.get("producerCommit")),
                "generatedAt": str(a.payload.get("generatedAt")),
            }
            for a in loaded
        ],
        "canonicalIntegrity": _build_canonical_integrity_metadata(loaded),
        "supportingAudits": [name for name, _ in supporting],
    }

    phaselock = (
        "erosion / terrace / delta / river / trust / sovereignty / value context -> CoherenceLattice renewal-braid and successor-delta formalization -> "
        "Sophia bounded successor audit -> Publisher successor overlays -> human/community/scientific stewardship of renewal and successor plurality"
    )
    caution = (
        "Recommendations are bounded successor-renewal guidance only and do not declare new epochs, authorize regime replacement, "
        "or canonize successor systems."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "successor_delta_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "successor_delta_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(SUCCESSOR_DELTA_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(SUCCESSOR_DELTA_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia successor-delta state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    SUCCESSOR_DELTA_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    SUCCESSOR_DELTA_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {SUCCESSOR_DELTA_AUDIT_OUT}")
    print(f"Wrote {SUCCESSOR_DELTA_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
