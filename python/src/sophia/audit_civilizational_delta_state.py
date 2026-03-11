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

DELTA_SEED_MAP_PATH = BRIDGE_DIR / "delta_seed_map.json"
PARADIGM_CONVERGENCE_REPORT_PATH = BRIDGE_DIR / "paradigm_convergence_report.json"
EPISTEMIC_REORGANIZATION_SIGNAL_PATH = BRIDGE_DIR / "epistemic_reorganization_signal.json"
CIVILIZATIONAL_DELTA_FORECAST_PATH = BRIDGE_DIR / "civilizational_delta_forecast.json"

KNOWLEDGE_RIVER_AUDIT_PATH = BRIDGE_DIR / "knowledge_river_audit.json"
DISCOVERY_NAVIGATION_AUDIT_PATH = BRIDGE_DIR / "discovery_navigation_audit.json"
EPISTEMIC_ATTRACTOR_AUDIT_PATH = BRIDGE_DIR / "epistemic_attractor_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
TRUST_SURFACE_AUDIT_PATH = BRIDGE_DIR / "trust_surface_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"

CIVILIZATIONAL_DELTA_AUDIT_OUT = BRIDGE_DIR / "civilizational_delta_audit.json"
CIVILIZATIONAL_DELTA_RECOMMENDATIONS_OUT = BRIDGE_DIR / "civilizational_delta_recommendations.json"

CIVILIZATIONAL_DELTA_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "civilizational_delta_audit_v1.schema.json"
CIVILIZATIONAL_DELTA_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "civilizational_delta_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "civilizational_delta_v1"
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


class CivilizationalDeltaInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class CivilizationalDeltaDecision:
    target_id: str
    target_type: str
    delta_status: str
    coherence_score: float
    risk_score: float
    river_context: str
    convergence_context: str
    reorganization_context: str
    trust_context: str
    commons_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_rows(payload: dict[str, Any], key: str = "targets") -> list[dict[str, Any]]:
    value = payload.get(key)
    return [r for r in value if isinstance(r, dict)] if isinstance(value, list) else []


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
    if status == "capture-risk":
        return "suppress" if risk_score >= 0.82 else "watch"
    if status == "delta-seed-visible":
        return "watch"
    return {
        "convergence-strengthen": "docket",
        "plurality-preserve": "watch",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise CivilizationalDeltaInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise CivilizationalDeltaInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise CivilizationalDeltaInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path) -> LoadedArtifact:
    if not path.exists():
        raise CivilizationalDeltaInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise CivilizationalDeltaInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise CivilizationalDeltaInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise CivilizationalDeltaInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise CivilizationalDeltaInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise CivilizationalDeltaInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise CivilizationalDeltaInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
    return manifest


def _build_canonical_integrity_metadata(artifacts: list[LoadedArtifact]) -> dict[str, Any]:
    manifests: list[dict[str, Any]] = []
    for artifact in artifacts:
        manifest = _extract_integrity_manifest(artifact.payload, path=artifact.path)
        if manifest is None:
            continue
        manifests.append({"path": _display_path(artifact.path), **manifest})

    if not manifests:
        return {
            "status": "absent",
            "warning": "No canonical integrity manifest fields found on civilizational-delta artifacts.",
            "divergenceReasons": [],
            "manifests": [],
        }

    baseline = manifests[0]
    reasons: list[str] = []
    for candidate in manifests[1:]:
        safety_changed = any(candidate[field] != baseline[field] for field in IMMUTABLE_SAFETY_FIELDS)
        same_sig = candidate["constraintSignatureSha256"] == baseline["constraintSignatureSha256"]
        if safety_changed and same_sig:
            reasons.append(f"{candidate['path']} changes immutable safety constraints without changing constraint signature")

    status = "divergent" if reasons else "canonical"
    warning = (
        "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical civilizational-delta constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across civilizational-delta artifacts."
    )
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def evaluate_target(
    row: dict[str, Any],
    *,
    convergence_rows: dict[str, dict[str, Any]],
    reorg_rows: dict[str, dict[str, Any]],
    forecast_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> CivilizationalDeltaDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "domain")

    delta_seed_strength = _clamp01(float(row.get("deltaSeedStrengthScore", 0.5)))
    plurality_preservation = _clamp01(float(row.get("pluralityPreservationScore", 0.5)))
    dissent_portability = _clamp01(float(row.get("dissentPortabilityScore", 0.5)))

    convergence = convergence_rows.get(target_id, {})
    convergence_strength = _clamp01(float(convergence.get("convergenceStrengthScore", 0.5)))
    convergence_capture_risk = _clamp01(float(convergence.get("captureRiskScore", 0.5)))

    reorg = reorg_rows.get(target_id, {})
    reorganization_signal = _clamp01(float(reorg.get("reorganizationSignalScore", 0.5)))
    canon_closure_risk = _clamp01(float(reorg.get("canonClosureRiskScore", 0.5)))

    forecast = forecast_rows.get(target_id, {})
    transition_overclaim_risk = _clamp01(float(forecast.get("transitionOverclaimRiskScore", 0.5)))

    coherence_score = _clamp01(
        0.20 * delta_seed_strength
        + 0.18 * plurality_preservation
        + 0.14 * dissent_portability
        + 0.18 * convergence_strength
        + 0.12 * reorganization_signal
        + 0.18 * (1.0 - support_risk)
    )
    risk_score = _clamp01(
        0.16 * (1.0 - plurality_preservation)
        + 0.14 * (1.0 - dissent_portability)
        + 0.14 * convergence_capture_risk
        + 0.12 * canon_closure_risk
        + 0.12 * transition_overclaim_risk
        + 0.18 * trust_surface_risk
        + 0.14 * support_risk
    )

    if convergence_capture_risk >= 0.72 or canon_closure_risk >= 0.72:
        status = "capture-risk"
        rule = "anti-capture-and-anti-canon-closure-gate"
    elif trust_surface_risk >= 0.66:
        status = "require-human-review"
        rule = "trust-surface-instability-suppression-gate"
    elif plurality_preservation >= 0.72 and dissent_portability >= 0.68 and delta_seed_strength >= 0.58:
        status = "plurality-preserve"
        rule = "plurality-is-positive-delta-condition"
    elif convergence_strength >= 0.72 and (plurality_preservation < 0.60 or dissent_portability < 0.58):
        status = "convergence-strengthen"
        rule = "convergence-without-dissent-needs-strengthening"
    elif delta_seed_strength >= 0.68 and convergence_strength >= 0.62 and trust_surface_risk < 0.58:
        status = "delta-seed-visible"
        rule = "bounded-delta-seed-visibility"
    else:
        status = "convergence-strengthen"
        rule = "default-convergence-strengthening"

    river_context = (
        f"deltaSeedStrengthScore={delta_seed_strength:.3f}, pluralityPreservationScore={plurality_preservation:.3f}, "
        f"dissentPortabilityScore={dissent_portability:.3f}; healthy delta formation favors plural tributary strengthening over singular channels."
    )
    convergence_context = (
        f"convergenceStrengthScore={convergence_strength:.3f}, captureRiskScore={convergence_capture_risk:.3f}; "
        "strong convergence without dissent preservation is constrained to watch-level caution and strengthening guidance."
    )
    reorganization_context = (
        f"reorganizationSignalScore={reorganization_signal:.3f}, canonClosureRiskScore={canon_closure_risk:.3f}, "
        f"transitionOverclaimRiskScore={transition_overclaim_risk:.3f}; no epochal overclaim is permitted."
    )
    trust_context = (
        f"trustSurfaceRisk={trust_surface_risk:.3f}; trust-surface instability suppresses delta enthusiasm and routes to review-oriented caution."
    )
    commons_context = (
        f"supportRisk={support_risk:.3f}; commons stewardship preserves distributed legitimacy, memory continuity, and non-centralized interpretation."
    )
    explanation = (
        "Recommendations are bounded civilizational-stewardship guidance only and do not declare epoch transition, canonize paradigms, or authorize centralized authority. "
        "They do not authorize automatic policy, deployment, or governance transition. "
        f"targetId={target_id}, deltaStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return CivilizationalDeltaDecision(
        target_id=target_id,
        target_type=target_type,
        delta_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        river_context=river_context,
        convergence_context=convergence_context,
        reorganization_context=reorganization_context,
        trust_context=trust_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: CivilizationalDeltaDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "deltaStatus": d.delta_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "riverContext": d.river_context,
        "convergenceContext": d.convergence_context,
        "reorganizationContext": d.reorganization_context,
        "trustContext": d.trust_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    delta_seed_map = _load_required_artifact(DELTA_SEED_MAP_PATH)
    convergence_report = _load_required_artifact(PARADIGM_CONVERGENCE_REPORT_PATH)
    reorganization_signal = _load_required_artifact(EPISTEMIC_REORGANIZATION_SIGNAL_PATH)
    delta_forecast = _load_required_artifact(CIVILIZATIONAL_DELTA_FORECAST_PATH)

    supporting = [
        ("knowledge river", _load_supporting_audit(KNOWLEDGE_RIVER_AUDIT_PATH)),
        ("discovery navigation", _load_supporting_audit(DISCOVERY_NAVIGATION_AUDIT_PATH)),
        ("epistemic attractor", _load_supporting_audit(EPISTEMIC_ATTRACTOR_AUDIT_PATH)),
        ("civilizational memory", _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)),
        ("commons sovereignty", _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)),
        ("trust surface", _load_supporting_audit(TRUST_SURFACE_AUDIT_PATH)),
        ("value alignment", _load_supporting_audit(VALUE_ALIGNMENT_AUDIT_PATH)),
    ]
    supporting_risks = [
        _safe_mean([float(r.get("riskScore")) for r in _parse_rows(payload, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
        for _, payload in supporting
    ]
    support_risk = _clamp01(_safe_mean(supporting_risks, 0.45))
    trust_surface_risk = _clamp01(supporting_risks[5])

    convergence_rows = {str(r.get("targetId")): r for r in _parse_rows(convergence_report.payload) if isinstance(r.get("targetId"), str)}
    reorg_rows = {str(r.get("targetId")): r for r in _parse_rows(reorganization_signal.payload) if isinstance(r.get("targetId"), str)}
    forecast_rows = {str(r.get("targetId")): r for r in _parse_rows(delta_forecast.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            convergence_rows=convergence_rows,
            reorg_rows=reorg_rows,
            forecast_rows=forecast_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(delta_seed_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [delta_seed_map, convergence_report, reorganization_signal, delta_forecast]
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
        "rivers / memory / trust / sovereignty / value context -> CoherenceLattice delta-seed and reorganization formalization -> "
        "Sophia bounded civilizational-delta audit -> Publisher delta overlays -> human/community/scientific interpretation and plural stewardship"
    )
    caution = (
        "Recommendations are bounded civilizational-stewardship guidance only and do not declare epoch transition, canonize paradigms, "
        "or authorize centralized authority."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "civilizational_delta_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "civilizational_delta_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(CIVILIZATIONAL_DELTA_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(CIVILIZATIONAL_DELTA_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia civilizational-delta state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    CIVILIZATIONAL_DELTA_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    CIVILIZATIONAL_DELTA_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {CIVILIZATIONAL_DELTA_AUDIT_OUT}")
    print(f"Wrote {CIVILIZATIONAL_DELTA_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
