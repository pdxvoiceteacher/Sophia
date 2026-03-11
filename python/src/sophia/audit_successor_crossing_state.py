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

SUCCESSOR_CROSSING_MAP_PATH = BRIDGE_DIR / "successor_crossing_map.json"
FALSE_FUTURE_DECAY_REPORT_PATH = BRIDGE_DIR / "false_future_decay_report.json"
DELTA_CROSSING_GATE_PATH = BRIDGE_DIR / "delta_crossing_gate.json"
FUTURE_VIABILITY_FORECAST_PATH = BRIDGE_DIR / "future_viability_forecast.json"

SUCCESSOR_MATURATION_AUDIT_PATH = BRIDGE_DIR / "successor_maturation_audit.json"
SUCCESSOR_DELTA_AUDIT_PATH = BRIDGE_DIR / "successor_delta_audit.json"
TERRACE_EROSION_AUDIT_PATH = BRIDGE_DIR / "terrace_erosion_audit.json"
EPOCHAL_TERRACE_AUDIT_PATH = BRIDGE_DIR / "epochal_terrace_audit.json"
CIVILIZATIONAL_DELTA_AUDIT_PATH = BRIDGE_DIR / "civilizational_delta_audit.json"
KNOWLEDGE_RIVER_AUDIT_PATH = BRIDGE_DIR / "knowledge_river_audit.json"
TRUST_SURFACE_AUDIT_PATH = BRIDGE_DIR / "trust_surface_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"

SUCCESSOR_CROSSING_AUDIT_OUT = BRIDGE_DIR / "successor_crossing_audit.json"
SUCCESSOR_CROSSING_RECOMMENDATIONS_OUT = BRIDGE_DIR / "successor_crossing_recommendations.json"

SUCCESSOR_CROSSING_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "successor_crossing_audit_v1.schema.json"
SUCCESSOR_CROSSING_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "successor_crossing_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "successor_crossing_v1"
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


class SuccessorCrossingInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class SuccessorCrossingDecision:
    target_id: str
    target_type: str
    crossing_status: str
    coherence_score: float
    risk_score: float
    crossing_context: str
    plurality_context: str
    decay_context: str
    trust_context: str
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
    if status == "false-future-decay":
        return "suppress" if risk_score >= 0.78 else "watch"
    if status in {"crossing-visible", "strengthen-foundations", "plurality-protect", "phase-transition-watch"}:
        return "watch"
    return {"require-human-review": "docket"}[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise SuccessorCrossingInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise SuccessorCrossingInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise SuccessorCrossingInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, expected_name: str) -> LoadedArtifact:
    if path.name != expected_name:
        raise SuccessorCrossingInputError(f"Canonical artifact-name mismatch for {path}: expected filename {expected_name}")
    if not path.exists():
        raise SuccessorCrossingInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SuccessorCrossingInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise SuccessorCrossingInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise SuccessorCrossingInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise SuccessorCrossingInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise SuccessorCrossingInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise SuccessorCrossingInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
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
            "warning": "No canonical integrity manifest fields found on successor-crossing artifacts.",
            "divergenceReasons": [],
            "manifests": [],
        }

    baseline = manifests[0]
    reasons: list[str] = []
    for candidate in manifests[1:]:
        if any(candidate[f] != baseline[f] for f in IMMUTABLE_SAFETY_FIELDS) and candidate["constraintSignatureSha256"] == baseline["constraintSignatureSha256"]:
            reasons.append(f"{candidate['path']} changes immutable safety constraints without changing constraint signature")

    return {
        "status": "divergent" if reasons else "canonical",
        "warning": "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical successor-crossing constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across successor-crossing artifacts.",
        "divergenceReasons": sorted(set(reasons)),
        "manifests": manifests,
    }


def evaluate_target(
    row: dict[str, Any],
    *,
    decay_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    viability_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> SuccessorCrossingDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "future")

    crossing_readiness = _clamp01(float(row.get("crossingReadinessScore", 0.5)))
    plurality_retention = _clamp01(float(row.get("pluralityRetentionScore", 0.5)))
    memory_continuity = _clamp01(float(row.get("memoryContinuityScore", 0.5)))
    trust_legibility = _clamp01(float(row.get("trustLegibilityScore", 0.5)))

    decay = decay_rows.get(target_id, {})
    simulated_legitimacy = _clamp01(float(decay.get("simulatedLegitimacyScore", 0.5)))
    capture_exposure = _clamp01(float(decay.get("captureExposureScore", 0.5)))
    trust_repair = _clamp01(float(decay.get("trustRepairScore", 0.5)))

    gate = gate_rows.get(target_id, {})
    delta_likelihood = _clamp01(float(gate.get("successorDeltaLikelihoodScore", 0.5)))
    phase_coupling = _clamp01(float(gate.get("phaseCouplingScore", 0.5)))

    viability = viability_rows.get(target_id, {})
    viability_score = _clamp01(float(viability.get("futureViabilityScore", 0.5)))
    foundation_durability = _clamp01(float(viability.get("foundationDurabilityScore", 0.5)))

    coherence_score = _clamp01(
        0.16 * crossing_readiness
        + 0.14 * plurality_retention
        + 0.12 * memory_continuity
        + 0.12 * trust_legibility
        + 0.10 * trust_repair
        + 0.10 * delta_likelihood
        + 0.08 * phase_coupling
        + 0.10 * viability_score
        + 0.08 * foundation_durability
    )
    risk_score = _clamp01(
        0.12 * (1.0 - plurality_retention)
        + 0.10 * (1.0 - memory_continuity)
        + 0.12 * (1.0 - trust_legibility)
        + 0.14 * simulated_legitimacy
        + 0.14 * capture_exposure
        + 0.10 * (1.0 - trust_repair)
        + 0.10 * (1.0 - foundation_durability)
        + 0.10 * support_risk
        + 0.08 * trust_surface_risk
    )

    outrun_gap = _safe_mean([simulated_legitimacy, capture_exposure], 0.5) - _safe_mean([memory_continuity, trust_repair], 0.5)
    false_future_decay = (
        simulated_legitimacy >= 0.66 and capture_exposure >= 0.64 and outrun_gap >= 0.10
    )

    weak_plurality_or_trust = plurality_retention < 0.64 or trust_legibility < 0.62
    support_not_durable = foundation_durability < 0.66 or viability_score < 0.66 or support_risk >= 0.56

    if false_future_decay:
        status = "false-future-decay"
        rule = "simulated-legitimacy-and-capture-outrun-memory-and-trust-repair"
    elif weak_plurality_or_trust:
        status = "plurality-protect"
        rule = "crossing-uplift-blocked-by-weak-plurality-or-trust-legibility"
    elif delta_likelihood >= 0.74 and phase_coupling >= 0.70 and plurality_retention >= 0.66:
        status = "phase-transition-watch"
        rule = "strong-successor-delta-likelihood-with-healthy-plurality"
    elif crossing_readiness >= 0.72 and trust_legibility >= 0.66 and plurality_retention >= 0.68 and not support_not_durable:
        status = "crossing-visible"
        rule = "durable-crossing-readiness-with-plurality-and-trust-legibility"
    elif crossing_readiness >= 0.70 and trust_legibility >= 0.64 and plurality_retention >= 0.66 and support_not_durable:
        status = "strengthen-foundations"
        rule = "high-readiness-but-foundations-not-yet-durable"
    else:
        status = "require-human-review"
        rule = "insufficient-crossing-legibility"

    crossing_context = (
        f"crossingReadinessScore={crossing_readiness:.3f}, successorDeltaLikelihoodScore={delta_likelihood:.3f}, foundationDurabilityScore={foundation_durability:.3f}; "
        "durable crossing requires readiness plus durable support conditions."
    )
    plurality_context = (
        f"pluralityRetentionScore={plurality_retention:.3f}, trustLegibilityScore={trust_legibility:.3f}; "
        "no future uplifts to crossing-visible when plurality retention or trust legibility is weak."
    )
    decay_context = (
        f"simulatedLegitimacyScore={simulated_legitimacy:.3f}, captureExposureScore={capture_exposure:.3f}, memoryContinuityScore={memory_continuity:.3f}, trustRepairScore={trust_repair:.3f}; "
        "false-future-decay triggers when simulated legitimacy and capture exposure outrun memory continuity and trust repair."
    )
    trust_context = (
        f"phaseCouplingScore={phase_coupling:.3f}, trustSurfaceRisk={trust_surface_risk:.3f}; "
        "strong successor-delta likelihood routes to phase-transition-watch only when plurality remains healthy."
    )
    commons_context = (
        f"futureViabilityScore={viability_score:.3f}, supportRisk={support_risk:.3f}; "
        "recommendations remain non-coercive and non-centralizing across successor, maturation, terrace, delta, trust, sovereignty, and value context."
    )
    explanation = (
        "Recommendations are bounded successor-crossing guidance only and do not declare new epochs, authorize successor rule, or canonize emergent futures. "
        "Recommendations do not authorize institutional displacement, centralized succession, governance transfer, or canon closure. "
        f"targetId={target_id}, crossingStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return SuccessorCrossingDecision(
        target_id=target_id,
        target_type=target_type,
        crossing_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        crossing_context=crossing_context,
        plurality_context=plurality_context,
        decay_context=decay_context,
        trust_context=trust_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: SuccessorCrossingDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "crossingStatus": d.crossing_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "crossingContext": d.crossing_context,
        "pluralityContext": d.plurality_context,
        "decayContext": d.decay_context,
        "trustContext": d.trust_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    crossing_map = _load_required_artifact(SUCCESSOR_CROSSING_MAP_PATH, expected_name="successor_crossing_map.json")
    decay_report = _load_required_artifact(FALSE_FUTURE_DECAY_REPORT_PATH, expected_name="false_future_decay_report.json")
    gate_report = _load_required_artifact(DELTA_CROSSING_GATE_PATH, expected_name="delta_crossing_gate.json")
    viability_forecast = _load_required_artifact(FUTURE_VIABILITY_FORECAST_PATH, expected_name="future_viability_forecast.json")

    supporting = [
        ("successor maturation", _load_supporting_audit(SUCCESSOR_MATURATION_AUDIT_PATH)),
        ("successor delta", _load_supporting_audit(SUCCESSOR_DELTA_AUDIT_PATH)),
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
    trust_surface_risk = _clamp01(supporting_risks[6])

    decay_rows = {str(r.get("targetId")): r for r in _parse_rows(decay_report.payload) if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(gate_report.payload) if isinstance(r.get("targetId"), str)}
    viability_rows = {str(r.get("targetId")): r for r in _parse_rows(viability_forecast.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            decay_rows=decay_rows,
            gate_rows=gate_rows,
            viability_rows=viability_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(crossing_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [crossing_map, decay_report, gate_report, viability_forecast]
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
        "successor / maturation / terrace / delta / trust / sovereignty / value context -> CoherenceLattice successor-crossing and false-future-decay formalization -> "
        "Sophia bounded crossing audit -> Publisher crossing/decay overlays -> human/community/scientific stewardship of viable and non-viable future formations"
    )
    caution = (
        "Recommendations are bounded successor-crossing guidance only and do not declare new epochs, authorize successor rule, "
        "or canonize emergent futures."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "successor_crossing_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "successor_crossing_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(SUCCESSOR_CROSSING_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(SUCCESSOR_CROSSING_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia successor-crossing state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    SUCCESSOR_CROSSING_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    SUCCESSOR_CROSSING_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {SUCCESSOR_CROSSING_AUDIT_OUT}")
    print(f"Wrote {SUCCESSOR_CROSSING_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
