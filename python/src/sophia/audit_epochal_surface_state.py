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

EPOCHAL_SURFACE_MAP_PATH = BRIDGE_DIR / "epochal_surface_map.json"
HABITABLE_PLATEAU_REPORT_PATH = BRIDGE_DIR / "habitable_plateau_report.json"
REOPENED_EXPERIMENT_REGISTRY_PATH = BRIDGE_DIR / "reopened_experiment_registry.json"
SURFACE_EMERGENCE_GATE_PATH = BRIDGE_DIR / "surface_emergence_gate.json"

TERRACE_SEED_AUDIT_PATH = BRIDGE_DIR / "terrace_seed_audit.json"
NEW_DELTA_STABILIZATION_AUDIT_PATH = BRIDGE_DIR / "new_delta_stabilization_audit.json"
SUCCESSOR_CROSSING_AUDIT_PATH = BRIDGE_DIR / "successor_crossing_audit.json"
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

EPOCHAL_SURFACE_AUDIT_OUT = BRIDGE_DIR / "epochal_surface_audit.json"
EPOCHAL_SURFACE_RECOMMENDATIONS_OUT = BRIDGE_DIR / "epochal_surface_recommendations.json"

EPOCHAL_SURFACE_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "epochal_surface_audit_v1.schema.json"
EPOCHAL_SURFACE_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "epochal_surface_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "epochal_surface_v1"
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


class EpochalSurfaceInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class EpochalSurfaceDecision:
    target_id: str
    target_type: str
    surface_status: str
    coherence_score: float
    risk_score: float
    surface_context: str
    plurality_context: str
    experimentation_context: str
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
    if status == "experimentation-reopen":
        return "watch" if risk_score < 0.78 else "suppress"
    if status in {"surface-visible", "strengthen-legibility", "plurality-protect", "phase-transition-watch"}:
        return "watch"
    return {"require-human-review": "docket"}[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise EpochalSurfaceInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise EpochalSurfaceInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise EpochalSurfaceInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, expected_name: str) -> LoadedArtifact:
    if path.name != expected_name:
        raise EpochalSurfaceInputError(f"Canonical artifact-name mismatch for {path}: expected filename {expected_name}")
    if not path.exists():
        raise EpochalSurfaceInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise EpochalSurfaceInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise EpochalSurfaceInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise EpochalSurfaceInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise EpochalSurfaceInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise EpochalSurfaceInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise EpochalSurfaceInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
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
            "warning": "No canonical integrity manifest fields found on epochal-surface artifacts.",
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
        "warning": "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical epochal-surface constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across epochal-surface artifacts.",
        "divergenceReasons": sorted(set(reasons)),
        "manifests": manifests,
    }


def evaluate_target(
    row: dict[str, Any],
    *,
    plateau_rows: dict[str, dict[str, Any]],
    experiment_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> EpochalSurfaceDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "future")

    surface_readiness = _clamp01(float(row.get("surfaceReadinessScore", 0.5)))
    plurality_durability = _clamp01(float(row.get("pluralityDurabilityScore", 0.5)))
    trust_stability = _clamp01(float(row.get("trustStabilityScore", 0.5)))

    plateau = plateau_rows.get(target_id, {})
    habitable_coherence = _clamp01(float(plateau.get("habitableCoherenceScore", 0.5)))
    commons_transmission = _clamp01(float(plateau.get("commonsTransmissionScore", 0.5)))
    memory_continuity = _clamp01(float(plateau.get("memoryContinuityScore", 0.5)))

    experiment = experiment_rows.get(target_id, {})
    seed_formation_strength = _clamp01(float(experiment.get("seedFormationStrengthScore", 0.5)))
    exploratory_plurality = _clamp01(float(experiment.get("exploratoryPluralityScore", 0.5)))

    gate = gate_rows.get(target_id, {})
    phase_coupling = _clamp01(float(gate.get("phaseCouplingScore", 0.5)))
    surface_governance_coherence = _clamp01(float(gate.get("surfaceGovernanceCoherenceScore", 0.5)))

    coherence_score = _clamp01(
        0.16 * surface_readiness
        + 0.14 * plurality_durability
        + 0.12 * trust_stability
        + 0.10 * habitable_coherence
        + 0.10 * commons_transmission
        + 0.08 * memory_continuity
        + 0.08 * seed_formation_strength
        + 0.08 * exploratory_plurality
        + 0.08 * surface_governance_coherence
        + 0.06 * (1.0 - support_risk)
    )
    risk_score = _clamp01(
        0.12 * (1.0 - plurality_durability)
        + 0.12 * (1.0 - trust_stability)
        + 0.10 * (1.0 - habitable_coherence)
        + 0.10 * (1.0 - commons_transmission)
        + 0.10 * (1.0 - memory_continuity)
        + 0.12 * (1.0 - seed_formation_strength)
        + 0.10 * support_risk
        + 0.10 * trust_surface_risk
        + 0.14 * phase_coupling
    )

    weak_plurality_or_trust = plurality_durability < 0.64 or trust_stability < 0.62
    experimentation_reopen = seed_formation_strength < 0.56 and exploratory_plurality >= 0.64
    legibility_weak = commons_transmission < 0.66 or memory_continuity < 0.64 or support_risk >= 0.56

    if experimentation_reopen:
        status = "experimentation-reopen"
        rule = "seed-formation-weak-but-exploratory-plurality-healthy"
    elif weak_plurality_or_trust:
        status = "plurality-protect"
        rule = "surface-uplift-blocked-by-weak-plurality-or-trust-stability"
    elif surface_readiness >= 0.74 and phase_coupling >= 0.70 and plurality_durability >= 0.68 and trust_stability >= 0.66:
        status = "phase-transition-watch"
        rule = "strong-surface-readiness-with-healthy-plurality-watch"
    elif surface_readiness >= 0.72 and plurality_durability >= 0.68 and trust_stability >= 0.66 and not legibility_weak:
        status = "surface-visible"
        rule = "habitable-surface-with-plurality-and-trust"
    elif surface_readiness >= 0.70 and plurality_durability >= 0.66 and trust_stability >= 0.64 and legibility_weak:
        status = "strengthen-legibility"
        rule = "surface-conditions-present-but-commons-transmission-weak"
    else:
        status = "require-human-review"
        rule = "insufficient-epochal-surface-legibility"

    surface_context = (
        f"surfaceReadinessScore={surface_readiness:.3f}, habitableCoherenceScore={habitable_coherence:.3f}, commonsTransmissionScore={commons_transmission:.3f}; "
        "surface emergence should remain reviewable until livability and transmission are durable."
    )
    plurality_context = (
        f"pluralityDurabilityScore={plurality_durability:.3f}, trustStabilityScore={trust_stability:.3f}; "
        "no surface uplifts to surface-visible when plurality durability or trust stability is weak."
    )
    experimentation_context = (
        f"seedFormationStrengthScore={seed_formation_strength:.3f}, exploratoryPluralityScore={exploratory_plurality:.3f}; "
        "experimentation-reopen triggers when seed formation weakens but exploratory plurality remains healthy."
    )
    trust_context = (
        f"phaseCouplingScore={phase_coupling:.3f}, trustSurfaceRisk={trust_surface_risk:.3f}; "
        "phase-transition-watch appears only when surface readiness is strong and plurality remains healthy."
    )
    commons_context = (
        f"supportRisk={support_risk:.3f}, surfaceGovernanceCoherenceScore={surface_governance_coherence:.3f}, memoryContinuityScore={memory_continuity:.3f}; "
        "recommendations remain non-coercive and non-centralizing across terrace-seed, stabilization, crossing, successor, delta, trust, sovereignty, and value context."
    )
    explanation = (
        "Recommendations are bounded epochal-surface guidance only and do not declare new epochs, authorize settlement, or canonize emergent futures. "
        "Recommendations do not authorize institutional settlement, governance transfer, canon closure, or centralized successor rule. "
        f"targetId={target_id}, surfaceStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return EpochalSurfaceDecision(
        target_id=target_id,
        target_type=target_type,
        surface_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        surface_context=surface_context,
        plurality_context=plurality_context,
        experimentation_context=experimentation_context,
        trust_context=trust_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: EpochalSurfaceDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "surfaceStatus": d.surface_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "surfaceContext": d.surface_context,
        "pluralityContext": d.plurality_context,
        "experimentationContext": d.experimentation_context,
        "trustContext": d.trust_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    surface_map = _load_required_artifact(EPOCHAL_SURFACE_MAP_PATH, expected_name="epochal_surface_map.json")
    plateau_report = _load_required_artifact(HABITABLE_PLATEAU_REPORT_PATH, expected_name="habitable_plateau_report.json")
    experiment_registry = _load_required_artifact(REOPENED_EXPERIMENT_REGISTRY_PATH, expected_name="reopened_experiment_registry.json")
    emergence_gate = _load_required_artifact(SURFACE_EMERGENCE_GATE_PATH, expected_name="surface_emergence_gate.json")

    supporting = [
        ("terrace seed", _load_supporting_audit(TERRACE_SEED_AUDIT_PATH)),
        ("new delta stabilization", _load_supporting_audit(NEW_DELTA_STABILIZATION_AUDIT_PATH)),
        ("successor crossing", _load_supporting_audit(SUCCESSOR_CROSSING_AUDIT_PATH)),
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
    trust_surface_risk = _clamp01(supporting_risks[9])

    plateau_rows = {str(r.get("targetId")): r for r in _parse_rows(plateau_report.payload) if isinstance(r.get("targetId"), str)}
    experiment_rows = {str(r.get("targetId")): r for r in _parse_rows(experiment_registry.payload) if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(emergence_gate.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            plateau_rows=plateau_rows,
            experiment_rows=experiment_rows,
            gate_rows=gate_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(surface_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [surface_map, plateau_report, experiment_registry, emergence_gate]
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
        "terrace-seed / stabilization / crossing / successor / delta / trust / sovereignty / value context -> CoherenceLattice epochal-surface and reopened-experimentation formalization -> "
        "Sophia bounded epochal-surface audit -> Publisher epochal-surface / experiment overlays -> human/community/scientific stewardship of livable emergence and plural experimentation"
    )
    caution = (
        "Recommendations are bounded epochal-surface guidance only and do not declare new epochs, authorize settlement, "
        "or canonize emergent futures."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "epochal_surface_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "epochal_surface_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(EPOCHAL_SURFACE_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(EPOCHAL_SURFACE_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia epochal-surface state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    EPOCHAL_SURFACE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    EPOCHAL_SURFACE_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {EPOCHAL_SURFACE_AUDIT_OUT}")
    print(f"Wrote {EPOCHAL_SURFACE_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
