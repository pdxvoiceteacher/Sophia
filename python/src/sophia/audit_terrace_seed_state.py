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

TERRACE_SEED_MAP_PATH = BRIDGE_DIR / "terrace_seed_map.json"
EXPERIMENTAL_REPLURALIZATION_REPORT_PATH = BRIDGE_DIR / "experimental_repluralization_report.json"
SEDIMENTATION_READINESS_SCORECARD_PATH = BRIDGE_DIR / "sedimentation_readiness_scorecard.json"
TERRACE_SEED_GATE_PATH = BRIDGE_DIR / "terrace_seed_gate.json"

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

TERRACE_SEED_AUDIT_OUT = BRIDGE_DIR / "terrace_seed_audit.json"
TERRACE_SEED_RECOMMENDATIONS_OUT = BRIDGE_DIR / "terrace_seed_recommendations.json"

TERRACE_SEED_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "terrace_seed_audit_v1.schema.json"
TERRACE_SEED_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "terrace_seed_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "terrace_seed_v1"
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


class TerraceSeedInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class TerraceSeedDecision:
    target_id: str
    target_type: str
    seed_status: str
    coherence_score: float
    risk_score: float
    seed_context: str
    plurality_context: str
    repluralization_context: str
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
    if status == "repluralization-visible":
        return "watch" if risk_score < 0.78 else "suppress"
    if status in {"seed-visible", "strengthen-legibility", "plurality-protect", "phase-transition-watch"}:
        return "watch"
    return {"require-human-review": "docket"}[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise TerraceSeedInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise TerraceSeedInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise TerraceSeedInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, expected_name: str) -> LoadedArtifact:
    if path.name != expected_name:
        raise TerraceSeedInputError(f"Canonical artifact-name mismatch for {path}: expected filename {expected_name}")
    if not path.exists():
        raise TerraceSeedInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise TerraceSeedInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise TerraceSeedInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise TerraceSeedInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise TerraceSeedInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise TerraceSeedInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise TerraceSeedInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
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
            "warning": "No canonical integrity manifest fields found on terrace-seed artifacts.",
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
        "warning": "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical terrace-seed constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across terrace-seed artifacts.",
        "divergenceReasons": sorted(set(reasons)),
        "manifests": manifests,
    }


def evaluate_target(
    row: dict[str, Any],
    *,
    repluralization_rows: dict[str, dict[str, Any]],
    sediment_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> TerraceSeedDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "future")

    seed_readiness = _clamp01(float(row.get("terraceSeedReadinessScore", 0.5)))
    plurality_durability = _clamp01(float(row.get("pluralityDurabilityScore", 0.5)))
    trust_stability = _clamp01(float(row.get("trustStabilityScore", 0.5)))

    replural = repluralization_rows.get(target_id, {})
    stabilization_health = _clamp01(float(replural.get("stabilizationHealthScore", 0.5)))
    experimentation_recovery = _clamp01(float(replural.get("experimentationRecoveryScore", 0.5)))
    scattering_pressure = _clamp01(float(replural.get("scatteringPressureScore", 0.5)))

    sediment = sediment_rows.get(target_id, {})
    commons_transmission = _clamp01(float(sediment.get("commonsTransmissionScore", 0.5)))
    memory_weave = _clamp01(float(sediment.get("memoryWeaveScore", 0.5)))

    gate = gate_rows.get(target_id, {})
    phase_coupling = _clamp01(float(gate.get("phaseCouplingScore", 0.5)))
    seed_governance_coherence = _clamp01(float(gate.get("seedGovernanceCoherenceScore", 0.5)))

    coherence_score = _clamp01(
        0.16 * seed_readiness
        + 0.14 * plurality_durability
        + 0.12 * trust_stability
        + 0.10 * stabilization_health
        + 0.10 * experimentation_recovery
        + 0.10 * commons_transmission
        + 0.10 * memory_weave
        + 0.10 * seed_governance_coherence
        + 0.08 * (1.0 - support_risk)
    )
    risk_score = _clamp01(
        0.12 * (1.0 - plurality_durability)
        + 0.12 * (1.0 - trust_stability)
        + 0.12 * (1.0 - stabilization_health)
        + 0.10 * (1.0 - commons_transmission)
        + 0.10 * (1.0 - memory_weave)
        + 0.12 * scattering_pressure
        + 0.10 * support_risk
        + 0.10 * trust_surface_risk
        + 0.12 * phase_coupling
    )

    weak_plurality_or_trust = plurality_durability < 0.64 or trust_stability < 0.62
    repluralization_visible = stabilization_health < 0.56 and experimentation_recovery >= 0.64
    legibility_weak = commons_transmission < 0.66 or memory_weave < 0.64 or support_risk >= 0.56

    if repluralization_visible:
        status = "repluralization-visible"
        rule = "stabilization-weak-but-experimentation-recovery-healthy"
    elif weak_plurality_or_trust:
        status = "plurality-protect"
        rule = "seed-uplift-blocked-by-weak-plurality-or-trust-stability"
    elif seed_readiness >= 0.74 and phase_coupling >= 0.70 and plurality_durability >= 0.68 and trust_stability >= 0.66:
        status = "phase-transition-watch"
        rule = "strong-seed-readiness-with-healthy-plurality-watch"
    elif seed_readiness >= 0.72 and plurality_durability >= 0.68 and trust_stability >= 0.66 and not legibility_weak:
        status = "seed-visible"
        rule = "durable-terrace-seed-with-plurality-and-trust"
    elif seed_readiness >= 0.70 and plurality_durability >= 0.66 and trust_stability >= 0.64 and legibility_weak:
        status = "strengthen-legibility"
        rule = "seed-conditions-present-but-commons-transmission-weak"
    else:
        status = "require-human-review"
        rule = "insufficient-terrace-seed-legibility"

    seed_context = (
        f"terraceSeedReadinessScore={seed_readiness:.3f}, commonsTransmissionScore={commons_transmission:.3f}, memoryWeaveScore={memory_weave:.3f}; "
        "seed formation should prioritize legible commons transmission over premature sediment claims."
    )
    plurality_context = (
        f"pluralityDurabilityScore={plurality_durability:.3f}, trustStabilityScore={trust_stability:.3f}; "
        "no formation uplifts to seed-visible when plurality durability or trust stability is weak."
    )
    repluralization_context = (
        f"stabilizationHealthScore={stabilization_health:.3f}, experimentationRecoveryScore={experimentation_recovery:.3f}, scatteringPressureScore={scattering_pressure:.3f}; "
        "repluralization-visible triggers when stabilization fails but experimentation recovery remains healthy."
    )
    trust_context = (
        f"phaseCouplingScore={phase_coupling:.3f}, trustSurfaceRisk={trust_surface_risk:.3f}; "
        "phase-transition-watch appears only when terrace seed readiness is strong and plurality remains healthy."
    )
    commons_context = (
        f"supportRisk={support_risk:.3f}, seedGovernanceCoherenceScore={seed_governance_coherence:.3f}; "
        "recommendations remain non-coercive and non-centralizing across stabilization, crossing, successor, terrace, delta, trust, sovereignty, and value context."
    )
    explanation = (
        "Recommendations are bounded terrace-seed guidance only and do not declare new epochs, authorize successor settlement, or canonize emergent futures. "
        "Recommendations do not authorize institutional settlement, governance transfer, canon closure, or centralized successor rule. "
        f"targetId={target_id}, seedStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return TerraceSeedDecision(
        target_id=target_id,
        target_type=target_type,
        seed_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        seed_context=seed_context,
        plurality_context=plurality_context,
        repluralization_context=repluralization_context,
        trust_context=trust_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: TerraceSeedDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "seedStatus": d.seed_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "seedContext": d.seed_context,
        "pluralityContext": d.plurality_context,
        "repluralizationContext": d.repluralization_context,
        "trustContext": d.trust_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    seed_map = _load_required_artifact(TERRACE_SEED_MAP_PATH, expected_name="terrace_seed_map.json")
    replural_report = _load_required_artifact(EXPERIMENTAL_REPLURALIZATION_REPORT_PATH, expected_name="experimental_repluralization_report.json")
    sediment_scorecard = _load_required_artifact(SEDIMENTATION_READINESS_SCORECARD_PATH, expected_name="sedimentation_readiness_scorecard.json")
    seed_gate = _load_required_artifact(TERRACE_SEED_GATE_PATH, expected_name="terrace_seed_gate.json")

    supporting = [
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
    trust_surface_risk = _clamp01(supporting_risks[8])

    repluralization_rows = {str(r.get("targetId")): r for r in _parse_rows(replural_report.payload) if isinstance(r.get("targetId"), str)}
    sediment_rows = {str(r.get("targetId")): r for r in _parse_rows(sediment_scorecard.payload) if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(seed_gate.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            repluralization_rows=repluralization_rows,
            sediment_rows=sediment_rows,
            gate_rows=gate_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(seed_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [seed_map, replural_report, sediment_scorecard, seed_gate]
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
        "stabilization / crossing / successor / terrace / delta / trust / sovereignty / value context -> CoherenceLattice terrace-seed and repluralization formalization -> "
        "Sophia bounded terrace-seed audit -> Publisher terrace-seed / repluralization overlays -> human/community/scientific stewardship of early sediment and plural experimentation"
    )
    caution = (
        "Recommendations are bounded terrace-seed guidance only and do not declare new epochs, authorize successor settlement, "
        "or canonize emergent futures."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "terrace_seed_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "terrace_seed_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(TERRACE_SEED_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(TERRACE_SEED_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia terrace-seed state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    TERRACE_SEED_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    TERRACE_SEED_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {TERRACE_SEED_AUDIT_OUT}")
    print(f"Wrote {TERRACE_SEED_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
