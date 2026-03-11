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

LIVING_TERRACE_MAP_PATH = BRIDGE_DIR / "living_terrace_map.json"
COMMONS_HABITABILITY_REPORT_PATH = BRIDGE_DIR / "commons_habitability_report.json"
PLURAL_HABITATION_REGISTRY_PATH = BRIDGE_DIR / "plural_habitation_registry.json"
TERRACE_CONSOLIDATION_GATE_PATH = BRIDGE_DIR / "terrace_consolidation_gate.json"

EPOCHAL_SURFACE_AUDIT_PATH = BRIDGE_DIR / "epochal_surface_audit.json"
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

LIVING_TERRACE_AUDIT_OUT = BRIDGE_DIR / "living_terrace_audit.json"
LIVING_TERRACE_RECOMMENDATIONS_OUT = BRIDGE_DIR / "living_terrace_recommendations.json"

LIVING_TERRACE_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "living_terrace_audit_v1.schema.json"
LIVING_TERRACE_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "living_terrace_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "living_terrace_v1"
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


class LivingTerraceInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class LivingTerraceDecision:
    target_id: str
    target_type: str
    terrace_status: str
    coherence_score: float
    risk_score: float
    terrace_context: str
    plurality_context: str
    habitability_context: str
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
    if status == "keep-open":
        return "watch" if risk_score < 0.78 else "suppress"
    if status in {"terrace-visible", "strengthen-habitability", "plurality-protect", "phase-transition-watch"}:
        return "watch"
    return {"require-human-review": "docket"}[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise LivingTerraceInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise LivingTerraceInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise LivingTerraceInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, expected_name: str) -> LoadedArtifact:
    if path.name != expected_name:
        raise LivingTerraceInputError(f"Canonical artifact-name mismatch for {path}: expected filename {expected_name}")
    if not path.exists():
        raise LivingTerraceInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise LivingTerraceInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise LivingTerraceInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise LivingTerraceInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise LivingTerraceInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise LivingTerraceInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise LivingTerraceInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
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
            "warning": "No canonical integrity manifest fields found on living-terrace artifacts.",
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
        "warning": "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical living-terrace constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across living-terrace artifacts.",
        "divergenceReasons": sorted(set(reasons)),
        "manifests": manifests,
    }


def evaluate_target(
    row: dict[str, Any],
    *,
    habitability_rows: dict[str, dict[str, Any]],
    habitation_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> LivingTerraceDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "future")

    terrace_readiness = _clamp01(float(row.get("livingTerraceReadinessScore", 0.5)))
    plurality_metabolization = _clamp01(float(row.get("pluralityMetabolizationScore", 0.5)))
    trust_ordinariness = _clamp01(float(row.get("trustOrdinarinessScore", 0.5)))

    habitability = habitability_rows.get(target_id, {})
    commons_habitability = _clamp01(float(habitability.get("commonsHabitabilityScore", 0.5)))
    ordinary_stewardship = _clamp01(float(habitability.get("ordinaryStewardshipScore", 0.5)))
    memory_continuity = _clamp01(float(habitability.get("memoryContinuityScore", 0.5)))

    habitation = habitation_rows.get(target_id, {})
    plural_habitation_health = _clamp01(float(habitation.get("pluralHabitationHealthScore", 0.5)))
    settlement_deservedness = _clamp01(float(habitation.get("settlementDeservednessScore", 0.5)))

    gate = gate_rows.get(target_id, {})
    terrace_consolidation = _clamp01(float(gate.get("terraceConsolidationScore", 0.5)))
    governance_coherence = _clamp01(float(gate.get("governanceCoherenceScore", 0.5)))

    coherence_score = _clamp01(
        0.16 * terrace_readiness
        + 0.14 * plurality_metabolization
        + 0.12 * trust_ordinariness
        + 0.12 * commons_habitability
        + 0.10 * ordinary_stewardship
        + 0.08 * memory_continuity
        + 0.08 * plural_habitation_health
        + 0.08 * settlement_deservedness
        + 0.06 * governance_coherence
        + 0.06 * (1.0 - support_risk)
    )
    risk_score = _clamp01(
        0.12 * (1.0 - plurality_metabolization)
        + 0.12 * (1.0 - trust_ordinariness)
        + 0.10 * (1.0 - commons_habitability)
        + 0.10 * (1.0 - ordinary_stewardship)
        + 0.08 * (1.0 - memory_continuity)
        + 0.10 * (1.0 - settlement_deservedness)
        + 0.10 * support_risk
        + 0.10 * trust_surface_risk
        + 0.10 * terrace_consolidation
        + 0.08 * (1.0 - plural_habitation_health)
    )

    weak_plurality_or_trust = plurality_metabolization < 0.64 or trust_ordinariness < 0.62
    keep_open = plural_habitation_health >= 0.66 and settlement_deservedness < 0.56
    habitability_weak = commons_habitability < 0.66 or ordinary_stewardship < 0.64 or support_risk >= 0.56

    if keep_open:
        status = "keep-open"
        rule = "plural-habitation-healthy-but-settlement-not-deserved"
    elif weak_plurality_or_trust:
        status = "plurality-protect"
        rule = "terrace-uplift-blocked-by-weak-plurality-metabolization-or-trust-ordinariness"
    elif terrace_readiness >= 0.74 and terrace_consolidation >= 0.70 and plurality_metabolization >= 0.68 and trust_ordinariness >= 0.66:
        status = "phase-transition-watch"
        rule = "strong-terrace-consolidation-with-healthy-plurality-watch"
    elif terrace_readiness >= 0.72 and plurality_metabolization >= 0.68 and trust_ordinariness >= 0.66 and not habitability_weak:
        status = "terrace-visible"
        rule = "living-terrace-visible-with-plurality-and-trust"
    elif terrace_readiness >= 0.70 and plurality_metabolization >= 0.66 and trust_ordinariness >= 0.64 and habitability_weak:
        status = "strengthen-habitability"
        rule = "surface-conditions-present-but-ordinary-stewardship-weak"
    else:
        status = "require-human-review"
        rule = "insufficient-living-terrace-legibility"

    terrace_context = (
        f"livingTerraceReadinessScore={terrace_readiness:.3f}, commonsHabitabilityScore={commons_habitability:.3f}, ordinaryStewardshipScore={ordinary_stewardship:.3f}; "
        "living terrace emergence should prioritize ordinary habitability, not expert-only consolidation."
    )
    plurality_context = (
        f"pluralityMetabolizationScore={plurality_metabolization:.3f}, trustOrdinarinessScore={trust_ordinariness:.3f}; "
        "no surface uplifts to terrace-visible when plurality metabolization or trust ordinariness is weak."
    )
    habitability_context = (
        f"pluralHabitationHealthScore={plural_habitation_health:.3f}, settlementDeservednessScore={settlement_deservedness:.3f}, memoryContinuityScore={memory_continuity:.3f}; "
        "keep-open triggers when plural habitation remains healthy but settlement is not yet deserved."
    )
    trust_context = (
        f"terraceConsolidationScore={terrace_consolidation:.3f}, trustSurfaceRisk={trust_surface_risk:.3f}; "
        "phase-transition-watch appears only when terrace consolidation is strong and plurality remains healthy."
    )
    commons_context = (
        f"supportRisk={support_risk:.3f}, governanceCoherenceScore={governance_coherence:.3f}; "
        "recommendations remain non-coercive and non-centralizing across surface, terrace-seed, stabilization, successor, delta, trust, sovereignty, and value context."
    )
    explanation = (
        "Recommendations are bounded living-terrace guidance only and do not declare new epochs, authorize settlement, or canonize emergent futures. "
        "Recommendations do not authorize institutional settlement, governance transfer, canon closure, or centralized successor rule. "
        f"targetId={target_id}, terraceStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return LivingTerraceDecision(
        target_id=target_id,
        target_type=target_type,
        terrace_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        terrace_context=terrace_context,
        plurality_context=plurality_context,
        habitability_context=habitability_context,
        trust_context=trust_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: LivingTerraceDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "terraceStatus": d.terrace_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "terraceContext": d.terrace_context,
        "pluralityContext": d.plurality_context,
        "habitabilityContext": d.habitability_context,
        "trustContext": d.trust_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    terrace_map = _load_required_artifact(LIVING_TERRACE_MAP_PATH, expected_name="living_terrace_map.json")
    habitability_report = _load_required_artifact(COMMONS_HABITABILITY_REPORT_PATH, expected_name="commons_habitability_report.json")
    habitation_registry = _load_required_artifact(PLURAL_HABITATION_REGISTRY_PATH, expected_name="plural_habitation_registry.json")
    consolidation_gate = _load_required_artifact(TERRACE_CONSOLIDATION_GATE_PATH, expected_name="terrace_consolidation_gate.json")

    supporting = [
        ("epochal surface", _load_supporting_audit(EPOCHAL_SURFACE_AUDIT_PATH)),
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
    trust_surface_risk = _clamp01(supporting_risks[10])

    habitability_rows = {str(r.get("targetId")): r for r in _parse_rows(habitability_report.payload) if isinstance(r.get("targetId"), str)}
    habitation_rows = {str(r.get("targetId")): r for r in _parse_rows(habitation_registry.payload) if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(consolidation_gate.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            habitability_rows=habitability_rows,
            habitation_rows=habitation_rows,
            gate_rows=gate_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(terrace_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [terrace_map, habitability_report, habitation_registry, consolidation_gate]
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
        "surface / terrace-seed / stabilization / successor / delta / trust / sovereignty / value context -> CoherenceLattice living-terrace and commons-habitability formalization -> "
        "Sophia bounded living-terrace audit -> Publisher living-terrace / plural-habitation overlays -> human/community/scientific stewardship of habitable emergence and open plurality"
    )
    caution = (
        "Recommendations are bounded living-terrace guidance only and do not declare new epochs, authorize settlement, "
        "or canonize emergent futures."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "living_terrace_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "living_terrace_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(LIVING_TERRACE_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(LIVING_TERRACE_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia living-terrace state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    LIVING_TERRACE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    LIVING_TERRACE_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {LIVING_TERRACE_AUDIT_OUT}")
    print(f"Wrote {LIVING_TERRACE_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
