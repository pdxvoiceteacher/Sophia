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

BACKGROUND_COHERENCE_MAP_PATH = BRIDGE_DIR / "background_coherence_map.json"
CIVILIZATIONAL_NORMALIZATION_REPORT_PATH = BRIDGE_DIR / "civilizational_normalization_report.json"
AMBIENT_MEMORY_REGISTRY_PATH = BRIDGE_DIR / "ambient_memory_registry.json"
NORMALIZATION_GATE_PATH = BRIDGE_DIR / "normalization_gate.json"

LIVING_TERRACE_AUDIT_PATH = BRIDGE_DIR / "living_terrace_audit.json"
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

BACKGROUND_COHERENCE_AUDIT_OUT = BRIDGE_DIR / "background_coherence_audit.json"
BACKGROUND_COHERENCE_RECOMMENDATIONS_OUT = BRIDGE_DIR / "background_coherence_recommendations.json"

BACKGROUND_COHERENCE_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "background_coherence_audit_v1.schema.json"
BACKGROUND_COHERENCE_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "background_coherence_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "background_coherence_v1"
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


class BackgroundCoherenceInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class BackgroundCoherenceDecision:
    target_id: str
    target_type: str
    background_status: str
    coherence_score: float
    risk_score: float
    background_context: str
    plurality_context: str
    normalization_context: str
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
    if status in {"background-visible", "strengthen-ordinariness", "plurality-protect", "phase-transition-watch"}:
        return "watch"
    return {"require-human-review": "docket"}[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise BackgroundCoherenceInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise BackgroundCoherenceInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise BackgroundCoherenceInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, expected_name: str) -> LoadedArtifact:
    if path.name != expected_name:
        raise BackgroundCoherenceInputError(f"Canonical artifact-name mismatch for {path}: expected filename {expected_name}")
    if not path.exists():
        raise BackgroundCoherenceInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise BackgroundCoherenceInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise BackgroundCoherenceInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise BackgroundCoherenceInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise BackgroundCoherenceInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise BackgroundCoherenceInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise BackgroundCoherenceInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
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
            "warning": "No canonical integrity manifest fields found on background-coherence artifacts.",
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
        "warning": "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical background-coherence constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across background-coherence artifacts.",
        "divergenceReasons": sorted(set(reasons)),
        "manifests": manifests,
    }


def evaluate_target(
    row: dict[str, Any],
    *,
    normalization_rows: dict[str, dict[str, Any]],
    ambient_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> BackgroundCoherenceDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "future")

    background_readiness = _clamp01(float(row.get("backgroundReadinessScore", 0.5)))
    plurality_metabolization = _clamp01(float(row.get("pluralityMetabolizationScore", 0.5)))
    trust_ordinariness = _clamp01(float(row.get("trustOrdinarinessScore", 0.5)))

    normalization = normalization_rows.get(target_id, {})
    normalization_deservedness = _clamp01(float(normalization.get("normalizationDeservednessScore", 0.5)))
    plural_habitation_health = _clamp01(float(normalization.get("pluralHabitationHealthScore", 0.5)))
    civilizational_legibility = _clamp01(float(normalization.get("civilizationalLegibilityScore", 0.5)))

    ambient = ambient_rows.get(target_id, {})
    ambient_memory_strength = _clamp01(float(ambient.get("ambientMemoryStrengthScore", 0.5)))
    ordinary_stewardship = _clamp01(float(ambient.get("ordinaryStewardshipScore", 0.5)))

    gate = gate_rows.get(target_id, {})
    background_consolidation = _clamp01(float(gate.get("backgroundConsolidationScore", 0.5)))
    governance_coherence = _clamp01(float(gate.get("governanceCoherenceScore", 0.5)))

    coherence_score = _clamp01(
        0.16 * background_readiness
        + 0.14 * plurality_metabolization
        + 0.12 * trust_ordinariness
        + 0.10 * normalization_deservedness
        + 0.10 * plural_habitation_health
        + 0.08 * civilizational_legibility
        + 0.08 * ambient_memory_strength
        + 0.08 * ordinary_stewardship
        + 0.08 * governance_coherence
        + 0.06 * (1.0 - support_risk)
    )
    risk_score = _clamp01(
        0.12 * (1.0 - plurality_metabolization)
        + 0.12 * (1.0 - trust_ordinariness)
        + 0.10 * (1.0 - normalization_deservedness)
        + 0.08 * (1.0 - plural_habitation_health)
        + 0.08 * (1.0 - civilizational_legibility)
        + 0.10 * (1.0 - ambient_memory_strength)
        + 0.10 * (1.0 - ordinary_stewardship)
        + 0.10 * support_risk
        + 0.10 * trust_surface_risk
        + 0.10 * background_consolidation
    )

    weak_plurality_or_trust = plurality_metabolization < 0.64 or trust_ordinariness < 0.62
    keep_open = plural_habitation_health >= 0.66 and normalization_deservedness < 0.56
    ordinariness_weak = ambient_memory_strength < 0.66 or ordinary_stewardship < 0.64 or support_risk >= 0.56

    if keep_open:
        status = "keep-open"
        rule = "plural-habitation-healthy-but-normalization-not-deserved"
    elif weak_plurality_or_trust:
        status = "plurality-protect"
        rule = "background-uplift-blocked-by-weak-plurality-metabolization-or-trust-ordinariness"
    elif background_readiness >= 0.74 and background_consolidation >= 0.70 and plurality_metabolization >= 0.68 and trust_ordinariness >= 0.66:
        status = "phase-transition-watch"
        rule = "strong-background-coherence-with-healthy-plurality-watch"
    elif background_readiness >= 0.72 and plurality_metabolization >= 0.68 and trust_ordinariness >= 0.66 and not ordinariness_weak:
        status = "background-visible"
        rule = "background-coherence-visible-with-plurality-and-trust"
    elif background_readiness >= 0.70 and plurality_metabolization >= 0.66 and trust_ordinariness >= 0.64 and ordinariness_weak:
        status = "strengthen-ordinariness"
        rule = "habitability-present-but-ambient-memory-and-ordinary-stewardship-weak"
    else:
        status = "require-human-review"
        rule = "insufficient-background-coherence-legibility"

    background_context = (
        f"backgroundReadinessScore={background_readiness:.3f}, civilizationalLegibilityScore={civilizational_legibility:.3f}, normalizationDeservednessScore={normalization_deservedness:.3f}; "
        "background coherence should remain ordinary, legible, and non-priestly."
    )
    plurality_context = (
        f"pluralityMetabolizationScore={plurality_metabolization:.3f}, trustOrdinarinessScore={trust_ordinariness:.3f}; "
        "no formation uplifts to background-visible when plurality metabolization or trust ordinariness is weak."
    )
    normalization_context = (
        f"pluralHabitationHealthScore={plural_habitation_health:.3f}, normalizationDeservednessScore={normalization_deservedness:.3f}; "
        "keep-open triggers when plural habitation remains healthy but normalization is not yet deserved."
    )
    trust_context = (
        f"backgroundConsolidationScore={background_consolidation:.3f}, trustSurfaceRisk={trust_surface_risk:.3f}; "
        "phase-transition-watch appears only when background coherence is strong and plurality remains healthy."
    )
    commons_context = (
        f"ambientMemoryStrengthScore={ambient_memory_strength:.3f}, ordinaryStewardshipScore={ordinary_stewardship:.3f}, supportRisk={support_risk:.3f}, governanceCoherenceScore={governance_coherence:.3f}; "
        "recommendations remain non-coercive and non-centralizing across living-terrace, epochal-surface, terrace-seed, successor, delta, trust, sovereignty, and value context."
    )
    explanation = (
        "Recommendations are bounded background-coherence guidance only and do not declare final epochs, authorize settlement, or canonize emergent civilizational assumptions. "
        "Recommendations do not authorize institutional settlement, governance transfer, canon closure, or centralized authority claims. "
        f"targetId={target_id}, backgroundStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return BackgroundCoherenceDecision(
        target_id=target_id,
        target_type=target_type,
        background_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        background_context=background_context,
        plurality_context=plurality_context,
        normalization_context=normalization_context,
        trust_context=trust_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: BackgroundCoherenceDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "backgroundStatus": d.background_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "backgroundContext": d.background_context,
        "pluralityContext": d.plurality_context,
        "normalizationContext": d.normalization_context,
        "trustContext": d.trust_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    background_map = _load_required_artifact(BACKGROUND_COHERENCE_MAP_PATH, expected_name="background_coherence_map.json")
    normalization_report = _load_required_artifact(CIVILIZATIONAL_NORMALIZATION_REPORT_PATH, expected_name="civilizational_normalization_report.json")
    ambient_registry = _load_required_artifact(AMBIENT_MEMORY_REGISTRY_PATH, expected_name="ambient_memory_registry.json")
    normalization_gate = _load_required_artifact(NORMALIZATION_GATE_PATH, expected_name="normalization_gate.json")

    supporting = [
        ("living terrace", _load_supporting_audit(LIVING_TERRACE_AUDIT_PATH)),
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
    trust_surface_risk = _clamp01(supporting_risks[11])

    normalization_rows = {str(r.get("targetId")): r for r in _parse_rows(normalization_report.payload) if isinstance(r.get("targetId"), str)}
    ambient_rows = {str(r.get("targetId")): r for r in _parse_rows(ambient_registry.payload) if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(normalization_gate.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            normalization_rows=normalization_rows,
            ambient_rows=ambient_rows,
            gate_rows=gate_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(background_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [background_map, normalization_report, ambient_registry, normalization_gate]
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
        "living-terrace / epochal-surface / terrace-seed / successor / delta / trust / sovereignty / value context -> CoherenceLattice background-coherence and civilizational-normalization formalization -> "
        "Sophia bounded background-coherence audit -> Publisher background-coherence / ambient-memory overlays -> human/community/scientific stewardship of ordinary, habitable, non-priestly civilizational coherence"
    )
    caution = (
        "Recommendations are bounded background-coherence guidance only and do not declare final epochs, authorize settlement, "
        "or canonize emergent civilizational assumptions."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "background_coherence_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "background_coherence_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(BACKGROUND_COHERENCE_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(BACKGROUND_COHERENCE_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia background-coherence state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    BACKGROUND_COHERENCE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    BACKGROUND_COHERENCE_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {BACKGROUND_COHERENCE_AUDIT_OUT}")
    print(f"Wrote {BACKGROUND_COHERENCE_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
