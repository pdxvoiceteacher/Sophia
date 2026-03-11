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

NEW_DELTA_STABILIZATION_MAP_PATH = BRIDGE_DIR / "new_delta_stabilization_map.json"
FRAGMENTED_RENEWAL_REVERSION_REPORT_PATH = BRIDGE_DIR / "fragmented_renewal_reversion_report.json"
CROSSING_RESILIENCE_SCORECARD_PATH = BRIDGE_DIR / "crossing_resilience_scorecard.json"
POST_CROSSING_GOVERNANCE_GATE_PATH = BRIDGE_DIR / "post_crossing_governance_gate.json"

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

NEW_DELTA_STABILIZATION_AUDIT_OUT = BRIDGE_DIR / "new_delta_stabilization_audit.json"
NEW_DELTA_STABILIZATION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "new_delta_stabilization_recommendations.json"

NEW_DELTA_STABILIZATION_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "new_delta_stabilization_audit_v1.schema.json"
NEW_DELTA_STABILIZATION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "new_delta_stabilization_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "new_delta_stabilization_v1"
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


class NewDeltaStabilizationInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class NewDeltaStabilizationDecision:
    target_id: str
    target_type: str
    stabilization_status: str
    coherence_score: float
    risk_score: float
    stabilization_context: str
    plurality_context: str
    reversion_context: str
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
    if status == "fragmented-reversion":
        return "suppress" if risk_score >= 0.78 else "watch"
    if status in {"stabilization-visible", "strengthen-resilience", "plurality-protect", "phase-transition-watch"}:
        return "watch"
    return {"require-human-review": "docket"}[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise NewDeltaStabilizationInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise NewDeltaStabilizationInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise NewDeltaStabilizationInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, expected_name: str) -> LoadedArtifact:
    if path.name != expected_name:
        raise NewDeltaStabilizationInputError(f"Canonical artifact-name mismatch for {path}: expected filename {expected_name}")
    if not path.exists():
        raise NewDeltaStabilizationInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise NewDeltaStabilizationInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise NewDeltaStabilizationInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise NewDeltaStabilizationInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise NewDeltaStabilizationInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise NewDeltaStabilizationInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise NewDeltaStabilizationInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
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
            "warning": "No canonical integrity manifest fields found on new-delta-stabilization artifacts.",
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
        "warning": "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical new-delta-stabilization constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across new-delta-stabilization artifacts.",
        "divergenceReasons": sorted(set(reasons)),
        "manifests": manifests,
    }


def evaluate_target(
    row: dict[str, Any],
    *,
    reversion_rows: dict[str, dict[str, Any]],
    resilience_rows: dict[str, dict[str, Any]],
    governance_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> NewDeltaStabilizationDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "future")

    stabilization_readiness = _clamp01(float(row.get("stabilizationReadinessScore", 0.5)))
    plurality_retention = _clamp01(float(row.get("pluralityRetentionScore", 0.5)))
    trust_legibility = _clamp01(float(row.get("trustLegibilityScore", 0.5)))

    reversion = reversion_rows.get(target_id, {})
    trust_repair = _clamp01(float(reversion.get("trustRepairScore", 0.5)))
    memory_continuity = _clamp01(float(reversion.get("memoryContinuityScore", 0.5)))
    renewal_scattering = _clamp01(float(reversion.get("renewalScatteringScore", 0.5)))

    resilience = resilience_rows.get(target_id, {})
    resilience_durability = _clamp01(float(resilience.get("resilienceDurabilityScore", 0.5)))
    institutional_repair = _clamp01(float(resilience.get("institutionalRepairScore", 0.5)))

    governance = governance_rows.get(target_id, {})
    governance_coherence = _clamp01(float(governance.get("governanceCoherenceScore", 0.5)))
    transition_pressure = _clamp01(float(governance.get("transitionPressureScore", 0.5)))

    coherence_score = _clamp01(
        0.16 * stabilization_readiness
        + 0.14 * plurality_retention
        + 0.12 * trust_legibility
        + 0.12 * trust_repair
        + 0.10 * memory_continuity
        + 0.12 * resilience_durability
        + 0.08 * institutional_repair
        + 0.08 * governance_coherence
        + 0.08 * (1.0 - support_risk)
    )
    risk_score = _clamp01(
        0.12 * (1.0 - plurality_retention)
        + 0.12 * (1.0 - trust_legibility)
        + 0.12 * (1.0 - trust_repair)
        + 0.12 * (1.0 - memory_continuity)
        + 0.14 * renewal_scattering
        + 0.10 * (1.0 - resilience_durability)
        + 0.08 * transition_pressure
        + 0.10 * support_risk
        + 0.10 * trust_surface_risk
    )

    fragmented_reversion = trust_repair < 0.56 or memory_continuity < 0.58 or renewal_scattering >= 0.66
    weak_plurality_or_trust = plurality_retention < 0.64 or trust_legibility < 0.62
    support_not_robust = resilience_durability < 0.66 or institutional_repair < 0.64 or support_risk >= 0.56

    if fragmented_reversion:
        status = "fragmented-reversion"
        rule = "trust-repair-or-memory-break-or-renewal-scattering-reversion"
    elif weak_plurality_or_trust:
        status = "plurality-protect"
        rule = "stabilization-uplift-blocked-by-weak-plurality-or-trust-legibility"
    elif stabilization_readiness >= 0.74 and resilience_durability >= 0.72 and plurality_retention >= 0.68 and trust_legibility >= 0.66 and governance_coherence >= 0.68 and support_not_robust:
        status = "phase-transition-watch"
        rule = "strong-stabilization-with-healthy-plurality-and-durable-resilience-watch"
    elif stabilization_readiness >= 0.72 and plurality_retention >= 0.68 and trust_legibility >= 0.66 and not support_not_robust:
        status = "stabilization-visible"
        rule = "durable-post-crossing-stabilization-with-plurality-and-trust-legibility"
    elif stabilization_readiness >= 0.70 and plurality_retention >= 0.66 and trust_legibility >= 0.64 and support_not_robust:
        status = "strengthen-resilience"
        rule = "support-present-but-not-yet-robust"
    else:
        status = "require-human-review"
        rule = "insufficient-post-crossing-stabilization-legibility"

    stabilization_context = (
        f"stabilizationReadinessScore={stabilization_readiness:.3f}, resilienceDurabilityScore={resilience_durability:.3f}, institutionalRepairScore={institutional_repair:.3f}; "
        "durable stabilization requires robust resilience, not brittle crossing visibility."
    )
    plurality_context = (
        f"pluralityRetentionScore={plurality_retention:.3f}, trustLegibilityScore={trust_legibility:.3f}; "
        "no crossing uplifts to stabilization-visible when plurality retention or trust legibility is weak."
    )
    reversion_context = (
        f"trustRepairScore={trust_repair:.3f}, memoryContinuityScore={memory_continuity:.3f}, renewalScatteringScore={renewal_scattering:.3f}; "
        "fragmented-reversion triggers when trust repair fails, memory continuity breaks, or renewal scattering rises."
    )
    trust_context = (
        f"governanceCoherenceScore={governance_coherence:.3f}, transitionPressureScore={transition_pressure:.3f}, trustSurfaceRisk={trust_surface_risk:.3f}; "
        "strong stabilization routes to phase-transition-watch only when plurality remains healthy and resilience is durable."
    )
    commons_context = (
        f"supportRisk={support_risk:.3f}; recommendations remain non-coercive and non-centralizing across crossing, successor, terrace, delta, trust, sovereignty, and value context."
    )
    explanation = (
        "Recommendations are bounded post-crossing stabilization guidance only and do not declare new epochs, authorize successor rule, or canonize emergent futures. "
        "Recommendations do not authorize institutional displacement, centralized succession, governance transfer, or canon closure. "
        f"targetId={target_id}, stabilizationStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return NewDeltaStabilizationDecision(
        target_id=target_id,
        target_type=target_type,
        stabilization_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        stabilization_context=stabilization_context,
        plurality_context=plurality_context,
        reversion_context=reversion_context,
        trust_context=trust_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: NewDeltaStabilizationDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "stabilizationStatus": d.stabilization_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "stabilizationContext": d.stabilization_context,
        "pluralityContext": d.plurality_context,
        "reversionContext": d.reversion_context,
        "trustContext": d.trust_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    stabilization_map = _load_required_artifact(NEW_DELTA_STABILIZATION_MAP_PATH, expected_name="new_delta_stabilization_map.json")
    reversion_report = _load_required_artifact(FRAGMENTED_RENEWAL_REVERSION_REPORT_PATH, expected_name="fragmented_renewal_reversion_report.json")
    resilience_scorecard = _load_required_artifact(CROSSING_RESILIENCE_SCORECARD_PATH, expected_name="crossing_resilience_scorecard.json")
    governance_gate = _load_required_artifact(POST_CROSSING_GOVERNANCE_GATE_PATH, expected_name="post_crossing_governance_gate.json")

    supporting = [
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
    trust_surface_risk = _clamp01(supporting_risks[7])

    reversion_rows = {str(r.get("targetId")): r for r in _parse_rows(reversion_report.payload) if isinstance(r.get("targetId"), str)}
    resilience_rows = {str(r.get("targetId")): r for r in _parse_rows(resilience_scorecard.payload) if isinstance(r.get("targetId"), str)}
    governance_rows = {str(r.get("targetId")): r for r in _parse_rows(governance_gate.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            reversion_rows=reversion_rows,
            resilience_rows=resilience_rows,
            governance_rows=governance_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(stabilization_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [stabilization_map, reversion_report, resilience_scorecard, governance_gate]
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
        "crossing / successor / terrace / delta / trust / sovereignty / value context -> CoherenceLattice new-delta stabilization and fragmented-reversion formalization -> "
        "Sophia bounded stabilization audit -> Publisher stabilization/reversion overlays -> human/community/scientific stewardship of durable and non-durable post-crossing futures"
    )
    caution = (
        "Recommendations are bounded post-crossing stabilization guidance only and do not declare new epochs, authorize successor rule, "
        "or canonize emergent futures."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "new_delta_stabilization_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "new_delta_stabilization_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(NEW_DELTA_STABILIZATION_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(NEW_DELTA_STABILIZATION_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia new-delta stabilization state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    NEW_DELTA_STABILIZATION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    NEW_DELTA_STABILIZATION_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {NEW_DELTA_STABILIZATION_AUDIT_OUT}")
    print(f"Wrote {NEW_DELTA_STABILIZATION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
