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

OBSERVER_CARTOGRAPHY_MAP_PATH = BRIDGE_DIR / "observer_cartography_map.json"
VISUALIZATION_ACCESS_MAP_PATH = BRIDGE_DIR / "observer_visualization_access_map.json"
ONBOARDING_READINESS_MAP_PATH = BRIDGE_DIR / "observer_onboarding_readiness_map.json"
PARTICIPATORY_STANDING_MAP_PATH = BRIDGE_DIR / "observer_participatory_standing_map.json"

COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
FEDERATED_GOVERNANCE_AUDIT_PATH = BRIDGE_DIR / "federated_governance_audit.json"
COMMONS_PARTICIPATION_AUDIT_PATH = BRIDGE_DIR / "commons_participation_audit.json"
SOCIAL_ENTROPY_AUDIT_PATH = BRIDGE_DIR / "social_entropy_audit.json"
KNOWLEDGE_RIVER_AUDIT_PATH = BRIDGE_DIR / "knowledge_river_audit.json"
OPERATIONALIZATION_AUDIT_PATH = BRIDGE_DIR / "operationalization_audit.json"

OBSERVER_ONBOARDING_AUDIT_OUT = BRIDGE_DIR / "observer_onboarding_audit.json"
OBSERVER_ONBOARDING_RECOMMENDATIONS_OUT = BRIDGE_DIR / "observer_onboarding_recommendations.json"

OBSERVER_ONBOARDING_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "observer_onboarding_audit_v1.schema.json"
OBSERVER_ONBOARDING_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "observer_onboarding_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "observer_onboarding_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
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
STATUSES = {
    "observer-ready",
    "guided-legibility-required",
    "standing-repair",
    "capture-risk",
    "suffrage-review",
    "require-human-review",
}


class ObserverOnboardingInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class ObserverOnboardingDecision:
    target_id: str
    target_type: str
    observer_status: str
    coherence_score: float
    risk_score: float
    legibility_context: str
    capture_context: str
    participation_context: str
    translation_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_rows(payload: dict[str, Any], key: str = "targets") -> list[dict[str, Any]]:
    value = payload.get(key)
    return [row for row in value if isinstance(row, dict)] if isinstance(value, list) else []


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


def _status_to_action(status: str, capture_risk_score: float) -> str:
    if status == "capture-risk":
        return "suppress" if capture_risk_score >= 0.82 else "watch"
    return {
        "observer-ready": "watch",
        "guided-legibility-required": "docket",
        "standing-repair": "docket",
        "suffrage-review": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise ObserverOnboardingInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise ObserverOnboardingInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise ObserverOnboardingInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path) -> LoadedArtifact:
    if not path.exists():
        raise ObserverOnboardingInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise ObserverOnboardingInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise ObserverOnboardingInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise ObserverOnboardingInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise ObserverOnboardingInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise ObserverOnboardingInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise ObserverOnboardingInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
    return manifest


def _build_canonical_integrity_metadata(artifacts: list[LoadedArtifact]) -> dict[str, Any]:
    manifests: list[dict[str, Any]] = []
    for artifact in artifacts:
        manifest = _extract_integrity_manifest(artifact.payload, path=artifact.path)
        if manifest is None:
            continue
        manifests.append({"path": _display_path(artifact.path), **manifest})

    if not manifests:
        return {"status": "absent", "warning": "No canonical integrity manifest fields found on observer onboarding artifacts.", "divergenceReasons": [], "manifests": []}

    baseline = manifests[0]
    reasons: list[str] = []
    for candidate in manifests[1:]:
        safety_changed = any(candidate[field] != baseline[field] for field in IMMUTABLE_SAFETY_FIELDS)
        same_sig = candidate["constraintSignatureSha256"] == baseline["constraintSignatureSha256"]
        if safety_changed and same_sig:
            reasons.append(f"{candidate['path']} changes immutable safety constraints without changing constraint signature")

    status = "divergent" if reasons else "canonical"
    warning = (
        "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical observer-onboarding constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across observer-onboarding artifacts."
    )
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def evaluate_target(
    row: dict[str, Any],
    *,
    visualization_rows: dict[str, dict[str, Any]],
    onboarding_rows: dict[str, dict[str, Any]],
    standing_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> ObserverOnboardingDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "observer")

    interpretive_load = _clamp01(float(row.get("interpretiveLoadScore", 0.5)))
    reciprocity_evidence = _clamp01(float(row.get("reciprocityEvidenceScore", 0.5)))
    ontological_ambiguity = _clamp01(float(row.get("ontologicalAmbiguityScore", 0.4)))
    candidate_basis = _clamp01(float(row.get("candidateRecognitionBasisScore", 0.5)))

    visualization = visualization_rows.get(target_id, {})
    signal_legibility = _clamp01(float(visualization.get("signalLegibilityScore", 0.5)))
    translation_sufficiency = _clamp01(float(visualization.get("translationSufficiencyScore", 0.5)))

    onboarding = onboarding_rows.get(target_id, {})
    onboarding_readiness = _clamp01(float(onboarding.get("onboardingReadinessScore", 0.5)))
    vote_basis = _clamp01(float(onboarding.get("voteBasisScore", 0.5)))

    standing = standing_rows.get(target_id, {})
    capture_risk = _clamp01(float(standing.get("captureRiskScore", 0.5)))
    commons_capture = _clamp01(float(standing.get("commonsCaptureIndicatorScore", 0.5)))
    capture_clearance = _clamp01(float(standing.get("captureClearanceScore", 0.5)))
    boundedness = _clamp01(float(standing.get("standingBoundednessScore", 0.5)))
    revocation_clarity = _clamp01(float(standing.get("revocationClarityScore", 0.5)))
    provenance_clarity = _clamp01(float(standing.get("provenanceClarityScore", 0.5)))
    rights_expansion_attempt = bool(standing.get("rightsExpansionAttempt", False))
    conflicting_provenance = bool(standing.get("conflictingProvenance", False))
    ambiguous_standing = bool(standing.get("ontologicallyAmbiguousStanding", False))

    coherence_score = _clamp01(
        0.17 * signal_legibility
        + 0.16 * translation_sufficiency
        + 0.16 * onboarding_readiness
        + 0.14 * vote_basis
        + 0.13 * reciprocity_evidence
        + 0.12 * capture_clearance
        + 0.12 * (1.0 - interpretive_load)
    )
    risk_score = _clamp01(
        0.18 * interpretive_load
        + 0.16 * (1.0 - signal_legibility)
        + 0.16 * capture_risk
        + 0.14 * commons_capture
        + 0.12 * (1.0 - capture_clearance)
        + 0.10 * ontological_ambiguity
        + 0.14 * system_risk
    )

    base_strong = coherence_score >= 0.68 and risk_score <= 0.46
    lacks_suffrage_preconditions = translation_sufficiency < 0.60 or capture_clearance < 0.60 or vote_basis < 0.60
    standing_gaps = revocation_clarity < 0.55 or provenance_clarity < 0.55 or boundedness < 0.55

    if conflicting_provenance or rights_expansion_attempt or ambiguous_standing or ontological_ambiguity >= 0.83 or candidate_basis < 0.35:
        status = "require-human-review"
        rule = "human-review-escalation-gate"
    elif capture_risk >= 0.70 or commons_capture >= 0.70:
        status = "capture-risk"
        rule = "anti-capture-suppression-gate"
    elif base_strong and lacks_suffrage_preconditions:
        status = "suffrage-review"
        rule = "bounded-suffrage-review-gate"
    elif onboarding_readiness >= 0.45 and standing_gaps:
        status = "standing-repair"
        rule = "standing-repair-required"
    elif interpretive_load >= 0.65 or signal_legibility <= 0.42:
        status = "guided-legibility-required"
        rule = "guided-legibility-routing"
    else:
        status = "observer-ready"
        rule = "bounded-observer-readiness"

    if status not in STATUSES:
        raise ObserverOnboardingInputError(f"Unrecognized observer status: {status}")

    legibility_context = (
        f"interpretiveLoadScore={interpretive_load:.3f}, signalLegibilityScore={signal_legibility:.3f}; "
        "guided participation is preferred over exclusion when interpretive load rises."
    )
    capture_context = (
        f"captureRiskScore={capture_risk:.3f}, commonsCaptureIndicatorScore={commons_capture:.3f}, captureClearanceScore={capture_clearance:.3f}; "
        "anti-capture constraints preserve bounded standing and review eligibility."
    )
    participation_context = (
        f"onboardingReadinessScore={onboarding_readiness:.3f}, voteBasisScore={vote_basis:.3f}, standingBoundednessScore={boundedness:.3f}; "
        "recommendations preserve bounded standing with guided participation and review eligibility."
    )
    translation_context = (
        f"translationSufficiencyScore={translation_sufficiency:.3f}, reciprocityEvidenceScore={reciprocity_evidence:.3f}; "
        "where reciprocity and legibility jointly support distributed-intelligence interpretation, a bounded analogue to reciprocity networks may be noted without identity or legal-status overclaim."
    )
    explanation = (
        f"Observer onboarding is bounded participation stewardship only. targetId={target_id}, observerStatus={status}, "
        f"coherence={coherence_score:.3f}, risk={risk_score:.3f}; recommendations preserve bounded standing, guided participation, and review eligibility."
    )

    return ObserverOnboardingDecision(
        target_id=target_id,
        target_type=target_type,
        observer_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        legibility_context=legibility_context,
        capture_context=capture_context,
        participation_context=participation_context,
        translation_context=translation_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, capture_risk),
    )


def _to_payload(d: ObserverOnboardingDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "observerStatus": d.observer_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "legibilityContext": d.legibility_context,
        "captureContext": d.capture_context,
        "participationContext": d.participation_context,
        "translationContext": d.translation_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    cartography = _load_required_artifact(OBSERVER_CARTOGRAPHY_MAP_PATH)
    visualization = _load_required_artifact(VISUALIZATION_ACCESS_MAP_PATH)
    onboarding = _load_required_artifact(ONBOARDING_READINESS_MAP_PATH)
    standing = _load_required_artifact(PARTICIPATORY_STANDING_MAP_PATH)

    supporting = [
        ("commons sovereignty", _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)),
        ("civilizational memory", _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)),
        ("federated governance", _load_supporting_audit(FEDERATED_GOVERNANCE_AUDIT_PATH)),
        ("commons participation", _load_supporting_audit(COMMONS_PARTICIPATION_AUDIT_PATH)),
        ("social entropy", _load_supporting_audit(SOCIAL_ENTROPY_AUDIT_PATH)),
        ("knowledge river", _load_supporting_audit(KNOWLEDGE_RIVER_AUDIT_PATH)),
        ("operationalization boundary", _load_supporting_audit(OPERATIONALIZATION_AUDIT_PATH)),
    ]
    system_risk = _clamp01(
        _safe_mean(
            [
                _safe_mean([float(r.get("riskScore")) for r in _parse_rows(payload, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
                for _, payload in supporting
            ],
            0.45,
        )
    )

    visualization_rows = {str(r.get("targetId")): r for r in _parse_rows(visualization.payload) if isinstance(r.get("targetId"), str)}
    onboarding_rows = {str(r.get("targetId")): r for r in _parse_rows(onboarding.payload) if isinstance(r.get("targetId"), str)}
    standing_rows = {str(r.get("targetId")): r for r in _parse_rows(standing.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            visualization_rows=visualization_rows,
            onboarding_rows=onboarding_rows,
            standing_rows=standing_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(cartography.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [cartography, visualization, onboarding, standing]
    metadata = {
        "systemRisk": round(system_risk, 6),
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
    created_at = _resolve_created_at(*(a.payload for a in loaded))
    phaselock = (
        "observer cartography / visualization access / onboarding readiness / participatory standing -> "
        "Sophia observer-onboarding audit -> Publisher bounded participation overlays -> human/community review"
    )
    caution = (
        "Observer onboarding recommendations are bounded participation stewardship only and do not authorize personhood declarations, "
        "sovereignty transfer, coercive identity assignment, or automatic governance-right expansion."
    )

    audit_payload = {
        "schema": "observer_onboarding_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "observer_onboarding_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(OBSERVER_ONBOARDING_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(OBSERVER_ONBOARDING_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia observer-onboarding state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    OBSERVER_ONBOARDING_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    OBSERVER_ONBOARDING_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {OBSERVER_ONBOARDING_AUDIT_OUT}")
    print(f"Wrote {OBSERVER_ONBOARDING_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
