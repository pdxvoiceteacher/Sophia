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

CIVIC_LITERACY_MAP_PATH = BRIDGE_DIR / "civic_literacy_map.json"
PARTICIPATION_BARRIER_REPORT_PATH = BRIDGE_DIR / "participation_barrier_report.json"
COMMONS_ACCESSIBILITY_INDEX_PATH = BRIDGE_DIR / "commons_accessibility_index.json"
EPISTEMIC_LEGIBILITY_MAP_PATH = BRIDGE_DIR / "epistemic_legibility_map.json"

SOCIAL_ENTROPY_AUDIT_PATH = BRIDGE_DIR / "social_entropy_audit.json"
FEDERATED_GOVERNANCE_AUDIT_PATH = BRIDGE_DIR / "federated_governance_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"
ARCHITECTURE_REVIEW_AUDIT_PATH = BRIDGE_DIR / "architecture_review_audit.json"

COMMONS_PARTICIPATION_AUDIT_OUT = BRIDGE_DIR / "commons_participation_audit.json"
COMMONS_PARTICIPATION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "commons_participation_recommendations.json"

COMMONS_PARTICIPATION_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "commons_participation_audit_v1.schema.json"
COMMONS_PARTICIPATION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "commons_participation_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "commons_participation_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class CommonsParticipationInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class CommonsParticipationDecision:
    target_id: str
    target_type: str
    participation_status: str
    coherence_score: float
    risk_score: float
    literacy_context: str
    participation_context: str
    accessibility_context: str
    legibility_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_rows(payload: dict[str, Any], key: str) -> list[dict[str, Any]]:
    value = payload.get(key)
    return [row for row in value if isinstance(row, dict)] if isinstance(value, list) else []


def _safe_mean(values: list[float], default: float = 0.0) -> float:
    return sum(values) / len(values) if values else default


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for doc in docs:
        for key in ("generatedAt", "created_at"):
            value = doc.get(key)
            if isinstance(value, str) and value:
                return value
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str) -> str:
    return {
        "commons-open": "watch",
        "literacy-repair": "docket",
        "accessibility-risk": "docket",
        "priesthood-risk": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise CommonsParticipationInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise CommonsParticipationInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise CommonsParticipationInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise CommonsParticipationInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise CommonsParticipationInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )

    payload = _load_json(found[0])
    _validate_provenance(payload, path=found[0])
    return LoadedArtifact(path=found[0], payload=payload, source_mode="compatibility")


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture commons-participation artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: commons-participation inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    barrier_rows: dict[str, dict[str, Any]],
    accessibility_rows: dict[str, dict[str, Any]],
    legibility_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> CommonsParticipationDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "commons-context")

    literacy_depth = _clamp01(float(row.get("literacyDepth", 0.5)))
    translation_readiness = _clamp01(float(row.get("translationReadiness", 0.5)))

    barrier = barrier_rows.get(target_id, {})
    participation_barrier = _clamp01(float(barrier.get("participationBarrier", 0.5)))
    onboarding_friction = _clamp01(float(barrier.get("onboardingFriction", 0.5)))

    accessibility = accessibility_rows.get(target_id, {})
    accessibility_gap = _clamp01(float(accessibility.get("accessibilityGap", 0.5)))
    inclusion_signal = _clamp01(float(accessibility.get("inclusionSignal", 0.5)))

    legibility = legibility_rows.get(target_id, {})
    epistemic_legibility = _clamp01(float(legibility.get("epistemicLegibility", 0.5)))
    prestige_mystique_risk = _clamp01(float(legibility.get("prestigeMystiqueRisk", 0.4)))
    exclusion_pressure = _clamp01(float(legibility.get("exclusionPressure", 0.4)))

    fairness_score = _clamp01(1.0 - 0.5 * prestige_mystique_risk - 0.5 * exclusion_pressure)

    coherence_score = _clamp01(
        0.16 * literacy_depth
        + 0.16 * translation_readiness
        + 0.16 * (1.0 - participation_barrier)
        + 0.16 * (1.0 - accessibility_gap)
        + 0.16 * epistemic_legibility
        + 0.20 * fairness_score
    )
    risk_score = _clamp01(
        0.14 * participation_barrier
        + 0.14 * onboarding_friction
        + 0.16 * accessibility_gap
        + 0.18 * prestige_mystique_risk
        + 0.18 * exclusion_pressure
        + 0.20 * system_risk
    )

    if prestige_mystique_risk >= 0.80 or exclusion_pressure >= 0.80:
        status = "require-human-review"
        rule = "anti-priesthood-and-anti-exclusion-gate"
    elif prestige_mystique_risk >= 0.70 or epistemic_legibility <= 0.34:
        status = "priesthood-risk"
        rule = "legibility-over-prestige-rule"
    elif accessibility_gap >= 0.70 or inclusion_signal <= 0.34:
        status = "accessibility-risk"
        rule = "accessibility-risk-repair"
    elif participation_barrier >= 0.58 or onboarding_friction >= 0.58 or literacy_depth <= 0.48:
        status = "literacy-repair"
        rule = "literacy-repair-priority"
    else:
        status = "commons-open"
        rule = "commons-open-watch"

    literacy_context = (
        f"literacyDepth={literacy_depth:.3f}, translationReadiness={translation_readiness:.3f}, onboardingFriction={onboarding_friction:.3f}; "
        "commons health improves through translation, simplification, and civic literacy support."
    )
    participation_context = (
        f"participationBarrier={participation_barrier:.3f}, inclusionSignal={inclusion_signal:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "participation support is favored over gatekeeping."
    )
    accessibility_context = (
        f"accessibilityGap={accessibility_gap:.3f}, inclusionSignal={inclusion_signal:.3f}; "
        "accessibility repair protects participatory legitimacy."
    )
    legibility_context = (
        f"epistemicLegibility={epistemic_legibility:.3f}, prestigeMystiqueRisk={prestige_mystique_risk:.3f}, exclusionPressure={exclusion_pressure:.3f}; "
        "civic legibility is preferred over opacity, mystique, or prestige authority."
    )
    explanation = (
        f"Commons-participation guidance is bounded civic-legibility guidance only. targetId={target_id}, "
        f"participationStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return CommonsParticipationDecision(
        target_id=target_id,
        target_type=target_type,
        participation_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        literacy_context=literacy_context,
        participation_context=participation_context,
        accessibility_context=accessibility_context,
        legibility_context=legibility_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: CommonsParticipationDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "participationStatus": d.participation_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "literacyContext": d.literacy_context,
        "participationContext": d.participation_context,
        "accessibilityContext": d.accessibility_context,
        "legibilityContext": d.legibility_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    literacy_map = _load_required_artifact(
        CIVIC_LITERACY_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "literacy_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    barrier_report = _load_required_artifact(
        PARTICIPATION_BARRIER_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "barrier_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    accessibility_index = _load_required_artifact(
        COMMONS_ACCESSIBILITY_INDEX_PATH,
        compatibility_paths=(BRIDGE_DIR / "accessibility_index.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    legibility_map = _load_required_artifact(
        EPISTEMIC_LEGIBILITY_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "legibility_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    social = _load_json(SOCIAL_ENTROPY_AUDIT_PATH)
    federation = _load_json(FEDERATED_GOVERNANCE_AUDIT_PATH)
    value = _load_json(VALUE_ALIGNMENT_AUDIT_PATH)
    architecture = _load_json(ARCHITECTURE_REVIEW_AUDIT_PATH)

    social_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(social, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    federation_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(federation, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    value_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(value, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    architecture_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(architecture, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.25 * social_risk + 0.25 * federation_risk + 0.25 * value_risk + 0.25 * architecture_risk)

    barrier_rows = {str(r.get("targetId")): r for r in _parse_rows(barrier_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    accessibility_rows = {str(r.get("targetId")): r for r in _parse_rows(accessibility_index.payload, "targets") if isinstance(r.get("targetId"), str)}
    legibility_rows = {str(r.get("targetId")): r for r in _parse_rows(legibility_map.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            barrier_rows=barrier_rows,
            accessibility_rows=accessibility_rows,
            legibility_rows=legibility_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(literacy_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [literacy_map, barrier_report, accessibility_index, legibility_map]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(literacy_map.payload, barrier_report.payload, accessibility_index.payload, legibility_map.payload)

    metadata = {
        "inputMode": mode,
        "inputModeWarning": warning,
        "systemRisk": round(system_risk, 6),
        "inputArtifacts": [
            {
                "path": str(a.path.relative_to(REPO_ROOT)) if a.path.is_relative_to(REPO_ROOT) else str(a.path),
                "sourceMode": a.source_mode,
                "schemaVersion": str(a.payload.get("schemaVersion")),
                "producerRepo": str(a.payload.get("producerRepo")),
                "producerModule": str(a.payload.get("producerModule")),
                "producerCommit": str(a.payload.get("producerCommit")),
                "generatedAt": str(a.payload.get("generatedAt")),
            }
            for a in loaded
        ],
    }

    phaselock = (
        "social entropy / federation / value / architecture context -> CoherenceLattice commons-participation formalization -> "
        "Sophia commons-participation audit -> Publisher civic-legibility overlays -> human/community repair and participation support"
    )
    caution = (
        "Commons-participation recommendations are bounded civic-legibility guidance only and do not authorize exclusion, "
        "ranking of persons, or closure of participation rights."
    )

    audit_payload = {
        "schema": "commons_participation_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "commons_participation_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(COMMONS_PARTICIPATION_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(COMMONS_PARTICIPATION_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia commons-participation state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    COMMONS_PARTICIPATION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    COMMONS_PARTICIPATION_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {COMMONS_PARTICIPATION_AUDIT_OUT}")
    print(f"Wrote {COMMONS_PARTICIPATION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
