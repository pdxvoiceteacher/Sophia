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

SOCIAL_ENTROPY_MAP_PATH = BRIDGE_DIR / "social_entropy_map.json"
CIVIC_COHESION_REPORT_PATH = BRIDGE_DIR / "civic_cohesion_report.json"
LEGITIMACY_DRIFT_REPORT_PATH = BRIDGE_DIR / "legitimacy_drift_report.json"
REVIEW_PARTICIPATION_RISK_MAP_PATH = BRIDGE_DIR / "review_participation_risk_map.json"

COLLABORATIVE_REVIEW_AUDIT_PATH = BRIDGE_DIR / "collaborative_review_audit.json"
THEORY_CORPUS_AUDIT_PATH = BRIDGE_DIR / "theory_corpus_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"
ARCHITECTURE_REVIEW_AUDIT_PATH = BRIDGE_DIR / "architecture_review_audit.json"

SOCIAL_ENTROPY_AUDIT_OUT = BRIDGE_DIR / "social_entropy_audit.json"
SOCIAL_ENTROPY_RECOMMENDATIONS_OUT = BRIDGE_DIR / "social_entropy_recommendations.json"

SOCIAL_ENTROPY_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "social_entropy_audit_v1.schema.json"
SOCIAL_ENTROPY_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "social_entropy_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "social_entropy_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class SocialEntropyInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class SocialEntropyDecision:
    target_id: str
    target_type: str
    social_status: str
    coherence_score: float
    risk_score: float
    participation_context: str
    dissent_context: str
    legitimacy_context: str
    fairness_context: str
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
        "cohesion-healthy": "watch",
        "repair-priority": "docket",
        "legitimacy-risk": "docket",
        "participation-brittle": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise SocialEntropyInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise SocialEntropyInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise SocialEntropyInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise SocialEntropyInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise SocialEntropyInputError(
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
        return "fixture", "Inputs are fixture social-entropy artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: social-entropy inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    cohesion_rows: dict[str, dict[str, Any]],
    legitimacy_rows: dict[str, dict[str, Any]],
    participation_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> SocialEntropyDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "social-context")

    social_stability = _clamp01(float(row.get("socialStability", 0.5)))
    repair_readiness = _clamp01(float(row.get("repairReadiness", 0.5)))

    cohesion = cohesion_rows.get(target_id, {})
    participation_coverage = _clamp01(float(cohesion.get("participationCoverage", 0.5)))
    dissent_safety = _clamp01(float(cohesion.get("dissentSafety", 0.5)))

    legitimacy = legitimacy_rows.get(target_id, {})
    legitimacy_drift = _clamp01(float(legitimacy.get("legitimacyDrift", 0.5)))
    transparency_gap = _clamp01(float(legitimacy.get("transparencyGap", 0.5)))

    participation = participation_rows.get(target_id, {})
    participation_fragility = _clamp01(float(participation.get("participationFragility", 0.5)))
    suppression_pressure = _clamp01(float(participation.get("suppressionPressure", 0.4)))
    coercive_unity_signal = _clamp01(float(participation.get("coerciveUnitySignal", 0.4)))

    fairness_score = _clamp01(1.0 - 0.5 * suppression_pressure - 0.5 * coercive_unity_signal)

    coherence = _clamp01(
        0.17 * social_stability
        + 0.16 * repair_readiness
        + 0.17 * participation_coverage
        + 0.16 * dissent_safety
        + 0.17 * (1.0 - legitimacy_drift)
        + 0.17 * fairness_score
    )
    risk = _clamp01(
        0.16 * legitimacy_drift
        + 0.14 * transparency_gap
        + 0.16 * participation_fragility
        + 0.18 * suppression_pressure
        + 0.18 * coercive_unity_signal
        + 0.18 * system_risk
    )

    if suppression_pressure >= 0.80 or coercive_unity_signal >= 0.80:
        status = "require-human-review"
        rule = "anti-suppression-and-anti-coercive-unity-gate"
    elif legitimacy_drift >= 0.74:
        status = "legitimacy-risk"
        rule = "legitimacy-drift-repair-priority"
    elif participation_fragility >= 0.70 or participation_coverage <= 0.34:
        status = "participation-brittle"
        rule = "participation-brittleness-response"
    elif repair_readiness >= 0.60 and (legitimacy_drift >= 0.56 or transparency_gap >= 0.56 or dissent_safety <= 0.50):
        status = "repair-priority"
        rule = "repair-priority-with-transparency-and-dissent-protection"
    else:
        status = "cohesion-healthy"
        rule = "cohesion-health-watch"

    participation_context = (
        f"participationCoverage={participation_coverage:.3f}, participationFragility={participation_fragility:.3f}, repairReadiness={repair_readiness:.3f}; "
        "stewardship resilience depends on participation support and redundancy."
    )
    dissent_context = (
        f"dissentSafety={dissent_safety:.3f}, suppressionPressure={suppression_pressure:.3f}, coerciveUnitySignal={coercive_unity_signal:.3f}; "
        "dissent is protected and cannot be resolved through suppression pressure."
    )
    legitimacy_context = (
        f"legitimacyDrift={legitimacy_drift:.3f}, transparencyGap={transparency_gap:.3f}, socialStability={social_stability:.3f}; "
        "legitimacy repair favors transparency and civic trust restoration."
    )
    fairness_context = (
        f"fairnessScore={fairness_score:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "recommendations are bounded civic-repair guidance and do not authorize censorship or coercive unity measures."
    )
    explanation = (
        f"Social-entropy guidance is bounded civic-repair guidance only. targetId={target_id}, "
        f"socialStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return SocialEntropyDecision(
        target_id=target_id,
        target_type=target_type,
        social_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        participation_context=participation_context,
        dissent_context=dissent_context,
        legitimacy_context=legitimacy_context,
        fairness_context=fairness_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: SocialEntropyDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "socialStatus": d.social_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "participationContext": d.participation_context,
        "dissentContext": d.dissent_context,
        "legitimacyContext": d.legitimacy_context,
        "fairnessContext": d.fairness_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    entropy_map = _load_required_artifact(
        SOCIAL_ENTROPY_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "entropy_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    cohesion_report = _load_required_artifact(
        CIVIC_COHESION_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "cohesion_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    legitimacy_report = _load_required_artifact(
        LEGITIMACY_DRIFT_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "drift_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    participation_risk = _load_required_artifact(
        REVIEW_PARTICIPATION_RISK_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "participation_risk_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    collaborative = _load_json(COLLABORATIVE_REVIEW_AUDIT_PATH)
    theory = _load_json(THEORY_CORPUS_AUDIT_PATH)
    value = _load_json(VALUE_ALIGNMENT_AUDIT_PATH)
    architecture = _load_json(ARCHITECTURE_REVIEW_AUDIT_PATH)

    collaborative_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(collaborative, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    theory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(theory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    value_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(value, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    architecture_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(architecture, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.25 * collaborative_risk + 0.25 * theory_risk + 0.25 * value_risk + 0.25 * architecture_risk)

    cohesion_rows = {str(r.get("targetId")): r for r in _parse_rows(cohesion_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    legitimacy_rows = {str(r.get("targetId")): r for r in _parse_rows(legitimacy_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    participation_rows = {str(r.get("targetId")): r for r in _parse_rows(participation_risk.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            cohesion_rows=cohesion_rows,
            legitimacy_rows=legitimacy_rows,
            participation_rows=participation_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(entropy_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [entropy_map, cohesion_report, legitimacy_report, participation_risk]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(entropy_map.payload, cohesion_report.payload, legitimacy_report.payload, participation_risk.payload)

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
        "collaborative + theory + value + architecture review state -> social-entropy synthesis -> "
        "Sophia social-entropy audit -> Publisher bounded governance overlays -> human/community review"
    )
    caution = (
        "Social-entropy recommendations are bounded civic-repair guidance only and do not authorize suppression, censorship, "
        "or coercive unity measures."
    )

    audit_payload = {
        "schema": "social_entropy_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "social_entropy_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(SOCIAL_ENTROPY_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(SOCIAL_ENTROPY_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia social-entropy state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    SOCIAL_ENTROPY_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    SOCIAL_ENTROPY_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {SOCIAL_ENTROPY_AUDIT_OUT}")
    print(f"Wrote {SOCIAL_ENTROPY_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
