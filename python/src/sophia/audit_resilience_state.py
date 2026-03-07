from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

SUCCESSION_STATE_MAP_PATH = BRIDGE_DIR / "succession_state_map.json"
SUCCESSION_STATE_SUMMARY_PATH = BRIDGE_DIR / "succession_state_summary.json"
QUORUM_RESILIENCE_REPORT_PATH = BRIDGE_DIR / "quorum_resilience_report.json"
CONTINUITY_ROSTER_CANDIDATES_PATH = BRIDGE_DIR / "continuity_roster_candidates.json"
GOVERNANCE_AUDIT_PATH = BRIDGE_DIR / "governance_audit.json"
REVIEWER_BEHAVIOR_AUDIT_PATH = BRIDGE_DIR / "reviewer_behavior_audit.json"
CONSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "constitutional_audit.json"
CONTINUITY_MODE_ASSESSMENT_PATH = BRIDGE_DIR / "continuity_mode_assessment.json"

RESILIENCE_AUDIT_OUT = BRIDGE_DIR / "resilience_audit.json"
SUCCESSION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "succession_recommendations.json"

RESILIENCE_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "resilience_audit_v1.schema.json"
SUCCESSION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "succession_recommendations_v1.schema.json"


@dataclass(slots=True)
class ResilienceDecision:
    resilience_id: str | None
    reviewer_id: str | None
    resilience_status: str
    audit_status: str
    coherence_score: float
    risk_score: float
    quorum_depth_context: dict[str, Any]
    anti_capture_risk: float
    governance_fragility_context: dict[str, Any]
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for doc in docs:
        ts = doc.get("created_at") if isinstance(doc, dict) else None
        if isinstance(ts, str) and ts:
            return ts
    return "1970-01-01T00:00:00Z"


def _safe_mean(values: list[float], default: float = 0.0) -> float:
    if not values:
        return default
    return sum(values) / len(values)


def _status_to_action(status: str) -> str:
    return {
        "continue": "watch",
        "queue-continuity-review": "docket",
        "increase-watch": "watch",
        "freeze-governance-expansion": "watch",
        "degraded-mode": "watch",
        "require-human-emergency-review": "docket",
    }[status]


def _system_signals(governance: dict[str, Any], reviewer_behavior: dict[str, Any], constitutional: dict[str, Any]) -> tuple[float, float, float]:
    gov_rows = governance.get("audits") if isinstance(governance.get("audits"), list) else []
    behavior_rows = reviewer_behavior.get("reviewers") if isinstance(reviewer_behavior.get("reviewers"), list) else []
    const_rows = constitutional.get("evaluations") if isinstance(constitutional.get("evaluations"), list) else []

    gov_risk = _safe_mean(
        [float(r.get("riskScore")) for r in gov_rows if isinstance(r, dict) and isinstance(r.get("riskScore"), (int, float))],
        0.3,
    )
    behavior_risk = _safe_mean(
        [float(r.get("overrideRisk")) for r in behavior_rows if isinstance(r, dict) and isinstance(r.get("overrideRisk"), (int, float))],
        0.25,
    )
    capture_risk = _safe_mean(
        [float(r.get("captureRisk")) for r in const_rows if isinstance(r, dict) and isinstance(r.get("captureRisk"), (int, float))],
        0.35,
    )
    return _clamp01(gov_risk), _clamp01(behavior_risk), _clamp01(capture_risk)


def evaluate_target(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    quorum_report: dict[str, Any],
    continuity_mode: dict[str, Any],
    system_gov_risk: float,
    system_behavior_risk: float,
    system_capture_risk: float,
) -> ResilienceDecision:
    resilience_id = str(row.get("resilienceId") or "resilience:unknown")
    succession_readiness = _clamp01(float(row.get("successionReadinessScore", summary.get("meanSuccessionReadinessScore", 0.5))))
    fragility = _clamp01(float(row.get("governanceFragilityScore", summary.get("meanGovernanceFragilityScore", 0.4))))
    concentration = _clamp01(float(row.get("concentrationRisk", 0.25)))

    quorum_depth = _clamp01(float(quorum_report.get("quorumDepthScore", row.get("quorumDepthScore", 0.5))))
    participation = _clamp01(float(quorum_report.get("participationDepthScore", 0.5)))
    continuity_stress = _clamp01(float(continuity_mode.get("stressScore", 0.0)))
    continuity_label = str(continuity_mode.get("continuityMode") or "normal")

    coherence = _clamp01(
        0.35 * succession_readiness
        + 0.30 * quorum_depth
        + 0.20 * participation
        + 0.15 * (1.0 - fragility)
    )
    anti_capture = _clamp01(
        0.35 * system_capture_risk
        + 0.25 * concentration
        + 0.20 * system_gov_risk
        + 0.20 * fragility
    )
    risk = _clamp01(
        0.30 * anti_capture
        + 0.20 * fragility
        + 0.15 * (1.0 - quorum_depth)
        + 0.15 * (1.0 - succession_readiness)
        + 0.10 * continuity_stress
        + 0.10 * system_behavior_risk
    )

    if risk >= 0.86 or anti_capture >= 0.82 or continuity_label == "emergency":
        resilience_status = "degraded"
        audit_status = "require-human-emergency-review"
        rule = "critical-resilience-degradation"
        explanation = "Resilience is degraded under severe fragility or capture pressure; immediate bounded human/community review is required."
    elif risk >= 0.68 or anti_capture >= 0.66:
        resilience_status = "capture-risk"
        audit_status = "freeze-governance-expansion"
        rule = "anti-capture-freeze-expansion"
        explanation = "Capture-risk is elevated; freeze governance expansion and preserve reviewability before structural changes."
    elif fragility >= 0.62 or quorum_depth < 0.45:
        resilience_status = "fragile"
        audit_status = "queue-continuity-review"
        rule = "fragility-queue-continuity-review"
        explanation = "Governance resilience is fragile; queue continuity candidates for human/community review without automatic transfer."
    elif fragility >= 0.45 or quorum_depth < 0.60:
        resilience_status = "thinning"
        audit_status = "increase-watch"
        rule = "thinning-watchlist"
        explanation = "Resilience layer is thinning; increase watch and maintain redundancy-focused review pathways."
    else:
        resilience_status = "stable"
        audit_status = "continue"
        rule = "stable-bounded-continuity"
        explanation = "Resilience remains stable under bounded anti-capture and quorum depth conditions."

    if continuity_label in {"preservation", "degraded"} and audit_status in {"continue", "increase-watch"}:
        audit_status = "degraded-mode"
        rule = "continuity-degraded-mode"
        explanation = "Degraded continuity mode applies constrained continuity safeguards; it is not sovereignty or autonomous authority transfer."

    return ResilienceDecision(
        resilience_id=resilience_id,
        reviewer_id=None,
        resilience_status=resilience_status,
        audit_status=audit_status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        quorum_depth_context={
            "quorumDepthScore": round(quorum_depth, 6),
            "participationDepthScore": round(participation, 6),
        },
        anti_capture_risk=round(anti_capture, 6),
        governance_fragility_context={
            "successionReadinessScore": round(succession_readiness, 6),
            "governanceFragilityScore": round(fragility, 6),
            "concentrationRisk": round(concentration, 6),
        },
        governing_rule=rule,
        explanation=(
            f"{explanation} resilienceId={resilience_id}, coherence={coherence:.3f}, risk={risk:.3f}, antiCaptureRisk={anti_capture:.3f}."
        ),
        target_publisher_action=_status_to_action(audit_status),
    )


def evaluate_roster_candidate(
    row: dict[str, Any],
    *,
    continuity_mode: dict[str, Any],
    system_capture_risk: float,
    quorum_report: dict[str, Any],
) -> ResilienceDecision:
    reviewer_id = str(row.get("reviewerId") or "reviewer:unknown")
    readiness = _clamp01(float(row.get("successionReadinessScore", 0.5)))
    conflict_risk = _clamp01(float(row.get("conflictRisk", 0.2)))
    reliability = _clamp01(float(row.get("reliabilityScore", 0.5)))

    continuity_stress = _clamp01(float(continuity_mode.get("stressScore", 0.0)))
    continuity_label = str(continuity_mode.get("continuityMode") or "normal")
    quorum_depth = _clamp01(float(quorum_report.get("quorumDepthScore", 0.5)))

    coherence = _clamp01(0.45 * readiness + 0.35 * reliability + 0.20 * quorum_depth)
    anti_capture = _clamp01(0.40 * system_capture_risk + 0.35 * conflict_risk + 0.25 * (1.0 - readiness))
    risk = _clamp01(0.40 * anti_capture + 0.30 * conflict_risk + 0.20 * continuity_stress + 0.10 * (1.0 - reliability))

    if risk >= 0.82:
        resilience_status = "capture-risk"
        audit_status = "require-human-emergency-review"
        rule = "roster-critical-risk"
        explanation = "Continuity roster candidate has critical anti-capture risk and requires immediate human/community escalation."
    elif risk >= 0.62:
        resilience_status = "fragile"
        audit_status = "queue-continuity-review"
        rule = "roster-review-queue"
        explanation = "Continuity roster candidate is fragile and should remain queued for broader human/community review."
    elif risk >= 0.45:
        resilience_status = "thinning"
        audit_status = "increase-watch"
        rule = "roster-watch"
        explanation = "Continuity roster candidate remains on watch pending stronger redundancy and anti-capture margin."
    else:
        resilience_status = "stable"
        audit_status = "queue-continuity-review"
        rule = "roster-bounded-readiness"
        explanation = "Continuity roster candidate appears stable enough for advisory queueing; no automatic authority transfer occurs."

    if continuity_label in {"degraded", "preservation"} and audit_status == "increase-watch":
        audit_status = "degraded-mode"
        rule = "roster-degraded-mode"
        explanation = "Degraded mode applies constrained continuity only; succession remains human/community reviewed and non-automatic."

    return ResilienceDecision(
        resilience_id=None,
        reviewer_id=reviewer_id,
        resilience_status=resilience_status,
        audit_status=audit_status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        quorum_depth_context={
            "quorumDepthScore": round(quorum_depth, 6),
            "continuityStressScore": round(continuity_stress, 6),
        },
        anti_capture_risk=round(anti_capture, 6),
        governance_fragility_context={
            "successionReadinessScore": round(readiness, 6),
            "conflictRisk": round(conflict_risk, 6),
            "reliabilityScore": round(reliability, 6),
        },
        governing_rule=rule,
        explanation=(
            f"{explanation} reviewerId={reviewer_id}, coherence={coherence:.3f}, risk={risk:.3f}, antiCaptureRisk={anti_capture:.3f}."
        ),
        target_publisher_action=_status_to_action(audit_status),
    )


def _to_payload(item: ResilienceDecision) -> dict[str, Any]:
    payload = {
        "resilienceStatus": item.resilience_status,
        "auditStatus": item.audit_status,
        "coherenceScore": item.coherence_score,
        "riskScore": item.risk_score,
        "quorumDepthContext": item.quorum_depth_context,
        "antiCaptureRisk": item.anti_capture_risk,
        "governanceFragilityContext": item.governance_fragility_context,
        "governingRule": item.governing_rule,
        "explanation": item.explanation,
        "targetPublisherAction": item.target_publisher_action,
    }
    if item.resilience_id is not None:
        payload["resilienceId"] = item.resilience_id
    if item.reviewer_id is not None:
        payload["reviewerId"] = item.reviewer_id
    return payload


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    succession_map = _load_json(SUCCESSION_STATE_MAP_PATH)
    succession_summary = _load_json(SUCCESSION_STATE_SUMMARY_PATH)
    quorum_report = _load_json(QUORUM_RESILIENCE_REPORT_PATH)
    roster_candidates = _load_json(CONTINUITY_ROSTER_CANDIDATES_PATH)
    governance_audit = _load_json(GOVERNANCE_AUDIT_PATH)
    reviewer_behavior = _load_json(REVIEWER_BEHAVIOR_AUDIT_PATH)
    constitutional_audit = _load_json(CONSTITUTIONAL_AUDIT_PATH)
    continuity_mode = _load_json(CONTINUITY_MODE_ASSESSMENT_PATH)

    system_gov_risk, system_behavior_risk, system_capture_risk = _system_signals(
        governance_audit, reviewer_behavior, constitutional_audit
    )

    target_rows = succession_map.get("resilienceTargets") if isinstance(succession_map.get("resilienceTargets"), list) else []
    target_decisions = [
        evaluate_target(
            row,
            summary=succession_summary,
            quorum_report=quorum_report,
            continuity_mode=continuity_mode,
            system_gov_risk=system_gov_risk,
            system_behavior_risk=system_behavior_risk,
            system_capture_risk=system_capture_risk,
        )
        for row in target_rows
        if isinstance(row, dict)
    ]

    roster_rows = roster_candidates.get("candidates") if isinstance(roster_candidates.get("candidates"), list) else []
    roster_decisions = [
        evaluate_roster_candidate(
            row,
            continuity_mode=continuity_mode,
            system_capture_risk=system_capture_risk,
            quorum_report=quorum_report,
        )
        for row in roster_rows
        if isinstance(row, dict)
    ]

    combined = target_decisions + roster_decisions
    combined = sorted(combined, key=lambda item: item.resilience_id or item.reviewer_id or "")
    roster_decisions = sorted(roster_decisions, key=lambda item: item.reviewer_id or "")

    created_at = _resolve_created_at(succession_summary, quorum_report, continuity_mode)
    phaselock = (
        "governance body state -> CoherenceLattice succession/resilience formalization -> Sophia resilience audit -> "
        "Publisher continuity/succession overlays -> human/community continuity decision"
    )

    audit_payload = {
        "schema": "resilience_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": "Continuity recommendations support lawful resilience and reviewer redundancy only; no automatic authority transfer occurs.",
        "records": [_to_payload(item) for item in combined],
    }

    recommendations_payload = {
        "schema": "succession_recommendations_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice succession/resilience formalization -> Sophia resilience audit -> Publisher succession docket",
        "caution": "Degraded mode means constrained continuity, not sovereignty; succession candidates remain human/community reviewed.",
        "recommendations": [_to_payload(item) for item in roster_decisions],
    }

    Draft202012Validator(_load_json(RESILIENCE_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(SUCCESSION_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main() -> int:
    audit_payload, recommendations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    RESILIENCE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    SUCCESSION_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {RESILIENCE_AUDIT_OUT}")
    print(f"Wrote {SUCCESSION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
