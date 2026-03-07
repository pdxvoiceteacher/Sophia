from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

DELIBERATION_MAP_PATH = BRIDGE_DIR / "deliberation_state_map.json"
DELIBERATION_SUMMARY_PATH = BRIDGE_DIR / "deliberation_state_summary.json"
AMENDMENT_MAP_PATH = BRIDGE_DIR / "amendment_candidate_map.json"
AMENDMENT_SUMMARY_PATH = BRIDGE_DIR / "amendment_candidate_summary.json"
GOVERNANCE_AUDIT_PATH = BRIDGE_DIR / "governance_audit.json"
REVIEWER_BEHAVIOR_AUDIT_PATH = BRIDGE_DIR / "reviewer_behavior_audit.json"
CONSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "constitutional_audit.json"
CONSTITUTIONAL_RECOMMENDATIONS_PATH = BRIDGE_DIR / "constitutional_recommendations.json"

QUORUM_AUDIT_OUT = BRIDGE_DIR / "quorum_audit.json"
AMENDMENT_RECOMMENDATIONS_OUT = BRIDGE_DIR / "amendment_recommendations.json"

QUORUM_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "quorum_audit_v1.schema.json"
AMENDMENT_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "amendment_recommendations_v1.schema.json"


@dataclass(slots=True)
class DeliberationDecision:
    deliberation_id: str | None
    amendment_id: str | None
    quorum_status: str
    amendment_status: str
    coherence_score: float
    risk_score: float
    anti_capture_risk: float
    conflict_context: dict[str, Any]
    continuity_mode_context: dict[str, Any]
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
        "recommend-deliberation": "docket",
        "hold": "watch",
        "watch": "watch",
        "reject-amendment": "suppress",
        "require-broader-human-review": "docket",
        "emergency-interpretation-only": "watch",
    }[status]


def _continuity_context(constitutional_recommendations: dict[str, Any]) -> dict[str, Any]:
    rows = constitutional_recommendations.get("recommendations") if isinstance(constitutional_recommendations.get("recommendations"), list) else []
    for row in rows:
        if not isinstance(row, dict):
            continue
        if row.get("systemTargetId") == "system:governance-continuity":
            ctx = row.get("continuityModeContext")
            if isinstance(ctx, dict):
                return ctx
    return {"continuityMode": "normal", "stressScore": 0.0, "preservationRecommended": False}


def _system_risks(governance_audit: dict[str, Any], reviewer_behavior: dict[str, Any], constitutional_audit: dict[str, Any]) -> tuple[float, float, float]:
    governance_rows = governance_audit.get("audits") if isinstance(governance_audit.get("audits"), list) else []
    reviewer_rows = reviewer_behavior.get("reviewers") if isinstance(reviewer_behavior.get("reviewers"), list) else []
    constitutional_rows = constitutional_audit.get("evaluations") if isinstance(constitutional_audit.get("evaluations"), list) else []

    governance_risk = _safe_mean(
        [float(row.get("riskScore")) for row in governance_rows if isinstance(row, dict) and isinstance(row.get("riskScore"), (int, float))],
        0.3,
    )
    reviewer_risk = _safe_mean(
        [float(row.get("overrideRisk")) for row in reviewer_rows if isinstance(row, dict) and isinstance(row.get("overrideRisk"), (int, float))],
        0.2,
    )
    capture_risk = _safe_mean(
        [float(row.get("captureRisk")) for row in constitutional_rows if isinstance(row, dict) and isinstance(row.get("captureRisk"), (int, float))],
        0.3,
    )
    return _clamp01(governance_risk), _clamp01(reviewer_risk), _clamp01(capture_risk)


def evaluate_deliberation(
    deliberation: dict[str, Any],
    *,
    summary: dict[str, Any],
    continuity_ctx: dict[str, Any],
    governance_risk: float,
    reviewer_risk: float,
    constitutional_capture_risk: float,
) -> DeliberationDecision:
    deliberation_id = str(deliberation.get("deliberationId") or "deliberation:unknown")
    participation = _clamp01(float(deliberation.get("participationRatio", summary.get("meanParticipationRatio", 0.5))))
    representation = _clamp01(float(deliberation.get("representationScore", summary.get("meanRepresentationScore", 0.5))))
    contradiction = _clamp01(float(deliberation.get("contradictionScore", 0.0)))
    declared_conflicts = deliberation.get("declaredConflicts") if isinstance(deliberation.get("declaredConflicts"), list) else []

    coherence = _clamp01(0.45 * participation + 0.35 * representation + 0.20 * (1.0 - contradiction))
    anti_capture = _clamp01(
        0.40 * constitutional_capture_risk
        + 0.25 * governance_risk
        + 0.20 * reviewer_risk
        + 0.15 * (1.0 - representation)
    )
    continuity_stress = _clamp01(float(continuity_ctx.get("stressScore", 0.0)))
    risk = _clamp01(0.45 * anti_capture + 0.25 * contradiction + 0.20 * continuity_stress + 0.10 * (1.0 - participation))

    if participation >= 0.70 and representation >= 0.68 and anti_capture <= 0.42:
        quorum_status = "sufficient"
    elif anti_capture >= 0.72:
        quorum_status = "stacked-risk"
    elif participation <= 0.35:
        quorum_status = "insufficient"
    elif coherence < 0.45:
        quorum_status = "indeterminate"
    else:
        quorum_status = "strained"

    if quorum_status == "stacked-risk" or anti_capture >= 0.78 or contradiction >= 0.60:
        amendment_status = "reject-amendment"
        rule = "anti-capture-freeze"
        explanation = "Deliberation posture indicates stacked-risk conditions; amendment pathway remains frozen pending broader external review."
    elif continuity_stress >= 0.70:
        amendment_status = "emergency-interpretation-only"
        rule = "emergency-interpretation-distinction"
        explanation = "Continuity stress permits emergency interpretation guidance only; it is not equivalent to constitutional amendment."
    elif quorum_status == "sufficient" and risk <= 0.40:
        amendment_status = "recommend-deliberation"
        rule = "legitimate-quorum-procedural"
        explanation = "Deliberation quorum appears procedurally legitimate for advisory human/community constitutional review."
    elif quorum_status in {"strained", "indeterminate"}:
        amendment_status = "require-broader-human-review"
        rule = "broaden-review-before-amendment"
        explanation = "Quorum legitimacy is limited; broader human/community review is required before amendment consideration."
    else:
        amendment_status = "watch"
        rule = "watchlist-deliberation"
        explanation = "Deliberation remains on quorum watchlist until participation and anti-capture margins improve."

    return DeliberationDecision(
        deliberation_id=deliberation_id,
        amendment_id=None,
        quorum_status=quorum_status,
        amendment_status=amendment_status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        anti_capture_risk=round(anti_capture, 6),
        conflict_context={
            "declaredConflictCount": len(declared_conflicts),
            "contradictionScore": round(contradiction, 6),
        },
        continuity_mode_context={
            "continuityMode": str(continuity_ctx.get("continuityMode", "normal")),
            "stressScore": continuity_stress,
            "preservationRecommended": bool(continuity_ctx.get("preservationRecommended", False)),
        },
        governing_rule=rule,
        explanation=(
            f"{explanation} deliberationId={deliberation_id}, coherence={coherence:.3f}, "
            f"risk={risk:.3f}, antiCaptureRisk={anti_capture:.3f}."
        ),
        target_publisher_action=_status_to_action(amendment_status),
    )


def evaluate_amendment(
    amendment: dict[str, Any],
    *,
    summary: dict[str, Any],
    deliberation_decisions: dict[str, DeliberationDecision],
    continuity_ctx: dict[str, Any],
    governance_risk: float,
    reviewer_risk: float,
    constitutional_capture_risk: float,
) -> DeliberationDecision:
    amendment_id = str(amendment.get("amendmentId") or "amendment:unknown")
    linked_deliberation_id = str(amendment.get("deliberationId") or "")

    formal_score = _clamp01(float(amendment.get("formalAmendmentScore", summary.get("meanFormalAmendmentScore", 0.5))))
    contradiction = _clamp01(float(amendment.get("contradictionScore", 0.0)))
    scope_risk = _clamp01(float(amendment.get("scopeRisk", 0.2)))

    linked = deliberation_decisions.get(linked_deliberation_id)
    linked_coherence = linked.coherence_score if linked else _clamp01(float(summary.get("meanLinkedDeliberationCoherence", 0.5)))
    linked_risk = linked.risk_score if linked else _clamp01(float(summary.get("meanLinkedDeliberationRisk", 0.4)))
    linked_quorum = linked.quorum_status if linked else "indeterminate"

    coherence = _clamp01(0.45 * formal_score + 0.30 * linked_coherence + 0.25 * (1.0 - contradiction))
    anti_capture = _clamp01(
        0.35 * constitutional_capture_risk + 0.25 * governance_risk + 0.20 * reviewer_risk + 0.20 * scope_risk
    )
    continuity_stress = _clamp01(float(continuity_ctx.get("stressScore", 0.0)))
    risk = _clamp01(0.35 * anti_capture + 0.25 * linked_risk + 0.20 * contradiction + 0.20 * continuity_stress)

    if linked_quorum == "sufficient" and anti_capture <= 0.42:
        quorum_status = "sufficient"
    elif linked_quorum == "stacked-risk" or anti_capture >= 0.72:
        quorum_status = "stacked-risk"
    elif linked_quorum == "insufficient":
        quorum_status = "insufficient"
    elif linked_quorum == "indeterminate":
        quorum_status = "indeterminate"
    else:
        quorum_status = "strained"

    if continuity_stress >= 0.75:
        amendment_status = "emergency-interpretation-only"
        rule = "emergency-not-amendment"
        explanation = "Under continuity emergency conditions, only temporary interpretation guidance is advisable, not amendment advancement."
    elif quorum_status == "stacked-risk" or anti_capture >= 0.78:
        amendment_status = "reject-amendment"
        rule = "stacked-risk-reject"
        explanation = "Amendment candidate is rejected for now due to stacked-risk anti-capture concerns."
    elif quorum_status == "sufficient" and coherence >= 0.70 and risk <= 0.40:
        amendment_status = "recommend-deliberation"
        rule = "sufficient-quorum-recommend-deliberation"
        explanation = "Amendment candidate is procedurally suitable for advisory human/community deliberation review."
    elif quorum_status in {"strained", "indeterminate"} and risk <= 0.65:
        amendment_status = "require-broader-human-review"
        rule = "broaden-deliberative-participation"
        explanation = "Amendment candidate requires broader human/community review before any constitutional revision pathway is considered."
    elif risk <= 0.74:
        amendment_status = "hold"
        rule = "hold-for-reversible-clarification"
        explanation = "Amendment candidate is held pending reversible clarification and anti-capture checks."
    else:
        amendment_status = "watch"
        rule = "watch-amendment-queue"
        explanation = "Amendment candidate remains on watch queue pending reduced risk and improved legitimacy conditions."

    return DeliberationDecision(
        deliberation_id=None,
        amendment_id=amendment_id,
        quorum_status=quorum_status,
        amendment_status=amendment_status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        anti_capture_risk=round(anti_capture, 6),
        conflict_context={
            "linkedDeliberationId": linked_deliberation_id,
            "linkedQuorumStatus": linked_quorum,
            "contradictionScore": round(contradiction, 6),
            "scopeRisk": round(scope_risk, 6),
        },
        continuity_mode_context={
            "continuityMode": str(continuity_ctx.get("continuityMode", "normal")),
            "stressScore": continuity_stress,
            "preservationRecommended": bool(continuity_ctx.get("preservationRecommended", False)),
        },
        governing_rule=rule,
        explanation=(
            f"{explanation} amendmentId={amendment_id}, coherence={coherence:.3f}, "
            f"risk={risk:.3f}, antiCaptureRisk={anti_capture:.3f}."
        ),
        target_publisher_action=_status_to_action(amendment_status),
    )


def _to_payload(item: DeliberationDecision) -> dict[str, Any]:
    payload = {
        "quorumStatus": item.quorum_status,
        "amendmentStatus": item.amendment_status,
        "coherenceScore": item.coherence_score,
        "riskScore": item.risk_score,
        "antiCaptureRisk": item.anti_capture_risk,
        "conflictContext": item.conflict_context,
        "continuityModeContext": item.continuity_mode_context,
        "governingRule": item.governing_rule,
        "explanation": item.explanation,
        "targetPublisherAction": item.target_publisher_action,
    }
    if item.deliberation_id is not None:
        payload["deliberationId"] = item.deliberation_id
    if item.amendment_id is not None:
        payload["amendmentId"] = item.amendment_id
    return payload


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    deliberation_map = _load_json(DELIBERATION_MAP_PATH)
    deliberation_summary = _load_json(DELIBERATION_SUMMARY_PATH)
    amendment_map = _load_json(AMENDMENT_MAP_PATH)
    amendment_summary = _load_json(AMENDMENT_SUMMARY_PATH)
    governance_audit = _load_json(GOVERNANCE_AUDIT_PATH)
    reviewer_behavior = _load_json(REVIEWER_BEHAVIOR_AUDIT_PATH)
    constitutional_audit = _load_json(CONSTITUTIONAL_AUDIT_PATH)
    constitutional_recommendations = _load_json(CONSTITUTIONAL_RECOMMENDATIONS_PATH)

    continuity_ctx = _continuity_context(constitutional_recommendations)
    governance_risk, reviewer_risk, constitutional_capture_risk = _system_risks(
        governance_audit, reviewer_behavior, constitutional_audit
    )

    deliberation_rows = deliberation_map.get("deliberations") if isinstance(deliberation_map.get("deliberations"), list) else []
    deliberation_decisions_list = [
        evaluate_deliberation(
            row,
            summary=deliberation_summary,
            continuity_ctx=continuity_ctx,
            governance_risk=governance_risk,
            reviewer_risk=reviewer_risk,
            constitutional_capture_risk=constitutional_capture_risk,
        )
        for row in deliberation_rows
        if isinstance(row, dict)
    ]
    deliberation_decisions_list = sorted(deliberation_decisions_list, key=lambda item: item.deliberation_id or "")
    deliberation_decisions = {
        item.deliberation_id: item for item in deliberation_decisions_list if item.deliberation_id is not None
    }

    amendment_rows = amendment_map.get("amendments") if isinstance(amendment_map.get("amendments"), list) else []
    amendment_decisions = [
        evaluate_amendment(
            row,
            summary=amendment_summary,
            deliberation_decisions=deliberation_decisions,
            continuity_ctx=continuity_ctx,
            governance_risk=governance_risk,
            reviewer_risk=reviewer_risk,
            constitutional_capture_risk=constitutional_capture_risk,
        )
        for row in amendment_rows
        if isinstance(row, dict)
    ]
    amendment_decisions = sorted(amendment_decisions, key=lambda item: item.amendment_id or "")

    created_at = _resolve_created_at(deliberation_summary, amendment_summary, constitutional_audit)
    phaselock = (
        "constitutional state -> CoherenceLattice deliberation/amendment formalization -> Sophia quorum/amendment audit -> "
        "Publisher deliberation docket + amendment queue -> human/community constitutional review"
    )

    combined = deliberation_decisions_list + amendment_decisions
    combined = sorted(combined, key=lambda item: item.deliberation_id or item.amendment_id or "")

    audit_payload = {
        "schema": "quorum_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": "Quorum and amendment outputs are advisory only; anti-capture procedural review remains central.",
        "records": [_to_payload(item) for item in combined],
    }

    recommendations_payload = {
        "schema": "amendment_recommendations_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice deliberation/amendment formalization -> Sophia quorum/amendment audit -> Publisher amendment queue",
        "caution": "No constitutional revision is automatic; emergency interpretation is not equivalent to amendment.",
        "recommendations": [_to_payload(item) for item in amendment_decisions],
    }

    Draft202012Validator(_load_json(QUORUM_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(AMENDMENT_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main() -> int:
    audit_payload, recommendations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    QUORUM_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    AMENDMENT_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {QUORUM_AUDIT_OUT}")
    print(f"Wrote {AMENDMENT_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
