from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

INTEGRITY_MAP_PATH = BRIDGE_DIR / "reviewer_integrity_map.json"
INTEGRITY_SUMMARY_PATH = BRIDGE_DIR / "reviewer_integrity_summary.json"
PROMOTION_AUDIT_PATH = BRIDGE_DIR / "promotion_audit.json"
PROMOTION_RECOMMENDATIONS_PATH = BRIDGE_DIR / "promotion_recommendations.json"
STABILITY_AUDIT_PATH = BRIDGE_DIR / "stability_audit.json"
REVIEWER_BEHAVIOR_HISTORY_PATH = BRIDGE_DIR / "reviewer_behavior_history.json"

GOVERNANCE_AUDIT_OUT = BRIDGE_DIR / "governance_audit.json"
GOVERNANCE_RECOMMENDATIONS_OUT = BRIDGE_DIR / "governance_recommendations.json"

GOVERNANCE_AUDIT_SCHEMA = SCHEMA_DIR / "governance_audit_v1.schema.json"
GOVERNANCE_RECOMMENDATIONS_SCHEMA = SCHEMA_DIR / "governance_recommendations_v1.schema.json"


@dataclass(slots=True)
class GovernanceDecision:
    reviewer_id: str
    governance_status: str
    coherence_score: float
    risk_score: float
    conflict_risk: float
    volatility_context: dict[str, Any]
    contradiction_context: dict[str, Any]
    integrity_signals: list[str]
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


def _status_to_action(status: str) -> str:
    return {
        "eligible": "watch",
        "watch": "watch",
        "hold": "watch",
        "recommend-human-review": "docket",
        "ineligible": "suppress",
    }[status]


def _dict_by_key(rows: Any, key: str) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    if not isinstance(rows, list):
        return out
    for row in rows:
        if not isinstance(row, dict):
            continue
        row_key = row.get(key)
        if isinstance(row_key, str):
            out[row_key] = row
    return out


def evaluate_candidate(
    candidate: dict[str, Any],
    *,
    summary: dict[str, Any],
    promotion_by_reviewer: dict[str, dict[str, Any]],
    stability_audit: dict[str, Any],
    behavior_by_reviewer: dict[str, dict[str, Any]],
) -> GovernanceDecision:
    reviewer_id = str(candidate.get("reviewerId") or "reviewer:unknown")
    consent_status = str(candidate.get("consentStatus") or "unknown")
    declared_conflicts = candidate.get("declaredConflicts") if isinstance(candidate.get("declaredConflicts"), list) else []
    contradiction_flags = candidate.get("contradictionFlags") if isinstance(candidate.get("contradictionFlags"), list) else []

    integrity_score = _clamp01(float(candidate.get("integrityScore", summary.get("meanIntegrityScore", 0.5))))
    base_conflict_risk = _clamp01(float(candidate.get("conflictRisk", 0.25 if declared_conflicts else 0.10)))

    promotion_row = promotion_by_reviewer.get(reviewer_id, {})
    promotion_risk = _clamp01(float(promotion_row.get("riskScore", summary.get("meanPromotionRisk", 0.35))))

    behavior_row = behavior_by_reviewer.get(reviewer_id, {})
    override_risk = _clamp01(float(behavior_row.get("overrideRisk", 0.0)))
    behavior_volatility = _clamp01(float(behavior_row.get("behaviorVolatility", 0.0)))

    stability_rows = stability_audit.get("threads") if isinstance(stability_audit.get("threads"), list) else []
    global_volatility = _clamp01(
        sum(float(row.get("riskScore", 0.0)) for row in stability_rows if isinstance(row, dict) and isinstance(row.get("riskScore"), (int, float)))
        / max(1, len(stability_rows))
    )

    coherence_score = _clamp01(0.50 * integrity_score + 0.25 * (1.0 - base_conflict_risk) + 0.15 * (1.0 - override_risk) + 0.10 * (1.0 - behavior_volatility))
    contradiction_pressure = min(0.45, 0.14 * len(contradiction_flags))
    risk_score = _clamp01(
        0.34 * promotion_risk
        + 0.22 * base_conflict_risk
        + 0.16 * override_risk
        + 0.14 * behavior_volatility
        + 0.08 * global_volatility
        + contradiction_pressure
        + (0.08 if consent_status != "voluntary" else 0.0)
    )

    signals: list[str] = []
    if consent_status == "voluntary":
        signals.append("consent-based governance participation")
    if declared_conflicts:
        signals.append("declared conflicts are bounded")
    if not contradiction_flags:
        signals.append("low contradiction exposure")
    if override_risk <= 0.30:
        signals.append("low override risk")
    if behavior_volatility <= 0.35:
        signals.append("stable reviewer behavior")

    if risk_score >= 0.80 or consent_status == "revoked":
        status = "ineligible"
        rule = "critical-governance-risk"
        explanation = "Candidate is ineligible under bounded governance protocol due to elevated risk or missing consent basis."
    elif coherence_score >= 0.74 and risk_score <= 0.34 and consent_status == "voluntary":
        status = "recommend-human-review"
        rule = "high-integrity-low-risk"
        explanation = "Candidate is suitable for human/community governance review based on bounded, consent-based evidence."
    elif coherence_score >= 0.64 and risk_score <= 0.50:
        status = "eligible"
        rule = "eligible-observational"
        explanation = "Candidate is currently eligible for continued observational governance consideration without docket escalation."
    elif coherence_score >= 0.54 and risk_score <= 0.66:
        status = "watch"
        rule = "watch-governance-queue"
        explanation = "Candidate remains in governance watch queue pending additional bounded evidence."
    else:
        status = "hold"
        rule = "hold-for-reassessment"
        explanation = "Candidate is held for reassessment before any human/community review recommendation."

    return GovernanceDecision(
        reviewer_id=reviewer_id,
        governance_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        conflict_risk=round(base_conflict_risk, 6),
        volatility_context={
            "behaviorVolatility": round(behavior_volatility, 6),
            "overrideRisk": round(override_risk, 6),
            "globalGovernanceVolatility": round(global_volatility, 6),
        },
        contradiction_context={
            "contradictionFlags": [str(flag) for flag in contradiction_flags],
            "contradictionCount": len(contradiction_flags),
        },
        integrity_signals=sorted(set(signals)),
        governing_rule=rule,
        explanation=(
            f"{explanation} reviewerId={reviewer_id}, coherence={coherence_score:.3f}, "
            f"risk={risk_score:.3f}, conflictRisk={base_conflict_risk:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(item: GovernanceDecision) -> dict[str, Any]:
    return {
        "reviewerId": item.reviewer_id,
        "governanceStatus": item.governance_status,
        "coherenceScore": item.coherence_score,
        "riskScore": item.risk_score,
        "conflictRisk": item.conflict_risk,
        "volatilityContext": item.volatility_context,
        "contradictionContext": item.contradiction_context,
        "integritySignals": item.integrity_signals,
        "governingRule": item.governing_rule,
        "explanation": item.explanation,
        "targetPublisherAction": item.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    integrity_map = _load_json(INTEGRITY_MAP_PATH)
    integrity_summary = _load_json(INTEGRITY_SUMMARY_PATH)
    promotion_audit = _load_json(PROMOTION_AUDIT_PATH)
    promotion_recommendations = _load_json(PROMOTION_RECOMMENDATIONS_PATH)
    stability_audit = _load_json(STABILITY_AUDIT_PATH)
    behavior_history = _load_json(REVIEWER_BEHAVIOR_HISTORY_PATH) if REVIEWER_BEHAVIOR_HISTORY_PATH.exists() else {}

    candidates = integrity_map.get("candidates") if isinstance(integrity_map.get("candidates"), list) else []
    promotion_rows = []
    if isinstance(promotion_audit.get("audits"), list):
        promotion_rows.extend(promotion_audit["audits"])
    if isinstance(promotion_recommendations.get("recommendations"), list):
        promotion_rows.extend(promotion_recommendations["recommendations"])

    promotion_by_reviewer = _dict_by_key(promotion_rows, "reviewerId")
    behavior_by_reviewer = _dict_by_key(behavior_history.get("reviewers") if isinstance(behavior_history, dict) else [], "reviewerId")

    decisions = [
        evaluate_candidate(
            candidate,
            summary=integrity_summary,
            promotion_by_reviewer=promotion_by_reviewer,
            stability_audit=stability_audit,
            behavior_by_reviewer=behavior_by_reviewer,
        )
        for candidate in candidates
        if isinstance(candidate, dict)
    ]
    decisions = sorted(decisions, key=lambda item: item.reviewer_id)

    created_at = _resolve_created_at(integrity_summary, integrity_map, promotion_audit)
    phaselock = (
        "candidate governance portfolio -> CoherenceLattice reviewer-integrity formalization -> Sophia governance audit -> "
        "Publisher governance review docket -> human/community decision -> ongoing reviewer behavior monitoring -> "
        "Sophia reviewer behavior audit -> Publisher reviewer monitor overlays"
    )

    audit_payload = {
        "schema": "governance_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "governanceMode": "bounded-consent-evidence",
        "caution": "Outputs are advisory for human/community governance selection; no automatic reviewer appointment occurs.",
        "audits": [_to_payload(item) for item in decisions],
    }
    recommendations_payload = {
        "schema": "governance_recommendations_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice reviewer-integrity formalization -> Sophia governance audit -> Publisher governance review docket",
        "caution": "Governance recommendations are advisory and reversible; reviewer selection remains human/community controlled.",
        "recommendations": [_to_payload(item) for item in decisions],
    }

    Draft202012Validator(_load_json(GOVERNANCE_AUDIT_SCHEMA)).validate(audit_payload)
    Draft202012Validator(_load_json(GOVERNANCE_RECOMMENDATIONS_SCHEMA)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main() -> int:
    audit_payload, recommendations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    GOVERNANCE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    GOVERNANCE_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {GOVERNANCE_AUDIT_OUT}")
    print(f"Wrote {GOVERNANCE_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
