from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

CANDIDATE_MAP_PATH = BRIDGE_DIR / "promotion_candidate_map.json"
CANDIDATE_SUMMARY_PATH = BRIDGE_DIR / "promotion_candidate_summary.json"
STABILITY_AUDIT_PATH = BRIDGE_DIR / "stability_audit.json"
RECURSIVE_ESCALATIONS_PATH = BRIDGE_DIR / "recursive_watch_escalations.json"
DONATION_AUDIT_PATH = BRIDGE_DIR / "pattern_donation_audit.json"
DONATION_DECISIONS_PATH = BRIDGE_DIR / "pattern_donation_decisions.json"
ATTENTION_UPDATES_PATH = BRIDGE_DIR / "attention_updates.json"
DRIFT_MAP_PATH = BRIDGE_DIR / "coherence_drift_map.json"

PROMOTION_AUDIT_OUT = BRIDGE_DIR / "promotion_audit.json"
PROMOTION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "promotion_recommendations.json"

PROMOTION_AUDIT_SCHEMA = SCHEMA_DIR / "promotion_audit_v1.schema.json"
PROMOTION_RECOMMENDATIONS_SCHEMA = SCHEMA_DIR / "promotion_recommendations_v1.schema.json"


@dataclass(slots=True)
class PromotionDecision:
    candidate_id: str
    candidate_type: str
    audit_status: str
    coherence_score: float
    risk_score: float
    persistence_score: float
    multimodal_context: dict[str, Any]
    reasoning_context: dict[str, Any]
    cognitive_watch_signals: list[str]
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
        "recommend-human-review": "docket",
        "hold": "watch",
        "watch": "watch",
        "reject": "suppress",
    }[status]


def _parse_persistence(candidate: dict[str, Any], default: float) -> float:
    val = candidate.get("persistenceScore")
    if isinstance(val, (int, float)):
        return _clamp01(val)

    basis = candidate.get("persistenceBasis")
    if isinstance(basis, list):
        for item in basis:
            if not isinstance(item, str):
                continue
            match = re.search(r"(\d+(?:\.\d+)?)", item)
            if match:
                cycles = float(match.group(1))
                if "cycle" in item.lower():
                    return _clamp01(cycles / 5.0)
                return _clamp01(cycles)

    return _clamp01(default)


def _thread_context(source_ids: list[str], stability: dict[str, Any], escalations: dict[str, Any]) -> dict[str, Any]:
    threads = [s for s in source_ids if isinstance(s, str) and s.startswith("thread:")]
    stability_rows = stability.get("threads") if isinstance(stability.get("threads"), list) else []
    escalation_rows = escalations.get("escalations") if isinstance(escalations.get("escalations"), list) else []

    thread_items = [row for row in stability_rows if isinstance(row, dict) and row.get("threadId") in threads]
    escalation_items = [row for row in escalation_rows if isinstance(row, dict) and row.get("threadId") in threads]

    if not thread_items and not escalation_items:
        return {}

    coherence_vals = [float(row.get("coherenceScore")) for row in thread_items if isinstance(row.get("coherenceScore"), (int, float))]
    persistence_vals = [float(row.get("persistenceScore")) for row in thread_items if isinstance(row.get("persistenceScore"), (int, float))]
    risk_vals = [float(row.get("riskScore")) for row in thread_items if isinstance(row.get("riskScore"), (int, float))]

    return {
        "linkedThreadIds": sorted(threads),
        "escalationCount": len(escalation_items),
        "meanThreadCoherence": _clamp01(sum(coherence_vals) / len(coherence_vals)) if coherence_vals else 0.0,
        "meanThreadPersistence": _clamp01(sum(persistence_vals) / len(persistence_vals)) if persistence_vals else 0.0,
        "meanThreadRisk": _clamp01(sum(risk_vals) / len(risk_vals)) if risk_vals else 0.0,
    }


def _multimodal_context(source_ids: list[str], donation_audit: dict[str, Any], donation_decisions: dict[str, Any]) -> dict[str, Any]:
    donation_ids = {s for s in source_ids if isinstance(s, str) and s.startswith("donation:")}
    audit_rows = donation_audit.get("donations") if isinstance(donation_audit.get("donations"), list) else []
    decision_rows = donation_decisions.get("decisions") if isinstance(donation_decisions.get("decisions"), list) else []

    linked = [row for row in audit_rows + decision_rows if isinstance(row, dict) and row.get("donationId") in donation_ids]
    if not linked:
        return {}

    support_vals = [
        float(row.get("reinforcementScore"))
        for row in linked
        if isinstance(row.get("reinforcementScore"), (int, float))
    ]
    risky = [
        float(row.get("riskScore"))
        for row in linked
        if isinstance(row.get("riskScore"), (int, float))
    ]
    statuses = sorted({str(row.get("auditStatus")) for row in linked if isinstance(row.get("auditStatus"), str)})

    return {
        "linkedDonationIds": sorted(donation_ids),
        "linkedDonationStatuses": statuses,
        "meanReinforcementScore": _clamp01(sum(support_vals) / len(support_vals)) if support_vals else 0.0,
        "meanDonationRisk": _clamp01(sum(risky) / len(risky)) if risky else 0.0,
    }


def _attention_for_targets(target_ids: list[str], attention_updates: dict[str, Any]) -> float:
    updates = attention_updates.get("updates") if isinstance(attention_updates.get("updates"), list) else []
    tokens = set(target_ids)
    tokens.update(t.split(":")[-1] for t in target_ids)
    vals = [
        float(row.get("updated_weight"))
        for row in updates
        if isinstance(row, dict)
        and isinstance(row.get("targetId"), str)
        and row.get("targetId") in tokens
        and isinstance(row.get("updated_weight"), (int, float))
    ]
    if not vals:
        return 0.0
    return _clamp01(sum(vals) / len(vals))


def evaluate_candidate(
    candidate: dict[str, Any],
    *,
    candidate_summary: dict[str, Any],
    stability_audit: dict[str, Any],
    watch_escalations: dict[str, Any],
    donation_audit: dict[str, Any],
    donation_decisions: dict[str, Any],
    attention_updates: dict[str, Any],
    drift_map: dict[str, Any],
) -> PromotionDecision:
    candidate_id = str(candidate.get("candidateId") or "candidate:unknown")
    candidate_type = str(candidate.get("candidateType") or "unknown")
    source_ids = candidate.get("sourceIds") if isinstance(candidate.get("sourceIds"), list) else []
    target_ids = candidate.get("targetIds") if isinstance(candidate.get("targetIds"), list) else []

    formal_score = _clamp01(float(candidate.get("formalPromotionScore", 0.0)))
    summary_coherence = _clamp01(float(candidate_summary.get("meanFormalPromotionScore", 0.5)))
    requires_review = bool(candidate.get("requiresExecutiveReview", True))
    contradiction_flags = candidate.get("contradictionFlags") if isinstance(candidate.get("contradictionFlags"), list) else []

    reasoning_context = _thread_context(source_ids, stability_audit, watch_escalations)
    multimodal_context = _multimodal_context(source_ids, donation_audit, donation_decisions)

    thread_persistence = float(reasoning_context.get("meanThreadPersistence", 0.0))
    persistence_default = _clamp01(float(candidate_summary.get("meanPersistenceScore", thread_persistence)))
    persistence_score = _parse_persistence(candidate, persistence_default)

    attention_score = _attention_for_targets([str(t) for t in target_ids if isinstance(t, str)], attention_updates)
    global_drift = _clamp01(float(drift_map.get("globalDriftScore", 0.0)))
    multimodal_support = _clamp01(float(multimodal_context.get("meanReinforcementScore", 0.0)))

    coherence_score = _clamp01(
        0.45 * formal_score
        + 0.20 * summary_coherence
        + 0.20 * persistence_score
        + 0.10 * multimodal_support
        + 0.05 * attention_score
    )

    contradiction_pressure = min(0.45, 0.15 * len(contradiction_flags))
    escalation_pressure = 0.08 if float(reasoning_context.get("escalationCount", 0)) > 0 else 0.0
    risk_score = _clamp01(
        0.35 * global_drift
        + 0.25 * (1.0 - persistence_score)
        + 0.20 * (1.0 - multimodal_support)
        + contradiction_pressure
        + escalation_pressure
        + (0.05 if requires_review else 0.0)
    )

    watch_signals: list[str] = []
    if persistence_score >= 0.65:
        watch_signals.append("repeated multi-cycle coherence")
    if not contradiction_flags:
        watch_signals.append("low contradiction")
    if multimodal_support >= 0.50:
        watch_signals.append("cross-modal support present")
    if float(reasoning_context.get("escalationCount", 0)) > 0:
        watch_signals.append("recursive watch escalation linkage")
    if global_drift >= 0.45:
        watch_signals.append("elevated global drift")

    if risk_score >= 0.82 or len(contradiction_flags) >= 3:
        status = "reject"
        rule = "critical-risk-or-contradiction"
        explanation = "Candidate is suppressed from review recommendation due to critical risk or repeated contradiction markers."
    elif coherence_score >= 0.74 and persistence_score >= 0.64 and risk_score <= 0.38 and requires_review:
        status = "recommend-human-review"
        rule = "high-coherence-stable-low-risk"
        explanation = "Candidate is suitable for human editorial review docketing under stable, low-risk governance conditions."
    elif coherence_score >= 0.58 and risk_score <= 0.65:
        status = "hold"
        rule = "hold-for-more-evidence"
        explanation = "Candidate remains in hold state while additional observations are gathered before any human review recommendation."
    else:
        status = "watch"
        rule = "watch-observational"
        explanation = "Candidate remains on promotion watch queue as an observational signal with insufficient governance margin for docketing."

    return PromotionDecision(
        candidate_id=candidate_id,
        candidate_type=candidate_type,
        audit_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        persistence_score=round(persistence_score, 6),
        multimodal_context=multimodal_context,
        reasoning_context=reasoning_context,
        cognitive_watch_signals=sorted(set(watch_signals)),
        governing_rule=rule,
        explanation=(
            f"{explanation} candidateId={candidate_id}, type={candidate_type}, "
            f"coherence={coherence_score:.3f}, risk={risk_score:.3f}, persistence={persistence_score:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def _item_to_payload(item: PromotionDecision) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "candidateId": item.candidate_id,
        "candidateType": item.candidate_type,
        "auditStatus": item.audit_status,
        "coherenceScore": item.coherence_score,
        "riskScore": item.risk_score,
        "persistenceScore": item.persistence_score,
        "cognitiveWatchSignals": item.cognitive_watch_signals,
        "governingRule": item.governing_rule,
        "explanation": item.explanation,
        "targetPublisherAction": item.target_publisher_action,
    }
    if item.multimodal_context:
        payload["multimodalContext"] = item.multimodal_context
    if item.reasoning_context:
        payload["reasoningContext"] = item.reasoning_context
    return payload


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    candidate_map = _load_json(CANDIDATE_MAP_PATH)
    candidate_summary = _load_json(CANDIDATE_SUMMARY_PATH)
    stability_audit = _load_json(STABILITY_AUDIT_PATH)
    watch_escalations = _load_json(RECURSIVE_ESCALATIONS_PATH)
    donation_audit = _load_json(DONATION_AUDIT_PATH)
    donation_decisions = _load_json(DONATION_DECISIONS_PATH)
    attention_updates = _load_json(ATTENTION_UPDATES_PATH)
    drift_map = _load_json(DRIFT_MAP_PATH)

    candidates = candidate_map.get("candidates") if isinstance(candidate_map.get("candidates"), list) else []
    decisions = [
        evaluate_candidate(
            c,
            candidate_summary=candidate_summary,
            stability_audit=stability_audit,
            watch_escalations=watch_escalations,
            donation_audit=donation_audit,
            donation_decisions=donation_decisions,
            attention_updates=attention_updates,
            drift_map=drift_map,
        )
        for c in candidates
        if isinstance(c, dict)
    ]
    decisions = sorted(decisions, key=lambda d: d.candidate_id)

    created_at = _resolve_created_at(candidate_summary, candidate_map, stability_audit)
    phaselock = (
        "raw input -> CoherenceLattice projection -> Sophia admission -> Publisher memory -> "
        "reasoning / monitoring / multimodal overlays -> CoherenceLattice promotion candidate formalization -> "
        "Sophia promotion audit -> Publisher review docket -> human review"
    )

    audit_payload = {
        "schema": "promotion_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "governanceMode": "human-review-recommendation-only",
        "caution": "No automatic canonical promotion occurs in this phase; recommendations only prepare a human review docket.",
        "audits": [_item_to_payload(item) for item in decisions],
    }
    recommendations_payload = {
        "schema": "promotion_recommendations_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice candidate formalization -> Sophia promotion audit -> Publisher review docket",
        "caution": "recommend-human-review indicates editorial docketing only; canonical truth remains unchanged until explicit human review.",
        "recommendations": [_item_to_payload(item) for item in decisions],
    }

    Draft202012Validator(_load_json(PROMOTION_AUDIT_SCHEMA)).validate(audit_payload)
    Draft202012Validator(_load_json(PROMOTION_RECOMMENDATIONS_SCHEMA)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main() -> int:
    audit_payload, recommendations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    PROMOTION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    PROMOTION_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {PROMOTION_AUDIT_OUT}")
    print(f"Wrote {PROMOTION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
