from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

MULTIMODAL_PROJECTION_PATH = BRIDGE_DIR / "multimodal_lattice_projection.json"
MULTIMODAL_SUMMARY_PATH = BRIDGE_DIR / "multimodal_projection_summary.json"
REINFORCEMENT_REPORT_PATH = BRIDGE_DIR / "cross_modal_reinforcement_report.json"
REINFORCEMENT_SUMMARY_PATH = BRIDGE_DIR / "cross_modal_reinforcement_summary.json"
DRIFT_MAP_PATH = BRIDGE_DIR / "coherence_drift_map.json"
THREAD_HISTORY_PATH = BRIDGE_DIR / "reasoning_thread_history.json"
STABILITY_AUDIT_PATH = BRIDGE_DIR / "stability_audit.json"
ATTENTION_UPDATES_PATH = BRIDGE_DIR / "attention_updates.json"

DONATION_AUDIT_OUT = BRIDGE_DIR / "pattern_donation_audit.json"
DONATION_DECISIONS_OUT = BRIDGE_DIR / "pattern_donation_decisions.json"

DONATION_AUDIT_SCHEMA = SCHEMA_DIR / "pattern_donation_audit_v1.schema.json"
DONATION_DECISIONS_SCHEMA = SCHEMA_DIR / "pattern_donation_decisions_v1.schema.json"


@dataclass(slots=True)
class DonationDecision:
    donation_id: str
    source_input_id: str
    target_type: str
    target_id: str
    audit_status: str
    coherence_score: float
    risk_score: float
    reinforcement_score: float
    drift_context: dict[str, Any]
    stability_context: dict[str, Any]
    cognitive_watch_signals: list[str]
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _clamp01(v: float) -> float:
    return max(0.0, min(1.0, float(v)))


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for d in docs:
        ts = d.get("created_at") if isinstance(d, dict) else None
        if isinstance(ts, str) and ts:
            return ts
    return "1970-01-01T00:00:00Z"


def _dict_by_key(items: Any, key: str) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    if isinstance(items, list):
        for row in items:
            if not isinstance(row, dict):
                continue
            v = row.get(key)
            if isinstance(v, str):
                out[v] = row
    return out


def _status_to_action(status: str) -> str:
    return {
        "observe": "watch",
        "annotate": "surface-overlay",
        "admit-overlay": "surface-overlay",
        "defer": "hold",
        "reject": "suppress",
        "watch": "watch",
    }[status]


def _thread_stability_for_target(target_id: str, thread_history: dict[str, Any], stability_audit: dict[str, Any]) -> dict[str, Any]:
    token = target_id.split(":")[-1]
    histories = thread_history.get("threads") if isinstance(thread_history, dict) else []
    audits = stability_audit.get("threads") if isinstance(stability_audit, dict) else []
    if not isinstance(histories, list):
        histories = []
    if not isinstance(audits, list):
        audits = []

    matched_obs = 0
    for h in histories:
        if not isinstance(h, dict):
            continue
        tid = h.get("threadId")
        if isinstance(tid, str) and token in tid:
            matched_obs = max(matched_obs, int(h.get("observationCount", 0)))

    stability_status = "emerging"
    for a in audits:
        if not isinstance(a, dict):
            continue
        tid = a.get("threadId")
        if isinstance(tid, str) and token in tid:
            stability_status = str(a.get("stabilityStatus") or stability_status)
            break

    return {
        "observationCount": matched_obs,
        "stabilityStatus": stability_status,
    }


def _attention_for_target(target_id: str, attention_updates: dict[str, Any]) -> float:
    target_token = target_id.split(":")[-1]
    updates = attention_updates.get("updates") if isinstance(attention_updates, dict) else []
    if not isinstance(updates, list):
        return 0.0
    vals = [
        float(u.get("updated_weight"))
        for u in updates
        if isinstance(u, dict)
        and isinstance(u.get("targetId"), str)
        and u.get("targetId") in {target_id, target_token}
        and isinstance(u.get("updated_weight"), (int, float))
    ]
    if not vals:
        return 0.0
    return _clamp01(sum(vals) / len(vals))


def evaluate_donation(
    projection: dict[str, Any],
    target_id: str,
    *,
    projection_summary: dict[str, Any],
    reinforcement_by_donation: dict[str, dict[str, Any]],
    reinforcement_by_pair: dict[tuple[str, str], dict[str, Any]],
    reinforcement_summary: dict[str, Any],
    drift_map: dict[str, Any],
    thread_history: dict[str, Any],
    stability_audit: dict[str, Any],
    attention_updates: dict[str, Any],
) -> DonationDecision:
    source_input_id = str(projection.get("inputId") or "unknown-input")
    donation_id = str(
        projection.get("donationId")
        or f"donation:{source_input_id.split(':')[-1]}:{target_id.split(':')[-1]}"
    )

    target_type = "concept" if target_id.startswith("concept:") else "thread"
    proj_conf = _clamp01(float(projection.get("projectionConfidence", 0.0)))
    requires_review = bool(projection.get("requiresExecutiveReview", False))
    contradiction_flags = projection.get("contradictionFlags") if isinstance(projection.get("contradictionFlags"), list) else []

    pair_row = reinforcement_by_pair.get((source_input_id, target_id), {})
    donation_row = reinforcement_by_donation.get(donation_id, {})
    reinforcement = _clamp01(
        float(
            donation_row.get(
                "reinforcementScore",
                pair_row.get("reinforcementScore", reinforcement_summary.get("meanReinforcementScore", 0.0)),
            )
        )
    )

    global_coherence = _clamp01(float(projection_summary.get("coherenceScore", 0.5)))
    global_risk = _clamp01(float(projection_summary.get("riskScore", 0.5)))
    drift = _clamp01(float(drift_map.get("globalDriftScore", 0.0)))

    stability_context = _thread_stability_for_target(target_id, thread_history, stability_audit)
    attention_weight = _attention_for_target(target_id, attention_updates)

    coherence = _clamp01(0.40 * proj_conf + 0.30 * global_coherence + 0.20 * reinforcement + 0.10 * attention_weight)
    contradiction_pressure = min(0.4, 0.12 * len(contradiction_flags))
    risk = _clamp01(
        0.45 * global_risk
        + 0.30 * drift
        + 0.15 * (1.0 - reinforcement)
        + contradiction_pressure
        + (0.10 if requires_review else 0.0)
    )

    watch_signals: list[str] = []
    if reinforcement >= 0.60:
        watch_signals.append("cross-modal reinforcement persistence")
    if contradiction_flags:
        watch_signals.append("projection contradiction markers")
    if stability_context.get("observationCount", 0) >= 3:
        watch_signals.append("thread continuity available")
    if attention_weight >= 0.60:
        watch_signals.append("aligned executive attention")

    if risk >= 0.80 or proj_conf < 0.25:
        status = "reject"
        rule = "critical-risk-reject"
        explanation = "Donation rejected due to critical risk or very low projection confidence."
    elif requires_review and risk >= 0.55:
        status = "defer"
        rule = "review-hold"
        explanation = "Donation deferred for additional governance review under elevated risk."
    elif coherence >= 0.72 and reinforcement >= 0.65 and risk <= 0.35 and not requires_review:
        status = "admit-overlay"
        rule = "high-coherence-overlay-admit"
        explanation = "Donation admitted as overlay-level reinforcement signal under coherent low-risk conditions."
    elif coherence >= 0.60 and risk <= 0.50:
        status = "annotate"
        rule = "annotate-balanced"
        explanation = "Donation retained as cross-modal annotation pending stronger recurrence evidence."
    elif coherence >= 0.50:
        status = "watch"
        rule = "watch-observational"
        explanation = "Donation placed on watchlist as observational reinforcement signal."
    else:
        status = "observe"
        rule = "observe-low-signal"
        explanation = "Donation remains observational due to weak coherence/reinforcement support."

    drift_context = {
        "globalDriftScore": round(drift, 6),
        "projectionRegime": str(projection.get("regime") or "unknown"),
        "requiresExecutiveReview": requires_review,
    }

    return DonationDecision(
        donation_id=donation_id,
        source_input_id=source_input_id,
        target_type=target_type,
        target_id=target_id,
        audit_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        reinforcement_score=round(reinforcement, 6),
        drift_context=drift_context,
        stability_context=stability_context,
        cognitive_watch_signals=sorted(set(watch_signals)),
        governing_rule=rule,
        explanation=(
            f"{explanation} donationId={donation_id}, source={source_input_id}, target={target_id}, "
            f"coherence={coherence:.3f}, risk={risk:.3f}, reinforcement={reinforcement:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    projection_doc = _load_json(MULTIMODAL_PROJECTION_PATH)
    projection_summary = _load_json(MULTIMODAL_SUMMARY_PATH)
    reinforcement_report = _load_json(REINFORCEMENT_REPORT_PATH)
    reinforcement_summary = _load_json(REINFORCEMENT_SUMMARY_PATH)
    drift_map = _load_json(DRIFT_MAP_PATH)
    thread_history = _load_json(THREAD_HISTORY_PATH)
    stability_audit = _load_json(STABILITY_AUDIT_PATH)
    attention_updates = _load_json(ATTENTION_UPDATES_PATH)

    reinforcement_rows = reinforcement_report.get("reinforcements")
    if not isinstance(reinforcement_rows, list):
        reinforcement_rows = []

    reinforcement_by_donation = _dict_by_key(reinforcement_rows, "donationId")
    reinforcement_by_pair: dict[tuple[str, str], dict[str, Any]] = {}
    for row in reinforcement_rows:
        if not isinstance(row, dict):
            continue
        src = row.get("sourceInputId")
        tgt = row.get("targetId")
        if isinstance(src, str) and isinstance(tgt, str):
            reinforcement_by_pair[(src, tgt)] = row

    projections = projection_doc.get("projections")
    if not isinstance(projections, list):
        projections = []

    decisions: list[DonationDecision] = []
    for proj in projections:
        if not isinstance(proj, dict):
            continue
        targets = proj.get("projectedConceptIds")
        if not isinstance(targets, list):
            targets = []
        for target in targets:
            if not isinstance(target, str):
                continue
            decisions.append(
                evaluate_donation(
                    proj,
                    target,
                    projection_summary=projection_summary,
                    reinforcement_by_donation=reinforcement_by_donation,
                    reinforcement_by_pair=reinforcement_by_pair,
                    reinforcement_summary=reinforcement_summary,
                    drift_map=drift_map,
                    thread_history=thread_history,
                    stability_audit=stability_audit,
                    attention_updates=attention_updates,
                )
            )

    decisions = sorted(decisions, key=lambda d: (d.donation_id, d.source_input_id, d.target_id))
    created_at = _resolve_created_at(projection_summary, reinforcement_summary, projection_doc)

    audit_payload = {
        "schema": "pattern_donation_audit_v1",
        "created_at": created_at,
        "phaselock": "raw multimodal input -> feature bundle -> CoherenceLattice multimodal projection -> Sophia pattern audit -> Publisher multimodal overlay -> CoherenceLattice cross-modal reinforcement analysis -> Sophia donation significance audit -> Publisher cross-modal presentation",
        "governanceMode": "observational",
        "donations": [
            {
                "donationId": d.donation_id,
                "sourceInputId": d.source_input_id,
                "targetType": d.target_type,
                "targetId": d.target_id,
                "auditStatus": d.audit_status,
                "coherenceScore": d.coherence_score,
                "riskScore": d.risk_score,
                "reinforcementScore": d.reinforcement_score,
                "driftContext": d.drift_context,
                "stabilityContext": d.stability_context,
                "cognitiveWatchSignals": d.cognitive_watch_signals,
                "governingRule": d.governing_rule,
                "explanation": d.explanation,
                "targetPublisherAction": d.target_publisher_action,
            }
            for d in decisions
        ],
    }

    decisions_payload = {
        "schema": "pattern_donation_decisions_v1",
        "created_at": created_at,
        "caution": "admit-overlay allows cross-modal annotation only; canonical graph truth remains unchanged.",
        "decisions": [
            {
                "donationId": d.donation_id,
                "sourceInputId": d.source_input_id,
                "targetType": d.target_type,
                "targetId": d.target_id,
                "auditStatus": d.audit_status,
                "coherenceScore": d.coherence_score,
                "riskScore": d.risk_score,
                "reinforcementScore": d.reinforcement_score,
                "driftContext": d.drift_context,
                "stabilityContext": d.stability_context,
                "cognitiveWatchSignals": d.cognitive_watch_signals,
                "governingRule": d.governing_rule,
                "explanation": d.explanation,
                "targetPublisherAction": d.target_publisher_action,
            }
            for d in decisions
        ],
    }

    Draft202012Validator(_load_json(DONATION_AUDIT_SCHEMA)).validate(audit_payload)
    Draft202012Validator(_load_json(DONATION_DECISIONS_SCHEMA)).validate(decisions_payload)
    return audit_payload, decisions_payload


def main() -> int:
    audit_payload, decisions_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    DONATION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    DONATION_DECISIONS_OUT.write_text(json.dumps(decisions_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {DONATION_AUDIT_OUT}")
    print(f"Wrote {DONATION_DECISIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
