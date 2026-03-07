from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

THREAD_HISTORY_PATH = BRIDGE_DIR / "reasoning_thread_history.json"
MONITOR_REPORT_PATH = BRIDGE_DIR / "coherence_monitor_report.json"
MONITOR_SUMMARY_PATH = BRIDGE_DIR / "coherence_monitor_summary.json"
REASONING_AUDIT_PATH = BRIDGE_DIR / "reasoning_audit.json"
RECURSIVE_CANDIDATES_PATH = BRIDGE_DIR / "recursive_reasoning_candidates.json"
DRIFT_MAP_PATH = BRIDGE_DIR / "coherence_drift_map.json"
ATTENTION_UPDATES_PATH = BRIDGE_DIR / "attention_updates.json"

STABILITY_AUDIT_OUT = BRIDGE_DIR / "stability_audit.json"
ESCALATIONS_OUT = BRIDGE_DIR / "recursive_watch_escalations.json"

STABILITY_SCHEMA_PATH = SCHEMA_DIR / "stability_audit_v1.schema.json"
ESCALATIONS_SCHEMA_PATH = SCHEMA_DIR / "recursive_watch_escalations_v1.schema.json"


@dataclass(slots=True)
class StabilityDecision:
    thread_id: str
    stability_status: str
    audit_status: str
    coherence_score: float
    risk_score: float
    persistence_score: float
    drift_context: dict[str, Any]
    contradiction_context: dict[str, Any]
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


def _status_to_action(status: str) -> str:
    return {
        "observe": "annotate",
        "promote": "surface",
        "hold": "hold",
        "escalate-human-review": "watch",
        "suppress": "hold",
    }[status]


def _dict_by_thread(items: Any, key: str = "threadId") -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    if isinstance(items, list):
        for row in items:
            if not isinstance(row, dict):
                continue
            thread_id = row.get(key)
            if isinstance(thread_id, str):
                out[thread_id] = row
    return out


def _attention_context(thread_id: str, reasoning_audit_row: dict[str, Any], attention_updates: dict[str, Any]) -> dict[str, Any]:
    target_count = 0
    mean_weight = 0.0
    updates = attention_updates.get("updates")
    if isinstance(updates, list):
        vals = [float(u.get("updated_weight")) for u in updates if isinstance(u, dict) and isinstance(u.get("updated_weight"), (int, float))]
        if vals:
            mean_weight = _clamp01(sum(vals) / len(vals))
            target_count = len(vals)

    existing = reasoning_audit_row.get("attentionContext") if isinstance(reasoning_audit_row, dict) else {}
    if isinstance(existing, dict):
        if isinstance(existing.get("meanAttentionWeight"), (int, float)):
            mean_weight = _clamp01(float(existing["meanAttentionWeight"]))
        if isinstance(existing.get("linkedAttentionTargets"), int):
            target_count = int(existing["linkedAttentionTargets"])

    return {
        "threadId": thread_id,
        "meanAttentionWeight": round(mean_weight, 6),
        "linkedAttentionTargets": target_count,
    }


def _compute_stability_status(coh_trend: str, drift_trend: str, contradiction_trend: str, persistence: float) -> str:
    coh = coh_trend.lower()
    dr = drift_trend.lower()
    ctr = contradiction_trend.lower()

    if ("rising" in coh or "stable" in coh) and ("falling" in dr or "stable-low" in dr) and persistence >= 0.65 and "low" in ctr:
        return "stable"
    if "falling" in coh and ("rising" in dr or "high" in ctr):
        return "degrading"
    if "oscillat" in coh or "oscillat" in dr:
        return "oscillating"
    return "emerging"


def evaluate_thread(
    thread_history: dict[str, Any],
    monitor_report: dict[str, Any],
    reasoning_audit_row: dict[str, Any],
    recursive_candidate_row: dict[str, Any] | None,
    *,
    global_coherence: float,
    global_risk: float,
    global_drift: float,
    attention_updates: dict[str, Any],
) -> StabilityDecision:
    thread_id = str(thread_history.get("threadId") or monitor_report.get("threadId") or "thread:unknown")

    report_coh = _clamp01(float(monitor_report.get("coherenceScore", 0.0)))
    base_coh = _clamp01(float(reasoning_audit_row.get("coherenceScore", global_coherence)))
    coherence = _clamp01(0.65 * base_coh + 0.35 * report_coh)

    report_risk = _clamp01(float(monitor_report.get("riskScore", 0.0)))
    contradiction_trend = str(monitor_report.get("contradictionTrend", "stable-low"))
    contradiction_high = 0.18 if "high" in contradiction_trend else 0.0
    risk = _clamp01(0.60 * global_risk + 0.30 * report_risk + 0.10 * global_drift + contradiction_high)

    persistence = _clamp01(float(monitor_report.get("persistenceScore", 0.0)))
    coh_trend = str(monitor_report.get("coherenceTrend", "emerging"))
    drift_trend = str(monitor_report.get("driftTrend", "stable"))

    stability = _compute_stability_status(coh_trend, drift_trend, contradiction_trend, persistence)

    watch_signals: list[str] = []
    monitor_flags = monitor_report.get("monitorFlags")
    if isinstance(monitor_flags, list):
        watch_signals.extend(str(x) for x in monitor_flags)

    if persistence >= 0.70:
        watch_signals.append("stable multi-cycle coherence")
    if "falling" in drift_trend.lower():
        watch_signals.append("decreasing drift")
    if recursive_candidate_row is not None:
        watch_signals.append("recursive candidate continuity")

    requires_exec_review = bool(monitor_report.get("requiresExecutiveReview", False))

    if stability == "degrading" and (risk >= 0.65 or requires_exec_review):
        audit_status = "escalate-human-review"
        rule = "degrading-high-risk-human-review"
        explanation = "Longitudinal degradation with elevated risk requires explicit human review priority."
    elif stability == "stable" and persistence >= 0.75 and risk <= 0.30:
        audit_status = "promote"
        rule = "persistent-high-coherence-low-risk"
        explanation = "Thread has remained coherent across repeated observations with controlled risk and drift."
    elif stability == "oscillating":
        audit_status = "hold"
        rule = "oscillation-hold"
        explanation = "Oscillating longitudinal profile is held for additional monitoring before presentation changes."
    elif risk >= 0.80:
        audit_status = "suppress"
        rule = "critical-risk-suppress"
        explanation = "Critical risk during longitudinal monitoring requires suppression of thread overlay."
    else:
        audit_status = "observe"
        rule = "observational-monitoring"
        explanation = "Thread remains in observational monitoring without escalation or suppression."

    drift_context = {
        "globalDriftScore": round(global_drift, 6),
        "driftTrend": drift_trend,
    }
    contradiction_context = {
        "contradictionTrend": contradiction_trend,
        "requiresExecutiveReview": requires_exec_review,
    }

    return StabilityDecision(
        thread_id=thread_id,
        stability_status=stability,
        audit_status=audit_status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        persistence_score=round(persistence, 6),
        drift_context=drift_context,
        contradiction_context=contradiction_context,
        cognitive_watch_signals=sorted(set(watch_signals)),
        governing_rule=rule,
        explanation=(
            f"{explanation} threadId={thread_id}, stability={stability}, coherence={coherence:.3f}, "
            f"risk={risk:.3f}, persistence={persistence:.3f}."
        ),
        target_publisher_action=_status_to_action(audit_status),
    )


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    history_doc = _load_json(THREAD_HISTORY_PATH)
    report_doc = _load_json(MONITOR_REPORT_PATH)
    summary_doc = _load_json(MONITOR_SUMMARY_PATH)
    reasoning_audit = _load_json(REASONING_AUDIT_PATH)
    recursive_candidates = _load_json(RECURSIVE_CANDIDATES_PATH)
    drift_doc = _load_json(DRIFT_MAP_PATH)
    attention_doc = _load_json(ATTENTION_UPDATES_PATH)

    global_coherence = _clamp01(float(summary_doc.get("coherenceScore", 0.5)))
    global_risk = _clamp01(float(summary_doc.get("riskScore", 0.5)))
    global_drift = _clamp01(float(drift_doc.get("globalDriftScore", summary_doc.get("globalDriftScore", 0.0))))

    histories = _dict_by_thread(history_doc.get("threads"))
    reports = _dict_by_thread(report_doc.get("reports"))
    reasoning_rows = _dict_by_thread(reasoning_audit.get("threads"))
    candidate_rows = _dict_by_thread(recursive_candidates.get("candidates"))

    thread_ids = sorted(set(histories) | set(reports) | set(reasoning_rows))

    decisions: list[StabilityDecision] = []
    for thread_id in thread_ids:
        decisions.append(
            evaluate_thread(
                histories.get(thread_id, {"threadId": thread_id}),
                reports.get(thread_id, {"threadId": thread_id}),
                reasoning_rows.get(thread_id, {"threadId": thread_id}),
                candidate_rows.get(thread_id),
                global_coherence=global_coherence,
                global_risk=global_risk,
                global_drift=global_drift,
                attention_updates=attention_doc,
            )
        )

    decisions = sorted(decisions, key=lambda d: d.thread_id)
    created_at = _resolve_created_at(summary_doc, report_doc, history_doc)

    audit_payload = {
        "schema": "stability_audit_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice monitor -> Sophia stability audit -> Publisher monitoring overlays",
        "threads": [
            {
                "threadId": d.thread_id,
                "stabilityStatus": d.stability_status,
                "auditStatus": d.audit_status,
                "coherenceScore": d.coherence_score,
                "riskScore": d.risk_score,
                "persistenceScore": d.persistence_score,
                "driftContext": d.drift_context,
                "contradictionContext": d.contradiction_context,
                "cognitiveWatchSignals": d.cognitive_watch_signals,
                "governingRule": d.governing_rule,
                "explanation": d.explanation,
                "targetPublisherAction": d.target_publisher_action,
            }
            for d in decisions
        ],
    }

    escalations_payload = {
        "schema": "recursive_watch_escalations_v1",
        "created_at": created_at,
        "caution": "Escalation indicates audit visibility/human review priority, not autonomy escalation.",
        "escalations": [
            {
                "threadId": d.thread_id,
                "stabilityStatus": d.stability_status,
                "auditStatus": d.audit_status,
                "coherenceScore": d.coherence_score,
                "riskScore": d.risk_score,
                "persistenceScore": d.persistence_score,
                "cognitiveWatchSignals": d.cognitive_watch_signals,
                "governingRule": d.governing_rule,
                "targetPublisherAction": d.target_publisher_action,
                "explanation": d.explanation,
            }
            for d in decisions
            if d.audit_status in {"promote", "escalate-human-review", "hold"}
        ],
    }

    Draft202012Validator(_load_json(STABILITY_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(ESCALATIONS_SCHEMA_PATH)).validate(escalations_payload)
    return audit_payload, escalations_payload


def main() -> int:
    audit_payload, escalations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    STABILITY_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    ESCALATIONS_OUT.write_text(json.dumps(escalations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {STABILITY_AUDIT_OUT}")
    print(f"Wrote {ESCALATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
