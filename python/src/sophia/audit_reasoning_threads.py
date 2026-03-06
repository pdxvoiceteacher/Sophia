from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

THREAD_MAP_PATH = BRIDGE_DIR / "reasoning_thread_map.json"
THREAD_SUMMARY_PATH = BRIDGE_DIR / "reasoning_thread_summary.json"
COHERENCE_DRIFT_PATH = BRIDGE_DIR / "coherence_drift_map.json"
COHERENCE_ASSESSMENT_PATH = BRIDGE_DIR / "coherence_assessment.json"
RECOMMENDATIONS_PATH = BRIDGE_DIR / "sophia_recommendations.json"
ATTENTION_UPDATES_PATH = BRIDGE_DIR / "attention_updates.json"

REASONING_AUDIT_OUT = BRIDGE_DIR / "reasoning_audit.json"
RECURSIVE_CANDIDATES_OUT = BRIDGE_DIR / "recursive_reasoning_candidates.json"

REASONING_AUDIT_SCHEMA = SCHEMA_DIR / "reasoning_audit_v1.schema.json"
RECURSIVE_CANDIDATES_SCHEMA = SCHEMA_DIR / "recursive_reasoning_candidates_v1.schema.json"


@dataclass(slots=True)
class ThreadDecision:
    thread_id: str
    audit_status: str
    coherence_score: float
    risk_score: float
    drift_context: dict[str, Any]
    attention_context: dict[str, Any]
    governing_rule: str
    recursive_potential_score: float
    cognitive_watch_signals: list[str]
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
        "defer": "hold",
        "reject": "suppress",
        "watch": "annotate",
    }[status]


def _thread_drift(thread: dict[str, Any], drift_map: dict[str, Any]) -> float:
    base = _clamp01(float(drift_map.get("globalDriftScore", 0.0)))
    by_node = drift_map.get("driftByNode")
    if not isinstance(by_node, dict):
        return base
    concept_ids = thread.get("linkedConceptIds")
    if not isinstance(concept_ids, list) or not concept_ids:
        return base
    vals: list[float] = []
    for cid in concept_ids:
        if not isinstance(cid, str):
            continue
        node_id = cid.split(":")[-1]
        dv = by_node.get(node_id)
        if isinstance(dv, (int, float)):
            vals.append(_clamp01(dv))
    if not vals:
        return base
    return _clamp01(sum(vals) / len(vals))


def _attention_for_thread(thread: dict[str, Any], attention_updates: dict[str, Any]) -> tuple[float, int]:
    updates = attention_updates.get("updates") if isinstance(attention_updates, dict) else []
    if not isinstance(updates, list):
        return 0.0, 0

    concept_ids = thread.get("linkedConceptIds")
    targets = {c.split(":")[-1] for c in concept_ids if isinstance(c, str)} if isinstance(concept_ids, list) else set()
    if not targets:
        return 0.0, 0

    vals: list[float] = []
    for row in updates:
        if not isinstance(row, dict):
            continue
        target = row.get("targetId")
        if not isinstance(target, str):
            continue
        if target in targets:
            w = row.get("updated_weight")
            if isinstance(w, (int, float)):
                vals.append(float(w))
    if not vals:
        return 0.0, 0
    return _clamp01(sum(vals) / len(vals)), len(vals)


def evaluate_thread(
    thread: dict[str, Any],
    *,
    global_coherence: float,
    global_risk: float,
    drift_map: dict[str, Any],
    attention_updates: dict[str, Any],
) -> ThreadDecision:
    thread_id = str(thread.get("threadId") or "thread:unknown")
    recursive_potential = _clamp01(float(thread.get("recursivePotentialScore", 0.0)))
    psi = _clamp01(float(thread.get("psiAggregate", global_coherence)))
    transition_valid = bool(thread.get("transitionValidity", False))
    requires_exec_review = bool(thread.get("requiresExecutiveReview", False))

    contradiction_flags = thread.get("contradictionFlags") if isinstance(thread.get("contradictionFlags"), list) else []
    contradiction_pressure = min(0.45, 0.15 * len(contradiction_flags))

    drift = _thread_drift(thread, drift_map)
    attention_strength, linked_attention_targets = _attention_for_thread(thread, attention_updates)

    coherence_score = _clamp01(0.35 * global_coherence + 0.35 * psi + 0.20 * recursive_potential + 0.10 * attention_strength)
    risk_score = _clamp01(
        0.45 * global_risk
        + 0.30 * drift
        + contradiction_pressure
        + (0.12 if not transition_valid else 0.0)
        + (0.08 if requires_exec_review else 0.0)
    )

    watch_signals: list[str] = []
    if transition_valid:
        watch_signals.append("multi-step coherence persistence")
    if len(contradiction_flags) == 0:
        watch_signals.append("low contradiction")
    if recursive_potential >= 0.65:
        watch_signals.append("stable concept reuse")
    if drift <= 0.30:
        watch_signals.append("low drift retention")

    if risk_score >= 0.80:
        status = "reject"
        rule = "critical-risk-suppress"
        explanation = "Thread rejected due to critical risk and contradiction pressure in governance audit context."
    elif risk_score >= 0.60:
        status = "defer"
        rule = "elevated-risk-hold"
        explanation = "Thread deferred because elevated risk exceeds safe presentation threshold."
    elif recursive_potential >= 0.80 and coherence_score >= 0.78 and risk_score <= 0.30 and transition_valid:
        status = "promote"
        rule = "high-coherence-recursive-candidate"
        explanation = "Thread promoted for surface-level presentation as a high-confidence recursive reasoning candidate."
    elif recursive_potential >= 0.65 and coherence_score >= 0.62 and risk_score <= 0.45:
        status = "watch"
        rule = "recursive-watch-observational"
        explanation = "Thread placed on recursive watchlist; candidate signal remains observational and governance-bound."
    else:
        status = "observe"
        rule = "baseline-observe"
        explanation = "Thread remains in observational audit state pending stronger coherence persistence evidence."

    if requires_exec_review and status == "observe":
        status = "defer"
        rule = "executive-review-hold"
        explanation = "Executive review flag requires hold before reasoning-thread presentation."

    return ThreadDecision(
        thread_id=thread_id,
        audit_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        drift_context={
            "globalDriftScore": round(_clamp01(float(drift_map.get("globalDriftScore", 0.0))), 6),
            "threadDriftScore": round(drift, 6),
            "contradictionCount": len(contradiction_flags),
        },
        attention_context={
            "meanAttentionWeight": round(attention_strength, 6),
            "linkedAttentionTargets": linked_attention_targets,
        },
        governing_rule=rule,
        recursive_potential_score=round(recursive_potential, 6),
        cognitive_watch_signals=watch_signals,
        explanation=(
            f"{explanation} threadId={thread_id}, coherence={coherence_score:.3f}, risk={risk_score:.3f}, "
            f"drift={drift:.3f}, recursivePotential={recursive_potential:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    thread_map = _load_json(THREAD_MAP_PATH)
    thread_summary = _load_json(THREAD_SUMMARY_PATH)
    drift_map = _load_json(COHERENCE_DRIFT_PATH)
    coherence_assessment = _load_json(COHERENCE_ASSESSMENT_PATH)
    recommendations = _load_json(RECOMMENDATIONS_PATH)
    attention_updates = _load_json(ATTENTION_UPDATES_PATH)

    global_coherence = _clamp01(float(coherence_assessment.get("coherenceScore", thread_summary.get("coherenceScore", 0.5))))
    global_risk = _clamp01(float(coherence_assessment.get("riskScore", thread_summary.get("riskScore", 0.5))))

    threads = thread_map.get("threads")
    if not isinstance(threads, list):
        threads = []

    decisions = [
        evaluate_thread(
            t,
            global_coherence=global_coherence,
            global_risk=global_risk,
            drift_map=drift_map,
            attention_updates=attention_updates,
        )
        for t in threads
        if isinstance(t, dict)
    ]
    decisions = sorted(decisions, key=lambda d: d.thread_id)

    created_at = _resolve_created_at(thread_summary, coherence_assessment, drift_map)
    recommendation_ref = recommendations.get("schema", "sophia_recommendations_v1") if isinstance(recommendations, dict) else "sophia_recommendations_v1"

    audit_payload = {
        "schema": "reasoning_audit_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice formalization -> Sophia recursive audit -> Publisher presentation",
        "governanceMode": "observational",
        "inputs": {
            "reasoning_thread_map": str(THREAD_MAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "reasoning_thread_summary": str(THREAD_SUMMARY_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "coherence_drift_map": str(COHERENCE_DRIFT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "coherence_assessment": str(COHERENCE_ASSESSMENT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sophia_recommendations": recommendation_ref,
            "attention_updates": str(ATTENTION_UPDATES_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "threads": [
            {
                "threadId": d.thread_id,
                "auditStatus": d.audit_status,
                "coherenceScore": d.coherence_score,
                "riskScore": d.risk_score,
                "driftContext": d.drift_context,
                "attentionContext": d.attention_context,
                "governingRule": d.governing_rule,
                "recursivePotentialScore": d.recursive_potential_score,
                "cognitiveWatchSignals": d.cognitive_watch_signals,
                "explanation": d.explanation,
                "targetPublisherAction": d.target_publisher_action,
            }
            for d in decisions
        ],
    }

    candidates_payload = {
        "schema": "recursive_reasoning_candidates_v1",
        "created_at": created_at,
        "caution": "Observational governance artifact; not an autonomy or AGI declaration.",
        "candidates": [
            {
                "threadId": d.thread_id,
                "auditStatus": d.audit_status,
                "coherenceScore": d.coherence_score,
                "riskScore": d.risk_score,
                "recursivePotentialScore": d.recursive_potential_score,
                "cognitiveWatchSignals": d.cognitive_watch_signals,
                "targetPublisherAction": d.target_publisher_action,
                "explanation": d.explanation,
            }
            for d in decisions
            if d.audit_status in {"watch", "promote", "observe"}
        ],
    }

    Draft202012Validator(_load_json(REASONING_AUDIT_SCHEMA)).validate(audit_payload)
    Draft202012Validator(_load_json(RECURSIVE_CANDIDATES_SCHEMA)).validate(candidates_payload)
    return audit_payload, candidates_payload


def main() -> int:
    audit_payload, candidates_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    REASONING_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    RECURSIVE_CANDIDATES_OUT.write_text(json.dumps(candidates_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {REASONING_AUDIT_OUT}")
    print(f"Wrote {RECURSIVE_CANDIDATES_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
