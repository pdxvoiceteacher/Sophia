from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"

PATTERN_DONATION_AUDIT_PATH = BRIDGE_DIR / "pattern_donation_audit.json"
PATTERN_DONATION_DECISIONS_PATH = BRIDGE_DIR / "pattern_donation_decisions.json"
PATTERN_AUDIT_PATH = BRIDGE_DIR / "pattern_audit.json"

PATTERN_TEMPORAL_AUDIT_OUT = BRIDGE_DIR / "pattern_temporal_audit.json"
PATTERN_TEMPORAL_RECOMMENDATIONS_OUT = BRIDGE_DIR / "pattern_temporal_recommendations.json"


@dataclass(slots=True)
class PatternTemporalDecision:
    target_id: str
    target_type: str
    pattern_status: str
    coherence_score: float
    risk_score: float
    temporal_context: str
    contradiction_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in ("records", "decisions", "donations", "targets"):
        value = payload.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, dict)]
    return []


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
        "pattern-transient": "watch",
        "pattern-recurring": "watch",
        "pattern-strengthening": "docket",
        "pattern-decaying": "watch",
        "pattern-require-human-review": "docket",
    }[status]


def evaluate_target(row: dict[str, Any], *, system_risk: float) -> PatternTemporalDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "pattern-target")

    coherence = _clamp01(float(row.get("coherenceScore", 0.5)))
    base_risk = _clamp01(float(row.get("riskScore", 0.45)))
    reinforcement = _clamp01(float(row.get("reinforcementScore", 0.5)))

    stability = row.get("stabilityContext") if isinstance(row.get("stabilityContext"), dict) else {}
    observation_count = int(stability.get("observationCount", 0) or 0)
    stability_status = str(stability.get("stabilityStatus", "unknown")).strip().lower()

    trend_score = _clamp01(float(row.get("trendScore", row.get("momentumScore", reinforcement))))
    decay_risk = _clamp01(float(row.get("decayRisk", row.get("fadeRisk", 1.0 - reinforcement))))
    recurrence_score = _clamp01(float(row.get("recurrenceScore", min(1.0, observation_count / 6.0))))

    drift = row.get("driftContext") if isinstance(row.get("driftContext"), dict) else {}
    global_drift = _clamp01(float(drift.get("globalDriftScore", 0.4)))
    requires_exec_review = bool(drift.get("requiresExecutiveReview", False))

    risk = _clamp01(0.30 * base_risk + 0.22 * global_drift + 0.18 * decay_risk + 0.16 * (1.0 - trend_score) + 0.14 * system_risk)

    if requires_exec_review or risk >= 0.78:
        status = "pattern-require-human-review"
        rule = "human-review-under-escalated-temporal-risk"
    elif trend_score >= 0.72 and recurrence_score >= 0.60 and decay_risk <= 0.34 and coherence >= 0.58:
        status = "pattern-strengthening"
        rule = "strengthening-under-consistent-reinforcement"
    elif decay_risk >= 0.62 or stability_status in {"decaying", "fading"}:
        status = "pattern-decaying"
        rule = "decay-detection-temporal-watch"
    elif recurrence_score >= 0.50 or observation_count >= 3:
        status = "pattern-recurring"
        rule = "recurring-pattern-observation"
    else:
        status = "pattern-transient"
        rule = "transient-pattern-preconfirmation"

    temporal_context = (
        f"observationCount={observation_count}, recurrenceScore={recurrence_score:.3f}, trendScore={trend_score:.3f}, "
        f"decayRisk={decay_risk:.3f}, stabilityStatus={stability_status}"
    )
    contradiction_context = (
        f"riskScore={base_risk:.3f}, globalDriftScore={global_drift:.3f}, systemRisk={system_risk:.3f}; "
        "temporal assessments are bounded interpretive guidance only."
    )
    explanation = (
        f"Pattern temporal guidance is bounded and non-accusatory. targetId={target_id}, patternStatus={status}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return PatternTemporalDecision(
        target_id=target_id,
        target_type=target_type,
        pattern_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        temporal_context=temporal_context,
        contradiction_context=contradiction_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(decision: PatternTemporalDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "patternStatus": decision.pattern_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "temporalContext": decision.temporal_context,
        "contradictionContext": decision.contradiction_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    donation_audit = _load_json(PATTERN_DONATION_AUDIT_PATH)
    donation_decisions = _load_json(PATTERN_DONATION_DECISIONS_PATH)
    pattern_audit = _load_json(PATTERN_AUDIT_PATH) if PATTERN_AUDIT_PATH.exists() else {"records": []}

    pattern_rows = _rows(pattern_audit)
    system_risk = _clamp01(
        sum(float(row.get("riskScore", 0.45)) for row in pattern_rows if isinstance(row.get("riskScore"), (int, float))) / max(1, len(pattern_rows))
        if pattern_rows
        else 0.45
    )

    source_rows = _rows(donation_decisions) or _rows(donation_audit)
    decisions = sorted((evaluate_target(row, system_risk=system_risk) for row in source_rows), key=lambda d: d.target_id)

    created_at = _resolve_created_at(donation_decisions, donation_audit, pattern_audit)
    phaselock = (
        "pattern donation audit -> temporal persistence evaluation -> Sophia temporal pattern audit -> "
        "Publisher bounded temporal overlays -> human/community review"
    )
    caution = "Pattern temporal recommendations are bounded guidance only and do not establish factual allegations."

    metadata = {
        "systemRisk": round(system_risk, 6),
        "inputs": [
            "bridge/pattern_donation_audit.json",
            "bridge/pattern_donation_decisions.json",
            "bridge/pattern_audit.json",
        ],
    }

    audit_payload = {
        "schema": "pattern_temporal_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(decision) for decision in decisions],
    }
    recommendations_payload = {
        "schema": "pattern_temporal_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(decision) for decision in decisions],
    }
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia temporal pattern-state audit")
    parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs()
    PATTERN_TEMPORAL_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    PATTERN_TEMPORAL_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"Wrote {PATTERN_TEMPORAL_AUDIT_OUT}")
    print(f"Wrote {PATTERN_TEMPORAL_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
