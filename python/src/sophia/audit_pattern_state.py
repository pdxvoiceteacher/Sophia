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
VERIFICATION_AUDIT_PATH = BRIDGE_DIR / "verification_audit.json"
PUBLIC_RECORD_AUDIT_PATH = BRIDGE_DIR / "public_record_audit.json"

PATTERN_AUDIT_OUT = BRIDGE_DIR / "pattern_audit.json"
PATTERN_RECOMMENDATIONS_OUT = BRIDGE_DIR / "pattern_recommendations.json"


@dataclass(slots=True)
class PatternDecision:
    target_id: str
    target_type: str
    pattern_status: str
    coherence_score: float
    risk_score: float
    pattern_context: str
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


def _safe_mean(values: list[float], default: float) -> float:
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
        "pattern-watch": "watch",
        "pattern-verify-first": "suppress",
        "pattern-provisional": "watch",
        "pattern-require-human-review": "docket",
    }[status]


def _normalize_action(action: str) -> str:
    return {
        "docket": "docket",
        "watch": "watch",
        "suppress": "suppress",
        "surface-overlay": "watch",
    }.get(action, "watch")


def evaluate_target(row: dict[str, Any], *, system_risk: float) -> PatternDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "pattern-target")

    coherence = _clamp01(float(row.get("coherenceScore", 0.5)))
    base_risk = _clamp01(float(row.get("riskScore", 0.45)))
    reinforcement = _clamp01(float(row.get("reinforcementScore", 0.5)))

    drift = row.get("driftContext") if isinstance(row.get("driftContext"), dict) else {}
    global_drift = _clamp01(float(drift.get("globalDriftScore", 0.4)))
    requires_exec_review = bool(drift.get("requiresExecutiveReview", False))

    stability = row.get("stabilityContext") if isinstance(row.get("stabilityContext"), dict) else {}
    observation_count = int(stability.get("observationCount", 0) or 0)
    stability_status = str(stability.get("stabilityStatus", "unknown"))

    risk = _clamp01(0.46 * base_risk + 0.24 * global_drift + 0.18 * system_risk + 0.12 * (1.0 - reinforcement))

    if requires_exec_review or (global_drift >= 0.78 and base_risk >= 0.60):
        status = "pattern-require-human-review"
        rule = "executive-review-or-high-drift"
    elif base_risk >= 0.62 or coherence <= 0.38:
        status = "pattern-verify-first"
        rule = "verify-first-under-weak-pattern-confidence"
    elif risk >= 0.46 or observation_count < 3 or stability_status not in {"stable", "converged"}:
        status = "pattern-watch"
        rule = "watch-pattern-drift-and-recurrence"
    else:
        status = "pattern-provisional"
        rule = "provisional-pattern-with-bounded-confidence"

    pattern_context = (
        f"coherenceScore={coherence:.3f}, reinforcementScore={reinforcement:.3f}, observationCount={observation_count}, "
        f"stabilityStatus={stability_status}"
    )
    contradiction_context = (
        f"riskScore={base_risk:.3f}, globalDriftScore={global_drift:.3f}, systemRisk={system_risk:.3f}; "
        "pattern outputs are bounded interpretive guidance only."
    )
    explanation = (
        f"Pattern guidance is bounded and non-accusatory. targetId={target_id}, patternStatus={status}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return PatternDecision(
        target_id=target_id,
        target_type=target_type,
        pattern_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        pattern_context=pattern_context,
        contradiction_context=contradiction_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(decision: PatternDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "patternStatus": decision.pattern_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "patternContext": decision.pattern_context,
        "contradictionContext": decision.contradiction_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    pattern_audit = _load_json(PATTERN_DONATION_AUDIT_PATH)
    pattern_decisions = _load_json(PATTERN_DONATION_DECISIONS_PATH)

    verification = _load_json(VERIFICATION_AUDIT_PATH) if VERIFICATION_AUDIT_PATH.exists() else {"records": []}
    public_record = _load_json(PUBLIC_RECORD_AUDIT_PATH) if PUBLIC_RECORD_AUDIT_PATH.exists() else {"records": []}

    verification_risk = _safe_mean(
        [float(row.get("riskScore")) for row in _rows(verification) if isinstance(row.get("riskScore"), (int, float))],
        0.45,
    )
    public_record_risk = _safe_mean(
        [float(row.get("riskScore")) for row in _rows(public_record) if isinstance(row.get("riskScore"), (int, float))],
        0.45,
    )
    system_risk = _clamp01(0.52 * verification_risk + 0.48 * public_record_risk)

    source_rows = _rows(pattern_decisions) or _rows(pattern_audit)
    decisions = sorted((evaluate_target(row, system_risk=system_risk) for row in source_rows), key=lambda d: d.target_id)

    created_at = _resolve_created_at(pattern_decisions, pattern_audit, verification, public_record)
    phaselock = (
        "raw multimodal input -> CoherenceLattice pattern donation formalization -> Sophia pattern-state audit -> "
        "Publisher bounded pattern overlays -> human/community review"
    )
    caution = "Pattern recommendations are bounded guidance only and do not establish facts or allegations."

    metadata = {
        "systemRisk": round(system_risk, 6),
        "upstreamPublisherActionHint": _normalize_action(str((source_rows[0].get("targetPublisherAction") if source_rows else "watch"))),
        "inputs": [
            "bridge/pattern_donation_audit.json",
            "bridge/pattern_donation_decisions.json",
            "bridge/verification_audit.json",
            "bridge/public_record_audit.json",
        ],
    }

    audit_payload = {
        "schema": "pattern_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(item) for item in decisions],
    }
    recommendations_payload = {
        "schema": "pattern_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(item) for item in decisions],
    }
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia pattern-state audit")
    parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs()
    PATTERN_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    PATTERN_RECOMMENDATIONS_OUT.write_text(json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {PATTERN_AUDIT_OUT}")
    print(f"Wrote {PATTERN_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
