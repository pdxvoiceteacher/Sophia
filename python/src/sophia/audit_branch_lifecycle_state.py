from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"

BRANCH_EMERGENCE_REPORT_PATH = BRIDGE_DIR / "branch_emergence_report.json"
ACTION_FUNCTIONAL_SCORECARD_PATH = BRIDGE_DIR / "action_functional_scorecard.json"
TELEMETRY_FIELD_AUDIT_PATH = BRIDGE_DIR / "telemetry_field_audit.json"
COLLABORATIVE_REVIEW_AUDIT_PATH = BRIDGE_DIR / "collaborative_review_audit.json"
CAUSAL_AUDIT_PATH = BRIDGE_DIR / "causal_audit.json"

BRANCH_LIFECYCLE_AUDIT_OUT = BRIDGE_DIR / "branch_lifecycle_audit.json"
BRANCH_LIFECYCLE_RECOMMENDATIONS_OUT = BRIDGE_DIR / "branch_lifecycle_recommendations.json"


@dataclass(slots=True)
class BranchLifecycleDecision:
    target_id: str
    target_type: str
    branch_status: str
    coherence_score: float
    risk_score: float
    lifecycle_context: str
    maturity_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in ("records", "recommendations", "targets", "branches"):
        value = payload.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, dict)]
    return []


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _safe_mean(values: list[float], default: float) -> float:
    return sum(values) / len(values) if values else default


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for doc in docs:
        for key in ("generatedAt", "created_at"):
            value = doc.get(key)
            if isinstance(value, str) and value:
                return value
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str) -> str:
    return {
        "branch-watch": "watch",
        "branch-verify-first": "suppress",
        "branch-provisional": "watch",
        "branch-stable-candidate": "docket",
        "branch-decay": "watch",
        "branch-require-human-review": "docket",
    }[status]


def evaluate_target(
    row: dict[str, Any],
    *,
    taf_rows: dict[str, dict[str, Any]],
    telemetry_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> BranchLifecycleDecision:
    target_id = str(row.get("targetId") or row.get("branchId") or "branch:unknown")
    target_type = str(row.get("targetType") or "branch")

    emergence = _clamp01(float(row.get("emergenceScore", 0.45)))
    readiness = _clamp01(float(row.get("branchReadiness", 0.45)))
    persistence = _clamp01(float(row.get("persistenceScore", 0.45)))
    decay_risk = _clamp01(float(row.get("decayRisk", 0.4)))

    taf_row = taf_rows.get(target_id, {})
    functional_score = _clamp01(float(taf_row.get("functionalScore", 0.5)))
    overreach_score = _clamp01(float(taf_row.get("overreachScore", 0.4)))

    tele_row = telemetry_rows.get(target_id, {})
    field_status = str(tele_row.get("fieldStatus") or "bounded-field")
    field_risk = _clamp01(float(tele_row.get("riskScore", 0.45)))

    coherence = _clamp01(0.24 * emergence + 0.24 * readiness + 0.20 * persistence + 0.20 * functional_score + 0.12 * (1.0 - decay_risk))
    risk = _clamp01(0.22 * decay_risk + 0.22 * overreach_score + 0.20 * field_risk + 0.18 * (1.0 - readiness) + 0.18 * system_risk)

    if overreach_score >= 0.82 or field_status == "require-human-review":
        status = "branch-require-human-review"
        rule = "overreach-or-upstream-human-review-gate"
    elif readiness <= 0.34 or functional_score <= 0.36:
        status = "branch-verify-first"
        rule = "verify-first-under-low-branch-readiness"
    elif decay_risk >= 0.66 or persistence <= 0.34:
        status = "branch-decay"
        rule = "branch-decay-detection"
    elif emergence >= 0.64 and readiness >= 0.62 and risk <= 0.42:
        status = "branch-stable-candidate"
        rule = "stable-candidate-under-bounded-risk"
    elif emergence >= 0.52 and readiness >= 0.46:
        status = "branch-provisional"
        rule = "provisional-branch-emergence"
    else:
        status = "branch-watch"
        rule = "watch-early-branch-signals"

    lifecycle_context = (
        f"emergenceScore={emergence:.3f}, branchReadiness={readiness:.3f}, persistenceScore={persistence:.3f}, "
        f"decayRisk={decay_risk:.3f}, fieldStatus={field_status}"
    )
    maturity_context = (
        f"functionalScore={functional_score:.3f}, overreachScore={overreach_score:.3f}, fieldRisk={field_risk:.3f}, systemRisk={system_risk:.3f}; "
        "branch lifecycle guidance is bounded and non-autonomous."
    )
    explanation = (
        f"Branch lifecycle recommendation is bounded process guidance only. targetId={target_id}, branchStatus={status}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return BranchLifecycleDecision(
        target_id=target_id,
        target_type=target_type,
        branch_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        lifecycle_context=lifecycle_context,
        maturity_context=maturity_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(decision: BranchLifecycleDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "branchStatus": decision.branch_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "lifecycleContext": decision.lifecycle_context,
        "maturityContext": decision.maturity_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    branch_report = _load_json(BRANCH_EMERGENCE_REPORT_PATH)
    taf_scorecard = _load_json(ACTION_FUNCTIONAL_SCORECARD_PATH)
    telemetry = _load_json(TELEMETRY_FIELD_AUDIT_PATH)
    collaborative = _load_json(COLLABORATIVE_REVIEW_AUDIT_PATH)
    causal = _load_json(CAUSAL_AUDIT_PATH)

    telemetry_risk = _safe_mean([float(r.get("riskScore")) for r in _rows(telemetry) if isinstance(r.get("riskScore"), (int, float))], 0.45)
    collaborative_risk = _safe_mean([float(r.get("riskScore")) for r in _rows(collaborative) if isinstance(r.get("riskScore"), (int, float))], 0.45)
    causal_risk = _safe_mean([float(r.get("riskScore")) for r in _rows(causal) if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.36 * telemetry_risk + 0.34 * collaborative_risk + 0.30 * causal_risk)

    taf_rows = {str(r.get("targetId")): r for r in _rows(taf_scorecard) if isinstance(r.get("targetId"), str)}
    telemetry_rows = {str(r.get("targetId")): r for r in _rows(telemetry) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            taf_rows=taf_rows,
            telemetry_rows=telemetry_rows,
            system_risk=system_risk,
        )
        for row in _rows(branch_report)
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    created_at = _resolve_created_at(branch_report, taf_scorecard, telemetry)
    phaselock = (
        "telemetry + taf + branch emergence -> branch lifecycle audit -> bounded recommendation overlay -> "
        "human/community branch supervision"
    )
    caution = "Branch lifecycle recommendations are bounded guidance only and do not autonomously authorize operations."

    metadata = {
        "systemRisk": round(system_risk, 6),
        "inputs": [
            "bridge/branch_emergence_report.json",
            "bridge/action_functional_scorecard.json",
            "bridge/telemetry_field_audit.json",
            "bridge/collaborative_review_audit.json",
            "bridge/causal_audit.json",
        ],
    }

    audit_payload = {
        "schema": "branch_lifecycle_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    recommendations_payload = {
        "schema": "branch_lifecycle_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia branch-lifecycle state audit")
    parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs()
    BRANCH_LIFECYCLE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    BRANCH_LIFECYCLE_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"Wrote {BRANCH_LIFECYCLE_AUDIT_OUT}")
    print(f"Wrote {BRANCH_LIFECYCLE_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
