from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

REVIEWER_BEHAVIOR_HISTORY_PATH = BRIDGE_DIR / "reviewer_behavior_history.json"
GOVERNANCE_AUDIT_PATH = BRIDGE_DIR / "governance_audit.json"

REVIEWER_BEHAVIOR_AUDIT_OUT = BRIDGE_DIR / "reviewer_behavior_audit.json"
REVIEWER_BEHAVIOR_AUDIT_SCHEMA = SCHEMA_DIR / "reviewer_behavior_audit_v1.schema.json"


@dataclass(slots=True)
class BehaviorDecision:
    reviewer_id: str
    continued_eligibility_status: str
    behavior_trend: str
    override_risk: float
    coherence_alignment: float
    human_review_flag: bool
    explanation: str


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


def _dict_by_key(items: Any, key: str) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    if not isinstance(items, list):
        return out
    for row in items:
        if not isinstance(row, dict):
            continue
        val = row.get(key)
        if isinstance(val, str):
            out[val] = row
    return out


def evaluate_reviewer(behavior_row: dict[str, Any], governance_row: dict[str, Any]) -> BehaviorDecision:
    reviewer_id = str(behavior_row.get("reviewerId") or governance_row.get("reviewerId") or "reviewer:unknown")
    behavior_trend = str(behavior_row.get("behaviorTrend") or "stable")
    override_risk = _clamp01(float(behavior_row.get("overrideRisk", 0.0)))
    coherence_alignment = _clamp01(float(behavior_row.get("coherenceAlignment", governance_row.get("coherenceScore", 0.5))))
    governance_status = str(governance_row.get("governanceStatus") or "watch")

    human_review_flag = False
    if governance_status in {"recommend-human-review", "ineligible"}:
        human_review_flag = True
    if override_risk >= 0.55 or behavior_trend in {"degrading", "volatile"}:
        human_review_flag = True

    if governance_status == "ineligible" or override_risk >= 0.80:
        status = "suspend-pending-review"
        explanation = "Reviewer is suspended pending human/community reassessment due to critical governance or override risk signals."
    elif human_review_flag:
        status = "re-review"
        explanation = "Reviewer remains auditable and is flagged for renewed human/community review under anti-capture safeguards."
    elif coherence_alignment >= 0.65 and override_risk <= 0.30 and behavior_trend in {"stable", "improving"}:
        status = "continue"
        explanation = "Reviewer remains eligible for continued service under bounded and reversible governance oversight."
    else:
        status = "watch"
        explanation = "Reviewer remains on watch for ongoing behavior audit and reversible governance monitoring."

    return BehaviorDecision(
        reviewer_id=reviewer_id,
        continued_eligibility_status=status,
        behavior_trend=behavior_trend,
        override_risk=round(override_risk, 6),
        coherence_alignment=round(coherence_alignment, 6),
        human_review_flag=human_review_flag,
        explanation=(
            f"{explanation} reviewerId={reviewer_id}, trend={behavior_trend}, "
            f"overrideRisk={override_risk:.3f}, coherenceAlignment={coherence_alignment:.3f}."
        ),
    )


def build_output() -> dict[str, Any]:
    behavior_history = _load_json(REVIEWER_BEHAVIOR_HISTORY_PATH)
    governance_audit = _load_json(GOVERNANCE_AUDIT_PATH)

    behavior_rows = behavior_history.get("reviewers") if isinstance(behavior_history.get("reviewers"), list) else []
    governance_rows = governance_audit.get("audits") if isinstance(governance_audit.get("audits"), list) else []

    behavior_by_id = _dict_by_key(behavior_rows, "reviewerId")
    governance_by_id = _dict_by_key(governance_rows, "reviewerId")

    reviewer_ids = sorted(set(behavior_by_id) | set(governance_by_id))
    decisions = [
        evaluate_reviewer(behavior_by_id.get(reviewer_id, {}), governance_by_id.get(reviewer_id, {}))
        for reviewer_id in reviewer_ids
    ]

    payload = {
        "schema": "reviewer_behavior_audit_v1",
        "created_at": _resolve_created_at(behavior_history, governance_audit),
        "phaselock": "ongoing reviewer behavior monitoring -> Sophia reviewer behavior audit -> Publisher reviewer monitor overlays",
        "caution": "Reviewer behavior audits are advisory, auditable, and reversible; they do not enact automatic permanent exclusion.",
        "reviewers": [
            {
                "reviewerId": item.reviewer_id,
                "continuedEligibilityStatus": item.continued_eligibility_status,
                "behaviorTrend": item.behavior_trend,
                "overrideRisk": item.override_risk,
                "coherenceAlignment": item.coherence_alignment,
                "humanReviewFlag": item.human_review_flag,
                "explanation": item.explanation,
            }
            for item in decisions
        ],
    }

    Draft202012Validator(_load_json(REVIEWER_BEHAVIOR_AUDIT_SCHEMA)).validate(payload)
    return payload


def main() -> int:
    payload = build_output()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    REVIEWER_BEHAVIOR_AUDIT_OUT.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {REVIEWER_BEHAVIOR_AUDIT_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
