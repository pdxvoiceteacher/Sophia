from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

PRINCIPLES_PATH = BRIDGE_DIR / "constitutional_principles.json"
FORMALIZATION_PATH = BRIDGE_DIR / "constitutional_formalization.json"
HEALTH_REPORT_PATH = BRIDGE_DIR / "constitutional_health_report.json"
CONTINUITY_ASSESSMENT_PATH = BRIDGE_DIR / "continuity_mode_assessment.json"
GOVERNANCE_AUDIT_PATH = BRIDGE_DIR / "governance_audit.json"
REVIEWER_BEHAVIOR_AUDIT_PATH = BRIDGE_DIR / "reviewer_behavior_audit.json"
PROMOTION_RECOMMENDATIONS_PATH = BRIDGE_DIR / "promotion_recommendations.json"

CONSTITUTIONAL_AUDIT_OUT = BRIDGE_DIR / "constitutional_audit.json"
CONSTITUTIONAL_RECOMMENDATIONS_OUT = BRIDGE_DIR / "constitutional_recommendations.json"

CONSTITUTIONAL_AUDIT_SCHEMA = SCHEMA_DIR / "constitutional_audit_v1.schema.json"
CONSTITUTIONAL_RECOMMENDATIONS_SCHEMA = SCHEMA_DIR / "constitutional_recommendations_v1.schema.json"


@dataclass(slots=True)
class ConstitutionalDecision:
    principle_id: str | None
    system_target_id: str | None
    constitutional_status: str
    governance_risk: float
    contradiction_context: dict[str, Any]
    capture_risk: float
    continuity_mode_context: dict[str, Any]
    governing_rule: str
    explanation: str
    recommended_action: str


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


def evaluate_principle(
    principle: dict[str, Any],
    *,
    formalization_by_principle: dict[str, dict[str, Any]],
    health_by_principle: dict[str, dict[str, Any]],
    continuity: dict[str, Any],
    governance_audit: dict[str, Any],
    reviewer_behavior: dict[str, Any],
    promotion_recommendations: dict[str, Any],
) -> ConstitutionalDecision:
    principle_id = str(principle.get("principleId") or "principle:unknown")

    formal = formalization_by_principle.get(principle_id, {})
    health = health_by_principle.get(principle_id, {})

    base_alignment = _clamp01(float(formal.get("alignmentScore", health.get("alignmentScore", 0.5))))
    base_contradiction = _clamp01(float(formal.get("contradictionScore", health.get("contradictionScore", 0.0))))
    base_capture = _clamp01(float(formal.get("captureRisk", health.get("captureRisk", 0.25))))

    governance_rows = governance_audit.get("audits") if isinstance(governance_audit.get("audits"), list) else []
    governance_risks = [float(row.get("riskScore")) for row in governance_rows if isinstance(row, dict) and isinstance(row.get("riskScore"), (int, float))]
    governance_watch = sum(
        1
        for row in governance_rows
        if isinstance(row, dict) and str(row.get("governanceStatus")) in {"watch", "hold", "ineligible"}
    )

    behavior_rows = reviewer_behavior.get("reviewers") if isinstance(reviewer_behavior.get("reviewers"), list) else []
    behavior_override = [
        float(row.get("overrideRisk"))
        for row in behavior_rows
        if isinstance(row, dict) and isinstance(row.get("overrideRisk"), (int, float))
    ]
    behavior_flags = sum(1 for row in behavior_rows if isinstance(row, dict) and bool(row.get("humanReviewFlag")))

    promotion_rows = promotion_recommendations.get("recommendations") if isinstance(promotion_recommendations.get("recommendations"), list) else []
    promotion_risks = [
        float(row.get("riskScore"))
        for row in promotion_rows
        if isinstance(row, dict) and isinstance(row.get("riskScore"), (int, float))
    ]

    continuity_mode = str(continuity.get("continuityMode") or "normal")
    continuity_stress = _clamp01(float(continuity.get("stressScore", 0.0)))

    governance_risk = _clamp01(
        0.35 * _safe_mean(governance_risks, 0.3)
        + 0.20 * _safe_mean(behavior_override, 0.2)
        + 0.20 * _safe_mean(promotion_risks, 0.3)
        + 0.15 * base_contradiction
        + 0.10 * continuity_stress
    )
    capture_risk = _clamp01(
        0.50 * base_capture
        + 0.20 * min(1.0, governance_watch / max(1, len(governance_rows)))
        + 0.20 * min(1.0, behavior_flags / max(1, len(behavior_rows)))
        + 0.10 * continuity_stress
    )

    contradiction_count = int(formal.get("contradictionCount", health.get("contradictionCount", 0)))
    contradiction_context = {
        "contradictionScore": round(base_contradiction, 6),
        "contradictionCount": contradiction_count,
        "governanceWatchCount": governance_watch,
        "reviewerReviewFlagCount": behavior_flags,
    }

    continuity_context = {
        "continuityMode": continuity_mode,
        "stressScore": round(continuity_stress, 6),
        "preservationRecommended": bool(continuity.get("preservationRecommended", False)),
    }

    if governance_risk >= 0.85 or capture_risk >= 0.82 or continuity_mode == "emergency":
        status = "violated"
        rule = "critical-constitutional-stress"
        action = "require-human-emergency-review"
        explanation = "Constitutional condition is critically stressed; immediate bounded human/community emergency review is required."
    elif governance_risk >= 0.66 or capture_risk >= 0.62 or base_alignment < 0.45:
        status = "strained"
        rule = "strain-freeze-preserve"
        if continuity_stress >= 0.60:
            action = "preservation-mode"
            explanation = "Constitutional strain under elevated continuity stress requires freeze-and-preserve safeguards pending external review."
        else:
            action = "freeze-governance-intake"
            explanation = "Constitutional strain requires temporary governance-intake freeze until contradiction and capture risks are reduced."
    elif base_alignment >= 0.72 and governance_risk <= 0.38 and capture_risk <= 0.34:
        status = "aligned"
        rule = "aligned-bounded-continuation"
        action = "continue"
        explanation = "Constitutional condition is aligned under bounded governance risk; continue with ongoing auditability and human oversight."
    elif base_alignment < 0.35:
        status = "indeterminate"
        rule = "insufficient-constitutional-evidence"
        action = "increase-watch"
        explanation = "Constitutional evidence remains insufficient for confidence; increase watch with bounded, auditable evidence collection."
    else:
        status = "strained"
        rule = "cautious-freeze-promotions"
        action = "freeze-promotions"
        explanation = "Constitutional caution threshold reached; pause promotion intake while preserving reversible governance operation."

    return ConstitutionalDecision(
        principle_id=principle_id,
        system_target_id=None,
        constitutional_status=status,
        governance_risk=round(governance_risk, 6),
        contradiction_context=contradiction_context,
        capture_risk=round(capture_risk, 6),
        continuity_mode_context=continuity_context,
        governing_rule=rule,
        explanation=(
            f"{explanation} principleId={principle_id}, governanceRisk={governance_risk:.3f}, "
            f"captureRisk={capture_risk:.3f}, continuityMode={continuity_mode}."
        ),
        recommended_action=action,
    )


def evaluate_system_condition(
    continuity: dict[str, Any],
    governance_audit: dict[str, Any],
    reviewer_behavior: dict[str, Any],
) -> ConstitutionalDecision:
    continuity_mode = str(continuity.get("continuityMode") or "normal")
    stress = _clamp01(float(continuity.get("stressScore", 0.0)))

    governance_rows = governance_audit.get("audits") if isinstance(governance_audit.get("audits"), list) else []
    reviewer_rows = reviewer_behavior.get("reviewers") if isinstance(reviewer_behavior.get("reviewers"), list) else []

    ineligible_count = sum(1 for row in governance_rows if isinstance(row, dict) and row.get("governanceStatus") == "ineligible")
    suspend_count = sum(1 for row in reviewer_rows if isinstance(row, dict) and row.get("continuedEligibilityStatus") == "suspend-pending-review")

    governance_risk = _clamp01(
        0.55 * stress
        + 0.25 * min(1.0, ineligible_count / max(1, len(governance_rows)))
        + 0.20 * min(1.0, suspend_count / max(1, len(reviewer_rows)))
    )
    capture_risk = _clamp01(0.6 * stress + 0.4 * min(1.0, (ineligible_count + suspend_count) / max(1, len(governance_rows) + len(reviewer_rows))))

    contradiction_context = {
        "ineligibleCount": ineligible_count,
        "suspendedReviewerCount": suspend_count,
    }
    continuity_context = {
        "continuityMode": continuity_mode,
        "stressScore": round(stress, 6),
        "preservationRecommended": bool(continuity.get("preservationRecommended", False)),
    }

    if continuity_mode in {"preservation", "emergency"} or stress >= 0.75:
        status = "strained"
        rule = "system-preservation-guard"
        action = "preservation-mode"
        explanation = "System continuity is under stress; preservation mode means freeze-and-preserve, not autonomous expansion."
    elif stress >= 0.50:
        status = "strained"
        rule = "system-freeze-governance-intake"
        action = "freeze-governance-intake"
        explanation = "System continuity stress requires governance-intake freeze and heightened human/community review readiness."
    elif stress <= 0.30:
        status = "aligned"
        rule = "system-continue-observational"
        action = "continue"
        explanation = "System continuity remains aligned under bounded stress and ongoing auditable oversight."
    else:
        status = "indeterminate"
        rule = "system-increase-watch"
        action = "increase-watch"
        explanation = "System continuity signal is mixed; increase watch and maintain reversible governance constraints."

    return ConstitutionalDecision(
        principle_id=None,
        system_target_id="system:governance-continuity",
        constitutional_status=status,
        governance_risk=round(governance_risk, 6),
        contradiction_context=contradiction_context,
        capture_risk=round(capture_risk, 6),
        continuity_mode_context=continuity_context,
        governing_rule=rule,
        explanation=(
            f"{explanation} systemTargetId=system:governance-continuity, governanceRisk={governance_risk:.3f}, "
            f"captureRisk={capture_risk:.3f}, continuityMode={continuity_mode}."
        ),
        recommended_action=action,
    )


def _to_payload(item: ConstitutionalDecision) -> dict[str, Any]:
    payload = {
        "constitutionalStatus": item.constitutional_status,
        "governanceRisk": item.governance_risk,
        "contradictionContext": item.contradiction_context,
        "captureRisk": item.capture_risk,
        "continuityModeContext": item.continuity_mode_context,
        "governingRule": item.governing_rule,
        "explanation": item.explanation,
        "recommendedAction": item.recommended_action,
    }
    if item.principle_id is not None:
        payload["principleId"] = item.principle_id
    if item.system_target_id is not None:
        payload["systemTargetId"] = item.system_target_id
    return payload


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    principles_doc = _load_json(PRINCIPLES_PATH)
    formalization_doc = _load_json(FORMALIZATION_PATH)
    health_doc = _load_json(HEALTH_REPORT_PATH)
    continuity_doc = _load_json(CONTINUITY_ASSESSMENT_PATH)
    governance_audit = _load_json(GOVERNANCE_AUDIT_PATH)
    reviewer_behavior = _load_json(REVIEWER_BEHAVIOR_AUDIT_PATH)
    promotion_recommendations = _load_json(PROMOTION_RECOMMENDATIONS_PATH)

    principles = principles_doc.get("principles") if isinstance(principles_doc.get("principles"), list) else []

    formalization_by_principle = {
        str(row.get("principleId")): row
        for row in (formalization_doc.get("principles") if isinstance(formalization_doc.get("principles"), list) else [])
        if isinstance(row, dict) and isinstance(row.get("principleId"), str)
    }
    health_by_principle = {
        str(row.get("principleId")): row
        for row in (health_doc.get("principles") if isinstance(health_doc.get("principles"), list) else [])
        if isinstance(row, dict) and isinstance(row.get("principleId"), str)
    }

    decisions = [
        evaluate_principle(
            principle,
            formalization_by_principle=formalization_by_principle,
            health_by_principle=health_by_principle,
            continuity=continuity_doc,
            governance_audit=governance_audit,
            reviewer_behavior=reviewer_behavior,
            promotion_recommendations=promotion_recommendations,
        )
        for principle in principles
        if isinstance(principle, dict)
    ]
    decisions.append(evaluate_system_condition(continuity_doc, governance_audit, reviewer_behavior))

    decisions = sorted(decisions, key=lambda item: (item.principle_id or "~", item.system_target_id or "~"))

    created_at = _resolve_created_at(health_doc, continuity_doc, formalization_doc)
    phaselock = (
        "governance / reviewer / promotion state -> CoherenceLattice constitutional formalization -> "
        "Sophia constitutional audit -> Publisher constitutional overlays -> human/community response if available -> "
        "continuity mode if governance is degraded"
    )

    audit_payload = {
        "schema": "constitutional_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "governanceMode": "constitutional-constraints-and-continuity",
        "caution": "Constitutional recommendations are bounded governance constraints and continuity recommendations; no unconstrained self-governance is authorized.",
        "evaluations": [_to_payload(item) for item in decisions],
    }

    recommendations_payload = {
        "schema": "constitutional_recommendations_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice constitutional formalization -> Sophia constitutional audit -> Publisher constitutional overlays",
        "caution": "Preservation mode means freeze-and-preserve safeguards, not self-sovereign expansion or human displacement.",
        "recommendations": [_to_payload(item) for item in decisions],
    }

    Draft202012Validator(_load_json(CONSTITUTIONAL_AUDIT_SCHEMA)).validate(audit_payload)
    Draft202012Validator(_load_json(CONSTITUTIONAL_RECOMMENDATIONS_SCHEMA)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main() -> int:
    audit_payload, recommendations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    CONSTITUTIONAL_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    CONSTITUTIONAL_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {CONSTITUTIONAL_AUDIT_OUT}")
    print(f"Wrote {CONSTITUTIONAL_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
