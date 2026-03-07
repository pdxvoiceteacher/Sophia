from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

INSTITUTIONAL_STATE_MAP_PATH = BRIDGE_DIR / "institutional_state_map.json"
INSTITUTIONAL_STATE_SUMMARY_PATH = BRIDGE_DIR / "institutional_state_summary.json"
INSTITUTIONAL_CONFLICT_REPORT_PATH = BRIDGE_DIR / "institutional_conflict_report.json"
INSTITUTIONAL_HEALTH_PROJECTION_PATH = BRIDGE_DIR / "institutional_health_projection.json"

INSTITUTIONAL_AUDIT_OUT = BRIDGE_DIR / "institutional_audit.json"
INSTITUTIONAL_RECOMMENDATIONS_OUT = BRIDGE_DIR / "institutional_recommendations.json"

INSTITUTIONAL_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "institutional_audit_v1.schema.json"
INSTITUTIONAL_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "institutional_recommendations_v1.schema.json"


@dataclass(slots=True)
class InstitutionalDecision:
    institution_id: str
    institutional_status: str
    synthesis_score: float
    risk_score: float
    conflict_score: float
    health_score: float
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
        "stable": "docket",
        "monitor": "watch",
        "caution": "watch",
        "freeze-pathways": "suppress",
        "require-human-review": "docket",
        "preservation-mode": "suppress",
    }[status]


def evaluate_institution(
    row: dict[str, Any],
    *,
    state_summary: dict[str, Any],
    conflict_rows: dict[str, dict[str, Any]],
    health_rows: dict[str, dict[str, Any]],
) -> InstitutionalDecision:
    institution_id = str(row.get("institutionId") or "institution:unknown")

    coherence = _clamp01(float(row.get("coherenceScore", state_summary.get("meanCoherenceScore", 0.5))))
    pathway_integrity = _clamp01(float(row.get("pathwayIntegrity", state_summary.get("meanPathwayIntegrity", 0.5))))

    conflict_row = conflict_rows.get(institution_id, {})
    health_row = health_rows.get(institution_id, {})

    conflict_score = _clamp01(float(conflict_row.get("conflictScore", state_summary.get("meanConflictScore", 0.4))))
    unresolved_conflicts = int(conflict_row.get("unresolvedConflicts", 0))
    health_score = _clamp01(float(health_row.get("healthScore", state_summary.get("meanHealthScore", 0.6))))
    decay_risk = _clamp01(float(health_row.get("decayRisk", state_summary.get("meanDecayRisk", 0.4))))

    synthesis = _clamp01(0.45 * coherence + 0.35 * pathway_integrity + 0.20 * health_score)
    risk = _clamp01(0.35 * conflict_score + 0.30 * decay_risk + 0.20 * (1.0 - pathway_integrity) + 0.15 * (1.0 - coherence))

    if health_score <= 0.28 or decay_risk >= 0.84:
        status = "preservation-mode"
        rule = "preserve-when-institutional-health-collapses"
        explanation = "Institutional health is in collapse-range; preserve evidence and continuity context while freezing fragile pathways."
    elif unresolved_conflicts >= 4 or (conflict_score >= 0.82 and pathway_integrity <= 0.40):
        status = "require-human-review"
        rule = "stacked-conflict-human-review-override"
        explanation = "Conflict accumulation is too high for automated pathway guidance and requires human/community adjudication."
    elif conflict_score >= 0.72 or risk >= 0.72:
        status = "freeze-pathways"
        rule = "freeze-under-high-institutional-risk"
        explanation = "Institutional risk is elevated; freeze high-impact pathways until review confirms safe re-entry conditions."
    elif synthesis >= 0.72 and risk <= 0.34 and unresolved_conflicts == 0:
        status = "stable"
        rule = "sustain-healthy-institutional-state"
        explanation = "Institutional synthesis is coherent and low-risk; continue bounded monitoring without pathway mutation."
    elif risk <= 0.55 and synthesis >= 0.48:
        status = "monitor"
        rule = "monitor-drift-before-escalation"
        explanation = "Institutional state is serviceable but requires drift monitoring to prevent latent governance degradation."
    else:
        status = "caution"
        rule = "caution-under-ambiguous-institutional-signals"
        explanation = "Institutional signals are mixed; maintain caution with bounded recommendations and explicit review checkpoints."

    return InstitutionalDecision(
        institution_id=institution_id,
        institutional_status=status,
        synthesis_score=round(synthesis, 6),
        risk_score=round(risk, 6),
        conflict_score=round(conflict_score, 6),
        health_score=round(health_score, 6),
        governing_rule=rule,
        explanation=(
            f"{explanation} institutionId={institution_id}, synthesis={synthesis:.3f}, "
            f"risk={risk:.3f}, conflict={conflict_score:.3f}, health={health_score:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(item: InstitutionalDecision) -> dict[str, Any]:
    return {
        "institutionId": item.institution_id,
        "institutionalStatus": item.institutional_status,
        "synthesisScore": item.synthesis_score,
        "riskScore": item.risk_score,
        "conflictScore": item.conflict_score,
        "healthScore": item.health_score,
        "governingRule": item.governing_rule,
        "explanation": item.explanation,
        "targetPublisherAction": item.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    state_map = _load_json(INSTITUTIONAL_STATE_MAP_PATH)
    state_summary = _load_json(INSTITUTIONAL_STATE_SUMMARY_PATH)
    conflict_report = _load_json(INSTITUTIONAL_CONFLICT_REPORT_PATH)
    health_projection = _load_json(INSTITUTIONAL_HEALTH_PROJECTION_PATH)

    conflict_rows = {
        str(r.get("institutionId")): r
        for r in (conflict_report.get("institutions") if isinstance(conflict_report.get("institutions"), list) else [])
        if isinstance(r, dict) and isinstance(r.get("institutionId"), str)
    }
    health_rows = {
        str(r.get("institutionId")): r
        for r in (health_projection.get("institutions") if isinstance(health_projection.get("institutions"), list) else [])
        if isinstance(r, dict) and isinstance(r.get("institutionId"), str)
    }

    institution_rows = state_map.get("institutions") if isinstance(state_map.get("institutions"), list) else []
    decisions = [
        evaluate_institution(
            row,
            state_summary=state_summary,
            conflict_rows=conflict_rows,
            health_rows=health_rows,
        )
        for row in institution_rows
        if isinstance(row, dict)
    ]
    decisions = sorted(decisions, key=lambda item: item.institution_id)

    created_at = _resolve_created_at(state_summary, state_map, conflict_report, health_projection)
    phaselock = (
        "CoherenceLattice institutional synthesis -> Sophia institutional audit -> "
        "Publisher institutional overlays (read-only over canonical truth)"
    )

    audit_payload = {
        "schema": "institutional_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": (
            "Institutional audit is bounded and advisory; it does not mutate canonical truth "
            "and does not authorize autonomous institutional pathway changes."
        ),
        "records": [_to_payload(item) for item in decisions],
    }

    recommendations_payload = {
        "schema": "institutional_recommendations_v1",
        "created_at": created_at,
        "phaselock": (
            "CoherenceLattice institutional synthesis -> Sophia bounded recommendations -> "
            "Publisher state surfacing without mutating canonical truth"
        ),
        "caution": (
            "Recommendations are bounded advisory outputs for human/community governance review; "
            "Publisher must surface institutional state without mutating canonical truth."
        ),
        "recommendations": [_to_payload(item) for item in decisions],
    }

    Draft202012Validator(_load_json(INSTITUTIONAL_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(INSTITUTIONAL_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main() -> int:
    audit_payload, recommendations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    INSTITUTIONAL_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    INSTITUTIONAL_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {INSTITUTIONAL_AUDIT_OUT}")
    print(f"Wrote {INSTITUTIONAL_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
