from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

SCENARIO_CATALOG_PATH = BRIDGE_DIR / "scenario_catalog.json"
SCENARIO_STATE_MAP_PATH = BRIDGE_DIR / "scenario_state_map.json"
SCENARIO_OUTCOME_PROJECTION_PATH = BRIDGE_DIR / "scenario_outcome_projection.json"
SCENARIO_STRESS_SUMMARY_PATH = BRIDGE_DIR / "scenario_stress_summary.json"
CONSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "constitutional_audit.json"
RESILIENCE_AUDIT_PATH = BRIDGE_DIR / "resilience_audit.json"
RECOVERY_AUDIT_PATH = BRIDGE_DIR / "recovery_audit.json"
WITNESS_AUDIT_PATH = BRIDGE_DIR / "witness_audit.json"
PRECEDENT_AUDIT_PATH = BRIDGE_DIR / "precedent_audit.json"

SCENARIO_AUDIT_OUT = BRIDGE_DIR / "scenario_audit.json"
SCENARIO_RECOMMENDATIONS_OUT = BRIDGE_DIR / "scenario_recommendations.json"

SCENARIO_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "scenario_audit_v1.schema.json"
SCENARIO_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "scenario_recommendations_v1.schema.json"


@dataclass(slots=True)
class ScenarioDecision:
    scenario_id: str
    scenario_status: str
    preparedness_recommendation: str
    coherence_score: float
    risk_score: float
    capture_risk: float
    continuity_risk: float
    explanation: str
    governing_rule: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _clamp01(v: float) -> float:
    return max(0.0, min(1.0, float(v)))


def _safe_mean(vals: list[float], default: float = 0.0) -> float:
    if not vals:
        return default
    return sum(vals) / len(vals)


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for d in docs:
        ts = d.get("created_at") if isinstance(d, dict) else None
        if isinstance(ts, str) and ts:
            return ts
    return "1970-01-01T00:00:00Z"


def _status_to_action(rec: str) -> str:
    return {
        "continue": "watch",
        "harden-watch": "watch",
        "rehearse-recovery": "docket",
        "freeze-pathway": "watch",
        "prioritize-redundancy": "docket",
        "require-broader-human-review": "docket",
    }[rec]


def _system_risk_context(
    constitutional: dict[str, Any],
    resilience: dict[str, Any],
    recovery: dict[str, Any],
    witness: dict[str, Any],
    precedent: dict[str, Any],
) -> tuple[float, float, float, float]:
    constitutional_rows = constitutional.get("evaluations") if isinstance(constitutional.get("evaluations"), list) else []
    resilience_rows = resilience.get("records") if isinstance(resilience.get("records"), list) else []
    recovery_rows = recovery.get("records") if isinstance(recovery.get("records"), list) else []
    witness_rows = witness.get("records") if isinstance(witness.get("records"), list) else []
    precedent_rows = precedent.get("records") if isinstance(precedent.get("records"), list) else []

    constitutional_risk = _safe_mean(
        [float(r.get("governanceRisk")) for r in constitutional_rows if isinstance(r, dict) and isinstance(r.get("governanceRisk"), (int, float))],
        0.3,
    )
    resilience_risk = _safe_mean(
        [float(r.get("riskScore")) for r in resilience_rows if isinstance(r, dict) and isinstance(r.get("riskScore"), (int, float))],
        0.35,
    )
    recovery_tamper = _safe_mean(
        [float(r.get("tamperRisk")) for r in recovery_rows if isinstance(r, dict) and isinstance(r.get("tamperRisk"), (int, float))],
        0.3,
    )
    witness_risk = _safe_mean(
        [float(r.get("riskScore")) for r in witness_rows if isinstance(r, dict) and isinstance(r.get("riskScore"), (int, float))],
        0.35,
    )
    precedent_divergence = _safe_mean(
        [float(r.get("divergenceLevel")) for r in precedent_rows if isinstance(r, dict) and isinstance(r.get("divergenceLevel"), (int, float))],
        0.3,
    )
    return (
        _clamp01(constitutional_risk),
        _clamp01(resilience_risk),
        _clamp01(max(recovery_tamper, witness_risk)),
        _clamp01(precedent_divergence),
    )


def evaluate_scenario(
    scenario_row: dict[str, Any],
    *,
    catalog_by_id: dict[str, dict[str, Any]],
    projection_by_id: dict[str, dict[str, Any]],
    stress_summary: dict[str, Any],
    constitutional_risk: float,
    resilience_risk: float,
    integrity_risk: float,
    precedent_divergence: float,
) -> ScenarioDecision:
    scenario_id = str(scenario_row.get("scenarioId") or "scenario:unknown")
    catalog = catalog_by_id.get(scenario_id, {})
    projection = projection_by_id.get(scenario_id, {})

    baseline = _clamp01(float(scenario_row.get("baselineStability", stress_summary.get("meanBaselineStability", 0.5))))
    adversarial_intensity = _clamp01(float(scenario_row.get("adversarialIntensity", 0.3)))
    projected_continuity = _clamp01(float(projection.get("projectedContinuityScore", 0.5)))
    projected_capture = _clamp01(float(projection.get("projectedCaptureRisk", 0.3)))
    ambiguity = _clamp01(float(projection.get("ambiguityScore", 0.2)))

    recoverability = _clamp01(float(catalog.get("recoverabilityScore", 0.5)))
    redundancy = _clamp01(float(catalog.get("redundancyScore", 0.5)))

    coherence = _clamp01(
        0.30 * baseline
        + 0.25 * projected_continuity
        + 0.20 * recoverability
        + 0.15 * redundancy
        + 0.10 * (1.0 - ambiguity)
    )

    capture_risk = _clamp01(
        0.35 * projected_capture
        + 0.25 * adversarial_intensity
        + 0.20 * constitutional_risk
        + 0.20 * resilience_risk
    )
    continuity_risk = _clamp01(
        0.35 * (1.0 - projected_continuity)
        + 0.25 * (1.0 - recoverability)
        + 0.20 * integrity_risk
        + 0.20 * ambiguity
    )
    risk = _clamp01(0.40 * capture_risk + 0.35 * continuity_risk + 0.15 * precedent_divergence + 0.10 * adversarial_intensity)

    if risk >= 0.85 or capture_risk >= 0.80 or ambiguity >= 0.80:
        status = "freeze-recommended"
        recommendation = "require-broader-human-review"
        rule = "high-ambiguity-freeze-before-escalation"
        explanation = "Scenario indicates high ambiguity/capture pressure; freeze-before-escalation and route to broader preparedness review."
    elif capture_risk >= 0.68:
        status = "capture-risk"
        recommendation = "freeze-pathway"
        rule = "capture-rehearsal-freeze-pathway"
        explanation = "Scenario projects governance capture pressure; freeze vulnerable pathways and avoid blind escalation."
    elif continuity_risk >= 0.62:
        status = "degraded"
        recommendation = "rehearse-recovery"
        rule = "rehearse-recovery-before-crisis"
        explanation = "Scenario projects continuity/recovery collision; rehearse recovery workflows before crisis conditions."
    elif risk >= 0.48:
        status = "strained"
        recommendation = "harden-watch"
        rule = "strained-harden-watch"
        explanation = "Scenario is strained and should remain in stress-test watch with strengthened controls."
    else:
        status = "stable"
        recommendation = "continue"
        rule = "stable-hypothetical-preparedness"
        explanation = "Scenario remains stable under hypothetical stress modeling and bounded preparedness assumptions."

    if recommendation in {"continue", "harden-watch"} and redundancy < 0.55:
        recommendation = "prioritize-redundancy"
        rule = "redundancy-over-concentration"
        explanation = "Preparedness favors redundancy over concentration to reduce single-point failure risk in hypothetical conditions."

    return ScenarioDecision(
        scenario_id=scenario_id,
        scenario_status=status,
        preparedness_recommendation=recommendation,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        capture_risk=round(capture_risk, 6),
        continuity_risk=round(continuity_risk, 6),
        explanation=(
            f"{explanation} scenarioId={scenario_id}, coherence={coherence:.3f}, risk={risk:.3f}, captureRisk={capture_risk:.3f}, continuityRisk={continuity_risk:.3f}."
        ),
        governing_rule=rule,
        target_publisher_action=_status_to_action(recommendation),
    )


def _to_payload(item: ScenarioDecision) -> dict[str, Any]:
    return {
        "scenarioId": item.scenario_id,
        "scenarioStatus": item.scenario_status,
        "preparednessRecommendation": item.preparedness_recommendation,
        "coherenceScore": item.coherence_score,
        "riskScore": item.risk_score,
        "captureRisk": item.capture_risk,
        "continuityRisk": item.continuity_risk,
        "explanation": item.explanation,
        "governingRule": item.governing_rule,
        "targetPublisherAction": item.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    scenario_catalog = _load_json(SCENARIO_CATALOG_PATH)
    scenario_state_map = _load_json(SCENARIO_STATE_MAP_PATH)
    scenario_outcome_projection = _load_json(SCENARIO_OUTCOME_PROJECTION_PATH)
    scenario_stress_summary = _load_json(SCENARIO_STRESS_SUMMARY_PATH)
    constitutional_audit = _load_json(CONSTITUTIONAL_AUDIT_PATH)
    resilience_audit = _load_json(RESILIENCE_AUDIT_PATH)
    recovery_audit = _load_json(RECOVERY_AUDIT_PATH)
    witness_audit = _load_json(WITNESS_AUDIT_PATH)
    precedent_audit = _load_json(PRECEDENT_AUDIT_PATH)

    constitutional_risk, resilience_risk, integrity_risk, precedent_divergence = _system_risk_context(
        constitutional_audit,
        resilience_audit,
        recovery_audit,
        witness_audit,
        precedent_audit,
    )

    catalog_by_id = {
        str(r.get("scenarioId")): r
        for r in (scenario_catalog.get("scenarios") if isinstance(scenario_catalog.get("scenarios"), list) else [])
        if isinstance(r, dict) and isinstance(r.get("scenarioId"), str)
    }
    projection_by_id = {
        str(r.get("scenarioId")): r
        for r in (scenario_outcome_projection.get("scenarios") if isinstance(scenario_outcome_projection.get("scenarios"), list) else [])
        if isinstance(r, dict) and isinstance(r.get("scenarioId"), str)
    }

    scenario_rows = scenario_state_map.get("scenarios") if isinstance(scenario_state_map.get("scenarios"), list) else []
    decisions = [
        evaluate_scenario(
            row,
            catalog_by_id=catalog_by_id,
            projection_by_id=projection_by_id,
            stress_summary=scenario_stress_summary,
            constitutional_risk=constitutional_risk,
            resilience_risk=resilience_risk,
            integrity_risk=integrity_risk,
            precedent_divergence=precedent_divergence,
        )
        for row in scenario_rows
        if isinstance(row, dict)
    ]
    decisions = sorted(decisions, key=lambda item: item.scenario_id)

    created_at = _resolve_created_at(scenario_stress_summary, scenario_state_map, scenario_catalog)
    phaselock = (
        "current system state -> CoherenceLattice scenario formalization -> Sophia scenario audit -> "
        "Publisher scenario and stress-test overlays -> human/community preparedness review"
    )

    scenario_audit_payload = {
        "schema": "scenario_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": "Scenario recommendations are hypothetical preparedness outputs only and do not authorize live emergency power.",
        "records": [_to_payload(item) for item in decisions],
    }

    scenario_recommendations_payload = {
        "schema": "scenario_recommendations_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice scenario formalization -> Sophia scenario audit -> Publisher stress-test docket",
        "caution": "Preparedness findings are advisory and non-executing; no automatic emergency activation or live execution authority is implied.",
        "recommendations": [_to_payload(item) for item in decisions],
    }

    Draft202012Validator(_load_json(SCENARIO_AUDIT_SCHEMA_PATH)).validate(scenario_audit_payload)
    Draft202012Validator(_load_json(SCENARIO_RECOMMENDATIONS_SCHEMA_PATH)).validate(scenario_recommendations_payload)
    return scenario_audit_payload, scenario_recommendations_payload


def main() -> int:
    scenario_audit_payload, scenario_recommendations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    SCENARIO_AUDIT_OUT.write_text(json.dumps(scenario_audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    SCENARIO_RECOMMENDATIONS_OUT.write_text(
        json.dumps(scenario_recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {SCENARIO_AUDIT_OUT}")
    print(f"Wrote {SCENARIO_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
