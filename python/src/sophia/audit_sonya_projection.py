from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

PROJECTION_PATH = BRIDGE_DIR / "sonya_lattice_projection.json"
PROJECTION_SUMMARY_PATH = BRIDGE_DIR / "sonya_projection_summary.json"
COHERENCE_ASSESSMENT_PATH = BRIDGE_DIR / "coherence_assessment.json"
COHERENCE_DRIFT_PATH = BRIDGE_DIR / "coherence_drift_map.json"
RECOMMENDATIONS_PATH = BRIDGE_DIR / "sophia_recommendations.json"
REGIME_PATH = BRIDGE_DIR / "publication_regime_map.json"

SONYA_AUDIT_OUT = BRIDGE_DIR / "sonya_audit.json"
SONYA_DECISIONS_OUT = BRIDGE_DIR / "sonya_admission_decisions.json"

AUDIT_SCHEMA_PATH = SCHEMA_DIR / "sonya_audit_v1.schema.json"
DECISIONS_SCHEMA_PATH = SCHEMA_DIR / "sonya_admission_decisions_v1.schema.json"


@dataclass(slots=True)
class AdmissionDecision:
    input_id: str
    audit_status: str
    coherence_score: float
    risk_score: float
    drift_context: dict[str, Any]
    governing_rule: str
    explanation: str
    target_publisher_action: str
    suggested_concept_targets: list[str]


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


def _drift_for_input(input_id: str, drift_map: dict[str, Any]) -> float:
    by_node = drift_map.get("driftByNode")
    if isinstance(by_node, dict):
        node_id = input_id.split(":")[-1]
        if isinstance(by_node.get(node_id), (int, float)):
            return _clamp01(by_node[node_id])
    return _clamp01(float(drift_map.get("globalDriftScore", 0.0)))


def _status_to_action(status: str) -> str:
    return {
        "admit": "store",
        "promote": "store",
        "observe": "annotate",
        "defer": "hold",
        "reject": "discard",
    }[status]


def evaluate_projection(
    projection: dict[str, Any],
    *,
    global_coherence: float,
    global_risk: float,
    global_drift: float,
    default_regime: str,
) -> AdmissionDecision:
    input_id = str(projection.get("inputId") or "unknown-input")
    projected = projection.get("projectedConceptIds")
    suggested_targets = [str(x) for x in projected] if isinstance(projected, list) else []

    confidence = _clamp01(float(projection.get("projectionConfidence", 0.0)))
    requires_review = bool(projection.get("requiresReview", False))
    contradiction_flags = projection.get("contradictionFlags") if isinstance(projection.get("contradictionFlags"), list) else []
    regime = str(projection.get("regime") or default_regime)

    node_drift = _clamp01(float(projection.get("driftScore", global_drift)))
    contradiction_pressure = min(0.4, 0.12 * len(contradiction_flags))

    coherence_score = _clamp01(0.55 * confidence + 0.45 * global_coherence - 0.20 * node_drift)
    risk_score = _clamp01(0.45 * global_risk + 0.35 * node_drift + contradiction_pressure + (0.10 if requires_review else 0.0))

    if risk_score >= 0.80 or confidence < 0.25:
        status = "reject"
        rule = "critical-risk-reject"
        explanation = "Projection rejected due to critical risk/low confidence against formal coherence constraints."
    elif requires_review or contradiction_flags:
        if confidence >= 0.60 and risk_score <= 0.65:
            status = "observe"
            rule = "review-observe"
            explanation = "Projection requires review; admitted only for annotated observation pending reconciliation."
        else:
            status = "defer"
            rule = "review-defer"
            explanation = "Projection deferred because review/contradictions exceed admissibility thresholds."
    elif confidence >= 0.85 and coherence_score >= 0.75 and risk_score <= 0.30 and node_drift <= 0.35:
        status = "promote"
        rule = "high-coherence-low-risk"
        explanation = "Projection promoted: high coherence with low drift/risk in stable mapping regime."
    elif confidence >= 0.65 and coherence_score >= 0.55 and risk_score <= 0.50:
        status = "admit"
        rule = "admit-balanced"
        explanation = "Projection admitted: confidence and coherence satisfy balanced executive gate thresholds."
    else:
        status = "defer"
        rule = "insufficient-coherence"
        explanation = "Projection deferred due to insufficient coherence-confidence margin under present drift/risk context."

    return AdmissionDecision(
        input_id=input_id,
        audit_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        drift_context={
            "globalDriftScore": round(global_drift, 6),
            "inputDriftScore": round(node_drift, 6),
            "projectionRegime": regime,
            "requiresReview": requires_review,
        },
        governing_rule=rule,
        explanation=(
            f"{explanation} inputId={input_id}, confidence={confidence:.3f}, "
            f"coherence={coherence_score:.3f}, risk={risk_score:.3f}, drift={node_drift:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
        suggested_concept_targets=suggested_targets,
    )


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    projection_doc = _load_json(PROJECTION_PATH)
    projection_summary = _load_json(PROJECTION_SUMMARY_PATH)
    assessment = _load_json(COHERENCE_ASSESSMENT_PATH) if COHERENCE_ASSESSMENT_PATH.exists() else {}
    drift_map = _load_json(COHERENCE_DRIFT_PATH) if COHERENCE_DRIFT_PATH.exists() else {}
    recommendations = _load_json(RECOMMENDATIONS_PATH) if RECOMMENDATIONS_PATH.exists() else {}
    regime_map = _load_json(REGIME_PATH) if REGIME_PATH.exists() else {}

    global_coherence = _clamp01(float(assessment.get("coherenceScore", projection_summary.get("coherenceScore", 0.5))))
    global_risk = _clamp01(float(assessment.get("riskScore", projection_summary.get("riskScore", 0.5))))
    global_drift = _clamp01(float(drift_map.get("globalDriftScore", projection_summary.get("globalDriftScore", 0.0))))
    default_regime = str(assessment.get("regimeClassification", regime_map.get("regime", "watch")))

    projections = projection_doc.get("projections")
    if not isinstance(projections, list):
        projections = []

    decisions = [
        evaluate_projection(
            p,
            global_coherence=global_coherence,
            global_risk=global_risk,
            global_drift=_drift_for_input(str(p.get("inputId") or ""), drift_map),
            default_regime=default_regime,
        )
        for p in projections
        if isinstance(p, dict)
    ]
    decisions = sorted(decisions, key=lambda d: d.input_id)

    created_at = _resolve_created_at(projection_summary, assessment, drift_map)
    recommendation_ref = recommendations.get("schema", "sophia_recommendations_v1") if isinstance(recommendations, dict) else "sophia_recommendations_v1"

    audit_payload = {
        "schema": "sonya_audit_v1",
        "created_at": created_at,
        "phaselock": "raw Sonya input -> CoherenceLattice projection -> Sophia audit -> Publisher memory storage",
        "inputs": {
            "sonya_lattice_projection": str(PROJECTION_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sonya_projection_summary": str(PROJECTION_SUMMARY_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "coherence_assessment": str(COHERENCE_ASSESSMENT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "coherence_drift_map": str(COHERENCE_DRIFT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "sophia_recommendations": recommendation_ref,
        },
        "policy_context": {
            "coherenceScore": global_coherence,
            "riskScore": global_risk,
            "globalDriftScore": global_drift,
            "regimeClassification": default_regime,
        },
        "audits": [
            {
                "inputId": d.input_id,
                "auditStatus": d.audit_status,
                "coherenceScore": d.coherence_score,
                "riskScore": d.risk_score,
                "driftContext": d.drift_context,
                "governingRule": d.governing_rule,
                "explanation": d.explanation,
                "targetPublisherAction": d.target_publisher_action,
                "suggestedConceptTargets": d.suggested_concept_targets,
            }
            for d in decisions
        ],
    }

    decisions_payload = {
        "schema": "sonya_admission_decisions_v1",
        "created_at": created_at,
        "decisions": [
            {
                "inputId": d.input_id,
                "auditStatus": d.audit_status,
                "coherenceScore": d.coherence_score,
                "riskScore": d.risk_score,
                "driftContext": d.drift_context,
                "governingRule": d.governing_rule,
                "explanation": d.explanation,
                "targetPublisherAction": d.target_publisher_action,
                "suggestedConceptTargets": d.suggested_concept_targets,
            }
            for d in decisions
        ],
    }

    Draft202012Validator(_load_json(AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(DECISIONS_SCHEMA_PATH)).validate(decisions_payload)
    return audit_payload, decisions_payload


def main() -> int:
    audit_payload, decisions_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    SONYA_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    SONYA_DECISIONS_OUT.write_text(json.dumps(decisions_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {SONYA_AUDIT_OUT}")
    print(f"Wrote {SONYA_DECISIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
