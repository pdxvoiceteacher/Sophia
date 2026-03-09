from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"

PREDICTION_MAP_PATH = BRIDGE_DIR / "prediction_map.json"
PREDICTION_OUTCOME_REPORT_PATH = BRIDGE_DIR / "prediction_outcome_report.json"
PREDICTION_CALIBRATION_REPORT_PATH = BRIDGE_DIR / "prediction_calibration_report.json"

BRANCH_LIFECYCLE_AUDIT_PATH = BRIDGE_DIR / "branch_lifecycle_audit.json"
TELEMETRY_FIELD_AUDIT_PATH = BRIDGE_DIR / "telemetry_field_audit.json"
CAUSAL_AUDIT_PATH = BRIDGE_DIR / "causal_audit.json"

PREDICTION_AUDIT_OUT = BRIDGE_DIR / "prediction_audit.json"
PREDICTION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "prediction_recommendations.json"


@dataclass(slots=True)
class PredictionDecision:
    target_id: str
    target_type: str
    prediction_status: str
    coherence_score: float
    risk_score: float
    prediction_context: str
    calibration_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in ("records", "recommendations", "targets", "predictions"):
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
        "prediction-watch": "watch",
        "prediction-verify-first": "suppress",
        "prediction-calibrated": "docket",
        "prediction-overconfidence-risk": "suppress",
        "prediction-require-human-review": "docket",
    }[status]


def evaluate_target(
    row: dict[str, Any],
    *,
    outcome_rows: dict[str, dict[str, Any]],
    calibration_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> PredictionDecision:
    target_id = str(row.get("targetId") or row.get("predictionId") or "prediction:unknown")
    target_type = str(row.get("targetType") or "prediction")

    confidence = _clamp01(float(row.get("predictionConfidence", row.get("confidenceScore", 0.5))))
    horizon_fit = _clamp01(float(row.get("horizonFit", 0.5)))
    uncertainty = _clamp01(float(row.get("uncertaintyScore", 0.45)))

    outcome = outcome_rows.get(target_id, {})
    outcome_agreement = _clamp01(float(outcome.get("outcomeAgreement", outcome.get("agreementScore", 0.5))))
    error_rate = _clamp01(float(outcome.get("errorRate", 0.4)))

    calibration = calibration_rows.get(target_id, {})
    calibration_score = _clamp01(float(calibration.get("calibrationScore", 0.5)))
    overconfidence = _clamp01(float(calibration.get("overconfidenceScore", 0.4)))

    coherence = _clamp01(
        0.24 * confidence
        + 0.20 * horizon_fit
        + 0.20 * outcome_agreement
        + 0.20 * calibration_score
        + 0.16 * (1.0 - uncertainty)
    )
    risk = _clamp01(
        0.26 * overconfidence
        + 0.20 * error_rate
        + 0.18 * uncertainty
        + 0.18 * (1.0 - calibration_score)
        + 0.18 * system_risk
    )

    if overconfidence >= 0.82 or (overconfidence >= 0.72 and error_rate >= 0.62):
        status = "prediction-require-human-review"
        rule = "stacked-overconfidence-human-review"
    elif calibration_score <= 0.34 or outcome_agreement <= 0.36:
        status = "prediction-verify-first"
        rule = "verify-first-under-low-calibration"
    elif overconfidence >= 0.62 or risk >= 0.62:
        status = "prediction-overconfidence-risk"
        rule = "suppress-under-overconfidence-risk"
    elif calibration_score >= 0.70 and outcome_agreement >= 0.66 and uncertainty <= 0.44:
        status = "prediction-calibrated"
        rule = "calibrated-prediction-path"
    else:
        status = "prediction-watch"
        rule = "watch-prediction-drift"

    prediction_context = (
        f"predictionConfidence={confidence:.3f}, horizonFit={horizon_fit:.3f}, outcomeAgreement={outcome_agreement:.3f}, "
        f"uncertaintyScore={uncertainty:.3f}"
    )
    calibration_context = (
        f"calibrationScore={calibration_score:.3f}, overconfidenceScore={overconfidence:.3f}, errorRate={error_rate:.3f}, systemRisk={system_risk:.3f}; "
        "predictions are bounded guidance and remain reviewable."
    )
    explanation = (
        f"Prediction guidance is bounded and non-autonomous. targetId={target_id}, predictionStatus={status}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return PredictionDecision(
        target_id=target_id,
        target_type=target_type,
        prediction_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        prediction_context=prediction_context,
        calibration_context=calibration_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(decision: PredictionDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "predictionStatus": decision.prediction_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "predictionContext": decision.prediction_context,
        "calibrationContext": decision.calibration_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def _load_optional(path: Path) -> dict[str, Any]:
    return _load_json(path) if path.exists() else {}


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    prediction_map = _load_optional(PREDICTION_MAP_PATH)
    outcome_report = _load_optional(PREDICTION_OUTCOME_REPORT_PATH)
    calibration_report = _load_optional(PREDICTION_CALIBRATION_REPORT_PATH)

    branch_audit = _load_json(BRANCH_LIFECYCLE_AUDIT_PATH)
    telemetry_audit = _load_json(TELEMETRY_FIELD_AUDIT_PATH)
    causal_audit = _load_json(CAUSAL_AUDIT_PATH)

    branch_risk = _safe_mean([float(r.get("riskScore")) for r in _rows(branch_audit) if isinstance(r.get("riskScore"), (int, float))], 0.45)
    telemetry_risk = _safe_mean([float(r.get("riskScore")) for r in _rows(telemetry_audit) if isinstance(r.get("riskScore"), (int, float))], 0.45)
    causal_risk = _safe_mean([float(r.get("riskScore")) for r in _rows(causal_audit) if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.36 * branch_risk + 0.34 * telemetry_risk + 0.30 * causal_risk)

    base_rows = _rows(prediction_map)
    if not base_rows:
        # fallback: synthesize prediction rows from branch lifecycle records for continuity
        base_rows = [
            {
                "targetId": str(r.get("targetId") or "prediction:unknown"),
                "targetType": str(r.get("targetType") or "prediction"),
                "predictionConfidence": _clamp01(float(r.get("coherenceScore", 0.5))),
                "horizonFit": _clamp01(1.0 - float(r.get("riskScore", 0.45))),
                "uncertaintyScore": _clamp01(float(r.get("riskScore", 0.45))),
            }
            for r in _rows(branch_audit)
        ]

    outcome_rows = {str(r.get("targetId")): r for r in _rows(outcome_report) if isinstance(r.get("targetId"), str)}
    calibration_rows = {str(r.get("targetId")): r for r in _rows(calibration_report) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            outcome_rows=outcome_rows,
            calibration_rows=calibration_rows,
            system_risk=system_risk,
        )
        for row in base_rows
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    created_at = _resolve_created_at(prediction_map, outcome_report, calibration_report, branch_audit)
    phaselock = (
        "telemetry -> lattice -> donation -> taf -> branch emergence/lifecycle -> prediction generation -> "
        "outcome comparison -> calibration feedback"
    )
    caution = "Prediction recommendations are bounded learning guidance only and do not autonomously authorize action."

    metadata = {
        "systemRisk": round(system_risk, 6),
        "inputs": [
            "bridge/prediction_map.json",
            "bridge/prediction_outcome_report.json",
            "bridge/prediction_calibration_report.json",
            "bridge/branch_lifecycle_audit.json",
            "bridge/telemetry_field_audit.json",
            "bridge/causal_audit.json",
        ],
    }

    audit_payload = {
        "schema": "prediction_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    recommendations_payload = {
        "schema": "prediction_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia prediction-state audit")
    parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs()
    PREDICTION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    PREDICTION_RECOMMENDATIONS_OUT.write_text(json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {PREDICTION_AUDIT_OUT}")
    print(f"Wrote {PREDICTION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
