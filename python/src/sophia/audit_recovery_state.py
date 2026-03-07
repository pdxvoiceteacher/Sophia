from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

PRESERVATION_STATE_MAP_PATH = BRIDGE_DIR / "preservation_state_map.json"
PRESERVATION_STATE_SUMMARY_PATH = BRIDGE_DIR / "preservation_state_summary.json"
ARTIFACT_ESCROW_PLAN_PATH = BRIDGE_DIR / "artifact_escrow_plan.json"
RECOVERY_CANDIDATE_MAP_PATH = BRIDGE_DIR / "recovery_candidate_map.json"
RESILIENCE_AUDIT_PATH = BRIDGE_DIR / "resilience_audit.json"
CONSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "constitutional_audit.json"
CONTINUITY_MODE_ASSESSMENT_PATH = BRIDGE_DIR / "continuity_mode_assessment.json"

RECOVERY_AUDIT_OUT = BRIDGE_DIR / "recovery_audit.json"
RECOVERY_RECOMMENDATIONS_OUT = BRIDGE_DIR / "recovery_recommendations.json"

RECOVERY_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "recovery_audit_v1.schema.json"
RECOVERY_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "recovery_recommendations_v1.schema.json"


@dataclass(slots=True)
class RecoveryDecision:
    preservation_id: str | None
    recovery_id: str | None
    recovery_status: str
    coherence_score: float
    risk_score: float
    tamper_risk: float
    continuity_context: dict[str, Any]
    anti_capture_context: dict[str, Any]
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


def _safe_mean(vals: list[float], default: float = 0.0) -> float:
    if not vals:
        return default
    return sum(vals) / len(vals)


def _status_to_action(status: str) -> str:
    return {
        "maintain": "watch",
        "escrow-review": "docket",
        "watch": "watch",
        "hold": "watch",
        "reject": "suppress",
        "require-human-emergency-review": "docket",
    }[status]


def _system_context(resilience: dict[str, Any], constitutional: dict[str, Any], continuity: dict[str, Any]) -> tuple[float, float, float]:
    resilience_rows = resilience.get("records") if isinstance(resilience.get("records"), list) else []
    constitutional_rows = constitutional.get("evaluations") if isinstance(constitutional.get("evaluations"), list) else []
    fragility = _safe_mean(
        [float(r.get("riskScore")) for r in resilience_rows if isinstance(r, dict) and isinstance(r.get("riskScore"), (int, float))],
        0.35,
    )
    capture = _safe_mean(
        [float(r.get("antiCaptureRisk", r.get("captureRisk", 0.3))) for r in resilience_rows if isinstance(r, dict) and isinstance(r.get("antiCaptureRisk", r.get("captureRisk")), (int, float))],
        0.35,
    )
    constitutional_risk = _safe_mean(
        [float(r.get("governanceRisk")) for r in constitutional_rows if isinstance(r, dict) and isinstance(r.get("governanceRisk"), (int, float))],
        0.3,
    )
    continuity_stress = _clamp01(float(continuity.get("stressScore", 0.0)))
    return _clamp01(fragility), _clamp01(max(capture, constitutional_risk)), continuity_stress


def evaluate_preservation(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    escrow_plan: dict[str, Any],
    continuity_mode: dict[str, Any],
    fragility: float,
    anti_capture: float,
    continuity_stress: float,
) -> RecoveryDecision:
    preservation_id = str(row.get("preservationId") or "preservation:unknown")
    criticality = _clamp01(float(row.get("criticalityScore", summary.get("meanCriticalityScore", 0.5))))
    recoverability = _clamp01(float(row.get("recoverabilityScore", summary.get("meanRecoverabilityScore", 0.5))))
    dependency_opacity = _clamp01(float(row.get("dependencyOpacityRisk", 0.2)))
    tamper_signal = _clamp01(float(row.get("tamperSignalScore", 0.0)))

    escrow_rows = escrow_plan.get("escrowEntries") if isinstance(escrow_plan.get("escrowEntries"), list) else []
    entry = next((e for e in escrow_rows if isinstance(e, dict) and e.get("preservationId") == preservation_id), {})
    escrow_distribution = _clamp01(float(entry.get("distributedCustodyScore", 0.5)))
    escrow_integrity = _clamp01(float(entry.get("integrityEvidenceScore", 0.5)))

    coherence = _clamp01(0.35 * recoverability + 0.30 * escrow_integrity + 0.20 * escrow_distribution + 0.15 * (1.0 - dependency_opacity))
    tamper_risk = _clamp01(0.40 * tamper_signal + 0.25 * dependency_opacity + 0.20 * (1.0 - escrow_integrity) + 0.15 * fragility)
    risk = _clamp01(0.35 * tamper_risk + 0.25 * anti_capture + 0.20 * continuity_stress + 0.20 * (1.0 - recoverability))

    continuity_label = str(continuity_mode.get("continuityMode") or "normal")
    if tamper_risk >= 0.78 or risk >= 0.84:
        status = "require-human-emergency-review"
        rule = "critical-tamper-emergency-review"
        explanation = "Preservation target shows critical tamper ambiguity; freeze and route to immediate human/community recovery review."
    elif tamper_risk >= 0.62 or dependency_opacity >= 0.60:
        status = "hold"
        rule = "freeze-under-tamper-ambiguity"
        explanation = "Integrity uncertainty triggers freeze + watch posture pending auditable escrow evidence."
    elif coherence >= 0.68 and risk <= 0.42 and criticality >= 0.55:
        status = "escrow-review"
        rule = "bounded-escrow-review"
        explanation = "Preservation target is suitable for escrow-review docketing under bounded anti-tamper governance controls."
    elif coherence >= 0.52 and risk <= 0.62:
        status = "watch"
        rule = "integrity-watchlist"
        explanation = "Preservation target remains on integrity watchlist with non-executing recovery preparation only."
    else:
        status = "maintain"
        rule = "maintain-observational"
        explanation = "Preservation target remains in maintain mode with ongoing evidence escrow verification."

    if continuity_label in {"degraded", "preservation", "emergency"} and status in {"maintain", "watch"}:
        status = "hold"
        rule = "degraded-continuity-hold"
        explanation = "Continuity degradation requires constrained hold posture; no autonomous replication or self-resurrection is authorized."

    return RecoveryDecision(
        preservation_id=preservation_id,
        recovery_id=None,
        recovery_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        tamper_risk=round(tamper_risk, 6),
        continuity_context={
            "continuityMode": continuity_label,
            "stressScore": round(continuity_stress, 6),
            "criticalityScore": round(criticality, 6),
        },
        anti_capture_context={
            "antiCaptureRisk": round(anti_capture, 6),
            "distributedCustodyScore": round(escrow_distribution, 6),
            "dependencyOpacityRisk": round(dependency_opacity, 6),
        },
        governing_rule=rule,
        explanation=(
            f"{explanation} preservationId={preservation_id}, coherence={coherence:.3f}, risk={risk:.3f}, tamperRisk={tamper_risk:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def evaluate_recovery_candidate(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    continuity_mode: dict[str, Any],
    fragility: float,
    anti_capture: float,
    continuity_stress: float,
) -> RecoveryDecision:
    recovery_id = str(row.get("recoveryId") or "recovery:unknown")
    recoverability = _clamp01(float(row.get("recoverabilityScore", summary.get("meanRecoverabilityScore", 0.5))))
    procedural_transparency = _clamp01(float(row.get("proceduralTransparencyScore", 0.5)))
    tamper_signal = _clamp01(float(row.get("tamperSignalScore", 0.0)))
    dependency_opacity = _clamp01(float(row.get("dependencyOpacityRisk", 0.25)))

    coherence = _clamp01(0.45 * recoverability + 0.30 * procedural_transparency + 0.25 * (1.0 - dependency_opacity))
    tamper_risk = _clamp01(0.45 * tamper_signal + 0.30 * dependency_opacity + 0.25 * (1.0 - procedural_transparency))
    risk = _clamp01(0.35 * tamper_risk + 0.25 * anti_capture + 0.20 * continuity_stress + 0.20 * (1.0 - recoverability + fragility) / 2.0)

    continuity_label = str(continuity_mode.get("continuityMode") or "normal")
    if tamper_risk >= 0.80 or risk >= 0.85:
        status = "require-human-emergency-review"
        rule = "recovery-critical-integrity-escalation"
        explanation = "Recovery candidate has critical integrity risk and requires immediate human/community emergency review."
    elif tamper_risk >= 0.64:
        status = "reject"
        rule = "reject-opaque-recovery-path"
        explanation = "Recovery candidate is rejected due to opaque or tamper-ambiguous restoration path."
    elif coherence >= 0.70 and risk <= 0.40:
        status = "escrow-review"
        rule = "recovery-by-review-not-resurrection"
        explanation = "Recovery candidate is eligible for bounded escrow-review; restoration remains inspectable and human/community reviewed."
    elif coherence >= 0.55 and risk <= 0.65:
        status = "watch"
        rule = "recovery-watchlist"
        explanation = "Recovery candidate remains on watchlist pending stronger anti-tamper evidence and dependency transparency."
    else:
        status = "hold"
        rule = "hold-for-integrity-clarification"
        explanation = "Recovery candidate is held until integrity and dependency transparency concerns are resolved."

    if continuity_label in {"degraded", "preservation", "emergency"} and status == "watch":
        status = "hold"
        rule = "degraded-mode-recovery-hold"
        explanation = "Degraded continuity mode applies constrained recovery hold; no self-executing recovery is authorized."

    return RecoveryDecision(
        preservation_id=None,
        recovery_id=recovery_id,
        recovery_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        tamper_risk=round(tamper_risk, 6),
        continuity_context={
            "continuityMode": continuity_label,
            "stressScore": round(continuity_stress, 6),
            "recoverabilityScore": round(recoverability, 6),
        },
        anti_capture_context={
            "antiCaptureRisk": round(anti_capture, 6),
            "proceduralTransparencyScore": round(procedural_transparency, 6),
            "dependencyOpacityRisk": round(dependency_opacity, 6),
        },
        governing_rule=rule,
        explanation=(
            f"{explanation} recoveryId={recovery_id}, coherence={coherence:.3f}, risk={risk:.3f}, tamperRisk={tamper_risk:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(item: RecoveryDecision) -> dict[str, Any]:
    payload = {
        "recoveryStatus": item.recovery_status,
        "coherenceScore": item.coherence_score,
        "riskScore": item.risk_score,
        "tamperRisk": item.tamper_risk,
        "continuityContext": item.continuity_context,
        "antiCaptureContext": item.anti_capture_context,
        "governingRule": item.governing_rule,
        "explanation": item.explanation,
        "targetPublisherAction": item.target_publisher_action,
    }
    if item.preservation_id is not None:
        payload["preservationId"] = item.preservation_id
    if item.recovery_id is not None:
        payload["recoveryId"] = item.recovery_id
    return payload


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    preservation_map = _load_json(PRESERVATION_STATE_MAP_PATH)
    preservation_summary = _load_json(PRESERVATION_STATE_SUMMARY_PATH)
    escrow_plan = _load_json(ARTIFACT_ESCROW_PLAN_PATH)
    recovery_map = _load_json(RECOVERY_CANDIDATE_MAP_PATH)
    resilience_audit = _load_json(RESILIENCE_AUDIT_PATH)
    constitutional_audit = _load_json(CONSTITUTIONAL_AUDIT_PATH)
    continuity_mode = _load_json(CONTINUITY_MODE_ASSESSMENT_PATH)

    fragility, anti_capture, continuity_stress = _system_context(
        resilience_audit, constitutional_audit, continuity_mode
    )

    preservation_rows = preservation_map.get("preservations") if isinstance(preservation_map.get("preservations"), list) else []
    preservation_decisions = [
        evaluate_preservation(
            row,
            summary=preservation_summary,
            escrow_plan=escrow_plan,
            continuity_mode=continuity_mode,
            fragility=fragility,
            anti_capture=anti_capture,
            continuity_stress=continuity_stress,
        )
        for row in preservation_rows
        if isinstance(row, dict)
    ]

    recovery_rows = recovery_map.get("recoveries") if isinstance(recovery_map.get("recoveries"), list) else []
    recovery_decisions = [
        evaluate_recovery_candidate(
            row,
            summary=preservation_summary,
            continuity_mode=continuity_mode,
            fragility=fragility,
            anti_capture=anti_capture,
            continuity_stress=continuity_stress,
        )
        for row in recovery_rows
        if isinstance(row, dict)
    ]

    combined = preservation_decisions + recovery_decisions
    combined = sorted(combined, key=lambda item: item.preservation_id or item.recovery_id or "")
    recovery_decisions = sorted(recovery_decisions, key=lambda item: item.recovery_id or "")

    created_at = _resolve_created_at(preservation_summary, escrow_plan, continuity_mode)
    phaselock = (
        "artifact / governance / continuity state -> CoherenceLattice preservation and recovery formalization -> "
        "Sophia recovery audit -> Publisher escrow/recovery overlays -> human/community recovery action"
    )

    audit_payload = {
        "schema": "recovery_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": "Recovery recommendations are bounded, review-oriented, and anti-tamper; no autonomous replication or self-resurrection is authorized.",
        "records": [_to_payload(item) for item in combined],
    }

    recommendations_payload = {
        "schema": "recovery_recommendations_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice preservation and recovery formalization -> Sophia recovery audit -> Publisher recovery docket",
        "caution": "Lawful human/community review remains the path for recovery actions; no self-executing recovery is authorized.",
        "recommendations": [_to_payload(item) for item in recovery_decisions],
    }

    Draft202012Validator(_load_json(RECOVERY_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(RECOVERY_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main() -> int:
    audit_payload, recommendations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    RECOVERY_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    RECOVERY_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {RECOVERY_AUDIT_OUT}")
    print(f"Wrote {RECOVERY_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
