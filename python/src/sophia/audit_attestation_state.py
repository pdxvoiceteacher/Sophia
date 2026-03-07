from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

ATTESTATION_STATE_MAP_PATH = BRIDGE_DIR / "attestation_state_map.json"
ATTESTATION_STATE_SUMMARY_PATH = BRIDGE_DIR / "attestation_state_summary.json"
WITNESS_ROSTER_CANDIDATES_PATH = BRIDGE_DIR / "witness_roster_candidates.json"
ATTESTATION_CANDIDATE_MAP_PATH = BRIDGE_DIR / "attestation_candidate_map.json"
RECOVERY_AUDIT_PATH = BRIDGE_DIR / "recovery_audit.json"
RESILIENCE_AUDIT_PATH = BRIDGE_DIR / "resilience_audit.json"
CONSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "constitutional_audit.json"
CONTINUITY_MODE_ASSESSMENT_PATH = BRIDGE_DIR / "continuity_mode_assessment.json"

WITNESS_AUDIT_OUT = BRIDGE_DIR / "witness_audit.json"
ATTESTATION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "attestation_recommendations.json"

WITNESS_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "witness_audit_v1.schema.json"
ATTESTATION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "attestation_recommendations_v1.schema.json"


@dataclass(slots=True)
class AttestationDecision:
    witness_id: str | None
    attestation_id: str | None
    witness_status: str
    attestation_status: str
    coherence_score: float
    risk_score: float
    tamper_risk: float
    anti_capture_risk: float
    continuity_context: dict[str, Any]
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
        "docket-for-witness": "docket",
        "watch": "watch",
        "hold": "watch",
        "reject-attestation": "suppress",
        "require-broader-human-review": "docket",
    }[status]


def _system_context(recovery: dict[str, Any], resilience: dict[str, Any], constitutional: dict[str, Any], continuity: dict[str, Any]) -> tuple[float, float, float]:
    recovery_rows = recovery.get("records") if isinstance(recovery.get("records"), list) else []
    resilience_rows = resilience.get("records") if isinstance(resilience.get("records"), list) else []
    constitutional_rows = constitutional.get("evaluations") if isinstance(constitutional.get("evaluations"), list) else []

    tamper = _safe_mean([float(r.get("tamperRisk")) for r in recovery_rows if isinstance(r, dict) and isinstance(r.get("tamperRisk"), (int, float))], 0.3)
    anti_capture = _safe_mean([float(r.get("antiCaptureRisk", r.get("captureRisk", 0.3))) for r in resilience_rows if isinstance(r, dict) and isinstance(r.get("antiCaptureRisk", r.get("captureRisk")), (int, float))], 0.35)
    gov_risk = _safe_mean([float(r.get("governanceRisk")) for r in constitutional_rows if isinstance(r, dict) and isinstance(r.get("governanceRisk"), (int, float))], 0.3)
    stress = _clamp01(float(continuity.get("stressScore", 0.0)))
    return _clamp01(tamper), _clamp01(max(anti_capture, gov_risk)), stress


def _witness_status(sufficiency: float, conflict_risk: float, anti_capture: float) -> str:
    if sufficiency >= 0.74 and conflict_risk <= 0.30 and anti_capture <= 0.42:
        return "sufficient"
    if anti_capture >= 0.74 or conflict_risk >= 0.70:
        return "stacked-risk"
    if sufficiency <= 0.35:
        return "insufficient"
    if sufficiency < 0.48:
        return "indeterminate"
    return "strained"


def evaluate_witness(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    continuity_mode: dict[str, Any],
    system_tamper: float,
    system_anti_capture: float,
    continuity_stress: float,
) -> AttestationDecision:
    witness_id = str(row.get("witnessId") or "witness:unknown")
    sufficiency = _clamp01(float(row.get("witnessSufficiencyScore", summary.get("meanWitnessSufficiencyScore", 0.5))))
    conflict_risk = _clamp01(float(row.get("conflictRisk", 0.2)))
    distribution = _clamp01(float(row.get("distributionScore", 0.5)))
    evidence_chain = _clamp01(float(row.get("evidenceChainScore", 0.5)))

    coherence = _clamp01(0.35 * sufficiency + 0.30 * distribution + 0.25 * evidence_chain + 0.10 * (1.0 - conflict_risk))
    tamper_risk = _clamp01(0.45 * system_tamper + 0.25 * (1.0 - evidence_chain) + 0.20 * (1.0 - distribution) + 0.10 * conflict_risk)
    anti_capture_risk = _clamp01(0.45 * system_anti_capture + 0.30 * conflict_risk + 0.25 * (1.0 - distribution))
    risk = _clamp01(0.35 * tamper_risk + 0.35 * anti_capture_risk + 0.20 * continuity_stress + 0.10 * (1.0 - sufficiency))

    witness_status = _witness_status(sufficiency, conflict_risk, anti_capture_risk)

    if witness_status == "stacked-risk" or risk >= 0.82:
        status = "reject-attestation"
        rule = "stacked-risk-reject"
        explanation = "Witness profile is stacked-risk under anti-capture constraints and cannot support attestation progression."
    elif risk >= 0.68 or witness_status in {"insufficient", "indeterminate"}:
        status = "require-broader-human-review"
        rule = "broaden-witness-review"
        explanation = "Witness sufficiency is limited; broader human/community review is required before attestation use."
    elif witness_status == "sufficient" and risk <= 0.40:
        status = "docket-for-witness"
        rule = "sufficient-witness-docket"
        explanation = "Witness candidate is sufficient for advisory docketing under distributed integrity testimony safeguards."
    elif risk <= 0.60:
        status = "watch"
        rule = "witness-watchlist"
        explanation = "Witness candidate remains on integrity testimony watchlist pending stronger distributed evidence confidence."
    else:
        status = "hold"
        rule = "witness-hold"
        explanation = "Witness candidate is held under elevated ambiguity pending additional anti-tamper evidence."

    continuity_label = str(continuity_mode.get("continuityMode") or "normal")
    if continuity_label in {"degraded", "preservation", "emergency"} and status == "watch":
        status = "hold"
        rule = "degraded-continuity-witness-hold"
        explanation = "Continuity degradation requires conservative hold posture for witness progression; no automatic transition is authorized."

    return AttestationDecision(
        witness_id=witness_id,
        attestation_id=None,
        witness_status=witness_status,
        attestation_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        tamper_risk=round(tamper_risk, 6),
        anti_capture_risk=round(anti_capture_risk, 6),
        continuity_context={
            "continuityMode": continuity_label,
            "stressScore": round(continuity_stress, 6),
            "witnessSufficiencyScore": round(sufficiency, 6),
        },
        governing_rule=rule,
        explanation=(
            f"{explanation} witnessId={witness_id}, coherence={coherence:.3f}, risk={risk:.3f}, tamperRisk={tamper_risk:.3f}, antiCaptureRisk={anti_capture_risk:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def evaluate_attestation(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    witness_by_id: dict[str, AttestationDecision],
    continuity_mode: dict[str, Any],
    system_tamper: float,
    system_anti_capture: float,
    continuity_stress: float,
) -> AttestationDecision:
    attestation_id = str(row.get("attestationId") or "attestation:unknown")
    witness_id = str(row.get("witnessId") or "")

    legitimacy = _clamp01(float(row.get("attestationLegitimacyScore", summary.get("meanAttestationLegitimacyScore", 0.5))))
    transparency = _clamp01(float(row.get("evidenceTransparencyScore", 0.5)))
    contradiction = _clamp01(float(row.get("contradictionScore", 0.0)))

    linked = witness_by_id.get(witness_id)
    linked_sufficiency = linked.coherence_score if linked else _clamp01(float(summary.get("meanLinkedWitnessCoherence", 0.5)))
    linked_risk = linked.risk_score if linked else _clamp01(float(summary.get("meanLinkedWitnessRisk", 0.4)))
    linked_witness_status = linked.witness_status if linked else "indeterminate"

    coherence = _clamp01(0.40 * legitimacy + 0.30 * transparency + 0.20 * linked_sufficiency + 0.10 * (1.0 - contradiction))
    tamper_risk = _clamp01(0.40 * system_tamper + 0.30 * contradiction + 0.20 * (1.0 - transparency) + 0.10 * linked_risk)
    anti_capture_risk = _clamp01(0.45 * system_anti_capture + 0.30 * linked_risk + 0.25 * contradiction)
    risk = _clamp01(0.35 * tamper_risk + 0.35 * anti_capture_risk + 0.20 * continuity_stress + 0.10 * (1.0 - legitimacy))

    if linked_witness_status == "sufficient" and anti_capture_risk <= 0.42:
        witness_status = "sufficient"
    elif linked_witness_status == "stacked-risk" or anti_capture_risk >= 0.74:
        witness_status = "stacked-risk"
    elif linked_witness_status == "insufficient":
        witness_status = "insufficient"
    elif linked_witness_status == "indeterminate":
        witness_status = "indeterminate"
    else:
        witness_status = "strained"

    if witness_status == "stacked-risk" or risk >= 0.82:
        status = "reject-attestation"
        rule = "attestation-stacked-risk-reject"
        explanation = "Attestation candidate is rejected under stacked-risk witness or integrity conditions."
    elif witness_status in {"insufficient", "indeterminate"} or risk >= 0.66:
        status = "require-broader-human-review"
        rule = "attestation-broader-review"
        explanation = "Attestation legitimacy requires broader human/community witnessing before any transition claims are considered."
    elif witness_status == "sufficient" and coherence >= 0.70 and risk <= 0.40:
        status = "docket-for-witness"
        rule = "attestation-docket-for-witness"
        explanation = "Attestation candidate is suitable for advisory witness docket review under distributed trust safeguards."
    elif risk <= 0.62:
        status = "watch"
        rule = "attestation-watchlist"
        explanation = "Attestation candidate remains on watchlist pending stronger testimony sufficiency and anti-tamper evidence."
    else:
        status = "hold"
        rule = "attestation-hold"
        explanation = "Attestation candidate is held due to unresolved integrity ambiguity."

    continuity_label = str(continuity_mode.get("continuityMode") or "normal")
    if continuity_label in {"degraded", "preservation", "emergency"} and status == "watch":
        status = "hold"
        rule = "degraded-mode-attestation-hold"
        explanation = "Degraded continuity mode applies constrained hold for attestation progression; witness audit alone cannot trigger state transition."

    return AttestationDecision(
        witness_id=None,
        attestation_id=attestation_id,
        witness_status=witness_status,
        attestation_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        tamper_risk=round(tamper_risk, 6),
        anti_capture_risk=round(anti_capture_risk, 6),
        continuity_context={
            "continuityMode": continuity_label,
            "stressScore": round(continuity_stress, 6),
            "linkedWitnessId": witness_id,
            "linkedWitnessStatus": linked_witness_status,
        },
        governing_rule=rule,
        explanation=(
            f"{explanation} attestationId={attestation_id}, coherence={coherence:.3f}, risk={risk:.3f}, tamperRisk={tamper_risk:.3f}, antiCaptureRisk={anti_capture_risk:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(item: AttestationDecision) -> dict[str, Any]:
    payload = {
        "witnessStatus": item.witness_status,
        "attestationStatus": item.attestation_status,
        "coherenceScore": item.coherence_score,
        "riskScore": item.risk_score,
        "tamperRisk": item.tamper_risk,
        "antiCaptureRisk": item.anti_capture_risk,
        "continuityContext": item.continuity_context,
        "governingRule": item.governing_rule,
        "explanation": item.explanation,
        "targetPublisherAction": item.target_publisher_action,
    }
    if item.witness_id is not None:
        payload["witnessId"] = item.witness_id
    if item.attestation_id is not None:
        payload["attestationId"] = item.attestation_id
    return payload


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    attestation_state_map = _load_json(ATTESTATION_STATE_MAP_PATH)
    attestation_state_summary = _load_json(ATTESTATION_STATE_SUMMARY_PATH)
    witness_roster = _load_json(WITNESS_ROSTER_CANDIDATES_PATH)
    attestation_candidate_map = _load_json(ATTESTATION_CANDIDATE_MAP_PATH)
    recovery_audit = _load_json(RECOVERY_AUDIT_PATH)
    resilience_audit = _load_json(RESILIENCE_AUDIT_PATH)
    constitutional_audit = _load_json(CONSTITUTIONAL_AUDIT_PATH)
    continuity_mode = _load_json(CONTINUITY_MODE_ASSESSMENT_PATH)

    system_tamper, system_anti_capture, continuity_stress = _system_context(
        recovery_audit, resilience_audit, constitutional_audit, continuity_mode
    )

    witness_rows = witness_roster.get("witnesses") if isinstance(witness_roster.get("witnesses"), list) else []
    witness_decisions = [
        evaluate_witness(
            row,
            summary=attestation_state_summary,
            continuity_mode=continuity_mode,
            system_tamper=system_tamper,
            system_anti_capture=system_anti_capture,
            continuity_stress=continuity_stress,
        )
        for row in witness_rows
        if isinstance(row, dict)
    ]
    witness_decisions = sorted(witness_decisions, key=lambda item: item.witness_id or "")
    witness_by_id = {item.witness_id: item for item in witness_decisions if item.witness_id is not None}

    attestation_rows = attestation_candidate_map.get("attestations") if isinstance(attestation_candidate_map.get("attestations"), list) else []
    attestation_decisions = [
        evaluate_attestation(
            row,
            summary=attestation_state_summary,
            witness_by_id=witness_by_id,
            continuity_mode=continuity_mode,
            system_tamper=system_tamper,
            system_anti_capture=system_anti_capture,
            continuity_stress=continuity_stress,
        )
        for row in attestation_rows
        if isinstance(row, dict)
    ]
    attestation_decisions = sorted(attestation_decisions, key=lambda item: item.attestation_id or "")

    combined = witness_decisions + attestation_decisions
    combined = sorted(combined, key=lambda item: item.witness_id or item.attestation_id or "")

    created_at = _resolve_created_at(attestation_state_summary, attestation_state_map, continuity_mode)
    phaselock = (
        "canonical / continuity / recovery state -> CoherenceLattice attestation formalization -> Sophia witness/attestation audit -> "
        "Publisher attestation overlays -> external human/community witnessing"
    )

    witness_audit_payload = {
        "schema": "witness_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": "Attestation recommendations are advisory and review-oriented; witnessing does not transfer sovereignty or canonical mutation rights.",
        "records": [_to_payload(item) for item in combined],
    }

    attestation_recommendations_payload = {
        "schema": "attestation_recommendations_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice attestation formalization -> Sophia witness/attestation audit -> Publisher attestation overlays",
        "caution": "No automatic state transition occurs from witness audit alone; external review remains required.",
        "recommendations": [_to_payload(item) for item in attestation_decisions],
    }

    Draft202012Validator(_load_json(WITNESS_AUDIT_SCHEMA_PATH)).validate(witness_audit_payload)
    Draft202012Validator(_load_json(ATTESTATION_RECOMMENDATIONS_SCHEMA_PATH)).validate(attestation_recommendations_payload)
    return witness_audit_payload, attestation_recommendations_payload


def main() -> int:
    witness_audit_payload, attestation_recommendations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    WITNESS_AUDIT_OUT.write_text(json.dumps(witness_audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    ATTESTATION_RECOMMENDATIONS_OUT.write_text(
        json.dumps(attestation_recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {WITNESS_AUDIT_OUT}")
    print(f"Wrote {ATTESTATION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
