from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

PRECEDENT_STATE_MAP_PATH = BRIDGE_DIR / "precedent_state_map.json"
PRECEDENT_STATE_SUMMARY_PATH = BRIDGE_DIR / "precedent_state_summary.json"
CASE_ANALOGY_CANDIDATES_PATH = BRIDGE_DIR / "case_analogy_candidates.json"
PRECEDENT_DIVERGENCE_REPORT_PATH = BRIDGE_DIR / "precedent_divergence_report.json"
CONSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "constitutional_audit.json"
QUORUM_AUDIT_PATH = BRIDGE_DIR / "quorum_audit.json"
RESILIENCE_AUDIT_PATH = BRIDGE_DIR / "resilience_audit.json"
RECOVERY_AUDIT_PATH = BRIDGE_DIR / "recovery_audit.json"
WITNESS_AUDIT_PATH = BRIDGE_DIR / "witness_audit.json"

PRECEDENT_AUDIT_OUT = BRIDGE_DIR / "precedent_audit.json"
PRECEDENT_RECOMMENDATIONS_OUT = BRIDGE_DIR / "precedent_recommendations.json"

PRECEDENT_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "precedent_audit_v1.schema.json"
PRECEDENT_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "precedent_recommendations_v1.schema.json"


@dataclass(slots=True)
class PrecedentDecision:
    case_id: str
    precedent_status: str
    coherence_score: float
    risk_score: float
    divergence_level: float
    anti_capture_risk: float
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
        "follow-precedent": "docket",
        "distinguish-case": "docket",
        "watch-divergence": "watch",
        "reject-analogy": "suppress",
        "require-broader-human-review": "docket",
    }[status]


def _system_risks(
    constitutional: dict[str, Any],
    quorum: dict[str, Any],
    resilience: dict[str, Any],
    recovery: dict[str, Any],
    witness: dict[str, Any],
) -> tuple[float, float, float]:
    constitutional_rows = constitutional.get("evaluations") if isinstance(constitutional.get("evaluations"), list) else []
    quorum_rows = quorum.get("records") if isinstance(quorum.get("records"), list) else []
    resilience_rows = resilience.get("records") if isinstance(resilience.get("records"), list) else []
    recovery_rows = recovery.get("records") if isinstance(recovery.get("records"), list) else []
    witness_rows = witness.get("records") if isinstance(witness.get("records"), list) else []

    constitutional_risk = _safe_mean(
        [float(r.get("governanceRisk")) for r in constitutional_rows if isinstance(r, dict) and isinstance(r.get("governanceRisk"), (int, float))],
        0.3,
    )
    anti_capture = _safe_mean(
        [float(r.get("antiCaptureRisk", r.get("captureRisk", 0.3))) for r in resilience_rows if isinstance(r, dict) and isinstance(r.get("antiCaptureRisk", r.get("captureRisk")), (int, float))],
        0.35,
    )
    process_risk = _safe_mean(
        [float(r.get("riskScore")) for r in quorum_rows if isinstance(r, dict) and isinstance(r.get("riskScore"), (int, float))],
        0.4,
    )
    recovery_tamper = _safe_mean(
        [float(r.get("tamperRisk")) for r in recovery_rows if isinstance(r, dict) and isinstance(r.get("tamperRisk"), (int, float))],
        0.3,
    )
    witness_risk = _safe_mean(
        [float(r.get("riskScore")) for r in witness_rows if isinstance(r, dict) and isinstance(r.get("riskScore"), (int, float))],
        0.35,
    )

    return _clamp01(max(anti_capture, constitutional_risk)), _clamp01(process_risk), _clamp01(max(recovery_tamper, witness_risk))


def evaluate_case(
    row: dict[str, Any],
    *,
    precedent_summary: dict[str, Any],
    analogy_rows: dict[str, dict[str, Any]],
    divergence_rows: dict[str, dict[str, Any]],
    anti_capture_risk: float,
    process_risk: float,
    integrity_risk: float,
) -> PrecedentDecision:
    case_id = str(row.get("caseId") or "case:unknown")
    base_precedent_strength = _clamp01(float(row.get("precedentStrength", precedent_summary.get("meanPrecedentStrength", 0.5))))
    constitutional_alignment = _clamp01(float(row.get("constitutionalAlignment", precedent_summary.get("meanConstitutionalAlignment", 0.5))))

    analogy = analogy_rows.get(case_id, {})
    similarity = _clamp01(float(analogy.get("similarityScore", precedent_summary.get("meanSimilarityScore", 0.5))))
    novelty = _clamp01(float(analogy.get("noveltyScore", 0.2)))
    conflict_exposure = _clamp01(float(analogy.get("conflictExposure", 0.2)))

    divergence = divergence_rows.get(case_id, {})
    divergence_level = _clamp01(float(divergence.get("divergenceLevel", precedent_summary.get("meanDivergenceLevel", 0.3))))
    divergence_explained = bool(divergence.get("divergenceExplained", False))

    coherence = _clamp01(
        0.30 * base_precedent_strength
        + 0.25 * similarity
        + 0.25 * constitutional_alignment
        + 0.20 * (1.0 - novelty)
    )

    risk = _clamp01(
        0.30 * divergence_level
        + 0.20 * anti_capture_risk
        + 0.20 * process_risk
        + 0.15 * integrity_risk
        + 0.15 * conflict_exposure
    )

    if anti_capture_risk >= 0.70 or (divergence_level >= 0.68 and not divergence_explained):
        status = "require-broader-human-review"
        rule = "anti-capture-review-override"
        explanation = "Precedent reuse under elevated anti-capture or unexplained divergence requires broader human/community review."
    elif divergence_level >= 0.78 and conflict_exposure >= 0.55:
        status = "reject-analogy"
        rule = "reject-capture-tainted-analogy"
        explanation = "Analogy is rejected due to high divergence/conflict risk that could harden weak precedent into dogma."
    elif coherence >= 0.72 and risk <= 0.38 and divergence_level <= 0.35:
        status = "follow-precedent"
        rule = "follow-persuasive-precedent"
        explanation = "Case can follow persuasive precedent under low-risk, constitutionally aligned conditions."
    elif divergence_level >= 0.45 and (constitutional_alignment >= 0.65 or anti_capture_risk >= 0.50):
        status = "distinguish-case"
        rule = "constitutional-or-anti-capture-distinguish"
        explanation = "Case should be distinguished with explicit reasoning; divergence may be legitimate under constitutional or anti-capture pressure."
    elif risk <= 0.62:
        status = "watch-divergence"
        rule = "divergence-watchlist"
        explanation = "Case remains on divergence watchlist pending stronger explanatory support and lower process risk."
    else:
        status = "require-broader-human-review"
        rule = "uncertain-precedent-broader-review"
        explanation = "Precedent context remains uncertain and requires broader human/community deliberation."

    return PrecedentDecision(
        case_id=case_id,
        precedent_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        divergence_level=round(divergence_level, 6),
        anti_capture_risk=round(anti_capture_risk, 6),
        governing_rule=rule,
        explanation=(
            f"{explanation} caseId={case_id}, coherence={coherence:.3f}, risk={risk:.3f}, divergence={divergence_level:.3f}, antiCaptureRisk={anti_capture_risk:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(item: PrecedentDecision) -> dict[str, Any]:
    return {
        "caseId": item.case_id,
        "precedentStatus": item.precedent_status,
        "coherenceScore": item.coherence_score,
        "riskScore": item.risk_score,
        "divergenceLevel": item.divergence_level,
        "antiCaptureRisk": item.anti_capture_risk,
        "governingRule": item.governing_rule,
        "explanation": item.explanation,
        "targetPublisherAction": item.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    precedent_state_map = _load_json(PRECEDENT_STATE_MAP_PATH)
    precedent_state_summary = _load_json(PRECEDENT_STATE_SUMMARY_PATH)
    case_analogies = _load_json(CASE_ANALOGY_CANDIDATES_PATH)
    divergence_report = _load_json(PRECEDENT_DIVERGENCE_REPORT_PATH)
    constitutional_audit = _load_json(CONSTITUTIONAL_AUDIT_PATH)
    quorum_audit = _load_json(QUORUM_AUDIT_PATH)
    resilience_audit = _load_json(RESILIENCE_AUDIT_PATH)
    recovery_audit = _load_json(RECOVERY_AUDIT_PATH)
    witness_audit = _load_json(WITNESS_AUDIT_PATH)

    anti_capture_risk, process_risk, integrity_risk = _system_risks(
        constitutional_audit,
        quorum_audit,
        resilience_audit,
        recovery_audit,
        witness_audit,
    )

    analogy_rows = {
        str(r.get("caseId")): r
        for r in (case_analogies.get("cases") if isinstance(case_analogies.get("cases"), list) else [])
        if isinstance(r, dict) and isinstance(r.get("caseId"), str)
    }
    divergence_rows = {
        str(r.get("caseId")): r
        for r in (divergence_report.get("cases") if isinstance(divergence_report.get("cases"), list) else [])
        if isinstance(r, dict) and isinstance(r.get("caseId"), str)
    }

    case_rows = precedent_state_map.get("cases") if isinstance(precedent_state_map.get("cases"), list) else []
    decisions = [
        evaluate_case(
            row,
            precedent_summary=precedent_state_summary,
            analogy_rows=analogy_rows,
            divergence_rows=divergence_rows,
            anti_capture_risk=anti_capture_risk,
            process_risk=process_risk,
            integrity_risk=integrity_risk,
        )
        for row in case_rows
        if isinstance(row, dict)
    ]
    decisions = sorted(decisions, key=lambda item: item.case_id)

    created_at = _resolve_created_at(precedent_state_summary, precedent_state_map, divergence_report)
    phaselock = (
        "review / governance / continuity / attestation outcomes -> CoherenceLattice precedent formalization -> "
        "Sophia precedent audit -> Publisher precedent and case-memory overlays -> human/community use of precedent in deliberation"
    )

    audit_payload = {
        "schema": "precedent_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": "Precedent recommendations are advisory only; precedent is persuasive rather than automatically binding.",
        "records": [_to_payload(item) for item in decisions],
    }

    recommendations_payload = {
        "schema": "precedent_recommendations_v1",
        "created_at": created_at,
        "phaselock": "CoherenceLattice precedent formalization -> Sophia precedent audit -> Publisher case-memory overlays",
        "caution": "Divergence may be legitimate under constitutional or anti-capture pressure; no automatic doctrine hardening occurs.",
        "recommendations": [_to_payload(item) for item in decisions],
    }

    Draft202012Validator(_load_json(PRECEDENT_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(PRECEDENT_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main() -> int:
    audit_payload, recommendations_payload = build_outputs()
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    PRECEDENT_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    PRECEDENT_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {PRECEDENT_AUDIT_OUT}")
    print(f"Wrote {PRECEDENT_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
