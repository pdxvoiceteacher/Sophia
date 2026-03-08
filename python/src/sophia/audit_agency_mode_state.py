from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

AGENCY_MODE_HYPOTHESIS_MAP_PATH = BRIDGE_DIR / "agency_mode_hypothesis_map.json"
AGENCY_FIT_COMPARISON_REPORT_PATH = BRIDGE_DIR / "agency_fit_comparison_report.json"
TEL_BRANCH_SIGNATURE_MAP_PATH = BRIDGE_DIR / "tel_branch_signature_map.json"
AGENCY_GOVERNANCE_MODE_GATE_PATH = BRIDGE_DIR / "agency_governance_mode_gate.json"

PREDICTION_AUDIT_PATH = BRIDGE_DIR / "prediction_audit.json"
EXPERIMENTAL_AUDIT_PATH = BRIDGE_DIR / "experimental_audit.json"
THEORY_CORPUS_AUDIT_PATH = BRIDGE_DIR / "theory_corpus_audit.json"
COLLABORATIVE_REVIEW_AUDIT_PATH = BRIDGE_DIR / "collaborative_review_audit.json"

AGENCY_MODE_AUDIT_OUT = BRIDGE_DIR / "agency_mode_audit.json"
AGENCY_MODE_RECOMMENDATIONS_OUT = BRIDGE_DIR / "agency_mode_recommendations.json"

AGENCY_MODE_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "agency_mode_audit_v1.schema.json"
AGENCY_MODE_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "agency_mode_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "agency_mode_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class AgencyModeInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class AgencyModeDecision:
    target_id: str
    target_type: str
    agency_status: str
    coherence_score: float
    risk_score: float
    fit_context: str
    entropy_context: str
    calibration_context: str
    fairness_context: str
    governance_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_rows(payload: dict[str, Any], key: str) -> list[dict[str, Any]]:
    value = payload.get(key)
    return [row for row in value if isinstance(row, dict)] if isinstance(value, list) else []


def _safe_mean(values: list[float], default: float = 0.0) -> float:
    return sum(values) / len(values) if values else default


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for doc in docs:
        for key in ("generatedAt", "created_at"):
            value = doc.get(key)
            if isinstance(value, str) and value:
                return value
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str) -> str:
    return {
        "deterministic-lean": "watch",
        "volitional-lean": "watch",
        "mixed": "watch",
        "underdetermined": "suppress",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise AgencyModeInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise AgencyModeInputError(f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}")
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise AgencyModeInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")
    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise AgencyModeInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise AgencyModeInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )
    payload = _load_json(found[0])
    _validate_provenance(payload, path=found[0])
    return LoadedArtifact(path=found[0], payload=payload, source_mode="compatibility")


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture agency-mode artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: agency-mode inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    fit_rows: dict[str, dict[str, Any]],
    signature_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> AgencyModeDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "agency-context")

    deterministic_fit = _clamp01(float(row.get("deterministicFit", 0.5)))
    volitional_fit = _clamp01(float(row.get("volitionalFit", 0.5)))

    fit = fit_rows.get(target_id, {})
    fit_confidence = _clamp01(float(fit.get("fitConfidence", 0.5)))
    fairness_score = _clamp01(float(fit.get("fairnessScore", 0.5)))

    sig = signature_rows.get(target_id, {})
    branch_entropy = _clamp01(float(sig.get("branchEntropy", 0.5)))
    calibration_score = _clamp01(float(sig.get("calibrationScore", 0.5)))

    gate = gate_rows.get(target_id, {})
    deterministic_overreach = _clamp01(float(gate.get("deterministicOverreach", 0.4)))
    punitive_volitional = _clamp01(float(gate.get("punitiveVolitional", 0.4)))
    governance_readiness = _clamp01(float(gate.get("governanceReadiness", 0.5)))

    fit_gap = abs(deterministic_fit - volitional_fit)

    coherence = _clamp01(
        0.18 * deterministic_fit
        + 0.18 * volitional_fit
        + 0.16 * fit_confidence
        + 0.16 * calibration_score
        + 0.16 * fairness_score
        + 0.16 * governance_readiness
    )
    risk = _clamp01(
        0.20 * deterministic_overreach
        + 0.20 * punitive_volitional
        + 0.16 * (1.0 - fairness_score)
        + 0.16 * (1.0 - governance_readiness)
        + 0.12 * branch_entropy
        + 0.16 * system_risk
    )

    if deterministic_overreach >= 0.80 or punitive_volitional >= 0.80:
        status = "require-human-review"
        rule = "overreach-or-punitive-human-review"
    elif governance_readiness <= 0.34 or fit_confidence <= 0.34:
        status = "underdetermined"
        rule = "underdetermined-governance-posture"
    elif fit_gap <= 0.10:
        status = "mixed"
        rule = "mixed-agency-hypothesis-balance"
    elif deterministic_fit > volitional_fit:
        status = "deterministic-lean"
        rule = "deterministic-lean-under-fairness-constraint"
    else:
        status = "volitional-lean"
        rule = "volitional-lean-under-fairness-constraint"

    fit_context = (
        f"deterministicFit={deterministic_fit:.3f}, volitionalFit={volitional_fit:.3f}, fitConfidence={fit_confidence:.3f}, fitGap={fit_gap:.3f}; "
        "agency models are comparative and provisional."
    )
    entropy_context = (
        f"branchEntropy={branch_entropy:.3f}, governanceReadiness={governance_readiness:.3f}; "
        "high entropy reduces governance certainty."
    )
    calibration_context = (
        f"calibrationScore={calibration_score:.3f}, systemRisk={system_risk:.3f}; "
        "calibration constrains stance switching."
    )
    fairness_context = (
        f"fairnessScore={fairness_score:.3f}, deterministicOverreach={deterministic_overreach:.3f}, punitiveVolitional={punitive_volitional:.3f}; "
        "both determinist overreach and volitional romanticism are constrained."
    )
    governance_context = (
        f"governanceReadiness={governance_readiness:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "agency guidance remains bounded modeling guidance only."
    )

    explanation = (
        f"Agency-mode guidance is bounded modeling guidance only. targetId={target_id}, agencyStatus={status}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return AgencyModeDecision(
        target_id=target_id,
        target_type=target_type,
        agency_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        fit_context=fit_context,
        entropy_context=entropy_context,
        calibration_context=calibration_context,
        fairness_context=fairness_context,
        governance_context=governance_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: AgencyModeDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "agencyStatus": d.agency_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "fitContext": d.fit_context,
        "entropyContext": d.entropy_context,
        "calibrationContext": d.calibration_context,
        "fairnessContext": d.fairness_context,
        "governanceContext": d.governance_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    hypothesis = _load_required_artifact(
        AGENCY_MODE_HYPOTHESIS_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "agency_hypothesis_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    fit_report = _load_required_artifact(
        AGENCY_FIT_COMPARISON_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "agency_fit_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    signature = _load_required_artifact(
        TEL_BRANCH_SIGNATURE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "branch_signature_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    gate = _load_required_artifact(
        AGENCY_GOVERNANCE_MODE_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "agency_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    prediction = _load_json(PREDICTION_AUDIT_PATH)
    experimental = _load_json(EXPERIMENTAL_AUDIT_PATH)
    theory = _load_json(THEORY_CORPUS_AUDIT_PATH)
    collaborative = _load_json(COLLABORATIVE_REVIEW_AUDIT_PATH)

    prediction_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(prediction, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    experimental_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(experimental, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    theory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(theory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    collaborative_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(collaborative, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.26 * prediction_risk + 0.24 * experimental_risk + 0.24 * theory_risk + 0.26 * collaborative_risk)

    fit_rows = {str(r.get("targetId")): r for r in _parse_rows(fit_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    signature_rows = {str(r.get("targetId")): r for r in _parse_rows(signature.payload, "targets") if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(gate.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            fit_rows=fit_rows,
            signature_rows=signature_rows,
            gate_rows=gate_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(hypothesis.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [hypothesis, fit_report, signature, gate]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(hypothesis.payload, fit_report.payload, signature.payload, gate.payload)

    metadata = {
        "inputMode": mode,
        "inputModeWarning": warning,
        "systemRisk": round(system_risk, 6),
        "inputArtifacts": [
            {
                "path": str(a.path.relative_to(REPO_ROOT)) if a.path.is_relative_to(REPO_ROOT) else str(a.path),
                "sourceMode": a.source_mode,
                "schemaVersion": str(a.payload.get("schemaVersion")),
                "producerRepo": str(a.payload.get("producerRepo")),
                "producerModule": str(a.payload.get("producerModule")),
                "producerCommit": str(a.payload.get("producerCommit")),
                "generatedAt": str(a.payload.get("generatedAt")),
            }
            for a in loaded
        ],
    }

    phaselock = (
        "prediction + experimental + theory + collaborative state -> agency-mode comparator formalization -> "
        "Sophia agency-mode audit -> Publisher bounded governance overlays -> human/community review"
    )
    caution = "Agency-mode recommendations are bounded modeling guidance only and do not certify metaphysical truth about human agency."

    audit_payload = {
        "schema": "agency_mode_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "agency_mode_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(AGENCY_MODE_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(AGENCY_MODE_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia agency-mode state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    AGENCY_MODE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    AGENCY_MODE_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {AGENCY_MODE_AUDIT_OUT}")
    print(f"Wrote {AGENCY_MODE_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
