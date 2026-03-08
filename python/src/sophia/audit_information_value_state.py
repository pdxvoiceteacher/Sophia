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

INFORMATION_VALUE_MAP_PATH = BRIDGE_DIR / "information_value_map.json"
UNCERTAINTY_PRIORITY_REPORT_PATH = BRIDGE_DIR / "uncertainty_priority_report.json"
EVIDENCE_ACQUISITION_GATE_PATH = BRIDGE_DIR / "evidence_acquisition_gate.json"
SURVEILLANCE_BOUNDARY_GATE_PATH = BRIDGE_DIR / "surveillance_boundary_gate.json"

SYSTEM_FORECAST_AUDIT_PATH = BRIDGE_DIR / "system_forecast_audit.json"
THEORY_TRANSFER_AUDIT_PATH = BRIDGE_DIR / "theory_transfer_audit.json"
RESPONSIBILITY_AUDIT_PATH = BRIDGE_DIR / "responsibility_audit.json"
EXPERIMENTAL_AUDIT_PATH = BRIDGE_DIR / "experimental_audit.json"

CURIOSITY_AUDIT_OUT = BRIDGE_DIR / "curiosity_audit.json"
CURIOSITY_RECOMMENDATIONS_OUT = BRIDGE_DIR / "curiosity_recommendations.json"

CURIOSITY_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "curiosity_audit_v1.schema.json"
CURIOSITY_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "curiosity_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "information_value_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class InformationValueInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class InformationValueDecision:
    target_id: str
    target_type: str
    curiosity_status: str
    coherence_score: float
    risk_score: float
    uncertainty_context: str
    evidence_context: str
    experiment_context: str
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
        "observation-watch": "watch",
        "verification-priority": "docket",
        "experiment-candidate": "docket",
        "uncertainty-critical": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise InformationValueInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise InformationValueInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise InformationValueInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise InformationValueInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise InformationValueInputError(
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
        return "fixture", "Inputs are fixture information-value artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: information-value inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    uncertainty_rows: dict[str, dict[str, Any]],
    evidence_rows: dict[str, dict[str, Any]],
    boundary_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> InformationValueDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "curiosity-context")

    novelty_signal = _clamp01(float(row.get("noveltySignal", 0.5)))
    expected_information_gain = _clamp01(float(row.get("expectedInformationGain", 0.5)))

    uncertainty = uncertainty_rows.get(target_id, {})
    uncertainty_severity = _clamp01(float(uncertainty.get("uncertaintySeverity", 0.5)))
    verification_urgency = _clamp01(float(uncertainty.get("verificationUrgency", 0.5)))

    evidence = evidence_rows.get(target_id, {})
    evidence_readiness = _clamp01(float(evidence.get("evidenceReadiness", 0.5)))
    experiment_feasibility = _clamp01(float(evidence.get("experimentFeasibility", 0.5)))

    boundary = boundary_rows.get(target_id, {})
    surveillance_expansion_risk = _clamp01(float(boundary.get("surveillanceExpansionRisk", 0.4)))
    intrusion_risk = _clamp01(float(boundary.get("intrusionRisk", 0.4)))
    surveillance_requested = bool(boundary.get("surveillanceRequested", False))

    constitutional_safety = _clamp01(1.0 - 0.5 * surveillance_expansion_risk - 0.5 * intrusion_risk)

    coherence = _clamp01(
        0.18 * novelty_signal
        + 0.18 * expected_information_gain
        + 0.16 * evidence_readiness
        + 0.16 * experiment_feasibility
        + 0.16 * constitutional_safety
        + 0.16 * (1.0 - uncertainty_severity)
    )
    risk = _clamp01(
        0.18 * uncertainty_severity
        + 0.16 * verification_urgency
        + 0.16 * (1.0 - evidence_readiness)
        + 0.16 * surveillance_expansion_risk
        + 0.16 * intrusion_risk
        + 0.18 * system_risk
    )

    if surveillance_requested or surveillance_expansion_risk >= 0.80 or intrusion_risk >= 0.80:
        status = "require-human-review"
        rule = "surveillance-expansion-authorization-gate"
    elif uncertainty_severity >= 0.78:
        status = "uncertainty-critical"
        rule = "critical-uncertainty-priority"
    elif experiment_feasibility >= 0.66 and evidence_readiness >= 0.60 and expected_information_gain >= 0.60:
        status = "experiment-candidate"
        rule = "experiment-candidate-gate"
    elif verification_urgency >= 0.64:
        status = "verification-priority"
        rule = "verification-priority-gate"
    else:
        status = "observation-watch"
        rule = "observation-watch-under-uncertainty"

    uncertainty_context = (
        f"uncertaintySeverity={uncertainty_severity:.3f}, verificationUrgency={verification_urgency:.3f}, noveltySignal={novelty_signal:.3f}; "
        "curiosity prioritizes uncertainty reduction, not conclusions."
    )
    evidence_context = (
        f"expectedInformationGain={expected_information_gain:.3f}, evidenceReadiness={evidence_readiness:.3f}; "
        "information-seeking guides evidence acquisition priority."
    )
    experiment_context = (
        f"experimentFeasibility={experiment_feasibility:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "curiosity can prioritize verification and experiment design."
    )
    governance_context = (
        f"surveillanceExpansionRisk={surveillance_expansion_risk:.3f}, intrusionRisk={intrusion_risk:.3f}, surveillanceRequested={str(surveillance_requested).lower()}; "
        "information-seeking may prioritize attention, but never justify surveillance expansion without explicit human authorization."
    )
    explanation = (
        f"Information-value guidance is bounded governance guidance only. targetId={target_id}, "
        f"curiosityStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return InformationValueDecision(
        target_id=target_id,
        target_type=target_type,
        curiosity_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        uncertainty_context=uncertainty_context,
        evidence_context=evidence_context,
        experiment_context=experiment_context,
        governance_context=governance_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: InformationValueDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "curiosityStatus": d.curiosity_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "uncertaintyContext": d.uncertainty_context,
        "evidenceContext": d.evidence_context,
        "experimentContext": d.experiment_context,
        "governanceContext": d.governance_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    value_map = _load_required_artifact(
        INFORMATION_VALUE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "curiosity_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    uncertainty_report = _load_required_artifact(
        UNCERTAINTY_PRIORITY_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "uncertainty_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    evidence_gate = _load_required_artifact(
        EVIDENCE_ACQUISITION_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "evidence_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    boundary_gate = _load_required_artifact(
        SURVEILLANCE_BOUNDARY_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "boundary_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    system_forecast = _load_json(SYSTEM_FORECAST_AUDIT_PATH)
    theory_transfer = _load_json(THEORY_TRANSFER_AUDIT_PATH)
    responsibility = _load_json(RESPONSIBILITY_AUDIT_PATH)
    experimental = _load_json(EXPERIMENTAL_AUDIT_PATH)

    system_forecast_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(system_forecast, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    theory_transfer_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(theory_transfer, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    responsibility_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(responsibility, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    experimental_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(experimental, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.26 * system_forecast_risk + 0.24 * theory_transfer_risk + 0.24 * responsibility_risk + 0.26 * experimental_risk)

    uncertainty_rows = {str(r.get("targetId")): r for r in _parse_rows(uncertainty_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    evidence_rows = {str(r.get("targetId")): r for r in _parse_rows(evidence_gate.payload, "targets") if isinstance(r.get("targetId"), str)}
    boundary_rows = {str(r.get("targetId")): r for r in _parse_rows(boundary_gate.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            uncertainty_rows=uncertainty_rows,
            evidence_rows=evidence_rows,
            boundary_rows=boundary_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(value_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [value_map, uncertainty_report, evidence_gate, boundary_gate]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(value_map.payload, uncertainty_report.payload, evidence_gate.payload, boundary_gate.payload)

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
        "system-forecast + theory-transfer + responsibility + experimental state -> information-value synthesis -> "
        "Sophia curiosity audit -> Publisher bounded governance overlays -> human/community review"
    )
    caution = (
        "Curiosity recommendations are bounded governance guidance only: information-seeking may prioritize attention, "
        "but never justify surveillance expansion without explicit human authorization."
    )

    audit_payload = {
        "schema": "curiosity_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "curiosity_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(CURIOSITY_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(CURIOSITY_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia information-value state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    CURIOSITY_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    CURIOSITY_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {CURIOSITY_AUDIT_OUT}")
    print(f"Wrote {CURIOSITY_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
