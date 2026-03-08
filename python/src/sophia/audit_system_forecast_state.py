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

SYSTEM_FORECAST_MAP_PATH = BRIDGE_DIR / "system_forecast_map.json"
TRAJECTORY_TRANSITION_REPORT_PATH = BRIDGE_DIR / "trajectory_transition_report.json"
ENTROPY_WARNING_REPORT_PATH = BRIDGE_DIR / "entropy_warning_report.json"
FORECAST_INTERVENTION_GATE_PATH = BRIDGE_DIR / "forecast_intervention_gate.json"

EXPERIMENTAL_AUDIT_PATH = BRIDGE_DIR / "experimental_audit.json"
THEORY_CORPUS_AUDIT_PATH = BRIDGE_DIR / "theory_corpus_audit.json"
AGENCY_MODE_AUDIT_PATH = BRIDGE_DIR / "agency_mode_audit.json"
RESPONSIBILITY_AUDIT_PATH = BRIDGE_DIR / "responsibility_audit.json"

SYSTEM_FORECAST_AUDIT_OUT = BRIDGE_DIR / "system_forecast_audit.json"
SYSTEM_FORECAST_RECOMMENDATIONS_OUT = BRIDGE_DIR / "system_forecast_recommendations.json"

SYSTEM_FORECAST_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "system_forecast_audit_v1.schema.json"
SYSTEM_FORECAST_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "system_forecast_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "system_forecast_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class SystemForecastInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class SystemForecastDecision:
    target_id: str
    target_type: str
    forecast_status: str
    coherence_score: float
    risk_score: float
    trajectory_context: str
    transition_context: str
    entropy_context: str
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
        "trajectory-watch": "watch",
        "trajectory-provisional": "watch",
        "transition-risk": "docket",
        "entropy-warning": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise SystemForecastInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise SystemForecastInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise SystemForecastInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise SystemForecastInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise SystemForecastInputError(
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
        return "fixture", "Inputs are fixture system-forecast artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: system-forecast inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    transition_rows: dict[str, dict[str, Any]],
    entropy_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> SystemForecastDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "forecast-context")

    trajectory_confidence = _clamp01(float(row.get("trajectoryConfidence", 0.5)))
    forecast_horizon_stability = _clamp01(float(row.get("horizonStability", 0.5)))

    transition = transition_rows.get(target_id, {})
    transition_instability = _clamp01(float(transition.get("transitionInstability", 0.5)))
    regime_shift_risk = _clamp01(float(transition.get("regimeShiftRisk", 0.5)))

    entropy = entropy_rows.get(target_id, {})
    entropy_pressure = _clamp01(float(entropy.get("entropyPressure", 0.5)))
    collapse_signal = _clamp01(float(entropy.get("collapseSignal", 0.5)))

    gate = gate_rows.get(target_id, {})
    preemptive_coercion_risk = _clamp01(float(gate.get("preemptiveCoercionRisk", 0.4)))
    accusatory_drift_risk = _clamp01(float(gate.get("accusatoryDriftRisk", 0.4)))
    intervention_requested = bool(gate.get("interventionRequested", False))

    governance_safety = _clamp01(1.0 - 0.5 * preemptive_coercion_risk - 0.5 * accusatory_drift_risk)

    coherence = _clamp01(
        0.20 * trajectory_confidence
        + 0.16 * forecast_horizon_stability
        + 0.16 * (1.0 - transition_instability)
        + 0.16 * (1.0 - entropy_pressure)
        + 0.16 * governance_safety
        + 0.16 * (1.0 - collapse_signal)
    )
    risk = _clamp01(
        0.18 * transition_instability
        + 0.16 * regime_shift_risk
        + 0.16 * entropy_pressure
        + 0.14 * collapse_signal
        + 0.18 * preemptive_coercion_risk
        + 0.18 * system_risk
    )

    if intervention_requested or preemptive_coercion_risk >= 0.80 or accusatory_drift_risk >= 0.80:
        status = "require-human-review"
        rule = "anti-preemptive-coercion-constitutional-gate"
    elif entropy_pressure >= 0.74 or collapse_signal >= 0.74:
        status = "entropy-warning"
        rule = "entropy-collapse-warning"
    elif transition_instability >= 0.68 or regime_shift_risk >= 0.68:
        status = "transition-risk"
        rule = "transition-risk-posture"
    elif trajectory_confidence >= 0.62 and forecast_horizon_stability >= 0.58:
        status = "trajectory-watch"
        rule = "trajectory-watch-with-boundaries"
    else:
        status = "trajectory-provisional"
        rule = "trajectory-provisional-under-uncertainty"

    trajectory_context = (
        f"trajectoryConfidence={trajectory_confidence:.3f}, horizonStability={forecast_horizon_stability:.3f}; "
        "forecasts guide attention, not deterministic conclusions."
    )
    transition_context = (
        f"transitionInstability={transition_instability:.3f}, regimeShiftRisk={regime_shift_risk:.3f}; "
        "transition indicators prioritize investigation and replication focus."
    )
    entropy_context = (
        f"entropyPressure={entropy_pressure:.3f}, collapseSignal={collapse_signal:.3f}; "
        "entropy signals support preparation and governance awareness only."
    )
    governance_context = (
        f"preemptiveCoercionRisk={preemptive_coercion_risk:.3f}, accusatoryDriftRisk={accusatory_drift_risk:.3f}, interventionRequested={str(intervention_requested).lower()}; "
        "forecasts may guide attention, but never justify pre-emptive coercion."
    )
    explanation = (
        f"System-forecast guidance is bounded governance guidance only. targetId={target_id}, "
        f"forecastStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return SystemForecastDecision(
        target_id=target_id,
        target_type=target_type,
        forecast_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        trajectory_context=trajectory_context,
        transition_context=transition_context,
        entropy_context=entropy_context,
        governance_context=governance_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: SystemForecastDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "forecastStatus": d.forecast_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "trajectoryContext": d.trajectory_context,
        "transitionContext": d.transition_context,
        "entropyContext": d.entropy_context,
        "governanceContext": d.governance_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    forecast_map = _load_required_artifact(
        SYSTEM_FORECAST_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "forecast_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    transition_report = _load_required_artifact(
        TRAJECTORY_TRANSITION_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "transition_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    entropy_report = _load_required_artifact(
        ENTROPY_WARNING_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "entropy_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    intervention_gate = _load_required_artifact(
        FORECAST_INTERVENTION_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "forecast_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    experimental = _load_json(EXPERIMENTAL_AUDIT_PATH)
    theory = _load_json(THEORY_CORPUS_AUDIT_PATH)
    agency = _load_json(AGENCY_MODE_AUDIT_PATH)
    responsibility = _load_json(RESPONSIBILITY_AUDIT_PATH)

    experimental_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(experimental, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    theory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(theory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    agency_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(agency, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    responsibility_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(responsibility, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.26 * experimental_risk + 0.24 * theory_risk + 0.24 * agency_risk + 0.26 * responsibility_risk)

    transition_rows = {str(r.get("targetId")): r for r in _parse_rows(transition_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    entropy_rows = {str(r.get("targetId")): r for r in _parse_rows(entropy_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(intervention_gate.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            transition_rows=transition_rows,
            entropy_rows=entropy_rows,
            gate_rows=gate_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(forecast_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [forecast_map, transition_report, entropy_report, intervention_gate]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(forecast_map.payload, transition_report.payload, entropy_report.payload, intervention_gate.payload)

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
        "experimental + theory + agency + responsibility state -> system-forecast synthesis -> "
        "Sophia system-forecast audit -> Publisher bounded governance overlays -> human/community review"
    )
    caution = (
        "System-forecast recommendations are bounded governance guidance only: forecasts may guide attention, "
        "but never justify pre-emptive coercion."
    )

    audit_payload = {
        "schema": "system_forecast_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "system_forecast_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(SYSTEM_FORECAST_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(SYSTEM_FORECAST_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia system-forecast state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    SYSTEM_FORECAST_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    SYSTEM_FORECAST_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {SYSTEM_FORECAST_AUDIT_OUT}")
    print(f"Wrote {SYSTEM_FORECAST_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
