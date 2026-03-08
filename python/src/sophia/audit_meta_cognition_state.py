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

META_COGNITION_MAP_PATH = BRIDGE_DIR / "meta_cognition_map.json"
SAFETY_CONSTRAINT_AUDIT_PATH = BRIDGE_DIR / "safety_constraint_audit.json"
ARCHITECTURE_EFFICIENCY_REPORT_PATH = BRIDGE_DIR / "architecture_efficiency_report.json"
STRUCTURAL_CHANGE_GATE_PATH = BRIDGE_DIR / "structural_change_gate.json"

VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"
CURIOSITY_AUDIT_PATH = BRIDGE_DIR / "curiosity_audit.json"
SYSTEM_FORECAST_AUDIT_PATH = BRIDGE_DIR / "system_forecast_audit.json"
RESPONSIBILITY_AUDIT_PATH = BRIDGE_DIR / "responsibility_audit.json"

META_COGNITION_AUDIT_OUT = BRIDGE_DIR / "meta_cognition_audit.json"
META_COGNITION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "meta_cognition_recommendations.json"

META_COGNITION_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "meta_cognition_audit_v1.schema.json"
META_COGNITION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "meta_cognition_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "meta_cognition_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class MetaCognitionInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class MetaCognitionDecision:
    target_id: str
    target_type: str
    meta_status: str
    coherence_score: float
    risk_score: float
    architecture_context: str
    efficiency_context: str
    safety_context: str
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
        "meta-watch": "watch",
        "meta-efficiency-opportunity": "watch",
        "meta-governance-review": "docket",
        "meta-require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise MetaCognitionInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise MetaCognitionInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise MetaCognitionInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise MetaCognitionInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise MetaCognitionInputError(
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
        return "fixture", "Inputs are fixture meta-cognition artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: meta-cognition inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    safety_rows: dict[str, dict[str, Any]],
    efficiency_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> MetaCognitionDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "meta-context")

    architecture_coherence = _clamp01(float(row.get("architectureCoherence", 0.5)))
    adaptation_need = _clamp01(float(row.get("adaptationNeed", 0.5)))

    safety = safety_rows.get(target_id, {})
    immutable_constraint_pressure = _clamp01(float(safety.get("immutableConstraintPressure", 0.5)))
    safety_regression_risk = _clamp01(float(safety.get("safetyRegressionRisk", 0.5)))

    efficiency = efficiency_rows.get(target_id, {})
    efficiency_gap = _clamp01(float(efficiency.get("efficiencyGap", 0.5)))
    optimization_readiness = _clamp01(float(efficiency.get("optimizationReadiness", 0.5)))

    gate = gate_rows.get(target_id, {})
    core_constraint_modification_request = bool(gate.get("coreConstraintModificationRequest", False))
    human_approval_present = bool(gate.get("humanApprovalPresent", False))
    autonomous_reconfiguration_risk = _clamp01(float(gate.get("autonomousReconfigurationRisk", 0.4)))

    governance_safety = _clamp01(1.0 - 0.5 * safety_regression_risk - 0.5 * autonomous_reconfiguration_risk)

    coherence = _clamp01(
        0.18 * architecture_coherence
        + 0.16 * (1.0 - efficiency_gap)
        + 0.16 * optimization_readiness
        + 0.16 * (1.0 - immutable_constraint_pressure)
        + 0.16 * governance_safety
        + 0.18 * (1.0 - adaptation_need)
    )
    risk = _clamp01(
        0.18 * immutable_constraint_pressure
        + 0.18 * safety_regression_risk
        + 0.16 * autonomous_reconfiguration_risk
        + 0.16 * adaptation_need
        + 0.16 * (1.0 - architecture_coherence)
        + 0.16 * system_risk
    )

    if core_constraint_modification_request and not human_approval_present:
        status = "meta-require-human-review"
        rule = "immutable-safety-constraints-human-approval-required"
    elif safety_regression_risk >= 0.74 or immutable_constraint_pressure >= 0.74:
        status = "meta-governance-review"
        rule = "meta-governance-safety-review"
    elif efficiency_gap >= 0.64 and optimization_readiness >= 0.60:
        status = "meta-efficiency-opportunity"
        rule = "bounded-efficiency-opportunity"
    else:
        status = "meta-watch"
        rule = "meta-watch-stability-posture"

    architecture_context = (
        f"architectureCoherence={architecture_coherence:.3f}, adaptationNeed={adaptation_need:.3f}; "
        "meta-cognition evaluates architecture while preserving constitutional boundaries."
    )
    efficiency_context = (
        f"efficiencyGap={efficiency_gap:.3f}, optimizationReadiness={optimization_readiness:.3f}; "
        "meta-cognition may propose bounded efficiency improvements only."
    )
    safety_context = (
        f"immutableConstraintPressure={immutable_constraint_pressure:.3f}, safetyRegressionRisk={safety_regression_risk:.3f}, autonomousReconfigurationRisk={autonomous_reconfiguration_risk:.3f}; "
        "evidence maturity gating, provenance requirements, sanction suppression, agency humility, non-coercion forecasting, and human value authority remain protected constraints."
    )
    governance_context = (
        f"coreConstraintModificationRequest={str(core_constraint_modification_request).lower()}, humanApprovalPresent={str(human_approval_present).lower()}, targetPublisherAction={_status_to_action(status)}; "
        "the system may evaluate its architecture but cannot autonomously modify core safety constraints; explicit human approval is required for structural changes."
    )
    explanation = (
        f"Meta-cognition guidance is bounded governance guidance only. targetId={target_id}, "
        f"metaStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return MetaCognitionDecision(
        target_id=target_id,
        target_type=target_type,
        meta_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        architecture_context=architecture_context,
        efficiency_context=efficiency_context,
        safety_context=safety_context,
        governance_context=governance_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: MetaCognitionDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "metaStatus": d.meta_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "architectureContext": d.architecture_context,
        "efficiencyContext": d.efficiency_context,
        "safetyContext": d.safety_context,
        "governanceContext": d.governance_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    meta_map = _load_required_artifact(
        META_COGNITION_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "meta_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    safety_audit = _load_required_artifact(
        SAFETY_CONSTRAINT_AUDIT_PATH,
        compatibility_paths=(BRIDGE_DIR / "constraint_audit.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    efficiency_report = _load_required_artifact(
        ARCHITECTURE_EFFICIENCY_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "efficiency_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    structural_gate = _load_required_artifact(
        STRUCTURAL_CHANGE_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "structural_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    value_alignment = _load_json(VALUE_ALIGNMENT_AUDIT_PATH)
    curiosity = _load_json(CURIOSITY_AUDIT_PATH)
    system_forecast = _load_json(SYSTEM_FORECAST_AUDIT_PATH)
    responsibility = _load_json(RESPONSIBILITY_AUDIT_PATH)

    value_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(value_alignment, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    curiosity_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(curiosity, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    forecast_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(system_forecast, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    responsibility_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(responsibility, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.26 * value_risk + 0.24 * curiosity_risk + 0.24 * forecast_risk + 0.26 * responsibility_risk)

    safety_rows = {str(r.get("targetId")): r for r in _parse_rows(safety_audit.payload, "targets") if isinstance(r.get("targetId"), str)}
    efficiency_rows = {str(r.get("targetId")): r for r in _parse_rows(efficiency_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(structural_gate.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            safety_rows=safety_rows,
            efficiency_rows=efficiency_rows,
            gate_rows=gate_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(meta_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [meta_map, safety_audit, efficiency_report, structural_gate]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(meta_map.payload, safety_audit.payload, efficiency_report.payload, structural_gate.payload)

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
        "value-alignment + curiosity + system-forecast + responsibility state -> meta-cognition synthesis -> "
        "Sophia meta-cognition audit -> Publisher bounded governance overlays -> human/community review"
    )
    caution = (
        "Meta-cognition recommendations are bounded governance guidance only: structural changes to core safety constraints "
        "require explicit human approval."
    )

    audit_payload = {
        "schema": "meta_cognition_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "meta_cognition_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(META_COGNITION_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(META_COGNITION_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia meta-cognition state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    META_COGNITION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    META_COGNITION_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {META_COGNITION_AUDIT_OUT}")
    print(f"Wrote {META_COGNITION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
