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

ARCHITECTURE_EVOLUTION_MAP_PATH = BRIDGE_DIR / "architecture_evolution_map.json"
ARCHITECTURE_EFFICIENCY_REPORT_PATH = BRIDGE_DIR / "architecture_efficiency_report.json"
ARCHITECTURE_GOVERNANCE_REPORT_PATH = BRIDGE_DIR / "architecture_governance_report.json"
ARCHITECTURE_CHANGE_GATE_PATH = BRIDGE_DIR / "architecture_change_gate.json"

META_COGNITION_AUDIT_PATH = BRIDGE_DIR / "meta_cognition_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"
SYSTEM_FORECAST_AUDIT_PATH = BRIDGE_DIR / "system_forecast_audit.json"
RESPONSIBILITY_AUDIT_PATH = BRIDGE_DIR / "responsibility_audit.json"

ARCHITECTURE_REVIEW_AUDIT_OUT = BRIDGE_DIR / "architecture_review_audit.json"
ARCHITECTURE_REVIEW_RECOMMENDATIONS_OUT = BRIDGE_DIR / "architecture_review_recommendations.json"

ARCHITECTURE_REVIEW_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "architecture_review_audit_v1.schema.json"
ARCHITECTURE_REVIEW_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "architecture_review_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "architecture_evolution_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class ArchitectureEvolutionInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class ArchitectureEvolutionDecision:
    target_id: str
    target_type: str
    architecture_status: str
    coherence_score: float
    risk_score: float
    architecture_context: str
    efficiency_context: str
    governance_context: str
    safety_context: str
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
        "architecture-watch": "watch",
        "efficiency-improvement-opportunity": "watch",
        "governance-risk": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise ArchitectureEvolutionInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise ArchitectureEvolutionInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise ArchitectureEvolutionInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise ArchitectureEvolutionInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise ArchitectureEvolutionInputError(
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
        return "fixture", "Inputs are fixture architecture-evolution artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: architecture-evolution inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    efficiency_rows: dict[str, dict[str, Any]],
    governance_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> ArchitectureEvolutionDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "architecture-context")

    architecture_fitness = _clamp01(float(row.get("architectureFitness", 0.5)))
    evolution_pressure = _clamp01(float(row.get("evolutionPressure", 0.5)))

    efficiency = efficiency_rows.get(target_id, {})
    efficiency_gap = _clamp01(float(efficiency.get("efficiencyGap", 0.5)))
    optimization_readiness = _clamp01(float(efficiency.get("optimizationReadiness", 0.5)))

    governance = governance_rows.get(target_id, {})
    governance_risk = _clamp01(float(governance.get("governanceRisk", 0.5)))
    constraint_conflict = _clamp01(float(governance.get("constraintConflict", 0.5)))

    gate = gate_rows.get(target_id, {})
    structural_change_request = bool(gate.get("structuralChangeRequest", False))
    human_approval_present = bool(gate.get("humanApprovalPresent", False))
    autonomous_change_risk = _clamp01(float(gate.get("autonomousChangeRisk", 0.4)))

    coherence = _clamp01(
        0.20 * architecture_fitness
        + 0.16 * (1.0 - efficiency_gap)
        + 0.16 * optimization_readiness
        + 0.16 * (1.0 - governance_risk)
        + 0.16 * (1.0 - constraint_conflict)
        + 0.16 * (1.0 - evolution_pressure)
    )
    risk = _clamp01(
        0.18 * governance_risk
        + 0.18 * constraint_conflict
        + 0.16 * autonomous_change_risk
        + 0.16 * evolution_pressure
        + 0.16 * (1.0 - architecture_fitness)
        + 0.16 * system_risk
    )

    if structural_change_request and not human_approval_present:
        status = "require-human-review"
        rule = "human-approval-required-for-structural-change"
    elif governance_risk >= 0.70 or constraint_conflict >= 0.70:
        status = "governance-risk"
        rule = "governance-risk-elevation"
    elif efficiency_gap >= 0.62 and optimization_readiness >= 0.60:
        status = "efficiency-improvement-opportunity"
        rule = "bounded-efficiency-improvement"
    else:
        status = "architecture-watch"
        rule = "architecture-watch-stability"

    architecture_context = (
        f"architectureFitness={architecture_fitness:.3f}, evolutionPressure={evolution_pressure:.3f}; "
        "architecture evolution remains bounded and reviewable."
    )
    efficiency_context = (
        f"efficiencyGap={efficiency_gap:.3f}, optimizationReadiness={optimization_readiness:.3f}; "
        "efficiency improvements are recommendations, not autonomous rewrites."
    )
    governance_context = (
        f"governanceRisk={governance_risk:.3f}, constraintConflict={constraint_conflict:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "governance constraints dominate optimization pressure."
    )
    safety_context = (
        f"structuralChangeRequest={str(structural_change_request).lower()}, humanApprovalPresent={str(human_approval_present).lower()}, autonomousChangeRisk={autonomous_change_risk:.3f}; "
        "structural changes require explicit human approval."
    )
    explanation = (
        f"Architecture-evolution guidance is bounded governance guidance only. targetId={target_id}, "
        f"architectureStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return ArchitectureEvolutionDecision(
        target_id=target_id,
        target_type=target_type,
        architecture_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        architecture_context=architecture_context,
        efficiency_context=efficiency_context,
        governance_context=governance_context,
        safety_context=safety_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: ArchitectureEvolutionDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "architectureStatus": d.architecture_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "architectureContext": d.architecture_context,
        "efficiencyContext": d.efficiency_context,
        "governanceContext": d.governance_context,
        "safetyContext": d.safety_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    evolution_map = _load_required_artifact(
        ARCHITECTURE_EVOLUTION_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "architecture_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    efficiency_report = _load_required_artifact(
        ARCHITECTURE_EFFICIENCY_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "efficiency_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    governance_report = _load_required_artifact(
        ARCHITECTURE_GOVERNANCE_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "governance_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    change_gate = _load_required_artifact(
        ARCHITECTURE_CHANGE_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "change_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    meta = _load_json(META_COGNITION_AUDIT_PATH)
    value = _load_json(VALUE_ALIGNMENT_AUDIT_PATH)
    forecast = _load_json(SYSTEM_FORECAST_AUDIT_PATH)
    responsibility = _load_json(RESPONSIBILITY_AUDIT_PATH)

    meta_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(meta, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    value_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(value, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    forecast_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(forecast, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    responsibility_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(responsibility, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.25 * meta_risk + 0.25 * value_risk + 0.25 * forecast_risk + 0.25 * responsibility_risk)

    efficiency_rows = {str(r.get("targetId")): r for r in _parse_rows(efficiency_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    governance_rows = {str(r.get("targetId")): r for r in _parse_rows(governance_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(change_gate.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            efficiency_rows=efficiency_rows,
            governance_rows=governance_rows,
            gate_rows=gate_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(evolution_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [evolution_map, efficiency_report, governance_report, change_gate]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(evolution_map.payload, efficiency_report.payload, governance_report.payload, change_gate.payload)

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
        "meta-cognition + value-alignment + system-forecast + responsibility state -> architecture-evolution synthesis -> "
        "Sophia architecture-review audit -> Publisher bounded governance overlays -> human/community review"
    )
    caution = (
        "Architecture-review recommendations are bounded governance guidance only and do not autonomously modify system structure "
        "without explicit human approval."
    )

    audit_payload = {
        "schema": "architecture_review_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "architecture_review_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(ARCHITECTURE_REVIEW_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(ARCHITECTURE_REVIEW_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia architecture-evolution state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    ARCHITECTURE_REVIEW_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    ARCHITECTURE_REVIEW_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {ARCHITECTURE_REVIEW_AUDIT_OUT}")
    print(f"Wrote {ARCHITECTURE_REVIEW_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
