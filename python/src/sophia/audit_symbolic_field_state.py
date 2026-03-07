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

SYMBOLIC_FIELD_STATE_PATH = BRIDGE_DIR / "symbolic_field_state.json"
SYMBOLIC_FIELD_SUMMARY_PATH = BRIDGE_DIR / "symbolic_field_summary.json"
REGIME_TRANSITION_REPORT_PATH = BRIDGE_DIR / "regime_transition_report.json"
EARLY_WARNING_SIGNAL_MAP_PATH = BRIDGE_DIR / "early_warning_signal_map.json"

INSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "institutional_audit.json"
LOAD_SHEDDING_AUDIT_PATH = BRIDGE_DIR / "load_shedding_audit.json"
TRIAGE_AUDIT_PATH = BRIDGE_DIR / "triage_audit.json"
CLOSURE_AUDIT_PATH = BRIDGE_DIR / "closure_audit.json"
SCENARIO_AUDIT_PATH = BRIDGE_DIR / "scenario_audit.json"
PRECEDENT_AUDIT_PATH = BRIDGE_DIR / "precedent_audit.json"

SYMBOLIC_FIELD_AUDIT_OUT = BRIDGE_DIR / "symbolic_field_audit.json"
SYMBOLIC_FIELD_RECOMMENDATIONS_OUT = BRIDGE_DIR / "symbolic_field_recommendations.json"

SYMBOLIC_FIELD_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "symbolic_field_audit_v1.schema.json"
SYMBOLIC_FIELD_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "symbolic_field_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "symbolic_field_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class SymbolicFieldInputError(RuntimeError):
    """Raised for fail-closed symbolic field input errors."""


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class SymbolicDecision:
    target_id: str
    target_type: str
    field_status: str
    coherence_score: float
    risk_score: float
    regime_context: str
    closure_context: str
    priority_context: str
    institutional_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_rows(payload: dict[str, Any], key: str) -> list[dict[str, Any]]:
    v = payload.get(key)
    return [r for r in v if isinstance(r, dict)] if isinstance(v, list) else []


def _safe_mean(vals: list[float], default: float = 0.0) -> float:
    return sum(vals) / len(vals) if vals else default


def _clamp01(v: float) -> float:
    return max(0.0, min(1.0, float(v)))


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [f for f in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(f), str) or not payload.get(f)]
    if missing:
        raise SymbolicFieldInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise SymbolicFieldInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise SymbolicFieldInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        p = _load_json(path)
        _validate_provenance(p, path=path)
        return LoadedArtifact(path, p, "canonical")
    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise SymbolicFieldInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise SymbolicFieldInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )
    p = _load_json(found[0])
    _validate_provenance(p, path=found[0])
    return LoadedArtifact(found[0], p, "compatibility")


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for d in docs:
        for key in ("generatedAt", "created_at"):
            ts = d.get(key)
            if isinstance(ts, str) and ts:
                return ts
    return "1970-01-01T00:00:00Z"


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture symbolic-field artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: symbolic-field inputs combine live and fixture producers; verify before action."


def _status_to_action(status: str) -> str:
    return {
        "stable": "docket",
        "monitor": "watch",
        "caution": "watch",
        "escalate": "docket",
        "freeze-dependent-pathways": "suppress",
        "require-human-review": "docket",
    }[status]


def evaluate_target(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    regime_rows: dict[str, dict[str, Any]],
    warning_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> SymbolicDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "symbolic-target")

    symbolic_coherence = _clamp01(float(row.get("symbolicCoherence", summary.get("meanSymbolicCoherence", 0.5))))
    ambiguity = _clamp01(float(row.get("ambiguityScore", summary.get("meanAmbiguityScore", 0.45))))

    regime = regime_rows.get(target_id, {})
    transition_risk = _clamp01(float(regime.get("transitionRisk", summary.get("meanTransitionRisk", 0.45))))
    volatility = _clamp01(float(regime.get("volatilityScore", summary.get("meanVolatilityScore", 0.45))))

    warning = warning_rows.get(target_id, {})
    early_warning = _clamp01(float(warning.get("earlyWarningScore", summary.get("meanEarlyWarningScore", 0.4))))
    warning_confidence = _clamp01(float(warning.get("warningConfidence", summary.get("meanWarningConfidence", 0.5))))

    coherence = _clamp01(0.35 * symbolic_coherence + 0.20 * (1.0 - ambiguity) + 0.20 * (1.0 - transition_risk) + 0.25 * warning_confidence)
    risk = _clamp01(0.25 * transition_risk + 0.20 * volatility + 0.20 * early_warning + 0.20 * ambiguity + 0.15 * system_risk)

    if early_warning >= 0.82 and warning_confidence >= 0.66:
        status = "require-human-review"
        rule = "evidence-bound-early-warning-override"
    elif transition_risk >= 0.78 and risk >= 0.68:
        status = "freeze-dependent-pathways"
        rule = "freeze-under-regime-instability"
    elif early_warning >= 0.66 or volatility >= 0.70:
        status = "escalate"
        rule = "escalate-early-warning-regime-shift"
    elif risk >= 0.54:
        status = "caution"
        rule = "caution-under-symbolic-ambiguity"
    elif risk >= 0.38:
        status = "monitor"
        rule = "monitor-symbolic-field"
    else:
        status = "stable"
        rule = "stable-symbolic-field"

    regime_context = f"transitionRisk={transition_risk:.3f}, volatilityScore={volatility:.3f}, earlyWarningScore={early_warning:.3f}; early-warning signals are evidence-bound."
    closure_context = "Closure linkage is interpretive only; processed outcomes are not assumed resolved without durability evidence."
    priority_context = "Priority linkage is advisory only; architecture-sensitive reasoning should remain auditable and contestable."
    institutional_context = f"symbolicCoherence={symbolic_coherence:.3f}, ambiguityScore={ambiguity:.3f}, systemRisk={system_risk:.3f}; field interpretation must remain cautious."

    explanation = (
        f"Symbolic field recommendation is bounded interpretive guidance only. targetId={target_id}, "
        f"fieldStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return SymbolicDecision(
        target_id=target_id,
        target_type=target_type,
        field_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        regime_context=regime_context,
        closure_context=closure_context,
        priority_context=priority_context,
        institutional_context=institutional_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: SymbolicDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "fieldStatus": d.field_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "regimeContext": d.regime_context,
        "closureContext": d.closure_context,
        "priorityContext": d.priority_context,
        "institutionalContext": d.institutional_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    field_state = _load_required_artifact(
        SYMBOLIC_FIELD_STATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "symbolic_state.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    field_summary = _load_required_artifact(
        SYMBOLIC_FIELD_SUMMARY_PATH,
        compatibility_paths=(BRIDGE_DIR / "symbolic_summary.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    regime_report = _load_required_artifact(
        REGIME_TRANSITION_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "regime_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    warning_map = _load_required_artifact(
        EARLY_WARNING_SIGNAL_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "early_warning_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    institutional = _load_json(INSTITUTIONAL_AUDIT_PATH)
    load_shedding = _load_json(LOAD_SHEDDING_AUDIT_PATH)
    triage = _load_json(TRIAGE_AUDIT_PATH)
    closure = _load_json(CLOSURE_AUDIT_PATH)
    scenario = _load_json(SCENARIO_AUDIT_PATH)
    precedent = _load_json(PRECEDENT_AUDIT_PATH)

    institutional_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(institutional, "records") if isinstance(r.get("riskScore"), (int, float))], 0.4)
    load_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(load_shedding, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    triage_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(triage, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    closure_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(closure, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    scenario_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(scenario, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    precedent_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(precedent, "records") if isinstance(r.get("riskScore"), (int, float))], 0.35)

    system_risk = _clamp01(0.18 * institutional_risk + 0.16 * load_risk + 0.16 * triage_risk + 0.16 * closure_risk + 0.18 * scenario_risk + 0.16 * precedent_risk)

    regime_rows = {str(r.get("targetId")): r for r in _parse_rows(regime_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    warning_rows = {str(r.get("targetId")): r for r in _parse_rows(warning_map.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            summary=field_summary.payload,
            regime_rows=regime_rows,
            warning_rows=warning_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(field_state.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [field_state, field_summary, regime_report, warning_map]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(field_state.payload, field_summary.payload, regime_report.payload, warning_map.payload)

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
        "symbolic / regime / warning state -> CoherenceLattice symbolic field and early-warning formalization -> "
        "Sophia symbolic field audit -> Publisher symbolic overlays -> human/community review"
    )
    caution = (
        "Symbolic field recommendations are bounded interpretive guidance only and do not automatically mutate memory, "
        "close cases, or reconfigure triadic governance."
    )

    audit_payload = {
        "schema": "symbolic_field_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "symbolic_field_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(SYMBOLIC_FIELD_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(SYMBOLIC_FIELD_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia symbolic field and early-warning audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    SYMBOLIC_FIELD_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    SYMBOLIC_FIELD_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {SYMBOLIC_FIELD_AUDIT_OUT}")
    print(f"Wrote {SYMBOLIC_FIELD_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
