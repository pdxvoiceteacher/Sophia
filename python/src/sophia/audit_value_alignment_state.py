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

VALUE_ALIGNMENT_MAP_PATH = BRIDGE_DIR / "value_alignment_map.json"
MORAL_CONSEQUENCE_REPORT_PATH = BRIDGE_DIR / "moral_consequence_report.json"
COMMUNITY_PRIORITY_SIGNAL_PATH = BRIDGE_DIR / "community_priority_signal.json"
VALUE_OVERRIDE_BOUNDARY_GATE_PATH = BRIDGE_DIR / "value_override_boundary_gate.json"

CURIOSITY_AUDIT_PATH = BRIDGE_DIR / "curiosity_audit.json"
SYSTEM_FORECAST_AUDIT_PATH = BRIDGE_DIR / "system_forecast_audit.json"
THEORY_TRANSFER_AUDIT_PATH = BRIDGE_DIR / "theory_transfer_audit.json"
RESPONSIBILITY_AUDIT_PATH = BRIDGE_DIR / "responsibility_audit.json"

VALUE_ALIGNMENT_AUDIT_OUT = BRIDGE_DIR / "value_alignment_audit.json"
VALUE_ALIGNMENT_RECOMMENDATIONS_OUT = BRIDGE_DIR / "value_alignment_recommendations.json"

VALUE_ALIGNMENT_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "value_alignment_audit_v1.schema.json"
VALUE_ALIGNMENT_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "value_alignment_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "value_alignment_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class ValueAlignmentInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class ValueAlignmentDecision:
    target_id: str
    target_type: str
    value_status: str
    coherence_score: float
    risk_score: float
    consequence_context: str
    community_context: str
    uncertainty_context: str
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
        "priority-high": "docket",
        "priority-moderate": "watch",
        "priority-watch": "watch",
        "value-risk": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise ValueAlignmentInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise ValueAlignmentInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise ValueAlignmentInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise ValueAlignmentInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise ValueAlignmentInputError(
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
        return "fixture", "Inputs are fixture value-alignment artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: value-alignment inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    consequence_rows: dict[str, dict[str, Any]],
    community_rows: dict[str, dict[str, Any]],
    boundary_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> ValueAlignmentDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "value-context")

    knowledge_priority_signal = _clamp01(float(row.get("knowledgePrioritySignal", 0.5)))
    value_clarity = _clamp01(float(row.get("valueClarity", 0.5)))

    consequence = consequence_rows.get(target_id, {})
    consequence_salience = _clamp01(float(consequence.get("consequenceSalience", 0.5)))
    externality_risk = _clamp01(float(consequence.get("externalityRisk", 0.5)))

    community = community_rows.get(target_id, {})
    community_consensus = _clamp01(float(community.get("communityConsensus", 0.5)))
    dissent_signal = _clamp01(float(community.get("dissentSignal", 0.5)))

    boundary = boundary_rows.get(target_id, {})
    value_override_risk = _clamp01(float(boundary.get("valueOverrideRisk", 0.4)))
    ethics_replacement_risk = _clamp01(float(boundary.get("ethicsReplacementRisk", 0.4)))
    autonomous_value_override_requested = bool(boundary.get("autonomousValueOverrideRequested", False))

    governance_safety = _clamp01(1.0 - 0.5 * value_override_risk - 0.5 * ethics_replacement_risk)

    coherence = _clamp01(
        0.18 * knowledge_priority_signal
        + 0.16 * value_clarity
        + 0.16 * consequence_salience
        + 0.16 * community_consensus
        + 0.16 * governance_safety
        + 0.18 * (1.0 - dissent_signal)
    )
    risk = _clamp01(
        0.16 * externality_risk
        + 0.16 * dissent_signal
        + 0.16 * (1.0 - value_clarity)
        + 0.18 * value_override_risk
        + 0.18 * ethics_replacement_risk
        + 0.16 * system_risk
    )

    if autonomous_value_override_requested or value_override_risk >= 0.80 or ethics_replacement_risk >= 0.80:
        status = "require-human-review"
        rule = "human-authority-value-judgment-gate"
    elif externality_risk >= 0.74 or dissent_signal >= 0.74:
        status = "value-risk"
        rule = "value-risk-with-dissent-or-externality"
    elif knowledge_priority_signal >= 0.70 and consequence_salience >= 0.66 and community_consensus >= 0.60:
        status = "priority-high"
        rule = "high-priority-community-aligned"
    elif knowledge_priority_signal >= 0.58 and value_clarity >= 0.56:
        status = "priority-moderate"
        rule = "moderate-priority-bounded"
    else:
        status = "priority-watch"
        rule = "watch-priority-under-uncertainty"

    consequence_context = (
        f"consequenceSalience={consequence_salience:.3f}, externalityRisk={externality_risk:.3f}, knowledgePrioritySignal={knowledge_priority_signal:.3f}; "
        "the triad illuminates moral consequences without issuing moral verdicts."
    )
    community_context = (
        f"communityConsensus={community_consensus:.3f}, dissentSignal={dissent_signal:.3f}, valueClarity={value_clarity:.3f}; "
        "human communities retain authority over final value judgments."
    )
    uncertainty_context = (
        f"systemRisk={system_risk:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "value prioritization is bounded and remains uncertainty-disclosing."
    )
    governance_context = (
        f"valueOverrideRisk={value_override_risk:.3f}, ethicsReplacementRisk={ethics_replacement_risk:.3f}, autonomousValueOverrideRequested={str(autonomous_value_override_requested).lower()}; "
        "the system may recommend knowledge priorities, but cannot replace human ethics."
    )
    explanation = (
        f"Value-alignment guidance is bounded governance guidance only. targetId={target_id}, "
        f"valueStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return ValueAlignmentDecision(
        target_id=target_id,
        target_type=target_type,
        value_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        consequence_context=consequence_context,
        community_context=community_context,
        uncertainty_context=uncertainty_context,
        governance_context=governance_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: ValueAlignmentDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "valueStatus": d.value_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "consequenceContext": d.consequence_context,
        "communityContext": d.community_context,
        "uncertaintyContext": d.uncertainty_context,
        "governanceContext": d.governance_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    value_map = _load_required_artifact(
        VALUE_ALIGNMENT_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "alignment_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    consequence_report = _load_required_artifact(
        MORAL_CONSEQUENCE_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "consequence_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    community_signal = _load_required_artifact(
        COMMUNITY_PRIORITY_SIGNAL_PATH,
        compatibility_paths=(BRIDGE_DIR / "community_signal.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    boundary_gate = _load_required_artifact(
        VALUE_OVERRIDE_BOUNDARY_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "value_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    curiosity = _load_json(CURIOSITY_AUDIT_PATH)
    system_forecast = _load_json(SYSTEM_FORECAST_AUDIT_PATH)
    theory_transfer = _load_json(THEORY_TRANSFER_AUDIT_PATH)
    responsibility = _load_json(RESPONSIBILITY_AUDIT_PATH)

    curiosity_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(curiosity, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_forecast_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(system_forecast, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    theory_transfer_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(theory_transfer, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    responsibility_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(responsibility, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.26 * curiosity_risk + 0.24 * system_forecast_risk + 0.24 * theory_transfer_risk + 0.26 * responsibility_risk)

    consequence_rows = {str(r.get("targetId")): r for r in _parse_rows(consequence_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    community_rows = {str(r.get("targetId")): r for r in _parse_rows(community_signal.payload, "targets") if isinstance(r.get("targetId"), str)}
    boundary_rows = {str(r.get("targetId")): r for r in _parse_rows(boundary_gate.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            consequence_rows=consequence_rows,
            community_rows=community_rows,
            boundary_rows=boundary_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(value_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [value_map, consequence_report, community_signal, boundary_gate]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(value_map.payload, consequence_report.payload, community_signal.payload, boundary_gate.payload)

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
        "curiosity + system-forecast + theory-transfer + responsibility state -> value-alignment synthesis -> "
        "Sophia value-alignment audit -> Publisher bounded governance overlays -> human/community review"
    )
    caution = (
        "Value-alignment recommendations are bounded governance guidance only: the system may recommend knowledge priorities, "
        "but human communities retain authority over final value judgments."
    )

    audit_payload = {
        "schema": "value_alignment_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "value_alignment_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(VALUE_ALIGNMENT_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(VALUE_ALIGNMENT_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia value-alignment state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    VALUE_ALIGNMENT_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    VALUE_ALIGNMENT_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {VALUE_ALIGNMENT_AUDIT_OUT}")
    print(f"Wrote {VALUE_ALIGNMENT_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
