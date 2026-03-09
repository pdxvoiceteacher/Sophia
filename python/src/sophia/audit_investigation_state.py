from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"

INVESTIGATION_PLAN_MAP_PATH = BRIDGE_DIR / "investigation_plan_map.json"
INVESTIGATION_STAGE_MAP_PATH = BRIDGE_DIR / "investigation_stage_map.json"
EVIDENCE_DEPENDENCY_GRAPH_PATH = BRIDGE_DIR / "evidence_dependency_graph.json"
INVESTIGATION_PROGRESS_REPORT_PATH = BRIDGE_DIR / "investigation_progress_report.json"

VERIFICATION_AUDIT_PATH = BRIDGE_DIR / "verification_audit.json"
ENVIRONMENT_AUDIT_PATH = BRIDGE_DIR / "environment_audit.json"
SYMBOLIC_FIELD_AUDIT_PATH = BRIDGE_DIR / "symbolic_field_audit.json"

INVESTIGATION_AUDIT_OUT = BRIDGE_DIR / "investigation_audit.json"
INVESTIGATION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "investigation_recommendations.json"


@dataclass(slots=True)
class InvestigationDecision:
    investigation_id: str
    investigation_status: str
    coherence_score: float
    risk_score: float
    stage_context: str
    dependency_context: str
    progress_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_rows(payload: dict[str, Any], keys: tuple[str, ...] = ("records", "targets", "investigations", "nodes")) -> list[dict[str, Any]]:
    for key in keys:
        value = payload.get(key)
        if isinstance(value, list):
            return [row for row in value if isinstance(row, dict)]
    return []


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _safe_mean(values: list[float], default: float = 0.0) -> float:
    return sum(values) / len(values) if values else default


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for doc in docs:
        for key in ("generatedAt", "created_at"):
            value = doc.get(key)
            if isinstance(value, str) and value:
                return value
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str) -> str:
    return {
        "plan-ready": "docket",
        "verify-stage": "docket",
        "blocked": "suppress",
        "contradiction-risk": "watch",
        "require-human-review": "docket",
    }[status]


def _extract_id(row: dict[str, Any]) -> str:
    for key in ("investigationId", "targetId", "nodeId", "id"):
        value = row.get(key)
        if isinstance(value, str) and value:
            return value
    return "investigation:unknown"


def _parse_float(row: dict[str, Any], *keys: str, default: float) -> float:
    for key in keys:
        value = row.get(key)
        if isinstance(value, (int, float)):
            return float(value)
    return default


def _parse_int(row: dict[str, Any], *keys: str, default: int) -> int:
    for key in keys:
        value = row.get(key)
        if isinstance(value, int):
            return value
        if isinstance(value, float):
            return int(value)
    return default


def evaluate_investigation(
    row: dict[str, Any],
    *,
    stage_rows: dict[str, dict[str, Any]],
    dependency_rows: dict[str, dict[str, Any]],
    progress_rows: dict[str, dict[str, Any]],
    verification_risk: float,
    environment_risk: float,
    symbolic_risk: float,
) -> InvestigationDecision:
    investigation_id = _extract_id(row)
    stage_row = stage_rows.get(investigation_id, {})
    dependency_row = dependency_rows.get(investigation_id, {})
    progress_row = progress_rows.get(investigation_id, {})

    plan_readiness = _clamp01(_parse_float(row, "planReadiness", "planScore", "readinessScore", default=0.5))
    stage_readiness = _clamp01(_parse_float(stage_row, "stageReadiness", "readinessScore", default=0.5))

    unresolved_dependencies = _parse_int(dependency_row, "unresolvedDependencies", "blockedByCount", default=0)
    dependency_risk = _clamp01(_parse_float(dependency_row, "dependencyRisk", "blockingRisk", default=0.35))

    completion = _clamp01(_parse_float(progress_row, "completionRatio", "progressRatio", "completionScore", default=0.45))
    contradiction_score = _clamp01(_parse_float(progress_row, "contradictionScore", "conflictScore", default=0.35))

    current_stage = str(stage_row.get("currentStage") or stage_row.get("stage") or "plan").strip().lower()
    stage_status = str(stage_row.get("stageStatus") or "").strip().lower()
    verify_stage_signal = current_stage in {"verify", "verification", "audit", "review"} or stage_status == "verify-stage"

    coherence = _clamp01(0.34 * plan_readiness + 0.24 * stage_readiness + 0.22 * completion + 0.20 * (1.0 - contradiction_score))
    risk = _clamp01(
        0.26 * dependency_risk
        + 0.23 * contradiction_score
        + 0.18 * verification_risk
        + 0.17 * environment_risk
        + 0.16 * symbolic_risk
    )

    if contradiction_score >= 0.80 and (verification_risk >= 0.62 or symbolic_risk >= 0.62):
        status = "require-human-review"
        rule = "stacked-contradiction-review-gate"
    elif unresolved_dependencies > 0 and (dependency_risk >= 0.62 or completion <= 0.40):
        status = "blocked"
        rule = "dependency-blocking-gate"
    elif contradiction_score >= 0.60 or risk >= 0.62:
        status = "contradiction-risk"
        rule = "contradiction-escalation-monitor"
    elif verify_stage_signal or completion >= 0.55:
        status = "verify-stage"
        rule = "verification-stage-entry"
    else:
        status = "plan-ready"
        rule = "plan-readiness-path"

    stage_context = (
        f"planReadiness={plan_readiness:.3f}, stageReadiness={stage_readiness:.3f}, "
        f"currentStage={current_stage}, stageSignal={'verify' if verify_stage_signal else 'plan'}"
    )
    dependency_context = (
        f"unresolvedDependencies={unresolved_dependencies}, dependencyRisk={dependency_risk:.3f}, "
        "dependency graph is advisory and must remain auditable"
    )
    progress_context = (
        f"completionRatio={completion:.3f}, contradictionScore={contradiction_score:.3f}, "
        f"verificationRisk={verification_risk:.3f}, environmentRisk={environment_risk:.3f}, symbolicRisk={symbolic_risk:.3f}"
    )

    explanation = (
        "Investigation recommendation is bounded process guidance only. "
        f"investigationId={investigation_id}, investigationStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return InvestigationDecision(
        investigation_id=investigation_id,
        investigation_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        stage_context=stage_context,
        dependency_context=dependency_context,
        progress_context=progress_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(decision: InvestigationDecision) -> dict[str, Any]:
    return {
        "investigationId": decision.investigation_id,
        "investigationStatus": decision.investigation_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "stageContext": decision.stage_context,
        "dependencyContext": decision.dependency_context,
        "progressContext": decision.progress_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    plan_map = _load_json(INVESTIGATION_PLAN_MAP_PATH)
    stage_map = _load_json(INVESTIGATION_STAGE_MAP_PATH)
    dependency_graph = _load_json(EVIDENCE_DEPENDENCY_GRAPH_PATH)
    progress_report = _load_json(INVESTIGATION_PROGRESS_REPORT_PATH)

    verification_audit = _load_json(VERIFICATION_AUDIT_PATH)
    environment_audit = _load_json(ENVIRONMENT_AUDIT_PATH)
    symbolic_field_audit = _load_json(SYMBOLIC_FIELD_AUDIT_PATH)

    verification_risk = _safe_mean(
        [float(row.get("riskScore")) for row in _parse_rows(verification_audit) if isinstance(row.get("riskScore"), (int, float))],
        default=0.45,
    )
    environment_risk = _safe_mean(
        [float(row.get("riskScore")) for row in _parse_rows(environment_audit) if isinstance(row.get("riskScore"), (int, float))],
        default=0.45,
    )
    symbolic_risk = _safe_mean(
        [float(row.get("riskScore")) for row in _parse_rows(symbolic_field_audit) if isinstance(row.get("riskScore"), (int, float))],
        default=0.45,
    )

    stage_rows = {_extract_id(row): row for row in _parse_rows(stage_map)}
    dependency_rows = {_extract_id(row): row for row in _parse_rows(dependency_graph)}
    progress_rows = {_extract_id(row): row for row in _parse_rows(progress_report)}

    decisions = [
        evaluate_investigation(
            row,
            stage_rows=stage_rows,
            dependency_rows=dependency_rows,
            progress_rows=progress_rows,
            verification_risk=verification_risk,
            environment_risk=environment_risk,
            symbolic_risk=symbolic_risk,
        )
        for row in _parse_rows(plan_map)
    ]
    decisions = sorted(decisions, key=lambda item: item.investigation_id)

    created_at = _resolve_created_at(
        plan_map,
        stage_map,
        dependency_graph,
        progress_report,
        verification_audit,
        environment_audit,
        symbolic_field_audit,
    )

    metadata = {
        "systemRisk": round(_clamp01(0.36 * verification_risk + 0.32 * environment_risk + 0.32 * symbolic_risk), 6),
        "inputs": [
            "bridge/investigation_plan_map.json",
            "bridge/investigation_stage_map.json",
            "bridge/evidence_dependency_graph.json",
            "bridge/investigation_progress_report.json",
            "bridge/verification_audit.json",
            "bridge/environment_audit.json",
            "bridge/symbolic_field_audit.json",
        ],
    }

    phaselock = (
        "investigation planning and stage control -> evidence dependency evaluation -> "
        "cross-audit risk synthesis -> Sophia investigation audit -> bounded recommendation handoff"
    )
    caution = (
        "Investigation recommendations are process-governance guidance only; they do not constitute factual findings or automated adjudication."
    )

    audit_payload = {
        "schema": "investigation_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(decision) for decision in decisions],
    }
    recommendations_payload = {
        "schema": "investigation_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(decision) for decision in decisions],
    }

    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia investigation-state audit")
    parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs()
    INVESTIGATION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    INVESTIGATION_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"Wrote {INVESTIGATION_AUDIT_OUT}")
    print(f"Wrote {INVESTIGATION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
