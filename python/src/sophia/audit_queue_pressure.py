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

QUEUE_PRESSURE_MAP_PATH = BRIDGE_DIR / "queue_pressure_map.json"
QUEUE_PRESSURE_SUMMARY_PATH = BRIDGE_DIR / "queue_pressure_summary.json"
REVIEW_LOAD_DISTRIBUTION_PATH = BRIDGE_DIR / "review_load_distribution.json"
GOODHART_RISK_REPORT_PATH = BRIDGE_DIR / "goodhart_risk_report.json"

INSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "institutional_audit.json"
INSTITUTIONAL_RECOMMENDATIONS_PATH = BRIDGE_DIR / "institutional_recommendations.json"
GOVERNANCE_AUDIT_PATH = BRIDGE_DIR / "governance_audit.json"
REVIEWER_BEHAVIOR_AUDIT_PATH = BRIDGE_DIR / "reviewer_behavior_audit.json"
SCENARIO_AUDIT_PATH = BRIDGE_DIR / "scenario_audit.json"
PRECEDENT_AUDIT_PATH = BRIDGE_DIR / "precedent_audit.json"
CONSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "constitutional_audit.json"

LOAD_SHEDDING_AUDIT_OUT = BRIDGE_DIR / "load_shedding_audit.json"
LOAD_SHEDDING_RECOMMENDATIONS_OUT = BRIDGE_DIR / "load_shedding_recommendations.json"

LOAD_SHEDDING_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "load_shedding_audit_v1.schema.json"
LOAD_SHEDDING_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "load_shedding_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "queue_pressure_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = (
    "schemaVersion",
    "producerRepo",
    "producerModule",
    "producerCommit",
    "generatedAt",
)


class QueuePressureInputError(RuntimeError):
    """Raised for fail-closed queue pressure input errors."""


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class LoadSheddingDecision:
    target_id: str
    target_type: str
    operational_status: str
    preparedness_recommendation: str
    coherence_score: float
    risk_score: float
    fatigue_context: str
    backlog_context: str
    goodhart_context: str
    dominance_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _safe_mean(values: list[float], default: float = 0.0) -> float:
    return sum(values) / len(values) if values else default


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise QueuePressureInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")

    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise QueuePressureInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )

    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise QueuePressureInputError(
            f"Unexpected producerRepo in {path}: {producer_repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(
    canonical_path: Path,
    *,
    compatibility_paths: tuple[Path, ...],
    allow_compatibility_names: bool,
) -> LoadedArtifact:
    if canonical_path.exists():
        payload = _load_json(canonical_path)
        _validate_provenance(payload, path=canonical_path)
        return LoadedArtifact(canonical_path, payload, "canonical")

    available = [path for path in compatibility_paths if path.exists()]
    if not available:
        raise QueuePressureInputError(f"Missing required canonical artifact: {canonical_path}")
    if not allow_compatibility_names:
        raise QueuePressureInputError(
            f"Canonical artifact missing ({canonical_path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in available)}"
        )

    payload = _load_json(available[0])
    _validate_provenance(payload, path=available[0])
    return LoadedArtifact(available[0], payload, "compatibility")


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for doc in docs:
        ts = doc.get("generatedAt")
        if isinstance(ts, str) and ts:
            return ts
        ts_legacy = doc.get("created_at")
        if isinstance(ts_legacy, str) and ts_legacy:
            return ts_legacy
    return "1970-01-01T00:00:00Z"


def _classify_mode(artifacts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in artifacts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture queue-pressure artifacts; results are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: queue-pressure inputs combine live and fixture producers; verify before operational action."


def _status_to_action(status: str) -> str:
    return {
        "healthy": "docket",
        "monitor": "watch",
        "overloaded": "watch",
        "stalled": "suppress",
        "gaming-risk": "watch",
        "capture-risk": "suppress",
    }[status]


def _recommendation_for_status(status: str) -> str:
    return {
        "healthy": "continue",
        "monitor": "reprioritize",
        "overloaded": "archive-low-priority",
        "stalled": "freeze-intake",
        "gaming-risk": "broaden-review",
        "capture-risk": "require-human-review",
    }[status]


def _parse_rows(payload: dict[str, Any], key: str) -> list[dict[str, Any]]:
    value = payload.get(key)
    return [r for r in value if isinstance(r, dict)] if isinstance(value, list) else []


def evaluate_target(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    load_rows: dict[str, dict[str, Any]],
    goodhart_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> LoadSheddingDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "queue")

    backlog_score = _clamp01(float(row.get("backlogScore", summary.get("meanBacklogScore", 0.5))))
    staleness_score = _clamp01(float(row.get("stalenessScore", summary.get("meanStalenessScore", 0.5))))

    load = load_rows.get(target_id, {})
    fatigue_score = _clamp01(float(load.get("reviewFatigueScore", summary.get("meanReviewFatigueScore", 0.45))))
    dominance_score = _clamp01(float(load.get("dominanceScore", summary.get("meanDominanceScore", 0.35))))

    goodhart = goodhart_rows.get(target_id, {})
    gaming_score = _clamp01(float(goodhart.get("gamingRiskScore", summary.get("meanGamingRiskScore", 0.35))))
    hollow_score = _clamp01(float(goodhart.get("hollowPerformanceScore", summary.get("meanHollowPerformanceScore", 0.3))))

    coherence = _clamp01(0.35 * (1.0 - backlog_score) + 0.25 * (1.0 - fatigue_score) + 0.20 * (1.0 - gaming_score) + 0.20 * (1.0 - dominance_score))
    risk = _clamp01(0.25 * backlog_score + 0.20 * staleness_score + 0.20 * fatigue_score + 0.20 * gaming_score + 0.15 * max(dominance_score, system_risk))

    if dominance_score >= 0.75 and gaming_score >= 0.65:
        status = "capture-risk"
        rule = "anti-capture-under-dominance-and-gaming"
    elif gaming_score >= 0.62 or hollow_score >= 0.70:
        status = "gaming-risk"
        rule = "anti-goodhart-broaden-review"
    elif staleness_score >= 0.78:
        status = "stalled"
        rule = "stalled-review-freeze-intake"
    elif backlog_score >= 0.72 or fatigue_score >= 0.72:
        status = "overloaded"
        rule = "load-shed-when-overloaded"
    elif risk >= 0.45:
        status = "monitor"
        rule = "monitor-queue-pressure"
    else:
        status = "healthy"
        rule = "continue-bounded-review"

    recommendation = _recommendation_for_status(status)
    fatigue_context = f"reviewFatigueScore={fatigue_score:.3f}; delay-driven fatigue can reduce review legitimacy."
    backlog_context = f"backlogScore={backlog_score:.3f}, stalenessScore={staleness_score:.3f}; queue overload is treated as governance signal."
    goodhart_context = f"gamingRiskScore={gaming_score:.3f}, hollowPerformanceScore={hollow_score:.3f}; metric performance is not integrity."
    dominance_context = f"dominanceScore={dominance_score:.3f}, systemRisk={system_risk:.3f}; persistent delay can become structural capture."

    explanation = (
        f"Operational hygiene recommendation is bounded and auditable. targetId={target_id}, "
        f"status={status}, recommendation={recommendation}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return LoadSheddingDecision(
        target_id=target_id,
        target_type=target_type,
        operational_status=status,
        preparedness_recommendation=recommendation,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        fatigue_context=fatigue_context,
        backlog_context=backlog_context,
        goodhart_context=goodhart_context,
        dominance_context=dominance_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(decision: LoadSheddingDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "operationalStatus": decision.operational_status,
        "preparednessRecommendation": decision.preparedness_recommendation,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "fatigueContext": decision.fatigue_context,
        "backlogContext": decision.backlog_context,
        "goodhartContext": decision.goodhart_context,
        "dominanceContext": decision.dominance_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    queue_map = _load_required_artifact(
        QUEUE_PRESSURE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "queue_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    queue_summary = _load_required_artifact(
        QUEUE_PRESSURE_SUMMARY_PATH,
        compatibility_paths=(BRIDGE_DIR / "queue_summary.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    review_dist = _load_required_artifact(
        REVIEW_LOAD_DISTRIBUTION_PATH,
        compatibility_paths=(BRIDGE_DIR / "review_load.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    goodhart_report = _load_required_artifact(
        GOODHART_RISK_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "metric_gaming_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    institutional_audit = _load_json(INSTITUTIONAL_AUDIT_PATH)
    institutional_recommendations = _load_json(INSTITUTIONAL_RECOMMENDATIONS_PATH)
    governance_audit = _load_json(GOVERNANCE_AUDIT_PATH)
    reviewer_behavior_audit = _load_json(REVIEWER_BEHAVIOR_AUDIT_PATH)
    scenario_audit = _load_json(SCENARIO_AUDIT_PATH)
    precedent_audit = _load_json(PRECEDENT_AUDIT_PATH)
    constitutional_audit = _load_json(CONSTITUTIONAL_AUDIT_PATH)

    queue_rows = _parse_rows(queue_map.payload, "targets")
    review_rows = {str(r.get("targetId")): r for r in _parse_rows(review_dist.payload, "targets") if isinstance(r.get("targetId"), str)}
    goodhart_rows = {str(r.get("targetId")): r for r in _parse_rows(goodhart_report.payload, "targets") if isinstance(r.get("targetId"), str)}

    governance_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(governance_audit, "audits") if isinstance(r.get("riskScore"), (int, float))], 0.35)
    reviewer_override = _safe_mean([float(r.get("overrideRisk")) for r in _parse_rows(reviewer_behavior_audit, "reviewers") if isinstance(r.get("overrideRisk"), (int, float))], 0.35)
    scenario_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(scenario_audit, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    precedent_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(precedent_audit, "records") if isinstance(r.get("riskScore"), (int, float))], 0.35)
    constitutional_risk = _safe_mean([float(r.get("governanceRisk")) for r in _parse_rows(constitutional_audit, "evaluations") if isinstance(r.get("governanceRisk"), (int, float))], 0.35)
    institutional_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(institutional_audit, "records") if isinstance(r.get("riskScore"), (int, float))], 0.4)

    system_risk = _clamp01(
        0.20 * governance_risk
        + 0.15 * reviewer_override
        + 0.15 * scenario_risk
        + 0.15 * precedent_risk
        + 0.15 * constitutional_risk
        + 0.20 * institutional_risk
    )

    decisions = [
        evaluate_target(
            row,
            summary=queue_summary.payload,
            load_rows=review_rows,
            goodhart_rows=goodhart_rows,
            system_risk=system_risk,
        )
        for row in queue_rows
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    created_at = _resolve_created_at(queue_map.payload, queue_summary.payload, review_dist.payload, goodhart_report.payload)
    loaded_inputs = [queue_map, queue_summary, review_dist, goodhart_report]
    input_mode, mode_warning = _classify_mode(loaded_inputs)

    metadata = {
        "inputMode": input_mode,
        "inputModeWarning": mode_warning,
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
            for a in loaded_inputs
        ],
        "upstreamArtifacts": {
            "institutionalAuditSchema": institutional_audit.get("schema"),
            "institutionalRecommendationsSchema": institutional_recommendations.get("schema"),
            "governanceAuditSchema": governance_audit.get("schema"),
            "reviewerBehaviorAuditSchema": reviewer_behavior_audit.get("schema"),
            "scenarioAuditSchema": scenario_audit.get("schema"),
            "precedentAuditSchema": precedent_audit.get("schema"),
            "constitutionalAuditSchema": constitutional_audit.get("schema"),
        },
    }

    phaselock = (
        "queue / review / watchlist state -> CoherenceLattice operational pressure formalization -> "
        "Sophia load-shedding and anti-Goodhart audit -> Publisher queue-health and backlog overlays -> "
        "human/community operational review"
    )

    caution = (
        "Load-shedding recommendations are bounded operational guidance only and do not automatically delete, suppress, "
        "or canonically mutate queued material."
    )

    audit_payload = {
        "schema": "load_shedding_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }

    recommendations_payload = {
        "schema": "load_shedding_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(LOAD_SHEDDING_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(LOAD_SHEDDING_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia queue pressure and load-shedding audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    LOAD_SHEDDING_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    LOAD_SHEDDING_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {LOAD_SHEDDING_AUDIT_OUT}")
    print(f"Wrote {LOAD_SHEDDING_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
