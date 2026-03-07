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

PRIORITY_STATE_MAP_PATH = BRIDGE_DIR / "priority_state_map.json"
PRIORITY_STATE_SUMMARY_PATH = BRIDGE_DIR / "priority_state_summary.json"
TRIAGE_CANDIDATE_MAP_PATH = BRIDGE_DIR / "triage_candidate_map.json"
TRIAGE_CONFLICT_REPORT_PATH = BRIDGE_DIR / "triage_conflict_report.json"

INSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "institutional_audit.json"
LOAD_SHEDDING_AUDIT_PATH = BRIDGE_DIR / "load_shedding_audit.json"
CONSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "constitutional_audit.json"
RESILIENCE_AUDIT_PATH = BRIDGE_DIR / "resilience_audit.json"
RECOVERY_AUDIT_PATH = BRIDGE_DIR / "recovery_audit.json"
SCENARIO_AUDIT_PATH = BRIDGE_DIR / "scenario_audit.json"

TRIAGE_AUDIT_OUT = BRIDGE_DIR / "triage_audit.json"
TRIAGE_RECOMMENDATIONS_OUT = BRIDGE_DIR / "triage_recommendations.json"

TRIAGE_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "triage_audit_v1.schema.json"
TRIAGE_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "triage_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "priority_state_v1"
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


class PriorityInputError(RuntimeError):
    """Raised for fail-closed priority input errors."""


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class TriageDecision:
    target_id: str
    target_type: str
    triage_status: str
    coherence_score: float
    risk_score: float
    urgency_context: str
    queue_context: str
    capture_context: str
    reversibility_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _safe_mean(values: list[float], default: float = 0.0) -> float:
    return sum(values) / len(values) if values else default


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _parse_rows(payload: dict[str, Any], key: str) -> list[dict[str, Any]]:
    value = payload.get(key)
    return [r for r in value if isinstance(r, dict)] if isinstance(value, list) else []


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise PriorityInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")

    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise PriorityInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )

    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise PriorityInputError(
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
        raise PriorityInputError(f"Missing required canonical artifact: {canonical_path}")
    if not allow_compatibility_names:
        raise PriorityInputError(
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
        ts2 = doc.get("created_at")
        if isinstance(ts2, str) and ts2:
            return ts2
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str) -> str:
    return {
        "immediate-review": "docket",
        "near-term-review": "docket",
        "monitor": "watch",
        "defer": "watch",
        "freeze-dependent-pathways": "suppress",
        "require-human-review": "docket",
    }[status]


def _classify_mode(artifacts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in artifacts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture priority artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: priority inputs combine live and fixture producers; verify before ordered review action."


def evaluate_target(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    candidate_rows: dict[str, dict[str, Any]],
    conflict_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> TriageDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "triage-target")

    baseline_priority = _clamp01(float(row.get("priorityScore", summary.get("meanPriorityScore", 0.5))))
    queue_pressure = _clamp01(float(row.get("queuePressureScore", summary.get("meanQueuePressureScore", 0.5))))

    candidate = candidate_rows.get(target_id, {})
    urgency = _clamp01(float(candidate.get("urgencyScore", summary.get("meanUrgencyScore", 0.5))))
    reversibility = _clamp01(float(candidate.get("reversibilityScore", summary.get("meanReversibilityScore", 0.5))))

    conflict = conflict_rows.get(target_id, {})
    capture = _clamp01(float(conflict.get("captureRisk", summary.get("meanCaptureRisk", 0.45))))
    dominance = _clamp01(float(conflict.get("dominanceRisk", summary.get("meanDominanceRisk", 0.4))))

    irreversibility = 1.0 - reversibility

    coherence = _clamp01(0.35 * baseline_priority + 0.20 * urgency + 0.20 * (1.0 - queue_pressure) + 0.25 * (1.0 - capture))
    risk = _clamp01(0.25 * queue_pressure + 0.20 * capture + 0.20 * dominance + 0.20 * irreversibility + 0.15 * system_risk)

    # Priority inversion handling: low-reversibility items escalate even if urgency is moderate.
    if capture >= 0.78 or dominance >= 0.80:
        status = "require-human-review"
        rule = "capture-risk-priority-override"
    elif irreversibility >= 0.80 and queue_pressure >= 0.55:
        status = "immediate-review"
        rule = "irreversibility-priority-inversion-override"
    elif queue_pressure >= 0.78 and risk >= 0.68:
        status = "freeze-dependent-pathways"
        rule = "freeze-under-triage-overload"
    elif urgency >= 0.72 and risk >= 0.54:
        status = "near-term-review"
        rule = "near-term-urgent-review"
    elif risk <= 0.38 and reversibility >= 0.68:
        status = "defer"
        rule = "defer-reversible-low-risk"
    else:
        status = "monitor"
        rule = "monitor-priority-state"

    urgency_context = f"urgencyScore={urgency:.3f}; attention is a constitutional resource and priority must remain explicit."
    queue_context = f"queuePressureScore={queue_pressure:.3f}, baselinePriority={baseline_priority:.3f}; silent prioritization is hidden power."
    capture_context = f"captureRisk={capture:.3f}, dominanceRisk={dominance:.3f}, systemRisk={system_risk:.3f}; capture risk increases triage priority."
    reversibility_context = f"reversibilityScore={reversibility:.3f}, irreversibility={irreversibility:.3f}; irreversible issues should be reviewed earlier."

    explanation = (
        f"Triage recommendation is bounded ordering guidance only. targetId={target_id}, status={status}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return TriageDecision(
        target_id=target_id,
        target_type=target_type,
        triage_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        urgency_context=urgency_context,
        queue_context=queue_context,
        capture_context=capture_context,
        reversibility_context=reversibility_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: TriageDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "triageStatus": d.triage_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "urgencyContext": d.urgency_context,
        "queueContext": d.queue_context,
        "captureContext": d.capture_context,
        "reversibilityContext": d.reversibility_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    p_map = _load_required_artifact(
        PRIORITY_STATE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "priority_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    p_summary = _load_required_artifact(
        PRIORITY_STATE_SUMMARY_PATH,
        compatibility_paths=(BRIDGE_DIR / "priority_summary.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    c_map = _load_required_artifact(
        TRIAGE_CANDIDATE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "triage_candidates.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    c_report = _load_required_artifact(
        TRIAGE_CONFLICT_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "triage_conflicts.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    institutional = _load_json(INSTITUTIONAL_AUDIT_PATH)
    load_shedding = _load_json(LOAD_SHEDDING_AUDIT_PATH)
    constitutional = _load_json(CONSTITUTIONAL_AUDIT_PATH)
    resilience = _load_json(RESILIENCE_AUDIT_PATH)
    recovery = _load_json(RECOVERY_AUDIT_PATH)
    scenario = _load_json(SCENARIO_AUDIT_PATH)

    institutional_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(institutional, "records") if isinstance(r.get("riskScore"), (int, float))], 0.4)
    queue_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(load_shedding, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    constitutional_risk = _safe_mean([float(r.get("governanceRisk")) for r in _parse_rows(constitutional, "evaluations") if isinstance(r.get("governanceRisk"), (int, float))], 0.35)
    resilience_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(resilience, "records") if isinstance(r.get("riskScore"), (int, float))], 0.4)
    recovery_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(recovery, "records") if isinstance(r.get("riskScore"), (int, float))], 0.4)
    scenario_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(scenario, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)

    system_risk = _clamp01(
        0.18 * institutional_risk
        + 0.18 * queue_risk
        + 0.16 * constitutional_risk
        + 0.16 * resilience_risk
        + 0.16 * recovery_risk
        + 0.16 * scenario_risk
    )

    candidate_rows = {str(r.get("targetId")): r for r in _parse_rows(c_map.payload, "targets") if isinstance(r.get("targetId"), str)}
    conflict_rows = {str(r.get("targetId")): r for r in _parse_rows(c_report.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            summary=p_summary.payload,
            candidate_rows=candidate_rows,
            conflict_rows=conflict_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(p_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    created_at = _resolve_created_at(p_map.payload, p_summary.payload, c_map.payload, c_report.payload)
    loaded = [p_map, p_summary, c_map, c_report]
    mode, warning = _classify_mode(loaded)

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
        "institutional / queue / watchlist state -> CoherenceLattice priority formalization -> "
        "Sophia triage audit -> Publisher priority and triage overlays -> human/community ordered review"
    )
    caution = (
        "Triage recommendations are bounded ordering guidance only and do not automatically reconfigure queues "
        "or canonical truth."
    )

    audit_payload = {
        "schema": "triage_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    recommendations_payload = {
        "schema": "triage_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(TRIAGE_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(TRIAGE_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia priority and triage audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    TRIAGE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    TRIAGE_RECOMMENDATIONS_OUT.write_text(json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {TRIAGE_AUDIT_OUT}")
    print(f"Wrote {TRIAGE_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
