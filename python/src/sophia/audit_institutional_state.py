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

INSTITUTIONAL_STATE_MAP_PATH = BRIDGE_DIR / "institutional_state_map.json"
INSTITUTIONAL_STATE_SUMMARY_PATH = BRIDGE_DIR / "institutional_state_summary.json"
INSTITUTIONAL_CONFLICT_REPORT_PATH = BRIDGE_DIR / "institutional_conflict_report.json"
INSTITUTIONAL_HEALTH_PROJECTION_PATH = BRIDGE_DIR / "institutional_health_projection.json"
PHASELOCK_CONTRACT_REPORT_PATH = BRIDGE_DIR / "phaselock_contract_report.json"

INSTITUTIONAL_AUDIT_OUT = BRIDGE_DIR / "institutional_audit.json"
INSTITUTIONAL_RECOMMENDATIONS_OUT = BRIDGE_DIR / "institutional_recommendations.json"

INSTITUTIONAL_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "institutional_audit_v1.schema.json"
INSTITUTIONAL_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "institutional_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "institutional_bridge_v1"
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


class InstitutionalInputError(RuntimeError):
    """Raised when institutional bridge inputs fail hardening checks."""


@dataclass(slots=True)
class InstitutionalDecision:
    institution_id: str
    institutional_status: str
    synthesis_score: float
    risk_score: float
    conflict_score: float
    health_score: float
    governing_rule: str
    explanation: str
    target_publisher_action: str


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _clamp01(v: float) -> float:
    return max(0.0, min(1.0, float(v)))


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for d in docs:
        ts = d.get("generatedAt") if isinstance(d, dict) else None
        if isinstance(ts, str) and ts:
            return ts
        ts_legacy = d.get("created_at") if isinstance(d, dict) else None
        if isinstance(ts_legacy, str) and ts_legacy:
            return ts_legacy
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str) -> str:
    return {
        "stable": "docket",
        "monitor": "watch",
        "caution": "watch",
        "freeze-pathways": "suppress",
        "require-human-review": "docket",
        "preservation-mode": "suppress",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise InstitutionalInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")

    schema_version = str(payload.get("schemaVersion"))
    if schema_version != SUPPORTED_SCHEMA_VERSION:
        raise InstitutionalInputError(
            f"Unsupported schemaVersion in {path}: {schema_version}; supported={SUPPORTED_SCHEMA_VERSION}"
        )

    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise InstitutionalInputError(
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
        return LoadedArtifact(path=canonical_path, payload=payload, source_mode="canonical")

    available_compat = [path for path in compatibility_paths if path.exists()]
    if not available_compat:
        raise InstitutionalInputError(f"Missing required canonical artifact: {canonical_path}")

    if not allow_compatibility_names:
        names = ", ".join(str(path) for path in available_compat)
        raise InstitutionalInputError(
            f"Canonical artifact missing ({canonical_path}) and deprecated/ambiguous alternatives found: {names}. "
            "Re-run with --allow-compatibility-names only for explicit migration fallback."
        )

    compat_path = available_compat[0]
    payload = _load_json(compat_path)
    _validate_provenance(payload, path=compat_path)
    return LoadedArtifact(path=compat_path, payload=payload, source_mode="compatibility")


def _classify_input_mode(artifacts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(item.payload.get("producerRepo")) for item in artifacts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture artifacts; output is for simulation/testing and must not be treated as canonical truth."
    return (
        "mixed",
        "MIXED MODE WARNING: Inputs combine live and fixture producers; review provenance before acting on recommendations.",
    )


def evaluate_institution(
    row: dict[str, Any],
    *,
    state_summary: dict[str, Any],
    conflict_rows: dict[str, dict[str, Any]],
    health_rows: dict[str, dict[str, Any]],
) -> InstitutionalDecision:
    institution_id = str(row.get("institutionId") or "institution:unknown")

    coherence = _clamp01(float(row.get("coherenceScore", state_summary.get("meanCoherenceScore", 0.5))))
    pathway_integrity = _clamp01(float(row.get("pathwayIntegrity", state_summary.get("meanPathwayIntegrity", 0.5))))

    conflict_row = conflict_rows.get(institution_id, {})
    health_row = health_rows.get(institution_id, {})

    conflict_score = _clamp01(float(conflict_row.get("conflictScore", state_summary.get("meanConflictScore", 0.4))))
    unresolved_conflicts = int(conflict_row.get("unresolvedConflicts", 0))
    health_score = _clamp01(float(health_row.get("healthScore", state_summary.get("meanHealthScore", 0.6))))
    decay_risk = _clamp01(float(health_row.get("decayRisk", state_summary.get("meanDecayRisk", 0.4))))

    synthesis = _clamp01(0.45 * coherence + 0.35 * pathway_integrity + 0.20 * health_score)
    risk = _clamp01(0.35 * conflict_score + 0.30 * decay_risk + 0.20 * (1.0 - pathway_integrity) + 0.15 * (1.0 - coherence))

    if health_score <= 0.28 or decay_risk >= 0.84:
        status = "preservation-mode"
        rule = "preserve-when-institutional-health-collapses"
        explanation = "Institutional health is in collapse-range; preserve evidence and continuity context while freezing fragile pathways."
    elif unresolved_conflicts >= 4 or (conflict_score >= 0.82 and pathway_integrity <= 0.40):
        status = "require-human-review"
        rule = "stacked-conflict-human-review-override"
        explanation = "Conflict accumulation is too high for automated pathway guidance and requires human/community adjudication."
    elif conflict_score >= 0.72 or risk >= 0.72:
        status = "freeze-pathways"
        rule = "freeze-under-high-institutional-risk"
        explanation = "Institutional risk is elevated; freeze high-impact pathways until review confirms safe re-entry conditions."
    elif synthesis >= 0.72 and risk <= 0.34 and unresolved_conflicts == 0:
        status = "stable"
        rule = "sustain-healthy-institutional-state"
        explanation = "Institutional synthesis is coherent and low-risk; continue bounded monitoring without pathway mutation."
    elif risk <= 0.55 and synthesis >= 0.48:
        status = "monitor"
        rule = "monitor-drift-before-escalation"
        explanation = "Institutional state is serviceable but requires drift monitoring to prevent latent governance degradation."
    else:
        status = "caution"
        rule = "caution-under-ambiguous-institutional-signals"
        explanation = "Institutional signals are mixed; maintain caution with bounded recommendations and explicit review checkpoints."

    return InstitutionalDecision(
        institution_id=institution_id,
        institutional_status=status,
        synthesis_score=round(synthesis, 6),
        risk_score=round(risk, 6),
        conflict_score=round(conflict_score, 6),
        health_score=round(health_score, 6),
        governing_rule=rule,
        explanation=(
            f"{explanation} institutionId={institution_id}, synthesis={synthesis:.3f}, "
            f"risk={risk:.3f}, conflict={conflict_score:.3f}, health={health_score:.3f}."
        ),
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(item: InstitutionalDecision) -> dict[str, Any]:
    return {
        "institutionId": item.institution_id,
        "institutionalStatus": item.institutional_status,
        "synthesisScore": item.synthesis_score,
        "riskScore": item.risk_score,
        "conflictScore": item.conflict_score,
        "healthScore": item.health_score,
        "governingRule": item.governing_rule,
        "explanation": item.explanation,
        "targetPublisherAction": item.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    state_map_artifact = _load_required_artifact(
        INSTITUTIONAL_STATE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "institutional_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    state_summary_artifact = _load_required_artifact(
        INSTITUTIONAL_STATE_SUMMARY_PATH,
        compatibility_paths=(BRIDGE_DIR / "institutional_summary.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    conflict_report_artifact = _load_required_artifact(
        INSTITUTIONAL_CONFLICT_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "institutional_conflicts.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    health_projection_artifact = _load_required_artifact(
        INSTITUTIONAL_HEALTH_PROJECTION_PATH,
        compatibility_paths=(BRIDGE_DIR / "institutional_health.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    state_map = state_map_artifact.payload
    state_summary = state_summary_artifact.payload
    conflict_report = conflict_report_artifact.payload
    health_projection = health_projection_artifact.payload

    loaded = [state_map_artifact, state_summary_artifact, conflict_report_artifact, health_projection_artifact]
    input_mode, mode_warning = _classify_input_mode(loaded)

    conflict_rows = {
        str(r.get("institutionId")): r
        for r in (conflict_report.get("institutions") if isinstance(conflict_report.get("institutions"), list) else [])
        if isinstance(r, dict) and isinstance(r.get("institutionId"), str)
    }
    health_rows = {
        str(r.get("institutionId")): r
        for r in (health_projection.get("institutions") if isinstance(health_projection.get("institutions"), list) else [])
        if isinstance(r, dict) and isinstance(r.get("institutionId"), str)
    }

    institution_rows = state_map.get("institutions") if isinstance(state_map.get("institutions"), list) else []
    decisions = [
        evaluate_institution(
            row,
            state_summary=state_summary,
            conflict_rows=conflict_rows,
            health_rows=health_rows,
        )
        for row in institution_rows
        if isinstance(row, dict)
    ]
    decisions = sorted(decisions, key=lambda item: item.institution_id)

    phaselock_contract_status = "not-present"
    if PHASELOCK_CONTRACT_REPORT_PATH.exists():
        phaselock_payload = _load_json(PHASELOCK_CONTRACT_REPORT_PATH)
        if isinstance(phaselock_payload.get("status"), str) and phaselock_payload.get("status"):
            phaselock_contract_status = str(phaselock_payload.get("status"))

    created_at = _resolve_created_at(state_summary, state_map, conflict_report, health_projection)
    phaselock = (
        "CoherenceLattice institutional synthesis -> Sophia institutional audit -> "
        "Publisher institutional overlays (read-only over canonical truth)"
    )

    metadata = {
        "inputMode": input_mode,
        "inputModeWarning": mode_warning,
        "phaselockContractStatus": phaselock_contract_status,
        "inputArtifacts": [
            {
                "path": (str(item.path.relative_to(REPO_ROOT)) if item.path.is_relative_to(REPO_ROOT) else str(item.path)),
                "sourceMode": item.source_mode,
                "schemaVersion": str(item.payload.get("schemaVersion")),
                "producerRepo": str(item.payload.get("producerRepo")),
                "producerModule": str(item.payload.get("producerModule")),
                "producerCommit": str(item.payload.get("producerCommit")),
                "generatedAt": str(item.payload.get("generatedAt")),
            }
            for item in loaded
        ],
    }

    audit_payload = {
        "schema": "institutional_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": (
            "Institutional audit is bounded and advisory; it does not mutate canonical truth "
            "and does not authorize autonomous institutional pathway changes."
        ),
        "metadata": metadata,
        "records": [_to_payload(item) for item in decisions],
    }

    recommendations_payload = {
        "schema": "institutional_recommendations_v1",
        "created_at": created_at,
        "phaselock": (
            "CoherenceLattice institutional synthesis -> Sophia bounded recommendations -> "
            "Publisher state surfacing without mutating canonical truth"
        ),
        "caution": (
            "Recommendations are bounded advisory outputs for human/community governance review; "
            "Publisher must surface institutional state without mutating canonical truth."
        ),
        "metadata": metadata,
        "recommendations": [_to_payload(item) for item in decisions],
    }

    Draft202012Validator(_load_json(INSTITUTIONAL_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(INSTITUTIONAL_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia institutional state audit")
    parser.add_argument(
        "--allow-compatibility-names",
        action="store_true",
        help="Allow deprecated artifact names as an explicit compatibility fallback.",
    )
    args = parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    BRIDGE_DIR.mkdir(parents=True, exist_ok=True)
    INSTITUTIONAL_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    INSTITUTIONAL_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {INSTITUTIONAL_AUDIT_OUT}")
    print(f"Wrote {INSTITUTIONAL_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
