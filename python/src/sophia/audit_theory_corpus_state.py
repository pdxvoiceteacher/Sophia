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

THEORY_CORPUS_MAP_PATH = BRIDGE_DIR / "theory_corpus_map.json"
THEORY_REVISION_LINEAGE_PATH = BRIDGE_DIR / "theory_revision_lineage.json"
NEGATIVE_RESULT_REGISTRY_PATH = BRIDGE_DIR / "negative_result_registry.json"
THEORY_COMPETITION_REPORT_PATH = BRIDGE_DIR / "theory_competition_report.json"

EXPERIMENTAL_AUDIT_PATH = BRIDGE_DIR / "experimental_audit.json"
PREDICTION_AUDIT_PATH = BRIDGE_DIR / "prediction_audit.json"
BRANCH_LIFECYCLE_AUDIT_PATH = BRIDGE_DIR / "branch_lifecycle_audit.json"
COLLABORATIVE_REVIEW_AUDIT_PATH = BRIDGE_DIR / "collaborative_review_audit.json"

THEORY_CORPUS_AUDIT_OUT = BRIDGE_DIR / "theory_corpus_audit.json"
THEORY_CORPUS_RECOMMENDATIONS_OUT = BRIDGE_DIR / "theory_corpus_recommendations.json"

THEORY_CORPUS_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "theory_corpus_audit_v1.schema.json"
THEORY_CORPUS_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "theory_corpus_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "theory_corpus_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class TheoryCorpusInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class TheoryDecision:
    target_id: str
    target_type: str
    theory_status: str
    coherence_score: float
    risk_score: float
    falsification_context: str
    replication_context: str
    revision_context: str
    negative_result_context: str
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
        "theory-watch": "watch",
        "hypothesis-only": "suppress",
        "replication-pending": "watch",
        "candidate-review": "docket",
        "competition-active": "watch",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise TheoryCorpusInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    schema_version = str(payload.get("schemaVersion"))
    if schema_version != SUPPORTED_SCHEMA_VERSION:
        raise TheoryCorpusInputError(f"Unsupported schemaVersion in {path}: {schema_version}; supported={SUPPORTED_SCHEMA_VERSION}")
    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise TheoryCorpusInputError(
            f"Unexpected producerRepo in {path}: {producer_repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(canonical_path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if canonical_path.exists():
        payload = _load_json(canonical_path)
        _validate_provenance(payload, path=canonical_path)
        return LoadedArtifact(path=canonical_path, payload=payload, source_mode="canonical")

    available_compat = [path for path in compatibility_paths if path.exists()]
    if not available_compat:
        raise TheoryCorpusInputError(f"Missing required canonical artifact: {canonical_path}")
    if not allow_compatibility_names:
        names = ", ".join(str(path) for path in available_compat)
        raise TheoryCorpusInputError(
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
        return "fixture", "Inputs are fixture theory-corpus artifacts; output is non-canonical simulation guidance."
    return (
        "mixed",
        "MIXED MODE WARNING: theory-corpus inputs combine live and fixture producers; review provenance before action.",
    )


def evaluate_target(
    row: dict[str, Any],
    *,
    lineage_rows: dict[str, dict[str, Any]],
    negative_rows: dict[str, dict[str, Any]],
    competition_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> TheoryDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "theory")

    theory_coherence = _clamp01(float(row.get("theoryCoherence", 0.5)))
    falsification_strength = _clamp01(float(row.get("falsificationStrength", 0.45)))
    replication_strength = _clamp01(float(row.get("replicationStrength", 0.45)))

    lineage = lineage_rows.get(target_id, {})
    revision_quality = _clamp01(float(lineage.get("revisionQuality", 0.5)))
    revision_transparency = _clamp01(float(lineage.get("revisionTransparency", 0.5)))

    negative = negative_rows.get(target_id, {})
    negative_preservation = _clamp01(float(negative.get("negativeResultPreservation", 0.5)))
    failed_line_erasure_risk = _clamp01(float(negative.get("failedLineErasureRisk", 0.4)))

    competition = competition_rows.get(target_id, {})
    competition_intensity = _clamp01(float(competition.get("competitionIntensity", 0.4)))
    suppression_risk = _clamp01(float(competition.get("suppressionRisk", 0.4)))

    coherence = _clamp01(
        0.18 * theory_coherence
        + 0.18 * falsification_strength
        + 0.18 * replication_strength
        + 0.16 * revision_quality
        + 0.14 * revision_transparency
        + 0.16 * negative_preservation
    )
    risk = _clamp01(
        0.20 * (1.0 - falsification_strength)
        + 0.18 * (1.0 - replication_strength)
        + 0.16 * failed_line_erasure_risk
        + 0.16 * suppression_risk
        + 0.14 * competition_intensity
        + 0.16 * system_risk
    )

    if suppression_risk >= 0.80 or failed_line_erasure_risk >= 0.78:
        status = "require-human-review"
        rule = "safeguard-against-suppression-or-erasure"
    elif falsification_strength <= 0.34:
        status = "hypothesis-only"
        rule = "insufficient-falsification-for-theory-status"
    elif replication_strength <= 0.44:
        status = "replication-pending"
        rule = "replication-path-pending"
    elif competition_intensity >= 0.64 or suppression_risk >= 0.58:
        status = "competition-active"
        rule = "competition-must-remain-open"
    elif coherence >= 0.68 and risk <= 0.42 and revision_transparency >= 0.62 and negative_preservation >= 0.62:
        status = "candidate-review"
        rule = "candidate-review-under-bounded-evidence"
    else:
        status = "theory-watch"
        rule = "watch-theory-until-maturity-improves"

    falsification_context = (
        f"falsificationStrength={falsification_strength:.3f}, theoryCoherence={theory_coherence:.3f}; "
        "theory claims remain provisional without strong falsification grounding."
    )
    replication_context = (
        f"replicationStrength={replication_strength:.3f}, competitionIntensity={competition_intensity:.3f}, suppressionRisk={suppression_risk:.3f}; "
        "competing theories remain visible and testable."
    )
    revision_context = (
        f"revisionQuality={revision_quality:.3f}, revisionTransparency={revision_transparency:.3f}; "
        "revision lineage must remain auditable over time."
    )
    negative_result_context = (
        f"negativeResultPreservation={negative_preservation:.3f}, failedLineErasureRisk={failed_line_erasure_risk:.3f}, systemRisk={system_risk:.3f}; "
        "negative results are preserved and cannot be erased silently."
    )

    explanation = (
        f"Theory-corpus guidance is bounded scientific-governance guidance only. targetId={target_id}, "
        f"theoryStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return TheoryDecision(
        target_id=target_id,
        target_type=target_type,
        theory_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        falsification_context=falsification_context,
        replication_context=replication_context,
        revision_context=revision_context,
        negative_result_context=negative_result_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(decision: TheoryDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "theoryStatus": decision.theory_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "falsificationContext": decision.falsification_context,
        "replicationContext": decision.replication_context,
        "revisionContext": decision.revision_context,
        "negativeResultContext": decision.negative_result_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    corpus_artifact = _load_required_artifact(
        THEORY_CORPUS_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "theory_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    lineage_artifact = _load_required_artifact(
        THEORY_REVISION_LINEAGE_PATH,
        compatibility_paths=(BRIDGE_DIR / "revision_lineage.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    negative_artifact = _load_required_artifact(
        NEGATIVE_RESULT_REGISTRY_PATH,
        compatibility_paths=(BRIDGE_DIR / "negative_results.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    competition_artifact = _load_required_artifact(
        THEORY_COMPETITION_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "competition_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    corpus_map = corpus_artifact.payload
    lineage_map = lineage_artifact.payload
    negative_registry = negative_artifact.payload
    competition_report = competition_artifact.payload

    experimental = _load_json(EXPERIMENTAL_AUDIT_PATH)
    prediction = _load_json(PREDICTION_AUDIT_PATH)
    branch = _load_json(BRANCH_LIFECYCLE_AUDIT_PATH)
    collaborative = _load_json(COLLABORATIVE_REVIEW_AUDIT_PATH)

    experimental_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(experimental, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    prediction_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(prediction, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    branch_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(branch, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    collaborative_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(collaborative, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.26 * experimental_risk + 0.24 * prediction_risk + 0.24 * branch_risk + 0.26 * collaborative_risk)

    lineage_rows = {str(r.get("targetId")): r for r in _parse_rows(lineage_map, "targets") if isinstance(r.get("targetId"), str)}
    negative_rows = {str(r.get("targetId")): r for r in _parse_rows(negative_registry, "targets") if isinstance(r.get("targetId"), str)}
    competition_rows = {str(r.get("targetId")): r for r in _parse_rows(competition_report, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            lineage_rows=lineage_rows,
            negative_rows=negative_rows,
            competition_rows=competition_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(corpus_map, "targets")
    ]
    decisions = sorted(decisions, key=lambda decision: decision.target_id)

    loaded = [corpus_artifact, lineage_artifact, negative_artifact, competition_artifact]
    input_mode, input_warning = _classify_input_mode(loaded)
    created_at = _resolve_created_at(corpus_map, lineage_map, negative_registry, competition_report)

    metadata = {
        "inputMode": input_mode,
        "inputModeWarning": input_warning,
        "systemRisk": round(system_risk, 6),
        "inputArtifacts": [
            {
                "path": str(item.path.relative_to(REPO_ROOT)) if item.path.is_relative_to(REPO_ROOT) else str(item.path),
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

    phaselock = (
        "experimental + prediction + branch + collaborative state -> CoherenceLattice theory-corpus formalization -> "
        "Sophia theory-corpus audit -> Publisher bounded scientific overlays -> human/community review"
    )
    caution = (
        "Theory-corpus recommendations are bounded scientific-governance guidance only and do not certify final truth, "
        "erase failed lines, or suppress competing theories."
    )

    audit_payload = {
        "schema": "theory_corpus_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(decision) for decision in decisions],
    }
    recommendations_payload = {
        "schema": "theory_corpus_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(decision) for decision in decisions],
    }

    Draft202012Validator(_load_json(THEORY_CORPUS_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(THEORY_CORPUS_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia theory-corpus state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    THEORY_CORPUS_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    THEORY_CORPUS_RECOMMENDATIONS_OUT.write_text(json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {THEORY_CORPUS_AUDIT_OUT}")
    print(f"Wrote {THEORY_CORPUS_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
