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

CAUSAL_BUNDLE_MAP_PATH = BRIDGE_DIR / "causal_bundle_map.json"
MECHANISM_CANDIDATE_MAP_PATH = BRIDGE_DIR / "mechanism_candidate_map.json"
MECHANISM_SEPARATION_REPORT_PATH = BRIDGE_DIR / "mechanism_separation_report.json"
CAUSAL_CONFLICT_REPORT_PATH = BRIDGE_DIR / "causal_conflict_report.json"

PATTERN_TEMPORAL_AUDIT_PATH = BRIDGE_DIR / "pattern_temporal_audit.json"
ENVIRONMENT_AUDIT_PATH = BRIDGE_DIR / "environment_audit.json"
EVIDENCE_AUTHORITY_AUDIT_PATH = BRIDGE_DIR / "evidence_authority_audit.json"
VERIFICATION_AUDIT_PATH = BRIDGE_DIR / "verification_audit.json"

CAUSAL_AUDIT_OUT = BRIDGE_DIR / "causal_audit.json"
CAUSAL_RECOMMENDATIONS_OUT = BRIDGE_DIR / "causal_recommendations.json"

CAUSAL_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "causal_audit_v1.schema.json"
CAUSAL_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "causal_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "causal_bundle_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class CausalInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class CausalDecision:
    target_id: str
    target_type: str
    causal_status: str
    coherence_score: float
    risk_score: float
    persistence_context: str
    mechanism_context: str
    counter_hypothesis_context: str
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
        "mechanism-watch": "watch",
        "mechanism-verify-first": "suppress",
        "mechanism-provisional": "watch",
        "mechanism-require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise CausalInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")

    schema_version = str(payload.get("schemaVersion"))
    if schema_version != SUPPORTED_SCHEMA_VERSION:
        raise CausalInputError(f"Unsupported schemaVersion in {path}: {schema_version}; supported={SUPPORTED_SCHEMA_VERSION}")

    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise CausalInputError(
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
        raise CausalInputError(f"Missing required canonical artifact: {canonical_path}")

    if not allow_compatibility_names:
        names = ", ".join(str(path) for path in available_compat)
        raise CausalInputError(
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
        return "fixture", "Inputs are fixture causal artifacts; output is non-canonical simulation guidance."
    return (
        "mixed",
        "MIXED MODE WARNING: causal inputs combine live and fixture producers; review provenance before action.",
    )


def evaluate_target(
    row: dict[str, Any],
    *,
    candidate_rows: dict[str, dict[str, Any]],
    separation_rows: dict[str, dict[str, Any]],
    conflict_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> CausalDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "causal-target")

    persistence = _clamp01(float(row.get("persistenceScore", 0.5)))
    bundle_coherence = _clamp01(float(row.get("bundleCoherence", 0.5)))

    candidate = candidate_rows.get(target_id, {})
    mechanism_confidence = _clamp01(float(candidate.get("mechanismConfidence", 0.5)))
    explanatory_maturity = _clamp01(float(candidate.get("explanatoryMaturity", 0.45)))

    separation = separation_rows.get(target_id, {})
    mechanism_overlap = _clamp01(float(separation.get("mechanismOverlap", 0.4)))
    separation_quality = _clamp01(float(separation.get("separationQuality", 0.5)))

    conflict = conflict_rows.get(target_id, {})
    conflict_score = _clamp01(float(conflict.get("conflictScore", 0.4)))
    counter_hypothesis_strength = _clamp01(float(conflict.get("counterHypothesisStrength", 0.5)))

    explanatory_gap = _clamp01(max(0.0, mechanism_confidence - explanatory_maturity))

    coherence = _clamp01(
        0.24 * persistence
        + 0.18 * bundle_coherence
        + 0.16 * mechanism_confidence
        + 0.14 * explanatory_maturity
        + 0.14 * separation_quality
        + 0.14 * (1.0 - mechanism_overlap)
    )
    risk = _clamp01(
        0.24 * explanatory_gap
        + 0.18 * conflict_score
        + 0.16 * mechanism_overlap
        + 0.14 * (1.0 - separation_quality)
        + 0.14 * (1.0 - explanatory_maturity)
        + 0.14 * system_risk
    )

    if conflict_score >= 0.82 and counter_hypothesis_strength >= 0.72:
        causal_status = "mechanism-require-human-review"
        rule = "stacked-conflict-counterhypothesis-review"
    elif explanatory_gap >= 0.24 or explanatory_maturity <= 0.34:
        causal_status = "mechanism-verify-first"
        rule = "explanatory-gap-verify-first"
    elif risk >= 0.54 or mechanism_overlap >= 0.66:
        causal_status = "mechanism-watch"
        rule = "watch-under-mechanism-entanglement"
    else:
        causal_status = "mechanism-provisional"
        rule = "provisional-mechanism-with-competing-explanations"

    persistence_context = (
        f"persistenceScore={persistence:.3f}, bundleCoherence={bundle_coherence:.3f}, mechanismConfidence={mechanism_confidence:.3f}; "
        "causal persistence is interpreted conservatively."
    )
    mechanism_context = (
        f"explanatoryMaturity={explanatory_maturity:.3f}, separationQuality={separation_quality:.3f}, mechanismOverlap={mechanism_overlap:.3f}; "
        "mechanisms remain separated until maturity improves."
    )
    counter_hypothesis_context = (
        f"counterHypothesisStrength={counter_hypothesis_strength:.3f}, conflictScore={conflict_score:.3f}, explanatoryGap={explanatory_gap:.3f}, systemRisk={system_risk:.3f}; "
        "competing explanations are preserved when uncertainty is high."
    )

    explanation = (
        f"Causal guidance is bounded mechanism guidance only. targetId={target_id}, causalStatus={causal_status}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return CausalDecision(
        target_id=target_id,
        target_type=target_type,
        causal_status=causal_status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        persistence_context=persistence_context,
        mechanism_context=mechanism_context,
        counter_hypothesis_context=counter_hypothesis_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(causal_status),
    )


def _to_payload(decision: CausalDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "causalStatus": decision.causal_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "persistenceContext": decision.persistence_context,
        "mechanismContext": decision.mechanism_context,
        "counterHypothesisContext": decision.counter_hypothesis_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    bundle_artifact = _load_required_artifact(
        CAUSAL_BUNDLE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "causal_bundle.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    candidate_artifact = _load_required_artifact(
        MECHANISM_CANDIDATE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "mechanism_candidates.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    separation_artifact = _load_required_artifact(
        MECHANISM_SEPARATION_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "mechanism_separation.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    conflict_artifact = _load_required_artifact(
        CAUSAL_CONFLICT_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "causal_conflicts.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    bundle_map = bundle_artifact.payload
    candidate_map = candidate_artifact.payload
    separation_report = separation_artifact.payload
    conflict_report = conflict_artifact.payload

    pattern_temporal = _load_json(PATTERN_TEMPORAL_AUDIT_PATH)
    environment = _load_json(ENVIRONMENT_AUDIT_PATH)
    authority = _load_json(EVIDENCE_AUTHORITY_AUDIT_PATH)
    verification = _load_json(VERIFICATION_AUDIT_PATH)

    pattern_risk = _safe_mean([float(row.get("riskScore")) for row in _parse_rows(pattern_temporal, "records") if isinstance(row.get("riskScore"), (int, float))], 0.45)
    environment_risk = _safe_mean([float(row.get("riskScore")) for row in _parse_rows(environment, "records") if isinstance(row.get("riskScore"), (int, float))], 0.45)
    authority_risk = _safe_mean([float(row.get("riskScore")) for row in _parse_rows(authority, "records") if isinstance(row.get("riskScore"), (int, float))], 0.45)
    verification_risk = _safe_mean([float(row.get("riskScore")) for row in _parse_rows(verification, "records") if isinstance(row.get("riskScore"), (int, float))], 0.45)

    system_risk = _clamp01(0.28 * pattern_risk + 0.24 * environment_risk + 0.24 * authority_risk + 0.24 * verification_risk)

    candidate_rows = {str(row.get("targetId")): row for row in _parse_rows(candidate_map, "targets") if isinstance(row.get("targetId"), str)}
    separation_rows = {str(row.get("targetId")): row for row in _parse_rows(separation_report, "targets") if isinstance(row.get("targetId"), str)}
    conflict_rows = {str(row.get("targetId")): row for row in _parse_rows(conflict_report, "targets") if isinstance(row.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            candidate_rows=candidate_rows,
            separation_rows=separation_rows,
            conflict_rows=conflict_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(bundle_map, "targets")
    ]
    decisions = sorted(decisions, key=lambda decision: decision.target_id)

    loaded = [bundle_artifact, candidate_artifact, separation_artifact, conflict_artifact]
    input_mode, input_warning = _classify_input_mode(loaded)
    created_at = _resolve_created_at(bundle_map, candidate_map, separation_report, conflict_report)

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
        "pattern / temporal / environment / authority state -> CoherenceLattice causal bundling and mechanism separation -> "
        "Sophia causal audit -> Publisher bounded causal overlays -> human/community review"
    )
    caution = (
        "Causal recommendations are bounded mechanism guidance only and do not conclude corruption, targeting, "
        "conspiracy, or coordinated guilt."
    )

    audit_payload = {
        "schema": "causal_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(decision) for decision in decisions],
    }
    recommendations_payload = {
        "schema": "causal_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(decision) for decision in decisions],
    }

    Draft202012Validator(_load_json(CAUSAL_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(CAUSAL_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia causal-state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    CAUSAL_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    CAUSAL_RECOMMENDATIONS_OUT.write_text(json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {CAUSAL_AUDIT_OUT}")
    print(f"Wrote {CAUSAL_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
