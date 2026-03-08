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

REVIEWER_DELIBERATION_MAP_PATH = BRIDGE_DIR / "reviewer_deliberation_map.json"
REVIEWER_POSITION_MAP_PATH = BRIDGE_DIR / "reviewer_position_map.json"
CONSENSUS_STATE_REPORT_PATH = BRIDGE_DIR / "consensus_state_report.json"
DISSENT_TRACE_REPORT_PATH = BRIDGE_DIR / "dissent_trace_report.json"

REVIEW_PACKET_AUDIT_PATH = BRIDGE_DIR / "review_packet_audit.json"
CAUSAL_AUDIT_PATH = BRIDGE_DIR / "causal_audit.json"
EVIDENCE_AUTHORITY_AUDIT_PATH = BRIDGE_DIR / "evidence_authority_audit.json"
CLOSURE_AUDIT_PATH = BRIDGE_DIR / "closure_audit.json"

COLLABORATIVE_REVIEW_AUDIT_OUT = BRIDGE_DIR / "collaborative_review_audit.json"
COLLABORATIVE_REVIEW_RECOMMENDATIONS_OUT = BRIDGE_DIR / "collaborative_review_recommendations.json"

COLLABORATIVE_REVIEW_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "collaborative_review_audit_v1.schema.json"
COLLABORATIVE_REVIEW_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "collaborative_review_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "collaborative_review_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class CollaborativeReviewInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class CollaborativeDecision:
    target_id: str
    target_type: str
    collaborative_status: str
    coherence_score: float
    risk_score: float
    consensus_context: str
    dissent_context: str
    maturity_context: str
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
        "consensus-bounded": "docket",
        "dissent-active": "watch",
        "verify-first": "suppress",
        "blocked": "suppress",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise CollaborativeReviewInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")

    schema_version = str(payload.get("schemaVersion"))
    if schema_version != SUPPORTED_SCHEMA_VERSION:
        raise CollaborativeReviewInputError(
            f"Unsupported schemaVersion in {path}: {schema_version}; supported={SUPPORTED_SCHEMA_VERSION}"
        )

    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise CollaborativeReviewInputError(
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
        raise CollaborativeReviewInputError(f"Missing required canonical artifact: {canonical_path}")

    if not allow_compatibility_names:
        names = ", ".join(str(path) for path in available_compat)
        raise CollaborativeReviewInputError(
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
        return "fixture", "Inputs are fixture collaborative-review artifacts; output is non-canonical simulation guidance."
    return (
        "mixed",
        "MIXED MODE WARNING: collaborative-review inputs combine live and fixture producers; review provenance before action.",
    )


def evaluate_target(
    row: dict[str, Any],
    *,
    position_rows: dict[str, dict[str, Any]],
    consensus_rows: dict[str, dict[str, Any]],
    dissent_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> CollaborativeDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "review-target")

    deliberation_depth = _clamp01(float(row.get("deliberationDepth", 0.5)))
    review_maturity = _clamp01(float(row.get("reviewMaturity", 0.5)))

    position = position_rows.get(target_id, {})
    position_alignment = _clamp01(float(position.get("positionAlignment", 0.5)))
    minority_caution = _clamp01(float(position.get("minorityCaution", 0.45)))

    consensus = consensus_rows.get(target_id, {})
    consensus_score = _clamp01(float(consensus.get("consensusScore", 0.5)))
    consensus_stability = _clamp01(float(consensus.get("consensusStability", 0.5)))

    dissent = dissent_rows.get(target_id, {})
    dissent_score = _clamp01(float(dissent.get("dissentScore", 0.4)))
    unresolved_dissent = int(dissent.get("unresolvedDissent", 0) or 0)

    coherence = _clamp01(
        0.24 * deliberation_depth
        + 0.18 * review_maturity
        + 0.18 * consensus_score
        + 0.16 * consensus_stability
        + 0.14 * position_alignment
        + 0.10 * (1.0 - dissent_score)
    )

    risk = _clamp01(
        0.22 * dissent_score
        + 0.18 * minority_caution
        + 0.16 * (1.0 - review_maturity)
        + 0.16 * (1.0 - consensus_stability)
        + 0.14 * (1.0 - position_alignment)
        + 0.14 * system_risk
    )

    if dissent_score >= 0.82 and unresolved_dissent >= 2:
        status = "require-human-review"
        rule = "stacked-dissent-human-review"
    elif review_maturity <= 0.34 or consensus_stability <= 0.30:
        status = "verify-first"
        rule = "verify-first-under-immature-consensus"
    elif unresolved_dissent >= 3 or (dissent_score >= 0.68 and consensus_score <= 0.45):
        status = "blocked"
        rule = "blocked-by-unresolved-dissent"
    elif dissent_score >= 0.50 or minority_caution >= 0.58:
        status = "dissent-active"
        rule = "preserve-dissent-with-bounded-consensus"
    else:
        status = "consensus-bounded"
        rule = "bounded-consensus-with-dissent-preserved"

    consensus_context = (
        f"consensusScore={consensus_score:.3f}, consensusStability={consensus_stability:.3f}, positionAlignment={position_alignment:.3f}; "
        "consensus is treated as provisional and bounded."
    )
    dissent_context = (
        f"dissentScore={dissent_score:.3f}, unresolvedDissent={unresolved_dissent}, minorityCaution={minority_caution:.3f}; "
        "dissent traces are preserved and not erased."
    )
    maturity_context = (
        f"deliberationDepth={deliberation_depth:.3f}, reviewMaturity={review_maturity:.3f}, systemRisk={system_risk:.3f}; "
        "ratification requires maturity and explicit review checkpoints."
    )

    explanation = (
        f"Collaborative-review guidance is bounded process guidance only. targetId={target_id}, "
        f"collaborativeStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return CollaborativeDecision(
        target_id=target_id,
        target_type=target_type,
        collaborative_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        consensus_context=consensus_context,
        dissent_context=dissent_context,
        maturity_context=maturity_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(decision: CollaborativeDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "collaborativeStatus": decision.collaborative_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "consensusContext": decision.consensus_context,
        "dissentContext": decision.dissent_context,
        "maturityContext": decision.maturity_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    deliberation_artifact = _load_required_artifact(
        REVIEWER_DELIBERATION_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "deliberation_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    position_artifact = _load_required_artifact(
        REVIEWER_POSITION_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "position_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    consensus_artifact = _load_required_artifact(
        CONSENSUS_STATE_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "consensus_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    dissent_artifact = _load_required_artifact(
        DISSENT_TRACE_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "dissent_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    deliberation_map = deliberation_artifact.payload
    position_map = position_artifact.payload
    consensus_report = consensus_artifact.payload
    dissent_report = dissent_artifact.payload

    review_packet = _load_json(REVIEW_PACKET_AUDIT_PATH)
    causal = _load_json(CAUSAL_AUDIT_PATH)
    authority = _load_json(EVIDENCE_AUTHORITY_AUDIT_PATH)
    closure = _load_json(CLOSURE_AUDIT_PATH)

    review_packet_risk = _safe_mean([float(row.get("riskScore")) for row in _parse_rows(review_packet, "records") if isinstance(row.get("riskScore"), (int, float))], 0.45)
    causal_risk = _safe_mean([float(row.get("riskScore")) for row in _parse_rows(causal, "records") if isinstance(row.get("riskScore"), (int, float))], 0.45)
    authority_risk = _safe_mean([float(row.get("riskScore")) for row in _parse_rows(authority, "records") if isinstance(row.get("riskScore"), (int, float))], 0.45)
    closure_risk = _safe_mean([float(row.get("riskScore")) for row in _parse_rows(closure, "records") if isinstance(row.get("riskScore"), (int, float))], 0.45)

    system_risk = _clamp01(0.28 * review_packet_risk + 0.24 * causal_risk + 0.24 * authority_risk + 0.24 * closure_risk)

    position_rows = {str(row.get("targetId")): row for row in _parse_rows(position_map, "targets") if isinstance(row.get("targetId"), str)}
    consensus_rows = {str(row.get("targetId")): row for row in _parse_rows(consensus_report, "targets") if isinstance(row.get("targetId"), str)}
    dissent_rows = {str(row.get("targetId")): row for row in _parse_rows(dissent_report, "targets") if isinstance(row.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            position_rows=position_rows,
            consensus_rows=consensus_rows,
            dissent_rows=dissent_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(deliberation_map, "targets")
    ]
    decisions = sorted(decisions, key=lambda decision: decision.target_id)

    loaded = [deliberation_artifact, position_artifact, consensus_artifact, dissent_artifact]
    input_mode, input_warning = _classify_input_mode(loaded)
    created_at = _resolve_created_at(deliberation_map, position_map, consensus_report, dissent_report)

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
        "review-packet / causal / authority state -> CoherenceLattice collaborative deliberation formalization -> "
        "Sophia collaborative-review audit -> Publisher bounded review overlays -> human/community deliberation"
    )
    caution = (
        "Collaborative review recommendations are bounded process guidance only and do not erase dissent or "
        "automatically ratify consensus."
    )

    audit_payload = {
        "schema": "collaborative_review_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(decision) for decision in decisions],
    }
    recommendations_payload = {
        "schema": "collaborative_review_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(decision) for decision in decisions],
    }

    Draft202012Validator(_load_json(COLLABORATIVE_REVIEW_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(COLLABORATIVE_REVIEW_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia collaborative-review state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    COLLABORATIVE_REVIEW_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    COLLABORATIVE_REVIEW_RECOMMENDATIONS_OUT.write_text(json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {COLLABORATIVE_REVIEW_AUDIT_OUT}")
    print(f"Wrote {COLLABORATIVE_REVIEW_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
