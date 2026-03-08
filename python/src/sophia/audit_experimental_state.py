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

EXPERIMENTAL_HYPOTHESIS_MAP_PATH = BRIDGE_DIR / "experimental_hypothesis_map.json"
FALSIFICATION_DESIGN_REPORT_PATH = BRIDGE_DIR / "falsification_design_report.json"
REPLICATION_PATHWAY_MAP_PATH = BRIDGE_DIR / "replication_pathway_map.json"
THEORY_PROMOTION_GATE_PATH = BRIDGE_DIR / "theory_promotion_gate.json"

PREDICTION_AUDIT_PATH = BRIDGE_DIR / "prediction_audit.json"
BRANCH_LIFECYCLE_AUDIT_PATH = BRIDGE_DIR / "branch_lifecycle_audit.json"
EVIDENCE_AUTHORITY_AUDIT_PATH = BRIDGE_DIR / "evidence_authority_audit.json"
COLLABORATIVE_REVIEW_AUDIT_PATH = BRIDGE_DIR / "collaborative_review_audit.json"

EXPERIMENTAL_AUDIT_OUT = BRIDGE_DIR / "experimental_audit.json"
EXPERIMENTAL_RECOMMENDATIONS_OUT = BRIDGE_DIR / "experimental_recommendations.json"

EXPERIMENTAL_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "experimental_audit_v1.schema.json"
EXPERIMENTAL_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "experimental_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "experimental_design_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class ExperimentalInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class ExperimentalDecision:
    target_id: str
    target_type: str
    experimental_status: str
    coherence_score: float
    risk_score: float
    calibration_context: str
    falsification_context: str
    replication_context: str
    authority_context: str
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
        "hypothesis-watch": "watch",
        "falsification-first": "suppress",
        "replication-required": "watch",
        "theory-candidate-review": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise ExperimentalInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    schema_version = str(payload.get("schemaVersion"))
    if schema_version != SUPPORTED_SCHEMA_VERSION:
        raise ExperimentalInputError(f"Unsupported schemaVersion in {path}: {schema_version}; supported={SUPPORTED_SCHEMA_VERSION}")
    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise ExperimentalInputError(
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
        raise ExperimentalInputError(f"Missing required canonical artifact: {canonical_path}")
    if not allow_compatibility_names:
        names = ", ".join(str(path) for path in available_compat)
        raise ExperimentalInputError(
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
        return "fixture", "Inputs are fixture experimental artifacts; output is non-canonical simulation guidance."
    return (
        "mixed",
        "MIXED MODE WARNING: experimental inputs combine live and fixture producers; review provenance before action.",
    )


def evaluate_target(
    row: dict[str, Any],
    *,
    falsification_rows: dict[str, dict[str, Any]],
    replication_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> ExperimentalDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "hypothesis")

    hypothesis_clarity = _clamp01(float(row.get("hypothesisClarity", 0.5)))
    prediction_calibration = _clamp01(float(row.get("predictionCalibration", 0.5)))

    falsification = falsification_rows.get(target_id, {})
    falsification_quality = _clamp01(float(falsification.get("falsificationQuality", 0.45)))
    falsification_coverage = _clamp01(float(falsification.get("falsificationCoverage", 0.45)))

    replication = replication_rows.get(target_id, {})
    replication_readiness = _clamp01(float(replication.get("replicationReadiness", 0.45)))
    replication_independence = _clamp01(float(replication.get("replicationIndependence", 0.45)))

    gate = gate_rows.get(target_id, {})
    promotion_readiness = _clamp01(float(gate.get("promotionReadiness", 0.4)))
    blocked_promotion = bool(gate.get("blockedPromotion", False))
    authority_pressure = _clamp01(float(gate.get("authorityPressure", 0.4)))

    coherence = _clamp01(
        0.18 * hypothesis_clarity
        + 0.18 * prediction_calibration
        + 0.18 * falsification_quality
        + 0.16 * falsification_coverage
        + 0.16 * replication_readiness
        + 0.14 * replication_independence
    )
    risk = _clamp01(
        0.22 * (1.0 - falsification_quality)
        + 0.20 * (1.0 - replication_readiness)
        + 0.16 * authority_pressure
        + 0.16 * (1.0 - promotion_readiness)
        + 0.12 * (1.0 - prediction_calibration)
        + 0.14 * system_risk
    )

    if blocked_promotion or authority_pressure >= 0.84:
        status = "require-human-review"
        rule = "blocked-promotion-human-review-gate"
    elif falsification_quality <= 0.34 or falsification_coverage <= 0.34:
        status = "falsification-first"
        rule = "falsification-required-before-promotion"
    elif replication_readiness <= 0.44 or replication_independence <= 0.44:
        status = "replication-required"
        rule = "replication-path-required"
    elif promotion_readiness >= 0.70 and falsification_quality >= 0.66 and replication_readiness >= 0.66 and risk <= 0.44:
        status = "theory-candidate-review"
        rule = "bounded-theory-candidate-review"
    else:
        status = "hypothesis-watch"
        rule = "watch-hypothesis-until-maturity"

    calibration_context = (
        f"predictionCalibration={prediction_calibration:.3f}, hypothesisClarity={hypothesis_clarity:.3f}, promotionReadiness={promotion_readiness:.3f}; "
        "calibration remains provisional under scientific governance."
    )
    falsification_context = (
        f"falsificationQuality={falsification_quality:.3f}, falsificationCoverage={falsification_coverage:.3f}; "
        "no promotion without explicit falsification design."
    )
    replication_context = (
        f"replicationReadiness={replication_readiness:.3f}, replicationIndependence={replication_independence:.3f}; "
        "replication pathways are required before theory promotion."
    )
    authority_context = (
        f"authorityPressure={authority_pressure:.3f}, blockedPromotion={str(blocked_promotion).lower()}, systemRisk={system_risk:.3f}; "
        "promotion decisions remain bounded and non-autonomous."
    )

    explanation = (
        f"Experimental guidance is bounded scientific-governance guidance only. targetId={target_id}, "
        f"experimentalStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return ExperimentalDecision(
        target_id=target_id,
        target_type=target_type,
        experimental_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        calibration_context=calibration_context,
        falsification_context=falsification_context,
        replication_context=replication_context,
        authority_context=authority_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(decision: ExperimentalDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "experimentalStatus": decision.experimental_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "calibrationContext": decision.calibration_context,
        "falsificationContext": decision.falsification_context,
        "replicationContext": decision.replication_context,
        "authorityContext": decision.authority_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    hypothesis_artifact = _load_required_artifact(
        EXPERIMENTAL_HYPOTHESIS_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "hypothesis_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    falsification_artifact = _load_required_artifact(
        FALSIFICATION_DESIGN_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "falsification_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    replication_artifact = _load_required_artifact(
        REPLICATION_PATHWAY_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "replication_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    gate_artifact = _load_required_artifact(
        THEORY_PROMOTION_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "promotion_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    hypothesis_map = hypothesis_artifact.payload
    falsification_report = falsification_artifact.payload
    replication_map = replication_artifact.payload
    promotion_gate = gate_artifact.payload

    prediction = _load_json(PREDICTION_AUDIT_PATH)
    branch = _load_json(BRANCH_LIFECYCLE_AUDIT_PATH)
    evidence = _load_json(EVIDENCE_AUTHORITY_AUDIT_PATH)
    collaborative = _load_json(COLLABORATIVE_REVIEW_AUDIT_PATH)

    prediction_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(prediction, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    branch_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(branch, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    evidence_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(evidence, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    collaborative_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(collaborative, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.26 * prediction_risk + 0.26 * branch_risk + 0.24 * evidence_risk + 0.24 * collaborative_risk)

    falsification_rows = {str(r.get("targetId")): r for r in _parse_rows(falsification_report, "targets") if isinstance(r.get("targetId"), str)}
    replication_rows = {str(r.get("targetId")): r for r in _parse_rows(replication_map, "targets") if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(promotion_gate, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            falsification_rows=falsification_rows,
            replication_rows=replication_rows,
            gate_rows=gate_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(hypothesis_map, "targets")
    ]
    decisions = sorted(decisions, key=lambda decision: decision.target_id)

    loaded = [hypothesis_artifact, falsification_artifact, replication_artifact, gate_artifact]
    input_mode, input_warning = _classify_input_mode(loaded)
    created_at = _resolve_created_at(hypothesis_map, falsification_report, replication_map, promotion_gate)

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
        "prediction + branch lifecycle + evidence + collaborative state -> CoherenceLattice experiment formalization -> "
        "Sophia experimental audit -> Publisher bounded scientific overlays -> human/community scientific review"
    )
    caution = (
        "Experimental recommendations are bounded scientific-governance guidance only and do not autonomously certify theory truth."
    )

    audit_payload = {
        "schema": "experimental_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(decision) for decision in decisions],
    }
    recommendations_payload = {
        "schema": "experimental_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(decision) for decision in decisions],
    }

    Draft202012Validator(_load_json(EXPERIMENTAL_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(EXPERIMENTAL_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia experimental-state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    EXPERIMENTAL_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    EXPERIMENTAL_RECOMMENDATIONS_OUT.write_text(json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {EXPERIMENTAL_AUDIT_OUT}")
    print(f"Wrote {EXPERIMENTAL_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
