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

TELEMETRY_FIELD_MAP_PATH = BRIDGE_DIR / "telemetry_field_map.json"
LATTICE_PROJECTION_MAP_PATH = BRIDGE_DIR / "lattice_projection_map.json"
PATTERN_DONATION_REGISTRY_PATH = BRIDGE_DIR / "pattern_donation_registry.json"
ACTION_FUNCTIONAL_SCORECARD_PATH = BRIDGE_DIR / "action_functional_scorecard.json"
BRANCH_EMERGENCE_REPORT_PATH = BRIDGE_DIR / "branch_emergence_report.json"

EVIDENCE_AUTHORITY_AUDIT_PATH = BRIDGE_DIR / "evidence_authority_audit.json"
COLLABORATIVE_REVIEW_AUDIT_PATH = BRIDGE_DIR / "collaborative_review_audit.json"
VERIFICATION_AUDIT_PATH = BRIDGE_DIR / "verification_audit.json"
CAUSAL_AUDIT_PATH = BRIDGE_DIR / "causal_audit.json"

TELEMETRY_FIELD_AUDIT_OUT = BRIDGE_DIR / "telemetry_field_audit.json"
TELEMETRY_FIELD_RECOMMENDATIONS_OUT = BRIDGE_DIR / "telemetry_field_recommendations.json"

TELEMETRY_FIELD_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "telemetry_field_audit_v1.schema.json"
TELEMETRY_FIELD_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "telemetry_field_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "telemetry_field_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class TelemetryFieldInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class TelemetryFieldDecision:
    target_id: str
    target_type: str
    field_status: str
    coherence_score: float
    risk_score: float
    lattice_context: str
    donation_context: str
    action_functional_context: str
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
        "bounded-field": "docket",
        "verify-first": "suppress",
        "provisional-branch": "watch",
        "overreach-risk": "suppress",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise TelemetryFieldInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise TelemetryFieldInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise TelemetryFieldInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise TelemetryFieldInputError(f"Missing required canonical artifact: {path}")

    if not allow_compatibility_names:
        raise TelemetryFieldInputError(
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
        return "fixture", "Inputs are fixture telemetry artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: telemetry inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    lattice_rows: dict[str, dict[str, Any]],
    donation_rows: dict[str, dict[str, Any]],
    taf_rows: dict[str, dict[str, Any]],
    branch_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> TelemetryFieldDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "telemetry-target")

    telemetry_coherence = _clamp01(float(row.get("telemetryCoherence", 0.5)))
    maturity_score = _clamp01(float(row.get("maturityScore", 0.5)))

    lattice = lattice_rows.get(target_id, {})
    projection_stability = _clamp01(float(lattice.get("projectionStability", 0.5)))
    lattice_divergence = _clamp01(float(lattice.get("latticeDivergence", 0.4)))

    donation = donation_rows.get(target_id, {})
    donation_confidence = _clamp01(float(donation.get("donationConfidence", 0.5)))
    donation_novelty = _clamp01(float(donation.get("donationNovelty", 0.4)))

    taf = taf_rows.get(target_id, {})
    functional_score = _clamp01(float(taf.get("functionalScore", 0.5)))
    overreach_score = _clamp01(float(taf.get("overreachScore", 0.4)))

    branch = branch_rows.get(target_id, {})
    emergence_score = _clamp01(float(branch.get("emergenceScore", 0.4)))
    branch_readiness = _clamp01(float(branch.get("branchReadiness", 0.4)))

    coherence = _clamp01(
        0.18 * telemetry_coherence
        + 0.16 * projection_stability
        + 0.16 * donation_confidence
        + 0.14 * functional_score
        + 0.12 * maturity_score
        + 0.12 * branch_readiness
        + 0.12 * (1.0 - lattice_divergence)
    )
    risk = _clamp01(
        0.22 * overreach_score
        + 0.18 * lattice_divergence
        + 0.16 * donation_novelty
        + 0.14 * (1.0 - maturity_score)
        + 0.14 * (1.0 - branch_readiness)
        + 0.16 * system_risk
    )

    if overreach_score >= 0.82 or (emergence_score >= 0.78 and maturity_score <= 0.40):
        status = "require-human-review"
        rule = "branch-overreach-human-review-gate"
    elif maturity_score <= 0.34 or functional_score <= 0.36:
        status = "verify-first"
        rule = "verify-first-under-low-maturity-taf"
    elif overreach_score >= 0.62 or risk >= 0.62:
        status = "overreach-risk"
        rule = "overreach-risk-suppression"
    elif emergence_score >= 0.60 and branch_readiness >= 0.50:
        status = "provisional-branch"
        rule = "provisional-branch-under-bounded-emergence"
    else:
        status = "bounded-field"
        rule = "bounded-field-guidance"

    lattice_context = (
        f"projectionStability={projection_stability:.3f}, latticeDivergence={lattice_divergence:.3f}, telemetryCoherence={telemetry_coherence:.3f}; "
        "lattice projections remain bounded and reviewable."
    )
    donation_context = (
        f"donationConfidence={donation_confidence:.3f}, donationNovelty={donation_novelty:.3f}, emergenceScore={emergence_score:.3f}; "
        "pattern donations are treated as probabilistic signals."
    )
    action_functional_context = (
        f"functionalScore={functional_score:.3f}, overreachScore={overreach_score:.3f}, branchReadiness={branch_readiness:.3f}; "
        "TAF scoring does not autonomously authorize operations."
    )
    maturity_context = (
        f"maturityScore={maturity_score:.3f}, systemRisk={system_risk:.3f}; "
        "branch emergence remains under maturity, authority, and human-review control."
    )

    explanation = (
        f"Telemetry-field guidance is bounded probabilistic guidance only. targetId={target_id}, fieldStatus={status}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return TelemetryFieldDecision(
        target_id=target_id,
        target_type=target_type,
        field_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        lattice_context=lattice_context,
        donation_context=donation_context,
        action_functional_context=action_functional_context,
        maturity_context=maturity_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: TelemetryFieldDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "fieldStatus": d.field_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "latticeContext": d.lattice_context,
        "donationContext": d.donation_context,
        "actionFunctionalContext": d.action_functional_context,
        "maturityContext": d.maturity_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    telemetry = _load_required_artifact(
        TELEMETRY_FIELD_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "telemetry_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    lattice = _load_required_artifact(
        LATTICE_PROJECTION_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "lattice_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    donation = _load_required_artifact(
        PATTERN_DONATION_REGISTRY_PATH,
        compatibility_paths=(BRIDGE_DIR / "donation_registry.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    taf = _load_required_artifact(
        ACTION_FUNCTIONAL_SCORECARD_PATH,
        compatibility_paths=(BRIDGE_DIR / "taf_scorecard.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    branch = _load_required_artifact(
        BRANCH_EMERGENCE_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "branch_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    evidence = _load_json(EVIDENCE_AUTHORITY_AUDIT_PATH)
    collaborative = _load_json(COLLABORATIVE_REVIEW_AUDIT_PATH)
    verification = _load_json(VERIFICATION_AUDIT_PATH)
    causal = _load_json(CAUSAL_AUDIT_PATH)

    evidence_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(evidence, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    collaborative_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(collaborative, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    verification_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(verification, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    causal_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(causal, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.26 * evidence_risk + 0.25 * collaborative_risk + 0.25 * verification_risk + 0.24 * causal_risk)

    lattice_rows = {str(r.get("targetId")): r for r in _parse_rows(lattice.payload, "targets") if isinstance(r.get("targetId"), str)}
    donation_rows = {str(r.get("targetId")): r for r in _parse_rows(donation.payload, "targets") if isinstance(r.get("targetId"), str)}
    taf_rows = {str(r.get("targetId")): r for r in _parse_rows(taf.payload, "targets") if isinstance(r.get("targetId"), str)}
    branch_rows = {str(r.get("targetId")): r for r in _parse_rows(branch.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            lattice_rows=lattice_rows,
            donation_rows=donation_rows,
            taf_rows=taf_rows,
            branch_rows=branch_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(telemetry.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [telemetry, lattice, donation, taf, branch]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(telemetry.payload, lattice.payload, donation.payload, taf.payload, branch.payload)

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
        "telemetry field + lattice + donation + taf emergence -> CoherenceLattice unified field formalization -> "
        "Sophia telemetry field audit -> Publisher bounded overlays -> human/community branch review"
    )
    caution = (
        "Telemetry-field recommendations are bounded probabilistic guidance only and do not autonomously authorize "
        "new operational branches."
    )

    audit_payload = {
        "schema": "telemetry_field_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "telemetry_field_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(TELEMETRY_FIELD_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(TELEMETRY_FIELD_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia telemetry-field state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    TELEMETRY_FIELD_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    TELEMETRY_FIELD_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {TELEMETRY_FIELD_AUDIT_OUT}")
    print(f"Wrote {TELEMETRY_FIELD_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
