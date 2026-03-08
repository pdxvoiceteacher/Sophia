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

EMERGENT_DOMAIN_MAP_PATH = BRIDGE_DIR / "emergent_domain_map.json"
CROSS_DOMAIN_INVARIANT_REPORT_PATH = BRIDGE_DIR / "cross_domain_invariant_report.json"
FIELD_BIRTH_PRESSURE_REPORT_PATH = BRIDGE_DIR / "field_birth_pressure_report.json"
DOMAIN_BOUNDARY_FAILURE_MAP_PATH = BRIDGE_DIR / "domain_boundary_failure_map.json"

THEORY_TRANSFER_AUDIT_PATH = BRIDGE_DIR / "theory_transfer_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"
CURIOSITY_AUDIT_PATH = BRIDGE_DIR / "curiosity_audit.json"
SOCIAL_ENTROPY_AUDIT_PATH = BRIDGE_DIR / "social_entropy_audit.json"
COMMONS_PARTICIPATION_AUDIT_PATH = BRIDGE_DIR / "commons_participation_audit.json"

EMERGENT_DOMAIN_AUDIT_OUT = BRIDGE_DIR / "emergent_domain_audit.json"
EMERGENT_DOMAIN_RECOMMENDATIONS_OUT = BRIDGE_DIR / "emergent_domain_recommendations.json"

EMERGENT_DOMAIN_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "emergent_domain_audit_v1.schema.json"
EMERGENT_DOMAIN_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "emergent_domain_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "emergent_domain_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class EmergentDomainInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class EmergentDomainDecision:
    target_id: str
    target_type: str
    domain_status: str
    coherence_score: float
    risk_score: float
    convergence_context: str
    transfer_context: str
    curiosity_context: str
    commons_context: str
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


def _display_path(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)) if path.is_relative_to(REPO_ROOT) else str(path)

def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for doc in docs:
        for key in ("generatedAt", "created_at"):
            value = doc.get(key)
            if isinstance(value, str) and value:
                return value
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str) -> str:
    return {
        "emergent-watch": "watch",
        "convergence-rising": "watch",
        "field-birth-threshold": "docket",
        "legibility-risk": "docket",
        "require-human-review": "suppress",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise EmergentDomainInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise EmergentDomainInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise EmergentDomainInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise EmergentDomainInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise EmergentDomainInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )

    payload = _load_json(found[0])
    _validate_provenance(payload, path=found[0])
    return LoadedArtifact(path=found[0], payload=payload, source_mode="compatibility")


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise EmergentDomainInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise EmergentDomainInputError(f"Supporting audit missing non-empty schema in {path}")
    records = payload.get("records")
    if not isinstance(records, list):
        raise EmergentDomainInputError(f"Supporting audit missing records array in {path}")
    return payload


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture emergent-domain artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: emergent-domain inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    invariant_rows: dict[str, dict[str, Any]],
    pressure_rows: dict[str, dict[str, Any]],
    boundary_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> EmergentDomainDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "emergent-domain-context")

    domain_convergence = _clamp01(float(row.get("domainConvergence", 0.5)))
    novelty_consistency = _clamp01(float(row.get("noveltyConsistency", 0.5)))

    invariant = invariant_rows.get(target_id, {})
    invariant_strength = _clamp01(float(invariant.get("invariantStrength", 0.5)))
    cross_domain_replicability = _clamp01(float(invariant.get("crossDomainReplicability", 0.5)))

    pressure = pressure_rows.get(target_id, {})
    field_birth_pressure = _clamp01(float(pressure.get("fieldBirthPressure", 0.5)))
    social_legibility = _clamp01(float(pressure.get("socialLegibility", 0.5)))

    boundary = boundary_rows.get(target_id, {})
    boundary_failure_risk = _clamp01(float(boundary.get("boundaryFailureRisk", 0.5)))
    overclaim_pressure = _clamp01(float(boundary.get("overclaimPressure", 0.4)))
    canonization_signal = _clamp01(float(boundary.get("canonizationSignal", 0.4)))

    humility_score = _clamp01(1.0 - 0.5 * overclaim_pressure - 0.5 * canonization_signal)

    coherence_score = _clamp01(
        0.14 * domain_convergence
        + 0.14 * novelty_consistency
        + 0.16 * invariant_strength
        + 0.16 * cross_domain_replicability
        + 0.14 * field_birth_pressure
        + 0.12 * social_legibility
        + 0.14 * humility_score
    )
    risk_score = _clamp01(
        0.16 * boundary_failure_risk
        + 0.16 * overclaim_pressure
        + 0.14 * canonization_signal
        + 0.14 * (1.0 - social_legibility)
        + 0.14 * (1.0 - cross_domain_replicability)
        + 0.12 * field_birth_pressure
        + 0.14 * system_risk
    )

    if overclaim_pressure >= 0.80 or canonization_signal >= 0.80:
        status = "require-human-review"
        rule = "anti-overclaim-and-anti-premature-canon-gate"
    elif boundary_failure_risk >= 0.72 or social_legibility <= 0.34:
        status = "legibility-risk"
        rule = "legibility-risk-repair-before-escalation"
    elif (
        domain_convergence >= 0.74
        and invariant_strength >= 0.70
        and cross_domain_replicability >= 0.66
        and field_birth_pressure >= 0.66
        and social_legibility >= 0.56
        and overclaim_pressure <= 0.56
    ):
        status = "field-birth-threshold"
        rule = "bounded-field-birth-threshold"
    elif domain_convergence >= 0.62 and invariant_strength >= 0.58:
        status = "convergence-rising"
        rule = "convergence-rising-watch"
    else:
        status = "emergent-watch"
        rule = "emergent-watch-under-uncertainty"

    convergence_context = (
        f"domainConvergence={domain_convergence:.3f}, invariantStrength={invariant_strength:.3f}, noveltyConsistency={novelty_consistency:.3f}; "
        "emergent convergence remains provisional and humility-bound."
    )
    transfer_context = (
        f"crossDomainReplicability={cross_domain_replicability:.3f}, fieldBirthPressure={field_birth_pressure:.3f}, boundaryFailureRisk={boundary_failure_risk:.3f}; "
        "cross-domain convergence must remain bounded before field elevation."
    )
    curiosity_context = (
        f"socialLegibility={social_legibility:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "discovery is surfaced through legibility and civic translation, not dominance."
    )
    commons_context = (
        f"overclaimPressure={overclaim_pressure:.3f}, canonizationSignal={canonization_signal:.3f}; "
        "recommendations are bounded scientific-governance guidance and do not certify final or socially ratified truth claims without ratification pathways."
    )
    explanation = (
        f"Emergent-domain guidance is bounded scientific-governance guidance only. targetId={target_id}, "
        f"domainStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return EmergentDomainDecision(
        target_id=target_id,
        target_type=target_type,
        domain_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        convergence_context=convergence_context,
        transfer_context=transfer_context,
        curiosity_context=curiosity_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: EmergentDomainDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "domainStatus": d.domain_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "convergenceContext": d.convergence_context,
        "transferContext": d.transfer_context,
        "curiosityContext": d.curiosity_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    domain_map = _load_required_artifact(
        EMERGENT_DOMAIN_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "domain_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    invariant_report = _load_required_artifact(
        CROSS_DOMAIN_INVARIANT_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "invariant_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    pressure_report = _load_required_artifact(
        FIELD_BIRTH_PRESSURE_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "birth_pressure_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    boundary_map = _load_required_artifact(
        DOMAIN_BOUNDARY_FAILURE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "boundary_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    theory_transfer = _load_supporting_audit(THEORY_TRANSFER_AUDIT_PATH)
    value = _load_supporting_audit(VALUE_ALIGNMENT_AUDIT_PATH)
    curiosity = _load_supporting_audit(CURIOSITY_AUDIT_PATH)
    social = _load_supporting_audit(SOCIAL_ENTROPY_AUDIT_PATH)
    commons = _load_supporting_audit(COMMONS_PARTICIPATION_AUDIT_PATH)

    transfer_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(theory_transfer, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    value_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(value, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    curiosity_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(curiosity, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    social_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(social, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    commons_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(commons, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.20 * transfer_risk + 0.20 * value_risk + 0.20 * curiosity_risk + 0.20 * social_risk + 0.20 * commons_risk)

    invariant_rows = {str(r.get("targetId")): r for r in _parse_rows(invariant_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    pressure_rows = {str(r.get("targetId")): r for r in _parse_rows(pressure_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    boundary_rows = {str(r.get("targetId")): r for r in _parse_rows(boundary_map.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            invariant_rows=invariant_rows,
            pressure_rows=pressure_rows,
            boundary_rows=boundary_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(domain_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [domain_map, invariant_report, pressure_report, boundary_map]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(domain_map.payload, invariant_report.payload, pressure_report.payload, boundary_map.payload)

    metadata = {
        "inputMode": mode,
        "inputModeWarning": warning,
        "systemRisk": round(system_risk, 6),
        "inputArtifacts": [
            {
                "path": _display_path(a.path),
                "sourceMode": a.source_mode,
                "schemaVersion": str(a.payload.get("schemaVersion")),
                "producerRepo": str(a.payload.get("producerRepo")),
                "producerModule": str(a.payload.get("producerModule")),
                "producerCommit": str(a.payload.get("producerCommit")),
                "generatedAt": str(a.payload.get("generatedAt")),
            }
            for a in loaded
        ],
        "supportingAudits": [
            _display_path(THEORY_TRANSFER_AUDIT_PATH),
            _display_path(VALUE_ALIGNMENT_AUDIT_PATH),
            _display_path(CURIOSITY_AUDIT_PATH),
            _display_path(SOCIAL_ENTROPY_AUDIT_PATH),
            _display_path(COMMONS_PARTICIPATION_AUDIT_PATH),
        ],
    }

    phaselock = (
        "transfer / theory / prediction / curiosity / value / commons context -> CoherenceLattice emergent-domain formalization -> "
        "Sophia emergent-domain audit -> Publisher field-birth overlays -> human/community/scientific ratification pathways"
    )
    caution = (
        "Emergent-domain recommendations are bounded scientific-governance guidance only and do not certify a new field as final "
        "or socially ratified truth."
    )

    audit_payload = {
        "schema": "emergent_domain_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "emergent_domain_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(EMERGENT_DOMAIN_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(EMERGENT_DOMAIN_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia emergent-domain state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    EMERGENT_DOMAIN_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    EMERGENT_DOMAIN_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {EMERGENT_DOMAIN_AUDIT_OUT}")
    print(f"Wrote {EMERGENT_DOMAIN_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
