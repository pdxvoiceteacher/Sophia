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

RESPONSIBILITY_MODE_MAP_PATH = BRIDGE_DIR / "responsibility_mode_map.json"
SUPPORT_PATHWAY_MAP_PATH = BRIDGE_DIR / "support_pathway_map.json"
INTERVENTION_BOUNDARY_REPORT_PATH = BRIDGE_DIR / "intervention_boundary_report.json"
SANCTION_SUPPRESSION_GATE_PATH = BRIDGE_DIR / "sanction_suppression_gate.json"

AGENCY_MODE_AUDIT_PATH = BRIDGE_DIR / "agency_mode_audit.json"
THEORY_CORPUS_AUDIT_PATH = BRIDGE_DIR / "theory_corpus_audit.json"
EXPERIMENTAL_AUDIT_PATH = BRIDGE_DIR / "experimental_audit.json"
COLLABORATIVE_REVIEW_AUDIT_PATH = BRIDGE_DIR / "collaborative_review_audit.json"

RESPONSIBILITY_AUDIT_OUT = BRIDGE_DIR / "responsibility_audit.json"
RESPONSIBILITY_RECOMMENDATIONS_OUT = BRIDGE_DIR / "responsibility_recommendations.json"

RESPONSIBILITY_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "responsibility_audit_v1.schema.json"
RESPONSIBILITY_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "responsibility_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "responsibility_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class ResponsibilityInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class ResponsibilityDecision:
    target_id: str
    target_type: str
    responsibility_status: str
    coherence_score: float
    risk_score: float
    agency_context: str
    structural_constraint_context: str
    fairness_context: str
    intervention_context: str
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
        "support-first": "watch",
        "consent-first": "watch",
        "mixed-accountability": "docket",
        "sanction-suppressed": "suppress",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise ResponsibilityInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise ResponsibilityInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise ResponsibilityInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise ResponsibilityInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise ResponsibilityInputError(
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
        return "fixture", "Inputs are fixture responsibility artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: responsibility inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    support_rows: dict[str, dict[str, Any]],
    intervention_rows: dict[str, dict[str, Any]],
    sanction_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> ResponsibilityDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "responsibility-context")

    support_fit = _clamp01(float(row.get("supportFit", 0.5)))
    consent_fit = _clamp01(float(row.get("consentFit", 0.5)))
    accountability_need = _clamp01(float(row.get("accountabilityNeed", 0.5)))

    support = support_rows.get(target_id, {})
    pathway_readiness = _clamp01(float(support.get("pathwayReadiness", 0.5)))
    structural_constraint = _clamp01(float(support.get("structuralConstraint", 0.5)))

    intervention = intervention_rows.get(target_id, {})
    intervention_risk = _clamp01(float(intervention.get("interventionRisk", 0.5)))
    consent_clarity = _clamp01(float(intervention.get("consentClarity", 0.5)))

    gate = sanction_rows.get(target_id, {})
    deterministic_overreach = _clamp01(float(gate.get("deterministicOverreach", 0.4)))
    punitive_volitional = _clamp01(float(gate.get("punitiveVolitional", 0.4)))
    sanction_suppressed = bool(gate.get("sanctionSuppressed", False))

    fairness_score = _clamp01(1.0 - 0.5 * deterministic_overreach - 0.5 * punitive_volitional)

    coherence = _clamp01(
        0.17 * support_fit
        + 0.17 * consent_fit
        + 0.16 * pathway_readiness
        + 0.16 * consent_clarity
        + 0.18 * fairness_score
        + 0.16 * (1.0 - structural_constraint)
    )
    risk = _clamp01(
        0.20 * intervention_risk
        + 0.16 * structural_constraint
        + 0.16 * (1.0 - consent_clarity)
        + 0.16 * deterministic_overreach
        + 0.16 * punitive_volitional
        + 0.16 * system_risk
    )

    if sanction_suppressed:
        status = "sanction-suppressed"
        rule = "sanction-suppression-gate-active"
    elif deterministic_overreach >= 0.80 or punitive_volitional >= 0.80:
        status = "require-human-review"
        rule = "overreach-or-punitive-human-review"
    elif support_fit >= 0.65 and consent_fit < 0.55:
        status = "support-first"
        rule = "support-first-under-uncertainty"
    elif consent_fit >= 0.65 and support_fit < 0.55:
        status = "consent-first"
        rule = "consent-first-boundary-rule"
    elif accountability_need >= 0.60 and structural_constraint <= 0.70:
        status = "mixed-accountability"
        rule = "mixed-accountability-with-guardrails"
    else:
        status = "require-human-review"
        rule = "insufficient-boundary-fit"

    agency_context = (
        f"supportFit={support_fit:.3f}, consentFit={consent_fit:.3f}, accountabilityNeed={accountability_need:.3f}; "
        "support and consent remain co-primary where fit is uncertain."
    )
    structural_context = (
        f"pathwayReadiness={pathway_readiness:.3f}, structuralConstraint={structural_constraint:.3f}; "
        "high structural constraints reduce confidence and trigger restraint."
    )
    fairness_context = (
        f"deterministicOverreach={deterministic_overreach:.3f}, punitiveVolitional={punitive_volitional:.3f}, fairnessScore={fairness_score:.3f}; "
        "governance prevents deterministic overreach and punitive romanticism."
    )
    intervention_context = (
        f"interventionRisk={intervention_risk:.3f}, consentClarity={consent_clarity:.3f}, sanctionSuppressed={str(sanction_suppressed).lower()}; "
        "recommendations are bounded guidance and do not autonomously authorize sanctions or coercion."
    )
    explanation = (
        f"Responsibility guidance is bounded governance guidance only. targetId={target_id}, "
        f"responsibilityStatus={status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return ResponsibilityDecision(
        target_id=target_id,
        target_type=target_type,
        responsibility_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        agency_context=agency_context,
        structural_constraint_context=structural_context,
        fairness_context=fairness_context,
        intervention_context=intervention_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: ResponsibilityDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "responsibilityStatus": d.responsibility_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "agencyContext": d.agency_context,
        "structuralConstraintContext": d.structural_constraint_context,
        "fairnessContext": d.fairness_context,
        "interventionContext": d.intervention_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    mode_map = _load_required_artifact(
        RESPONSIBILITY_MODE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "responsibility_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    support_map = _load_required_artifact(
        SUPPORT_PATHWAY_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "support_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    intervention_report = _load_required_artifact(
        INTERVENTION_BOUNDARY_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "intervention_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    sanction_gate = _load_required_artifact(
        SANCTION_SUPPRESSION_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "sanction_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    agency = _load_json(AGENCY_MODE_AUDIT_PATH)
    theory = _load_json(THEORY_CORPUS_AUDIT_PATH)
    experimental = _load_json(EXPERIMENTAL_AUDIT_PATH)
    collaborative = _load_json(COLLABORATIVE_REVIEW_AUDIT_PATH)

    agency_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(agency, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    theory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(theory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    experimental_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(experimental, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    collaborative_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(collaborative, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.25 * agency_risk + 0.25 * theory_risk + 0.25 * experimental_risk + 0.25 * collaborative_risk)

    support_rows = {str(r.get("targetId")): r for r in _parse_rows(support_map.payload, "targets") if isinstance(r.get("targetId"), str)}
    intervention_rows = {str(r.get("targetId")): r for r in _parse_rows(intervention_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    sanction_rows = {str(r.get("targetId")): r for r in _parse_rows(sanction_gate.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            support_rows=support_rows,
            intervention_rows=intervention_rows,
            sanction_rows=sanction_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(mode_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [mode_map, support_map, intervention_report, sanction_gate]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(mode_map.payload, support_map.payload, intervention_report.payload, sanction_gate.payload)

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
        "agency-mode + theory + experimental + collaborative state -> responsibility/support/intervention synthesis -> "
        "Sophia responsibility audit -> Publisher bounded governance overlays -> human/community review"
    )
    caution = (
        "Responsibility recommendations are bounded governance guidance only and do not autonomously authorize sanctions, "
        "coercion, or moral condemnation."
    )

    audit_payload = {
        "schema": "responsibility_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "responsibility_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(RESPONSIBILITY_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(RESPONSIBILITY_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia responsibility state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    RESPONSIBILITY_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    RESPONSIBILITY_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {RESPONSIBILITY_AUDIT_OUT}")
    print(f"Wrote {RESPONSIBILITY_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
