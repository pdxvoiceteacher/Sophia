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

EVIDENCE_AUTHORITY_MAP_PATH = BRIDGE_DIR / "evidence_authority_map.json"
EVIDENCE_AUTHORITY_SUMMARY_PATH = BRIDGE_DIR / "evidence_authority_summary.json"
PROPAGATION_RIGHTS_MAP_PATH = BRIDGE_DIR / "propagation_rights_map.json"
MATURITY_GATE_REPORT_PATH = BRIDGE_DIR / "maturity_gate_report.json"

VERIFICATION_AUDIT_PATH = BRIDGE_DIR / "verification_audit.json"
PUBLIC_RECORD_AUDIT_PATH = BRIDGE_DIR / "public_record_audit.json"
SYMBOLIC_FIELD_AUDIT_PATH = BRIDGE_DIR / "symbolic_field_audit.json"
INVESTIGATION_AUDIT_PATH = BRIDGE_DIR / "investigation_audit.json"
CLOSURE_AUDIT_PATH = BRIDGE_DIR / "closure_audit.json"
PRECEDENT_AUDIT_PATH = BRIDGE_DIR / "precedent_audit.json"

EVIDENCE_AUTHORITY_AUDIT_OUT = BRIDGE_DIR / "evidence_authority_audit.json"
EVIDENCE_AUTHORITY_RECOMMENDATIONS_OUT = BRIDGE_DIR / "evidence_authority_recommendations.json"

EVIDENCE_AUTHORITY_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "evidence_authority_audit_v1.schema.json"
EVIDENCE_AUTHORITY_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "evidence_authority_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "evidence_authority_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class EvidenceAuthorityInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class EvidenceAuthorityDecision:
    target_id: str
    target_type: str
    authority_status: str
    coherence_score: float
    risk_score: float
    maturity_context: str
    claim_context: str
    entity_context: str
    contradiction_context: str
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
        "within-bounds": "docket",
        "over-propagated": "watch",
        "verify-first": "suppress",
        "restrict-propagation": "suppress",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise EvidenceAuthorityInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")

    schema_version = str(payload.get("schemaVersion"))
    if schema_version != SUPPORTED_SCHEMA_VERSION:
        raise EvidenceAuthorityInputError(
            f"Unsupported schemaVersion in {path}: {schema_version}; supported={SUPPORTED_SCHEMA_VERSION}"
        )

    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise EvidenceAuthorityInputError(
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
        raise EvidenceAuthorityInputError(f"Missing required canonical artifact: {canonical_path}")

    if not allow_compatibility_names:
        names = ", ".join(str(path) for path in available_compat)
        raise EvidenceAuthorityInputError(
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
        return "fixture", "Inputs are fixture evidence-authority artifacts; output is non-canonical simulation guidance."
    return (
        "mixed",
        "MIXED MODE WARNING: evidence-authority inputs combine live and fixture producers; review provenance before action.",
    )


def evaluate_target(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    rights_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> EvidenceAuthorityDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "authority-target")

    evidence_maturity = _clamp01(float(row.get("evidenceMaturity", summary.get("meanEvidenceMaturity", 0.5))))
    authority_level = _clamp01(float(row.get("authorityLevel", summary.get("meanAuthorityLevel", 0.45))))
    propagation_exposure = _clamp01(float(row.get("propagationExposure", summary.get("meanPropagationExposure", 0.4))))

    rights = rights_rows.get(target_id, {})
    propagation_right = _clamp01(float(rights.get("propagationRight", rights.get("rightsScore", summary.get("meanPropagationRight", 0.45)))))
    entity_ambiguity = _clamp01(float(rights.get("entityAmbiguity", summary.get("meanEntityAmbiguity", 0.45))))

    gate = gate_rows.get(target_id, {})
    gate_severity = _clamp01(float(gate.get("gateSeverity", summary.get("meanGateSeverity", 0.45))))
    contradiction_score = _clamp01(float(gate.get("contradictionScore", summary.get("meanContradictionScore", 0.4))))
    verification_readiness = _clamp01(float(gate.get("verificationReadiness", summary.get("meanVerificationReadiness", 0.5))))

    over_propagation = _clamp01(max(0.0, authority_level - evidence_maturity))

    coherence = _clamp01(
        0.34 * evidence_maturity
        + 0.16 * verification_readiness
        + 0.18 * propagation_right
        + 0.12 * (1.0 - contradiction_score)
        + 0.12 * (1.0 - gate_severity)
        + 0.08 * (1.0 - entity_ambiguity)
    )
    risk = _clamp01(
        0.28 * over_propagation
        + 0.18 * gate_severity
        + 0.18 * contradiction_score
        + 0.12 * (1.0 - verification_readiness)
        + 0.12 * entity_ambiguity
        + 0.12 * system_risk
    )

    if contradiction_score >= 0.82 and gate_severity >= 0.72:
        authority_status = "require-human-review"
        governing_rule = "stacked-contradiction-human-review"
    elif evidence_maturity <= 0.34 and (authority_level >= 0.70 or propagation_exposure >= 0.70):
        authority_status = "restrict-propagation"
        governing_rule = "restrict-weak-evidence-high-reach"
    elif verification_readiness <= 0.36 or gate_severity >= 0.74:
        authority_status = "verify-first"
        governing_rule = "verification-gate-first"
    elif over_propagation >= 0.22 or (propagation_exposure >= 0.62 and evidence_maturity <= 0.55):
        authority_status = "over-propagated"
        governing_rule = "over-propagation-detection"
    else:
        authority_status = "within-bounds"
        governing_rule = "authority-within-evidence-bounds"

    maturity_context = (
        f"evidenceMaturity={evidence_maturity:.3f}, authorityLevel={authority_level:.3f}, propagationExposure={propagation_exposure:.3f}; "
        "authority should not exceed evidence maturity."
    )
    claim_context = (
        f"verificationReadiness={verification_readiness:.3f}, gateSeverity={gate_severity:.3f}; "
        "claims remain provisional until verification gates are satisfied."
    )
    entity_context = (
        f"propagationRight={propagation_right:.3f}, entityAmbiguity={entity_ambiguity:.3f}; "
        "identity and relationship inferences remain reviewable and bounded."
    )
    contradiction_context = (
        f"contradictionScore={contradiction_score:.3f}, overPropagation={over_propagation:.3f}, systemRisk={system_risk:.3f}; "
        "propagation rights are constrained under contradiction risk."
    )

    explanation = (
        f"Evidence-authority guidance is bounded institutional guidance only. targetId={target_id}, "
        f"authorityStatus={authority_status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return EvidenceAuthorityDecision(
        target_id=target_id,
        target_type=target_type,
        authority_status=authority_status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        maturity_context=maturity_context,
        claim_context=claim_context,
        entity_context=entity_context,
        contradiction_context=contradiction_context,
        governing_rule=governing_rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(authority_status),
    )


def _to_payload(decision: EvidenceAuthorityDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "authorityStatus": decision.authority_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "maturityContext": decision.maturity_context,
        "claimContext": decision.claim_context,
        "entityContext": decision.entity_context,
        "contradictionContext": decision.contradiction_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    authority_map_artifact = _load_required_artifact(
        EVIDENCE_AUTHORITY_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "evidence_authority.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    authority_summary_artifact = _load_required_artifact(
        EVIDENCE_AUTHORITY_SUMMARY_PATH,
        compatibility_paths=(BRIDGE_DIR / "authority_summary.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    rights_map_artifact = _load_required_artifact(
        PROPAGATION_RIGHTS_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "propagation_rights.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    maturity_gate_artifact = _load_required_artifact(
        MATURITY_GATE_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "maturity_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    authority_map = authority_map_artifact.payload
    authority_summary = authority_summary_artifact.payload
    rights_map = rights_map_artifact.payload
    maturity_gate = maturity_gate_artifact.payload

    verification = _load_json(VERIFICATION_AUDIT_PATH)
    public_record = _load_json(PUBLIC_RECORD_AUDIT_PATH)
    symbolic_field = _load_json(SYMBOLIC_FIELD_AUDIT_PATH)
    investigation = _load_json(INVESTIGATION_AUDIT_PATH)
    closure = _load_json(CLOSURE_AUDIT_PATH)
    precedent = _load_json(PRECEDENT_AUDIT_PATH)

    verification_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(verification, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    public_record_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(public_record, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    symbolic_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(symbolic_field, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    investigation_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(investigation, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    closure_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(closure, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    precedent_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(precedent, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)

    system_risk = _clamp01(
        0.20 * verification_risk
        + 0.18 * public_record_risk
        + 0.18 * symbolic_risk
        + 0.16 * investigation_risk
        + 0.14 * closure_risk
        + 0.14 * precedent_risk
    )

    rights_rows = {str(row.get("targetId")): row for row in _parse_rows(rights_map, "targets") if isinstance(row.get("targetId"), str)}
    gate_rows = {str(row.get("targetId")): row for row in _parse_rows(maturity_gate, "targets") if isinstance(row.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            summary=authority_summary,
            rights_rows=rights_rows,
            gate_rows=gate_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(authority_map, "targets")
    ]
    decisions = sorted(decisions, key=lambda decision: decision.target_id)

    loaded = [authority_map_artifact, authority_summary_artifact, rights_map_artifact, maturity_gate_artifact]
    input_mode, input_warning = _classify_input_mode(loaded)
    created_at = _resolve_created_at(authority_map, authority_summary, rights_map, maturity_gate)

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
        "claim / entity / graph / closure / precedent / investigation state -> "
        "CoherenceLattice evidence-authority formalization -> Sophia evidence-authority audit -> "
        "Publisher authority-gating overlays -> human/community review of propagation limits"
    )
    caution = (
        "Evidence-authority recommendations are bounded institutional guidance only and do not "
        "automatically rewrite graph edges, identities, precedents, or closures."
    )

    audit_payload = {
        "schema": "evidence_authority_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(decision) for decision in decisions],
    }
    recommendations_payload = {
        "schema": "evidence_authority_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(decision) for decision in decisions],
    }

    Draft202012Validator(_load_json(EVIDENCE_AUTHORITY_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(EVIDENCE_AUTHORITY_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia evidence-authority state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    EVIDENCE_AUTHORITY_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    EVIDENCE_AUTHORITY_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"Wrote {EVIDENCE_AUTHORITY_AUDIT_OUT}")
    print(f"Wrote {EVIDENCE_AUTHORITY_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
