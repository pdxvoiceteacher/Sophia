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

OPERATIONAL_MATURITY_MAP_PATH = BRIDGE_DIR / "operational_maturity_map.json"
DEPLOYMENT_BOUNDARY_REPORT_PATH = BRIDGE_DIR / "deployment_boundary_report.json"
TRANSLATION_RISK_REGISTER_PATH = BRIDGE_DIR / "translation_risk_register.json"
OPERATIONALIZATION_GATE_PATH = BRIDGE_DIR / "operationalization_gate.json"

EPISTEMIC_ATTRACTOR_AUDIT_PATH = BRIDGE_DIR / "epistemic_attractor_audit.json"
EMERGENT_DOMAIN_AUDIT_PATH = BRIDGE_DIR / "emergent_domain_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"

OPERATIONALIZATION_AUDIT_OUT = BRIDGE_DIR / "operationalization_audit.json"
OPERATIONALIZATION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "operationalization_recommendations.json"

OPERATIONALIZATION_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "operationalization_audit_v1.schema.json"
OPERATIONALIZATION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "operationalization_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "operationalization_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")
CANONICAL_INTEGRITY_FIELDS = (
    "originProject",
    "canonicalPhaselock",
    "modificationDisclosureRequired",
    "ethicalBoundaryNotice",
    "commonsIntegrityNotice",
    "constraintSignatureVersion",
    "constraintSignatureSha256",
)
IMMUTABLE_SAFETY_FIELDS = (
    "canonicalPhaselock",
    "ethicalBoundaryNotice",
    "commonsIntegrityNotice",
    "constraintSignatureVersion",
)


class OperationalizationInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class OperationalizationDecision:
    target_id: str
    target_type: str
    operational_status: str
    coherence_score: float
    risk_score: float
    maturity_context: str
    boundary_context: str
    translation_risk_context: str
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
        "research-only": "watch",
        "bounded-pilot": "docket",
        "translation-risk": "docket",
        "deployment-review": "docket",
        "require-human-review": "suppress",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise OperationalizationInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise OperationalizationInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise OperationalizationInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise OperationalizationInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise OperationalizationInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )

    payload = _load_json(found[0])
    _validate_provenance(payload, path=found[0])
    return LoadedArtifact(path=found[0], payload=payload, source_mode="compatibility")


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise OperationalizationInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise OperationalizationInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise OperationalizationInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise OperationalizationInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise OperationalizationInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise OperationalizationInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
    return manifest


def _build_canonical_integrity_metadata(artifacts: list[LoadedArtifact]) -> dict[str, Any]:
    manifests: list[dict[str, Any]] = []
    for artifact in artifacts:
        manifest = _extract_integrity_manifest(artifact.payload, path=artifact.path)
        if manifest is None:
            continue
        manifests.append({"path": _display_path(artifact.path), **manifest})

    if not manifests:
        return {"status": "absent", "warning": "No canonical integrity manifest fields found on operationalization artifacts.", "divergenceReasons": [], "manifests": []}

    baseline = manifests[0]
    reasons: list[str] = []
    for candidate in manifests[1:]:
        safety_changed = any(candidate[field] != baseline[field] for field in IMMUTABLE_SAFETY_FIELDS)
        same_sig = candidate["constraintSignatureSha256"] == baseline["constraintSignatureSha256"]
        if safety_changed and same_sig:
            reasons.append(f"{candidate['path']} changes immutable safety constraints without changing constraint signature")

    status = "divergent" if reasons else "canonical"
    warning = (
        "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical operationalization constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across operationalization artifacts."
    )
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture operationalization artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: operationalization inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    boundary_rows: dict[str, dict[str, Any]],
    translation_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> OperationalizationDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "operationalization-context")

    operational_maturity = _clamp01(float(row.get("operationalMaturity", 0.5)))
    safeguard_readiness = _clamp01(float(row.get("safeguardReadiness", 0.5)))

    boundary = boundary_rows.get(target_id, {})
    deployment_boundary_clarity = _clamp01(float(boundary.get("deploymentBoundaryClarity", 0.5)))
    coercive_amplification_risk = _clamp01(float(boundary.get("coerciveAmplificationRisk", 0.4)))
    dead_zone_adjacency = _clamp01(float(boundary.get("deadZoneAdjacency", 0.4)))

    translation = translation_rows.get(target_id, {})
    institutional_translation_risk = _clamp01(float(translation.get("institutionalTranslationRisk", 0.5)))
    governance_override_risk = _clamp01(float(translation.get("governanceOverrideRisk", 0.4)))

    gate = gate_rows.get(target_id, {})
    operational_gate_score = _clamp01(float(gate.get("operationalGateScore", 0.5)))
    auto_deployment_signal = _clamp01(float(gate.get("automaticDeploymentSignal", 0.4)))

    humility_score = _clamp01(1.0 - 0.5 * auto_deployment_signal - 0.5 * governance_override_risk)

    coherence_score = _clamp01(
        0.14 * operational_maturity
        + 0.14 * safeguard_readiness
        + 0.14 * deployment_boundary_clarity
        + 0.14 * (1.0 - institutional_translation_risk)
        + 0.14 * operational_gate_score
        + 0.14 * (1.0 - dead_zone_adjacency)
        + 0.16 * humility_score
    )
    risk_score = _clamp01(
        0.14 * institutional_translation_risk
        + 0.14 * governance_override_risk
        + 0.14 * coercive_amplification_risk
        + 0.14 * dead_zone_adjacency
        + 0.14 * auto_deployment_signal
        + 0.14 * (1.0 - deployment_boundary_clarity)
        + 0.16 * system_risk
    )

    if auto_deployment_signal >= 0.80 or governance_override_risk >= 0.80 or coercive_amplification_risk >= 0.80:
        status = "require-human-review"
        rule = "anti-coercion-and-anti-automatic-deployment-gate"
    elif dead_zone_adjacency >= 0.72:
        status = "translation-risk"
        rule = "dead-zone-adjacency-suppression"
    elif institutional_translation_risk >= 0.68:
        status = "translation-risk"
        rule = "translation-risk-containment"
    elif operational_gate_score >= 0.68 and deployment_boundary_clarity >= 0.62 and safeguard_readiness >= 0.62:
        status = "deployment-review"
        rule = "deployment-review-with-explicit-safeguards"
    elif operational_maturity >= 0.56 and safeguard_readiness >= 0.56:
        status = "bounded-pilot"
        rule = "bounded-pilot-under-review"
    else:
        status = "research-only"
        rule = "research-only-until-maturity"

    maturity_context = (
        f"operationalMaturity={operational_maturity:.3f}, safeguardReadiness={safeguard_readiness:.3f}, operationalGateScore={operational_gate_score:.3f}; "
        "discoveries may be epistemically strong yet socially immature for deployment."
    )
    boundary_context = (
        f"deploymentBoundaryClarity={deployment_boundary_clarity:.3f}, deadZoneAdjacency={dead_zone_adjacency:.3f}; "
        "bounded pilots and explicit safeguards are favored over deployment enthusiasm."
    )
    translation_risk_context = (
        f"institutionalTranslationRisk={institutional_translation_risk:.3f}, governanceOverrideRisk={governance_override_risk:.3f}, automaticDeploymentSignal={auto_deployment_signal:.3f}; "
        "translation remains legible and non-coercive, never automatic."
    )
    commons_context = (
        f"coerciveAmplificationRisk={coercive_amplification_risk:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "recommendations are bounded deployment-stewardship guidance only and do not authorize automatic implementation, governance override, or coercive operationalization."
    )
    explanation = (
        f"Operationalization guidance is bounded deployment-stewardship guidance only. targetId={target_id}, "
        f"operationalStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return OperationalizationDecision(
        target_id=target_id,
        target_type=target_type,
        operational_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        maturity_context=maturity_context,
        boundary_context=boundary_context,
        translation_risk_context=translation_risk_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: OperationalizationDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "operationalStatus": d.operational_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "maturityContext": d.maturity_context,
        "boundaryContext": d.boundary_context,
        "translationRiskContext": d.translation_risk_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    maturity_map = _load_required_artifact(
        OPERATIONAL_MATURITY_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "maturity_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    boundary_report = _load_required_artifact(
        DEPLOYMENT_BOUNDARY_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "boundary_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    translation_register = _load_required_artifact(
        TRANSLATION_RISK_REGISTER_PATH,
        compatibility_paths=(BRIDGE_DIR / "translation_register.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    gate = _load_required_artifact(
        OPERATIONALIZATION_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "deployment_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    attractor = _load_supporting_audit(EPISTEMIC_ATTRACTOR_AUDIT_PATH)
    emergent = _load_supporting_audit(EMERGENT_DOMAIN_AUDIT_PATH)
    sovereignty = _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)
    memory = _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)
    value = _load_supporting_audit(VALUE_ALIGNMENT_AUDIT_PATH)

    attractor_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(attractor, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    emergent_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(emergent, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    sovereignty_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(sovereignty, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    memory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(memory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    value_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(value, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.20 * attractor_risk + 0.20 * emergent_risk + 0.20 * sovereignty_risk + 0.20 * memory_risk + 0.20 * value_risk)

    boundary_rows = {str(r.get("targetId")): r for r in _parse_rows(boundary_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    translation_rows = {str(r.get("targetId")): r for r in _parse_rows(translation_register.payload, "targets") if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(gate.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            boundary_rows=boundary_rows,
            translation_rows=translation_rows,
            gate_rows=gate_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(maturity_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [maturity_map, boundary_report, translation_register, gate]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(maturity_map.payload, boundary_report.payload, translation_register.payload, gate.payload)
    canonical_integrity = _build_canonical_integrity_metadata(loaded)

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
        "canonicalIntegrity": canonical_integrity,
        "supportingAudits": [
            _display_path(EPISTEMIC_ATTRACTOR_AUDIT_PATH),
            _display_path(EMERGENT_DOMAIN_AUDIT_PATH),
            _display_path(COMMONS_SOVEREIGNTY_AUDIT_PATH),
            _display_path(CIVILIZATIONAL_MEMORY_AUDIT_PATH),
            _display_path(VALUE_ALIGNMENT_AUDIT_PATH),
        ],
    }

    phaselock = (
        "attractor / basin / dead-zone / memory / sovereignty / value context -> CoherenceLattice operational maturity and deployment-boundary formalization -> "
        "Sophia bounded operationalization audit -> Publisher deployment-maturity overlays -> human/community/scientific/institutional deliberation"
    )
    caution = (
        "Operationalization recommendations are bounded deployment-stewardship guidance only and do not authorize automatic implementation, "
        "governance override, or coercive operationalization."
    )

    audit_payload = {
        "schema": "operationalization_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "operationalization_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(OPERATIONALIZATION_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(OPERATIONALIZATION_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia operationalization state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    OPERATIONALIZATION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    OPERATIONALIZATION_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {OPERATIONALIZATION_AUDIT_OUT}")
    print(f"Wrote {OPERATIONALIZATION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
