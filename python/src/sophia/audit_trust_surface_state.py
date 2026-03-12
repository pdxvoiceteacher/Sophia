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

TRUST_SURFACE_MAP_PATH = BRIDGE_DIR / "trust_surface_map.json"
DELEGATED_ACCESS_REGISTRY_PATH = BRIDGE_DIR / "delegated_access_registry.json"
REVOCATION_ASYMMETRY_REPORT_PATH = BRIDGE_DIR / "revocation_asymmetry_report.json"
INTERFACE_LEGITIMACY_RISK_REPORT_PATH = BRIDGE_DIR / "interface_legitimacy_risk_report.json"

OBSERVER_ONBOARDING_AUDIT_PATH = BRIDGE_DIR / "observer_onboarding_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"

TRUST_SURFACE_AUDIT_OUT = BRIDGE_DIR / "trust_surface_audit.json"
TRUST_SURFACE_RECOMMENDATIONS_OUT = BRIDGE_DIR / "trust_surface_recommendations.json"

TRUST_SURFACE_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "trust_surface_audit_v1.schema.json"
TRUST_SURFACE_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "trust_surface_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "trust_surface_v1"
EXPECTED_PRODUCER_REPOS = {"Sophia", "Sophia-Fixtures"}
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


class TrustSurfaceInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class TrustSurfaceDecision:
    target_id: str
    target_type: str
    trust_surface_status: str
    coherence_score: float
    risk_score: float
    legitimacy_context: str
    revocation_context: str
    wrapper_context: str
    audit_burden_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_rows(payload: dict[str, Any], key: str = "targets") -> list[dict[str, Any]]:
    rows = payload.get(key)
    return [r for r in rows if isinstance(r, dict)] if isinstance(rows, list) else []


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


def _status_to_action(status: str, risk_score: float, revocation_asymmetry: float) -> str:
    if status == "wrapper-provenance-risk":
        return "suppress" if risk_score >= 0.82 else "watch"
    if status == "revocation-asymmetry-risk":
        return "watch" if revocation_asymmetry >= 0.70 else "docket"
    return {
        "trust-surface-stable": "watch",
        "legitimacy-risk": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise TrustSurfaceInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise TrustSurfaceInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise TrustSurfaceInputError(
            f"Unexpected producerRepo in {path}: {producer_repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path) -> LoadedArtifact:
    if not path.exists():
        raise TrustSurfaceInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise TrustSurfaceInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise TrustSurfaceInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise TrustSurfaceInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise TrustSurfaceInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")

    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise TrustSurfaceInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise TrustSurfaceInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
    return manifest


def _build_canonical_integrity_metadata(artifacts: list[LoadedArtifact]) -> dict[str, Any]:
    manifests: list[dict[str, Any]] = []
    for artifact in artifacts:
        manifest = _extract_integrity_manifest(artifact.payload, path=artifact.path)
        if manifest is None:
            continue
        manifests.append({"path": _display_path(artifact.path), **manifest})

    if not manifests:
        return {
            "status": "absent",
            "warning": "No canonical integrity manifest fields found on trust-surface artifacts.",
            "divergenceReasons": [],
            "manifests": [],
        }

    baseline = manifests[0]
    reasons: list[str] = []
    for candidate in manifests[1:]:
        safety_changed = any(candidate[field] != baseline[field] for field in IMMUTABLE_SAFETY_FIELDS)
        same_sig = candidate["constraintSignatureSha256"] == baseline["constraintSignatureSha256"]
        if safety_changed and same_sig:
            reasons.append(f"{candidate['path']} changes immutable safety constraints without changing constraint signature")

    status = "divergent" if reasons else "canonical"
    warning = (
        "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical trust-surface constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across trust-surface artifacts."
    )
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def evaluate_target(
    row: dict[str, Any],
    *,
    delegated_rows: dict[str, dict[str, Any]],
    revocation_rows: dict[str, dict[str, Any]],
    legitimacy_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> TrustSurfaceDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "interface")

    consent_legibility = _clamp01(float(row.get("consentLegibilityScore", 0.5)))
    trust_compression = _clamp01(float(row.get("trustCompressionRisk", 0.5)))

    delegated = delegated_rows.get(target_id, {})
    wrapper_lineage_clarity = _clamp01(float(delegated.get("wrapperLineageClarityScore", 0.5)))
    provenance_traceability = _clamp01(float(delegated.get("provenanceTraceabilityScore", 0.5)))
    wrapper_obscurity = _clamp01(1.0 - _safe_mean([wrapper_lineage_clarity, provenance_traceability], 0.5))

    revocation = revocation_rows.get(target_id, {})
    revocation_asymmetry = _clamp01(float(revocation.get("revocationAsymmetryScore", 0.5)))
    multisystem_investigation = bool(revocation.get("multiSystemInvestigationRequired", False))
    revocation_steps = _clamp01(float(revocation.get("revocationProcessComplexityScore", 0.5)))

    legitimacy = legitimacy_rows.get(target_id, {})
    interface_legitimacy_risk = _clamp01(float(legitimacy.get("interfaceLegitimacyRiskScore", 0.5)))

    audit_burden_score = _clamp01(0.55 * revocation_steps + 0.45 * (1.0 if multisystem_investigation else 0.0))

    coherence_score = _clamp01(
        0.24 * consent_legibility
        + 0.18 * (1.0 - trust_compression)
        + 0.18 * wrapper_lineage_clarity
        + 0.14 * provenance_traceability
        + 0.12 * (1.0 - revocation_asymmetry)
        + 0.14 * (1.0 - interface_legitimacy_risk)
    )
    risk_score = _clamp01(
        0.20 * (1.0 - consent_legibility)
        + 0.18 * trust_compression
        + 0.16 * wrapper_obscurity
        + 0.14 * revocation_asymmetry
        + 0.14 * interface_legitimacy_risk
        + 0.08 * audit_burden_score
        + 0.10 * system_risk
    )

    if wrapper_lineage_clarity < 0.34 or provenance_traceability < 0.34 or wrapper_obscurity >= 0.70:
        status = "wrapper-provenance-risk"
        rule = "wrapper-lineage-obscurity-gate"
    elif revocation_asymmetry >= 0.82 or (multisystem_investigation and audit_burden_score >= 0.72):
        status = "require-human-review"
        rule = "revocation-asymmetry-human-review"
    elif revocation_asymmetry >= 0.64:
        status = "revocation-asymmetry-risk"
        rule = "revocation-asymmetry-watch"
    elif consent_legibility <= 0.42 or interface_legitimacy_risk >= 0.64 or trust_compression >= 0.70:
        status = "legitimacy-risk"
        rule = "consent-legibility-and-trust-compression-gate"
    else:
        status = "trust-surface-stable"
        rule = "bounded-legitimacy-stability"

    legitimacy_context = (
        f"consentLegibilityScore={consent_legibility:.3f}, trustCompressionRisk={trust_compression:.3f}, "
        f"interfaceLegitimacyRiskScore={interface_legitimacy_risk:.3f}; structural legitimacy is prioritized over individual blame."
    )
    revocation_context = (
        f"revocationAsymmetryScore={revocation_asymmetry:.3f}, revocationProcessComplexityScore={revocation_steps:.3f}, "
        f"multiSystemInvestigationRequired={str(multisystem_investigation).lower()}; high revocation asymmetry routes to watch or review."
    )
    wrapper_context = (
        f"wrapperLineageClarityScore={wrapper_lineage_clarity:.3f}, provenanceTraceabilityScore={provenance_traceability:.3f}, wrapperObscurity={wrapper_obscurity:.3f}; "
        "wrapper lineage obscurity raises provenance risk and trust caution."
    )
    audit_burden_context = (
        f"auditBurdenScore={audit_burden_score:.3f}; escalation applies when revocation requires multi-system investigation and elevated verification burden."
    )
    explanation = (
        "Trust-surface audits provide bounded legitimacy guidance only and do not imply wrongdoing or authorize enforcement. "
        f"targetId={target_id}, trustSurfaceStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return TrustSurfaceDecision(
        target_id=target_id,
        target_type=target_type,
        trust_surface_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        legitimacy_context=legitimacy_context,
        revocation_context=revocation_context,
        wrapper_context=wrapper_context,
        audit_burden_context=audit_burden_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score, revocation_asymmetry),
    )


def _to_payload(d: TrustSurfaceDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "trustSurfaceStatus": d.trust_surface_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "legitimacyContext": d.legitimacy_context,
        "revocationContext": d.revocation_context,
        "wrapperContext": d.wrapper_context,
        "auditBurdenContext": d.audit_burden_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    trust_surface_map = _load_required_artifact(TRUST_SURFACE_MAP_PATH)
    delegated_access_registry = _load_required_artifact(DELEGATED_ACCESS_REGISTRY_PATH)
    revocation_asymmetry_report = _load_required_artifact(REVOCATION_ASYMMETRY_REPORT_PATH)
    interface_legitimacy_risk_report = _load_required_artifact(INTERFACE_LEGITIMACY_RISK_REPORT_PATH)

    supporting = [
        ("observer onboarding", _load_supporting_audit(OBSERVER_ONBOARDING_AUDIT_PATH)),
        ("commons sovereignty", _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)),
        ("civilizational memory", _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)),
    ]
    system_risk = _clamp01(
        _safe_mean(
            [
                _safe_mean([float(r.get("riskScore")) for r in _parse_rows(payload, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
                for _, payload in supporting
            ],
            0.45,
        )
    )

    delegated_rows = {str(r.get("targetId")): r for r in _parse_rows(delegated_access_registry.payload) if isinstance(r.get("targetId"), str)}
    revocation_rows = {str(r.get("targetId")): r for r in _parse_rows(revocation_asymmetry_report.payload) if isinstance(r.get("targetId"), str)}
    legitimacy_rows = {str(r.get("targetId")): r for r in _parse_rows(interface_legitimacy_risk_report.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            delegated_rows=delegated_rows,
            revocation_rows=revocation_rows,
            legitimacy_rows=legitimacy_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(trust_surface_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [trust_surface_map, delegated_access_registry, revocation_asymmetry_report, interface_legitimacy_risk_report]
    metadata = {
        "systemRisk": round(system_risk, 6),
        "inputArtifacts": [
            {
                "path": _display_path(a.path),
                "schemaVersion": str(a.payload.get("schemaVersion")),
                "producerRepo": str(a.payload.get("producerRepo")),
                "producerModule": str(a.payload.get("producerModule")),
                "producerCommit": str(a.payload.get("producerCommit")),
                "generatedAt": str(a.payload.get("generatedAt")),
            }
            for a in loaded
        ],
        "canonicalIntegrity": _build_canonical_integrity_metadata(loaded),
        "supportingAudits": [name for name, _ in supporting],
    }

    phaselock = (
        "trust surface map + delegated access + revocation asymmetry + interface legitimacy context -> "
        "CoherenceLattice trust-surface formalization -> Sophia bounded trust-surface audit -> "
        "publisher trust overlays + human/community review"
    )
    caution = "Trust-surface audits provide bounded legitimacy guidance only and do not imply wrongdoing or authorize enforcement."
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "trust_surface_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "trust_surface_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(TRUST_SURFACE_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(TRUST_SURFACE_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia trust-surface state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    TRUST_SURFACE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    TRUST_SURFACE_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {TRUST_SURFACE_AUDIT_OUT}")
    print(f"Wrote {TRUST_SURFACE_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
