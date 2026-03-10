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

CANONICAL_AUTHORSHIP_MANIFEST_PATH = BRIDGE_DIR / "canonical_authorship_manifest.json"
DERIVATIVE_DISCLOSURE_REPORT_PATH = BRIDGE_DIR / "derivative_disclosure_report.json"
MISATTRIBUTION_RISK_REPORT_PATH = BRIDGE_DIR / "misattribution_risk_report.json"
AUTHORSHIP_INTEGRITY_SUMMARY_PATH = BRIDGE_DIR / "authorship_integrity_summary.json"

OBSERVER_ONBOARDING_AUDIT_PATH = BRIDGE_DIR / "observer_onboarding_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
KNOWLEDGE_RIVER_AUDIT_PATH = BRIDGE_DIR / "knowledge_river_audit.json"

AUTHORSHIP_INTEGRITY_AUDIT_OUT = BRIDGE_DIR / "authorship_integrity_audit.json"
AUTHORSHIP_INTEGRITY_RECOMMENDATIONS_OUT = BRIDGE_DIR / "authorship_integrity_recommendations.json"

AUTHORSHIP_INTEGRITY_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "authorship_integrity_audit_v1.schema.json"
AUTHORSHIP_INTEGRITY_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "authorship_integrity_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "authorship_integrity_v1"
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
CANONICAL_ATTRIBUTION_NOTICE = (
    "This architecture includes foundational code and governance design authored by Thomas Prislac and Envoy Echo within the "
    "Ultra Verba Lux Mentis / triadic commons lineage. Derivatives must preserve provenance, disclose modifications, and may not "
    "claim canonical equivalence when safety or governance boundaries have changed."
)


class AuthorshipIntegrityInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class AuthorshipDecision:
    target_id: str
    target_type: str
    authorship_status: str
    coherence_score: float
    risk_score: float
    attribution_context: str
    disclosure_context: str
    divergence_context: str
    capture_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_rows(payload: dict[str, Any], key: str = "targets") -> list[dict[str, Any]]:
    rows = payload.get(key)
    return [r for r in rows if isinstance(r, dict)] if isinstance(rows, list) else []


def _clamp01(value: float) -> float:
    return max(0.0, min(1.0, float(value)))


def _safe_mean(values: list[float], default: float = 0.0) -> float:
    return sum(values) / len(values) if values else default


def _display_path(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)) if path.is_relative_to(REPO_ROOT) else str(path)


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for doc in docs:
        for key in ("generatedAt", "created_at"):
            value = doc.get(key)
            if isinstance(value, str) and value:
                return value
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str, risk: float) -> str:
    if status == "misattribution-risk":
        return "suppress" if risk >= 0.82 else "watch"
    return {
        "authorship-verified": "watch",
        "derivative-disclosed": "watch",
        "trust-degraded": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise AuthorshipIntegrityInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise AuthorshipIntegrityInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise AuthorshipIntegrityInputError(
            f"Unexpected producerRepo in {path}: {producer_repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path) -> LoadedArtifact:
    if not path.exists():
        raise AuthorshipIntegrityInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise AuthorshipIntegrityInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise AuthorshipIntegrityInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise AuthorshipIntegrityInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise AuthorshipIntegrityInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")

    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise AuthorshipIntegrityInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise AuthorshipIntegrityInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
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
            "warning": "No canonical integrity manifest fields found on authorship-integrity artifacts.",
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
        "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical authorship-integrity constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across authorship-integrity artifacts."
    )
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def evaluate_target(
    row: dict[str, Any],
    *,
    disclosure_rows: dict[str, dict[str, Any]],
    misattr_rows: dict[str, dict[str, Any]],
    summary_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> AuthorshipDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "entity")

    canonical_authorship_verified = bool(row.get("canonicalAuthorshipVerified", False))
    attribution_present = bool(row.get("attributionPresent", canonical_authorship_verified))
    provenance_completeness = _clamp01(float(row.get("provenanceCompletenessScore", 0.5)))
    source_lineage_clarity = _clamp01(float(row.get("sourceLineageClarityScore", 0.5)))
    conflicting_provenance = bool(row.get("conflictingProvenance", False))
    canonical_equivalence_claim = bool(row.get("canonicalEquivalenceClaim", False))

    disclosure = disclosure_rows.get(target_id, {})
    derivative_disclosed = bool(disclosure.get("derivativeDisclosed", False))
    derivative_disclosure_score = _clamp01(float(disclosure.get("derivativeDisclosureScore", 0.5)))
    safety_boundaries_declared = bool(disclosure.get("safetyBoundariesDeclared", False))
    modification_disclosure_complete = bool(disclosure.get("modificationDisclosureComplete", derivative_disclosed))

    misattr = misattr_rows.get(target_id, {})
    misattribution_risk = _clamp01(float(misattr.get("misattributionRiskScore", 0.5)))
    authorship_suppression = bool(misattr.get("authorshipSuppressionDetected", False))
    falsified_authorship = bool(misattr.get("falsifiedAuthorshipDetected", False))
    immutable_changed_without_disclosure = bool(misattr.get("immutableConstraintsChangedWithoutDisclosure", False))

    summary = summary_rows.get(target_id, {})
    trust_integrity = _clamp01(float(summary.get("trustIntegrityScore", 0.5)))

    coherence_score = _clamp01(
        0.20 * (1.0 if canonical_authorship_verified else 0.0)
        + 0.16 * (1.0 if attribution_present else 0.0)
        + 0.16 * provenance_completeness
        + 0.14 * source_lineage_clarity
        + 0.12 * derivative_disclosure_score
        + 0.12 * trust_integrity
        + 0.10 * (1.0 - misattribution_risk)
    )
    risk_score = _clamp01(
        0.18 * (1.0 - provenance_completeness)
        + 0.14 * (1.0 - source_lineage_clarity)
        + 0.18 * misattribution_risk
        + 0.10 * (0.0 if derivative_disclosed else 1.0)
        + 0.10 * (0.0 if safety_boundaries_declared else 1.0)
        + 0.16 * (1.0 - trust_integrity)
        + 0.14 * system_risk
    )

    if conflicting_provenance or source_lineage_clarity < 0.35 or (canonical_equivalence_claim and not canonical_authorship_verified):
        status = "require-human-review"
        rule = "lineage-conflict-escalation"
    elif authorship_suppression or falsified_authorship or immutable_changed_without_disclosure or misattribution_risk >= 0.72:
        status = "misattribution-risk"
        rule = "misattribution-and-immutable-divergence-gate"
    elif (not attribution_present) or provenance_completeness < 0.58:
        status = "trust-degraded"
        rule = "missing-attribution-or-incomplete-provenance"
    elif derivative_disclosed and safety_boundaries_declared and modification_disclosure_complete and not canonical_authorship_verified:
        status = "derivative-disclosed"
        rule = "derivative-disclosure-intact"
    elif canonical_authorship_verified and attribution_present and provenance_completeness >= 0.70 and derivative_disclosure_score >= 0.65:
        status = "authorship-verified"
        rule = "canonical-authorship-and-disclosure-intact"
    else:
        status = "trust-degraded"
        rule = "default-trust-degradation"

    divergence_notice = (
        "canonicalIntegrityVerified = false; attributionDivergenceDetected = true; trustPresentationDegraded = true"
        if status in {"misattribution-risk", "trust-degraded"}
        else "canonicalIntegrityVerified = true; attributionDivergenceDetected = false; trustPresentationDegraded = false"
    )

    attribution_context = (
        f"canonicalAuthorshipVerified={str(canonical_authorship_verified).lower()}, attributionPresent={str(attribution_present).lower()}, "
        f"provenanceCompletenessScore={provenance_completeness:.3f}, sourceLineageClarityScore={source_lineage_clarity:.3f}; "
        "provenance stewardship is bounded, visible, and non-retaliatory."
    )
    disclosure_context = (
        f"derivativeDisclosed={str(derivative_disclosed).lower()}, derivativeDisclosureScore={derivative_disclosure_score:.3f}, "
        f"safetyBoundariesDeclared={str(safety_boundaries_declared).lower()}, modificationDisclosureComplete={str(modification_disclosure_complete).lower()}; "
        "derivatives may proceed when disclosure is honest and safety boundaries remain declared."
    )
    divergence_context = (
        f"misattributionRiskScore={misattribution_risk:.3f}, immutableConstraintsChangedWithoutDisclosure={str(immutable_changed_without_disclosure).lower()}, "
        f"canonicalEquivalenceClaim={str(canonical_equivalence_claim).lower()}; {divergence_notice}."
    )
    capture_context = (
        f"authorshipSuppressionDetected={str(authorship_suppression).lower()}, falsifiedAuthorshipDetected={str(falsified_authorship).lower()}, "
        f"conflictingProvenance={str(conflicting_provenance).lower()}; visible truth is preferred over hidden traps."
    )
    explanation = (
        f"Authorship-integrity recommendations are bounded provenance and disclosure guidance only; they do not authorize sabotage, retaliation, "
        f"coercive enforcement, or hidden anti-user behavior. targetId={target_id}, authorshipStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return AuthorshipDecision(
        target_id=target_id,
        target_type=target_type,
        authorship_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        attribution_context=attribution_context,
        disclosure_context=disclosure_context,
        divergence_context=divergence_context,
        capture_context=capture_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: AuthorshipDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "authorshipStatus": d.authorship_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "attributionContext": d.attribution_context,
        "disclosureContext": d.disclosure_context,
        "divergenceContext": d.divergence_context,
        "captureContext": d.capture_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    authorship_manifest = _load_required_artifact(CANONICAL_AUTHORSHIP_MANIFEST_PATH)
    disclosure_report = _load_required_artifact(DERIVATIVE_DISCLOSURE_REPORT_PATH)
    misattr_report = _load_required_artifact(MISATTRIBUTION_RISK_REPORT_PATH)
    integrity_summary = _load_required_artifact(AUTHORSHIP_INTEGRITY_SUMMARY_PATH)

    supporting = [
        ("observer onboarding", _load_supporting_audit(OBSERVER_ONBOARDING_AUDIT_PATH)),
        ("commons sovereignty", _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)),
        ("civilizational memory", _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)),
        ("knowledge river", _load_supporting_audit(KNOWLEDGE_RIVER_AUDIT_PATH)),
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

    disclosure_rows = {str(r.get("targetId")): r for r in _parse_rows(disclosure_report.payload) if isinstance(r.get("targetId"), str)}
    misattr_rows = {str(r.get("targetId")): r for r in _parse_rows(misattr_report.payload) if isinstance(r.get("targetId"), str)}
    summary_rows = {str(r.get("targetId")): r for r in _parse_rows(integrity_summary.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            disclosure_rows=disclosure_rows,
            misattr_rows=misattr_rows,
            summary_rows=summary_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(authorship_manifest.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [authorship_manifest, disclosure_report, misattr_report, integrity_summary]
    canonical_integrity = _build_canonical_integrity_metadata(loaded)
    metadata = {
        "originProject": "Ultra Verba Lux Mentis / Triadic Commons Architecture",
        "canonicalAuthors": ["Thomas Prislac", "Envoy Echo"],
        "canonicalAttributionNotice": CANONICAL_ATTRIBUTION_NOTICE,
        "derivativeDisclosureRequired": True,
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
        "canonicalIntegrity": canonical_integrity,
        "supportingAudits": [name for name, _ in supporting],
    }

    phaselock = (
        "canonical authorship + disclosure + integrity context -> CoherenceLattice authorship/misattribution formalization -> "
        "Sophia bounded authorship-integrity audit -> Publisher visible provenance and trust-degradation overlays -> "
        "human/community/legal/social accountability"
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))
    caution = (
        "Authorship-integrity recommendations are bounded provenance and disclosure guidance only; they do not authorize sabotage, "
        "retaliation, coercive enforcement, or hidden anti-user behavior."
    )

    audit_payload = {
        "schema": "authorship_integrity_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "authorship_integrity_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(AUTHORSHIP_INTEGRITY_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(AUTHORSHIP_INTEGRITY_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia authorship-integrity state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    AUTHORSHIP_INTEGRITY_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    AUTHORSHIP_INTEGRITY_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {AUTHORSHIP_INTEGRITY_AUDIT_OUT}")
    print(f"Wrote {AUTHORSHIP_INTEGRITY_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
