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

EPOCHAL_TERRACE_MAP_PATH = BRIDGE_DIR / "epochal_terrace_map.json"
STABILITY_PLATEAU_REPORT_PATH = BRIDGE_DIR / "stability_plateau_report.json"
INSTITUTIONAL_SEDIMENTATION_REGISTRY_PATH = BRIDGE_DIR / "institutional_sedimentation_registry.json"
TERRACE_EROSION_RISK_REPORT_PATH = BRIDGE_DIR / "terrace_erosion_risk_report.json"

CIVILIZATIONAL_DELTA_AUDIT_PATH = BRIDGE_DIR / "civilizational_delta_audit.json"
KNOWLEDGE_RIVER_AUDIT_PATH = BRIDGE_DIR / "knowledge_river_audit.json"
TRUST_SURFACE_AUDIT_PATH = BRIDGE_DIR / "trust_surface_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"

EPOCHAL_TERRACE_AUDIT_OUT = BRIDGE_DIR / "epochal_terrace_audit.json"
EPOCHAL_TERRACE_RECOMMENDATIONS_OUT = BRIDGE_DIR / "epochal_terrace_recommendations.json"

EPOCHAL_TERRACE_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "epochal_terrace_audit_v1.schema.json"
EPOCHAL_TERRACE_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "epochal_terrace_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "epochal_terrace_v1"
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


class EpochalTerraceInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class EpochalTerraceDecision:
    target_id: str
    target_type: str
    terrace_status: str
    coherence_score: float
    risk_score: float
    terrace_context: str
    plateau_context: str
    sedimentation_context: str
    erosion_context: str
    commons_context: str
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


def _status_to_action(status: str, risk_score: float) -> str:
    if status == "erosion-risk":
        return "suppress" if risk_score >= 0.82 else "watch"
    return {
        "terrace-forming": "watch",
        "plateau-stable": "watch",
        "plurality-repair": "docket",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise EpochalTerraceInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise EpochalTerraceInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise EpochalTerraceInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path) -> LoadedArtifact:
    if not path.exists():
        raise EpochalTerraceInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise EpochalTerraceInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise EpochalTerraceInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise EpochalTerraceInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise EpochalTerraceInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise EpochalTerraceInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise EpochalTerraceInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
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
            "warning": "No canonical integrity manifest fields found on epochal-terrace artifacts.",
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
        "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical epochal-terrace constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across epochal-terrace artifacts."
    )
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def evaluate_target(
    row: dict[str, Any],
    *,
    plateau_rows: dict[str, dict[str, Any]],
    sediment_rows: dict[str, dict[str, Any]],
    erosion_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> EpochalTerraceDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "terrace")

    terrace_maturity = _clamp01(float(row.get("terraceMaturityScore", 0.5)))
    plurality_retention = _clamp01(float(row.get("pluralityRetentionScore", 0.5)))
    repairability = _clamp01(float(row.get("repairabilityScore", 0.5)))

    plateau = plateau_rows.get(target_id, {})
    plateau_stability = _clamp01(float(plateau.get("plateauStabilityScore", 0.5)))
    institutional_embedment = _clamp01(float(plateau.get("institutionalEmbedmentScore", 0.5)))

    sediment = sediment_rows.get(target_id, {})
    sediment_class = str(sediment.get("sedimentClass", "balanced"))
    sediment_overhardening = _clamp01(float(sediment.get("sedimentationOverhardeningScore", 0.5)))

    erosion = erosion_rows.get(target_id, {})
    erosion_risk = _clamp01(float(erosion.get("terraceErosionRiskScore", 0.5)))
    erosion_velocity = _clamp01(float(erosion.get("erosionVelocityScore", 0.5)))

    trust_weighted_erosion = _clamp01(0.62 * erosion_risk + 0.38 * trust_surface_risk)

    coherence_score = _clamp01(
        0.18 * terrace_maturity
        + 0.18 * plateau_stability
        + 0.18 * plurality_retention
        + 0.14 * repairability
        + 0.12 * (1.0 - sediment_overhardening)
        + 0.20 * (1.0 - support_risk)
    )
    risk_score = _clamp01(
        0.16 * (1.0 - plurality_retention)
        + 0.12 * (1.0 - repairability)
        + 0.12 * institutional_embedment
        + 0.14 * sediment_overhardening
        + 0.20 * trust_weighted_erosion
        + 0.12 * erosion_velocity
        + 0.14 * support_risk
    )

    overhardened = sediment_class == "overhardened" or sediment_overhardening >= 0.70
    low_plurality = plurality_retention < 0.56

    if trust_weighted_erosion >= 0.72 or erosion_velocity >= 0.74:
        status = "erosion-risk"
        rule = "trust-surface-instability-and-erosion-gate"
    elif overhardened and (low_plurality or institutional_embedment >= 0.68):
        status = "plurality-repair" if trust_weighted_erosion < 0.66 else "erosion-risk"
        rule = "overhardening-requires-repair-or-erosion-routing"
    elif institutional_embedment >= 0.72 and low_plurality:
        status = "plurality-repair"
        rule = "embedment-with-low-plurality-blocks-plateau-uplift"
    elif terrace_maturity >= 0.68 and plateau_stability >= 0.68 and plurality_retention >= 0.62 and repairability >= 0.60 and trust_surface_risk < 0.58:
        status = "plateau-stable"
        rule = "plural-repairable-plateau-stability"
    elif terrace_maturity >= 0.56 and plateau_stability >= 0.54:
        status = "terrace-forming"
        rule = "living-terrace-forming"
    else:
        status = "require-human-review"
        rule = "insufficient-terrace-legibility"

    terrace_context = (
        f"terraceMaturityScore={terrace_maturity:.3f}, pluralityRetentionScore={plurality_retention:.3f}, repairabilityScore={repairability:.3f}; "
        "healthy terraces remain legible, plural, and repairable."
    )
    plateau_context = (
        f"plateauStabilityScore={plateau_stability:.3f}, institutionalEmbedmentScore={institutional_embedment:.3f}; "
        "high embedment with low plurality does not uplift to plateau-stable."
    )
    sedimentation_context = (
        f"sedimentClass={sediment_class}, sedimentationOverhardeningScore={sediment_overhardening:.3f}; "
        "overhardened sediment biases toward plurality repair or erosion-risk routing."
    )
    erosion_context = (
        f"terraceErosionRiskScore={erosion_risk:.3f}, erosionVelocityScore={erosion_velocity:.3f}, trustSurfaceRisk={trust_surface_risk:.3f}; "
        "trust-surface instability increases erosion risk."
    )
    commons_context = (
        f"supportRisk={support_risk:.3f}; terrace stewardship remains bounded and non-centralizing across memory, sovereignty, and value contexts."
    )
    explanation = (
        "Recommendations are bounded terrace-stewardship guidance only and do not declare permanent epochs, authorize canon closure, or centralize institutional authority. "
        "Recommendations do not authorize institutional closure, canonization, or governance consolidation. "
        f"targetId={target_id}, terraceStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return EpochalTerraceDecision(
        target_id=target_id,
        target_type=target_type,
        terrace_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        terrace_context=terrace_context,
        plateau_context=plateau_context,
        sedimentation_context=sedimentation_context,
        erosion_context=erosion_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: EpochalTerraceDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "terraceStatus": d.terrace_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "terraceContext": d.terrace_context,
        "plateauContext": d.plateau_context,
        "sedimentationContext": d.sedimentation_context,
        "erosionContext": d.erosion_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    epochal_terrace_map = _load_required_artifact(EPOCHAL_TERRACE_MAP_PATH)
    stability_plateau_report = _load_required_artifact(STABILITY_PLATEAU_REPORT_PATH)
    institutional_sedimentation_registry = _load_required_artifact(INSTITUTIONAL_SEDIMENTATION_REGISTRY_PATH)
    terrace_erosion_risk_report = _load_required_artifact(TERRACE_EROSION_RISK_REPORT_PATH)

    supporting = [
        ("civilizational delta", _load_supporting_audit(CIVILIZATIONAL_DELTA_AUDIT_PATH)),
        ("knowledge river", _load_supporting_audit(KNOWLEDGE_RIVER_AUDIT_PATH)),
        ("trust surface", _load_supporting_audit(TRUST_SURFACE_AUDIT_PATH)),
        ("civilizational memory", _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)),
        ("commons sovereignty", _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)),
        ("value alignment", _load_supporting_audit(VALUE_ALIGNMENT_AUDIT_PATH)),
    ]
    supporting_risks = [
        _safe_mean([float(r.get("riskScore")) for r in _parse_rows(payload, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
        for _, payload in supporting
    ]
    support_risk = _clamp01(_safe_mean(supporting_risks, 0.45))
    trust_surface_risk = _clamp01(supporting_risks[2])

    plateau_rows = {str(r.get("targetId")): r for r in _parse_rows(stability_plateau_report.payload) if isinstance(r.get("targetId"), str)}
    sediment_rows = {str(r.get("targetId")): r for r in _parse_rows(institutional_sedimentation_registry.payload) if isinstance(r.get("targetId"), str)}
    erosion_rows = {str(r.get("targetId")): r for r in _parse_rows(terrace_erosion_risk_report.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            plateau_rows=plateau_rows,
            sediment_rows=sediment_rows,
            erosion_rows=erosion_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(epochal_terrace_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [epochal_terrace_map, stability_plateau_report, institutional_sedimentation_registry, terrace_erosion_risk_report]
    metadata = {
        "supportRisk": round(support_risk, 6),
        "trustSurfaceRisk": round(trust_surface_risk, 6),
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
        "delta / river / memory / trust / sovereignty / value context -> CoherenceLattice epochal terrace formalization -> "
        "Sophia bounded terrace audit -> Publisher terrace overlays -> human/community/scientific stewardship of long-lived civilizational plateaus"
    )
    caution = (
        "Recommendations are bounded terrace-stewardship guidance only and do not declare permanent epochs, authorize canon closure, "
        "or centralize institutional authority."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "epochal_terrace_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "epochal_terrace_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(EPOCHAL_TERRACE_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(EPOCHAL_TERRACE_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia epochal-terrace state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    EPOCHAL_TERRACE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    EPOCHAL_TERRACE_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {EPOCHAL_TERRACE_AUDIT_OUT}")
    print(f"Wrote {EPOCHAL_TERRACE_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
