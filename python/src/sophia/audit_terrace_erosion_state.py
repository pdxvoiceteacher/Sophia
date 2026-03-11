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

TERRACE_EROSION_MAP_PATH = BRIDGE_DIR / "terrace_erosion_map.json"
ORTHODOXY_PRESSURE_REPORT_PATH = BRIDGE_DIR / "orthodoxy_pressure_report.json"
RENEWAL_CORRIDOR_REGISTRY_PATH = BRIDGE_DIR / "renewal_corridor_registry.json"
EPOCHAL_TRANSITION_FORECAST_PATH = BRIDGE_DIR / "epochal_transition_forecast.json"

EPOCHAL_TERRACE_AUDIT_PATH = BRIDGE_DIR / "epochal_terrace_audit.json"
CIVILIZATIONAL_DELTA_AUDIT_PATH = BRIDGE_DIR / "civilizational_delta_audit.json"
KNOWLEDGE_RIVER_AUDIT_PATH = BRIDGE_DIR / "knowledge_river_audit.json"
TRUST_SURFACE_AUDIT_PATH = BRIDGE_DIR / "trust_surface_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"

TERRACE_EROSION_AUDIT_OUT = BRIDGE_DIR / "terrace_erosion_audit.json"
TERRACE_EROSION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "terrace_erosion_recommendations.json"

TERRACE_EROSION_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "terrace_erosion_audit_v1.schema.json"
TERRACE_EROSION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "terrace_erosion_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "terrace_erosion_v1"
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


class TerraceErosionInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class TerraceErosionDecision:
    target_id: str
    target_type: str
    erosion_status: str
    coherence_score: float
    risk_score: float
    terrace_context: str
    orthodoxy_context: str
    renewal_context: str
    transition_context: str
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
    if status == "orthodoxy-risk":
        return "suppress" if risk_score >= 0.82 else "watch"
    if status in {"phase-transition-watch", "renewal-visible", "erosion-local"}:
        return "watch"
    return {"plurality-repair": "docket", "require-human-review": "docket"}[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise TerraceErosionInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise TerraceErosionInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise TerraceErosionInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path) -> LoadedArtifact:
    if not path.exists():
        raise TerraceErosionInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise TerraceErosionInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise TerraceErosionInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise TerraceErosionInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise TerraceErosionInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise TerraceErosionInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise TerraceErosionInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
    return manifest


def _build_canonical_integrity_metadata(artifacts: list[LoadedArtifact]) -> dict[str, Any]:
    manifests: list[dict[str, Any]] = []
    for artifact in artifacts:
        manifest = _extract_integrity_manifest(artifact.payload, path=artifact.path)
        if manifest is None:
            continue
        manifests.append({"path": _display_path(artifact.path), **manifest})
    if not manifests:
        return {"status": "absent", "warning": "No canonical integrity manifest fields found on terrace-erosion artifacts.", "divergenceReasons": [], "manifests": []}
    baseline = manifests[0]
    reasons: list[str] = []
    for candidate in manifests[1:]:
        if any(candidate[f] != baseline[f] for f in IMMUTABLE_SAFETY_FIELDS) and candidate["constraintSignatureSha256"] == baseline["constraintSignatureSha256"]:
            reasons.append(f"{candidate['path']} changes immutable safety constraints without changing constraint signature")
    status = "divergent" if reasons else "canonical"
    warning = "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical terrace-erosion constraints." if reasons else "Canonical integrity manifest present and internally consistent across terrace-erosion artifacts."
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def evaluate_target(
    row: dict[str, Any],
    *,
    orthodoxy_rows: dict[str, dict[str, Any]],
    renewal_rows: dict[str, dict[str, Any]],
    transition_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> TerraceErosionDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "terrace")

    local_erosion = _clamp01(float(row.get("localErosionScore", 0.5)))
    synchronized_erosion = _clamp01(float(row.get("synchronizedErosionScore", 0.5)))
    plurality_retention = _clamp01(float(row.get("pluralityRetentionScore", 0.5)))

    orth = orthodoxy_rows.get(target_id, {})
    orthodoxy_pressure = _clamp01(float(orth.get("orthodoxyPressureScore", 0.5)))

    renew = renewal_rows.get(target_id, {})
    renewal_corridor_strength = _clamp01(float(renew.get("renewalCorridorStrengthScore", 0.5)))
    trust_repair_capacity = _clamp01(float(renew.get("boundedTrustRepairScore", 0.5)))

    trans = transition_rows.get(target_id, {})
    transition_signal = _clamp01(float(trans.get("transitionSignalScore", 0.5)))
    collapse_narrative_risk = _clamp01(float(trans.get("collapseNarrativeRiskScore", 0.5)))

    coherence_score = _clamp01(
        0.18 * (1.0 - local_erosion)
        + 0.14 * (1.0 - synchronized_erosion)
        + 0.18 * plurality_retention
        + 0.16 * (1.0 - orthodoxy_pressure)
        + 0.18 * renewal_corridor_strength
        + 0.16 * (1.0 - support_risk)
    )
    risk_score = _clamp01(
        0.14 * local_erosion
        + 0.18 * synchronized_erosion
        + 0.16 * orthodoxy_pressure
        + 0.14 * (1.0 - plurality_retention)
        + 0.12 * (1.0 - trust_repair_capacity)
        + 0.10 * transition_signal
        + 0.08 * collapse_narrative_risk
        + 0.08 * trust_surface_risk
    )

    if orthodoxy_pressure >= 0.70 and plurality_retention < 0.56:
        status = "orthodoxy-risk"
        rule = "orthodoxy-pressure-with-low-plurality"
    elif synchronized_erosion >= 0.70 and transition_signal >= 0.66 and trust_surface_risk < 0.70:
        status = "phase-transition-watch"
        rule = "synchronized-erosion-transition-watch"
    elif renewal_corridor_strength >= 0.70 and trust_repair_capacity >= 0.64 and trust_surface_risk < 0.66:
        status = "renewal-visible"
        rule = "renewal-corridor-visible-under-bounded-trust-repair"
    elif local_erosion >= 0.62 and synchronized_erosion < 0.60:
        status = "erosion-local"
        rule = "local-erosion-without-sync-escalation"
    elif plurality_retention < 0.60 or trust_repair_capacity < 0.52:
        status = "plurality-repair"
        rule = "plurality-and-repair-corridor-strengthening"
    else:
        status = "require-human-review"
        rule = "insufficient-erosion-legibility"

    terrace_context = (
        f"localErosionScore={local_erosion:.3f}, synchronizedErosionScore={synchronized_erosion:.3f}, pluralityRetentionScore={plurality_retention:.3f}; "
        "isolated erosion does not escalate to phase-transition-watch without cross-terrace synchronization."
    )
    orthodoxy_context = (
        f"orthodoxyPressureScore={orthodoxy_pressure:.3f}; orthodoxy pressure plus low plurality retention biases toward orthodoxy-risk."
    )
    renewal_context = (
        f"renewalCorridorStrengthScore={renewal_corridor_strength:.3f}, boundedTrustRepairScore={trust_repair_capacity:.3f}; "
        "strong renewal corridors with bounded trust repair may route to renewal-visible."
    )
    transition_context = (
        f"transitionSignalScore={transition_signal:.3f}, collapseNarrativeRiskScore={collapse_narrative_risk:.3f}, trustSurfaceRisk={trust_surface_risk:.3f}; "
        "phase-transition guidance remains watch-level and bounded."
    )
    commons_context = (
        f"supportRisk={support_risk:.3f}; recommendations remain non-coercive and non-centralizing across delta, river, sovereignty, memory, and value context."
    )
    explanation = (
        "Recommendations are bounded renewal-stewardship guidance only and do not declare epoch collapse, authorize regime change, or canonize successor systems. "
        "Recommendations do not authorize institutional overthrow, coercive transition, or centralized replacement. "
        f"targetId={target_id}, erosionStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return TerraceErosionDecision(
        target_id=target_id,
        target_type=target_type,
        erosion_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        terrace_context=terrace_context,
        orthodoxy_context=orthodoxy_context,
        renewal_context=renewal_context,
        transition_context=transition_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: TerraceErosionDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "erosionStatus": d.erosion_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "terraceContext": d.terrace_context,
        "orthodoxyContext": d.orthodoxy_context,
        "renewalContext": d.renewal_context,
        "transitionContext": d.transition_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    erosion_map = _load_required_artifact(TERRACE_EROSION_MAP_PATH)
    orthodoxy_report = _load_required_artifact(ORTHODOXY_PRESSURE_REPORT_PATH)
    renewal_registry = _load_required_artifact(RENEWAL_CORRIDOR_REGISTRY_PATH)
    transition_forecast = _load_required_artifact(EPOCHAL_TRANSITION_FORECAST_PATH)

    supporting = [
        ("epochal terrace", _load_supporting_audit(EPOCHAL_TERRACE_AUDIT_PATH)),
        ("civilizational delta", _load_supporting_audit(CIVILIZATIONAL_DELTA_AUDIT_PATH)),
        ("knowledge river", _load_supporting_audit(KNOWLEDGE_RIVER_AUDIT_PATH)),
        ("trust surface", _load_supporting_audit(TRUST_SURFACE_AUDIT_PATH)),
        ("civilizational memory", _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)),
        ("commons sovereignty", _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)),
        ("value alignment", _load_supporting_audit(VALUE_ALIGNMENT_AUDIT_PATH)),
    ]
    supporting_risks = [_safe_mean([float(r.get("riskScore")) for r in _parse_rows(p, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45) for _, p in supporting]
    support_risk = _clamp01(_safe_mean(supporting_risks, 0.45))
    trust_surface_risk = _clamp01(supporting_risks[3])

    orthodoxy_rows = {str(r.get("targetId")): r for r in _parse_rows(orthodoxy_report.payload) if isinstance(r.get("targetId"), str)}
    renewal_rows = {str(r.get("targetId")): r for r in _parse_rows(renewal_registry.payload) if isinstance(r.get("targetId"), str)}
    transition_rows = {str(r.get("targetId")): r for r in _parse_rows(transition_forecast.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            orthodoxy_rows=orthodoxy_rows,
            renewal_rows=renewal_rows,
            transition_rows=transition_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(erosion_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [erosion_map, orthodoxy_report, renewal_registry, transition_forecast]
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
        "terrace / delta / river / trust / sovereignty / value context -> CoherenceLattice erosion and renewal formalization -> "
        "Sophia bounded erosion audit -> Publisher erosion/renewal overlays -> human/community/scientific stewardship of brittle epochs and emerging renewal"
    )
    caution = (
        "Recommendations are bounded renewal-stewardship guidance only and do not declare epoch collapse, authorize regime change, "
        "or canonize successor systems."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "terrace_erosion_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "terrace_erosion_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(TERRACE_EROSION_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(TERRACE_EROSION_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia terrace-erosion state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    TERRACE_EROSION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    TERRACE_EROSION_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {TERRACE_EROSION_AUDIT_OUT}")
    print(f"Wrote {TERRACE_EROSION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
