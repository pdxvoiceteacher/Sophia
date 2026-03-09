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

KNOWLEDGE_RIVER_MAP_PATH = BRIDGE_DIR / "knowledge_river_map.json"
CORRIDOR_BRAIDING_REPORT_PATH = BRIDGE_DIR / "corridor_braiding_report.json"
TRIBUTARY_SUPPORT_REGISTRY_PATH = BRIDGE_DIR / "tributary_support_registry.json"
RIVER_CAPTURE_RISK_REPORT_PATH = BRIDGE_DIR / "river_capture_risk_report.json"

DISCOVERY_NAVIGATION_AUDIT_PATH = BRIDGE_DIR / "discovery_navigation_audit.json"
EPISTEMIC_ATTRACTOR_AUDIT_PATH = BRIDGE_DIR / "epistemic_attractor_audit.json"
OPERATIONALIZATION_AUDIT_PATH = BRIDGE_DIR / "operationalization_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"

KNOWLEDGE_RIVER_AUDIT_OUT = BRIDGE_DIR / "knowledge_river_audit.json"
KNOWLEDGE_RIVER_RECOMMENDATIONS_OUT = BRIDGE_DIR / "knowledge_river_recommendations.json"

KNOWLEDGE_RIVER_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "knowledge_river_audit_v1.schema.json"
KNOWLEDGE_RIVER_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "knowledge_river_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "knowledge_river_v1"
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


class KnowledgeRiverInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class KnowledgeRiverDecision:
    target_id: str
    target_type: str
    river_status: str
    coherence_score: float
    risk_score: float
    river_context: str
    braid_context: str
    tributary_context: str
    capture_context: str
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
        "river-forming": "watch",
        "braid-stable": "docket",
        "tributary-strengthen": "docket",
        "capture-risk": "suppress",
        "require-human-review": "suppress",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise KnowledgeRiverInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise KnowledgeRiverInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise KnowledgeRiverInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise KnowledgeRiverInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise KnowledgeRiverInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )

    payload = _load_json(found[0])
    _validate_provenance(payload, path=found[0])
    return LoadedArtifact(path=found[0], payload=payload, source_mode="compatibility")


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise KnowledgeRiverInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise KnowledgeRiverInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise KnowledgeRiverInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise KnowledgeRiverInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")

    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise KnowledgeRiverInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise KnowledgeRiverInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
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
            "warning": "No canonical integrity manifest fields found on knowledge-river artifacts.",
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
        "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical knowledge-river constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across knowledge-river artifacts."
    )
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture knowledge-river artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: knowledge-river inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    braid_rows: dict[str, dict[str, Any]],
    tributary_rows: dict[str, dict[str, Any]],
    capture_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> KnowledgeRiverDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "knowledge-river-context")

    river_coherence = _clamp01(float(row.get("riverCoherence", 0.5)))
    flow_plurality = _clamp01(float(row.get("flowPlurality", 0.5)))
    river_legibility = _clamp01(float(row.get("riverLegibility", 0.5)))

    braid = braid_rows.get(target_id, {})
    braid_stability = _clamp01(float(braid.get("braidStability", 0.5)))
    braid_legibility = _clamp01(float(braid.get("braidLegibility", 0.5)))
    corridor_redundancy = _clamp01(float(braid.get("corridorRedundancy", 0.5)))

    tributary = tributary_rows.get(target_id, {})
    tributary_support = _clamp01(float(tributary.get("tributarySupport", 0.5)))
    dissent_preservation = _clamp01(float(tributary.get("dissentPreservation", 0.6)))
    minority_legibility = _clamp01(float(tributary.get("minorityLegibility", 0.5)))

    capture = capture_rows.get(target_id, {})
    capture_risk = _clamp01(float(capture.get("captureRisk", 0.4)))
    centralization_pressure = _clamp01(float(capture.get("centralizationPressure", 0.4)))
    priesthood_pressure = _clamp01(float(capture.get("priesthoodPressure", 0.3)))
    canon_closure_risk = _clamp01(float(capture.get("canonClosureRisk", 0.3)))
    monopolization_risk = _clamp01(float(capture.get("monopolizationRisk", 0.4)))
    commons_irrigation = _clamp01(float(capture.get("commonsIrrigation", 0.5)))
    value_alignment_support = _clamp01(float(capture.get("valueAlignmentSupport", 0.5)))

    coherence_score = _clamp01(
        0.16 * river_coherence
        + 0.14 * flow_plurality
        + 0.10 * river_legibility
        + 0.15 * braid_stability
        + 0.10 * braid_legibility
        + 0.10 * corridor_redundancy
        + 0.13 * tributary_support
        + 0.12 * dissent_preservation
    )
    risk_score = _clamp01(
        0.17 * capture_risk
        + 0.15 * centralization_pressure
        + 0.14 * priesthood_pressure
        + 0.14 * canon_closure_risk
        + 0.12 * monopolization_risk
        + 0.10 * (1.0 - dissent_preservation)
        + 0.08 * (1.0 - commons_irrigation)
        + 0.10 * system_risk
    )

    if priesthood_pressure >= 0.72 or canon_closure_risk >= 0.72:
        status = "require-human-review"
        rule = "anti-priesthood-and-canon-closure-suppression"
    elif capture_risk >= 0.72 or centralization_pressure >= 0.72 or monopolization_risk >= 0.72:
        status = "capture-risk"
        rule = "anti-capture-suppression"
    elif tributary_support < 0.52 or dissent_preservation < 0.56:
        status = "tributary-strengthen"
        rule = "tributary-support-and-dissent-preservation"
    elif (
        river_coherence >= 0.64
        and flow_plurality >= 0.62
        and braid_stability >= 0.64
        and braid_legibility >= 0.60
        and corridor_redundancy >= 0.60
        and tributary_support >= 0.58
        and dissent_preservation >= 0.62
        and capture_risk <= 0.50
        and centralization_pressure <= 0.52
    ):
        status = "braid-stable"
        rule = "braided-river-stability-gate"
    elif river_coherence >= 0.56 and flow_plurality >= 0.54 and braid_stability >= 0.54:
        status = "river-forming"
        rule = "river-forming-observability-gate"
    else:
        status = "tributary-strengthen"
        rule = "tributary-first-default"

    river_context = (
        f"riverCoherence={river_coherence:.3f}, flowPlurality={flow_plurality:.3f}, riverLegibility={river_legibility:.3f}; "
        "knowledge rivers are bounded public learning channels, not sovereignty claims."
    )
    braid_context = (
        f"braidStability={braid_stability:.3f}, braidLegibility={braid_legibility:.3f}, corridorRedundancy={corridor_redundancy:.3f}; "
        "healthy rivers carry many strands forward without hardening into monopoly."
    )
    tributary_context = (
        f"tributarySupport={tributary_support:.3f}, dissentPreservation={dissent_preservation:.3f}, minorityLegibility={minority_legibility:.3f}; "
        "tributaries and dissent remain protected as first-class scientific alternatives."
    )
    capture_context = (
        f"captureRisk={capture_risk:.3f}, centralizationPressure={centralization_pressure:.3f}, priesthoodPressure={priesthood_pressure:.3f}, canonClosureRisk={canon_closure_risk:.3f}, monopolizationRisk={monopolization_risk:.3f}; "
        "capture and canon-closure signals trigger suppression and review."
    )
    commons_context = (
        f"commonsIrrigation={commons_irrigation:.3f}, valueAlignmentSupport={value_alignment_support:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "recommendations are bounded knowledge-stewardship guidance only and do not authorize canonization, centralized control, deployment authority, or closure of scientific alternatives."
    )
    explanation = (
        f"Knowledge-river guidance is bounded knowledge-stewardship guidance only. targetId={target_id}, "
        f"riverStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return KnowledgeRiverDecision(
        target_id=target_id,
        target_type=target_type,
        river_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        river_context=river_context,
        braid_context=braid_context,
        tributary_context=tributary_context,
        capture_context=capture_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: KnowledgeRiverDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "riverStatus": d.river_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "riverContext": d.river_context,
        "braidContext": d.braid_context,
        "tributaryContext": d.tributary_context,
        "captureContext": d.capture_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    river_map = _load_required_artifact(
        KNOWLEDGE_RIVER_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "knowledge_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    braid_report = _load_required_artifact(
        CORRIDOR_BRAIDING_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "braiding_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    tributary_registry = _load_required_artifact(
        TRIBUTARY_SUPPORT_REGISTRY_PATH,
        compatibility_paths=(BRIDGE_DIR / "tributary_registry.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    capture_report = _load_required_artifact(
        RIVER_CAPTURE_RISK_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "capture_risk_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    discovery = _load_supporting_audit(DISCOVERY_NAVIGATION_AUDIT_PATH)
    attractor = _load_supporting_audit(EPISTEMIC_ATTRACTOR_AUDIT_PATH)
    operationalization = _load_supporting_audit(OPERATIONALIZATION_AUDIT_PATH)
    sovereignty = _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)
    memory = _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)
    value = _load_supporting_audit(VALUE_ALIGNMENT_AUDIT_PATH)

    discovery_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(discovery, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    attractor_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(attractor, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    operationalization_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(operationalization, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    sovereignty_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(sovereignty, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    memory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(memory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    value_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(value, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(
        0.15 * discovery_risk
        + 0.17 * attractor_risk
        + 0.17 * operationalization_risk
        + 0.17 * sovereignty_risk
        + 0.17 * memory_risk
        + 0.17 * value_risk
    )

    river_rows = _parse_rows(river_map.payload, "targets")
    braid_rows = {str(r.get("targetId")): r for r in _parse_rows(braid_report.payload, "targets") if r.get("targetId")}
    tributary_rows = {str(r.get("targetId")): r for r in _parse_rows(tributary_registry.payload, "targets") if r.get("targetId")}
    capture_rows = {str(r.get("targetId")): r for r in _parse_rows(capture_report.payload, "targets") if r.get("targetId")}

    decisions = sorted(
        (
            evaluate_target(
                row,
                braid_rows=braid_rows,
                tributary_rows=tributary_rows,
                capture_rows=capture_rows,
                system_risk=system_risk,
            )
            for row in river_rows
        ),
        key=lambda d: d.target_id,
    )

    input_artifacts = [river_map, braid_report, tributary_registry, capture_report]
    canonical_integrity = _build_canonical_integrity_metadata(input_artifacts)
    input_mode, mode_warning = _classify_mode(input_artifacts)

    metadata = {
        "inputMode": input_mode,
        "inputModeWarning": mode_warning,
        "systemRisk": round(system_risk, 6),
        "inputArtifacts": [
            {
                "path": _display_path(a.path),
                "sourceMode": a.source_mode,
                "schemaVersion": a.payload.get("schemaVersion"),
                "producerRepo": a.payload.get("producerRepo"),
                "producerModule": a.payload.get("producerModule"),
                "producerCommit": a.payload.get("producerCommit"),
                "generatedAt": a.payload.get("generatedAt"),
            }
            for a in input_artifacts
        ],
        "canonicalIntegrity": canonical_integrity,
        "supportingAudits": [
            _display_path(DISCOVERY_NAVIGATION_AUDIT_PATH),
            _display_path(EPISTEMIC_ATTRACTOR_AUDIT_PATH),
            _display_path(OPERATIONALIZATION_AUDIT_PATH),
            _display_path(COMMONS_SOVEREIGNTY_AUDIT_PATH),
            _display_path(CIVILIZATIONAL_MEMORY_AUDIT_PATH),
            _display_path(VALUE_ALIGNMENT_AUDIT_PATH),
        ],
    }

    created_at = _resolve_created_at(river_map.payload, braid_report.payload, tributary_registry.payload, capture_report.payload)
    phaselock = (
        "discovery/attractor/memory/sovereignty/value context -> CoherenceLattice knowledge-river and braid formalization "
        "-> Sophia bounded river audit -> Publisher river overlays -> human/community/scientific stewardship of braided discovery channels"
    )
    caution = (
        "Recommendations are bounded knowledge-stewardship guidance only and do not authorize canonization, centralized "
        "control, deployment authority, or closure of scientific alternatives."
    )

    records = [_to_payload(d) for d in decisions]
    audit_payload = {
        "schema": "knowledge_river_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": records,
    }
    recommendations_payload = {
        "schema": "knowledge_river_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": records,
    }

    Draft202012Validator(_load_json(KNOWLEDGE_RIVER_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(KNOWLEDGE_RIVER_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main() -> None:
    parser = argparse.ArgumentParser(description="Build bounded knowledge-river audit + recommendations artifacts.")
    parser.add_argument("--allow-compatibility-names", action="store_true", help="Allow deprecated fallback artifact names.")
    args = parser.parse_args()

    audit_payload, recommendations_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    KNOWLEDGE_RIVER_AUDIT_OUT.parent.mkdir(parents=True, exist_ok=True)
    KNOWLEDGE_RIVER_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    KNOWLEDGE_RIVER_RECOMMENDATIONS_OUT.write_text(
        json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
