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

EPISTEMIC_ATTRACTOR_MAP_PATH = BRIDGE_DIR / "epistemic_attractor_map.json"
KNOWLEDGE_BASIN_REGISTRY_PATH = BRIDGE_DIR / "knowledge_basin_registry.json"
DEAD_ZONE_REPORT_PATH = BRIDGE_DIR / "dead_zone_report.json"
PARADIGM_SHIFT_FORECAST_PATH = BRIDGE_DIR / "paradigm_shift_forecast.json"

THEORY_CORPUS_AUDIT_PATH = BRIDGE_DIR / "theory_corpus_audit.json"
EMERGENT_DOMAIN_AUDIT_PATH = BRIDGE_DIR / "emergent_domain_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"

EPISTEMIC_ATTRACTOR_AUDIT_OUT = BRIDGE_DIR / "epistemic_attractor_audit.json"
EPISTEMIC_ATTRACTOR_RECOMMENDATIONS_OUT = BRIDGE_DIR / "epistemic_attractor_recommendations.json"

EPISTEMIC_ATTRACTOR_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "epistemic_attractor_audit_v1.schema.json"
EPISTEMIC_ATTRACTOR_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "epistemic_attractor_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "epistemic_attractor_v1"
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


class EpistemicAttractorInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class EpistemicAttractorDecision:
    target_id: str
    target_type: str
    epistemic_status: str
    coherence_score: float
    risk_score: float
    attractor_context: str
    basin_context: str
    dead_zone_context: str
    shift_context: str
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
        "attractor-stable": "watch",
        "basin-contested": "docket",
        "dead-zone-watch": "docket",
        "paradigm-shift-rising": "docket",
        "require-human-review": "suppress",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise EpistemicAttractorInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise EpistemicAttractorInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise EpistemicAttractorInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise EpistemicAttractorInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise EpistemicAttractorInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )

    payload = _load_json(found[0])
    _validate_provenance(payload, path=found[0])
    return LoadedArtifact(path=found[0], payload=payload, source_mode="compatibility")


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise EpistemicAttractorInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise EpistemicAttractorInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise EpistemicAttractorInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise EpistemicAttractorInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise EpistemicAttractorInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise EpistemicAttractorInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
    return manifest


def _build_canonical_integrity_metadata(artifacts: list[LoadedArtifact]) -> dict[str, Any]:
    manifests: list[dict[str, Any]] = []
    for artifact in artifacts:
        manifest = _extract_integrity_manifest(artifact.payload, path=artifact.path)
        if manifest is None:
            continue
        manifests.append({"path": _display_path(artifact.path), **manifest})

    if not manifests:
        return {"status": "absent", "warning": "No canonical integrity manifest fields found on epistemic-attractor artifacts.", "divergenceReasons": [], "manifests": []}

    baseline = manifests[0]
    reasons: list[str] = []
    for candidate in manifests[1:]:
        safety_changed = any(candidate[field] != baseline[field] for field in IMMUTABLE_SAFETY_FIELDS)
        same_sig = candidate["constraintSignatureSha256"] == baseline["constraintSignatureSha256"]
        if safety_changed and same_sig:
            reasons.append(f"{candidate['path']} changes immutable safety constraints without changing constraint signature")

    status = "divergent" if reasons else "canonical"
    warning = (
        "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical epistemic-topology constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across epistemic-attractor artifacts."
    )
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture epistemic-attractor artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: epistemic-attractor inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    basin_rows: dict[str, dict[str, Any]],
    dead_zone_rows: dict[str, dict[str, Any]],
    shift_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> EpistemicAttractorDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "epistemic-attractor-context")

    attractor_stability = _clamp01(float(row.get("attractorStability", 0.5)))
    recurrence_visibility = _clamp01(float(row.get("recurrenceVisibility", 0.5)))

    basin = basin_rows.get(target_id, {})
    basin_coherence = _clamp01(float(basin.get("basinCoherence", 0.5)))
    basin_contestation = _clamp01(float(basin.get("basinContestation", 0.5)))

    dead = dead_zone_rows.get(target_id, {})
    dead_zone_recurrence = _clamp01(float(dead.get("deadZoneRecurrence", 0.5)))
    dead_zone_opacity = _clamp01(float(dead.get("deadZoneOpacity", 0.4)))
    negative_result_preservation = _clamp01(float(dead.get("negativeResultPreservation", 0.5)))

    shift = shift_rows.get(target_id, {})
    paradigm_shift_signal = _clamp01(float(shift.get("paradigmShiftSignal", 0.5)))
    overclaim_pressure = _clamp01(float(shift.get("overclaimPressure", 0.4)))

    humility_score = _clamp01(1.0 - 0.5 * overclaim_pressure - 0.5 * basin_contestation)

    coherence_score = _clamp01(
        0.14 * attractor_stability
        + 0.14 * recurrence_visibility
        + 0.14 * basin_coherence
        + 0.14 * (1.0 - basin_contestation)
        + 0.14 * (1.0 - dead_zone_recurrence)
        + 0.14 * negative_result_preservation
        + 0.16 * humility_score
    )
    risk_score = _clamp01(
        0.14 * basin_contestation
        + 0.14 * dead_zone_recurrence
        + 0.12 * dead_zone_opacity
        + 0.14 * paradigm_shift_signal
        + 0.14 * overclaim_pressure
        + 0.12 * (1.0 - negative_result_preservation)
        + 0.10 * (1.0 - attractor_stability)
        + 0.10 * system_risk
    )

    if overclaim_pressure >= 0.80 or paradigm_shift_signal >= 0.84:
        status = "require-human-review"
        rule = "paradigm-shift-overclaim-suppression-gate"
    elif dead_zone_recurrence >= 0.72 or dead_zone_opacity >= 0.72:
        status = "dead-zone-watch"
        rule = "dead-zone-recurrence-visibility-protection"
    elif paradigm_shift_signal >= 0.68 and overclaim_pressure <= 0.64:
        status = "paradigm-shift-rising"
        rule = "bounded-paradigm-shift-rising"
    elif basin_contestation >= 0.62:
        status = "basin-contested"
        rule = "contested-basin-plurality-protection"
    else:
        status = "attractor-stable"
        rule = "attractor-stability-under-audit"

    attractor_context = (
        f"attractorStability={attractor_stability:.3f}, recurrenceVisibility={recurrence_visibility:.3f}, basinCoherence={basin_coherence:.3f}; "
        "stable attractors remain auditable and subject to revision."
    )
    basin_context = (
        f"basinContestation={basin_contestation:.3f}, negativeResultPreservation={negative_result_preservation:.3f}; "
        "contested basins and failed lines remain visible for plural interpretation."
    )
    dead_zone_context = (
        f"deadZoneRecurrence={dead_zone_recurrence:.3f}, deadZoneOpacity={dead_zone_opacity:.3f}; "
        "dead zones remain legible so civilizations do not endlessly rediscover them."
    )
    shift_context = (
        f"paradigmShiftSignal={paradigm_shift_signal:.3f}, overclaimPressure={overclaim_pressure:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "recommendations are bounded epistemic-stewardship guidance only and do not certify final truth, erase contested theories, or canonize emergent domains."
    )
    explanation = (
        f"Epistemic-attractor guidance is bounded epistemic-stewardship guidance only. targetId={target_id}, "
        f"epistemicStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return EpistemicAttractorDecision(
        target_id=target_id,
        target_type=target_type,
        epistemic_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        attractor_context=attractor_context,
        basin_context=basin_context,
        dead_zone_context=dead_zone_context,
        shift_context=shift_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: EpistemicAttractorDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "epistemicStatus": d.epistemic_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "attractorContext": d.attractor_context,
        "basinContext": d.basin_context,
        "deadZoneContext": d.dead_zone_context,
        "shiftContext": d.shift_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    attractor_map = _load_required_artifact(
        EPISTEMIC_ATTRACTOR_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "attractor_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    basin_registry = _load_required_artifact(
        KNOWLEDGE_BASIN_REGISTRY_PATH,
        compatibility_paths=(BRIDGE_DIR / "basin_registry.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    dead_zone_report = _load_required_artifact(
        DEAD_ZONE_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "deadzone_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    shift_forecast = _load_required_artifact(
        PARADIGM_SHIFT_FORECAST_PATH,
        compatibility_paths=(BRIDGE_DIR / "shift_forecast.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    theory = _load_supporting_audit(THEORY_CORPUS_AUDIT_PATH)
    emergent = _load_supporting_audit(EMERGENT_DOMAIN_AUDIT_PATH)
    sovereignty = _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)
    memory = _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)

    theory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(theory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    emergent_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(emergent, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    sovereignty_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(sovereignty, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    memory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(memory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.25 * theory_risk + 0.25 * emergent_risk + 0.25 * sovereignty_risk + 0.25 * memory_risk)

    basin_rows = {str(r.get("targetId")): r for r in _parse_rows(basin_registry.payload, "targets") if isinstance(r.get("targetId"), str)}
    dead_zone_rows = {str(r.get("targetId")): r for r in _parse_rows(dead_zone_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    shift_rows = {str(r.get("targetId")): r for r in _parse_rows(shift_forecast.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            basin_rows=basin_rows,
            dead_zone_rows=dead_zone_rows,
            shift_rows=shift_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(attractor_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [attractor_map, basin_registry, dead_zone_report, shift_forecast]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(attractor_map.payload, basin_registry.payload, dead_zone_report.payload, shift_forecast.payload)
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
            _display_path(THEORY_CORPUS_AUDIT_PATH),
            _display_path(EMERGENT_DOMAIN_AUDIT_PATH),
            _display_path(COMMONS_SOVEREIGNTY_AUDIT_PATH),
            _display_path(CIVILIZATIONAL_MEMORY_AUDIT_PATH),
        ],
    }

    phaselock = (
        "theory / memory / emergence / trajectory context -> CoherenceLattice attractor and dead-zone formalization -> "
        "Sophia bounded epistemic-topology audit -> Publisher topology overlays -> human/scientific/community interpretation and stewardship"
    )
    caution = (
        "Epistemic-attractor recommendations are bounded epistemic-stewardship guidance only and do not certify final truth, "
        "erase contested theories, or canonize emergent domains."
    )

    audit_payload = {
        "schema": "epistemic_attractor_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "epistemic_attractor_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(EPISTEMIC_ATTRACTOR_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(EPISTEMIC_ATTRACTOR_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia epistemic attractor state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    EPISTEMIC_ATTRACTOR_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    EPISTEMIC_ATTRACTOR_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {EPISTEMIC_ATTRACTOR_AUDIT_OUT}")
    print(f"Wrote {EPISTEMIC_ATTRACTOR_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
