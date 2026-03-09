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

DISCOVERY_VECTOR_FIELD_PATH = BRIDGE_DIR / "discovery_vector_field.json"
CROSS_DOMAIN_BRIDGE_MAP_PATH = BRIDGE_DIR / "cross_domain_bridge_map.json"
ENTROPY_REDUCTION_CORRIDOR_PATH = BRIDGE_DIR / "entropy_reduction_corridor.json"
DISCOVERY_NAVIGATION_REPORT_PATH = BRIDGE_DIR / "discovery_navigation_report.json"

EPISTEMIC_ATTRACTOR_AUDIT_PATH = BRIDGE_DIR / "epistemic_attractor_audit.json"
OPERATIONALIZATION_AUDIT_PATH = BRIDGE_DIR / "operationalization_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"

DISCOVERY_NAVIGATION_AUDIT_OUT = BRIDGE_DIR / "discovery_navigation_audit.json"
DISCOVERY_NAVIGATION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "discovery_navigation_recommendations.json"

DISCOVERY_NAVIGATION_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "discovery_navigation_audit_v1.schema.json"
DISCOVERY_NAVIGATION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "discovery_navigation_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "discovery_navigation_v1"
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


class DiscoveryNavigationInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class DiscoveryNavigationDecision:
    target_id: str
    target_type: str
    discovery_status: str
    coherence_score: float
    risk_score: float
    vector_context: str
    bridge_context: str
    corridor_context: str
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
        "observe": "watch",
        "explore-bounded": "docket",
        "bridge-first": "docket",
        "dead-zone-risk": "suppress",
        "require-human-review": "suppress",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise DiscoveryNavigationInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise DiscoveryNavigationInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise DiscoveryNavigationInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise DiscoveryNavigationInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise DiscoveryNavigationInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )

    payload = _load_json(found[0])
    _validate_provenance(payload, path=found[0])
    return LoadedArtifact(path=found[0], payload=payload, source_mode="compatibility")


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise DiscoveryNavigationInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise DiscoveryNavigationInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise DiscoveryNavigationInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise DiscoveryNavigationInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")

    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise DiscoveryNavigationInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise DiscoveryNavigationInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
    return manifest


def _build_canonical_integrity_metadata(artifacts: list[LoadedArtifact]) -> dict[str, Any]:
    manifests: list[dict[str, Any]] = []
    for artifact in artifacts:
        manifest = _extract_integrity_manifest(artifact.payload, path=artifact.path)
        if manifest is None:
            continue
        manifests.append({"path": _display_path(artifact.path), **manifest})

    if not manifests:
        return {"status": "absent", "warning": "No canonical integrity manifest fields found on discovery-navigation artifacts.", "divergenceReasons": [], "manifests": []}

    baseline = manifests[0]
    reasons: list[str] = []
    for candidate in manifests[1:]:
        safety_changed = any(candidate[field] != baseline[field] for field in IMMUTABLE_SAFETY_FIELDS)
        same_sig = candidate["constraintSignatureSha256"] == baseline["constraintSignatureSha256"]
        if safety_changed and same_sig:
            reasons.append(f"{candidate['path']} changes immutable safety constraints without changing constraint signature")

    status = "divergent" if reasons else "canonical"
    warning = (
        "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical discovery-navigation constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across discovery-navigation artifacts."
    )
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture discovery-navigation artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: discovery-navigation inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    bridge_rows: dict[str, dict[str, Any]],
    corridor_rows: dict[str, dict[str, Any]],
    report_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> DiscoveryNavigationDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "discovery-navigation-context")

    vector_coherence = _clamp01(float(row.get("vectorCoherence", 0.5)))
    novelty_gradient = _clamp01(float(row.get("noveltyGradient", 0.5)))

    bridge = bridge_rows.get(target_id, {})
    bridge_strength = _clamp01(float(bridge.get("bridgeStrength", 0.5)))
    bridge_legibility = _clamp01(float(bridge.get("bridgeLegibility", 0.5)))

    corridor = corridor_rows.get(target_id, {})
    entropy_reduction_signal = _clamp01(float(corridor.get("entropyReductionSignal", 0.5)))
    dead_zone_adjacency = _clamp01(float(corridor.get("deadZoneAdjacency", 0.4)))

    report = report_rows.get(target_id, {})
    overclaim_pressure = _clamp01(float(report.get("overclaimPressure", 0.4)))
    commons_legibility = _clamp01(float(report.get("commonsLegibility", 0.5)))
    value_alignment_support = _clamp01(float(report.get("valueAlignmentSupport", 0.5)))

    humility_score = _clamp01(1.0 - 0.5 * overclaim_pressure - 0.5 * dead_zone_adjacency)

    coherence_score = _clamp01(
        0.14 * vector_coherence
        + 0.14 * novelty_gradient
        + 0.14 * bridge_strength
        + 0.14 * bridge_legibility
        + 0.14 * entropy_reduction_signal
        + 0.14 * commons_legibility
        + 0.16 * humility_score
    )
    risk_score = _clamp01(
        0.16 * dead_zone_adjacency
        + 0.14 * overclaim_pressure
        + 0.14 * (1.0 - bridge_legibility)
        + 0.14 * (1.0 - commons_legibility)
        + 0.14 * (1.0 - value_alignment_support)
        + 0.12 * (1.0 - bridge_strength)
        + 0.16 * system_risk
    )

    if overclaim_pressure >= 0.80:
        status = "require-human-review"
        rule = "anti-overclaim-suppression-gate"
    elif dead_zone_adjacency >= 0.72:
        status = "dead-zone-risk"
        rule = "dead-zone-adjacency-suppression"
    elif bridge_strength <= 0.50 or bridge_legibility <= 0.52:
        status = "bridge-first"
        rule = "bridge-strengthening-before-exploration"
    elif vector_coherence >= 0.62 and entropy_reduction_signal >= 0.60 and commons_legibility >= 0.56 and value_alignment_support >= 0.56:
        status = "explore-bounded"
        rule = "bounded-exploration-corridor"
    else:
        status = "observe"
        rule = "observe-under-uncertainty"

    vector_context = (
        f"vectorCoherence={vector_coherence:.3f}, noveltyGradient={novelty_gradient:.3f}, entropyReductionSignal={entropy_reduction_signal:.3f}; "
        "a promising corridor is not a command."
    )
    bridge_context = (
        f"bridgeStrength={bridge_strength:.3f}, bridgeLegibility={bridge_legibility:.3f}; "
        "bridge strengthening and legible translation are favored before novelty enthusiasm."
    )
    corridor_context = (
        f"deadZoneAdjacency={dead_zone_adjacency:.3f}, overclaimPressure={overclaim_pressure:.3f}; "
        "dead-zone adjacency and overclaim require suppression and review."
    )
    commons_context = (
        f"commonsLegibility={commons_legibility:.3f}, valueAlignmentSupport={value_alignment_support:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "recommendations are bounded discovery-stewardship guidance only and do not authorize automatic pursuit, canonization, deployment, or institutional override."
    )
    explanation = (
        f"Discovery-navigation guidance is bounded discovery-stewardship guidance only. targetId={target_id}, "
        f"discoveryStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return DiscoveryNavigationDecision(
        target_id=target_id,
        target_type=target_type,
        discovery_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        vector_context=vector_context,
        bridge_context=bridge_context,
        corridor_context=corridor_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: DiscoveryNavigationDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "discoveryStatus": d.discovery_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "vectorContext": d.vector_context,
        "bridgeContext": d.bridge_context,
        "corridorContext": d.corridor_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    vector_field = _load_required_artifact(
        DISCOVERY_VECTOR_FIELD_PATH,
        compatibility_paths=(BRIDGE_DIR / "vector_field.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    bridge_map = _load_required_artifact(
        CROSS_DOMAIN_BRIDGE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "bridge_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    corridor = _load_required_artifact(
        ENTROPY_REDUCTION_CORRIDOR_PATH,
        compatibility_paths=(BRIDGE_DIR / "reduction_corridor.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    navigation_report = _load_required_artifact(
        DISCOVERY_NAVIGATION_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "navigation_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    attractor = _load_supporting_audit(EPISTEMIC_ATTRACTOR_AUDIT_PATH)
    operationalization = _load_supporting_audit(OPERATIONALIZATION_AUDIT_PATH)
    sovereignty = _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)
    memory = _load_supporting_audit(CIVILIZATIONAL_MEMORY_AUDIT_PATH)
    value = _load_supporting_audit(VALUE_ALIGNMENT_AUDIT_PATH)

    attractor_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(attractor, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    operationalization_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(operationalization, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    sovereignty_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(sovereignty, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    memory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(memory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    value_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(value, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.20 * attractor_risk + 0.20 * operationalization_risk + 0.20 * sovereignty_risk + 0.20 * memory_risk + 0.20 * value_risk)

    bridge_rows = {str(r.get("targetId")): r for r in _parse_rows(bridge_map.payload, "targets") if isinstance(r.get("targetId"), str)}
    corridor_rows = {str(r.get("targetId")): r for r in _parse_rows(corridor.payload, "targets") if isinstance(r.get("targetId"), str)}
    report_rows = {str(r.get("targetId")): r for r in _parse_rows(navigation_report.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            bridge_rows=bridge_rows,
            corridor_rows=corridor_rows,
            report_rows=report_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(vector_field.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [vector_field, bridge_map, corridor, navigation_report]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(vector_field.payload, bridge_map.payload, corridor.payload, navigation_report.payload)
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
            _display_path(OPERATIONALIZATION_AUDIT_PATH),
            _display_path(COMMONS_SOVEREIGNTY_AUDIT_PATH),
            _display_path(CIVILIZATIONAL_MEMORY_AUDIT_PATH),
            _display_path(VALUE_ALIGNMENT_AUDIT_PATH),
        ],
    }

    phaselock = (
        "attractor / basin / dead-zone / operational-boundary / value / commons context -> CoherenceLattice discovery-vector and corridor formalization -> "
        "Sophia bounded discovery-navigation audit -> Publisher corridor overlays -> human/community/scientific deliberation and bounded exploration"
    )
    caution = (
        "Discovery-navigation recommendations are bounded discovery-stewardship guidance only and do not authorize automatic pursuit, "
        "canonization, deployment, or institutional override."
    )

    audit_payload = {
        "schema": "discovery_navigation_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "discovery_navigation_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(DISCOVERY_NAVIGATION_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(DISCOVERY_NAVIGATION_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia discovery navigation state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    DISCOVERY_NAVIGATION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    DISCOVERY_NAVIGATION_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {DISCOVERY_NAVIGATION_AUDIT_OUT}")
    print(f"Wrote {DISCOVERY_NAVIGATION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
