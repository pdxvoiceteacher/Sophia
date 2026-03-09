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

CIVILIZATIONAL_MEMORY_MAP_PATH = BRIDGE_DIR / "civilizational_memory_map.json"
INTERGENERATIONAL_LEGIBILITY_REPORT_PATH = BRIDGE_DIR / "intergenerational_legibility_report.json"
EPISTEMIC_RESILIENCE_SCORECARD_PATH = BRIDGE_DIR / "epistemic_resilience_scorecard.json"
MEMORY_FRAGILITY_REPORT_PATH = BRIDGE_DIR / "memory_fragility_report.json"

COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
THEORY_CORPUS_AUDIT_PATH = BRIDGE_DIR / "theory_corpus_audit.json"
REVIEW_PACKET_AUDIT_PATH = BRIDGE_DIR / "review_packet_audit.json"
RECOVERY_AUDIT_PATH = BRIDGE_DIR / "recovery_audit.json"
COMMONS_PARTICIPATION_AUDIT_PATH = BRIDGE_DIR / "commons_participation_audit.json"

CIVILIZATIONAL_MEMORY_AUDIT_OUT = BRIDGE_DIR / "civilizational_memory_audit.json"
CIVILIZATIONAL_MEMORY_RECOMMENDATIONS_OUT = BRIDGE_DIR / "civilizational_memory_recommendations.json"

CIVILIZATIONAL_MEMORY_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "civilizational_memory_audit_v1.schema.json"
CIVILIZATIONAL_MEMORY_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "civilizational_memory_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "civilizational_memory_v1"
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


class CivilizationalMemoryInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class CivilizationalMemoryDecision:
    target_id: str
    target_type: str
    memory_status: str
    coherence_score: float
    risk_score: float
    continuity_context: str
    legibility_context: str
    fragility_context: str
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
        "memory-stable": "watch",
        "legibility-repair": "docket",
        "fragility-watch": "docket",
        "capture-risk": "suppress",
        "require-human-review": "suppress",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise CivilizationalMemoryInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise CivilizationalMemoryInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise CivilizationalMemoryInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise CivilizationalMemoryInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise CivilizationalMemoryInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )

    payload = _load_json(found[0])
    _validate_provenance(payload, path=found[0])
    return LoadedArtifact(path=found[0], payload=payload, source_mode="compatibility")


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise CivilizationalMemoryInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise CivilizationalMemoryInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise CivilizationalMemoryInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None

    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise CivilizationalMemoryInputError(
            f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}"
        )

    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise CivilizationalMemoryInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise CivilizationalMemoryInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
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
            "warning": "No canonical integrity manifest fields found on civilizational-memory artifacts.",
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
        "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical memory-integrity constraints."
        if reasons
        else "Canonical integrity manifest present and internally consistent across civilizational-memory artifacts."
    )
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture civilizational-memory artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: civilizational-memory inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    legibility_rows: dict[str, dict[str, Any]],
    resilience_rows: dict[str, dict[str, Any]],
    fragility_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> CivilizationalMemoryDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "civilizational-memory-context")

    continuity_strength = _clamp01(float(row.get("continuityStrength", 0.5)))
    plural_memory_support = _clamp01(float(row.get("pluralMemorySupport", 0.5)))

    legibility = legibility_rows.get(target_id, {})
    intergenerational_legibility = _clamp01(float(legibility.get("intergenerationalLegibility", 0.5)))
    translation_durability = _clamp01(float(legibility.get("translationDurability", 0.5)))
    opacity_risk = _clamp01(float(legibility.get("opacityRisk", 0.4)))

    resilience = resilience_rows.get(target_id, {})
    epistemic_resilience = _clamp01(float(resilience.get("epistemicResilience", 0.5)))
    negative_result_preservation = _clamp01(float(resilience.get("negativeResultPreservation", 0.5)))

    fragility = fragility_rows.get(target_id, {})
    memory_fragility = _clamp01(float(fragility.get("memoryFragility", 0.5)))
    archive_loss_risk = _clamp01(float(fragility.get("archiveLossRisk", 0.5)))
    capture_pressure = _clamp01(float(fragility.get("capturePressure", 0.4)))
    priesthood_opacity_risk = _clamp01(float(fragility.get("priesthoodOpacityRisk", 0.4)))
    canon_closure_pressure = _clamp01(float(fragility.get("canonClosurePressure", 0.4)))

    openness_score = _clamp01(1.0 - 0.5 * priesthood_opacity_risk - 0.5 * canon_closure_pressure)

    coherence_score = _clamp01(
        0.14 * continuity_strength
        + 0.14 * plural_memory_support
        + 0.14 * intergenerational_legibility
        + 0.14 * translation_durability
        + 0.14 * epistemic_resilience
        + 0.14 * negative_result_preservation
        + 0.16 * openness_score
    )
    risk_score = _clamp01(
        0.14 * memory_fragility
        + 0.14 * archive_loss_risk
        + 0.14 * capture_pressure
        + 0.14 * priesthood_opacity_risk
        + 0.12 * canon_closure_pressure
        + 0.12 * (1.0 - negative_result_preservation)
        + 0.10 * (1.0 - intergenerational_legibility)
        + 0.10 * system_risk
    )

    if capture_pressure >= 0.80 or canon_closure_pressure >= 0.80:
        status = "require-human-review"
        rule = "anti-erasure-and-anti-canon-closure-gate"
    elif priesthood_opacity_risk >= 0.74 or opacity_risk >= 0.74:
        status = "capture-risk"
        rule = "anti-memory-priesthood-and-opacity"
    elif memory_fragility >= 0.68 or archive_loss_risk >= 0.68 or negative_result_preservation <= 0.38:
        status = "fragility-watch"
        rule = "negative-result-preservation-and-fragility-watch"
    elif intergenerational_legibility <= 0.54 or translation_durability <= 0.54:
        status = "legibility-repair"
        rule = "intergenerational-legibility-repair"
    else:
        status = "memory-stable"
        rule = "plural-memory-continuity-watch"

    continuity_context = (
        f"continuityStrength={continuity_strength:.3f}, pluralMemorySupport={plural_memory_support:.3f}, epistemicResilience={epistemic_resilience:.3f}; "
        "memory stewardship preserves uncertainty, dissent, and failed branches alongside successful theories."
    )
    legibility_context = (
        f"intergenerationalLegibility={intergenerational_legibility:.3f}, translationDurability={translation_durability:.3f}, opacityRisk={opacity_risk:.3f}; "
        "knowledge remains legible across generations through public translation rather than priesthood opacity."
    )
    fragility_context = (
        f"memoryFragility={memory_fragility:.3f}, archiveLossRisk={archive_loss_risk:.3f}, negativeResultPreservation={negative_result_preservation:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "recommendations are bounded stewardship guidance only and do not authorize erasure, canon closure, or centralized historical authority."
    )
    explanation = (
        f"Civilizational memory guidance is bounded stewardship guidance only. targetId={target_id}, "
        f"memoryStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return CivilizationalMemoryDecision(
        target_id=target_id,
        target_type=target_type,
        memory_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        continuity_context=continuity_context,
        legibility_context=legibility_context,
        fragility_context=fragility_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: CivilizationalMemoryDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "memoryStatus": d.memory_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "continuityContext": d.continuity_context,
        "legibilityContext": d.legibility_context,
        "fragilityContext": d.fragility_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    memory_map = _load_required_artifact(
        CIVILIZATIONAL_MEMORY_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "memory_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    legibility_report = _load_required_artifact(
        INTERGENERATIONAL_LEGIBILITY_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "legibility_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    resilience_scorecard = _load_required_artifact(
        EPISTEMIC_RESILIENCE_SCORECARD_PATH,
        compatibility_paths=(BRIDGE_DIR / "resilience_scorecard.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    fragility_report = _load_required_artifact(
        MEMORY_FRAGILITY_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "fragility_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    sovereignty = _load_supporting_audit(COMMONS_SOVEREIGNTY_AUDIT_PATH)
    theory = _load_supporting_audit(THEORY_CORPUS_AUDIT_PATH)
    review = _load_supporting_audit(REVIEW_PACKET_AUDIT_PATH)
    recovery = _load_supporting_audit(RECOVERY_AUDIT_PATH)
    participation = _load_supporting_audit(COMMONS_PARTICIPATION_AUDIT_PATH)

    sovereignty_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(sovereignty, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    theory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(theory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    review_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(review, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    recovery_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(recovery, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    participation_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(participation, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.20 * sovereignty_risk + 0.20 * theory_risk + 0.20 * review_risk + 0.20 * recovery_risk + 0.20 * participation_risk)

    legibility_rows = {str(r.get("targetId")): r for r in _parse_rows(legibility_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    resilience_rows = {str(r.get("targetId")): r for r in _parse_rows(resilience_scorecard.payload, "targets") if isinstance(r.get("targetId"), str)}
    fragility_rows = {str(r.get("targetId")): r for r in _parse_rows(fragility_report.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            legibility_rows=legibility_rows,
            resilience_rows=resilience_rows,
            fragility_rows=fragility_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(memory_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [memory_map, legibility_report, resilience_scorecard, fragility_report]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(memory_map.payload, legibility_report.payload, resilience_scorecard.payload, fragility_report.payload)
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
            _display_path(COMMONS_SOVEREIGNTY_AUDIT_PATH),
            _display_path(THEORY_CORPUS_AUDIT_PATH),
            _display_path(REVIEW_PACKET_AUDIT_PATH),
            _display_path(RECOVERY_AUDIT_PATH),
            _display_path(COMMONS_PARTICIPATION_AUDIT_PATH),
        ],
    }

    caution = (
        "Civilizational memory recommendations are bounded stewardship guidance only and do not authorize erasure, canon closure, "
        "or centralized historical authority."
    )

    audit_payload = {
        "schema": "civilizational_memory_audit_v1",
        "created_at": created_at,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "civilizational_memory_recommendations_v1",
        "created_at": created_at,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(CIVILIZATIONAL_MEMORY_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(CIVILIZATIONAL_MEMORY_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia civilizational memory state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    CIVILIZATIONAL_MEMORY_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    CIVILIZATIONAL_MEMORY_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {CIVILIZATIONAL_MEMORY_AUDIT_OUT}")
    print(f"Wrote {CIVILIZATIONAL_MEMORY_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
