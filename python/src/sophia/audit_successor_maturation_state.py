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

SUCCESSOR_MATURATION_MAP_PATH = BRIDGE_DIR / "successor_maturation_map.json"
FALSE_FUTURE_RISK_REPORT_PATH = BRIDGE_DIR / "false_future_risk_report.json"
PLURALITY_RETENTION_SCORECARD_PATH = BRIDGE_DIR / "plurality_retention_scorecard.json"
MATURATION_GATE_REPORT_PATH = BRIDGE_DIR / "maturation_gate_report.json"

SUCCESSOR_DELTA_AUDIT_PATH = BRIDGE_DIR / "successor_delta_audit.json"
TERRACE_EROSION_AUDIT_PATH = BRIDGE_DIR / "terrace_erosion_audit.json"
EPOCHAL_TERRACE_AUDIT_PATH = BRIDGE_DIR / "epochal_terrace_audit.json"
CIVILIZATIONAL_DELTA_AUDIT_PATH = BRIDGE_DIR / "civilizational_delta_audit.json"
KNOWLEDGE_RIVER_AUDIT_PATH = BRIDGE_DIR / "knowledge_river_audit.json"
TRUST_SURFACE_AUDIT_PATH = BRIDGE_DIR / "trust_surface_audit.json"
CIVILIZATIONAL_MEMORY_AUDIT_PATH = BRIDGE_DIR / "civilizational_memory_audit.json"
COMMONS_SOVEREIGNTY_AUDIT_PATH = BRIDGE_DIR / "commons_sovereignty_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"

SUCCESSOR_MATURATION_AUDIT_OUT = BRIDGE_DIR / "successor_maturation_audit.json"
SUCCESSOR_MATURATION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "successor_maturation_recommendations.json"

SUCCESSOR_MATURATION_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "successor_maturation_audit_v1.schema.json"
SUCCESSOR_MATURATION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "successor_maturation_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "successor_maturation_v1"
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


class SuccessorMaturationInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]


@dataclass(slots=True)
class SuccessorMaturationDecision:
    target_id: str
    target_type: str
    maturation_status: str
    coherence_score: float
    risk_score: float
    maturation_context: str
    plurality_context: str
    false_future_context: str
    trust_context: str
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


def _status_to_action(status: str, risk: float) -> str:
    if status in {"false-future-risk", "capture-risk"}:
        return "suppress" if risk >= 0.82 else "watch"
    if status in {"maturation-visible", "plurality-retain", "phase-transition-watch"}:
        return "watch"
    return {"require-human-review": "docket"}[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise SuccessorMaturationInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise SuccessorMaturationInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise SuccessorMaturationInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path) -> LoadedArtifact:
    if not path.exists():
        raise SuccessorMaturationInputError(f"Missing required canonical artifact: {path}")
    payload = _load_json(path)
    _validate_provenance(payload, path=path)
    return LoadedArtifact(path=path, payload=payload)


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SuccessorMaturationInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise SuccessorMaturationInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise SuccessorMaturationInputError(f"Supporting audit missing records array in {path}")
    return payload


def _extract_integrity_manifest(payload: dict[str, Any], *, path: Path) -> dict[str, Any] | None:
    present = [field for field in CANONICAL_INTEGRITY_FIELDS if field in payload]
    if not present:
        return None
    missing = [field for field in CANONICAL_INTEGRITY_FIELDS if field not in payload]
    if missing:
        raise SuccessorMaturationInputError(f"Canonical integrity manifest in {path} is incomplete; missing: {', '.join(missing)}")
    manifest = {field: payload.get(field) for field in CANONICAL_INTEGRITY_FIELDS}
    for field in CANONICAL_INTEGRITY_FIELDS:
        value = manifest[field]
        if field == "modificationDisclosureRequired":
            if not isinstance(value, bool):
                raise SuccessorMaturationInputError(f"Canonical integrity field {field} in {path} must be boolean")
        elif not isinstance(value, str) or not value:
            raise SuccessorMaturationInputError(f"Canonical integrity field {field} in {path} must be non-empty string")
    return manifest


def _build_canonical_integrity_metadata(artifacts: list[LoadedArtifact]) -> dict[str, Any]:
    manifests: list[dict[str, Any]] = []
    for artifact in artifacts:
        manifest = _extract_integrity_manifest(artifact.payload, path=artifact.path)
        if manifest is None:
            continue
        manifests.append({"path": _display_path(artifact.path), **manifest})
    if not manifests:
        return {"status": "absent", "warning": "No canonical integrity manifest fields found on successor-maturation artifacts.", "divergenceReasons": [], "manifests": []}
    baseline = manifests[0]
    reasons: list[str] = []
    for candidate in manifests[1:]:
        if any(candidate[f] != baseline[f] for f in IMMUTABLE_SAFETY_FIELDS) and candidate["constraintSignatureSha256"] == baseline["constraintSignatureSha256"]:
            reasons.append(f"{candidate['path']} changes immutable safety constraints without changing constraint signature")
    status = "divergent" if reasons else "canonical"
    warning = "CANONICAL DIVERGENCE: downstream overlays must visibly mark divergence from canonical successor-maturation constraints." if reasons else "Canonical integrity manifest present and internally consistent across successor-maturation artifacts."
    return {"status": status, "warning": warning, "divergenceReasons": sorted(set(reasons)), "manifests": manifests}


def evaluate_target(
    row: dict[str, Any],
    *,
    false_rows: dict[str, dict[str, Any]],
    plurality_rows: dict[str, dict[str, Any]],
    gate_rows: dict[str, dict[str, Any]],
    support_risk: float,
    trust_surface_risk: float,
) -> SuccessorMaturationDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "successor")

    maturation_score = _clamp01(float(row.get("maturationScore", 0.5)))
    memory_continuity = _clamp01(float(row.get("memoryContinuityScore", 0.5)))

    false = false_rows.get(target_id, {})
    simulated_legitimacy = _clamp01(float(false.get("simulatedLegitimacyScore", 0.5)))
    trust_compression = _clamp01(float(false.get("trustCompressionScore", 0.5)))
    premature_convergence = _clamp01(float(false.get("prematureConvergenceScore", 0.5)))

    plurality = plurality_rows.get(target_id, {})
    plurality_retention = _clamp01(float(plurality.get("pluralityRetentionScore", 0.5)))

    gate = gate_rows.get(target_id, {})
    successor_capture_risk = _clamp01(float(gate.get("successorCaptureRiskScore", 0.5)))
    coupling_strength = _clamp01(float(gate.get("couplingStrengthScore", 0.5)))

    coherence_score = _clamp01(
        0.18 * maturation_score
        + 0.16 * plurality_retention
        + 0.14 * memory_continuity
        + 0.14 * (1.0 - simulated_legitimacy)
        + 0.12 * (1.0 - trust_compression)
        + 0.10 * (1.0 - premature_convergence)
        + 0.16 * (1.0 - support_risk)
    )
    risk_score = _clamp01(
        0.12 * (1.0 - plurality_retention)
        + 0.10 * (1.0 - memory_continuity)
        + 0.14 * simulated_legitimacy
        + 0.14 * trust_compression
        + 0.14 * premature_convergence
        + 0.14 * successor_capture_risk
        + 0.10 * coupling_strength
        + 0.12 * trust_surface_risk
    )

    false_future = (
        simulated_legitimacy >= 0.68
        or trust_compression >= 0.68
        or premature_convergence >= 0.68
    ) and (plurality_retention < 0.62 or memory_continuity < 0.62)

    if successor_capture_risk >= 0.70:
        status = "capture-risk"
        rule = "capture-risk-suppresses-maturation-uplift"
    elif false_future:
        status = "false-future-risk"
        rule = "simulated-legitimacy-or-premature-convergence-gate"
    elif coupling_strength >= 0.72 and plurality_retention >= 0.66 and trust_surface_risk < 0.70:
        status = "phase-transition-watch"
        rule = "strong-coupling-plus-healthy-plurality-watch"
    elif plurality_retention >= 0.68 and memory_continuity >= 0.66 and maturation_score < 0.70:
        status = "plurality-retain"
        rule = "plurality-and-memory-retention-priority"
    elif maturation_score >= 0.72 and plurality_retention >= 0.66 and memory_continuity >= 0.66:
        status = "maturation-visible"
        rule = "maturation-visible-with-plurality-gate"
    else:
        status = "require-human-review"
        rule = "insufficient-successor-maturation-legibility"

    maturation_context = (
        f"maturationScore={maturation_score:.3f}, memoryContinuityScore={memory_continuity:.3f}; no successor uplifts to maturation-visible when plurality retention is weak."
    )
    plurality_context = (
        f"pluralityRetentionScore={plurality_retention:.3f}; plurality retention is required for healthy successor formation and future legibility."
    )
    false_future_context = (
        f"simulatedLegitimacyScore={simulated_legitimacy:.3f}, trustCompressionScore={trust_compression:.3f}, prematureConvergenceScore={premature_convergence:.3f}; false-future risk triggers when simulated legitimacy outruns plurality and memory continuity."
    )
    trust_context = (
        f"couplingStrengthScore={coupling_strength:.3f}, trustSurfaceRisk={trust_surface_risk:.3f}; phase-transition watch requires strong coupling plus healthy plurality, not hype alone."
    )
    commons_context = (
        f"supportRisk={support_risk:.3f}, successorCaptureRiskScore={successor_capture_risk:.3f}; recommendations remain non-coercive and non-centralizing across renewal, successor, terrace, delta, sovereignty, and value context."
    )
    explanation = (
        "Recommendations are bounded successor-maturation guidance only and do not declare new epochs, authorize successor rule, or canonize emergent futures. "
        "Recommendations do not authorize institutional displacement, centralized succession, governance transfer, or canon closure. "
        f"targetId={target_id}, maturationStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return SuccessorMaturationDecision(
        target_id=target_id,
        target_type=target_type,
        maturation_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        maturation_context=maturation_context,
        plurality_context=plurality_context,
        false_future_context=false_future_context,
        trust_context=trust_context,
        commons_context=commons_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status, risk_score),
    )


def _to_payload(d: SuccessorMaturationDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "maturationStatus": d.maturation_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "maturationContext": d.maturation_context,
        "pluralityContext": d.plurality_context,
        "falseFutureContext": d.false_future_context,
        "trustContext": d.trust_context,
        "commonsContext": d.commons_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs() -> tuple[dict[str, Any], dict[str, Any]]:
    maturation_map = _load_required_artifact(SUCCESSOR_MATURATION_MAP_PATH)
    false_future_report = _load_required_artifact(FALSE_FUTURE_RISK_REPORT_PATH)
    plurality_scorecard = _load_required_artifact(PLURALITY_RETENTION_SCORECARD_PATH)
    maturation_gate_report = _load_required_artifact(MATURATION_GATE_REPORT_PATH)

    supporting = [
        ("successor delta", _load_supporting_audit(SUCCESSOR_DELTA_AUDIT_PATH)),
        ("terrace erosion", _load_supporting_audit(TERRACE_EROSION_AUDIT_PATH)),
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
    trust_surface_risk = _clamp01(supporting_risks[5])

    false_rows = {str(r.get("targetId")): r for r in _parse_rows(false_future_report.payload) if isinstance(r.get("targetId"), str)}
    plurality_rows = {str(r.get("targetId")): r for r in _parse_rows(plurality_scorecard.payload) if isinstance(r.get("targetId"), str)}
    gate_rows = {str(r.get("targetId")): r for r in _parse_rows(maturation_gate_report.payload) if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            false_rows=false_rows,
            plurality_rows=plurality_rows,
            gate_rows=gate_rows,
            support_risk=support_risk,
            trust_surface_risk=trust_surface_risk,
        )
        for row in _parse_rows(maturation_map.payload)
    ]
    decisions = sorted(decisions, key=lambda d: (d.target_id, d.target_type))

    loaded = [maturation_map, false_future_report, plurality_scorecard, maturation_gate_report]
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
        "renewal / successor / terrace / delta / trust / sovereignty / value context -> CoherenceLattice successor-maturation and false-future formalization -> "
        "Sophia bounded maturation audit -> Publisher future overlays -> human/community/scientific stewardship of viable and non-viable successor formations"
    )
    caution = (
        "Recommendations are bounded successor-maturation guidance only and do not declare new epochs, authorize successor rule, "
        "or canonize emergent futures."
    )
    created_at = _resolve_created_at(*(a.payload for a in loaded))

    audit_payload = {
        "schema": "successor_maturation_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "successor_maturation_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(SUCCESSOR_MATURATION_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(SUCCESSOR_MATURATION_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia successor-maturation state audit")
    parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs()
    SUCCESSOR_MATURATION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    SUCCESSOR_MATURATION_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {SUCCESSOR_MATURATION_AUDIT_OUT}")
    print(f"Wrote {SUCCESSOR_MATURATION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
