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

CLAIM_TYPE_MAP_PATH = BRIDGE_DIR / "claim_type_map.json"
ENTITY_RESOLUTION_MAP_PATH = BRIDGE_DIR / "entity_resolution_map.json"
ENTITY_RESOLUTION_SUMMARY_PATH = BRIDGE_DIR / "entity_resolution_summary.json"
VERIFICATION_TASK_MAP_PATH = BRIDGE_DIR / "verification_task_map.json"

SYMBOLIC_FIELD_AUDIT_PATH = BRIDGE_DIR / "symbolic_field_audit.json"
CLOSURE_AUDIT_PATH = BRIDGE_DIR / "closure_audit.json"
TRIAGE_AUDIT_PATH = BRIDGE_DIR / "triage_audit.json"
PRECEDENT_AUDIT_PATH = BRIDGE_DIR / "precedent_audit.json"
WITNESS_AUDIT_PATH = BRIDGE_DIR / "witness_audit.json"

VERIFICATION_AUDIT_OUT = BRIDGE_DIR / "verification_audit.json"
VERIFICATION_RECOMMENDATIONS_OUT = BRIDGE_DIR / "verification_recommendations.json"

VERIFICATION_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "verification_audit_v1.schema.json"
VERIFICATION_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "verification_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "verification_state_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class VerificationInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class VerificationDecision:
    target_id: str
    target_type: str
    verification_status: str
    coherence_score: float
    risk_score: float
    claim_context: str
    entity_context: str
    contradiction_context: str
    governing_rule: str
    explanation: str
    target_publisher_action: str


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _parse_rows(payload: dict[str, Any], key: str) -> list[dict[str, Any]]:
    v = payload.get(key)
    return [r for r in v if isinstance(r, dict)] if isinstance(v, list) else []


def _safe_mean(vals: list[float], default: float = 0.0) -> float:
    return sum(vals) / len(vals) if vals else default


def _clamp01(v: float) -> float:
    return max(0.0, min(1.0, float(v)))


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [f for f in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(f), str) or not payload.get(f)]
    if missing:
        raise VerificationInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise VerificationInputError(f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}")
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise VerificationInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        p = _load_json(path)
        _validate_provenance(p, path=path)
        return LoadedArtifact(path, p, "canonical")
    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise VerificationInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise VerificationInputError(f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}")
    p = _load_json(found[0])
    _validate_provenance(p, path=found[0])
    return LoadedArtifact(found[0], p, "compatibility")


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture verification artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: verification inputs combine live and fixture producers; verify before action."


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for d in docs:
        for k in ("generatedAt", "created_at"):
            v = d.get(k)
            if isinstance(v, str) and v:
                return v
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str) -> str:
    return {
        "verify-now": "docket",
        "near-term-verify": "docket",
        "monitor": "watch",
        "defer": "watch",
        "require-human-review": "docket",
    }[status]


def evaluate_target(
    row: dict[str, Any],
    *,
    entity_rows: dict[str, dict[str, Any]],
    summary: dict[str, Any],
    task_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> VerificationDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "claim")

    claim_conf = _clamp01(float(row.get("claimConfidence", summary.get("meanClaimConfidence", 0.5))))
    claim_sensitivity = _clamp01(float(row.get("sensitivityScore", summary.get("meanSensitivityScore", 0.45))))

    entity = entity_rows.get(target_id, {})
    ambiguity = _clamp01(float(entity.get("entityAmbiguity", summary.get("meanEntityAmbiguity", 0.45))))
    identity_collision = _clamp01(float(entity.get("identityCollisionRisk", summary.get("meanIdentityCollisionRisk", 0.35))))

    task = task_rows.get(target_id, {})
    verification_urgency = _clamp01(float(task.get("verificationUrgency", summary.get("meanVerificationUrgency", 0.45))))
    contradiction = _clamp01(float(task.get("contradictionScore", summary.get("meanContradictionScore", 0.4))))

    coherence = _clamp01(0.35 * claim_conf + 0.25 * (1.0 - ambiguity) + 0.20 * (1.0 - contradiction) + 0.20 * (1.0 - identity_collision))
    risk = _clamp01(0.22 * ambiguity + 0.2 * identity_collision + 0.2 * contradiction + 0.2 * verification_urgency + 0.1 * claim_sensitivity + 0.08 * system_risk)

    if ambiguity >= 0.80 or identity_collision >= 0.78:
        status = "require-human-review"
        rule = "entity-ambiguity-human-review"
    elif verification_urgency >= 0.75 and contradiction >= 0.55:
        status = "verify-now"
        rule = "urgent-contradiction-verify-now"
    elif risk >= 0.56:
        status = "near-term-verify"
        rule = "near-term-verification-queue"
    elif risk <= 0.34 and claim_conf >= 0.70:
        status = "defer"
        rule = "defer-high-confidence-low-risk"
    else:
        status = "monitor"
        rule = "monitor-verification-state"

    claim_context = f"claimConfidence={claim_conf:.3f}, sensitivityScore={claim_sensitivity:.3f}, verificationUrgency={verification_urgency:.3f}; recommendations are evidence-guidance only."
    entity_context = f"entityAmbiguity={ambiguity:.3f}, identityCollisionRisk={identity_collision:.3f}; no automatic identity resolution is performed."
    contradiction_context = f"contradictionScore={contradiction:.3f}, systemRisk={system_risk:.3f}; claims remain contestable and reviewable."

    explanation = (
        f"Verification guidance is bounded and non-accusatory. targetId={target_id}, verificationStatus={status}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return VerificationDecision(
        target_id=target_id,
        target_type=target_type,
        verification_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        claim_context=claim_context,
        entity_context=entity_context,
        contradiction_context=contradiction_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: VerificationDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "verificationStatus": d.verification_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "claimContext": d.claim_context,
        "entityContext": d.entity_context,
        "contradictionContext": d.contradiction_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    claim_map = _load_required_artifact(CLAIM_TYPE_MAP_PATH, compatibility_paths=(BRIDGE_DIR / "claim_map.json",), allow_compatibility_names=allow_compatibility_names)
    entity_map = _load_required_artifact(ENTITY_RESOLUTION_MAP_PATH, compatibility_paths=(BRIDGE_DIR / "entity_map.json",), allow_compatibility_names=allow_compatibility_names)
    entity_summary = _load_required_artifact(ENTITY_RESOLUTION_SUMMARY_PATH, compatibility_paths=(BRIDGE_DIR / "entity_summary.json",), allow_compatibility_names=allow_compatibility_names)
    task_map = _load_required_artifact(VERIFICATION_TASK_MAP_PATH, compatibility_paths=(BRIDGE_DIR / "verification_tasks.json",), allow_compatibility_names=allow_compatibility_names)

    symbolic = _load_json(SYMBOLIC_FIELD_AUDIT_PATH)
    closure = _load_json(CLOSURE_AUDIT_PATH)
    triage = _load_json(TRIAGE_AUDIT_PATH)
    precedent = _load_json(PRECEDENT_AUDIT_PATH)
    witness = _load_json(WITNESS_AUDIT_PATH)

    symbolic_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(symbolic, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    closure_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(closure, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    triage_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(triage, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    precedent_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(precedent, "records") if isinstance(r.get("riskScore"), (int, float))], 0.35)
    witness_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(witness, "records") if isinstance(r.get("riskScore"), (int, float))], 0.35)
    system_risk = _clamp01(0.22 * symbolic_risk + 0.2 * closure_risk + 0.2 * triage_risk + 0.19 * precedent_risk + 0.19 * witness_risk)

    entity_rows = {str(r.get("targetId")): r for r in _parse_rows(entity_map.payload, "targets") if isinstance(r.get("targetId"), str)}
    task_rows = {str(r.get("targetId")): r for r in _parse_rows(task_map.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            entity_rows=entity_rows,
            summary=entity_summary.payload,
            task_rows=task_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(claim_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [claim_map, entity_map, entity_summary, task_map]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(claim_map.payload, entity_map.payload, entity_summary.payload, task_map.payload)

    metadata = {
        "inputMode": mode,
        "inputModeWarning": warning,
        "systemRisk": round(system_risk, 6),
        "inputArtifacts": [
            {
                "path": str(a.path.relative_to(REPO_ROOT)) if a.path.is_relative_to(REPO_ROOT) else str(a.path),
                "sourceMode": a.source_mode,
                "schemaVersion": str(a.payload.get("schemaVersion")),
                "producerRepo": str(a.payload.get("producerRepo")),
                "producerModule": str(a.payload.get("producerModule")),
                "producerCommit": str(a.payload.get("producerCommit")),
                "generatedAt": str(a.payload.get("generatedAt")),
            }
            for a in loaded
        ],
    }

    phaselock = (
        "claim / entity / verification-task state -> CoherenceLattice claim typing and resolution formalization -> "
        "Sophia verification audit -> Publisher verification overlays -> human/community evidence review"
    )
    caution = (
        "Verification recommendations are bounded evidence-guidance only and do not accuse, defame, "
        "or automatically resolve identity."
    )

    audit_payload = {
        "schema": "verification_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "verification_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(VERIFICATION_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(VERIFICATION_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia verification-state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    VERIFICATION_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    VERIFICATION_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {VERIFICATION_AUDIT_OUT}")
    print(f"Wrote {VERIFICATION_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
