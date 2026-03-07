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

CLOSURE_STATE_MAP_PATH = BRIDGE_DIR / "closure_state_map.json"
CLOSURE_STATE_SUMMARY_PATH = BRIDGE_DIR / "closure_state_summary.json"
REPAIR_CANDIDATE_MAP_PATH = BRIDGE_DIR / "repair_candidate_map.json"
REOPEN_SIGNAL_REPORT_PATH = BRIDGE_DIR / "reopen_signal_report.json"

TRIAGE_AUDIT_PATH = BRIDGE_DIR / "triage_audit.json"
INSTITUTIONAL_AUDIT_PATH = BRIDGE_DIR / "institutional_audit.json"
PRECEDENT_AUDIT_PATH = BRIDGE_DIR / "precedent_audit.json"
RECOVERY_AUDIT_PATH = BRIDGE_DIR / "recovery_audit.json"
WITNESS_AUDIT_PATH = BRIDGE_DIR / "witness_audit.json"

CLOSURE_AUDIT_OUT = BRIDGE_DIR / "closure_audit.json"
CLOSURE_RECOMMENDATIONS_OUT = BRIDGE_DIR / "closure_recommendations.json"

CLOSURE_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "closure_audit_v1.schema.json"
CLOSURE_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "closure_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "closure_state_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = (
    "schemaVersion",
    "producerRepo",
    "producerModule",
    "producerCommit",
    "generatedAt",
)


class ClosureInputError(RuntimeError):
    """Raised for fail-closed closure input errors."""


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class ClosureDecision:
    target_id: str
    target_type: str
    closure_recommendation: str
    coherence_score: float
    risk_score: float
    closure_context: str
    repair_context: str
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
        raise ClosureInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise ClosureInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise ClosureInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        p = _load_json(path)
        _validate_provenance(p, path=path)
        return LoadedArtifact(path, p, "canonical")
    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise ClosureInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise ClosureInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )
    p = _load_json(found[0])
    _validate_provenance(p, path=found[0])
    return LoadedArtifact(found[0], p, "compatibility")


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for d in docs:
        for key in ("generatedAt", "created_at"):
            ts = d.get(key)
            if isinstance(ts, str) and ts:
                return ts
    return "1970-01-01T00:00:00Z"


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture closure artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: closure inputs combine live and fixture producers; verify before action."


def _recommendation_to_action(rec: str) -> str:
    return {
        "confirm-closure": "docket",
        "keep-open": "watch",
        "provisional-close": "watch",
        "reopen-for-review": "docket",
        "queue-repair": "watch",
        "require-human-review": "docket",
    }[rec]


def evaluate_target(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    repair_rows: dict[str, dict[str, Any]],
    reopen_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> ClosureDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "closure-target")

    closure_conf = _clamp01(float(row.get("closureConfidence", summary.get("meanClosureConfidence", 0.5))))
    contradiction = _clamp01(float(row.get("contradictionScore", summary.get("meanContradictionScore", 0.4))))

    repair = repair_rows.get(target_id, {})
    repair_need = _clamp01(float(repair.get("repairNeedScore", summary.get("meanRepairNeedScore", 0.45))))
    reversibility = _clamp01(float(repair.get("reversibilityScore", summary.get("meanReversibilityScore", 0.5))))

    reopen = reopen_rows.get(target_id, {})
    reopen_signal = _clamp01(float(reopen.get("reopenSignalScore", summary.get("meanReopenSignalScore", 0.4))))
    evidence_quality = _clamp01(float(reopen.get("evidenceQuality", summary.get("meanEvidenceQuality", 0.5))))

    coherence = _clamp01(0.40 * closure_conf + 0.20 * (1.0 - contradiction) + 0.20 * (1.0 - repair_need) + 0.20 * evidence_quality)
    risk = _clamp01(0.25 * contradiction + 0.25 * repair_need + 0.20 * reopen_signal + 0.15 * (1.0 - reversibility) + 0.15 * system_risk)

    if reopen_signal >= 0.75 and evidence_quality >= 0.62:
        rec = "reopen-for-review"
        rule = "evidence-bound-reopen"
    elif repair_need >= 0.72 and reopen_signal < 0.70:
        rec = "queue-repair"
        rule = "repair-before-reopen"
    elif contradiction >= 0.78:
        rec = "require-human-review"
        rule = "contradiction-human-review"
    elif closure_conf >= 0.76 and risk <= 0.34:
        rec = "confirm-closure"
        rule = "confirm-stable-closure"
    elif closure_conf >= 0.58 and risk <= 0.54:
        rec = "provisional-close"
        rule = "provisional-closure-with-watch"
    elif risk >= 0.60:
        rec = "keep-open"
        rule = "keep-open-under-instability"
    else:
        rec = "provisional-close"
        rule = "bounded-provisional-default"

    closure_context = f"closureConfidence={closure_conf:.3f}, reopenSignal={reopen_signal:.3f}; processed is not automatically resolved."
    repair_context = f"repairNeedScore={repair_need:.3f}, reversibilityScore={reversibility:.3f}; repair need is integrity work, not failure."
    contradiction_context = f"contradictionScore={contradiction:.3f}, evidenceQuality={evidence_quality:.3f}, systemRisk={system_risk:.3f}; closure must remain reviewable."

    explanation = (
        f"Closure guidance is bounded and non-mutating. targetId={target_id}, recommendation={rec}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return ClosureDecision(
        target_id=target_id,
        target_type=target_type,
        closure_recommendation=rec,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        closure_context=closure_context,
        repair_context=repair_context,
        contradiction_context=contradiction_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_recommendation_to_action(rec),
    )


def _to_payload(d: ClosureDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "closureRecommendation": d.closure_recommendation,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "closureContext": d.closure_context,
        "repairContext": d.repair_context,
        "contradictionContext": d.contradiction_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    c_map = _load_required_artifact(
        CLOSURE_STATE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "closure_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    c_summary = _load_required_artifact(
        CLOSURE_STATE_SUMMARY_PATH,
        compatibility_paths=(BRIDGE_DIR / "closure_summary.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    r_map = _load_required_artifact(
        REPAIR_CANDIDATE_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "repair_candidates.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    reopen_report = _load_required_artifact(
        REOPEN_SIGNAL_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "reopen_signals.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    triage = _load_json(TRIAGE_AUDIT_PATH)
    institutional = _load_json(INSTITUTIONAL_AUDIT_PATH)
    precedent = _load_json(PRECEDENT_AUDIT_PATH)
    recovery = _load_json(RECOVERY_AUDIT_PATH)
    witness = _load_json(WITNESS_AUDIT_PATH)

    triage_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(triage, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    institutional_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(institutional, "records") if isinstance(r.get("riskScore"), (int, float))], 0.4)
    precedent_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(precedent, "records") if isinstance(r.get("riskScore"), (int, float))], 0.35)
    recovery_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(recovery, "records") if isinstance(r.get("riskScore"), (int, float))], 0.4)
    witness_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(witness, "records") if isinstance(r.get("riskScore"), (int, float))], 0.35)

    system_risk = _clamp01(0.22 * triage_risk + 0.2 * institutional_risk + 0.19 * precedent_risk + 0.2 * recovery_risk + 0.19 * witness_risk)

    repair_rows = {str(r.get("targetId")): r for r in _parse_rows(r_map.payload, "targets") if isinstance(r.get("targetId"), str)}
    reopen_rows = {str(r.get("targetId")): r for r in _parse_rows(reopen_report.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            summary=c_summary.payload,
            repair_rows=repair_rows,
            reopen_rows=reopen_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(c_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [c_map, c_summary, r_map, reopen_report]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(c_map.payload, c_summary.payload, r_map.payload, reopen_report.payload)

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
        "docket / outcome / recommendation state -> CoherenceLattice closure and repair formalization -> "
        "Sophia closure audit -> Publisher closure and repair overlays -> human/community review of outcome durability"
    )
    caution = (
        "Closure recommendations are bounded outcome guidance only and do not automatically reopen, close, "
        "or repair anything."
    )

    audit_payload = {
        "schema": "closure_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "closure_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(CLOSURE_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(CLOSURE_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia closure and repair audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    CLOSURE_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    CLOSURE_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {CLOSURE_AUDIT_OUT}")
    print(f"Wrote {CLOSURE_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
