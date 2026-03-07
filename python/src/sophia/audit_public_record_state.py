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

PUBLIC_RECORD_INTAKE_MAP_PATH = BRIDGE_DIR / "public_record_intake_map.json"
ENTITY_GRAPH_MAP_PATH = BRIDGE_DIR / "entity_graph_map.json"
RELATIONSHIP_EDGE_MAP_PATH = BRIDGE_DIR / "relationship_edge_map.json"
CHAIN_OF_CUSTODY_REPORT_PATH = BRIDGE_DIR / "chain_of_custody_report.json"

VERIFICATION_AUDIT_PATH = BRIDGE_DIR / "verification_audit.json"
SYMBOLIC_FIELD_AUDIT_PATH = BRIDGE_DIR / "symbolic_field_audit.json"
CLOSURE_AUDIT_PATH = BRIDGE_DIR / "closure_audit.json"
TRIAGE_AUDIT_PATH = BRIDGE_DIR / "triage_audit.json"

PUBLIC_RECORD_AUDIT_OUT = BRIDGE_DIR / "public_record_audit.json"
PUBLIC_RECORD_RECOMMENDATIONS_OUT = BRIDGE_DIR / "public_record_recommendations.json"

PUBLIC_RECORD_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "public_record_audit_v1.schema.json"
PUBLIC_RECORD_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "public_record_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "public_record_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class PublicRecordInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class PublicRecordDecision:
    target_id: str
    target_type: str
    graph_status: str
    coherence_score: float
    risk_score: float
    claim_context: str
    entity_context: str
    custody_context: str
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
        raise PublicRecordInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise PublicRecordInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise PublicRecordInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        p = _load_json(path)
        _validate_provenance(p, path=path)
        return LoadedArtifact(path, p, "canonical")
    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise PublicRecordInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise PublicRecordInputError(f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}")
    p = _load_json(found[0])
    _validate_provenance(p, path=found[0])
    return LoadedArtifact(found[0], p, "compatibility")


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture public-record artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: public-record inputs combine live and fixture producers; verify before action."


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for d in docs:
        for k in ("generatedAt", "created_at"):
            ts = d.get(k)
            if isinstance(ts, str) and ts:
                return ts
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str) -> str:
    return {
        "sound": "docket",
        "monitor": "watch",
        "ambiguous": "watch",
        "verify-first": "suppress",
        "require-human-review": "docket",
    }[status]


def evaluate_target(
    row: dict[str, Any],
    *,
    graph_rows: dict[str, dict[str, Any]],
    edge_rows: dict[str, dict[str, Any]],
    custody_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> PublicRecordDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "public-record")

    record_quality = _clamp01(float(row.get("recordQuality", 0.5)))
    claim_reliability = _clamp01(float(row.get("claimReliability", 0.5)))

    graph = graph_rows.get(target_id, {})
    entity_ambiguity = _clamp01(float(graph.get("entityAmbiguity", 0.45)))
    node_consistency = _clamp01(float(graph.get("nodeConsistency", 0.55)))

    edge = edge_rows.get(target_id, {})
    edge_confidence = _clamp01(float(edge.get("edgeConfidence", 0.5)))
    edge_ambiguity = _clamp01(float(edge.get("edgeAmbiguity", 0.45)))

    custody = custody_rows.get(target_id, {})
    chain_completeness = _clamp01(float(custody.get("chainCompleteness", 0.5)))
    tamper_risk = _clamp01(float(custody.get("tamperRisk", 0.4)))

    coherence = _clamp01(
        0.20 * record_quality
        + 0.20 * claim_reliability
        + 0.20 * node_consistency
        + 0.15 * edge_confidence
        + 0.15 * chain_completeness
        + 0.10 * (1.0 - entity_ambiguity)
    )
    risk = _clamp01(
        0.20 * entity_ambiguity
        + 0.20 * edge_ambiguity
        + 0.18 * tamper_risk
        + 0.16 * (1.0 - chain_completeness)
        + 0.14 * (1.0 - edge_confidence)
        + 0.12 * system_risk
    )

    if entity_ambiguity >= 0.82 or edge_ambiguity >= 0.80:
        status = "require-human-review"
        rule = "ambiguous-entity-human-review"
    elif tamper_risk >= 0.72 or chain_completeness <= 0.35:
        status = "verify-first"
        rule = "chain-of-custody-verify-first"
    elif risk >= 0.58:
        status = "ambiguous"
        rule = "ambiguous-relationship-watch"
    elif risk >= 0.40:
        status = "monitor"
        rule = "monitor-public-record-graph"
    else:
        status = "sound"
        rule = "sound-evidence-graph"

    claim_context = f"recordQuality={record_quality:.3f}, claimReliability={claim_reliability:.3f}; evidence first, conclusions later."
    entity_context = f"entityAmbiguity={entity_ambiguity:.3f}, nodeConsistency={node_consistency:.3f}, edgeAmbiguity={edge_ambiguity:.3f}; identity inference remains bounded."
    custody_context = f"chainCompleteness={chain_completeness:.3f}, tamperRisk={tamper_risk:.3f}, edgeConfidence={edge_confidence:.3f}, systemRisk={system_risk:.3f}; chain-of-custody sufficiency is required before conclusion."

    explanation = (
        f"Public-record guidance is bounded evidence guidance only. targetId={target_id}, graphStatus={status}, "
        f"coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return PublicRecordDecision(
        target_id=target_id,
        target_type=target_type,
        graph_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        claim_context=claim_context,
        entity_context=entity_context,
        custody_context=custody_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: PublicRecordDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "graphStatus": d.graph_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "claimContext": d.claim_context,
        "entityContext": d.entity_context,
        "custodyContext": d.custody_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    intake = _load_required_artifact(PUBLIC_RECORD_INTAKE_MAP_PATH, compatibility_paths=(BRIDGE_DIR / "public_record_map.json",), allow_compatibility_names=allow_compatibility_names)
    graph = _load_required_artifact(ENTITY_GRAPH_MAP_PATH, compatibility_paths=(BRIDGE_DIR / "entity_graph.json",), allow_compatibility_names=allow_compatibility_names)
    edges = _load_required_artifact(RELATIONSHIP_EDGE_MAP_PATH, compatibility_paths=(BRIDGE_DIR / "relationship_edges.json",), allow_compatibility_names=allow_compatibility_names)
    custody = _load_required_artifact(CHAIN_OF_CUSTODY_REPORT_PATH, compatibility_paths=(BRIDGE_DIR / "custody_report.json",), allow_compatibility_names=allow_compatibility_names)

    verification = _load_json(VERIFICATION_AUDIT_PATH)
    symbolic = _load_json(SYMBOLIC_FIELD_AUDIT_PATH)
    closure = _load_json(CLOSURE_AUDIT_PATH)
    triage = _load_json(TRIAGE_AUDIT_PATH)

    verification_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(verification, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    symbolic_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(symbolic, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    closure_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(closure, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    triage_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(triage, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.28 * verification_risk + 0.24 * symbolic_risk + 0.24 * closure_risk + 0.24 * triage_risk)

    graph_rows = {str(r.get("targetId")): r for r in _parse_rows(graph.payload, "targets") if isinstance(r.get("targetId"), str)}
    edge_rows = {str(r.get("targetId")): r for r in _parse_rows(edges.payload, "targets") if isinstance(r.get("targetId"), str)}
    custody_rows = {str(r.get("targetId")): r for r in _parse_rows(custody.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            graph_rows=graph_rows,
            edge_rows=edge_rows,
            custody_rows=custody_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(intake.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [intake, graph, edges, custody]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(intake.payload, graph.payload, edges.payload, custody.payload)

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
        "public-record / entity-graph / custody state -> CoherenceLattice public-record formalization -> "
        "Sophia public-record audit -> Publisher public-record overlays -> human/community evidence review"
    )
    caution = (
        "Public-record recommendations are bounded evidence guidance only and do not accuse, defame, "
        "or automatically publish conclusions."
    )

    audit_payload = {
        "schema": "public_record_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "public_record_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(PUBLIC_RECORD_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(PUBLIC_RECORD_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia public-record state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    PUBLIC_RECORD_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    PUBLIC_RECORD_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {PUBLIC_RECORD_AUDIT_OUT}")
    print(f"Wrote {PUBLIC_RECORD_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
