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

THEORY_TRANSFER_MAP_PATH = BRIDGE_DIR / "theory_transfer_map.json"
DONOR_TARGET_ASYMMETRY_REPORT_PATH = BRIDGE_DIR / "donor_target_asymmetry_report.json"
TRANSFER_REPLICATION_GATE_PATH = BRIDGE_DIR / "transfer_replication_gate.json"
TRANSFER_RISK_REGISTER_PATH = BRIDGE_DIR / "transfer_risk_register.json"

EXPERIMENTAL_AUDIT_PATH = BRIDGE_DIR / "experimental_audit.json"
THEORY_CORPUS_AUDIT_PATH = BRIDGE_DIR / "theory_corpus_audit.json"
AGENCY_MODE_AUDIT_PATH = BRIDGE_DIR / "agency_mode_audit.json"
RESPONSIBILITY_AUDIT_PATH = BRIDGE_DIR / "responsibility_audit.json"

THEORY_TRANSFER_AUDIT_OUT = BRIDGE_DIR / "theory_transfer_audit.json"
THEORY_TRANSFER_RECOMMENDATIONS_OUT = BRIDGE_DIR / "theory_transfer_recommendations.json"

THEORY_TRANSFER_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "theory_transfer_audit_v1.schema.json"
THEORY_TRANSFER_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "theory_transfer_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "theory_transfer_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class TheoryTransferInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class TheoryTransferDecision:
    target_id: str
    target_type: str
    transfer_status: str
    coherence_score: float
    risk_score: float
    asymmetry_context: str
    replication_context: str
    agency_context: str
    fairness_context: str
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


def _resolve_created_at(*docs: dict[str, Any]) -> str:
    for doc in docs:
        for key in ("generatedAt", "created_at"):
            value = doc.get(key)
            if isinstance(value, str) and value:
                return value
    return "1970-01-01T00:00:00Z"


def _status_to_action(status: str) -> str:
    return {
        "analogy-only": "watch",
        "bounded-transfer": "watch",
        "replication-required": "docket",
        "blocked": "suppress",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise TheoryTransferInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise TheoryTransferInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise TheoryTransferInputError(f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}")


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise TheoryTransferInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise TheoryTransferInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )

    payload = _load_json(found[0])
    _validate_provenance(payload, path=found[0])
    return LoadedArtifact(path=found[0], payload=payload, source_mode="compatibility")


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture transfer artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: transfer inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    asymmetry_rows: dict[str, dict[str, Any]],
    replication_rows: dict[str, dict[str, Any]],
    risk_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> TheoryTransferDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "theory-transfer-context")

    analogy_strength = _clamp01(float(row.get("analogyStrength", 0.5)))
    transfer_readiness = _clamp01(float(row.get("transferReadiness", 0.5)))

    asymmetry = asymmetry_rows.get(target_id, {})
    asymmetry_score = _clamp01(float(asymmetry.get("asymmetryScore", 0.5)))
    domain_distance = _clamp01(float(asymmetry.get("domainDistance", 0.5)))

    replication = replication_rows.get(target_id, {})
    donor_replication_maturity = _clamp01(float(replication.get("donorReplicationMaturity", 0.5)))
    target_replication_maturity = _clamp01(float(replication.get("targetReplicationMaturity", 0.5)))
    replication_required = bool(replication.get("replicationRequired", False))

    risk = risk_rows.get(target_id, {})
    transfer_harm_risk = _clamp01(float(risk.get("transferHarmRisk", 0.5)))
    deterministic_overreach = _clamp01(float(risk.get("deterministicOverreach", 0.4)))

    fairness_score = _clamp01(1.0 - 0.5 * asymmetry_score - 0.5 * deterministic_overreach)

    coherence = _clamp01(
        0.18 * analogy_strength
        + 0.18 * transfer_readiness
        + 0.18 * donor_replication_maturity
        + 0.18 * target_replication_maturity
        + 0.14 * fairness_score
        + 0.14 * (1.0 - domain_distance)
    )
    risk_score = _clamp01(
        0.20 * asymmetry_score
        + 0.16 * domain_distance
        + 0.20 * transfer_harm_risk
        + 0.16 * deterministic_overreach
        + 0.14 * (1.0 - target_replication_maturity)
        + 0.14 * system_risk
    )

    if asymmetry_score >= 0.82:
        status = "blocked"
        rule = "high-asymmetry-block"
    elif deterministic_overreach >= 0.80 or transfer_harm_risk >= 0.84:
        status = "require-human-review"
        rule = "overreach-or-harm-human-review"
    elif replication_required and target_replication_maturity < 0.60:
        status = "replication-required"
        rule = "target-domain-replication-gate"
    elif transfer_readiness >= 0.65 and asymmetry_score <= 0.45 and target_replication_maturity >= 0.65:
        status = "bounded-transfer"
        rule = "bounded-transfer-with-replication"
    else:
        status = "analogy-only"
        rule = "analogy-only-under-uncertainty"

    asymmetry_context = (
        f"asymmetryScore={asymmetry_score:.3f}, domainDistance={domain_distance:.3f}, analogyStrength={analogy_strength:.3f}; "
        "cross-domain analogies are provisional and non-final."
    )
    replication_context = (
        f"replicationRequired={str(replication_required).lower()}, donorReplicationMaturity={donor_replication_maturity:.3f}, "
        f"targetReplicationMaturity={target_replication_maturity:.3f}; cross-domain transfer remains replication-gated."
    )
    agency_context = (
        f"transferReadiness={transfer_readiness:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "recommendations remain bounded scientific-governance guidance only."
    )
    fairness_context = (
        f"transferHarmRisk={transfer_harm_risk:.3f}, deterministicOverreach={deterministic_overreach:.3f}, fairnessScore={fairness_score:.3f}; "
        "analogy elegance does not become policy truth without safeguards."
    )
    explanation = (
        f"Theory-transfer guidance is bounded scientific-governance guidance only. targetId={target_id}, "
        f"transferStatus={status}, coherence={coherence:.3f}, risk={risk_score:.3f}."
    )

    return TheoryTransferDecision(
        target_id=target_id,
        target_type=target_type,
        transfer_status=status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk_score, 6),
        asymmetry_context=asymmetry_context,
        replication_context=replication_context,
        agency_context=agency_context,
        fairness_context=fairness_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: TheoryTransferDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "transferStatus": d.transfer_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "asymmetryContext": d.asymmetry_context,
        "replicationContext": d.replication_context,
        "agencyContext": d.agency_context,
        "fairnessContext": d.fairness_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    transfer_map = _load_required_artifact(
        THEORY_TRANSFER_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "transfer_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    asymmetry_report = _load_required_artifact(
        DONOR_TARGET_ASYMMETRY_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "transfer_asymmetry_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    replication_gate = _load_required_artifact(
        TRANSFER_REPLICATION_GATE_PATH,
        compatibility_paths=(BRIDGE_DIR / "replication_gate.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    risk_register = _load_required_artifact(
        TRANSFER_RISK_REGISTER_PATH,
        compatibility_paths=(BRIDGE_DIR / "transfer_risk_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    experimental = _load_json(EXPERIMENTAL_AUDIT_PATH)
    theory = _load_json(THEORY_CORPUS_AUDIT_PATH)
    agency = _load_json(AGENCY_MODE_AUDIT_PATH)
    responsibility = _load_json(RESPONSIBILITY_AUDIT_PATH)

    experimental_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(experimental, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    theory_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(theory, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    agency_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(agency, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    responsibility_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(responsibility, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.26 * experimental_risk + 0.26 * theory_risk + 0.24 * agency_risk + 0.24 * responsibility_risk)

    asymmetry_rows = {str(r.get("targetId")): r for r in _parse_rows(asymmetry_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    replication_rows = {str(r.get("targetId")): r for r in _parse_rows(replication_gate.payload, "targets") if isinstance(r.get("targetId"), str)}
    risk_rows = {str(r.get("targetId")): r for r in _parse_rows(risk_register.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            asymmetry_rows=asymmetry_rows,
            replication_rows=replication_rows,
            risk_rows=risk_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(transfer_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [transfer_map, asymmetry_report, replication_gate, risk_register]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(transfer_map.payload, asymmetry_report.payload, replication_gate.payload, risk_register.payload)

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
        "experimental + theory + agency + responsibility state -> donor/target transfer synthesis -> "
        "Sophia theory-transfer audit -> Publisher bounded governance overlays -> human/community review"
    )
    caution = (
        "Theory-transfer recommendations are bounded scientific-governance guidance only and do not certify cross-domain truth "
        "without replication."
    )

    audit_payload = {
        "schema": "theory_transfer_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "theory_transfer_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(THEORY_TRANSFER_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(THEORY_TRANSFER_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia theory-transfer state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    THEORY_TRANSFER_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    THEORY_TRANSFER_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {THEORY_TRANSFER_AUDIT_OUT}")
    print(f"Wrote {THEORY_TRANSFER_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
