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

REVIEW_PACKET_MAP_PATH = BRIDGE_DIR / "review_packet_map.json"
REVIEW_PACKET_SUMMARY_PATH = BRIDGE_DIR / "review_packet_summary.json"
NARRATIVE_SYNTHESIS_MAP_PATH = BRIDGE_DIR / "narrative_synthesis_map.json"
UNCERTAINTY_DISCLOSURE_REPORT_PATH = BRIDGE_DIR / "uncertainty_disclosure_report.json"

INVESTIGATION_AUDIT_PATH = BRIDGE_DIR / "investigation_audit.json"
VERIFICATION_AUDIT_PATH = BRIDGE_DIR / "verification_audit.json"
PUBLIC_RECORD_AUDIT_PATH = BRIDGE_DIR / "public_record_audit.json"
EVIDENCE_AUTHORITY_AUDIT_PATH = BRIDGE_DIR / "evidence_authority_audit.json"
ENVIRONMENT_AUDIT_PATH = BRIDGE_DIR / "environment_audit.json"

REVIEW_PACKET_AUDIT_OUT = BRIDGE_DIR / "review_packet_audit.json"
REVIEW_PACKET_RECOMMENDATIONS_OUT = BRIDGE_DIR / "review_packet_recommendations.json"

REVIEW_PACKET_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "review_packet_audit_v1.schema.json"
REVIEW_PACKET_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "review_packet_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "review_packet_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class ReviewPacketInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class ReviewPacketDecision:
    target_id: str
    target_type: str
    packet_status: str
    coherence_score: float
    risk_score: float
    maturity_context: str
    ambiguity_context: str
    authority_context: str
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
        "review-ready": "docket",
        "provisional": "watch",
        "uncertainty-heavy": "watch",
        "verify-first": "suppress",
        "require-human-review": "docket",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise ReviewPacketInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")

    schema_version = str(payload.get("schemaVersion"))
    if schema_version != SUPPORTED_SCHEMA_VERSION:
        raise ReviewPacketInputError(f"Unsupported schemaVersion in {path}: {schema_version}; supported={SUPPORTED_SCHEMA_VERSION}")

    producer_repo = str(payload.get("producerRepo"))
    if producer_repo not in EXPECTED_PRODUCER_REPOS:
        raise ReviewPacketInputError(
            f"Unexpected producerRepo in {path}: {producer_repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(canonical_path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if canonical_path.exists():
        payload = _load_json(canonical_path)
        _validate_provenance(payload, path=canonical_path)
        return LoadedArtifact(path=canonical_path, payload=payload, source_mode="canonical")

    available_compat = [path for path in compatibility_paths if path.exists()]
    if not available_compat:
        raise ReviewPacketInputError(f"Missing required canonical artifact: {canonical_path}")

    if not allow_compatibility_names:
        names = ", ".join(str(path) for path in available_compat)
        raise ReviewPacketInputError(
            f"Canonical artifact missing ({canonical_path}) and deprecated/ambiguous alternatives found: {names}. "
            "Re-run with --allow-compatibility-names only for explicit migration fallback."
        )

    compat_path = available_compat[0]
    payload = _load_json(compat_path)
    _validate_provenance(payload, path=compat_path)
    return LoadedArtifact(path=compat_path, payload=payload, source_mode="compatibility")


def _classify_input_mode(artifacts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(item.payload.get("producerRepo")) for item in artifacts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture review-packet artifacts; output is non-canonical simulation guidance."
    return (
        "mixed",
        "MIXED MODE WARNING: review-packet inputs combine live and fixture producers; review provenance before action.",
    )


def evaluate_target(
    row: dict[str, Any],
    *,
    summary: dict[str, Any],
    narrative_rows: dict[str, dict[str, Any]],
    disclosure_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> ReviewPacketDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "review-packet")

    packet_maturity = _clamp01(float(row.get("packetMaturity", summary.get("meanPacketMaturity", 0.5))))
    packet_confidence = _clamp01(float(row.get("packetConfidence", summary.get("meanPacketConfidence", 0.5))))

    narrative = narrative_rows.get(target_id, {})
    synthesis_confidence = _clamp01(float(narrative.get("synthesisConfidence", summary.get("meanSynthesisConfidence", 0.5))))
    ambiguity_score = _clamp01(float(narrative.get("ambiguityScore", summary.get("meanAmbiguityScore", 0.45))))

    disclosure = disclosure_rows.get(target_id, {})
    disclosure_completeness = _clamp01(float(disclosure.get("disclosureCompleteness", summary.get("meanDisclosureCompleteness", 0.55))))
    uncertainty_load = _clamp01(float(disclosure.get("uncertaintyLoad", summary.get("meanUncertaintyLoad", 0.4))))
    contradiction_score = _clamp01(float(disclosure.get("contradictionScore", summary.get("meanContradictionScore", 0.4))))

    coherence = _clamp01(
        0.24 * packet_maturity
        + 0.20 * packet_confidence
        + 0.18 * synthesis_confidence
        + 0.16 * disclosure_completeness
        + 0.12 * (1.0 - ambiguity_score)
        + 0.10 * (1.0 - contradiction_score)
    )

    risk = _clamp01(
        0.22 * (1.0 - disclosure_completeness)
        + 0.20 * uncertainty_load
        + 0.18 * ambiguity_score
        + 0.16 * contradiction_score
        + 0.12 * (1.0 - packet_maturity)
        + 0.12 * system_risk
    )

    if contradiction_score >= 0.80 and ambiguity_score >= 0.76:
        packet_status = "require-human-review"
        rule = "stacked-ambiguity-contradiction-review"
    elif disclosure_completeness <= 0.36:
        packet_status = "verify-first"
        rule = "disclosure-minimum-enforcement"
    elif uncertainty_load >= 0.70 or ambiguity_score >= 0.70:
        packet_status = "uncertainty-heavy"
        rule = "uncertainty-disclosure-heavy"
    elif packet_maturity >= 0.72 and disclosure_completeness >= 0.70 and risk <= 0.42:
        packet_status = "review-ready"
        rule = "review-ready-under-maturity-bounds"
    else:
        packet_status = "provisional"
        rule = "provisional-packet-guidance"

    maturity_context = (
        f"packetMaturity={packet_maturity:.3f}, packetConfidence={packet_confidence:.3f}, synthesisConfidence={synthesis_confidence:.3f}; "
        "packet synthesis remains bounded by maturity ceilings."
    )
    ambiguity_context = (
        f"ambiguityScore={ambiguity_score:.3f}, uncertaintyLoad={uncertainty_load:.3f}, disclosureCompleteness={disclosure_completeness:.3f}; "
        "explicit uncertainty disclosure is mandatory."
    )
    authority_context = (
        f"contradictionScore={contradiction_score:.3f}, systemRisk={system_risk:.3f}; "
        "review packets guide human review and do not produce automatic adjudication."
    )

    explanation = (
        f"Review-packet guidance is bounded human-review guidance only. targetId={target_id}, "
        f"packetStatus={packet_status}, coherence={coherence:.3f}, risk={risk:.3f}."
    )

    return ReviewPacketDecision(
        target_id=target_id,
        target_type=target_type,
        packet_status=packet_status,
        coherence_score=round(coherence, 6),
        risk_score=round(risk, 6),
        maturity_context=maturity_context,
        ambiguity_context=ambiguity_context,
        authority_context=authority_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(packet_status),
    )


def _to_payload(decision: ReviewPacketDecision) -> dict[str, Any]:
    return {
        "targetId": decision.target_id,
        "targetType": decision.target_type,
        "packetStatus": decision.packet_status,
        "coherenceScore": decision.coherence_score,
        "riskScore": decision.risk_score,
        "maturityContext": decision.maturity_context,
        "ambiguityContext": decision.ambiguity_context,
        "authorityContext": decision.authority_context,
        "governingRule": decision.governing_rule,
        "explanation": decision.explanation,
        "targetPublisherAction": decision.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    packet_map_artifact = _load_required_artifact(
        REVIEW_PACKET_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "review_packets.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    packet_summary_artifact = _load_required_artifact(
        REVIEW_PACKET_SUMMARY_PATH,
        compatibility_paths=(BRIDGE_DIR / "packet_summary.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    narrative_map_artifact = _load_required_artifact(
        NARRATIVE_SYNTHESIS_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "narrative_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    disclosure_report_artifact = _load_required_artifact(
        UNCERTAINTY_DISCLOSURE_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "uncertainty_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    packet_map = packet_map_artifact.payload
    packet_summary = packet_summary_artifact.payload
    narrative_map = narrative_map_artifact.payload
    disclosure_report = disclosure_report_artifact.payload

    investigation = _load_json(INVESTIGATION_AUDIT_PATH)
    verification = _load_json(VERIFICATION_AUDIT_PATH)
    public_record = _load_json(PUBLIC_RECORD_AUDIT_PATH)
    evidence_authority = _load_json(EVIDENCE_AUTHORITY_AUDIT_PATH)
    environment = _load_json(ENVIRONMENT_AUDIT_PATH)

    investigation_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(investigation, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    verification_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(verification, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    public_record_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(public_record, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    authority_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(evidence_authority, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    environment_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(environment, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)

    system_risk = _clamp01(
        0.24 * investigation_risk
        + 0.22 * verification_risk
        + 0.20 * public_record_risk
        + 0.18 * authority_risk
        + 0.16 * environment_risk
    )

    narrative_rows = {str(row.get("targetId")): row for row in _parse_rows(narrative_map, "targets") if isinstance(row.get("targetId"), str)}
    disclosure_rows = {str(row.get("targetId")): row for row in _parse_rows(disclosure_report, "targets") if isinstance(row.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            summary=packet_summary,
            narrative_rows=narrative_rows,
            disclosure_rows=disclosure_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(packet_map, "targets")
    ]
    decisions = sorted(decisions, key=lambda decision: decision.target_id)

    loaded = [packet_map_artifact, packet_summary_artifact, narrative_map_artifact, disclosure_report_artifact]
    input_mode, input_warning = _classify_input_mode(loaded)
    created_at = _resolve_created_at(packet_map, packet_summary, narrative_map, disclosure_report)

    metadata = {
        "inputMode": input_mode,
        "inputModeWarning": input_warning,
        "systemRisk": round(system_risk, 6),
        "inputArtifacts": [
            {
                "path": str(item.path.relative_to(REPO_ROOT)) if item.path.is_relative_to(REPO_ROOT) else str(item.path),
                "sourceMode": item.source_mode,
                "schemaVersion": str(item.payload.get("schemaVersion")),
                "producerRepo": str(item.payload.get("producerRepo")),
                "producerModule": str(item.payload.get("producerModule")),
                "producerCommit": str(item.payload.get("producerCommit")),
                "generatedAt": str(item.payload.get("generatedAt")),
            }
            for item in loaded
        ],
    }

    phaselock = (
        "investigation / verification / evidence-authority state -> CoherenceLattice review-packet formalization -> "
        "Sophia packet audit -> Publisher review-packet overlays -> human/community bounded review"
    )
    caution = (
        "Review-packet recommendations are bounded human-review guidance only and do not convert packets into "
        "verdicts, accusations, or public allegations."
    )

    audit_payload = {
        "schema": "review_packet_audit_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(decision) for decision in decisions],
    }
    recommendations_payload = {
        "schema": "review_packet_recommendations_v1",
        "created_at": created_at,
        "phaselock": phaselock,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(decision) for decision in decisions],
    }

    Draft202012Validator(_load_json(REVIEW_PACKET_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(REVIEW_PACKET_RECOMMENDATIONS_SCHEMA_PATH)).validate(recommendations_payload)
    return audit_payload, recommendations_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia review-packet state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, recommendations_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    REVIEW_PACKET_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    REVIEW_PACKET_RECOMMENDATIONS_OUT.write_text(json.dumps(recommendations_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {REVIEW_PACKET_AUDIT_OUT}")
    print(f"Wrote {REVIEW_PACKET_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
