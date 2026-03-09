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

COMMONS_SOVEREIGNTY_MAP_PATH = BRIDGE_DIR / "commons_sovereignty_map.json"
INSTITUTIONAL_CAPTURE_RISK_REPORT_PATH = BRIDGE_DIR / "institutional_capture_risk_report.json"
PUBLIC_TRUST_SIGNAL_MAP_PATH = BRIDGE_DIR / "public_trust_signal_map.json"
CIVILIZATIONAL_INTEGRITY_REPORT_PATH = BRIDGE_DIR / "civilizational_integrity_report.json"

FEDERATED_GOVERNANCE_AUDIT_PATH = BRIDGE_DIR / "federated_governance_audit.json"
SOCIAL_ENTROPY_AUDIT_PATH = BRIDGE_DIR / "social_entropy_audit.json"
COMMONS_PARTICIPATION_AUDIT_PATH = BRIDGE_DIR / "commons_participation_audit.json"
VALUE_ALIGNMENT_AUDIT_PATH = BRIDGE_DIR / "value_alignment_audit.json"
ARCHITECTURE_REVIEW_AUDIT_PATH = BRIDGE_DIR / "architecture_review_audit.json"

COMMONS_SOVEREIGNTY_AUDIT_OUT = BRIDGE_DIR / "commons_sovereignty_audit.json"
COMMONS_SOVEREIGNTY_RECOMMENDATIONS_OUT = BRIDGE_DIR / "commons_sovereignty_recommendations.json"

COMMONS_SOVEREIGNTY_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "commons_sovereignty_audit_v1.schema.json"
COMMONS_SOVEREIGNTY_RECOMMENDATIONS_SCHEMA_PATH = SCHEMA_DIR / "commons_sovereignty_recommendations_v1.schema.json"

SUPPORTED_SCHEMA_VERSION = "commons_sovereignty_v1"
LIVE_PRODUCER_REPO = "Sophia"
FIXTURE_PRODUCER_REPO = "Sophia-Fixtures"
EXPECTED_PRODUCER_REPOS = {LIVE_PRODUCER_REPO, FIXTURE_PRODUCER_REPO}
REQUIRED_PROVENANCE_FIELDS = ("schemaVersion", "producerRepo", "producerModule", "producerCommit", "generatedAt")


class CommonsSovereigntyInputError(RuntimeError):
    pass


@dataclass(slots=True)
class LoadedArtifact:
    path: Path
    payload: dict[str, Any]
    source_mode: str


@dataclass(slots=True)
class CommonsSovereigntyDecision:
    target_id: str
    target_type: str
    sovereignty_status: str
    coherence_score: float
    risk_score: float
    federation_context: str
    trust_context: str
    capture_context: str
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
        "commons-stable": "watch",
        "repair-priority": "docket",
        "capture-risk": "docket",
        "trust-collapse-risk": "suppress",
        "require-human-review": "suppress",
    }[status]


def _validate_provenance(payload: dict[str, Any], *, path: Path) -> None:
    missing = [field for field in REQUIRED_PROVENANCE_FIELDS if not isinstance(payload.get(field), str) or not payload.get(field)]
    if missing:
        raise CommonsSovereigntyInputError(f"Missing required provenance fields in {path}: {', '.join(missing)}")
    if str(payload.get("schemaVersion")) != SUPPORTED_SCHEMA_VERSION:
        raise CommonsSovereigntyInputError(
            f"Unsupported schemaVersion in {path}: {payload.get('schemaVersion')}; supported={SUPPORTED_SCHEMA_VERSION}"
        )
    repo = str(payload.get("producerRepo"))
    if repo not in EXPECTED_PRODUCER_REPOS:
        raise CommonsSovereigntyInputError(
            f"Unexpected producerRepo in {path}: {repo}; expected one of {sorted(EXPECTED_PRODUCER_REPOS)}"
        )


def _load_required_artifact(path: Path, *, compatibility_paths: tuple[Path, ...], allow_compatibility_names: bool) -> LoadedArtifact:
    if path.exists():
        payload = _load_json(path)
        _validate_provenance(payload, path=path)
        return LoadedArtifact(path=path, payload=payload, source_mode="canonical")

    found = [p for p in compatibility_paths if p.exists()]
    if not found:
        raise CommonsSovereigntyInputError(f"Missing required canonical artifact: {path}")
    if not allow_compatibility_names:
        raise CommonsSovereigntyInputError(
            f"Canonical artifact missing ({path}) and deprecated/ambiguous alternatives found: {', '.join(str(p) for p in found)}"
        )

    payload = _load_json(found[0])
    _validate_provenance(payload, path=found[0])
    return LoadedArtifact(path=found[0], payload=payload, source_mode="compatibility")


def _load_supporting_audit(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise CommonsSovereigntyInputError(f"Missing required supporting audit: {path}")
    payload = _load_json(path)
    if not isinstance(payload.get("schema"), str) or not payload.get("schema"):
        raise CommonsSovereigntyInputError(f"Supporting audit missing non-empty schema in {path}")
    if not isinstance(payload.get("records"), list):
        raise CommonsSovereigntyInputError(f"Supporting audit missing records array in {path}")
    return payload


def _classify_mode(arts: list[LoadedArtifact]) -> tuple[str, str]:
    repos = {str(a.payload.get("producerRepo")) for a in arts}
    if repos == {LIVE_PRODUCER_REPO}:
        return "live", ""
    if repos == {FIXTURE_PRODUCER_REPO}:
        return "fixture", "Inputs are fixture commons-sovereignty artifacts; recommendations are non-canonical simulation guidance."
    return "mixed", "MIXED MODE WARNING: commons-sovereignty inputs combine live and fixture producers; verify before action."


def evaluate_target(
    row: dict[str, Any],
    *,
    capture_rows: dict[str, dict[str, Any]],
    trust_rows: dict[str, dict[str, Any]],
    integrity_rows: dict[str, dict[str, Any]],
    system_risk: float,
) -> CommonsSovereigntyDecision:
    target_id = str(row.get("targetId") or "target:unknown")
    target_type = str(row.get("targetType") or "commons-sovereignty-context")

    distribution_resilience = _clamp01(float(row.get("distributionResilience", 0.5)))
    legitimacy_distribution = _clamp01(float(row.get("legitimacyDistribution", 0.5)))

    capture = capture_rows.get(target_id, {})
    institutional_capture_risk = _clamp01(float(capture.get("institutionalCaptureRisk", 0.5)))
    centralization_pressure = _clamp01(float(capture.get("centralizationPressure", 0.5)))

    trust = trust_rows.get(target_id, {})
    public_trust = _clamp01(float(trust.get("publicTrust", 0.5)))
    trust_collapse_signal = _clamp01(float(trust.get("trustCollapseSignal", 0.5)))

    integrity = integrity_rows.get(target_id, {})
    civilizational_integrity = _clamp01(float(integrity.get("civilizationalIntegrity", 0.5)))
    institutional_legibility = _clamp01(float(integrity.get("institutionalLegibility", 0.5)))

    anti_capture = _clamp01(1.0 - 0.5 * institutional_capture_risk - 0.5 * centralization_pressure)

    coherence_score = _clamp01(
        0.16 * distribution_resilience
        + 0.16 * legitimacy_distribution
        + 0.16 * public_trust
        + 0.16 * civilizational_integrity
        + 0.16 * institutional_legibility
        + 0.20 * anti_capture
    )
    risk_score = _clamp01(
        0.18 * institutional_capture_risk
        + 0.16 * centralization_pressure
        + 0.18 * trust_collapse_signal
        + 0.16 * (1.0 - public_trust)
        + 0.16 * (1.0 - civilizational_integrity)
        + 0.16 * system_risk
    )

    if institutional_capture_risk >= 0.82 or centralization_pressure >= 0.84:
        status = "require-human-review"
        rule = "anti-centralization-hard-gate"
    elif trust_collapse_signal >= 0.78 or public_trust <= 0.30:
        status = "trust-collapse-risk"
        rule = "public-trust-recovery-before-expansion"
    elif institutional_capture_risk >= 0.70 or centralization_pressure >= 0.70:
        status = "capture-risk"
        rule = "capture-risk-mitigation"
    elif legitimacy_distribution <= 0.52 or institutional_legibility <= 0.50:
        status = "repair-priority"
        rule = "distributed-legitimacy-repair-priority"
    else:
        status = "commons-stable"
        rule = "distributed-commons-stability-watch"

    federation_context = (
        f"distributionResilience={distribution_resilience:.3f}, legitimacyDistribution={legitimacy_distribution:.3f}, civilizationalIntegrity={civilizational_integrity:.3f}; "
        "distributed legitimacy and redundancy are favored over coordination efficiency."
    )
    trust_context = (
        f"publicTrust={public_trust:.3f}, trustCollapseSignal={trust_collapse_signal:.3f}, institutionalLegibility={institutional_legibility:.3f}; "
        "trust repair must remain public, legible, and non-dominating."
    )
    capture_context = (
        f"institutionalCaptureRisk={institutional_capture_risk:.3f}, centralizationPressure={centralization_pressure:.3f}, targetPublisherAction={_status_to_action(status)}; "
        "recommendations are bounded commons governance guidance only and do not authorize centralized epistemic control or sovereignty transfer."
    )
    explanation = (
        f"Commons sovereignty guidance is bounded commons governance guidance only. targetId={target_id}, "
        f"sovereigntyStatus={status}, coherence={coherence_score:.3f}, risk={risk_score:.3f}."
    )

    return CommonsSovereigntyDecision(
        target_id=target_id,
        target_type=target_type,
        sovereignty_status=status,
        coherence_score=round(coherence_score, 6),
        risk_score=round(risk_score, 6),
        federation_context=federation_context,
        trust_context=trust_context,
        capture_context=capture_context,
        governing_rule=rule,
        explanation=explanation,
        target_publisher_action=_status_to_action(status),
    )


def _to_payload(d: CommonsSovereigntyDecision) -> dict[str, Any]:
    return {
        "targetId": d.target_id,
        "targetType": d.target_type,
        "sovereigntyStatus": d.sovereignty_status,
        "coherenceScore": d.coherence_score,
        "riskScore": d.risk_score,
        "federationContext": d.federation_context,
        "trustContext": d.trust_context,
        "captureContext": d.capture_context,
        "governingRule": d.governing_rule,
        "explanation": d.explanation,
        "targetPublisherAction": d.target_publisher_action,
    }


def build_outputs(*, allow_compatibility_names: bool = False) -> tuple[dict[str, Any], dict[str, Any]]:
    sovereignty_map = _load_required_artifact(
        COMMONS_SOVEREIGNTY_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "sovereignty_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    capture_report = _load_required_artifact(
        INSTITUTIONAL_CAPTURE_RISK_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "capture_risk_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    trust_map = _load_required_artifact(
        PUBLIC_TRUST_SIGNAL_MAP_PATH,
        compatibility_paths=(BRIDGE_DIR / "trust_signal_map.json",),
        allow_compatibility_names=allow_compatibility_names,
    )
    integrity_report = _load_required_artifact(
        CIVILIZATIONAL_INTEGRITY_REPORT_PATH,
        compatibility_paths=(BRIDGE_DIR / "integrity_report.json",),
        allow_compatibility_names=allow_compatibility_names,
    )

    federated = _load_supporting_audit(FEDERATED_GOVERNANCE_AUDIT_PATH)
    social = _load_supporting_audit(SOCIAL_ENTROPY_AUDIT_PATH)
    participation = _load_supporting_audit(COMMONS_PARTICIPATION_AUDIT_PATH)
    value = _load_supporting_audit(VALUE_ALIGNMENT_AUDIT_PATH)
    architecture = _load_supporting_audit(ARCHITECTURE_REVIEW_AUDIT_PATH)

    federated_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(federated, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    social_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(social, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    participation_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(participation, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    value_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(value, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    architecture_risk = _safe_mean([float(r.get("riskScore")) for r in _parse_rows(architecture, "records") if isinstance(r.get("riskScore"), (int, float))], 0.45)
    system_risk = _clamp01(0.20 * federated_risk + 0.20 * social_risk + 0.20 * participation_risk + 0.20 * value_risk + 0.20 * architecture_risk)

    capture_rows = {str(r.get("targetId")): r for r in _parse_rows(capture_report.payload, "targets") if isinstance(r.get("targetId"), str)}
    trust_rows = {str(r.get("targetId")): r for r in _parse_rows(trust_map.payload, "targets") if isinstance(r.get("targetId"), str)}
    integrity_rows = {str(r.get("targetId")): r for r in _parse_rows(integrity_report.payload, "targets") if isinstance(r.get("targetId"), str)}

    decisions = [
        evaluate_target(
            row,
            capture_rows=capture_rows,
            trust_rows=trust_rows,
            integrity_rows=integrity_rows,
            system_risk=system_risk,
        )
        for row in _parse_rows(sovereignty_map.payload, "targets")
    ]
    decisions = sorted(decisions, key=lambda d: d.target_id)

    loaded = [sovereignty_map, capture_report, trust_map, integrity_report]
    mode, warning = _classify_mode(loaded)
    created_at = _resolve_created_at(sovereignty_map.payload, capture_report.payload, trust_map.payload, integrity_report.payload)

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
        "supportingAudits": [
            _display_path(FEDERATED_GOVERNANCE_AUDIT_PATH),
            _display_path(SOCIAL_ENTROPY_AUDIT_PATH),
            _display_path(COMMONS_PARTICIPATION_AUDIT_PATH),
            _display_path(VALUE_ALIGNMENT_AUDIT_PATH),
            _display_path(ARCHITECTURE_REVIEW_AUDIT_PATH),
        ],
    }

    caution = (
        "Commons sovereignty recommendations are bounded commons governance guidance only and do not authorize centralized epistemic control."
    )

    audit_payload = {
        "schema": "commons_sovereignty_audit_v1",
        "created_at": created_at,
        "caution": caution,
        "metadata": metadata,
        "records": [_to_payload(d) for d in decisions],
    }
    rec_payload = {
        "schema": "commons_sovereignty_recommendations_v1",
        "created_at": created_at,
        "caution": caution,
        "metadata": metadata,
        "recommendations": [_to_payload(d) for d in decisions],
    }

    Draft202012Validator(_load_json(COMMONS_SOVEREIGNTY_AUDIT_SCHEMA_PATH)).validate(audit_payload)
    Draft202012Validator(_load_json(COMMONS_SOVEREIGNTY_RECOMMENDATIONS_SCHEMA_PATH)).validate(rec_payload)
    return audit_payload, rec_payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia commons sovereignty state audit")
    parser.add_argument("--allow-compatibility-names", action="store_true")
    args = parser.parse_args(argv)

    audit_payload, rec_payload = build_outputs(allow_compatibility_names=args.allow_compatibility_names)
    COMMONS_SOVEREIGNTY_AUDIT_OUT.write_text(json.dumps(audit_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    COMMONS_SOVEREIGNTY_RECOMMENDATIONS_OUT.write_text(json.dumps(rec_payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {COMMONS_SOVEREIGNTY_AUDIT_OUT}")
    print(f"Wrote {COMMONS_SOVEREIGNTY_RECOMMENDATIONS_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
