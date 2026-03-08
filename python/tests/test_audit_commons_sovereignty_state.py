from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_commons_sovereignty_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "commons_sovereignty_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.commons_sovereignty.fixture",
        "producerCommit": "fixture-au-0001",
        "generatedAt": "2026-04-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {
        "schema": "audit_fixture_v1",
        "created_at": "2026-04-08T00:00:00Z",
        "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)],
    }


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_MAP_PATH", tmp_path / "bridge/commons_sovereignty_map.json")
    monkeypatch.setattr(module, "INSTITUTIONAL_CAPTURE_RISK_REPORT_PATH", tmp_path / "bridge/institutional_capture_risk_report.json")
    monkeypatch.setattr(module, "PUBLIC_TRUST_SIGNAL_MAP_PATH", tmp_path / "bridge/public_trust_signal_map.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_INTEGRITY_REPORT_PATH", tmp_path / "bridge/civilizational_integrity_report.json")
    monkeypatch.setattr(module, "FEDERATED_GOVERNANCE_AUDIT_PATH", tmp_path / "bridge/federated_governance_audit.json")
    monkeypatch.setattr(module, "SOCIAL_ENTROPY_AUDIT_PATH", tmp_path / "bridge/social_entropy_audit.json")
    monkeypatch.setattr(module, "COMMONS_PARTICIPATION_AUDIT_PATH", tmp_path / "bridge/commons_participation_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "ARCHITECTURE_REVIEW_AUDIT_PATH", tmp_path / "bridge/architecture_review_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/commons_sovereignty_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "COMMONS_SOVEREIGNTY_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/commons_sovereignty_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "commons_sovereignty_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "commons", "distributionResilience": 0.70, "legitimacyDistribution": 0.68},
                    {"targetId": "target:a", "targetType": "commons", "distributionResilience": 0.62, "legitimacyDistribution": 0.60},
                ]
            }
        ),
    )
    _write_json(
        bridge / "institutional_capture_risk_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "institutionalCaptureRisk": 0.42, "centralizationPressure": 0.40},
                    {"targetId": "target:a", "institutionalCaptureRisk": 0.50, "centralizationPressure": 0.48},
                ]
            }
        ),
    )
    _write_json(
        bridge / "public_trust_signal_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "publicTrust": 0.68, "trustCollapseSignal": 0.34},
                    {"targetId": "target:a", "publicTrust": 0.60, "trustCollapseSignal": 0.40},
                ]
            }
        ),
    )
    _write_json(
        bridge / "civilizational_integrity_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "civilizationalIntegrity": 0.70, "institutionalLegibility": 0.68},
                    {"targetId": "target:a", "civilizationalIntegrity": 0.62, "institutionalLegibility": 0.58},
                ]
            }
        ),
    )

    for name in (
        "federated_governance_audit.json",
        "social_entropy_audit.json",
        "commons_participation_audit.json",
        "value_alignment_audit.json",
        "architecture_review_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/commons_sovereignty_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/commons_sovereignty_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_status_coverage() -> None:
    cases = [
        (
            "stable",
            {"distributionResilience": 0.72, "legitimacyDistribution": 0.70},
            {"institutionalCaptureRisk": 0.40, "centralizationPressure": 0.38},
            {"publicTrust": 0.70, "trustCollapseSignal": 0.30},
            {"civilizationalIntegrity": 0.72, "institutionalLegibility": 0.66},
            "commons-stable",
        ),
        (
            "repair",
            {"distributionResilience": 0.60, "legitimacyDistribution": 0.50},
            {"institutionalCaptureRisk": 0.54, "centralizationPressure": 0.50},
            {"publicTrust": 0.58, "trustCollapseSignal": 0.44},
            {"civilizationalIntegrity": 0.60, "institutionalLegibility": 0.48},
            "repair-priority",
        ),
        (
            "capture",
            {"distributionResilience": 0.60, "legitimacyDistribution": 0.58},
            {"institutionalCaptureRisk": 0.72, "centralizationPressure": 0.64},
            {"publicTrust": 0.58, "trustCollapseSignal": 0.44},
            {"civilizationalIntegrity": 0.60, "institutionalLegibility": 0.58},
            "capture-risk",
        ),
        (
            "collapse",
            {"distributionResilience": 0.58, "legitimacyDistribution": 0.56},
            {"institutionalCaptureRisk": 0.60, "centralizationPressure": 0.58},
            {"publicTrust": 0.28, "trustCollapseSignal": 0.80},
            {"civilizationalIntegrity": 0.56, "institutionalLegibility": 0.52},
            "trust-collapse-risk",
        ),
        (
            "human",
            {"distributionResilience": 0.58, "legitimacyDistribution": 0.56},
            {"institutionalCaptureRisk": 0.84, "centralizationPressure": 0.86},
            {"publicTrust": 0.58, "trustCollapseSignal": 0.44},
            {"civilizationalIntegrity": 0.56, "institutionalLegibility": 0.52},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, capture, trust, integrity, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "commons", **row},
            capture_rows={target_id: capture},
            trust_rows={target_id: trust},
            integrity_rows={target_id: integrity},
            system_risk=0.35,
        )
        statuses.add(decision.sovereignty_status)
        assert decision.sovereignty_status == expected

    assert statuses == {
        "commons-stable",
        "repair-priority",
        "capture-risk",
        "trust-collapse-risk",
        "require-human-review",
    }


def test_anti_centralization_behavior() -> None:
    decision = module.evaluate_target(
        {"targetId": "capture", "targetType": "commons", "distributionResilience": 0.60, "legitimacyDistribution": 0.56},
        capture_rows={"capture": {"institutionalCaptureRisk": 0.84, "centralizationPressure": 0.84}},
        trust_rows={"capture": {"publicTrust": 0.60, "trustCollapseSignal": 0.42}},
        integrity_rows={"capture": {"civilizationalIntegrity": 0.58, "institutionalLegibility": 0.56}},
        system_risk=0.35,
    )

    assert decision.sovereignty_status == "require-human-review"
    assert decision.target_publisher_action == "suppress"


def test_bounded_language_no_sovereignty_transfer() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "commons", "distributionResilience": 0.64, "legitimacyDistribution": 0.60},
        capture_rows={"tone": {"institutionalCaptureRisk": 0.52, "centralizationPressure": 0.50}},
        trust_rows={"tone": {"publicTrust": 0.60, "trustCollapseSignal": 0.42}},
        integrity_rows={"tone": {"civilizationalIntegrity": 0.60, "institutionalLegibility": 0.58}},
        system_risk=0.35,
    )

    text = " ".join([decision.federation_context, decision.trust_context, decision.capture_context, decision.explanation]).lower()
    assert "bounded" in text
    assert "do not authorize centralized epistemic control" in text
    assert "sovereignty transfer" in text
    assert "absolute authority" not in text


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "commons"}]})
    _write_json(tmp_path / "bridge/commons_sovereignty_map.json", bad)

    with pytest.raises(module.CommonsSovereigntyInputError):
        module.build_outputs()
