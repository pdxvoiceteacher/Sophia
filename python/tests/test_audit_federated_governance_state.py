from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_federated_governance_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "federated_governance_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.federation.fixture",
        "producerCommit": "fixture-ar-0001",
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
    monkeypatch.setattr(module, "STEWARDSHIP_NODE_MAP_PATH", tmp_path / "bridge/stewardship_node_map.json")
    monkeypatch.setattr(module, "FEDERATION_COHERENCE_REPORT_PATH", tmp_path / "bridge/federation_coherence_report.json")
    monkeypatch.setattr(module, "CROSS_NODE_DISSENT_MAP_PATH", tmp_path / "bridge/cross_node_dissent_map.json")
    monkeypatch.setattr(module, "COMMONS_CAPTURE_RISK_REPORT_PATH", tmp_path / "bridge/commons_capture_risk_report.json")
    monkeypatch.setattr(module, "SOCIAL_ENTROPY_AUDIT_PATH", tmp_path / "bridge/social_entropy_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "ARCHITECTURE_REVIEW_AUDIT_PATH", tmp_path / "bridge/architecture_review_audit.json")
    monkeypatch.setattr(module, "COLLABORATIVE_REVIEW_AUDIT_PATH", tmp_path / "bridge/collaborative_review_audit.json")
    monkeypatch.setattr(module, "FEDERATED_GOVERNANCE_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/federated_governance_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "FEDERATED_GOVERNANCE_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/federated_governance_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "stewardship_node_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "federation", "nodeDiversity": 0.70, "federationResilience": 0.64},
                    {"targetId": "target:a", "targetType": "federation", "nodeDiversity": 0.62, "federationResilience": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "federation_coherence_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "federationCoherence": 0.66, "legitimacyBalance": 0.62},
                    {"targetId": "target:a", "federationCoherence": 0.60, "legitimacyBalance": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "cross_node_dissent_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "dissentPortability": 0.66, "dissentBurialRisk": 0.42},
                    {"targetId": "target:a", "dissentPortability": 0.60, "dissentBurialRisk": 0.48},
                ]
            }
        ),
    )
    _write_json(
        bridge / "commons_capture_risk_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "commonsCaptureRisk": 0.34, "centralizationPressure": 0.36, "sovereigntyTransferSignal": 0.30},
                    {"targetId": "target:a", "commonsCaptureRisk": 0.40, "centralizationPressure": 0.42, "sovereigntyTransferSignal": 0.34},
                ]
            }
        ),
    )

    for name in (
        "social_entropy_audit.json",
        "value_alignment_audit.json",
        "architecture_review_audit.json",
        "collaborative_review_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/federated_governance_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/federated_governance_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_federation_status_coverage() -> None:
    cases = [
        (
            "healthy",
            {"nodeDiversity": 0.72, "federationResilience": 0.68},
            {"federationCoherence": 0.68, "legitimacyBalance": 0.66},
            {"dissentPortability": 0.68, "dissentBurialRisk": 0.42},
            {"commonsCaptureRisk": 0.34, "centralizationPressure": 0.36, "sovereigntyTransferSignal": 0.32},
            "federation-healthy",
        ),
        (
            "repair",
            {"nodeDiversity": 0.62, "federationResilience": 0.62},
            {"federationCoherence": 0.52, "legitimacyBalance": 0.50},
            {"dissentPortability": 0.58, "dissentBurialRisk": 0.56},
            {"commonsCaptureRisk": 0.50, "centralizationPressure": 0.52, "sovereigntyTransferSignal": 0.42},
            "repair-priority",
        ),
        (
            "capture",
            {"nodeDiversity": 0.58, "federationResilience": 0.56},
            {"federationCoherence": 0.54, "legitimacyBalance": 0.52},
            {"dissentPortability": 0.56, "dissentBurialRisk": 0.58},
            {"commonsCaptureRisk": 0.74, "centralizationPressure": 0.68, "sovereigntyTransferSignal": 0.52},
            "capture-risk",
        ),
        (
            "dissent",
            {"nodeDiversity": 0.60, "federationResilience": 0.58},
            {"federationCoherence": 0.56, "legitimacyBalance": 0.54},
            {"dissentPortability": 0.50, "dissentBurialRisk": 0.76},
            {"commonsCaptureRisk": 0.54, "centralizationPressure": 0.56, "sovereigntyTransferSignal": 0.46},
            "dissent-burial-risk",
        ),
        (
            "human",
            {"nodeDiversity": 0.60, "federationResilience": 0.58},
            {"federationCoherence": 0.56, "legitimacyBalance": 0.54},
            {"dissentPortability": 0.56, "dissentBurialRisk": 0.58},
            {"commonsCaptureRisk": 0.82, "centralizationPressure": 0.56, "sovereigntyTransferSignal": 0.46},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, coherence, dissent, capture, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "federation", **row},
            coherence_rows={target_id: coherence},
            dissent_rows={target_id: dissent},
            capture_rows={target_id: capture},
            system_risk=0.35,
        )
        statuses.add(decision.federation_status)
        assert decision.federation_status == expected

    assert statuses == {
        "federation-healthy",
        "repair-priority",
        "capture-risk",
        "dissent-burial-risk",
        "require-human-review",
    }


def test_bounded_non_sovereign_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "federation", "nodeDiversity": 0.64, "federationResilience": 0.60},
        coherence_rows={"tone": {"federationCoherence": 0.58, "legitimacyBalance": 0.56}},
        dissent_rows={"tone": {"dissentPortability": 0.58, "dissentBurialRisk": 0.54}},
        capture_rows={"tone": {"commonsCaptureRisk": 0.52, "centralizationPressure": 0.54, "sovereigntyTransferSignal": 0.44}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.node_context,
            decision.dissent_context,
            decision.legitimacy_context,
            decision.capture_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "do not authorize sovereignty transfer" in text
    assert "centralized epistemic rule" in text


def test_anti_capture_and_dissent_burial_handling() -> None:
    capture = module.evaluate_target(
        {"targetId": "capture", "targetType": "federation", "nodeDiversity": 0.58, "federationResilience": 0.56},
        coherence_rows={"capture": {"federationCoherence": 0.54, "legitimacyBalance": 0.52}},
        dissent_rows={"capture": {"dissentPortability": 0.56, "dissentBurialRisk": 0.58}},
        capture_rows={"capture": {"commonsCaptureRisk": 0.82, "centralizationPressure": 0.56, "sovereigntyTransferSignal": 0.46}},
        system_risk=0.35,
    )
    dissent = module.evaluate_target(
        {"targetId": "dissent", "targetType": "federation", "nodeDiversity": 0.60, "federationResilience": 0.58},
        coherence_rows={"dissent": {"federationCoherence": 0.56, "legitimacyBalance": 0.54}},
        dissent_rows={"dissent": {"dissentPortability": 0.50, "dissentBurialRisk": 0.76}},
        capture_rows={"dissent": {"commonsCaptureRisk": 0.54, "centralizationPressure": 0.56, "sovereigntyTransferSignal": 0.46}},
        system_risk=0.35,
    )

    assert capture.federation_status == "require-human-review"
    assert dissent.federation_status == "dissent-burial-risk"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "federation"}]})
    _write_json(tmp_path / "bridge/stewardship_node_map.json", bad_map)

    with pytest.raises(module.FederatedGovernanceInputError):
        module.build_outputs()
