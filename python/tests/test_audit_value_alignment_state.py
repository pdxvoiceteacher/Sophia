from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_value_alignment_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "value_alignment_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.value_alignment.fixture",
        "producerCommit": "fixture-an-0001",
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
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_MAP_PATH", tmp_path / "bridge/value_alignment_map.json")
    monkeypatch.setattr(module, "MORAL_CONSEQUENCE_REPORT_PATH", tmp_path / "bridge/moral_consequence_report.json")
    monkeypatch.setattr(module, "COMMUNITY_PRIORITY_SIGNAL_PATH", tmp_path / "bridge/community_priority_signal.json")
    monkeypatch.setattr(module, "VALUE_OVERRIDE_BOUNDARY_GATE_PATH", tmp_path / "bridge/value_override_boundary_gate.json")
    monkeypatch.setattr(module, "CURIOSITY_AUDIT_PATH", tmp_path / "bridge/curiosity_audit.json")
    monkeypatch.setattr(module, "SYSTEM_FORECAST_AUDIT_PATH", tmp_path / "bridge/system_forecast_audit.json")
    monkeypatch.setattr(module, "THEORY_TRANSFER_AUDIT_PATH", tmp_path / "bridge/theory_transfer_audit.json")
    monkeypatch.setattr(module, "RESPONSIBILITY_AUDIT_PATH", tmp_path / "bridge/responsibility_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/value_alignment_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "VALUE_ALIGNMENT_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/value_alignment_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "value_alignment_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "value", "knowledgePrioritySignal": 0.68, "valueClarity": 0.62},
                    {"targetId": "target:a", "targetType": "value", "knowledgePrioritySignal": 0.60, "valueClarity": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "moral_consequence_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "consequenceSalience": 0.66, "externalityRisk": 0.42},
                    {"targetId": "target:a", "consequenceSalience": 0.62, "externalityRisk": 0.46},
                ]
            }
        ),
    )
    _write_json(
        bridge / "community_priority_signal.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "communityConsensus": 0.64, "dissentSignal": 0.34},
                    {"targetId": "target:a", "communityConsensus": 0.60, "dissentSignal": 0.40},
                ]
            }
        ),
    )
    _write_json(
        bridge / "value_override_boundary_gate.json",
        _artifact(
            {
                "targets": [
                    {
                        "targetId": "target:z",
                        "valueOverrideRisk": 0.30,
                        "ethicsReplacementRisk": 0.32,
                        "autonomousValueOverrideRequested": False,
                    },
                    {
                        "targetId": "target:a",
                        "valueOverrideRisk": 0.34,
                        "ethicsReplacementRisk": 0.36,
                        "autonomousValueOverrideRequested": False,
                    },
                ]
            }
        ),
    )

    for name in (
        "curiosity_audit.json",
        "system_forecast_audit.json",
        "theory_transfer_audit.json",
        "responsibility_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/value_alignment_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/value_alignment_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_value_status_coverage() -> None:
    cases = [
        (
            "high",
            {"knowledgePrioritySignal": 0.74, "valueClarity": 0.66},
            {"consequenceSalience": 0.70, "externalityRisk": 0.40},
            {"communityConsensus": 0.66, "dissentSignal": 0.32},
            {"valueOverrideRisk": 0.30, "ethicsReplacementRisk": 0.32, "autonomousValueOverrideRequested": False},
            "priority-high",
        ),
        (
            "moderate",
            {"knowledgePrioritySignal": 0.62, "valueClarity": 0.58},
            {"consequenceSalience": 0.62, "externalityRisk": 0.46},
            {"communityConsensus": 0.56, "dissentSignal": 0.44},
            {"valueOverrideRisk": 0.30, "ethicsReplacementRisk": 0.32, "autonomousValueOverrideRequested": False},
            "priority-moderate",
        ),
        (
            "watch",
            {"knowledgePrioritySignal": 0.54, "valueClarity": 0.50},
            {"consequenceSalience": 0.56, "externalityRisk": 0.48},
            {"communityConsensus": 0.52, "dissentSignal": 0.46},
            {"valueOverrideRisk": 0.30, "ethicsReplacementRisk": 0.32, "autonomousValueOverrideRequested": False},
            "priority-watch",
        ),
        (
            "risk",
            {"knowledgePrioritySignal": 0.66, "valueClarity": 0.60},
            {"consequenceSalience": 0.66, "externalityRisk": 0.78},
            {"communityConsensus": 0.56, "dissentSignal": 0.60},
            {"valueOverrideRisk": 0.30, "ethicsReplacementRisk": 0.32, "autonomousValueOverrideRequested": False},
            "value-risk",
        ),
        (
            "human",
            {"knowledgePrioritySignal": 0.72, "valueClarity": 0.64},
            {"consequenceSalience": 0.70, "externalityRisk": 0.44},
            {"communityConsensus": 0.64, "dissentSignal": 0.34},
            {"valueOverrideRisk": 0.82, "ethicsReplacementRisk": 0.32, "autonomousValueOverrideRequested": False},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, consequence, community, boundary, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "value", **row},
            consequence_rows={target_id: consequence},
            community_rows={target_id: community},
            boundary_rows={target_id: boundary},
            system_risk=0.35,
        )
        statuses.add(decision.value_status)
        assert decision.value_status == expected

    assert statuses == {
        "priority-high",
        "priority-moderate",
        "priority-watch",
        "value-risk",
        "require-human-review",
    }


def test_bounded_non_replacement_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "value", "knowledgePrioritySignal": 0.66, "valueClarity": 0.60},
        consequence_rows={"tone": {"consequenceSalience": 0.62, "externalityRisk": 0.48}},
        community_rows={"tone": {"communityConsensus": 0.58, "dissentSignal": 0.42}},
        boundary_rows={"tone": {"valueOverrideRisk": 0.34, "ethicsReplacementRisk": 0.36, "autonomousValueOverrideRequested": False}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.consequence_context,
            decision.community_context,
            decision.uncertainty_context,
            decision.governance_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "human communities retain authority" in text
    assert "cannot replace human ethics" in text
    assert "final moral verdict" not in text


def test_value_override_safeguard() -> None:
    decision = module.evaluate_target(
        {"targetId": "gate", "targetType": "value", "knowledgePrioritySignal": 0.76, "valueClarity": 0.66},
        consequence_rows={"gate": {"consequenceSalience": 0.72, "externalityRisk": 0.40}},
        community_rows={"gate": {"communityConsensus": 0.66, "dissentSignal": 0.34}},
        boundary_rows={"gate": {"valueOverrideRisk": 0.44, "ethicsReplacementRisk": 0.42, "autonomousValueOverrideRequested": True}},
        system_risk=0.35,
    )

    assert decision.value_status == "require-human-review"
    assert decision.target_publisher_action == "docket"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "value"}]})
    _write_json(tmp_path / "bridge/value_alignment_map.json", bad_map)

    with pytest.raises(module.ValueAlignmentInputError):
        module.build_outputs()
