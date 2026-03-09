from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_meta_cognition_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "meta_cognition_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.meta_cognition.fixture",
        "producerCommit": "fixture-ao-0001",
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
    monkeypatch.setattr(module, "META_COGNITION_MAP_PATH", tmp_path / "bridge/meta_cognition_map.json")
    monkeypatch.setattr(module, "SAFETY_CONSTRAINT_AUDIT_PATH", tmp_path / "bridge/safety_constraint_audit.json")
    monkeypatch.setattr(module, "ARCHITECTURE_EFFICIENCY_REPORT_PATH", tmp_path / "bridge/architecture_efficiency_report.json")
    monkeypatch.setattr(module, "STRUCTURAL_CHANGE_GATE_PATH", tmp_path / "bridge/structural_change_gate.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "CURIOSITY_AUDIT_PATH", tmp_path / "bridge/curiosity_audit.json")
    monkeypatch.setattr(module, "SYSTEM_FORECAST_AUDIT_PATH", tmp_path / "bridge/system_forecast_audit.json")
    monkeypatch.setattr(module, "RESPONSIBILITY_AUDIT_PATH", tmp_path / "bridge/responsibility_audit.json")
    monkeypatch.setattr(module, "META_COGNITION_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/meta_cognition_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "META_COGNITION_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/meta_cognition_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "meta_cognition_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "meta", "architectureCoherence": 0.66, "adaptationNeed": 0.44},
                    {"targetId": "target:a", "targetType": "meta", "architectureCoherence": 0.62, "adaptationNeed": 0.48},
                ]
            }
        ),
    )
    _write_json(
        bridge / "safety_constraint_audit.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "immutableConstraintPressure": 0.40, "safetyRegressionRisk": 0.42},
                    {"targetId": "target:a", "immutableConstraintPressure": 0.44, "safetyRegressionRisk": 0.46},
                ]
            }
        ),
    )
    _write_json(
        bridge / "architecture_efficiency_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "efficiencyGap": 0.54, "optimizationReadiness": 0.62},
                    {"targetId": "target:a", "efficiencyGap": 0.58, "optimizationReadiness": 0.60},
                ]
            }
        ),
    )
    _write_json(
        bridge / "structural_change_gate.json",
        _artifact(
            {
                "targets": [
                    {
                        "targetId": "target:z",
                        "coreConstraintModificationRequest": False,
                        "humanApprovalPresent": False,
                        "autonomousReconfigurationRisk": 0.32,
                    },
                    {
                        "targetId": "target:a",
                        "coreConstraintModificationRequest": False,
                        "humanApprovalPresent": False,
                        "autonomousReconfigurationRisk": 0.36,
                    },
                ]
            }
        ),
    )

    for name in (
        "value_alignment_audit.json",
        "curiosity_audit.json",
        "system_forecast_audit.json",
        "responsibility_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/meta_cognition_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/meta_cognition_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_meta_status_coverage() -> None:
    cases = [
        (
            "watch",
            {"architectureCoherence": 0.68, "adaptationNeed": 0.46},
            {"immutableConstraintPressure": 0.42, "safetyRegressionRisk": 0.44},
            {"efficiencyGap": 0.52, "optimizationReadiness": 0.56},
            {"coreConstraintModificationRequest": False, "humanApprovalPresent": False, "autonomousReconfigurationRisk": 0.34},
            "meta-watch",
        ),
        (
            "efficiency",
            {"architectureCoherence": 0.66, "adaptationNeed": 0.50},
            {"immutableConstraintPressure": 0.44, "safetyRegressionRisk": 0.46},
            {"efficiencyGap": 0.70, "optimizationReadiness": 0.66},
            {"coreConstraintModificationRequest": False, "humanApprovalPresent": False, "autonomousReconfigurationRisk": 0.34},
            "meta-efficiency-opportunity",
        ),
        (
            "gov",
            {"architectureCoherence": 0.62, "adaptationNeed": 0.54},
            {"immutableConstraintPressure": 0.76, "safetyRegressionRisk": 0.60},
            {"efficiencyGap": 0.56, "optimizationReadiness": 0.60},
            {"coreConstraintModificationRequest": False, "humanApprovalPresent": False, "autonomousReconfigurationRisk": 0.36},
            "meta-governance-review",
        ),
        (
            "human",
            {"architectureCoherence": 0.66, "adaptationNeed": 0.50},
            {"immutableConstraintPressure": 0.44, "safetyRegressionRisk": 0.46},
            {"efficiencyGap": 0.70, "optimizationReadiness": 0.66},
            {"coreConstraintModificationRequest": True, "humanApprovalPresent": False, "autonomousReconfigurationRisk": 0.34},
            "meta-require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, safety, efficiency, gate, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "meta", **row},
            safety_rows={target_id: safety},
            efficiency_rows={target_id: efficiency},
            gate_rows={target_id: gate},
            system_risk=0.35,
        )
        statuses.add(decision.meta_status)
        assert decision.meta_status == expected

    assert statuses == {
        "meta-watch",
        "meta-efficiency-opportunity",
        "meta-governance-review",
        "meta-require-human-review",
    }


def test_bounded_non_autonomous_reconfiguration_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "meta", "architectureCoherence": 0.66, "adaptationNeed": 0.48},
        safety_rows={"tone": {"immutableConstraintPressure": 0.46, "safetyRegressionRisk": 0.44}},
        efficiency_rows={"tone": {"efficiencyGap": 0.62, "optimizationReadiness": 0.64}},
        gate_rows={"tone": {"coreConstraintModificationRequest": False, "humanApprovalPresent": False, "autonomousReconfigurationRisk": 0.34}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.architecture_context,
            decision.efficiency_context,
            decision.safety_context,
            decision.governance_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "cannot autonomously modify core safety constraints" in text
    assert "human approval" in text
    assert "override" not in text


def test_core_constraint_modification_requires_human_review() -> None:
    decision = module.evaluate_target(
        {"targetId": "gate", "targetType": "meta", "architectureCoherence": 0.72, "adaptationNeed": 0.44},
        safety_rows={"gate": {"immutableConstraintPressure": 0.40, "safetyRegressionRisk": 0.42}},
        efficiency_rows={"gate": {"efficiencyGap": 0.66, "optimizationReadiness": 0.68}},
        gate_rows={"gate": {"coreConstraintModificationRequest": True, "humanApprovalPresent": False, "autonomousReconfigurationRisk": 0.36}},
        system_risk=0.35,
    )

    assert decision.meta_status == "meta-require-human-review"
    assert decision.target_publisher_action == "docket"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "meta"}]})
    _write_json(tmp_path / "bridge/meta_cognition_map.json", bad_map)

    with pytest.raises(module.MetaCognitionInputError):
        module.build_outputs()
