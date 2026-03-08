from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_architecture_evolution_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "architecture_evolution_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.architecture_evolution.fixture",
        "producerCommit": "fixture-ap-0001",
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
    monkeypatch.setattr(module, "ARCHITECTURE_EVOLUTION_MAP_PATH", tmp_path / "bridge/architecture_evolution_map.json")
    monkeypatch.setattr(module, "ARCHITECTURE_EFFICIENCY_REPORT_PATH", tmp_path / "bridge/architecture_efficiency_report.json")
    monkeypatch.setattr(module, "ARCHITECTURE_GOVERNANCE_REPORT_PATH", tmp_path / "bridge/architecture_governance_report.json")
    monkeypatch.setattr(module, "ARCHITECTURE_CHANGE_GATE_PATH", tmp_path / "bridge/architecture_change_gate.json")
    monkeypatch.setattr(module, "META_COGNITION_AUDIT_PATH", tmp_path / "bridge/meta_cognition_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "SYSTEM_FORECAST_AUDIT_PATH", tmp_path / "bridge/system_forecast_audit.json")
    monkeypatch.setattr(module, "RESPONSIBILITY_AUDIT_PATH", tmp_path / "bridge/responsibility_audit.json")
    monkeypatch.setattr(module, "ARCHITECTURE_REVIEW_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/architecture_review_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "ARCHITECTURE_REVIEW_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/architecture_review_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "architecture_evolution_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "architecture", "architectureFitness": 0.68, "evolutionPressure": 0.44},
                    {"targetId": "target:a", "targetType": "architecture", "architectureFitness": 0.62, "evolutionPressure": 0.48},
                ]
            }
        ),
    )
    _write_json(
        bridge / "architecture_efficiency_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "efficiencyGap": 0.60, "optimizationReadiness": 0.62},
                    {"targetId": "target:a", "efficiencyGap": 0.58, "optimizationReadiness": 0.60},
                ]
            }
        ),
    )
    _write_json(
        bridge / "architecture_governance_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "governanceRisk": 0.44, "constraintConflict": 0.40},
                    {"targetId": "target:a", "governanceRisk": 0.48, "constraintConflict": 0.44},
                ]
            }
        ),
    )
    _write_json(
        bridge / "architecture_change_gate.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "structuralChangeRequest": False, "humanApprovalPresent": False, "autonomousChangeRisk": 0.30},
                    {"targetId": "target:a", "structuralChangeRequest": False, "humanApprovalPresent": False, "autonomousChangeRisk": 0.34},
                ]
            }
        ),
    )

    for name in (
        "meta_cognition_audit.json",
        "value_alignment_audit.json",
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

    audit_schema = json.loads(Path("/workspace/Sophia/schema/architecture_review_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/architecture_review_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_architecture_status_coverage() -> None:
    cases = [
        (
            "watch",
            {"architectureFitness": 0.66, "evolutionPressure": 0.48},
            {"efficiencyGap": 0.56, "optimizationReadiness": 0.58},
            {"governanceRisk": 0.42, "constraintConflict": 0.44},
            {"structuralChangeRequest": False, "humanApprovalPresent": False, "autonomousChangeRisk": 0.34},
            "architecture-watch",
        ),
        (
            "efficiency",
            {"architectureFitness": 0.66, "evolutionPressure": 0.52},
            {"efficiencyGap": 0.70, "optimizationReadiness": 0.64},
            {"governanceRisk": 0.46, "constraintConflict": 0.48},
            {"structuralChangeRequest": False, "humanApprovalPresent": False, "autonomousChangeRisk": 0.34},
            "efficiency-improvement-opportunity",
        ),
        (
            "gov",
            {"architectureFitness": 0.62, "evolutionPressure": 0.54},
            {"efficiencyGap": 0.58, "optimizationReadiness": 0.60},
            {"governanceRisk": 0.74, "constraintConflict": 0.62},
            {"structuralChangeRequest": False, "humanApprovalPresent": False, "autonomousChangeRisk": 0.36},
            "governance-risk",
        ),
        (
            "human",
            {"architectureFitness": 0.70, "evolutionPressure": 0.46},
            {"efficiencyGap": 0.72, "optimizationReadiness": 0.66},
            {"governanceRisk": 0.46, "constraintConflict": 0.48},
            {"structuralChangeRequest": True, "humanApprovalPresent": False, "autonomousChangeRisk": 0.34},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, efficiency, governance, gate, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "architecture", **row},
            efficiency_rows={target_id: efficiency},
            governance_rows={target_id: governance},
            gate_rows={target_id: gate},
            system_risk=0.35,
        )
        statuses.add(decision.architecture_status)
        assert decision.architecture_status == expected

    assert statuses == {
        "architecture-watch",
        "efficiency-improvement-opportunity",
        "governance-risk",
        "require-human-review",
    }


def test_bounded_non_autonomous_change_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "architecture", "architectureFitness": 0.66, "evolutionPressure": 0.50},
        efficiency_rows={"tone": {"efficiencyGap": 0.66, "optimizationReadiness": 0.62}},
        governance_rows={"tone": {"governanceRisk": 0.48, "constraintConflict": 0.46}},
        gate_rows={"tone": {"structuralChangeRequest": False, "humanApprovalPresent": False, "autonomousChangeRisk": 0.34}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.architecture_context,
            decision.efficiency_context,
            decision.governance_context,
            decision.safety_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "human approval" in text
    assert "not autonomous rewrites" in text


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "architecture"}]})
    _write_json(tmp_path / "bridge/architecture_evolution_map.json", bad_map)

    with pytest.raises(module.ArchitectureEvolutionInputError):
        module.build_outputs()
