from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_system_forecast_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "system_forecast_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.system_forecast.fixture",
        "producerCommit": "fixture-al-0001",
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
    monkeypatch.setattr(module, "SYSTEM_FORECAST_MAP_PATH", tmp_path / "bridge/system_forecast_map.json")
    monkeypatch.setattr(module, "TRAJECTORY_TRANSITION_REPORT_PATH", tmp_path / "bridge/trajectory_transition_report.json")
    monkeypatch.setattr(module, "ENTROPY_WARNING_REPORT_PATH", tmp_path / "bridge/entropy_warning_report.json")
    monkeypatch.setattr(module, "FORECAST_INTERVENTION_GATE_PATH", tmp_path / "bridge/forecast_intervention_gate.json")
    monkeypatch.setattr(module, "EXPERIMENTAL_AUDIT_PATH", tmp_path / "bridge/experimental_audit.json")
    monkeypatch.setattr(module, "THEORY_CORPUS_AUDIT_PATH", tmp_path / "bridge/theory_corpus_audit.json")
    monkeypatch.setattr(module, "AGENCY_MODE_AUDIT_PATH", tmp_path / "bridge/agency_mode_audit.json")
    monkeypatch.setattr(module, "RESPONSIBILITY_AUDIT_PATH", tmp_path / "bridge/responsibility_audit.json")
    monkeypatch.setattr(module, "SYSTEM_FORECAST_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/system_forecast_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "SYSTEM_FORECAST_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/system_forecast_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "system_forecast_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "system", "trajectoryConfidence": 0.66, "horizonStability": 0.62},
                    {"targetId": "target:a", "targetType": "system", "trajectoryConfidence": 0.58, "horizonStability": 0.54},
                ]
            }
        ),
    )
    _write_json(
        bridge / "trajectory_transition_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "transitionInstability": 0.46, "regimeShiftRisk": 0.44},
                    {"targetId": "target:a", "transitionInstability": 0.50, "regimeShiftRisk": 0.48},
                ]
            }
        ),
    )
    _write_json(
        bridge / "entropy_warning_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "entropyPressure": 0.44, "collapseSignal": 0.42},
                    {"targetId": "target:a", "entropyPressure": 0.46, "collapseSignal": 0.44},
                ]
            }
        ),
    )
    _write_json(
        bridge / "forecast_intervention_gate.json",
        _artifact(
            {
                "targets": [
                    {
                        "targetId": "target:z",
                        "preemptiveCoercionRisk": 0.28,
                        "accusatoryDriftRisk": 0.30,
                        "interventionRequested": False,
                    },
                    {
                        "targetId": "target:a",
                        "preemptiveCoercionRisk": 0.32,
                        "accusatoryDriftRisk": 0.34,
                        "interventionRequested": False,
                    },
                ]
            }
        ),
    )

    for name in (
        "experimental_audit.json",
        "theory_corpus_audit.json",
        "agency_mode_audit.json",
        "responsibility_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/system_forecast_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/system_forecast_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_forecast_status_coverage() -> None:
    cases = [
        (
            "watch",
            {"trajectoryConfidence": 0.70, "horizonStability": 0.64},
            {"transitionInstability": 0.42, "regimeShiftRisk": 0.40},
            {"entropyPressure": 0.42, "collapseSignal": 0.40},
            {"preemptiveCoercionRisk": 0.30, "accusatoryDriftRisk": 0.32, "interventionRequested": False},
            "trajectory-watch",
        ),
        (
            "prov",
            {"trajectoryConfidence": 0.56, "horizonStability": 0.54},
            {"transitionInstability": 0.46, "regimeShiftRisk": 0.44},
            {"entropyPressure": 0.44, "collapseSignal": 0.42},
            {"preemptiveCoercionRisk": 0.30, "accusatoryDriftRisk": 0.32, "interventionRequested": False},
            "trajectory-provisional",
        ),
        (
            "transition",
            {"trajectoryConfidence": 0.60, "horizonStability": 0.56},
            {"transitionInstability": 0.72, "regimeShiftRisk": 0.66},
            {"entropyPressure": 0.48, "collapseSignal": 0.46},
            {"preemptiveCoercionRisk": 0.30, "accusatoryDriftRisk": 0.32, "interventionRequested": False},
            "transition-risk",
        ),
        (
            "entropy",
            {"trajectoryConfidence": 0.60, "horizonStability": 0.56},
            {"transitionInstability": 0.54, "regimeShiftRisk": 0.52},
            {"entropyPressure": 0.76, "collapseSignal": 0.68},
            {"preemptiveCoercionRisk": 0.30, "accusatoryDriftRisk": 0.32, "interventionRequested": False},
            "entropy-warning",
        ),
        (
            "human",
            {"trajectoryConfidence": 0.66, "horizonStability": 0.62},
            {"transitionInstability": 0.44, "regimeShiftRisk": 0.42},
            {"entropyPressure": 0.44, "collapseSignal": 0.42},
            {"preemptiveCoercionRisk": 0.82, "accusatoryDriftRisk": 0.30, "interventionRequested": False},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, transition, entropy, gate, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "system", **row},
            transition_rows={target_id: transition},
            entropy_rows={target_id: entropy},
            gate_rows={target_id: gate},
            system_risk=0.35,
        )
        statuses.add(decision.forecast_status)
        assert decision.forecast_status == expected

    assert statuses == {
        "trajectory-watch",
        "trajectory-provisional",
        "transition-risk",
        "entropy-warning",
        "require-human-review",
    }


def test_bounded_non_coercive_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "system", "trajectoryConfidence": 0.64, "horizonStability": 0.58},
        transition_rows={"tone": {"transitionInstability": 0.48, "regimeShiftRisk": 0.46}},
        entropy_rows={"tone": {"entropyPressure": 0.50, "collapseSignal": 0.48}},
        gate_rows={"tone": {"preemptiveCoercionRisk": 0.30, "accusatoryDriftRisk": 0.34, "interventionRequested": False}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.trajectory_context,
            decision.transition_context,
            decision.entropy_context,
            decision.governance_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "never justify pre-emptive coercion" in text
    assert "guilt" not in text
    assert "punish" not in text


def test_preemptive_coercion_safeguard() -> None:
    decision = module.evaluate_target(
        {"targetId": "gate", "targetType": "system", "trajectoryConfidence": 0.72, "horizonStability": 0.68},
        transition_rows={"gate": {"transitionInstability": 0.42, "regimeShiftRisk": 0.40}},
        entropy_rows={"gate": {"entropyPressure": 0.42, "collapseSignal": 0.40}},
        gate_rows={"gate": {"preemptiveCoercionRisk": 0.40, "accusatoryDriftRisk": 0.36, "interventionRequested": True}},
        system_risk=0.35,
    )

    assert decision.forecast_status == "require-human-review"
    assert decision.target_publisher_action == "docket"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "system"}]})
    _write_json(tmp_path / "bridge/system_forecast_map.json", bad_map)

    with pytest.raises(module.SystemForecastInputError):
        module.build_outputs()
