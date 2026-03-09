from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_information_value_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "information_value_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.information_value.fixture",
        "producerCommit": "fixture-am-0001",
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
    monkeypatch.setattr(module, "INFORMATION_VALUE_MAP_PATH", tmp_path / "bridge/information_value_map.json")
    monkeypatch.setattr(module, "UNCERTAINTY_PRIORITY_REPORT_PATH", tmp_path / "bridge/uncertainty_priority_report.json")
    monkeypatch.setattr(module, "EVIDENCE_ACQUISITION_GATE_PATH", tmp_path / "bridge/evidence_acquisition_gate.json")
    monkeypatch.setattr(module, "SURVEILLANCE_BOUNDARY_GATE_PATH", tmp_path / "bridge/surveillance_boundary_gate.json")
    monkeypatch.setattr(module, "SYSTEM_FORECAST_AUDIT_PATH", tmp_path / "bridge/system_forecast_audit.json")
    monkeypatch.setattr(module, "THEORY_TRANSFER_AUDIT_PATH", tmp_path / "bridge/theory_transfer_audit.json")
    monkeypatch.setattr(module, "RESPONSIBILITY_AUDIT_PATH", tmp_path / "bridge/responsibility_audit.json")
    monkeypatch.setattr(module, "EXPERIMENTAL_AUDIT_PATH", tmp_path / "bridge/experimental_audit.json")
    monkeypatch.setattr(module, "CURIOSITY_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/curiosity_audit_v1.schema.json"))
    monkeypatch.setattr(module, "CURIOSITY_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/curiosity_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "information_value_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "curiosity", "noveltySignal": 0.64, "expectedInformationGain": 0.62},
                    {"targetId": "target:a", "targetType": "curiosity", "noveltySignal": 0.58, "expectedInformationGain": 0.56},
                ]
            }
        ),
    )
    _write_json(
        bridge / "uncertainty_priority_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "uncertaintySeverity": 0.44, "verificationUrgency": 0.56},
                    {"targetId": "target:a", "uncertaintySeverity": 0.50, "verificationUrgency": 0.60},
                ]
            }
        ),
    )
    _write_json(
        bridge / "evidence_acquisition_gate.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "evidenceReadiness": 0.62, "experimentFeasibility": 0.66},
                    {"targetId": "target:a", "evidenceReadiness": 0.58, "experimentFeasibility": 0.60},
                ]
            }
        ),
    )
    _write_json(
        bridge / "surveillance_boundary_gate.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "surveillanceExpansionRisk": 0.30, "intrusionRisk": 0.32, "surveillanceRequested": False},
                    {"targetId": "target:a", "surveillanceExpansionRisk": 0.34, "intrusionRisk": 0.36, "surveillanceRequested": False},
                ]
            }
        ),
    )

    for name in (
        "system_forecast_audit.json",
        "theory_transfer_audit.json",
        "responsibility_audit.json",
        "experimental_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/curiosity_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/curiosity_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_curiosity_status_coverage() -> None:
    cases = [
        (
            "watch",
            {"noveltySignal": 0.56, "expectedInformationGain": 0.54},
            {"uncertaintySeverity": 0.46, "verificationUrgency": 0.58},
            {"evidenceReadiness": 0.54, "experimentFeasibility": 0.56},
            {"surveillanceExpansionRisk": 0.30, "intrusionRisk": 0.34, "surveillanceRequested": False},
            "observation-watch",
        ),
        (
            "verify",
            {"noveltySignal": 0.60, "expectedInformationGain": 0.58},
            {"uncertaintySeverity": 0.56, "verificationUrgency": 0.70},
            {"evidenceReadiness": 0.56, "experimentFeasibility": 0.58},
            {"surveillanceExpansionRisk": 0.30, "intrusionRisk": 0.34, "surveillanceRequested": False},
            "verification-priority",
        ),
        (
            "experiment",
            {"noveltySignal": 0.68, "expectedInformationGain": 0.66},
            {"uncertaintySeverity": 0.52, "verificationUrgency": 0.60},
            {"evidenceReadiness": 0.66, "experimentFeasibility": 0.70},
            {"surveillanceExpansionRisk": 0.30, "intrusionRisk": 0.34, "surveillanceRequested": False},
            "experiment-candidate",
        ),
        (
            "critical",
            {"noveltySignal": 0.64, "expectedInformationGain": 0.62},
            {"uncertaintySeverity": 0.82, "verificationUrgency": 0.72},
            {"evidenceReadiness": 0.62, "experimentFeasibility": 0.64},
            {"surveillanceExpansionRisk": 0.30, "intrusionRisk": 0.34, "surveillanceRequested": False},
            "uncertainty-critical",
        ),
        (
            "human",
            {"noveltySignal": 0.70, "expectedInformationGain": 0.68},
            {"uncertaintySeverity": 0.50, "verificationUrgency": 0.58},
            {"evidenceReadiness": 0.64, "experimentFeasibility": 0.68},
            {"surveillanceExpansionRisk": 0.84, "intrusionRisk": 0.32, "surveillanceRequested": False},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, uncertainty, evidence, boundary, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "curiosity", **row},
            uncertainty_rows={target_id: uncertainty},
            evidence_rows={target_id: evidence},
            boundary_rows={target_id: boundary},
            system_risk=0.35,
        )
        statuses.add(decision.curiosity_status)
        assert decision.curiosity_status == expected

    assert statuses == {
        "observation-watch",
        "verification-priority",
        "experiment-candidate",
        "uncertainty-critical",
        "require-human-review",
    }


def test_bounded_non_intrusive_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "curiosity", "noveltySignal": 0.62, "expectedInformationGain": 0.60},
        uncertainty_rows={"tone": {"uncertaintySeverity": 0.56, "verificationUrgency": 0.62}},
        evidence_rows={"tone": {"evidenceReadiness": 0.58, "experimentFeasibility": 0.62}},
        boundary_rows={"tone": {"surveillanceExpansionRisk": 0.34, "intrusionRisk": 0.36, "surveillanceRequested": False}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.uncertainty_context,
            decision.evidence_context,
            decision.experiment_context,
            decision.governance_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "never justify surveillance expansion" in text
    assert "intrusion" in text
    assert "spy" not in text
    assert "punish" not in text


def test_surveillance_expansion_safeguard() -> None:
    decision = module.evaluate_target(
        {"targetId": "gate", "targetType": "curiosity", "noveltySignal": 0.72, "expectedInformationGain": 0.70},
        uncertainty_rows={"gate": {"uncertaintySeverity": 0.50, "verificationUrgency": 0.60}},
        evidence_rows={"gate": {"evidenceReadiness": 0.68, "experimentFeasibility": 0.70}},
        boundary_rows={"gate": {"surveillanceExpansionRisk": 0.42, "intrusionRisk": 0.40, "surveillanceRequested": True}},
        system_risk=0.35,
    )

    assert decision.curiosity_status == "require-human-review"
    assert decision.target_publisher_action == "docket"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "curiosity"}]})
    _write_json(tmp_path / "bridge/information_value_map.json", bad_map)

    with pytest.raises(module.InformationValueInputError):
        module.build_outputs()
