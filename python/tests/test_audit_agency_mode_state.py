from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_agency_mode_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "agency_mode_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.agency_mode.fixture",
        "producerCommit": "fixture-u-0001",
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
    monkeypatch.setattr(module, "AGENCY_MODE_HYPOTHESIS_MAP_PATH", tmp_path / "bridge/agency_mode_hypothesis_map.json")
    monkeypatch.setattr(module, "AGENCY_FIT_COMPARISON_REPORT_PATH", tmp_path / "bridge/agency_fit_comparison_report.json")
    monkeypatch.setattr(module, "TEL_BRANCH_SIGNATURE_MAP_PATH", tmp_path / "bridge/tel_branch_signature_map.json")
    monkeypatch.setattr(module, "AGENCY_GOVERNANCE_MODE_GATE_PATH", tmp_path / "bridge/agency_governance_mode_gate.json")
    monkeypatch.setattr(module, "PREDICTION_AUDIT_PATH", tmp_path / "bridge/prediction_audit.json")
    monkeypatch.setattr(module, "EXPERIMENTAL_AUDIT_PATH", tmp_path / "bridge/experimental_audit.json")
    monkeypatch.setattr(module, "THEORY_CORPUS_AUDIT_PATH", tmp_path / "bridge/theory_corpus_audit.json")
    monkeypatch.setattr(module, "COLLABORATIVE_REVIEW_AUDIT_PATH", tmp_path / "bridge/collaborative_review_audit.json")
    monkeypatch.setattr(module, "AGENCY_MODE_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/agency_mode_audit_v1.schema.json"))
    monkeypatch.setattr(module, "AGENCY_MODE_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/agency_mode_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "agency_mode_hypothesis_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "context", "deterministicFit": 0.66, "volitionalFit": 0.52},
                    {"targetId": "target:a", "targetType": "context", "deterministicFit": 0.54, "volitionalFit": 0.60},
                ]
            }
        ),
    )
    _write_json(
        bridge / "agency_fit_comparison_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "fitConfidence": 0.66, "fairnessScore": 0.64},
                    {"targetId": "target:a", "fitConfidence": 0.60, "fairnessScore": 0.62},
                ]
            }
        ),
    )
    _write_json(
        bridge / "tel_branch_signature_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "branchEntropy": 0.44, "calibrationScore": 0.62},
                    {"targetId": "target:a", "branchEntropy": 0.48, "calibrationScore": 0.60},
                ]
            }
        ),
    )
    _write_json(
        bridge / "agency_governance_mode_gate.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "deterministicOverreach": 0.36, "punitiveVolitional": 0.30, "governanceReadiness": 0.64},
                    {"targetId": "target:a", "deterministicOverreach": 0.34, "punitiveVolitional": 0.36, "governanceReadiness": 0.62},
                ]
            }
        ),
    )

    for name in (
        "prediction_audit.json",
        "experimental_audit.json",
        "theory_corpus_audit.json",
        "collaborative_review_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/agency_mode_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/agency_mode_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_agency_status_coverage() -> None:
    cases = [
        (
            "det",
            {"deterministicFit": 0.72, "volitionalFit": 0.48},
            {"fitConfidence": 0.66, "fairnessScore": 0.64},
            {"branchEntropy": 0.44, "calibrationScore": 0.62},
            {"deterministicOverreach": 0.34, "punitiveVolitional": 0.30, "governanceReadiness": 0.62},
            "deterministic-lean",
        ),
        (
            "vol",
            {"deterministicFit": 0.46, "volitionalFit": 0.72},
            {"fitConfidence": 0.66, "fairnessScore": 0.64},
            {"branchEntropy": 0.44, "calibrationScore": 0.62},
            {"deterministicOverreach": 0.30, "punitiveVolitional": 0.34, "governanceReadiness": 0.62},
            "volitional-lean",
        ),
        (
            "mix",
            {"deterministicFit": 0.58, "volitionalFit": 0.54},
            {"fitConfidence": 0.62, "fairnessScore": 0.62},
            {"branchEntropy": 0.48, "calibrationScore": 0.60},
            {"deterministicOverreach": 0.34, "punitiveVolitional": 0.34, "governanceReadiness": 0.58},
            "mixed",
        ),
        (
            "under",
            {"deterministicFit": 0.58, "volitionalFit": 0.56},
            {"fitConfidence": 0.30, "fairnessScore": 0.56},
            {"branchEntropy": 0.52, "calibrationScore": 0.56},
            {"deterministicOverreach": 0.42, "punitiveVolitional": 0.44, "governanceReadiness": 0.32},
            "underdetermined",
        ),
        (
            "human",
            {"deterministicFit": 0.64, "volitionalFit": 0.52},
            {"fitConfidence": 0.62, "fairnessScore": 0.52},
            {"branchEntropy": 0.52, "calibrationScore": 0.56},
            {"deterministicOverreach": 0.84, "punitiveVolitional": 0.42, "governanceReadiness": 0.50},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, fit, sig, gate, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "context", **row},
            fit_rows={target_id: fit},
            signature_rows={target_id: sig},
            gate_rows={target_id: gate},
            system_risk=0.35,
        )
        statuses.add(decision.agency_status)
        assert decision.agency_status == expected

    assert statuses == {
        "deterministic-lean",
        "volitional-lean",
        "mixed",
        "underdetermined",
        "require-human-review",
    }


def test_bounded_non_metaphysical_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "context", "deterministicFit": 0.62, "volitionalFit": 0.52},
        fit_rows={"tone": {"fitConfidence": 0.60, "fairnessScore": 0.62}},
        signature_rows={"tone": {"branchEntropy": 0.50, "calibrationScore": 0.58}},
        gate_rows={"tone": {"deterministicOverreach": 0.38, "punitiveVolitional": 0.36, "governanceReadiness": 0.60}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.fit_context,
            decision.entropy_context,
            decision.calibration_context,
            decision.fairness_context,
            decision.governance_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "metaphysical" not in text
    assert "truth" not in text


def test_deterministic_overreach_and_punitive_volitional_handling() -> None:
    det = module.evaluate_target(
        {"targetId": "det", "targetType": "context", "deterministicFit": 0.70, "volitionalFit": 0.48},
        fit_rows={"det": {"fitConfidence": 0.62, "fairnessScore": 0.52}},
        signature_rows={"det": {"branchEntropy": 0.52, "calibrationScore": 0.58}},
        gate_rows={"det": {"deterministicOverreach": 0.84, "punitiveVolitional": 0.40, "governanceReadiness": 0.56}},
        system_risk=0.35,
    )
    vol = module.evaluate_target(
        {"targetId": "vol", "targetType": "context", "deterministicFit": 0.46, "volitionalFit": 0.72},
        fit_rows={"vol": {"fitConfidence": 0.62, "fairnessScore": 0.52}},
        signature_rows={"vol": {"branchEntropy": 0.52, "calibrationScore": 0.58}},
        gate_rows={"vol": {"deterministicOverreach": 0.40, "punitiveVolitional": 0.84, "governanceReadiness": 0.56}},
        system_risk=0.35,
    )
    assert det.agency_status == "require-human-review"
    assert vol.agency_status == "require-human-review"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "context"}]})
    _write_json(tmp_path / "bridge/agency_mode_hypothesis_map.json", bad_map)

    with pytest.raises(module.AgencyModeInputError):
        module.build_outputs()
