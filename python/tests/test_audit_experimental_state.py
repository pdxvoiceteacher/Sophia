from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_experimental_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "experimental_design_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.experimental.fixture",
        "producerCommit": "fixture-u-0001",
        "generatedAt": "2026-04-06T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {
        "schema": "audit_fixture_v1",
        "created_at": "2026-04-06T00:00:00Z",
        "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)],
    }


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "EXPERIMENTAL_HYPOTHESIS_MAP_PATH", tmp_path / "bridge/experimental_hypothesis_map.json")
    monkeypatch.setattr(module, "FALSIFICATION_DESIGN_REPORT_PATH", tmp_path / "bridge/falsification_design_report.json")
    monkeypatch.setattr(module, "REPLICATION_PATHWAY_MAP_PATH", tmp_path / "bridge/replication_pathway_map.json")
    monkeypatch.setattr(module, "THEORY_PROMOTION_GATE_PATH", tmp_path / "bridge/theory_promotion_gate.json")
    monkeypatch.setattr(module, "PREDICTION_AUDIT_PATH", tmp_path / "bridge/prediction_audit.json")
    monkeypatch.setattr(module, "BRANCH_LIFECYCLE_AUDIT_PATH", tmp_path / "bridge/branch_lifecycle_audit.json")
    monkeypatch.setattr(module, "EVIDENCE_AUTHORITY_AUDIT_PATH", tmp_path / "bridge/evidence_authority_audit.json")
    monkeypatch.setattr(module, "COLLABORATIVE_REVIEW_AUDIT_PATH", tmp_path / "bridge/collaborative_review_audit.json")
    monkeypatch.setattr(module, "EXPERIMENTAL_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/experimental_audit_v1.schema.json"))
    monkeypatch.setattr(module, "EXPERIMENTAL_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/experimental_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "experimental_hypothesis_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "hypothesis", "hypothesisClarity": 0.75, "predictionCalibration": 0.70},
                    {"targetId": "target:a", "targetType": "hypothesis", "hypothesisClarity": 0.62, "predictionCalibration": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "falsification_design_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "falsificationQuality": 0.70, "falsificationCoverage": 0.68},
                    {"targetId": "target:a", "falsificationQuality": 0.58, "falsificationCoverage": 0.56},
                ]
            }
        ),
    )
    _write_json(
        bridge / "replication_pathway_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "replicationReadiness": 0.72, "replicationIndependence": 0.70},
                    {"targetId": "target:a", "replicationReadiness": 0.60, "replicationIndependence": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "theory_promotion_gate.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "promotionReadiness": 0.72, "blockedPromotion": False, "authorityPressure": 0.32},
                    {"targetId": "target:a", "promotionReadiness": 0.58, "blockedPromotion": False, "authorityPressure": 0.46},
                ]
            }
        ),
    )

    for name in (
        "prediction_audit.json",
        "branch_lifecycle_audit.json",
        "evidence_authority_audit.json",
        "collaborative_review_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/experimental_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/experimental_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_experimental_status_coverage() -> None:
    cases = [
        (
            "watch",
            {"hypothesisClarity": 0.60, "predictionCalibration": 0.58},
            {"falsificationQuality": 0.60, "falsificationCoverage": 0.56},
            {"replicationReadiness": 0.58, "replicationIndependence": 0.56},
            {"promotionReadiness": 0.58, "blockedPromotion": False, "authorityPressure": 0.44},
            "hypothesis-watch",
        ),
        (
            "falsification",
            {"hypothesisClarity": 0.58, "predictionCalibration": 0.56},
            {"falsificationQuality": 0.30, "falsificationCoverage": 0.33},
            {"replicationReadiness": 0.62, "replicationIndependence": 0.60},
            {"promotionReadiness": 0.56, "blockedPromotion": False, "authorityPressure": 0.40},
            "falsification-first",
        ),
        (
            "replication",
            {"hypothesisClarity": 0.66, "predictionCalibration": 0.62},
            {"falsificationQuality": 0.62, "falsificationCoverage": 0.60},
            {"replicationReadiness": 0.40, "replicationIndependence": 0.42},
            {"promotionReadiness": 0.62, "blockedPromotion": False, "authorityPressure": 0.42},
            "replication-required",
        ),
        (
            "candidate",
            {"hypothesisClarity": 0.76, "predictionCalibration": 0.74},
            {"falsificationQuality": 0.72, "falsificationCoverage": 0.70},
            {"replicationReadiness": 0.72, "replicationIndependence": 0.70},
            {"promotionReadiness": 0.74, "blockedPromotion": False, "authorityPressure": 0.30},
            "theory-candidate-review",
        ),
        (
            "human",
            {"hypothesisClarity": 0.58, "predictionCalibration": 0.56},
            {"falsificationQuality": 0.56, "falsificationCoverage": 0.54},
            {"replicationReadiness": 0.56, "replicationIndependence": 0.54},
            {"promotionReadiness": 0.58, "blockedPromotion": True, "authorityPressure": 0.86},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, falsification, replication, gate, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "hypothesis", **row},
            falsification_rows={target_id: falsification},
            replication_rows={target_id: replication},
            gate_rows={target_id: gate},
            system_risk=0.35,
        )
        statuses.add(decision.experimental_status)
        assert decision.experimental_status == expected

    assert statuses == {
        "hypothesis-watch",
        "falsification-first",
        "replication-required",
        "theory-candidate-review",
        "require-human-review",
    }


def test_non_autonomous_bounded_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "hypothesis", "hypothesisClarity": 0.62, "predictionCalibration": 0.58},
        falsification_rows={"tone": {"falsificationQuality": 0.58, "falsificationCoverage": 0.56}},
        replication_rows={"tone": {"replicationReadiness": 0.56, "replicationIndependence": 0.54}},
        gate_rows={"tone": {"promotionReadiness": 0.60, "blockedPromotion": False, "authorityPressure": 0.46}},
        system_risk=0.35,
    )

    text = " ".join([
        decision.calibration_context,
        decision.falsification_context,
        decision.replication_context,
        decision.authority_context,
        decision.explanation,
    ]).lower()
    assert "bounded" in text
    assert "autonomous" in text
    assert "certify" not in text
    assert "truth" not in text


def test_blocked_promotion_handling() -> None:
    decision = module.evaluate_target(
        {"targetId": "blocked", "targetType": "hypothesis", "hypothesisClarity": 0.68, "predictionCalibration": 0.66},
        falsification_rows={"blocked": {"falsificationQuality": 0.68, "falsificationCoverage": 0.66}},
        replication_rows={"blocked": {"replicationReadiness": 0.70, "replicationIndependence": 0.68}},
        gate_rows={"blocked": {"promotionReadiness": 0.72, "blockedPromotion": True, "authorityPressure": 0.72}},
        system_risk=0.34,
    )
    assert decision.experimental_status == "require-human-review"
    assert decision.target_publisher_action == "docket"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "hypothesis"}]})
    _write_json(tmp_path / "bridge/experimental_hypothesis_map.json", bad_map)

    with pytest.raises(module.ExperimentalInputError):
        module.build_outputs()
