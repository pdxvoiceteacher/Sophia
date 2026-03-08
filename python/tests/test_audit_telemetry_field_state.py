from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_telemetry_field_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "telemetry_field_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.telemetry.fixture",
        "producerCommit": "fixture-u-0001",
        "generatedAt": "2026-04-05T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {
        "schema": "audit_fixture_v1",
        "created_at": "2026-04-05T00:00:00Z",
        "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)],
    }


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "TELEMETRY_FIELD_MAP_PATH", tmp_path / "bridge/telemetry_field_map.json")
    monkeypatch.setattr(module, "LATTICE_PROJECTION_MAP_PATH", tmp_path / "bridge/lattice_projection_map.json")
    monkeypatch.setattr(module, "PATTERN_DONATION_REGISTRY_PATH", tmp_path / "bridge/pattern_donation_registry.json")
    monkeypatch.setattr(module, "ACTION_FUNCTIONAL_SCORECARD_PATH", tmp_path / "bridge/action_functional_scorecard.json")
    monkeypatch.setattr(module, "BRANCH_EMERGENCE_REPORT_PATH", tmp_path / "bridge/branch_emergence_report.json")
    monkeypatch.setattr(module, "EVIDENCE_AUTHORITY_AUDIT_PATH", tmp_path / "bridge/evidence_authority_audit.json")
    monkeypatch.setattr(module, "COLLABORATIVE_REVIEW_AUDIT_PATH", tmp_path / "bridge/collaborative_review_audit.json")
    monkeypatch.setattr(module, "VERIFICATION_AUDIT_PATH", tmp_path / "bridge/verification_audit.json")
    monkeypatch.setattr(module, "CAUSAL_AUDIT_PATH", tmp_path / "bridge/causal_audit.json")
    monkeypatch.setattr(module, "TELEMETRY_FIELD_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/telemetry_field_audit_v1.schema.json"))
    monkeypatch.setattr(module, "TELEMETRY_FIELD_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/telemetry_field_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "telemetry_field_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "field", "telemetryCoherence": 0.78, "maturityScore": 0.74},
                    {"targetId": "target:a", "targetType": "field", "telemetryCoherence": 0.62, "maturityScore": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "lattice_projection_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "projectionStability": 0.74, "latticeDivergence": 0.26},
                    {"targetId": "target:a", "projectionStability": 0.60, "latticeDivergence": 0.38},
                ]
            }
        ),
    )
    _write_json(
        bridge / "pattern_donation_registry.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "donationConfidence": 0.72, "donationNovelty": 0.32},
                    {"targetId": "target:a", "donationConfidence": 0.58, "donationNovelty": 0.42},
                ]
            }
        ),
    )
    _write_json(
        bridge / "action_functional_scorecard.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "functionalScore": 0.76, "overreachScore": 0.24},
                    {"targetId": "target:a", "functionalScore": 0.60, "overreachScore": 0.38},
                ]
            }
        ),
    )
    _write_json(
        bridge / "branch_emergence_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "emergenceScore": 0.48, "branchReadiness": 0.52},
                    {"targetId": "target:a", "emergenceScore": 0.62, "branchReadiness": 0.55},
                ]
            }
        ),
    )

    for name in (
        "evidence_authority_audit.json",
        "collaborative_review_audit.json",
        "verification_audit.json",
        "causal_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/telemetry_field_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/telemetry_field_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_field_status_coverage() -> None:
    cases = [
        (
            "bounded",
            {"telemetryCoherence": 0.78, "maturityScore": 0.74},
            {"projectionStability": 0.72, "latticeDivergence": 0.26},
            {"donationConfidence": 0.70, "donationNovelty": 0.34},
            {"functionalScore": 0.76, "overreachScore": 0.20},
            {"emergenceScore": 0.45, "branchReadiness": 0.54},
            "bounded-field",
        ),
        (
            "verify",
            {"telemetryCoherence": 0.58, "maturityScore": 0.30},
            {"projectionStability": 0.56, "latticeDivergence": 0.38},
            {"donationConfidence": 0.54, "donationNovelty": 0.45},
            {"functionalScore": 0.52, "overreachScore": 0.40},
            {"emergenceScore": 0.58, "branchReadiness": 0.46},
            "verify-first",
        ),
        (
            "provisional",
            {"telemetryCoherence": 0.66, "maturityScore": 0.58},
            {"projectionStability": 0.62, "latticeDivergence": 0.34},
            {"donationConfidence": 0.60, "donationNovelty": 0.44},
            {"functionalScore": 0.64, "overreachScore": 0.42},
            {"emergenceScore": 0.66, "branchReadiness": 0.58},
            "provisional-branch",
        ),
        (
            "overreach",
            {"telemetryCoherence": 0.60, "maturityScore": 0.56},
            {"projectionStability": 0.52, "latticeDivergence": 0.62},
            {"donationConfidence": 0.56, "donationNovelty": 0.70},
            {"functionalScore": 0.60, "overreachScore": 0.70},
            {"emergenceScore": 0.68, "branchReadiness": 0.52},
            "overreach-risk",
        ),
        (
            "human",
            {"telemetryCoherence": 0.55, "maturityScore": 0.36},
            {"projectionStability": 0.50, "latticeDivergence": 0.58},
            {"donationConfidence": 0.54, "donationNovelty": 0.72},
            {"functionalScore": 0.50, "overreachScore": 0.86},
            {"emergenceScore": 0.80, "branchReadiness": 0.40},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, lattice, donation, taf, branch, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "field", **row},
            lattice_rows={target_id: lattice},
            donation_rows={target_id: donation},
            taf_rows={target_id: taf},
            branch_rows={target_id: branch},
            system_risk=0.35,
        )
        statuses.add(decision.field_status)
        assert decision.field_status == expected

    assert statuses == {"bounded-field", "verify-first", "provisional-branch", "overreach-risk", "require-human-review"}


def test_non_autonomous_bounded_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "field", "telemetryCoherence": 0.64, "maturityScore": 0.58},
        lattice_rows={"tone": {"projectionStability": 0.60, "latticeDivergence": 0.36}},
        donation_rows={"tone": {"donationConfidence": 0.58, "donationNovelty": 0.44}},
        taf_rows={"tone": {"functionalScore": 0.62, "overreachScore": 0.40}},
        branch_rows={"tone": {"emergenceScore": 0.58, "branchReadiness": 0.50}},
        system_risk=0.35,
    )

    text = " ".join([
        decision.lattice_context,
        decision.donation_context,
        decision.action_functional_context,
        decision.maturity_context,
        decision.explanation,
    ]).lower()
    assert "bounded" in text
    assert "autonom" in text
    assert "authorize" in text
    assert "guilty" not in text


def test_overreach_risk_handling() -> None:
    decision = module.evaluate_target(
        {"targetId": "overreach", "targetType": "field", "telemetryCoherence": 0.62, "maturityScore": 0.56},
        lattice_rows={"overreach": {"projectionStability": 0.54, "latticeDivergence": 0.60}},
        donation_rows={"overreach": {"donationConfidence": 0.56, "donationNovelty": 0.66}},
        taf_rows={"overreach": {"functionalScore": 0.62, "overreachScore": 0.68}},
        branch_rows={"overreach": {"emergenceScore": 0.70, "branchReadiness": 0.52}},
        system_risk=0.35,
    )
    assert decision.field_status == "overreach-risk"
    assert decision.target_publisher_action == "suppress"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "field"}]})
    _write_json(tmp_path / "bridge/telemetry_field_map.json", bad_map)

    with pytest.raises(module.TelemetryFieldInputError):
        module.build_outputs()
