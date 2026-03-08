from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_collaborative_review_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "collaborative_review_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.collaborative_review.fixture",
        "producerCommit": "fixture-u-0001",
        "generatedAt": "2026-04-04T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {
        "schema": "audit_fixture_v1",
        "created_at": "2026-04-04T00:00:00Z",
        "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)],
    }


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "REVIEWER_DELIBERATION_MAP_PATH", tmp_path / "bridge/reviewer_deliberation_map.json")
    monkeypatch.setattr(module, "REVIEWER_POSITION_MAP_PATH", tmp_path / "bridge/reviewer_position_map.json")
    monkeypatch.setattr(module, "CONSENSUS_STATE_REPORT_PATH", tmp_path / "bridge/consensus_state_report.json")
    monkeypatch.setattr(module, "DISSENT_TRACE_REPORT_PATH", tmp_path / "bridge/dissent_trace_report.json")
    monkeypatch.setattr(module, "REVIEW_PACKET_AUDIT_PATH", tmp_path / "bridge/review_packet_audit.json")
    monkeypatch.setattr(module, "CAUSAL_AUDIT_PATH", tmp_path / "bridge/causal_audit.json")
    monkeypatch.setattr(module, "EVIDENCE_AUTHORITY_AUDIT_PATH", tmp_path / "bridge/evidence_authority_audit.json")
    monkeypatch.setattr(module, "CLOSURE_AUDIT_PATH", tmp_path / "bridge/closure_audit.json")
    monkeypatch.setattr(module, "COLLABORATIVE_REVIEW_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/collaborative_review_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "COLLABORATIVE_REVIEW_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/collaborative_review_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "reviewer_deliberation_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "review", "deliberationDepth": 0.70, "reviewMaturity": 0.68},
                    {"targetId": "target:a", "targetType": "review", "deliberationDepth": 0.60, "reviewMaturity": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "reviewer_position_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "positionAlignment": 0.70, "minorityCaution": 0.40},
                    {"targetId": "target:a", "positionAlignment": 0.62, "minorityCaution": 0.48},
                ]
            }
        ),
    )
    _write_json(
        bridge / "consensus_state_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "consensusScore": 0.72, "consensusStability": 0.70},
                    {"targetId": "target:a", "consensusScore": 0.62, "consensusStability": 0.60},
                ]
            }
        ),
    )
    _write_json(
        bridge / "dissent_trace_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "dissentScore": 0.32, "unresolvedDissent": 0},
                    {"targetId": "target:a", "dissentScore": 0.44, "unresolvedDissent": 1},
                ]
            }
        ),
    )

    for name in ("review_packet_audit.json", "causal_audit.json", "evidence_authority_audit.json", "closure_audit.json"):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/collaborative_review_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/collaborative_review_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_collaborative_status_coverage() -> None:
    cases = [
        (
            "bounded",
            {"deliberationDepth": 0.78, "reviewMaturity": 0.78},
            {"positionAlignment": 0.76, "minorityCaution": 0.30},
            {"consensusScore": 0.74, "consensusStability": 0.72},
            {"dissentScore": 0.32, "unresolvedDissent": 0},
            "consensus-bounded",
        ),
        (
            "dissent",
            {"deliberationDepth": 0.66, "reviewMaturity": 0.60},
            {"positionAlignment": 0.64, "minorityCaution": 0.64},
            {"consensusScore": 0.58, "consensusStability": 0.56},
            {"dissentScore": 0.56, "unresolvedDissent": 1},
            "dissent-active",
        ),
        (
            "verify",
            {"deliberationDepth": 0.58, "reviewMaturity": 0.30},
            {"positionAlignment": 0.62, "minorityCaution": 0.50},
            {"consensusScore": 0.56, "consensusStability": 0.42},
            {"dissentScore": 0.45, "unresolvedDissent": 1},
            "verify-first",
        ),
        (
            "blocked",
            {"deliberationDepth": 0.56, "reviewMaturity": 0.58},
            {"positionAlignment": 0.44, "minorityCaution": 0.62},
            {"consensusScore": 0.42, "consensusStability": 0.52},
            {"dissentScore": 0.72, "unresolvedDissent": 3},
            "blocked",
        ),
        (
            "human",
            {"deliberationDepth": 0.62, "reviewMaturity": 0.58},
            {"positionAlignment": 0.52, "minorityCaution": 0.66},
            {"consensusScore": 0.46, "consensusStability": 0.48},
            {"dissentScore": 0.86, "unresolvedDissent": 3},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, position, consensus, dissent, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "review", **row},
            position_rows={target_id: position},
            consensus_rows={target_id: consensus},
            dissent_rows={target_id: dissent},
            system_risk=0.35,
        )
        statuses.add(decision.collaborative_status)
        assert decision.collaborative_status == expected

    assert statuses == {"consensus-bounded", "dissent-active", "verify-first", "blocked", "require-human-review"}


def test_non_accusatory_bounded_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "review", "deliberationDepth": 0.62, "reviewMaturity": 0.56},
        position_rows={"tone": {"positionAlignment": 0.58, "minorityCaution": 0.52}},
        consensus_rows={"tone": {"consensusScore": 0.55, "consensusStability": 0.54}},
        dissent_rows={"tone": {"dissentScore": 0.50, "unresolvedDissent": 1}},
        system_risk=0.35,
    )

    text = " ".join([
        decision.consensus_context,
        decision.dissent_context,
        decision.maturity_context,
        decision.explanation,
    ]).lower()
    assert "bounded" in text
    assert "accuse" not in text
    assert "guilty" not in text
    assert "allegation" not in text


def test_dissent_preservation() -> None:
    decision = module.evaluate_target(
        {"targetId": "dissent", "targetType": "review", "deliberationDepth": 0.64, "reviewMaturity": 0.60},
        position_rows={"dissent": {"positionAlignment": 0.60, "minorityCaution": 0.64}},
        consensus_rows={"dissent": {"consensusScore": 0.56, "consensusStability": 0.52}},
        dissent_rows={"dissent": {"dissentScore": 0.58, "unresolvedDissent": 2}},
        system_risk=0.34,
    )
    assert decision.collaborative_status == "dissent-active"
    assert "not erased" in decision.dissent_context


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact(
        {
            "producerCommit": "",
            "targets": [{"targetId": "target:a", "targetType": "review", "deliberationDepth": 0.60, "reviewMaturity": 0.58}],
        }
    )
    _write_json(tmp_path / "bridge/reviewer_deliberation_map.json", bad_map)

    with pytest.raises(module.CollaborativeReviewInputError):
        module.build_outputs()
