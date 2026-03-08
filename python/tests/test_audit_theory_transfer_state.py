from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_theory_transfer_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "theory_transfer_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.theory_transfer.fixture",
        "producerCommit": "fixture-ak-0001",
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
    monkeypatch.setattr(module, "THEORY_TRANSFER_MAP_PATH", tmp_path / "bridge/theory_transfer_map.json")
    monkeypatch.setattr(module, "DONOR_TARGET_ASYMMETRY_REPORT_PATH", tmp_path / "bridge/donor_target_asymmetry_report.json")
    monkeypatch.setattr(module, "TRANSFER_REPLICATION_GATE_PATH", tmp_path / "bridge/transfer_replication_gate.json")
    monkeypatch.setattr(module, "TRANSFER_RISK_REGISTER_PATH", tmp_path / "bridge/transfer_risk_register.json")
    monkeypatch.setattr(module, "EXPERIMENTAL_AUDIT_PATH", tmp_path / "bridge/experimental_audit.json")
    monkeypatch.setattr(module, "THEORY_CORPUS_AUDIT_PATH", tmp_path / "bridge/theory_corpus_audit.json")
    monkeypatch.setattr(module, "AGENCY_MODE_AUDIT_PATH", tmp_path / "bridge/agency_mode_audit.json")
    monkeypatch.setattr(module, "RESPONSIBILITY_AUDIT_PATH", tmp_path / "bridge/responsibility_audit.json")
    monkeypatch.setattr(module, "THEORY_TRANSFER_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/theory_transfer_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "THEORY_TRANSFER_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/theory_transfer_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "theory_transfer_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "transfer", "analogyStrength": 0.56, "transferReadiness": 0.68},
                    {"targetId": "target:a", "targetType": "transfer", "analogyStrength": 0.52, "transferReadiness": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "donor_target_asymmetry_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "asymmetryScore": 0.40, "domainDistance": 0.42},
                    {"targetId": "target:a", "asymmetryScore": 0.48, "domainDistance": 0.46},
                ]
            }
        ),
    )
    _write_json(
        bridge / "transfer_replication_gate.json",
        _artifact(
            {
                "targets": [
                    {
                        "targetId": "target:z",
                        "donorReplicationMaturity": 0.72,
                        "targetReplicationMaturity": 0.70,
                        "replicationRequired": False,
                    },
                    {
                        "targetId": "target:a",
                        "donorReplicationMaturity": 0.66,
                        "targetReplicationMaturity": 0.62,
                        "replicationRequired": True,
                    },
                ]
            }
        ),
    )
    _write_json(
        bridge / "transfer_risk_register.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "transferHarmRisk": 0.36, "deterministicOverreach": 0.30},
                    {"targetId": "target:a", "transferHarmRisk": 0.40, "deterministicOverreach": 0.34},
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

    audit_schema = json.loads(Path("/workspace/Sophia/schema/theory_transfer_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/theory_transfer_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_transfer_status_coverage() -> None:
    cases = [
        (
            "analogy",
            {"analogyStrength": 0.54, "transferReadiness": 0.58},
            {"asymmetryScore": 0.50, "domainDistance": 0.52},
            {"donorReplicationMaturity": 0.64, "targetReplicationMaturity": 0.62, "replicationRequired": False},
            {"transferHarmRisk": 0.44, "deterministicOverreach": 0.34},
            "analogy-only",
        ),
        (
            "bounded",
            {"analogyStrength": 0.66, "transferReadiness": 0.72},
            {"asymmetryScore": 0.36, "domainDistance": 0.40},
            {"donorReplicationMaturity": 0.74, "targetReplicationMaturity": 0.70, "replicationRequired": False},
            {"transferHarmRisk": 0.34, "deterministicOverreach": 0.28},
            "bounded-transfer",
        ),
        (
            "replication",
            {"analogyStrength": 0.66, "transferReadiness": 0.70},
            {"asymmetryScore": 0.42, "domainDistance": 0.44},
            {"donorReplicationMaturity": 0.74, "targetReplicationMaturity": 0.52, "replicationRequired": True},
            {"transferHarmRisk": 0.34, "deterministicOverreach": 0.28},
            "replication-required",
        ),
        (
            "blocked",
            {"analogyStrength": 0.70, "transferReadiness": 0.72},
            {"asymmetryScore": 0.86, "domainDistance": 0.70},
            {"donorReplicationMaturity": 0.78, "targetReplicationMaturity": 0.72, "replicationRequired": False},
            {"transferHarmRisk": 0.34, "deterministicOverreach": 0.28},
            "blocked",
        ),
        (
            "human",
            {"analogyStrength": 0.66, "transferReadiness": 0.70},
            {"asymmetryScore": 0.48, "domainDistance": 0.48},
            {"donorReplicationMaturity": 0.74, "targetReplicationMaturity": 0.68, "replicationRequired": False},
            {"transferHarmRisk": 0.86, "deterministicOverreach": 0.28},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, asymmetry, replication, risk, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "transfer", **row},
            asymmetry_rows={target_id: asymmetry},
            replication_rows={target_id: replication},
            risk_rows={target_id: risk},
            system_risk=0.35,
        )
        statuses.add(decision.transfer_status)
        assert decision.transfer_status == expected

    assert statuses == {
        "analogy-only",
        "bounded-transfer",
        "replication-required",
        "blocked",
        "require-human-review",
    }


def test_bounded_non_final_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "transfer", "analogyStrength": 0.56, "transferReadiness": 0.60},
        asymmetry_rows={"tone": {"asymmetryScore": 0.46, "domainDistance": 0.50}},
        replication_rows={"tone": {"donorReplicationMaturity": 0.64, "targetReplicationMaturity": 0.58, "replicationRequired": True}},
        risk_rows={"tone": {"transferHarmRisk": 0.42, "deterministicOverreach": 0.34}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.asymmetry_context,
            decision.replication_context,
            decision.agency_context,
            decision.fairness_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "replication" in text
    assert "non-final" in text
    assert "final truth" not in text


def test_high_asymmetry_blocking() -> None:
    decision = module.evaluate_target(
        {"targetId": "block", "targetType": "transfer", "analogyStrength": 0.80, "transferReadiness": 0.78},
        asymmetry_rows={"block": {"asymmetryScore": 0.90, "domainDistance": 0.82}},
        replication_rows={"block": {"donorReplicationMaturity": 0.82, "targetReplicationMaturity": 0.78, "replicationRequired": False}},
        risk_rows={"block": {"transferHarmRisk": 0.40, "deterministicOverreach": 0.32}},
        system_risk=0.35,
    )

    assert decision.transfer_status == "blocked"
    assert decision.target_publisher_action == "suppress"


def test_target_domain_replication_enforcement() -> None:
    decision = module.evaluate_target(
        {"targetId": "repl", "targetType": "transfer", "analogyStrength": 0.74, "transferReadiness": 0.74},
        asymmetry_rows={"repl": {"asymmetryScore": 0.38, "domainDistance": 0.42}},
        replication_rows={"repl": {"donorReplicationMaturity": 0.80, "targetReplicationMaturity": 0.48, "replicationRequired": True}},
        risk_rows={"repl": {"transferHarmRisk": 0.38, "deterministicOverreach": 0.30}},
        system_risk=0.35,
    )

    assert decision.transfer_status == "replication-required"
    assert decision.target_publisher_action == "docket"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "transfer"}]})
    _write_json(tmp_path / "bridge/theory_transfer_map.json", bad_map)

    with pytest.raises(module.TheoryTransferInputError):
        module.build_outputs()
