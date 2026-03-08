from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_emergent_domain_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "emergent_domain_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.emergent_domain.fixture",
        "producerCommit": "fixture-at-0001",
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
    monkeypatch.setattr(module, "EMERGENT_DOMAIN_MAP_PATH", tmp_path / "bridge/emergent_domain_map.json")
    monkeypatch.setattr(module, "CROSS_DOMAIN_INVARIANT_REPORT_PATH", tmp_path / "bridge/cross_domain_invariant_report.json")
    monkeypatch.setattr(module, "FIELD_BIRTH_PRESSURE_REPORT_PATH", tmp_path / "bridge/field_birth_pressure_report.json")
    monkeypatch.setattr(module, "DOMAIN_BOUNDARY_FAILURE_MAP_PATH", tmp_path / "bridge/domain_boundary_failure_map.json")
    monkeypatch.setattr(module, "THEORY_TRANSFER_AUDIT_PATH", tmp_path / "bridge/theory_transfer_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "CURIOSITY_AUDIT_PATH", tmp_path / "bridge/curiosity_audit.json")
    monkeypatch.setattr(module, "SOCIAL_ENTROPY_AUDIT_PATH", tmp_path / "bridge/social_entropy_audit.json")
    monkeypatch.setattr(module, "COMMONS_PARTICIPATION_AUDIT_PATH", tmp_path / "bridge/commons_participation_audit.json")
    monkeypatch.setattr(module, "EMERGENT_DOMAIN_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/emergent_domain_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "EMERGENT_DOMAIN_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/emergent_domain_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "emergent_domain_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "domain", "domainConvergence": 0.68, "noveltyConsistency": 0.64},
                    {"targetId": "target:a", "targetType": "domain", "domainConvergence": 0.60, "noveltyConsistency": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "cross_domain_invariant_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "invariantStrength": 0.66, "crossDomainReplicability": 0.64},
                    {"targetId": "target:a", "invariantStrength": 0.60, "crossDomainReplicability": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "field_birth_pressure_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "fieldBirthPressure": 0.62, "socialLegibility": 0.60},
                    {"targetId": "target:a", "fieldBirthPressure": 0.58, "socialLegibility": 0.56},
                ]
            }
        ),
    )
    _write_json(
        bridge / "domain_boundary_failure_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "boundaryFailureRisk": 0.44, "overclaimPressure": 0.36, "canonizationSignal": 0.34},
                    {"targetId": "target:a", "boundaryFailureRisk": 0.50, "overclaimPressure": 0.40, "canonizationSignal": 0.38},
                ]
            }
        ),
    )

    for name in (
        "theory_transfer_audit.json",
        "value_alignment_audit.json",
        "curiosity_audit.json",
        "social_entropy_audit.json",
        "commons_participation_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/emergent_domain_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/emergent_domain_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_domain_status_coverage() -> None:
    cases = [
        (
            "watch",
            {"domainConvergence": 0.54, "noveltyConsistency": 0.54},
            {"invariantStrength": 0.54, "crossDomainReplicability": 0.54},
            {"fieldBirthPressure": 0.54, "socialLegibility": 0.56},
            {"boundaryFailureRisk": 0.46, "overclaimPressure": 0.44, "canonizationSignal": 0.40},
            "emergent-watch",
        ),
        (
            "rising",
            {"domainConvergence": 0.66, "noveltyConsistency": 0.62},
            {"invariantStrength": 0.62, "crossDomainReplicability": 0.58},
            {"fieldBirthPressure": 0.60, "socialLegibility": 0.60},
            {"boundaryFailureRisk": 0.46, "overclaimPressure": 0.44, "canonizationSignal": 0.40},
            "convergence-rising",
        ),
        (
            "threshold",
            {"domainConvergence": 0.78, "noveltyConsistency": 0.72},
            {"invariantStrength": 0.74, "crossDomainReplicability": 0.70},
            {"fieldBirthPressure": 0.70, "socialLegibility": 0.60},
            {"boundaryFailureRisk": 0.48, "overclaimPressure": 0.46, "canonizationSignal": 0.42},
            "field-birth-threshold",
        ),
        (
            "legibility",
            {"domainConvergence": 0.66, "noveltyConsistency": 0.62},
            {"invariantStrength": 0.62, "crossDomainReplicability": 0.58},
            {"fieldBirthPressure": 0.60, "socialLegibility": 0.30},
            {"boundaryFailureRisk": 0.74, "overclaimPressure": 0.44, "canonizationSignal": 0.40},
            "legibility-risk",
        ),
        (
            "human",
            {"domainConvergence": 0.66, "noveltyConsistency": 0.62},
            {"invariantStrength": 0.62, "crossDomainReplicability": 0.58},
            {"fieldBirthPressure": 0.60, "socialLegibility": 0.60},
            {"boundaryFailureRisk": 0.48, "overclaimPressure": 0.82, "canonizationSignal": 0.42},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, invariant, pressure, boundary, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "domain", **row},
            invariant_rows={target_id: invariant},
            pressure_rows={target_id: pressure},
            boundary_rows={target_id: boundary},
            system_risk=0.35,
        )
        statuses.add(decision.domain_status)
        assert decision.domain_status == expected

    assert statuses == {
        "emergent-watch",
        "convergence-rising",
        "field-birth-threshold",
        "legibility-risk",
        "require-human-review",
    }


def test_bounded_non_grandiose_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "domain", "domainConvergence": 0.66, "noveltyConsistency": 0.62},
        invariant_rows={"tone": {"invariantStrength": 0.62, "crossDomainReplicability": 0.58}},
        pressure_rows={"tone": {"fieldBirthPressure": 0.60, "socialLegibility": 0.60}},
        boundary_rows={"tone": {"boundaryFailureRisk": 0.48, "overclaimPressure": 0.44, "canonizationSignal": 0.40}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.convergence_context,
            decision.transfer_context,
            decision.curiosity_context,
            decision.commons_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "do not certify final" in text
    assert "humility" in text
    assert "inevitable" not in text


def test_legibility_risk_and_overclaim_suppression() -> None:
    leg = module.evaluate_target(
        {"targetId": "leg", "targetType": "domain", "domainConvergence": 0.66, "noveltyConsistency": 0.62},
        invariant_rows={"leg": {"invariantStrength": 0.62, "crossDomainReplicability": 0.58}},
        pressure_rows={"leg": {"fieldBirthPressure": 0.60, "socialLegibility": 0.30}},
        boundary_rows={"leg": {"boundaryFailureRisk": 0.74, "overclaimPressure": 0.44, "canonizationSignal": 0.40}},
        system_risk=0.35,
    )
    overclaim = module.evaluate_target(
        {"targetId": "over", "targetType": "domain", "domainConvergence": 0.74, "noveltyConsistency": 0.70},
        invariant_rows={"over": {"invariantStrength": 0.70, "crossDomainReplicability": 0.66}},
        pressure_rows={"over": {"fieldBirthPressure": 0.68, "socialLegibility": 0.60}},
        boundary_rows={"over": {"boundaryFailureRisk": 0.50, "overclaimPressure": 0.84, "canonizationSignal": 0.44}},
        system_risk=0.35,
    )

    assert leg.domain_status == "legibility-risk"
    assert leg.target_publisher_action == "docket"
    assert overclaim.domain_status == "require-human-review"
    assert overclaim.target_publisher_action == "suppress"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "domain"}]})
    _write_json(tmp_path / "bridge/emergent_domain_map.json", bad_map)

    with pytest.raises(module.EmergentDomainInputError):
        module.build_outputs()


def test_supporting_audits_must_have_records(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    _write_json(
        tmp_path / "bridge/theory_transfer_audit.json",
        {"schema": "theory_transfer_audit_v1", "created_at": "2026-04-08T00:00:00Z", "records": "invalid"},
    )

    with pytest.raises(module.EmergentDomainInputError):
        module.build_outputs()
