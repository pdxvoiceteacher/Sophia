from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_evidence_authority_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "evidence_authority_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.evidence_authority.fixture",
        "producerCommit": "fixture-u-0001",
        "generatedAt": "2026-04-01T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {
        "schema": "audit_fixture_v1",
        "created_at": "2026-04-01T00:00:00Z",
        "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)],
    }


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "EVIDENCE_AUTHORITY_MAP_PATH", tmp_path / "bridge/evidence_authority_map.json")
    monkeypatch.setattr(module, "EVIDENCE_AUTHORITY_SUMMARY_PATH", tmp_path / "bridge/evidence_authority_summary.json")
    monkeypatch.setattr(module, "PROPAGATION_RIGHTS_MAP_PATH", tmp_path / "bridge/propagation_rights_map.json")
    monkeypatch.setattr(module, "MATURITY_GATE_REPORT_PATH", tmp_path / "bridge/maturity_gate_report.json")
    monkeypatch.setattr(module, "VERIFICATION_AUDIT_PATH", tmp_path / "bridge/verification_audit.json")
    monkeypatch.setattr(module, "PUBLIC_RECORD_AUDIT_PATH", tmp_path / "bridge/public_record_audit.json")
    monkeypatch.setattr(module, "SYMBOLIC_FIELD_AUDIT_PATH", tmp_path / "bridge/symbolic_field_audit.json")
    monkeypatch.setattr(module, "INVESTIGATION_AUDIT_PATH", tmp_path / "bridge/investigation_audit.json")
    monkeypatch.setattr(module, "CLOSURE_AUDIT_PATH", tmp_path / "bridge/closure_audit.json")
    monkeypatch.setattr(module, "PRECEDENT_AUDIT_PATH", tmp_path / "bridge/precedent_audit.json")
    monkeypatch.setattr(module, "EVIDENCE_AUTHORITY_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/evidence_authority_audit_v1.schema.json"))
    monkeypatch.setattr(module, "EVIDENCE_AUTHORITY_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/evidence_authority_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "evidence_authority_map.json",
        _artifact(
            {
                "targets": [
                    {
                        "targetId": "target:z",
                        "targetType": "claim",
                        "evidenceMaturity": 0.8,
                        "authorityLevel": 0.5,
                        "propagationExposure": 0.4,
                    },
                    {
                        "targetId": "target:a",
                        "targetType": "claim",
                        "evidenceMaturity": 0.5,
                        "authorityLevel": 0.52,
                        "propagationExposure": 0.4,
                    },
                ]
            }
        ),
    )
    _write_json(
        bridge / "evidence_authority_summary.json",
        _artifact(
            {
                "meanEvidenceMaturity": 0.5,
                "meanAuthorityLevel": 0.45,
                "meanPropagationExposure": 0.4,
                "meanPropagationRight": 0.5,
                "meanEntityAmbiguity": 0.35,
                "meanGateSeverity": 0.35,
                "meanContradictionScore": 0.25,
                "meanVerificationReadiness": 0.65,
            }
        ),
    )
    _write_json(
        bridge / "propagation_rights_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "propagationRight": 0.6, "entityAmbiguity": 0.2},
                    {"targetId": "target:a", "propagationRight": 0.7, "entityAmbiguity": 0.2},
                ]
            }
        ),
    )
    _write_json(
        bridge / "maturity_gate_report.json",
        _artifact(
            {
                "targets": [
                    {
                        "targetId": "target:z",
                        "gateSeverity": 0.2,
                        "contradictionScore": 0.2,
                        "verificationReadiness": 0.8,
                    },
                    {
                        "targetId": "target:a",
                        "gateSeverity": 0.25,
                        "contradictionScore": 0.2,
                        "verificationReadiness": 0.75,
                    },
                ]
            }
        ),
    )

    for name in (
        "verification_audit.json",
        "public_record_audit.json",
        "symbolic_field_audit.json",
        "investigation_audit.json",
        "closure_audit.json",
        "precedent_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    # Deterministic ordering by targetId
    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/evidence_authority_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/evidence_authority_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_authority_status_coverage() -> None:
    summary = {
        "meanEvidenceMaturity": 0.5,
        "meanAuthorityLevel": 0.5,
        "meanPropagationExposure": 0.5,
        "meanPropagationRight": 0.5,
        "meanEntityAmbiguity": 0.4,
        "meanGateSeverity": 0.4,
        "meanContradictionScore": 0.4,
        "meanVerificationReadiness": 0.5,
    }

    cases = [
        (
            {"targetId": "bounds", "evidenceMaturity": 0.85, "authorityLevel": 0.45, "propagationExposure": 0.3},
            {"gateSeverity": 0.2, "contradictionScore": 0.2, "verificationReadiness": 0.8},
            "within-bounds",
        ),
        (
            {"targetId": "over", "evidenceMaturity": 0.45, "authorityLevel": 0.75, "propagationExposure": 0.6},
            {"gateSeverity": 0.35, "contradictionScore": 0.35, "verificationReadiness": 0.65},
            "over-propagated",
        ),
        (
            {"targetId": "verify", "evidenceMaturity": 0.55, "authorityLevel": 0.45, "propagationExposure": 0.35},
            {"gateSeverity": 0.45, "contradictionScore": 0.3, "verificationReadiness": 0.25},
            "verify-first",
        ),
        (
            {"targetId": "restrict", "evidenceMaturity": 0.3, "authorityLevel": 0.75, "propagationExposure": 0.8},
            {"gateSeverity": 0.4, "contradictionScore": 0.3, "verificationReadiness": 0.6},
            "restrict-propagation",
        ),
        (
            {"targetId": "human", "evidenceMaturity": 0.45, "authorityLevel": 0.5, "propagationExposure": 0.5},
            {"gateSeverity": 0.8, "contradictionScore": 0.85, "verificationReadiness": 0.4},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for row, gate_row, expected in cases:
        decision = module.evaluate_target(
            row,
            summary=summary,
            rights_rows={row["targetId"]: {"propagationRight": 0.55, "entityAmbiguity": 0.2}},
            gate_rows={row["targetId"]: gate_row},
            system_risk=0.35,
        )
        statuses.add(decision.authority_status)
        assert decision.authority_status == expected

    assert statuses == {
        "within-bounds",
        "over-propagated",
        "verify-first",
        "restrict-propagation",
        "require-human-review",
    }


def test_non_accusatory_bounded_language() -> None:
    summary = {
        "meanEvidenceMaturity": 0.5,
        "meanAuthorityLevel": 0.5,
        "meanPropagationExposure": 0.5,
        "meanPropagationRight": 0.5,
        "meanEntityAmbiguity": 0.4,
        "meanGateSeverity": 0.4,
        "meanContradictionScore": 0.4,
        "meanVerificationReadiness": 0.5,
    }
    decision = module.evaluate_target(
        {"targetId": "tone", "evidenceMaturity": 0.5, "authorityLevel": 0.7, "propagationExposure": 0.65},
        summary=summary,
        rights_rows={"tone": {"propagationRight": 0.5, "entityAmbiguity": 0.3}},
        gate_rows={"tone": {"gateSeverity": 0.45, "contradictionScore": 0.45, "verificationReadiness": 0.55}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.maturity_context,
            decision.claim_context,
            decision.entity_context,
            decision.contradiction_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "accuse" not in text
    assert "guilty" not in text
    assert "defame" not in text


def test_over_propagation_detection() -> None:
    summary = {
        "meanEvidenceMaturity": 0.5,
        "meanAuthorityLevel": 0.5,
        "meanPropagationExposure": 0.5,
        "meanPropagationRight": 0.5,
        "meanEntityAmbiguity": 0.4,
        "meanGateSeverity": 0.4,
        "meanContradictionScore": 0.4,
        "meanVerificationReadiness": 0.5,
    }
    decision = module.evaluate_target(
        {"targetId": "over", "evidenceMaturity": 0.46, "authorityLevel": 0.82, "propagationExposure": 0.55},
        summary=summary,
        rights_rows={"over": {"propagationRight": 0.55, "entityAmbiguity": 0.2}},
        gate_rows={"over": {"gateSeverity": 0.35, "contradictionScore": 0.3, "verificationReadiness": 0.72}},
        system_risk=0.3,
    )
    assert decision.authority_status == "over-propagated"
    assert decision.target_publisher_action == "watch"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact(
        {
            "producerCommit": "",
            "targets": [{"targetId": "target:a", "targetType": "claim", "evidenceMaturity": 0.5, "authorityLevel": 0.4}],
        }
    )
    _write_json(tmp_path / "bridge/evidence_authority_map.json", bad_map)

    with pytest.raises(module.EvidenceAuthorityInputError):
        module.build_outputs()
