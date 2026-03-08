from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_review_packet_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "review_packet_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.review_packet.fixture",
        "producerCommit": "fixture-u-0001",
        "generatedAt": "2026-04-02T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {
        "schema": "audit_fixture_v1",
        "created_at": "2026-04-02T00:00:00Z",
        "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)],
    }


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "REVIEW_PACKET_MAP_PATH", tmp_path / "bridge/review_packet_map.json")
    monkeypatch.setattr(module, "REVIEW_PACKET_SUMMARY_PATH", tmp_path / "bridge/review_packet_summary.json")
    monkeypatch.setattr(module, "NARRATIVE_SYNTHESIS_MAP_PATH", tmp_path / "bridge/narrative_synthesis_map.json")
    monkeypatch.setattr(module, "UNCERTAINTY_DISCLOSURE_REPORT_PATH", tmp_path / "bridge/uncertainty_disclosure_report.json")
    monkeypatch.setattr(module, "INVESTIGATION_AUDIT_PATH", tmp_path / "bridge/investigation_audit.json")
    monkeypatch.setattr(module, "VERIFICATION_AUDIT_PATH", tmp_path / "bridge/verification_audit.json")
    monkeypatch.setattr(module, "PUBLIC_RECORD_AUDIT_PATH", tmp_path / "bridge/public_record_audit.json")
    monkeypatch.setattr(module, "EVIDENCE_AUTHORITY_AUDIT_PATH", tmp_path / "bridge/evidence_authority_audit.json")
    monkeypatch.setattr(module, "ENVIRONMENT_AUDIT_PATH", tmp_path / "bridge/environment_audit.json")
    monkeypatch.setattr(module, "REVIEW_PACKET_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/review_packet_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "REVIEW_PACKET_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/review_packet_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "review_packet_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "packet", "packetMaturity": 0.80, "packetConfidence": 0.82},
                    {"targetId": "target:a", "targetType": "packet", "packetMaturity": 0.58, "packetConfidence": 0.56},
                ]
            }
        ),
    )
    _write_json(
        bridge / "review_packet_summary.json",
        _artifact(
            {
                "meanPacketMaturity": 0.55,
                "meanPacketConfidence": 0.55,
                "meanSynthesisConfidence": 0.55,
                "meanAmbiguityScore": 0.4,
                "meanDisclosureCompleteness": 0.6,
                "meanUncertaintyLoad": 0.4,
                "meanContradictionScore": 0.35,
            }
        ),
    )
    _write_json(
        bridge / "narrative_synthesis_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "synthesisConfidence": 0.80, "ambiguityScore": 0.20},
                    {"targetId": "target:a", "synthesisConfidence": 0.58, "ambiguityScore": 0.40},
                ]
            }
        ),
    )
    _write_json(
        bridge / "uncertainty_disclosure_report.json",
        _artifact(
            {
                "targets": [
                    {
                        "targetId": "target:z",
                        "disclosureCompleteness": 0.82,
                        "uncertaintyLoad": 0.28,
                        "contradictionScore": 0.24,
                    },
                    {
                        "targetId": "target:a",
                        "disclosureCompleteness": 0.60,
                        "uncertaintyLoad": 0.48,
                        "contradictionScore": 0.40,
                    },
                ]
            }
        ),
    )
    for name in (
        "investigation_audit.json",
        "verification_audit.json",
        "public_record_audit.json",
        "evidence_authority_audit.json",
        "environment_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/review_packet_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/review_packet_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_packet_status_coverage() -> None:
    summary = {
        "meanPacketMaturity": 0.5,
        "meanPacketConfidence": 0.5,
        "meanSynthesisConfidence": 0.5,
        "meanAmbiguityScore": 0.4,
        "meanDisclosureCompleteness": 0.6,
        "meanUncertaintyLoad": 0.4,
        "meanContradictionScore": 0.4,
    }

    cases = [
        (
            {"targetId": "ready", "packetMaturity": 0.80, "packetConfidence": 0.80},
            {"synthesisConfidence": 0.75, "ambiguityScore": 0.25},
            {"disclosureCompleteness": 0.82, "uncertaintyLoad": 0.28, "contradictionScore": 0.30},
            "review-ready",
        ),
        (
            {"targetId": "prov", "packetMaturity": 0.55, "packetConfidence": 0.56},
            {"synthesisConfidence": 0.54, "ambiguityScore": 0.45},
            {"disclosureCompleteness": 0.62, "uncertaintyLoad": 0.46, "contradictionScore": 0.42},
            "provisional",
        ),
        (
            {"targetId": "heavy", "packetMaturity": 0.60, "packetConfidence": 0.62},
            {"synthesisConfidence": 0.60, "ambiguityScore": 0.72},
            {"disclosureCompleteness": 0.62, "uncertaintyLoad": 0.74, "contradictionScore": 0.40},
            "uncertainty-heavy",
        ),
        (
            {"targetId": "verify", "packetMaturity": 0.58, "packetConfidence": 0.58},
            {"synthesisConfidence": 0.57, "ambiguityScore": 0.40},
            {"disclosureCompleteness": 0.30, "uncertaintyLoad": 0.50, "contradictionScore": 0.35},
            "verify-first",
        ),
        (
            {"targetId": "human", "packetMaturity": 0.56, "packetConfidence": 0.55},
            {"synthesisConfidence": 0.56, "ambiguityScore": 0.80},
            {"disclosureCompleteness": 0.50, "uncertaintyLoad": 0.66, "contradictionScore": 0.85},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for row, narrative, disclosure, expected in cases:
        decision = module.evaluate_target(
            row,
            summary=summary,
            narrative_rows={row["targetId"]: narrative},
            disclosure_rows={row["targetId"]: disclosure},
            system_risk=0.35,
        )
        statuses.add(decision.packet_status)
        assert decision.packet_status == expected

    assert statuses == {"review-ready", "provisional", "uncertainty-heavy", "verify-first", "require-human-review"}


def test_non_accusatory_bounded_language() -> None:
    summary = {
        "meanPacketMaturity": 0.5,
        "meanPacketConfidence": 0.5,
        "meanSynthesisConfidence": 0.5,
        "meanAmbiguityScore": 0.4,
        "meanDisclosureCompleteness": 0.6,
        "meanUncertaintyLoad": 0.4,
        "meanContradictionScore": 0.4,
    }
    decision = module.evaluate_target(
        {"targetId": "tone", "packetMaturity": 0.62, "packetConfidence": 0.61},
        summary=summary,
        narrative_rows={"tone": {"synthesisConfidence": 0.58, "ambiguityScore": 0.52}},
        disclosure_rows={"tone": {"disclosureCompleteness": 0.60, "uncertaintyLoad": 0.55, "contradictionScore": 0.44}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.maturity_context,
            decision.ambiguity_context,
            decision.authority_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "accuse" not in text
    assert "guilty" not in text
    assert "allegation" not in text


def test_uncertainty_disclosure_enforcement() -> None:
    summary = {
        "meanPacketMaturity": 0.5,
        "meanPacketConfidence": 0.5,
        "meanSynthesisConfidence": 0.5,
        "meanAmbiguityScore": 0.4,
        "meanDisclosureCompleteness": 0.6,
        "meanUncertaintyLoad": 0.4,
        "meanContradictionScore": 0.4,
    }
    decision = module.evaluate_target(
        {"targetId": "disclose", "packetMaturity": 0.74, "packetConfidence": 0.70},
        summary=summary,
        narrative_rows={"disclose": {"synthesisConfidence": 0.72, "ambiguityScore": 0.30}},
        disclosure_rows={"disclose": {"disclosureCompleteness": 0.32, "uncertaintyLoad": 0.45, "contradictionScore": 0.30}},
        system_risk=0.30,
    )
    assert decision.packet_status == "verify-first"
    assert decision.target_publisher_action == "suppress"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "packet"}]})
    _write_json(tmp_path / "bridge/review_packet_map.json", bad)

    with pytest.raises(module.ReviewPacketInputError):
        module.build_outputs()
