from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_responsibility_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "responsibility_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.responsibility.fixture",
        "producerCommit": "fixture-aj-0001",
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
    monkeypatch.setattr(module, "RESPONSIBILITY_MODE_MAP_PATH", tmp_path / "bridge/responsibility_mode_map.json")
    monkeypatch.setattr(module, "SUPPORT_PATHWAY_MAP_PATH", tmp_path / "bridge/support_pathway_map.json")
    monkeypatch.setattr(module, "INTERVENTION_BOUNDARY_REPORT_PATH", tmp_path / "bridge/intervention_boundary_report.json")
    monkeypatch.setattr(module, "SANCTION_SUPPRESSION_GATE_PATH", tmp_path / "bridge/sanction_suppression_gate.json")
    monkeypatch.setattr(module, "AGENCY_MODE_AUDIT_PATH", tmp_path / "bridge/agency_mode_audit.json")
    monkeypatch.setattr(module, "THEORY_CORPUS_AUDIT_PATH", tmp_path / "bridge/theory_corpus_audit.json")
    monkeypatch.setattr(module, "EXPERIMENTAL_AUDIT_PATH", tmp_path / "bridge/experimental_audit.json")
    monkeypatch.setattr(module, "COLLABORATIVE_REVIEW_AUDIT_PATH", tmp_path / "bridge/collaborative_review_audit.json")
    monkeypatch.setattr(module, "RESPONSIBILITY_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/responsibility_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "RESPONSIBILITY_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/responsibility_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "responsibility_mode_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "case", "supportFit": 0.70, "consentFit": 0.48, "accountabilityNeed": 0.52},
                    {"targetId": "target:a", "targetType": "case", "supportFit": 0.46, "consentFit": 0.70, "accountabilityNeed": 0.54},
                ]
            }
        ),
    )
    _write_json(
        bridge / "support_pathway_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "pathwayReadiness": 0.62, "structuralConstraint": 0.42},
                    {"targetId": "target:a", "pathwayReadiness": 0.58, "structuralConstraint": 0.44},
                ]
            }
        ),
    )
    _write_json(
        bridge / "intervention_boundary_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "interventionRisk": 0.40, "consentClarity": 0.58},
                    {"targetId": "target:a", "interventionRisk": 0.38, "consentClarity": 0.64},
                ]
            }
        ),
    )
    _write_json(
        bridge / "sanction_suppression_gate.json",
        _artifact(
            {
                "targets": [
                    {
                        "targetId": "target:z",
                        "deterministicOverreach": 0.32,
                        "punitiveVolitional": 0.34,
                        "sanctionSuppressed": False,
                    },
                    {
                        "targetId": "target:a",
                        "deterministicOverreach": 0.30,
                        "punitiveVolitional": 0.28,
                        "sanctionSuppressed": False,
                    },
                ]
            }
        ),
    )

    for name in (
        "agency_mode_audit.json",
        "theory_corpus_audit.json",
        "experimental_audit.json",
        "collaborative_review_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/responsibility_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/responsibility_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_responsibility_status_coverage() -> None:
    cases = [
        (
            "support",
            {"supportFit": 0.72, "consentFit": 0.48, "accountabilityNeed": 0.52},
            {"pathwayReadiness": 0.62, "structuralConstraint": 0.42},
            {"interventionRisk": 0.42, "consentClarity": 0.56},
            {"deterministicOverreach": 0.30, "punitiveVolitional": 0.34, "sanctionSuppressed": False},
            "support-first",
        ),
        (
            "consent",
            {"supportFit": 0.48, "consentFit": 0.72, "accountabilityNeed": 0.52},
            {"pathwayReadiness": 0.62, "structuralConstraint": 0.42},
            {"interventionRisk": 0.40, "consentClarity": 0.66},
            {"deterministicOverreach": 0.30, "punitiveVolitional": 0.34, "sanctionSuppressed": False},
            "consent-first",
        ),
        (
            "mixed",
            {"supportFit": 0.60, "consentFit": 0.60, "accountabilityNeed": 0.70},
            {"pathwayReadiness": 0.58, "structuralConstraint": 0.50},
            {"interventionRisk": 0.44, "consentClarity": 0.62},
            {"deterministicOverreach": 0.30, "punitiveVolitional": 0.34, "sanctionSuppressed": False},
            "mixed-accountability",
        ),
        (
            "suppressed",
            {"supportFit": 0.70, "consentFit": 0.48, "accountabilityNeed": 0.52},
            {"pathwayReadiness": 0.62, "structuralConstraint": 0.42},
            {"interventionRisk": 0.40, "consentClarity": 0.56},
            {"deterministicOverreach": 0.30, "punitiveVolitional": 0.34, "sanctionSuppressed": True},
            "sanction-suppressed",
        ),
        (
            "human",
            {"supportFit": 0.58, "consentFit": 0.58, "accountabilityNeed": 0.54},
            {"pathwayReadiness": 0.52, "structuralConstraint": 0.78},
            {"interventionRisk": 0.50, "consentClarity": 0.48},
            {"deterministicOverreach": 0.40, "punitiveVolitional": 0.42, "sanctionSuppressed": False},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, support, intervention, gate, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "case", **row},
            support_rows={target_id: support},
            intervention_rows={target_id: intervention},
            sanction_rows={target_id: gate},
            system_risk=0.35,
        )
        statuses.add(decision.responsibility_status)
        assert decision.responsibility_status == expected

    assert statuses == {
        "support-first",
        "consent-first",
        "mixed-accountability",
        "sanction-suppressed",
        "require-human-review",
    }


def test_bounded_non_punitive_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "case", "supportFit": 0.68, "consentFit": 0.52, "accountabilityNeed": 0.56},
        support_rows={"tone": {"pathwayReadiness": 0.60, "structuralConstraint": 0.44}},
        intervention_rows={"tone": {"interventionRisk": 0.42, "consentClarity": 0.56}},
        sanction_rows={"tone": {"deterministicOverreach": 0.34, "punitiveVolitional": 0.36, "sanctionSuppressed": False}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.agency_context,
            decision.structural_constraint_context,
            decision.fairness_context,
            decision.intervention_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "support" in text
    assert "consent" in text
    assert "condemn" not in text
    assert "punish" not in text
    assert "blame" not in text


def test_deterministic_overreach_and_punitive_volitional_prevention() -> None:
    det = module.evaluate_target(
        {"targetId": "det", "targetType": "case", "supportFit": 0.72, "consentFit": 0.46, "accountabilityNeed": 0.56},
        support_rows={"det": {"pathwayReadiness": 0.60, "structuralConstraint": 0.42}},
        intervention_rows={"det": {"interventionRisk": 0.46, "consentClarity": 0.56}},
        sanction_rows={"det": {"deterministicOverreach": 0.84, "punitiveVolitional": 0.36, "sanctionSuppressed": False}},
        system_risk=0.35,
    )
    vol = module.evaluate_target(
        {"targetId": "vol", "targetType": "case", "supportFit": 0.46, "consentFit": 0.72, "accountabilityNeed": 0.56},
        support_rows={"vol": {"pathwayReadiness": 0.60, "structuralConstraint": 0.42}},
        intervention_rows={"vol": {"interventionRisk": 0.46, "consentClarity": 0.56}},
        sanction_rows={"vol": {"deterministicOverreach": 0.36, "punitiveVolitional": 0.84, "sanctionSuppressed": False}},
        system_risk=0.35,
    )

    assert det.responsibility_status == "require-human-review"
    assert vol.responsibility_status == "require-human-review"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "case"}]})
    _write_json(tmp_path / "bridge/responsibility_mode_map.json", bad_map)

    with pytest.raises(module.ResponsibilityInputError):
        module.build_outputs()
