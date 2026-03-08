from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_theory_corpus_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "theory_corpus_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.theory.fixture",
        "producerCommit": "fixture-u-0001",
        "generatedAt": "2026-04-07T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {
        "schema": "audit_fixture_v1",
        "created_at": "2026-04-07T00:00:00Z",
        "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)],
    }


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "THEORY_CORPUS_MAP_PATH", tmp_path / "bridge/theory_corpus_map.json")
    monkeypatch.setattr(module, "THEORY_REVISION_LINEAGE_PATH", tmp_path / "bridge/theory_revision_lineage.json")
    monkeypatch.setattr(module, "NEGATIVE_RESULT_REGISTRY_PATH", tmp_path / "bridge/negative_result_registry.json")
    monkeypatch.setattr(module, "THEORY_COMPETITION_REPORT_PATH", tmp_path / "bridge/theory_competition_report.json")
    monkeypatch.setattr(module, "EXPERIMENTAL_AUDIT_PATH", tmp_path / "bridge/experimental_audit.json")
    monkeypatch.setattr(module, "PREDICTION_AUDIT_PATH", tmp_path / "bridge/prediction_audit.json")
    monkeypatch.setattr(module, "BRANCH_LIFECYCLE_AUDIT_PATH", tmp_path / "bridge/branch_lifecycle_audit.json")
    monkeypatch.setattr(module, "COLLABORATIVE_REVIEW_AUDIT_PATH", tmp_path / "bridge/collaborative_review_audit.json")
    monkeypatch.setattr(module, "THEORY_CORPUS_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/theory_corpus_audit_v1.schema.json"))
    monkeypatch.setattr(module, "THEORY_CORPUS_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/theory_corpus_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "theory_corpus_map.json",
        _artifact(
            {
                "targets": [
                    {
                        "targetId": "target:z",
                        "targetType": "theory",
                        "theoryCoherence": 0.72,
                        "falsificationStrength": 0.68,
                        "replicationStrength": 0.66,
                    },
                    {
                        "targetId": "target:a",
                        "targetType": "theory",
                        "theoryCoherence": 0.60,
                        "falsificationStrength": 0.56,
                        "replicationStrength": 0.54,
                    },
                ]
            }
        ),
    )
    _write_json(
        bridge / "theory_revision_lineage.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "revisionQuality": 0.70, "revisionTransparency": 0.68},
                    {"targetId": "target:a", "revisionQuality": 0.58, "revisionTransparency": 0.56},
                ]
            }
        ),
    )
    _write_json(
        bridge / "negative_result_registry.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "negativeResultPreservation": 0.70, "failedLineErasureRisk": 0.28},
                    {"targetId": "target:a", "negativeResultPreservation": 0.58, "failedLineErasureRisk": 0.42},
                ]
            }
        ),
    )
    _write_json(
        bridge / "theory_competition_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "competitionIntensity": 0.40, "suppressionRisk": 0.32},
                    {"targetId": "target:a", "competitionIntensity": 0.50, "suppressionRisk": 0.44},
                ]
            }
        ),
    )

    for name in (
        "experimental_audit.json",
        "prediction_audit.json",
        "branch_lifecycle_audit.json",
        "collaborative_review_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/theory_corpus_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/theory_corpus_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_theory_status_coverage() -> None:
    cases = [
        (
            "watch",
            {"theoryCoherence": 0.60, "falsificationStrength": 0.56, "replicationStrength": 0.54},
            {"revisionQuality": 0.58, "revisionTransparency": 0.56},
            {"negativeResultPreservation": 0.58, "failedLineErasureRisk": 0.42},
            {"competitionIntensity": 0.50, "suppressionRisk": 0.44},
            "theory-watch",
        ),
        (
            "hypo",
            {"theoryCoherence": 0.56, "falsificationStrength": 0.30, "replicationStrength": 0.58},
            {"revisionQuality": 0.56, "revisionTransparency": 0.56},
            {"negativeResultPreservation": 0.60, "failedLineErasureRisk": 0.38},
            {"competitionIntensity": 0.46, "suppressionRisk": 0.42},
            "hypothesis-only",
        ),
        (
            "replication",
            {"theoryCoherence": 0.62, "falsificationStrength": 0.60, "replicationStrength": 0.40},
            {"revisionQuality": 0.60, "revisionTransparency": 0.58},
            {"negativeResultPreservation": 0.62, "failedLineErasureRisk": 0.36},
            {"competitionIntensity": 0.46, "suppressionRisk": 0.44},
            "replication-pending",
        ),
        (
            "candidate",
            {"theoryCoherence": 0.76, "falsificationStrength": 0.72, "replicationStrength": 0.72},
            {"revisionQuality": 0.72, "revisionTransparency": 0.70},
            {"negativeResultPreservation": 0.72, "failedLineErasureRisk": 0.24},
            {"competitionIntensity": 0.42, "suppressionRisk": 0.30},
            "candidate-review",
        ),
        (
            "competition",
            {"theoryCoherence": 0.66, "falsificationStrength": 0.62, "replicationStrength": 0.60},
            {"revisionQuality": 0.60, "revisionTransparency": 0.58},
            {"negativeResultPreservation": 0.62, "failedLineErasureRisk": 0.40},
            {"competitionIntensity": 0.70, "suppressionRisk": 0.60},
            "competition-active",
        ),
        (
            "human",
            {"theoryCoherence": 0.62, "falsificationStrength": 0.60, "replicationStrength": 0.58},
            {"revisionQuality": 0.58, "revisionTransparency": 0.56},
            {"negativeResultPreservation": 0.50, "failedLineErasureRisk": 0.82},
            {"competitionIntensity": 0.66, "suppressionRisk": 0.84},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, lineage, negative, competition, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "theory", **row},
            lineage_rows={target_id: lineage},
            negative_rows={target_id: negative},
            competition_rows={target_id: competition},
            system_risk=0.35,
        )
        statuses.add(decision.theory_status)
        assert decision.theory_status == expected

    assert statuses == {
        "theory-watch",
        "hypothesis-only",
        "replication-pending",
        "candidate-review",
        "competition-active",
        "require-human-review",
    }


def test_bounded_non_final_language_and_negative_preservation() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "theory", "theoryCoherence": 0.62, "falsificationStrength": 0.58, "replicationStrength": 0.56},
        lineage_rows={"tone": {"revisionQuality": 0.60, "revisionTransparency": 0.58}},
        negative_rows={"tone": {"negativeResultPreservation": 0.64, "failedLineErasureRisk": 0.36}},
        competition_rows={"tone": {"competitionIntensity": 0.54, "suppressionRisk": 0.42}},
        system_risk=0.35,
    )

    text = " ".join([
        decision.falsification_context,
        decision.replication_context,
        decision.revision_context,
        decision.negative_result_context,
        decision.explanation,
    ]).lower()
    assert "bounded" in text
    assert "negative results" in text
    assert "final truth" not in text


def test_competition_handling() -> None:
    decision = module.evaluate_target(
        {"targetId": "comp", "targetType": "theory", "theoryCoherence": 0.66, "falsificationStrength": 0.62, "replicationStrength": 0.60},
        lineage_rows={"comp": {"revisionQuality": 0.60, "revisionTransparency": 0.58}},
        negative_rows={"comp": {"negativeResultPreservation": 0.62, "failedLineErasureRisk": 0.40}},
        competition_rows={"comp": {"competitionIntensity": 0.70, "suppressionRisk": 0.62}},
        system_risk=0.35,
    )
    assert decision.theory_status == "competition-active"
    assert decision.target_publisher_action == "watch"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "theory"}]})
    _write_json(tmp_path / "bridge/theory_corpus_map.json", bad_map)

    with pytest.raises(module.TheoryCorpusInputError):
        module.build_outputs()
