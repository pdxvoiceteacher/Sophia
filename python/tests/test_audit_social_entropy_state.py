from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_social_entropy_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "social_entropy_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.social_entropy.fixture",
        "producerCommit": "fixture-aq-0001",
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
    monkeypatch.setattr(module, "SOCIAL_ENTROPY_MAP_PATH", tmp_path / "bridge/social_entropy_map.json")
    monkeypatch.setattr(module, "CIVIC_COHESION_REPORT_PATH", tmp_path / "bridge/civic_cohesion_report.json")
    monkeypatch.setattr(module, "LEGITIMACY_DRIFT_REPORT_PATH", tmp_path / "bridge/legitimacy_drift_report.json")
    monkeypatch.setattr(module, "REVIEW_PARTICIPATION_RISK_MAP_PATH", tmp_path / "bridge/review_participation_risk_map.json")
    monkeypatch.setattr(module, "COLLABORATIVE_REVIEW_AUDIT_PATH", tmp_path / "bridge/collaborative_review_audit.json")
    monkeypatch.setattr(module, "THEORY_CORPUS_AUDIT_PATH", tmp_path / "bridge/theory_corpus_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "ARCHITECTURE_REVIEW_AUDIT_PATH", tmp_path / "bridge/architecture_review_audit.json")
    monkeypatch.setattr(module, "SOCIAL_ENTROPY_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/social_entropy_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "SOCIAL_ENTROPY_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/social_entropy_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "social_entropy_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "stewardship", "socialStability": 0.68, "repairReadiness": 0.60},
                    {"targetId": "target:a", "targetType": "stewardship", "socialStability": 0.62, "repairReadiness": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "civic_cohesion_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "participationCoverage": 0.66, "dissentSafety": 0.62},
                    {"targetId": "target:a", "participationCoverage": 0.60, "dissentSafety": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "legitimacy_drift_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "legitimacyDrift": 0.42, "transparencyGap": 0.44},
                    {"targetId": "target:a", "legitimacyDrift": 0.50, "transparencyGap": 0.52},
                ]
            }
        ),
    )
    _write_json(
        bridge / "review_participation_risk_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "participationFragility": 0.46, "suppressionPressure": 0.30, "coerciveUnitySignal": 0.32},
                    {"targetId": "target:a", "participationFragility": 0.54, "suppressionPressure": 0.34, "coerciveUnitySignal": 0.36},
                ]
            }
        ),
    )

    for name in (
        "collaborative_review_audit.json",
        "theory_corpus_audit.json",
        "value_alignment_audit.json",
        "architecture_review_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/social_entropy_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/social_entropy_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_social_status_coverage() -> None:
    cases = [
        (
            "healthy",
            {"socialStability": 0.72, "repairReadiness": 0.54},
            {"participationCoverage": 0.68, "dissentSafety": 0.66},
            {"legitimacyDrift": 0.42, "transparencyGap": 0.44},
            {"participationFragility": 0.44, "suppressionPressure": 0.32, "coerciveUnitySignal": 0.34},
            "cohesion-healthy",
        ),
        (
            "repair",
            {"socialStability": 0.62, "repairReadiness": 0.68},
            {"participationCoverage": 0.60, "dissentSafety": 0.46},
            {"legitimacyDrift": 0.60, "transparencyGap": 0.58},
            {"participationFragility": 0.56, "suppressionPressure": 0.34, "coerciveUnitySignal": 0.36},
            "repair-priority",
        ),
        (
            "legit",
            {"socialStability": 0.58, "repairReadiness": 0.62},
            {"participationCoverage": 0.58, "dissentSafety": 0.54},
            {"legitimacyDrift": 0.78, "transparencyGap": 0.62},
            {"participationFragility": 0.58, "suppressionPressure": 0.34, "coerciveUnitySignal": 0.36},
            "legitimacy-risk",
        ),
        (
            "brittle",
            {"socialStability": 0.56, "repairReadiness": 0.54},
            {"participationCoverage": 0.52, "dissentSafety": 0.54},
            {"legitimacyDrift": 0.56, "transparencyGap": 0.54},
            {"participationFragility": 0.74, "suppressionPressure": 0.34, "coerciveUnitySignal": 0.36},
            "participation-brittle",
        ),
        (
            "human",
            {"socialStability": 0.60, "repairReadiness": 0.58},
            {"participationCoverage": 0.58, "dissentSafety": 0.52},
            {"legitimacyDrift": 0.60, "transparencyGap": 0.56},
            {"participationFragility": 0.60, "suppressionPressure": 0.84, "coerciveUnitySignal": 0.34},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, cohesion, legitimacy, participation, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "stewardship", **row},
            cohesion_rows={target_id: cohesion},
            legitimacy_rows={target_id: legitimacy},
            participation_rows={target_id: participation},
            system_risk=0.35,
        )
        statuses.add(decision.social_status)
        assert decision.social_status == expected

    assert statuses == {
        "cohesion-healthy",
        "repair-priority",
        "legitimacy-risk",
        "participation-brittle",
        "require-human-review",
    }


def test_bounded_non_coercive_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "stewardship", "socialStability": 0.62, "repairReadiness": 0.62},
        cohesion_rows={"tone": {"participationCoverage": 0.60, "dissentSafety": 0.56}},
        legitimacy_rows={"tone": {"legitimacyDrift": 0.58, "transparencyGap": 0.56}},
        participation_rows={"tone": {"participationFragility": 0.58, "suppressionPressure": 0.34, "coerciveUnitySignal": 0.36}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.participation_context,
            decision.dissent_context,
            decision.legitimacy_context,
            decision.fairness_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "do not authorize censorship" in text
    assert "coercive unity" in text
    assert "punish" not in text


def test_anti_suppression_enforcement_and_legitimacy_risk() -> None:
    anti = module.evaluate_target(
        {"targetId": "anti", "targetType": "stewardship", "socialStability": 0.62, "repairReadiness": 0.60},
        cohesion_rows={"anti": {"participationCoverage": 0.58, "dissentSafety": 0.54}},
        legitimacy_rows={"anti": {"legitimacyDrift": 0.60, "transparencyGap": 0.58}},
        participation_rows={"anti": {"participationFragility": 0.58, "suppressionPressure": 0.82, "coerciveUnitySignal": 0.40}},
        system_risk=0.35,
    )
    legit = module.evaluate_target(
        {"targetId": "legit", "targetType": "stewardship", "socialStability": 0.58, "repairReadiness": 0.62},
        cohesion_rows={"legit": {"participationCoverage": 0.60, "dissentSafety": 0.54}},
        legitimacy_rows={"legit": {"legitimacyDrift": 0.78, "transparencyGap": 0.62}},
        participation_rows={"legit": {"participationFragility": 0.58, "suppressionPressure": 0.34, "coerciveUnitySignal": 0.36}},
        system_risk=0.35,
    )

    assert anti.social_status == "require-human-review"
    assert legit.social_status == "legitimacy-risk"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "stewardship"}]})
    _write_json(tmp_path / "bridge/social_entropy_map.json", bad_map)

    with pytest.raises(module.SocialEntropyInputError):
        module.build_outputs()
