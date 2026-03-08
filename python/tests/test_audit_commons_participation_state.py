from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_commons_participation_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "commons_participation_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.commons_participation.fixture",
        "producerCommit": "fixture-as-0001",
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
    monkeypatch.setattr(module, "CIVIC_LITERACY_MAP_PATH", tmp_path / "bridge/civic_literacy_map.json")
    monkeypatch.setattr(module, "PARTICIPATION_BARRIER_REPORT_PATH", tmp_path / "bridge/participation_barrier_report.json")
    monkeypatch.setattr(module, "COMMONS_ACCESSIBILITY_INDEX_PATH", tmp_path / "bridge/commons_accessibility_index.json")
    monkeypatch.setattr(module, "EPISTEMIC_LEGIBILITY_MAP_PATH", tmp_path / "bridge/epistemic_legibility_map.json")
    monkeypatch.setattr(module, "SOCIAL_ENTROPY_AUDIT_PATH", tmp_path / "bridge/social_entropy_audit.json")
    monkeypatch.setattr(module, "FEDERATED_GOVERNANCE_AUDIT_PATH", tmp_path / "bridge/federated_governance_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "ARCHITECTURE_REVIEW_AUDIT_PATH", tmp_path / "bridge/architecture_review_audit.json")
    monkeypatch.setattr(module, "COMMONS_PARTICIPATION_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/commons_participation_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "COMMONS_PARTICIPATION_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/commons_participation_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "civic_literacy_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "commons", "literacyDepth": 0.68, "translationReadiness": 0.66},
                    {"targetId": "target:a", "targetType": "commons", "literacyDepth": 0.60, "translationReadiness": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "participation_barrier_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "participationBarrier": 0.42, "onboardingFriction": 0.44},
                    {"targetId": "target:a", "participationBarrier": 0.48, "onboardingFriction": 0.50},
                ]
            }
        ),
    )
    _write_json(
        bridge / "commons_accessibility_index.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "accessibilityGap": 0.42, "inclusionSignal": 0.66},
                    {"targetId": "target:a", "accessibilityGap": 0.48, "inclusionSignal": 0.60},
                ]
            }
        ),
    )
    _write_json(
        bridge / "epistemic_legibility_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "epistemicLegibility": 0.66, "prestigeMystiqueRisk": 0.34, "exclusionPressure": 0.32},
                    {"targetId": "target:a", "epistemicLegibility": 0.60, "prestigeMystiqueRisk": 0.40, "exclusionPressure": 0.36},
                ]
            }
        ),
    )

    for name in (
        "social_entropy_audit.json",
        "federated_governance_audit.json",
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

    audit_schema = json.loads(Path("/workspace/Sophia/schema/commons_participation_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/commons_participation_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_participation_status_coverage() -> None:
    cases = [
        (
            "open",
            {"literacyDepth": 0.70, "translationReadiness": 0.68},
            {"participationBarrier": 0.40, "onboardingFriction": 0.42},
            {"accessibilityGap": 0.40, "inclusionSignal": 0.66},
            {"epistemicLegibility": 0.68, "prestigeMystiqueRisk": 0.34, "exclusionPressure": 0.32},
            "commons-open",
        ),
        (
            "literacy",
            {"literacyDepth": 0.44, "translationReadiness": 0.52},
            {"participationBarrier": 0.62, "onboardingFriction": 0.64},
            {"accessibilityGap": 0.50, "inclusionSignal": 0.56},
            {"epistemicLegibility": 0.58, "prestigeMystiqueRisk": 0.44, "exclusionPressure": 0.40},
            "literacy-repair",
        ),
        (
            "access",
            {"literacyDepth": 0.56, "translationReadiness": 0.56},
            {"participationBarrier": 0.52, "onboardingFriction": 0.54},
            {"accessibilityGap": 0.74, "inclusionSignal": 0.30},
            {"epistemicLegibility": 0.60, "prestigeMystiqueRisk": 0.42, "exclusionPressure": 0.40},
            "accessibility-risk",
        ),
        (
            "priest",
            {"literacyDepth": 0.56, "translationReadiness": 0.56},
            {"participationBarrier": 0.50, "onboardingFriction": 0.52},
            {"accessibilityGap": 0.52, "inclusionSignal": 0.56},
            {"epistemicLegibility": 0.32, "prestigeMystiqueRisk": 0.72, "exclusionPressure": 0.54},
            "priesthood-risk",
        ),
        (
            "human",
            {"literacyDepth": 0.56, "translationReadiness": 0.56},
            {"participationBarrier": 0.50, "onboardingFriction": 0.52},
            {"accessibilityGap": 0.52, "inclusionSignal": 0.56},
            {"epistemicLegibility": 0.50, "prestigeMystiqueRisk": 0.82, "exclusionPressure": 0.54},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, barrier, accessibility, legibility, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "commons", **row},
            barrier_rows={target_id: barrier},
            accessibility_rows={target_id: accessibility},
            legibility_rows={target_id: legibility},
            system_risk=0.35,
        )
        statuses.add(decision.participation_status)
        assert decision.participation_status == expected

    assert statuses == {
        "commons-open",
        "literacy-repair",
        "accessibility-risk",
        "priesthood-risk",
        "require-human-review",
    }


def test_bounded_non_exclusionary_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "commons", "literacyDepth": 0.60, "translationReadiness": 0.58},
        barrier_rows={"tone": {"participationBarrier": 0.50, "onboardingFriction": 0.52}},
        accessibility_rows={"tone": {"accessibilityGap": 0.50, "inclusionSignal": 0.58}},
        legibility_rows={"tone": {"epistemicLegibility": 0.58, "prestigeMystiqueRisk": 0.46, "exclusionPressure": 0.42}},
        system_risk=0.35,
    )

    text = " ".join(
        [
            decision.literacy_context,
            decision.participation_context,
            decision.accessibility_context,
            decision.legibility_context,
            decision.explanation,
        ]
    ).lower()
    assert "bounded" in text
    assert "participation support" in text
    assert "gatekeeping" in text
    assert "exclude persons" not in text


def test_anti_priesthood_and_accessibility_handling() -> None:
    priest = module.evaluate_target(
        {"targetId": "priest", "targetType": "commons", "literacyDepth": 0.56, "translationReadiness": 0.56},
        barrier_rows={"priest": {"participationBarrier": 0.50, "onboardingFriction": 0.52}},
        accessibility_rows={"priest": {"accessibilityGap": 0.52, "inclusionSignal": 0.56}},
        legibility_rows={"priest": {"epistemicLegibility": 0.50, "prestigeMystiqueRisk": 0.82, "exclusionPressure": 0.54}},
        system_risk=0.35,
    )
    access = module.evaluate_target(
        {"targetId": "access", "targetType": "commons", "literacyDepth": 0.56, "translationReadiness": 0.56},
        barrier_rows={"access": {"participationBarrier": 0.52, "onboardingFriction": 0.54}},
        accessibility_rows={"access": {"accessibilityGap": 0.74, "inclusionSignal": 0.30}},
        legibility_rows={"access": {"epistemicLegibility": 0.58, "prestigeMystiqueRisk": 0.42, "exclusionPressure": 0.40}},
        system_risk=0.35,
    )

    assert priest.participation_status == "require-human-review"
    assert access.participation_status == "accessibility-risk"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad_map = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "commons"}]})
    _write_json(tmp_path / "bridge/civic_literacy_map.json", bad_map)

    with pytest.raises(module.CommonsParticipationInputError):
        module.build_outputs()
