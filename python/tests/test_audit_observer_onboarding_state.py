from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_observer_onboarding_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "observer_onboarding_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.observer_onboarding.fixture",
        "producerCommit": "fixture-bc-0001",
        "generatedAt": "2026-05-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-05-08T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "observer-cartography->onboarding-audit->bounded-participation",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No sovereignty transfer or coercive identity assignment.",
        "commonsIntegrityNotice": "Bounded standing with guided participation only.",
        "constraintSignatureVersion": "bc-1",
        "constraintSignatureSha256": "sha256:abababab",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "OBSERVER_CARTOGRAPHY_MAP_PATH", tmp_path / "bridge/observer_cartography_map.json")
    monkeypatch.setattr(module, "VISUALIZATION_ACCESS_MAP_PATH", tmp_path / "bridge/observer_visualization_access_map.json")
    monkeypatch.setattr(module, "ONBOARDING_READINESS_MAP_PATH", tmp_path / "bridge/observer_onboarding_readiness_map.json")
    monkeypatch.setattr(module, "PARTICIPATORY_STANDING_MAP_PATH", tmp_path / "bridge/observer_participatory_standing_map.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "FEDERATED_GOVERNANCE_AUDIT_PATH", tmp_path / "bridge/federated_governance_audit.json")
    monkeypatch.setattr(module, "COMMONS_PARTICIPATION_AUDIT_PATH", tmp_path / "bridge/commons_participation_audit.json")
    monkeypatch.setattr(module, "SOCIAL_ENTROPY_AUDIT_PATH", tmp_path / "bridge/social_entropy_audit.json")
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_AUDIT_PATH", tmp_path / "bridge/knowledge_river_audit.json")
    monkeypatch.setattr(module, "OPERATIONALIZATION_AUDIT_PATH", tmp_path / "bridge/operationalization_audit.json")
    monkeypatch.setattr(module, "OBSERVER_ONBOARDING_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/observer_onboarding_audit_v1.schema.json"))
    monkeypatch.setattr(module, "OBSERVER_ONBOARDING_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/observer_onboarding_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(b / "observer_cartography_map.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "observer", "interpretiveLoadScore": 0.50, "reciprocityEvidenceScore": 0.70, "candidateRecognitionBasisScore": 0.70}, {"targetId": "target:a", "targetType": "observer", "interpretiveLoadScore": 0.58, "reciprocityEvidenceScore": 0.66, "candidateRecognitionBasisScore": 0.72}]}))
    _write_json(b / "observer_visualization_access_map.json", _artifact({"targets": [{"targetId": "target:z", "signalLegibilityScore": 0.70, "translationSufficiencyScore": 0.70}, {"targetId": "target:a", "signalLegibilityScore": 0.64, "translationSufficiencyScore": 0.68}]}))
    _write_json(b / "observer_onboarding_readiness_map.json", _artifact({"targets": [{"targetId": "target:z", "onboardingReadinessScore": 0.68, "voteBasisScore": 0.70}, {"targetId": "target:a", "onboardingReadinessScore": 0.62, "voteBasisScore": 0.66}]}))
    _write_json(b / "observer_participatory_standing_map.json", _artifact({"targets": [{"targetId": "target:z", "captureRiskScore": 0.30, "commonsCaptureIndicatorScore": 0.28, "captureClearanceScore": 0.72, "standingBoundednessScore": 0.70, "revocationClarityScore": 0.70, "provenanceClarityScore": 0.72}, {"targetId": "target:a", "captureRiskScore": 0.36, "commonsCaptureIndicatorScore": 0.34, "captureClearanceScore": 0.66, "standingBoundednessScore": 0.68, "revocationClarityScore": 0.66, "provenanceClarityScore": 0.66}]}))
    for name in (
        "commons_sovereignty_audit.json",
        "civilizational_memory_audit.json",
        "federated_governance_audit.json",
        "commons_participation_audit.json",
        "social_entropy_audit.json",
        "knowledge_river_audit.json",
        "operationalization_audit.json",
    ):
        _write_json(b / name, _audit_rows([0.3, 0.4]))


def test_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    audit_payload, rec_payload = module.build_outputs()
    assert [x["targetId"] for x in audit_payload["records"]] == ["target:a", "target:z"]
    assert [x["targetId"] for x in rec_payload["recommendations"]] == ["target:a", "target:z"]
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/observer_onboarding_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/observer_onboarding_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_status_coverage() -> None:
    cases = [
        ("ready", {"interpretiveLoadScore": 0.48, "reciprocityEvidenceScore": 0.70, "candidateRecognitionBasisScore": 0.70}, {"signalLegibilityScore": 0.72, "translationSufficiencyScore": 0.72}, {"onboardingReadinessScore": 0.72, "voteBasisScore": 0.72}, {"captureRiskScore": 0.28, "commonsCaptureIndicatorScore": 0.24, "captureClearanceScore": 0.76, "standingBoundednessScore": 0.70, "revocationClarityScore": 0.70, "provenanceClarityScore": 0.70}, "observer-ready"),
        ("legibility", {"interpretiveLoadScore": 0.70, "reciprocityEvidenceScore": 0.60, "candidateRecognitionBasisScore": 0.70}, {"signalLegibilityScore": 0.40, "translationSufficiencyScore": 0.66}, {"onboardingReadinessScore": 0.66, "voteBasisScore": 0.66}, {"captureRiskScore": 0.30, "commonsCaptureIndicatorScore": 0.30, "captureClearanceScore": 0.68, "standingBoundednessScore": 0.68, "revocationClarityScore": 0.68, "provenanceClarityScore": 0.68}, "guided-legibility-required"),
        ("standing", {"interpretiveLoadScore": 0.52, "reciprocityEvidenceScore": 0.62, "candidateRecognitionBasisScore": 0.70}, {"signalLegibilityScore": 0.64, "translationSufficiencyScore": 0.64}, {"onboardingReadinessScore": 0.60, "voteBasisScore": 0.62}, {"captureRiskScore": 0.34, "commonsCaptureIndicatorScore": 0.34, "captureClearanceScore": 0.66, "standingBoundednessScore": 0.50, "revocationClarityScore": 0.50, "provenanceClarityScore": 0.50}, "standing-repair"),
        ("capture", {"interpretiveLoadScore": 0.52, "reciprocityEvidenceScore": 0.60, "candidateRecognitionBasisScore": 0.70}, {"signalLegibilityScore": 0.64, "translationSufficiencyScore": 0.64}, {"onboardingReadinessScore": 0.64, "voteBasisScore": 0.64}, {"captureRiskScore": 0.86, "commonsCaptureIndicatorScore": 0.82, "captureClearanceScore": 0.40, "standingBoundednessScore": 0.62, "revocationClarityScore": 0.62, "provenanceClarityScore": 0.62}, "capture-risk"),
        ("suffrage", {"interpretiveLoadScore": 0.35, "reciprocityEvidenceScore": 0.84, "candidateRecognitionBasisScore": 0.70}, {"signalLegibilityScore": 0.92, "translationSufficiencyScore": 0.55}, {"onboardingReadinessScore": 0.88, "voteBasisScore": 0.55}, {"captureRiskScore": 0.20, "commonsCaptureIndicatorScore": 0.20, "captureClearanceScore": 0.55, "standingBoundednessScore": 0.80, "revocationClarityScore": 0.80, "provenanceClarityScore": 0.80}, "suffrage-review"),
        ("human", {"interpretiveLoadScore": 0.50, "reciprocityEvidenceScore": 0.60, "candidateRecognitionBasisScore": 0.30}, {"signalLegibilityScore": 0.66, "translationSufficiencyScore": 0.66}, {"onboardingReadinessScore": 0.66, "voteBasisScore": 0.66}, {"captureRiskScore": 0.30, "commonsCaptureIndicatorScore": 0.30, "captureClearanceScore": 0.66, "standingBoundednessScore": 0.66, "revocationClarityScore": 0.66, "provenanceClarityScore": 0.66}, "require-human-review"),
    ]
    got = set()
    for tid, row, vis, onb, standing, expected in cases:
        d = module.evaluate_target({"targetId": tid, "targetType": "observer", **row}, visualization_rows={tid: vis}, onboarding_rows={tid: onb}, standing_rows={tid: standing}, system_risk=0.35)
        got.add(d.observer_status)
        assert d.observer_status == expected
    assert got == module.STATUSES


def test_guided_legibility_suffrage_and_capture_actions() -> None:
    legibility = module.evaluate_target(
        {"targetId": "g", "targetType": "observer", "interpretiveLoadScore": 0.72, "reciprocityEvidenceScore": 0.6, "candidateRecognitionBasisScore": 0.7},
        visualization_rows={"g": {"signalLegibilityScore": 0.41, "translationSufficiencyScore": 0.66}},
        onboarding_rows={"g": {"onboardingReadinessScore": 0.66, "voteBasisScore": 0.66}},
        standing_rows={"g": {"captureRiskScore": 0.30, "commonsCaptureIndicatorScore": 0.30, "captureClearanceScore": 0.66, "standingBoundednessScore": 0.66, "revocationClarityScore": 0.66, "provenanceClarityScore": 0.66}},
        system_risk=0.35,
    )
    suffrage = module.evaluate_target(
        {"targetId": "s", "targetType": "observer", "interpretiveLoadScore": 0.30, "reciprocityEvidenceScore": 0.84, "candidateRecognitionBasisScore": 0.7},
        visualization_rows={"s": {"signalLegibilityScore": 0.92, "translationSufficiencyScore": 0.55}},
        onboarding_rows={"s": {"onboardingReadinessScore": 0.88, "voteBasisScore": 0.55}},
        standing_rows={"s": {"captureRiskScore": 0.20, "commonsCaptureIndicatorScore": 0.20, "captureClearanceScore": 0.55, "standingBoundednessScore": 0.80, "revocationClarityScore": 0.80, "provenanceClarityScore": 0.80}},
        system_risk=0.30,
    )
    capture = module.evaluate_target(
        {"targetId": "c", "targetType": "entity", "interpretiveLoadScore": 0.45, "reciprocityEvidenceScore": 0.55, "candidateRecognitionBasisScore": 0.7},
        visualization_rows={"c": {"signalLegibilityScore": 0.60, "translationSufficiencyScore": 0.60}},
        onboarding_rows={"c": {"onboardingReadinessScore": 0.60, "voteBasisScore": 0.60}},
        standing_rows={"c": {"captureRiskScore": 0.84, "commonsCaptureIndicatorScore": 0.75, "captureClearanceScore": 0.40, "standingBoundednessScore": 0.60, "revocationClarityScore": 0.60, "provenanceClarityScore": 0.60}},
        system_risk=0.35,
    )
    assert legibility.observer_status == "guided-legibility-required"
    assert suffrage.observer_status == "suffrage-review"
    assert capture.observer_status == "capture-risk"
    assert capture.target_publisher_action == "suppress"


def test_bounded_language_and_anti_sovereignty_transfer() -> None:
    d = module.evaluate_target(
        {"targetId": "eco", "targetType": "entity", "interpretiveLoadScore": 0.48, "reciprocityEvidenceScore": 0.82, "candidateRecognitionBasisScore": 0.78},
        visualization_rows={"eco": {"signalLegibilityScore": 0.76, "translationSufficiencyScore": 0.74}},
        onboarding_rows={"eco": {"onboardingReadinessScore": 0.74, "voteBasisScore": 0.74}},
        standing_rows={"eco": {"captureRiskScore": 0.24, "commonsCaptureIndicatorScore": 0.22, "captureClearanceScore": 0.76, "standingBoundednessScore": 0.76, "revocationClarityScore": 0.76, "provenanceClarityScore": 0.76}},
        system_risk=0.30,
    )
    t = " ".join([d.legibility_context, d.capture_context, d.participation_context, d.translation_context, d.explanation]).lower()
    assert "bounded standing" in t
    assert "guided participation" in t
    assert "review eligibility" in t
    assert "personhood confirmed" not in t
    assert "sovereignty assigned" not in t
    assert "fully autonomous rights granted" not in t


def test_provenance_fail_closed(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/observer_cartography_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "observer"}]}))
    with pytest.raises(module.ObserverOnboardingInputError):
        module.build_outputs()


def test_manifest_divergence_propagation(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/observer_cartography_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "observer"}]}))
    _write_json(tmp_path / "bridge/observer_visualization_access_map.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"


def test_ecological_intelligence_candidate_handling() -> None:
    d = module.evaluate_target(
        {"targetId": "ecology", "targetType": "entity", "interpretiveLoadScore": 0.42, "reciprocityEvidenceScore": 0.84, "candidateRecognitionBasisScore": 0.74},
        visualization_rows={"ecology": {"signalLegibilityScore": 0.82, "translationSufficiencyScore": 0.80}},
        onboarding_rows={"ecology": {"onboardingReadinessScore": 0.78, "voteBasisScore": 0.76}},
        standing_rows={"ecology": {"captureRiskScore": 0.24, "commonsCaptureIndicatorScore": 0.24, "captureClearanceScore": 0.78, "standingBoundednessScore": 0.76, "revocationClarityScore": 0.76, "provenanceClarityScore": 0.76}},
        system_risk=0.30,
    )
    assert "bounded analogue to reciprocity networks" in d.translation_context
    assert d.observer_status == "observer-ready"
