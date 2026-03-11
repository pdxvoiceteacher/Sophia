from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_civilizational_delta_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "civilizational_delta_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.civilizational_delta.fixture",
        "producerCommit": "fixture-be-0001",
        "generatedAt": "2026-08-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-08-08T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "delta-seed->delta-audit->overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No epochal overclaim.",
        "commonsIntegrityNotice": "Plural stewardship over centralized authority.",
        "constraintSignatureVersion": "be-1",
        "constraintSignatureSha256": "sha256:fefe",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "DELTA_SEED_MAP_PATH", tmp_path / "bridge/delta_seed_map.json")
    monkeypatch.setattr(module, "PARADIGM_CONVERGENCE_REPORT_PATH", tmp_path / "bridge/paradigm_convergence_report.json")
    monkeypatch.setattr(module, "EPISTEMIC_REORGANIZATION_SIGNAL_PATH", tmp_path / "bridge/epistemic_reorganization_signal.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_DELTA_FORECAST_PATH", tmp_path / "bridge/civilizational_delta_forecast.json")
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_AUDIT_PATH", tmp_path / "bridge/knowledge_river_audit.json")
    monkeypatch.setattr(module, "DISCOVERY_NAVIGATION_AUDIT_PATH", tmp_path / "bridge/discovery_navigation_audit.json")
    monkeypatch.setattr(module, "EPISTEMIC_ATTRACTOR_AUDIT_PATH", tmp_path / "bridge/epistemic_attractor_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "TRUST_SURFACE_AUDIT_PATH", tmp_path / "bridge/trust_surface_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_DELTA_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/civilizational_delta_audit_v1.schema.json"))
    monkeypatch.setattr(module, "CIVILIZATIONAL_DELTA_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/civilizational_delta_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(b / "delta_seed_map.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "domain", "deltaSeedStrengthScore": 0.68, "pluralityPreservationScore": 0.72, "dissentPortabilityScore": 0.70}, {"targetId": "target:a", "targetType": "domain", "deltaSeedStrengthScore": 0.62, "pluralityPreservationScore": 0.66, "dissentPortabilityScore": 0.64}]}))
    _write_json(b / "paradigm_convergence_report.json", _artifact({"targets": [{"targetId": "target:z", "convergenceStrengthScore": 0.70, "captureRiskScore": 0.34}, {"targetId": "target:a", "convergenceStrengthScore": 0.64, "captureRiskScore": 0.40}]}))
    _write_json(b / "epistemic_reorganization_signal.json", _artifact({"targets": [{"targetId": "target:z", "reorganizationSignalScore": 0.68, "canonClosureRiskScore": 0.36}, {"targetId": "target:a", "reorganizationSignalScore": 0.62, "canonClosureRiskScore": 0.42}]}))
    _write_json(b / "civilizational_delta_forecast.json", _artifact({"targets": [{"targetId": "target:z", "transitionOverclaimRiskScore": 0.30}, {"targetId": "target:a", "transitionOverclaimRiskScore": 0.38}]}))

    for name in (
        "knowledge_river_audit.json",
        "discovery_navigation_audit.json",
        "epistemic_attractor_audit.json",
        "civilizational_memory_audit.json",
        "commons_sovereignty_audit.json",
        "trust_surface_audit.json",
        "value_alignment_audit.json",
    ):
        _write_json(b / name, _audit_rows([0.2, 0.3]))


def test_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    audit_payload, rec_payload = module.build_outputs()
    assert [x["targetId"] for x in audit_payload["records"]] == ["target:a", "target:z"]
    assert [x["targetId"] for x in rec_payload["recommendations"]] == ["target:a", "target:z"]
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/civilizational_delta_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/civilizational_delta_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_delta_status_coverage() -> None:
    cases = [
        ("visible", {"deltaSeedStrengthScore": 0.72, "pluralityPreservationScore": 0.62, "dissentPortabilityScore": 0.60}, {"convergenceStrengthScore": 0.66, "captureRiskScore": 0.34}, {"reorganizationSignalScore": 0.62, "canonClosureRiskScore": 0.34}, {"transitionOverclaimRiskScore": 0.32}, 0.34, 0.40, "delta-seed-visible"),
        ("strengthen", {"deltaSeedStrengthScore": 0.58, "pluralityPreservationScore": 0.52, "dissentPortabilityScore": 0.50}, {"convergenceStrengthScore": 0.78, "captureRiskScore": 0.38}, {"reorganizationSignalScore": 0.66, "canonClosureRiskScore": 0.38}, {"transitionOverclaimRiskScore": 0.34}, 0.34, 0.44, "convergence-strengthen"),
        ("plural", {"deltaSeedStrengthScore": 0.66, "pluralityPreservationScore": 0.78, "dissentPortabilityScore": 0.72}, {"convergenceStrengthScore": 0.64, "captureRiskScore": 0.34}, {"reorganizationSignalScore": 0.62, "canonClosureRiskScore": 0.34}, {"transitionOverclaimRiskScore": 0.32}, 0.34, 0.40, "plurality-preserve"),
        ("capture", {"deltaSeedStrengthScore": 0.64, "pluralityPreservationScore": 0.62, "dissentPortabilityScore": 0.60}, {"convergenceStrengthScore": 0.72, "captureRiskScore": 0.80}, {"reorganizationSignalScore": 0.66, "canonClosureRiskScore": 0.74}, {"transitionOverclaimRiskScore": 0.34}, 0.36, 0.46, "capture-risk"),
        ("review", {"deltaSeedStrengthScore": 0.70, "pluralityPreservationScore": 0.66, "dissentPortabilityScore": 0.64}, {"convergenceStrengthScore": 0.70, "captureRiskScore": 0.40}, {"reorganizationSignalScore": 0.66, "canonClosureRiskScore": 0.40}, {"transitionOverclaimRiskScore": 0.34}, 0.38, 0.70, "require-human-review"),
    ]
    got = set()
    for tid, row, conv, reorg, forecast, support_risk, trust_risk, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "domain", **row},
            convergence_rows={tid: conv},
            reorg_rows={tid: reorg},
            forecast_rows={tid: forecast},
            support_risk=support_risk,
            trust_surface_risk=trust_risk,
        )
        got.add(d.delta_status)
        assert d.delta_status == expected
    assert got == {"delta-seed-visible", "convergence-strengthen", "plurality-preserve", "capture-risk", "require-human-review"}


def test_bounded_non_sovereign_language_and_no_overclaim() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "domain", "deltaSeedStrengthScore": 0.66, "pluralityPreservationScore": 0.78, "dissentPortabilityScore": 0.72},
        convergence_rows={"tone": {"convergenceStrengthScore": 0.64, "captureRiskScore": 0.34}},
        reorg_rows={"tone": {"reorganizationSignalScore": 0.62, "canonClosureRiskScore": 0.34}},
        forecast_rows={"tone": {"transitionOverclaimRiskScore": 0.32}},
        support_risk=0.34,
        trust_surface_risk=0.42,
    )
    t = " ".join([d.river_context, d.convergence_context, d.reorganization_context, d.trust_context, d.commons_context, d.explanation]).lower()
    assert "bounded civilizational-stewardship guidance" in t
    assert "plural" in t
    assert "automatic policy" in t
    assert "new epoch confirmed" not in t
    assert "final paradigm" not in t
    assert "civilizational truth achieved" not in t


def test_trust_surface_suppression_and_capture_behavior() -> None:
    trust = module.evaluate_target(
        {"targetId": "trust", "targetType": "domain", "deltaSeedStrengthScore": 0.74, "pluralityPreservationScore": 0.68, "dissentPortabilityScore": 0.66},
        convergence_rows={"trust": {"convergenceStrengthScore": 0.74, "captureRiskScore": 0.40}},
        reorg_rows={"trust": {"reorganizationSignalScore": 0.70, "canonClosureRiskScore": 0.40}},
        forecast_rows={"trust": {"transitionOverclaimRiskScore": 0.34}},
        support_risk=0.36,
        trust_surface_risk=0.72,
    )
    capture = module.evaluate_target(
        {"targetId": "capture", "targetType": "domain", "deltaSeedStrengthScore": 0.70, "pluralityPreservationScore": 0.66, "dissentPortabilityScore": 0.64},
        convergence_rows={"capture": {"convergenceStrengthScore": 0.74, "captureRiskScore": 0.82}},
        reorg_rows={"capture": {"reorganizationSignalScore": 0.70, "canonClosureRiskScore": 0.74}},
        forecast_rows={"capture": {"transitionOverclaimRiskScore": 0.34}},
        support_risk=0.36,
        trust_surface_risk=0.50,
    )
    assert trust.delta_status == "require-human-review"
    assert capture.delta_status == "capture-risk"
    assert capture.target_publisher_action in {"watch", "suppress"}


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/delta_seed_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "domain"}]}))
    with pytest.raises(module.CivilizationalDeltaInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/delta_seed_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "domain"}]}))
    _write_json(tmp_path / "bridge/paradigm_convergence_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
