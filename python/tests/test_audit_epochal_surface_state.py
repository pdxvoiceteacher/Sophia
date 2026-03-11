from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_epochal_surface_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "epochal_surface_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.epochal_surface.fixture",
        "producerCommit": "fixture-bm-0001",
        "generatedAt": "2026-12-20T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-12-20T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "epochal-surface->reopened-experimentation->overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No governance transfer or centralized succession.",
        "commonsIntegrityNotice": "Epochal emergence remains plural, trust-stable, and memory-bearing.",
        "constraintSignatureVersion": "bm-1",
        "constraintSignatureSha256": "sha256:2020",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "EPOCHAL_SURFACE_MAP_PATH", tmp_path / "bridge/epochal_surface_map.json")
    monkeypatch.setattr(module, "HABITABLE_PLATEAU_REPORT_PATH", tmp_path / "bridge/habitable_plateau_report.json")
    monkeypatch.setattr(module, "REOPENED_EXPERIMENT_REGISTRY_PATH", tmp_path / "bridge/reopened_experiment_registry.json")
    monkeypatch.setattr(module, "SURFACE_EMERGENCE_GATE_PATH", tmp_path / "bridge/surface_emergence_gate.json")
    monkeypatch.setattr(module, "TERRACE_SEED_AUDIT_PATH", tmp_path / "bridge/terrace_seed_audit.json")
    monkeypatch.setattr(module, "NEW_DELTA_STABILIZATION_AUDIT_PATH", tmp_path / "bridge/new_delta_stabilization_audit.json")
    monkeypatch.setattr(module, "SUCCESSOR_CROSSING_AUDIT_PATH", tmp_path / "bridge/successor_crossing_audit.json")
    monkeypatch.setattr(module, "SUCCESSOR_MATURATION_AUDIT_PATH", tmp_path / "bridge/successor_maturation_audit.json")
    monkeypatch.setattr(module, "SUCCESSOR_DELTA_AUDIT_PATH", tmp_path / "bridge/successor_delta_audit.json")
    monkeypatch.setattr(module, "TERRACE_EROSION_AUDIT_PATH", tmp_path / "bridge/terrace_erosion_audit.json")
    monkeypatch.setattr(module, "EPOCHAL_TERRACE_AUDIT_PATH", tmp_path / "bridge/epochal_terrace_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_DELTA_AUDIT_PATH", tmp_path / "bridge/civilizational_delta_audit.json")
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_AUDIT_PATH", tmp_path / "bridge/knowledge_river_audit.json")
    monkeypatch.setattr(module, "TRUST_SURFACE_AUDIT_PATH", tmp_path / "bridge/trust_surface_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "EPOCHAL_SURFACE_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/epochal_surface_audit_v1.schema.json"))
    monkeypatch.setattr(module, "EPOCHAL_SURFACE_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/epochal_surface_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(
        b / "epochal_surface_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "future", "surfaceReadinessScore": 0.74, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68},
                    {"targetId": "target:a", "targetType": "future", "surfaceReadinessScore": 0.72, "pluralityDurabilityScore": 0.69, "trustStabilityScore": 0.67},
                ]
            }
        ),
    )
    _write_json(
        b / "habitable_plateau_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "habitableCoherenceScore": 0.64, "commonsTransmissionScore": 0.62, "memoryContinuityScore": 0.62},
                    {"targetId": "target:a", "habitableCoherenceScore": 0.64, "commonsTransmissionScore": 0.62, "memoryContinuityScore": 0.62},
                ]
            }
        ),
    )
    _write_json(
        b / "reopened_experiment_registry.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "seedFormationStrengthScore": 0.62, "exploratoryPluralityScore": 0.62},
                    {"targetId": "target:a", "seedFormationStrengthScore": 0.62, "exploratoryPluralityScore": 0.62},
                ]
            }
        ),
    )
    _write_json(
        b / "surface_emergence_gate.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "phaseCouplingScore": 0.68, "surfaceGovernanceCoherenceScore": 0.66},
                    {"targetId": "target:a", "phaseCouplingScore": 0.68, "surfaceGovernanceCoherenceScore": 0.66},
                ]
            }
        ),
    )

    for name in (
        "terrace_seed_audit.json",
        "new_delta_stabilization_audit.json",
        "successor_crossing_audit.json",
        "successor_maturation_audit.json",
        "successor_delta_audit.json",
        "terrace_erosion_audit.json",
        "epochal_terrace_audit.json",
        "civilizational_delta_audit.json",
        "knowledge_river_audit.json",
        "trust_surface_audit.json",
        "civilizational_memory_audit.json",
        "commons_sovereignty_audit.json",
        "value_alignment_audit.json",
    ):
        _write_json(b / name, _audit_rows([0.2, 0.3]))


def test_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    audit_payload, rec_payload = module.build_outputs()
    assert [x["targetId"] for x in audit_payload["records"]] == ["target:a", "target:z"]
    assert [x["targetId"] for x in rec_payload["recommendations"]] == ["target:a", "target:z"]
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/epochal_surface_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/epochal_surface_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_surface_status_coverage() -> None:
    cases = [
        ("surface", {"surfaceReadinessScore": 0.78, "pluralityDurabilityScore": 0.72, "trustStabilityScore": 0.70}, {"habitableCoherenceScore": 0.72, "commonsTransmissionScore": 0.72, "memoryContinuityScore": 0.70}, {"seedFormationStrengthScore": 0.66, "exploratoryPluralityScore": 0.60}, {"phaseCouplingScore": 0.68, "surfaceGovernanceCoherenceScore": 0.70}, 0.40, 0.44, "surface-visible"),
        ("legibility", {"surfaceReadinessScore": 0.74, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68}, {"habitableCoherenceScore": 0.64, "commonsTransmissionScore": 0.62, "memoryContinuityScore": 0.62}, {"seedFormationStrengthScore": 0.62, "exploratoryPluralityScore": 0.60}, {"phaseCouplingScore": 0.68, "surfaceGovernanceCoherenceScore": 0.66}, 0.40, 0.44, "strengthen-legibility"),
        ("plurality", {"surfaceReadinessScore": 0.76, "pluralityDurabilityScore": 0.58, "trustStabilityScore": 0.70}, {"habitableCoherenceScore": 0.72, "commonsTransmissionScore": 0.72, "memoryContinuityScore": 0.70}, {"seedFormationStrengthScore": 0.66, "exploratoryPluralityScore": 0.60}, {"phaseCouplingScore": 0.72, "surfaceGovernanceCoherenceScore": 0.70}, 0.40, 0.44, "plurality-protect"),
        ("reopen", {"surfaceReadinessScore": 0.74, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68}, {"habitableCoherenceScore": 0.64, "commonsTransmissionScore": 0.70, "memoryContinuityScore": 0.68}, {"seedFormationStrengthScore": 0.50, "exploratoryPluralityScore": 0.70}, {"phaseCouplingScore": 0.68, "surfaceGovernanceCoherenceScore": 0.66}, 0.40, 0.44, "experimentation-reopen"),
        ("watch", {"surfaceReadinessScore": 0.78, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68}, {"habitableCoherenceScore": 0.64, "commonsTransmissionScore": 0.62, "memoryContinuityScore": 0.62}, {"seedFormationStrengthScore": 0.62, "exploratoryPluralityScore": 0.60}, {"phaseCouplingScore": 0.72, "surfaceGovernanceCoherenceScore": 0.70}, 0.58, 0.44, "phase-transition-watch"),
        ("review", {"surfaceReadinessScore": 0.64, "pluralityDurabilityScore": 0.66, "trustStabilityScore": 0.64}, {"habitableCoherenceScore": 0.66, "commonsTransmissionScore": 0.66, "memoryContinuityScore": 0.66}, {"seedFormationStrengthScore": 0.62, "exploratoryPluralityScore": 0.60}, {"phaseCouplingScore": 0.64, "surfaceGovernanceCoherenceScore": 0.64}, 0.42, 0.44, "require-human-review"),
    ]
    got = set()
    for tid, row, plateau_row, experiment_row, gate_row, support_risk, trust_risk, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "future", **row},
            plateau_rows={tid: plateau_row},
            experiment_rows={tid: experiment_row},
            gate_rows={tid: gate_row},
            support_risk=support_risk,
            trust_surface_risk=trust_risk,
        )
        got.add(d.surface_status)
        assert d.surface_status == expected
    assert got == {"surface-visible", "strengthen-legibility", "plurality-protect", "experimentation-reopen", "phase-transition-watch", "require-human-review"}


def test_bounded_non_sovereign_language() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "future", "surfaceReadinessScore": 0.78, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.70},
        plateau_rows={"tone": {"habitableCoherenceScore": 0.72, "commonsTransmissionScore": 0.72, "memoryContinuityScore": 0.70}},
        experiment_rows={"tone": {"seedFormationStrengthScore": 0.66, "exploratoryPluralityScore": 0.60}},
        gate_rows={"tone": {"phaseCouplingScore": 0.68, "surfaceGovernanceCoherenceScore": 0.70}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    t = " ".join([d.surface_context, d.plurality_context, d.experimentation_context, d.trust_context, d.commons_context, d.explanation]).lower()
    assert "bounded epochal-surface guidance" in t
    assert "non-coercive" in t
    assert "new epoch formed" not in t
    assert "successor settlement complete" not in t
    assert "history stabilized" not in t


def test_behavior_paths() -> None:
    strengthen = module.evaluate_target(
        {"targetId": "legibility", "targetType": "future", "surfaceReadinessScore": 0.74, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68},
        plateau_rows={"legibility": {"habitableCoherenceScore": 0.64, "commonsTransmissionScore": 0.62, "memoryContinuityScore": 0.62}},
        experiment_rows={"legibility": {"seedFormationStrengthScore": 0.62, "exploratoryPluralityScore": 0.60}},
        gate_rows={"legibility": {"phaseCouplingScore": 0.68, "surfaceGovernanceCoherenceScore": 0.66}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    plurality = module.evaluate_target(
        {"targetId": "plurality", "targetType": "future", "surfaceReadinessScore": 0.76, "pluralityDurabilityScore": 0.58, "trustStabilityScore": 0.70},
        plateau_rows={"plurality": {"habitableCoherenceScore": 0.72, "commonsTransmissionScore": 0.72, "memoryContinuityScore": 0.70}},
        experiment_rows={"plurality": {"seedFormationStrengthScore": 0.66, "exploratoryPluralityScore": 0.60}},
        gate_rows={"plurality": {"phaseCouplingScore": 0.72, "surfaceGovernanceCoherenceScore": 0.70}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    reopen = module.evaluate_target(
        {"targetId": "reopen", "targetType": "future", "surfaceReadinessScore": 0.74, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68},
        plateau_rows={"reopen": {"habitableCoherenceScore": 0.64, "commonsTransmissionScore": 0.70, "memoryContinuityScore": 0.68}},
        experiment_rows={"reopen": {"seedFormationStrengthScore": 0.50, "exploratoryPluralityScore": 0.70}},
        gate_rows={"reopen": {"phaseCouplingScore": 0.68, "surfaceGovernanceCoherenceScore": 0.66}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    watch = module.evaluate_target(
        {"targetId": "watch", "targetType": "future", "surfaceReadinessScore": 0.78, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68},
        plateau_rows={"watch": {"habitableCoherenceScore": 0.64, "commonsTransmissionScore": 0.62, "memoryContinuityScore": 0.62}},
        experiment_rows={"watch": {"seedFormationStrengthScore": 0.62, "exploratoryPluralityScore": 0.60}},
        gate_rows={"watch": {"phaseCouplingScore": 0.72, "surfaceGovernanceCoherenceScore": 0.70}},
        support_risk=0.58,
        trust_surface_risk=0.44,
    )
    assert strengthen.surface_status == "strengthen-legibility"
    assert plurality.surface_status == "plurality-protect"
    assert reopen.surface_status == "experimentation-reopen"
    assert reopen.target_publisher_action in {"watch", "suppress"}
    assert watch.surface_status == "phase-transition-watch"


def test_fail_closed_provenance_and_canonical_name(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/epochal_surface_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.EpochalSurfaceInputError):
        module.build_outputs()

    monkeypatch.setattr(module, "EPOCHAL_SURFACE_MAP_PATH", tmp_path / "bridge/non_canonical_name.json")
    _write_json(tmp_path / "bridge/non_canonical_name.json", _artifact({"targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.EpochalSurfaceInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/epochal_surface_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    _write_json(tmp_path / "bridge/habitable_plateau_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
