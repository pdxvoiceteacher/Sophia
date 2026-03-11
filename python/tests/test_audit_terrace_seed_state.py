from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_terrace_seed_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "terrace_seed_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.terrace_seed.fixture",
        "producerCommit": "fixture-bl-0001",
        "generatedAt": "2026-12-15T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-12-15T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "terrace-seed->repluralization->overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No governance transfer or centralized succession.",
        "commonsIntegrityNotice": "Terrace pathways remain plural, trust-stable, and memory-bearing.",
        "constraintSignatureVersion": "bl-1",
        "constraintSignatureSha256": "sha256:1515",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "TERRACE_SEED_MAP_PATH", tmp_path / "bridge/terrace_seed_map.json")
    monkeypatch.setattr(module, "EXPERIMENTAL_REPLURALIZATION_REPORT_PATH", tmp_path / "bridge/experimental_repluralization_report.json")
    monkeypatch.setattr(module, "SEDIMENTATION_READINESS_SCORECARD_PATH", tmp_path / "bridge/sedimentation_readiness_scorecard.json")
    monkeypatch.setattr(module, "TERRACE_SEED_GATE_PATH", tmp_path / "bridge/terrace_seed_gate.json")
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
    monkeypatch.setattr(module, "TERRACE_SEED_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/terrace_seed_audit_v1.schema.json"))
    monkeypatch.setattr(module, "TERRACE_SEED_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/terrace_seed_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(
        b / "terrace_seed_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "future", "terraceSeedReadinessScore": 0.74, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68},
                    {"targetId": "target:a", "targetType": "future", "terraceSeedReadinessScore": 0.72, "pluralityDurabilityScore": 0.69, "trustStabilityScore": 0.67},
                ]
            }
        ),
    )
    _write_json(
        b / "experimental_repluralization_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "stabilizationHealthScore": 0.62, "experimentationRecoveryScore": 0.62, "scatteringPressureScore": 0.52},
                    {"targetId": "target:a", "stabilizationHealthScore": 0.62, "experimentationRecoveryScore": 0.62, "scatteringPressureScore": 0.52},
                ]
            }
        ),
    )
    _write_json(
        b / "sedimentation_readiness_scorecard.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "commonsTransmissionScore": 0.62, "memoryWeaveScore": 0.62},
                    {"targetId": "target:a", "commonsTransmissionScore": 0.62, "memoryWeaveScore": 0.62},
                ]
            }
        ),
    )
    _write_json(
        b / "terrace_seed_gate.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "phaseCouplingScore": 0.68, "seedGovernanceCoherenceScore": 0.66},
                    {"targetId": "target:a", "phaseCouplingScore": 0.68, "seedGovernanceCoherenceScore": 0.66},
                ]
            }
        ),
    )

    for name in (
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
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/terrace_seed_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/terrace_seed_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_seed_status_coverage() -> None:
    cases = [
        ("seed", {"terraceSeedReadinessScore": 0.78, "pluralityDurabilityScore": 0.72, "trustStabilityScore": 0.70}, {"stabilizationHealthScore": 0.66, "experimentationRecoveryScore": 0.60, "scatteringPressureScore": 0.50}, {"commonsTransmissionScore": 0.72, "memoryWeaveScore": 0.70}, {"phaseCouplingScore": 0.68, "seedGovernanceCoherenceScore": 0.70}, 0.40, 0.44, "seed-visible"),
        ("legibility", {"terraceSeedReadinessScore": 0.74, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68}, {"stabilizationHealthScore": 0.64, "experimentationRecoveryScore": 0.60, "scatteringPressureScore": 0.52}, {"commonsTransmissionScore": 0.62, "memoryWeaveScore": 0.62}, {"phaseCouplingScore": 0.68, "seedGovernanceCoherenceScore": 0.66}, 0.40, 0.44, "strengthen-legibility"),
        ("plurality", {"terraceSeedReadinessScore": 0.76, "pluralityDurabilityScore": 0.58, "trustStabilityScore": 0.70}, {"stabilizationHealthScore": 0.66, "experimentationRecoveryScore": 0.60, "scatteringPressureScore": 0.50}, {"commonsTransmissionScore": 0.72, "memoryWeaveScore": 0.70}, {"phaseCouplingScore": 0.72, "seedGovernanceCoherenceScore": 0.70}, 0.40, 0.44, "plurality-protect"),
        ("replural", {"terraceSeedReadinessScore": 0.74, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68}, {"stabilizationHealthScore": 0.50, "experimentationRecoveryScore": 0.70, "scatteringPressureScore": 0.58}, {"commonsTransmissionScore": 0.70, "memoryWeaveScore": 0.68}, {"phaseCouplingScore": 0.68, "seedGovernanceCoherenceScore": 0.66}, 0.40, 0.44, "repluralization-visible"),
        ("watch", {"terraceSeedReadinessScore": 0.78, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68}, {"stabilizationHealthScore": 0.66, "experimentationRecoveryScore": 0.60, "scatteringPressureScore": 0.50}, {"commonsTransmissionScore": 0.62, "memoryWeaveScore": 0.62}, {"phaseCouplingScore": 0.72, "seedGovernanceCoherenceScore": 0.70}, 0.58, 0.44, "phase-transition-watch"),
        ("review", {"terraceSeedReadinessScore": 0.64, "pluralityDurabilityScore": 0.66, "trustStabilityScore": 0.64}, {"stabilizationHealthScore": 0.62, "experimentationRecoveryScore": 0.60, "scatteringPressureScore": 0.58}, {"commonsTransmissionScore": 0.66, "memoryWeaveScore": 0.66}, {"phaseCouplingScore": 0.64, "seedGovernanceCoherenceScore": 0.64}, 0.42, 0.44, "require-human-review"),
    ]
    got = set()
    for tid, row, replural_row, sediment_row, gate_row, support_risk, trust_risk, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "future", **row},
            repluralization_rows={tid: replural_row},
            sediment_rows={tid: sediment_row},
            gate_rows={tid: gate_row},
            support_risk=support_risk,
            trust_surface_risk=trust_risk,
        )
        got.add(d.seed_status)
        assert d.seed_status == expected
    assert got == {"seed-visible", "strengthen-legibility", "plurality-protect", "repluralization-visible", "phase-transition-watch", "require-human-review"}


def test_bounded_non_sovereign_language() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "future", "terraceSeedReadinessScore": 0.78, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.70},
        repluralization_rows={"tone": {"stabilizationHealthScore": 0.66, "experimentationRecoveryScore": 0.60, "scatteringPressureScore": 0.50}},
        sediment_rows={"tone": {"commonsTransmissionScore": 0.72, "memoryWeaveScore": 0.70}},
        gate_rows={"tone": {"phaseCouplingScore": 0.68, "seedGovernanceCoherenceScore": 0.70}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    t = " ".join([d.seed_context, d.plurality_context, d.repluralization_context, d.trust_context, d.commons_context, d.explanation]).lower()
    assert "bounded terrace-seed guidance" in t
    assert "non-coercive" in t
    assert "new epoch formed" not in t
    assert "successor order settled" not in t
    assert "history stabilized" not in t


def test_behavior_paths() -> None:
    strengthen = module.evaluate_target(
        {"targetId": "legibility", "targetType": "future", "terraceSeedReadinessScore": 0.74, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68},
        repluralization_rows={"legibility": {"stabilizationHealthScore": 0.64, "experimentationRecoveryScore": 0.60, "scatteringPressureScore": 0.52}},
        sediment_rows={"legibility": {"commonsTransmissionScore": 0.62, "memoryWeaveScore": 0.62}},
        gate_rows={"legibility": {"phaseCouplingScore": 0.68, "seedGovernanceCoherenceScore": 0.66}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    plurality = module.evaluate_target(
        {"targetId": "plurality", "targetType": "future", "terraceSeedReadinessScore": 0.76, "pluralityDurabilityScore": 0.58, "trustStabilityScore": 0.70},
        repluralization_rows={"plurality": {"stabilizationHealthScore": 0.66, "experimentationRecoveryScore": 0.60, "scatteringPressureScore": 0.50}},
        sediment_rows={"plurality": {"commonsTransmissionScore": 0.72, "memoryWeaveScore": 0.70}},
        gate_rows={"plurality": {"phaseCouplingScore": 0.72, "seedGovernanceCoherenceScore": 0.70}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    replural = module.evaluate_target(
        {"targetId": "replural", "targetType": "future", "terraceSeedReadinessScore": 0.74, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68},
        repluralization_rows={"replural": {"stabilizationHealthScore": 0.50, "experimentationRecoveryScore": 0.70, "scatteringPressureScore": 0.58}},
        sediment_rows={"replural": {"commonsTransmissionScore": 0.70, "memoryWeaveScore": 0.68}},
        gate_rows={"replural": {"phaseCouplingScore": 0.68, "seedGovernanceCoherenceScore": 0.66}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    watch = module.evaluate_target(
        {"targetId": "watch", "targetType": "future", "terraceSeedReadinessScore": 0.78, "pluralityDurabilityScore": 0.70, "trustStabilityScore": 0.68},
        repluralization_rows={"watch": {"stabilizationHealthScore": 0.66, "experimentationRecoveryScore": 0.60, "scatteringPressureScore": 0.50}},
        sediment_rows={"watch": {"commonsTransmissionScore": 0.62, "memoryWeaveScore": 0.62}},
        gate_rows={"watch": {"phaseCouplingScore": 0.72, "seedGovernanceCoherenceScore": 0.70}},
        support_risk=0.58,
        trust_surface_risk=0.44,
    )
    assert strengthen.seed_status == "strengthen-legibility"
    assert plurality.seed_status == "plurality-protect"
    assert replural.seed_status == "repluralization-visible"
    assert replural.target_publisher_action in {"watch", "suppress"}
    assert watch.seed_status == "phase-transition-watch"


def test_fail_closed_provenance_and_canonical_name(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/terrace_seed_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.TerraceSeedInputError):
        module.build_outputs()

    monkeypatch.setattr(module, "TERRACE_SEED_MAP_PATH", tmp_path / "bridge/non_canonical_name.json")
    _write_json(tmp_path / "bridge/non_canonical_name.json", _artifact({"targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.TerraceSeedInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/terrace_seed_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    _write_json(tmp_path / "bridge/experimental_repluralization_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
