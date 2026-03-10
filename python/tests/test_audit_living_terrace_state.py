from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_living_terrace_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "living_terrace_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.living_terrace.fixture",
        "producerCommit": "fixture-bn-0001",
        "generatedAt": "2026-12-24T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-12-24T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "living-terrace->commons-habitability->overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No governance transfer or centralized succession.",
        "commonsIntegrityNotice": "Living terraces remain plural, habitable, and trust-ordinary.",
        "constraintSignatureVersion": "bn-1",
        "constraintSignatureSha256": "sha256:2424",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "LIVING_TERRACE_MAP_PATH", tmp_path / "bridge/living_terrace_map.json")
    monkeypatch.setattr(module, "COMMONS_HABITABILITY_REPORT_PATH", tmp_path / "bridge/commons_habitability_report.json")
    monkeypatch.setattr(module, "PLURAL_HABITATION_REGISTRY_PATH", tmp_path / "bridge/plural_habitation_registry.json")
    monkeypatch.setattr(module, "TERRACE_CONSOLIDATION_GATE_PATH", tmp_path / "bridge/terrace_consolidation_gate.json")
    monkeypatch.setattr(module, "EPOCHAL_SURFACE_AUDIT_PATH", tmp_path / "bridge/epochal_surface_audit.json")
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
    monkeypatch.setattr(module, "LIVING_TERRACE_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/living_terrace_audit_v1.schema.json"))
    monkeypatch.setattr(module, "LIVING_TERRACE_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/living_terrace_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(
        b / "living_terrace_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "future", "livingTerraceReadinessScore": 0.74, "pluralityMetabolizationScore": 0.70, "trustOrdinarinessScore": 0.68},
                    {"targetId": "target:a", "targetType": "future", "livingTerraceReadinessScore": 0.72, "pluralityMetabolizationScore": 0.69, "trustOrdinarinessScore": 0.67},
                ]
            }
        ),
    )
    _write_json(
        b / "commons_habitability_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "commonsHabitabilityScore": 0.64, "ordinaryStewardshipScore": 0.62, "memoryContinuityScore": 0.62},
                    {"targetId": "target:a", "commonsHabitabilityScore": 0.64, "ordinaryStewardshipScore": 0.62, "memoryContinuityScore": 0.62},
                ]
            }
        ),
    )
    _write_json(
        b / "plural_habitation_registry.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.62},
                    {"targetId": "target:a", "pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.62},
                ]
            }
        ),
    )
    _write_json(
        b / "terrace_consolidation_gate.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "terraceConsolidationScore": 0.68, "governanceCoherenceScore": 0.66},
                    {"targetId": "target:a", "terraceConsolidationScore": 0.68, "governanceCoherenceScore": 0.66},
                ]
            }
        ),
    )

    for name in (
        "epochal_surface_audit.json",
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
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/living_terrace_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/living_terrace_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_terrace_status_coverage() -> None:
    cases = [
        ("terrace", {"livingTerraceReadinessScore": 0.78, "pluralityMetabolizationScore": 0.72, "trustOrdinarinessScore": 0.70}, {"commonsHabitabilityScore": 0.72, "ordinaryStewardshipScore": 0.70, "memoryContinuityScore": 0.70}, {"pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.70}, {"terraceConsolidationScore": 0.68, "governanceCoherenceScore": 0.70}, 0.40, 0.44, "terrace-visible"),
        ("habit", {"livingTerraceReadinessScore": 0.74, "pluralityMetabolizationScore": 0.70, "trustOrdinarinessScore": 0.68}, {"commonsHabitabilityScore": 0.64, "ordinaryStewardshipScore": 0.62, "memoryContinuityScore": 0.62}, {"pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.62}, {"terraceConsolidationScore": 0.68, "governanceCoherenceScore": 0.66}, 0.40, 0.44, "strengthen-habitability"),
        ("plurality", {"livingTerraceReadinessScore": 0.76, "pluralityMetabolizationScore": 0.58, "trustOrdinarinessScore": 0.70}, {"commonsHabitabilityScore": 0.72, "ordinaryStewardshipScore": 0.70, "memoryContinuityScore": 0.70}, {"pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.70}, {"terraceConsolidationScore": 0.72, "governanceCoherenceScore": 0.70}, 0.40, 0.44, "plurality-protect"),
        ("open", {"livingTerraceReadinessScore": 0.74, "pluralityMetabolizationScore": 0.70, "trustOrdinarinessScore": 0.68}, {"commonsHabitabilityScore": 0.70, "ordinaryStewardshipScore": 0.68, "memoryContinuityScore": 0.68}, {"pluralHabitationHealthScore": 0.70, "settlementDeservednessScore": 0.50}, {"terraceConsolidationScore": 0.68, "governanceCoherenceScore": 0.66}, 0.40, 0.44, "keep-open"),
        ("watch", {"livingTerraceReadinessScore": 0.78, "pluralityMetabolizationScore": 0.70, "trustOrdinarinessScore": 0.68}, {"commonsHabitabilityScore": 0.64, "ordinaryStewardshipScore": 0.62, "memoryContinuityScore": 0.62}, {"pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.62}, {"terraceConsolidationScore": 0.72, "governanceCoherenceScore": 0.70}, 0.58, 0.44, "phase-transition-watch"),
        ("review", {"livingTerraceReadinessScore": 0.64, "pluralityMetabolizationScore": 0.66, "trustOrdinarinessScore": 0.64}, {"commonsHabitabilityScore": 0.66, "ordinaryStewardshipScore": 0.66, "memoryContinuityScore": 0.66}, {"pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.62}, {"terraceConsolidationScore": 0.64, "governanceCoherenceScore": 0.64}, 0.42, 0.44, "require-human-review"),
    ]
    got = set()
    for tid, row, habitability_row, habitation_row, gate_row, support_risk, trust_risk, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "future", **row},
            habitability_rows={tid: habitability_row},
            habitation_rows={tid: habitation_row},
            gate_rows={tid: gate_row},
            support_risk=support_risk,
            trust_surface_risk=trust_risk,
        )
        got.add(d.terrace_status)
        assert d.terrace_status == expected
    assert got == {"terrace-visible", "strengthen-habitability", "plurality-protect", "keep-open", "phase-transition-watch", "require-human-review"}


def test_bounded_non_sovereign_language() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "future", "livingTerraceReadinessScore": 0.78, "pluralityMetabolizationScore": 0.70, "trustOrdinarinessScore": 0.70},
        habitability_rows={"tone": {"commonsHabitabilityScore": 0.72, "ordinaryStewardshipScore": 0.70, "memoryContinuityScore": 0.70}},
        habitation_rows={"tone": {"pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.70}},
        gate_rows={"tone": {"terraceConsolidationScore": 0.68, "governanceCoherenceScore": 0.70}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    t = " ".join([d.terrace_context, d.plurality_context, d.habitability_context, d.trust_context, d.commons_context, d.explanation]).lower()
    assert "bounded living-terrace guidance" in t
    assert "non-coercive" in t
    assert "new age settled" not in t
    assert "epoch complete" not in t
    assert "history resolved" not in t


def test_behavior_paths() -> None:
    strengthen = module.evaluate_target(
        {"targetId": "habit", "targetType": "future", "livingTerraceReadinessScore": 0.74, "pluralityMetabolizationScore": 0.70, "trustOrdinarinessScore": 0.68},
        habitability_rows={"habit": {"commonsHabitabilityScore": 0.64, "ordinaryStewardshipScore": 0.62, "memoryContinuityScore": 0.62}},
        habitation_rows={"habit": {"pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.62}},
        gate_rows={"habit": {"terraceConsolidationScore": 0.68, "governanceCoherenceScore": 0.66}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    plurality = module.evaluate_target(
        {"targetId": "plurality", "targetType": "future", "livingTerraceReadinessScore": 0.76, "pluralityMetabolizationScore": 0.58, "trustOrdinarinessScore": 0.70},
        habitability_rows={"plurality": {"commonsHabitabilityScore": 0.72, "ordinaryStewardshipScore": 0.70, "memoryContinuityScore": 0.70}},
        habitation_rows={"plurality": {"pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.70}},
        gate_rows={"plurality": {"terraceConsolidationScore": 0.72, "governanceCoherenceScore": 0.70}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    keep_open = module.evaluate_target(
        {"targetId": "open", "targetType": "future", "livingTerraceReadinessScore": 0.74, "pluralityMetabolizationScore": 0.70, "trustOrdinarinessScore": 0.68},
        habitability_rows={"open": {"commonsHabitabilityScore": 0.70, "ordinaryStewardshipScore": 0.68, "memoryContinuityScore": 0.68}},
        habitation_rows={"open": {"pluralHabitationHealthScore": 0.70, "settlementDeservednessScore": 0.50}},
        gate_rows={"open": {"terraceConsolidationScore": 0.68, "governanceCoherenceScore": 0.66}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    watch = module.evaluate_target(
        {"targetId": "watch", "targetType": "future", "livingTerraceReadinessScore": 0.78, "pluralityMetabolizationScore": 0.70, "trustOrdinarinessScore": 0.68},
        habitability_rows={"watch": {"commonsHabitabilityScore": 0.64, "ordinaryStewardshipScore": 0.62, "memoryContinuityScore": 0.62}},
        habitation_rows={"watch": {"pluralHabitationHealthScore": 0.62, "settlementDeservednessScore": 0.62}},
        gate_rows={"watch": {"terraceConsolidationScore": 0.72, "governanceCoherenceScore": 0.70}},
        support_risk=0.58,
        trust_surface_risk=0.44,
    )
    assert strengthen.terrace_status == "strengthen-habitability"
    assert plurality.terrace_status == "plurality-protect"
    assert keep_open.terrace_status == "keep-open"
    assert keep_open.target_publisher_action in {"watch", "suppress"}
    assert watch.terrace_status == "phase-transition-watch"


def test_fail_closed_provenance_and_canonical_name(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/living_terrace_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.LivingTerraceInputError):
        module.build_outputs()

    monkeypatch.setattr(module, "LIVING_TERRACE_MAP_PATH", tmp_path / "bridge/non_canonical_name.json")
    _write_json(tmp_path / "bridge/non_canonical_name.json", _artifact({"targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.LivingTerraceInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/living_terrace_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    _write_json(tmp_path / "bridge/commons_habitability_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
