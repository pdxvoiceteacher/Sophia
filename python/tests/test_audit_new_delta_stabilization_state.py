from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_new_delta_stabilization_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "new_delta_stabilization_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.new_delta_stabilization.fixture",
        "producerCommit": "fixture-bk-0001",
        "generatedAt": "2026-12-12T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-12-12T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "new-delta-stabilization->fragmented-reversion->overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No governance transfer or centralized succession.",
        "commonsIntegrityNotice": "Post-crossing futures remain plural, trust-legible, and memory-bearing.",
        "constraintSignatureVersion": "bk-1",
        "constraintSignatureSha256": "sha256:1212",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "NEW_DELTA_STABILIZATION_MAP_PATH", tmp_path / "bridge/new_delta_stabilization_map.json")
    monkeypatch.setattr(module, "FRAGMENTED_RENEWAL_REVERSION_REPORT_PATH", tmp_path / "bridge/fragmented_renewal_reversion_report.json")
    monkeypatch.setattr(module, "CROSSING_RESILIENCE_SCORECARD_PATH", tmp_path / "bridge/crossing_resilience_scorecard.json")
    monkeypatch.setattr(module, "POST_CROSSING_GOVERNANCE_GATE_PATH", tmp_path / "bridge/post_crossing_governance_gate.json")
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
    monkeypatch.setattr(module, "NEW_DELTA_STABILIZATION_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/new_delta_stabilization_audit_v1.schema.json"))
    monkeypatch.setattr(module, "NEW_DELTA_STABILIZATION_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/new_delta_stabilization_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(
        b / "new_delta_stabilization_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "future", "stabilizationReadinessScore": 0.74, "pluralityRetentionScore": 0.70, "trustLegibilityScore": 0.68},
                    {"targetId": "target:a", "targetType": "future", "stabilizationReadinessScore": 0.72, "pluralityRetentionScore": 0.69, "trustLegibilityScore": 0.67},
                ]
            }
        ),
    )
    _write_json(
        b / "fragmented_renewal_reversion_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "trustRepairScore": 0.64, "memoryContinuityScore": 0.64, "renewalScatteringScore": 0.54},
                    {"targetId": "target:a", "trustRepairScore": 0.64, "memoryContinuityScore": 0.64, "renewalScatteringScore": 0.54},
                ]
            }
        ),
    )
    _write_json(
        b / "crossing_resilience_scorecard.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "resilienceDurabilityScore": 0.62, "institutionalRepairScore": 0.62},
                    {"targetId": "target:a", "resilienceDurabilityScore": 0.62, "institutionalRepairScore": 0.62},
                ]
            }
        ),
    )
    _write_json(
        b / "post_crossing_governance_gate.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "governanceCoherenceScore": 0.68, "transitionPressureScore": 0.54},
                    {"targetId": "target:a", "governanceCoherenceScore": 0.68, "transitionPressureScore": 0.54},
                ]
            }
        ),
    )

    for name in (
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
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/new_delta_stabilization_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/new_delta_stabilization_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_stabilization_status_coverage() -> None:
    cases = [
        ("stable", {"stabilizationReadinessScore": 0.78, "pluralityRetentionScore": 0.72, "trustLegibilityScore": 0.70}, {"trustRepairScore": 0.70, "memoryContinuityScore": 0.70, "renewalScatteringScore": 0.50}, {"resilienceDurabilityScore": 0.72, "institutionalRepairScore": 0.70}, {"governanceCoherenceScore": 0.70, "transitionPressureScore": 0.52}, 0.40, 0.44, "stabilization-visible"),
        ("strengthen", {"stabilizationReadinessScore": 0.74, "pluralityRetentionScore": 0.70, "trustLegibilityScore": 0.68}, {"trustRepairScore": 0.68, "memoryContinuityScore": 0.68, "renewalScatteringScore": 0.52}, {"resilienceDurabilityScore": 0.62, "institutionalRepairScore": 0.62}, {"governanceCoherenceScore": 0.68, "transitionPressureScore": 0.54}, 0.40, 0.44, "strengthen-resilience"),
        ("plurality", {"stabilizationReadinessScore": 0.76, "pluralityRetentionScore": 0.58, "trustLegibilityScore": 0.70}, {"trustRepairScore": 0.70, "memoryContinuityScore": 0.70, "renewalScatteringScore": 0.50}, {"resilienceDurabilityScore": 0.72, "institutionalRepairScore": 0.70}, {"governanceCoherenceScore": 0.70, "transitionPressureScore": 0.52}, 0.40, 0.44, "plurality-protect"),
        ("revert", {"stabilizationReadinessScore": 0.74, "pluralityRetentionScore": 0.70, "trustLegibilityScore": 0.68}, {"trustRepairScore": 0.50, "memoryContinuityScore": 0.56, "renewalScatteringScore": 0.72}, {"resilienceDurabilityScore": 0.72, "institutionalRepairScore": 0.70}, {"governanceCoherenceScore": 0.70, "transitionPressureScore": 0.52}, 0.40, 0.44, "fragmented-reversion"),
        ("watch", {"stabilizationReadinessScore": 0.78, "pluralityRetentionScore": 0.70, "trustLegibilityScore": 0.68}, {"trustRepairScore": 0.70, "memoryContinuityScore": 0.70, "renewalScatteringScore": 0.50}, {"resilienceDurabilityScore": 0.74, "institutionalRepairScore": 0.62}, {"governanceCoherenceScore": 0.70, "transitionPressureScore": 0.54}, 0.58, 0.44, "phase-transition-watch"),
        ("review", {"stabilizationReadinessScore": 0.64, "pluralityRetentionScore": 0.66, "trustLegibilityScore": 0.64}, {"trustRepairScore": 0.64, "memoryContinuityScore": 0.62, "renewalScatteringScore": 0.60}, {"resilienceDurabilityScore": 0.64, "institutionalRepairScore": 0.64}, {"governanceCoherenceScore": 0.64, "transitionPressureScore": 0.56}, 0.42, 0.44, "require-human-review"),
    ]
    got = set()
    for tid, row, reversion_row, resilience_row, governance_row, support_risk, trust_risk, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "future", **row},
            reversion_rows={tid: reversion_row},
            resilience_rows={tid: resilience_row},
            governance_rows={tid: governance_row},
            support_risk=support_risk,
            trust_surface_risk=trust_risk,
        )
        got.add(d.stabilization_status)
        assert d.stabilization_status == expected
    assert got == {"stabilization-visible", "strengthen-resilience", "plurality-protect", "fragmented-reversion", "phase-transition-watch", "require-human-review"}


def test_bounded_non_sovereign_language() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "future", "stabilizationReadinessScore": 0.78, "pluralityRetentionScore": 0.70, "trustLegibilityScore": 0.70},
        reversion_rows={"tone": {"trustRepairScore": 0.70, "memoryContinuityScore": 0.70, "renewalScatteringScore": 0.50}},
        resilience_rows={"tone": {"resilienceDurabilityScore": 0.72, "institutionalRepairScore": 0.70}},
        governance_rows={"tone": {"governanceCoherenceScore": 0.70, "transitionPressureScore": 0.52}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    t = " ".join([d.stabilization_context, d.plurality_context, d.reversion_context, d.trust_context, d.commons_context, d.explanation]).lower()
    assert "bounded post-crossing stabilization guidance" in t
    assert "non-coercive" in t
    assert "new epoch established" not in t
    assert "successor governance legitimate" not in t
    assert "history has turned" not in t
    assert "future secured permanently" not in t


def test_behavior_paths() -> None:
    strengthen = module.evaluate_target(
        {"targetId": "strengthen", "targetType": "future", "stabilizationReadinessScore": 0.74, "pluralityRetentionScore": 0.70, "trustLegibilityScore": 0.68},
        reversion_rows={"strengthen": {"trustRepairScore": 0.68, "memoryContinuityScore": 0.68, "renewalScatteringScore": 0.52}},
        resilience_rows={"strengthen": {"resilienceDurabilityScore": 0.62, "institutionalRepairScore": 0.62}},
        governance_rows={"strengthen": {"governanceCoherenceScore": 0.68, "transitionPressureScore": 0.54}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    plurality = module.evaluate_target(
        {"targetId": "plurality", "targetType": "future", "stabilizationReadinessScore": 0.78, "pluralityRetentionScore": 0.58, "trustLegibilityScore": 0.70},
        reversion_rows={"plurality": {"trustRepairScore": 0.70, "memoryContinuityScore": 0.70, "renewalScatteringScore": 0.50}},
        resilience_rows={"plurality": {"resilienceDurabilityScore": 0.72, "institutionalRepairScore": 0.70}},
        governance_rows={"plurality": {"governanceCoherenceScore": 0.70, "transitionPressureScore": 0.52}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    reversion = module.evaluate_target(
        {"targetId": "reversion", "targetType": "future", "stabilizationReadinessScore": 0.74, "pluralityRetentionScore": 0.70, "trustLegibilityScore": 0.68},
        reversion_rows={"reversion": {"trustRepairScore": 0.50, "memoryContinuityScore": 0.56, "renewalScatteringScore": 0.72}},
        resilience_rows={"reversion": {"resilienceDurabilityScore": 0.72, "institutionalRepairScore": 0.70}},
        governance_rows={"reversion": {"governanceCoherenceScore": 0.70, "transitionPressureScore": 0.52}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    watch = module.evaluate_target(
        {"targetId": "watch", "targetType": "future", "stabilizationReadinessScore": 0.78, "pluralityRetentionScore": 0.70, "trustLegibilityScore": 0.68},
        reversion_rows={"watch": {"trustRepairScore": 0.70, "memoryContinuityScore": 0.70, "renewalScatteringScore": 0.50}},
        resilience_rows={"watch": {"resilienceDurabilityScore": 0.74, "institutionalRepairScore": 0.62}},
        governance_rows={"watch": {"governanceCoherenceScore": 0.70, "transitionPressureScore": 0.54}},
        support_risk=0.58,
        trust_surface_risk=0.44,
    )
    assert strengthen.stabilization_status == "strengthen-resilience"
    assert plurality.stabilization_status == "plurality-protect"
    assert reversion.stabilization_status == "fragmented-reversion"
    assert reversion.target_publisher_action in {"watch", "suppress"}
    assert watch.stabilization_status == "phase-transition-watch"


def test_fail_closed_provenance_and_canonical_name(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/new_delta_stabilization_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.NewDeltaStabilizationInputError):
        module.build_outputs()

    monkeypatch.setattr(module, "NEW_DELTA_STABILIZATION_MAP_PATH", tmp_path / "bridge/non_canonical_name.json")
    _write_json(tmp_path / "bridge/non_canonical_name.json", _artifact({"targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.NewDeltaStabilizationInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/new_delta_stabilization_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    _write_json(tmp_path / "bridge/fragmented_renewal_reversion_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
