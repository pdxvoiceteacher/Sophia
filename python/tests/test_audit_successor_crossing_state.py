from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_successor_crossing_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "successor_crossing_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.successor_crossing.fixture",
        "producerCommit": "fixture-bj-0001",
        "generatedAt": "2026-12-10T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-12-10T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "successor-crossing->false-future-decay->overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No governance transfer or centralized succession.",
        "commonsIntegrityNotice": "Futures remain plural, trust-legible, and memory-bearing.",
        "constraintSignatureVersion": "bj-1",
        "constraintSignatureSha256": "sha256:9898",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "SUCCESSOR_CROSSING_MAP_PATH", tmp_path / "bridge/successor_crossing_map.json")
    monkeypatch.setattr(module, "FALSE_FUTURE_DECAY_REPORT_PATH", tmp_path / "bridge/false_future_decay_report.json")
    monkeypatch.setattr(module, "DELTA_CROSSING_GATE_PATH", tmp_path / "bridge/delta_crossing_gate.json")
    monkeypatch.setattr(module, "FUTURE_VIABILITY_FORECAST_PATH", tmp_path / "bridge/future_viability_forecast.json")
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
    monkeypatch.setattr(module, "SUCCESSOR_CROSSING_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/successor_crossing_audit_v1.schema.json"))
    monkeypatch.setattr(module, "SUCCESSOR_CROSSING_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/successor_crossing_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(
        b / "successor_crossing_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "future", "crossingReadinessScore": 0.74, "pluralityRetentionScore": 0.70, "memoryContinuityScore": 0.68, "trustLegibilityScore": 0.68},
                    {"targetId": "target:a", "targetType": "future", "crossingReadinessScore": 0.72, "pluralityRetentionScore": 0.69, "memoryContinuityScore": 0.67, "trustLegibilityScore": 0.67},
                ]
            }
        ),
    )
    _write_json(
        b / "false_future_decay_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "simulatedLegitimacyScore": 0.52, "captureExposureScore": 0.50, "trustRepairScore": 0.64},
                    {"targetId": "target:a", "simulatedLegitimacyScore": 0.50, "captureExposureScore": 0.50, "trustRepairScore": 0.64},
                ]
            }
        ),
    )
    _write_json(
        b / "delta_crossing_gate.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "successorDeltaLikelihoodScore": 0.72, "phaseCouplingScore": 0.68},
                    {"targetId": "target:a", "successorDeltaLikelihoodScore": 0.71, "phaseCouplingScore": 0.68},
                ]
            }
        ),
    )
    _write_json(
        b / "future_viability_forecast.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "futureViabilityScore": 0.63, "foundationDurabilityScore": 0.62},
                    {"targetId": "target:a", "futureViabilityScore": 0.63, "foundationDurabilityScore": 0.62},
                ]
            }
        ),
    )

    for name in (
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
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/successor_crossing_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/successor_crossing_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_crossing_status_coverage() -> None:
    cases = [
        ("cross", {"crossingReadinessScore": 0.78, "pluralityRetentionScore": 0.72, "memoryContinuityScore": 0.70, "trustLegibilityScore": 0.70}, {"simulatedLegitimacyScore": 0.48, "captureExposureScore": 0.48, "trustRepairScore": 0.68}, {"successorDeltaLikelihoodScore": 0.70, "phaseCouplingScore": 0.68}, {"futureViabilityScore": 0.72, "foundationDurabilityScore": 0.72}, 0.36, 0.44, "crossing-visible"),
        ("foundation", {"crossingReadinessScore": 0.74, "pluralityRetentionScore": 0.70, "memoryContinuityScore": 0.68, "trustLegibilityScore": 0.68}, {"simulatedLegitimacyScore": 0.50, "captureExposureScore": 0.50, "trustRepairScore": 0.66}, {"successorDeltaLikelihoodScore": 0.71, "phaseCouplingScore": 0.68}, {"futureViabilityScore": 0.62, "foundationDurabilityScore": 0.62}, 0.40, 0.44, "strengthen-foundations"),
        ("plurality", {"crossingReadinessScore": 0.76, "pluralityRetentionScore": 0.56, "memoryContinuityScore": 0.68, "trustLegibilityScore": 0.70}, {"simulatedLegitimacyScore": 0.48, "captureExposureScore": 0.50, "trustRepairScore": 0.66}, {"successorDeltaLikelihoodScore": 0.75, "phaseCouplingScore": 0.72}, {"futureViabilityScore": 0.72, "foundationDurabilityScore": 0.70}, 0.36, 0.44, "plurality-protect"),
        ("decay", {"crossingReadinessScore": 0.74, "pluralityRetentionScore": 0.70, "memoryContinuityScore": 0.50, "trustLegibilityScore": 0.68}, {"simulatedLegitimacyScore": 0.78, "captureExposureScore": 0.74, "trustRepairScore": 0.50}, {"successorDeltaLikelihoodScore": 0.72, "phaseCouplingScore": 0.68}, {"futureViabilityScore": 0.70, "foundationDurabilityScore": 0.70}, 0.40, 0.44, "false-future-decay"),
        ("watch", {"crossingReadinessScore": 0.70, "pluralityRetentionScore": 0.69, "memoryContinuityScore": 0.67, "trustLegibilityScore": 0.67}, {"simulatedLegitimacyScore": 0.52, "captureExposureScore": 0.50, "trustRepairScore": 0.64}, {"successorDeltaLikelihoodScore": 0.78, "phaseCouplingScore": 0.74}, {"futureViabilityScore": 0.60, "foundationDurabilityScore": 0.60}, 0.54, 0.46, "phase-transition-watch"),
        ("review", {"crossingReadinessScore": 0.64, "pluralityRetentionScore": 0.65, "memoryContinuityScore": 0.62, "trustLegibilityScore": 0.64}, {"simulatedLegitimacyScore": 0.54, "captureExposureScore": 0.54, "trustRepairScore": 0.60}, {"successorDeltaLikelihoodScore": 0.62, "phaseCouplingScore": 0.62}, {"futureViabilityScore": 0.64, "foundationDurabilityScore": 0.64}, 0.40, 0.44, "require-human-review"),
    ]
    got = set()
    for tid, row, decay_row, gate, viability, support_risk, trust_risk, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "future", **row},
            decay_rows={tid: decay_row},
            gate_rows={tid: gate},
            viability_rows={tid: viability},
            support_risk=support_risk,
            trust_surface_risk=trust_risk,
        )
        got.add(d.crossing_status)
        assert d.crossing_status == expected
    assert got == {"crossing-visible", "strengthen-foundations", "plurality-protect", "false-future-decay", "phase-transition-watch", "require-human-review"}


def test_bounded_non_sovereign_language() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "future", "crossingReadinessScore": 0.78, "pluralityRetentionScore": 0.70, "memoryContinuityScore": 0.70, "trustLegibilityScore": 0.70},
        decay_rows={"tone": {"simulatedLegitimacyScore": 0.50, "captureExposureScore": 0.50, "trustRepairScore": 0.66}},
        gate_rows={"tone": {"successorDeltaLikelihoodScore": 0.70, "phaseCouplingScore": 0.68}},
        viability_rows={"tone": {"futureViabilityScore": 0.72, "foundationDurabilityScore": 0.72}},
        support_risk=0.36,
        trust_surface_risk=0.44,
    )
    t = " ".join([d.crossing_context, d.plurality_context, d.decay_context, d.trust_context, d.commons_context, d.explanation]).lower()
    assert "bounded successor-crossing guidance" in t
    assert "non-coercive" in t
    assert "new epoch confirmed" not in t
    assert "successor authority established" not in t
    assert "future secured" not in t
    assert "historical replacement complete" not in t


def test_behavior_paths() -> None:
    strengthen = module.evaluate_target(
        {"targetId": "foundation", "targetType": "future", "crossingReadinessScore": 0.74, "pluralityRetentionScore": 0.70, "memoryContinuityScore": 0.68, "trustLegibilityScore": 0.68},
        decay_rows={"foundation": {"simulatedLegitimacyScore": 0.50, "captureExposureScore": 0.50, "trustRepairScore": 0.66}},
        gate_rows={"foundation": {"successorDeltaLikelihoodScore": 0.71, "phaseCouplingScore": 0.68}},
        viability_rows={"foundation": {"futureViabilityScore": 0.62, "foundationDurabilityScore": 0.62}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    plurality = module.evaluate_target(
        {"targetId": "plurality", "targetType": "future", "crossingReadinessScore": 0.78, "pluralityRetentionScore": 0.58, "memoryContinuityScore": 0.70, "trustLegibilityScore": 0.70},
        decay_rows={"plurality": {"simulatedLegitimacyScore": 0.50, "captureExposureScore": 0.50, "trustRepairScore": 0.66}},
        gate_rows={"plurality": {"successorDeltaLikelihoodScore": 0.78, "phaseCouplingScore": 0.74}},
        viability_rows={"plurality": {"futureViabilityScore": 0.74, "foundationDurabilityScore": 0.72}},
        support_risk=0.36,
        trust_surface_risk=0.44,
    )
    decay = module.evaluate_target(
        {"targetId": "decay", "targetType": "future", "crossingReadinessScore": 0.74, "pluralityRetentionScore": 0.70, "memoryContinuityScore": 0.50, "trustLegibilityScore": 0.68},
        decay_rows={"decay": {"simulatedLegitimacyScore": 0.78, "captureExposureScore": 0.74, "trustRepairScore": 0.50}},
        gate_rows={"decay": {"successorDeltaLikelihoodScore": 0.72, "phaseCouplingScore": 0.68}},
        viability_rows={"decay": {"futureViabilityScore": 0.70, "foundationDurabilityScore": 0.70}},
        support_risk=0.40,
        trust_surface_risk=0.44,
    )
    watch = module.evaluate_target(
        {"targetId": "watch", "targetType": "future", "crossingReadinessScore": 0.70, "pluralityRetentionScore": 0.69, "memoryContinuityScore": 0.67, "trustLegibilityScore": 0.67},
        decay_rows={"watch": {"simulatedLegitimacyScore": 0.52, "captureExposureScore": 0.50, "trustRepairScore": 0.64}},
        gate_rows={"watch": {"successorDeltaLikelihoodScore": 0.78, "phaseCouplingScore": 0.74}},
        viability_rows={"watch": {"futureViabilityScore": 0.60, "foundationDurabilityScore": 0.60}},
        support_risk=0.54,
        trust_surface_risk=0.46,
    )
    assert strengthen.crossing_status == "strengthen-foundations"
    assert plurality.crossing_status == "plurality-protect"
    assert decay.crossing_status == "false-future-decay"
    assert decay.target_publisher_action in {"watch", "suppress"}
    assert watch.crossing_status == "phase-transition-watch"


def test_fail_closed_provenance_and_canonical_name(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/successor_crossing_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.SuccessorCrossingInputError):
        module.build_outputs()

    monkeypatch.setattr(module, "SUCCESSOR_CROSSING_MAP_PATH", tmp_path / "bridge/non_canonical_name.json")
    _write_json(tmp_path / "bridge/non_canonical_name.json", _artifact({"targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.SuccessorCrossingInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/successor_crossing_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    _write_json(tmp_path / "bridge/false_future_decay_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
