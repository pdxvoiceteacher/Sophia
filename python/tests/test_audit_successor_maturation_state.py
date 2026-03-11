from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_successor_maturation_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "successor_maturation_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.successor_maturation.fixture",
        "producerCommit": "fixture-bi-0001",
        "generatedAt": "2026-12-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-12-08T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "successor-maturation->false-future-audit->overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No governance transfer or centralized succession.",
        "commonsIntegrityNotice": "Futures remain plural, trust-legible, and memory-bearing.",
        "constraintSignatureVersion": "bi-1",
        "constraintSignatureSha256": "sha256:6767",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "SUCCESSOR_MATURATION_MAP_PATH", tmp_path / "bridge/successor_maturation_map.json")
    monkeypatch.setattr(module, "FALSE_FUTURE_RISK_REPORT_PATH", tmp_path / "bridge/false_future_risk_report.json")
    monkeypatch.setattr(module, "PLURALITY_RETENTION_SCORECARD_PATH", tmp_path / "bridge/plurality_retention_scorecard.json")
    monkeypatch.setattr(module, "MATURATION_GATE_REPORT_PATH", tmp_path / "bridge/maturation_gate_report.json")
    monkeypatch.setattr(module, "SUCCESSOR_DELTA_AUDIT_PATH", tmp_path / "bridge/successor_delta_audit.json")
    monkeypatch.setattr(module, "TERRACE_EROSION_AUDIT_PATH", tmp_path / "bridge/terrace_erosion_audit.json")
    monkeypatch.setattr(module, "EPOCHAL_TERRACE_AUDIT_PATH", tmp_path / "bridge/epochal_terrace_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_DELTA_AUDIT_PATH", tmp_path / "bridge/civilizational_delta_audit.json")
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_AUDIT_PATH", tmp_path / "bridge/knowledge_river_audit.json")
    monkeypatch.setattr(module, "TRUST_SURFACE_AUDIT_PATH", tmp_path / "bridge/trust_surface_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "SUCCESSOR_MATURATION_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/successor_maturation_audit_v1.schema.json"))
    monkeypatch.setattr(module, "SUCCESSOR_MATURATION_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/successor_maturation_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(b / "successor_maturation_map.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "future", "maturationScore": 0.66, "memoryContinuityScore": 0.66}, {"targetId": "target:a", "targetType": "future", "maturationScore": 0.64, "memoryContinuityScore": 0.64}]}))
    _write_json(b / "false_future_risk_report.json", _artifact({"targets": [{"targetId": "target:z", "simulatedLegitimacyScore": 0.52, "trustCompressionScore": 0.50, "prematureConvergenceScore": 0.50}, {"targetId": "target:a", "simulatedLegitimacyScore": 0.50, "trustCompressionScore": 0.50, "prematureConvergenceScore": 0.48}]}))
    _write_json(b / "plurality_retention_scorecard.json", _artifact({"targets": [{"targetId": "target:z", "pluralityRetentionScore": 0.68}, {"targetId": "target:a", "pluralityRetentionScore": 0.66}]}))
    _write_json(b / "maturation_gate_report.json", _artifact({"targets": [{"targetId": "target:z", "successorCaptureRiskScore": 0.42, "couplingStrengthScore": 0.62}, {"targetId": "target:a", "successorCaptureRiskScore": 0.40, "couplingStrengthScore": 0.60}]}))

    for name in (
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
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/successor_maturation_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/successor_maturation_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_maturation_status_coverage() -> None:
    cases = [
        ("mature", {"maturationScore": 0.76, "memoryContinuityScore": 0.72}, {"simulatedLegitimacyScore": 0.50, "trustCompressionScore": 0.48, "prematureConvergenceScore": 0.48}, {"pluralityRetentionScore": 0.70}, {"successorCaptureRiskScore": 0.42, "couplingStrengthScore": 0.62}, 0.34, 0.44, "maturation-visible"),
        ("plural", {"maturationScore": 0.66, "memoryContinuityScore": 0.70}, {"simulatedLegitimacyScore": 0.52, "trustCompressionScore": 0.50, "prematureConvergenceScore": 0.50}, {"pluralityRetentionScore": 0.70}, {"successorCaptureRiskScore": 0.42, "couplingStrengthScore": 0.62}, 0.34, 0.44, "plurality-retain"),
        ("false", {"maturationScore": 0.72, "memoryContinuityScore": 0.54}, {"simulatedLegitimacyScore": 0.74, "trustCompressionScore": 0.72, "prematureConvergenceScore": 0.72}, {"pluralityRetentionScore": 0.54}, {"successorCaptureRiskScore": 0.42, "couplingStrengthScore": 0.62}, 0.36, 0.50, "false-future-risk"),
        ("capture", {"maturationScore": 0.78, "memoryContinuityScore": 0.74}, {"simulatedLegitimacyScore": 0.50, "trustCompressionScore": 0.48, "prematureConvergenceScore": 0.48}, {"pluralityRetentionScore": 0.70}, {"successorCaptureRiskScore": 0.82, "couplingStrengthScore": 0.62}, 0.34, 0.44, "capture-risk"),
        ("watch", {"maturationScore": 0.72, "memoryContinuityScore": 0.70}, {"simulatedLegitimacyScore": 0.50, "trustCompressionScore": 0.48, "prematureConvergenceScore": 0.48}, {"pluralityRetentionScore": 0.70}, {"successorCaptureRiskScore": 0.42, "couplingStrengthScore": 0.74}, 0.36, 0.50, "phase-transition-watch"),
        ("review", {"maturationScore": 0.60, "memoryContinuityScore": 0.60}, {"simulatedLegitimacyScore": 0.52, "trustCompressionScore": 0.52, "prematureConvergenceScore": 0.50}, {"pluralityRetentionScore": 0.60}, {"successorCaptureRiskScore": 0.42, "couplingStrengthScore": 0.60}, 0.34, 0.44, "require-human-review"),
    ]
    got = set()
    for tid, row, false_row, plurality, gate, support_risk, trust_risk, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "future", **row},
            false_rows={tid: false_row},
            plurality_rows={tid: plurality},
            gate_rows={tid: gate},
            support_risk=support_risk,
            trust_surface_risk=trust_risk,
        )
        got.add(d.maturation_status)
        assert d.maturation_status == expected
    assert got == {"maturation-visible", "plurality-retain", "false-future-risk", "capture-risk", "phase-transition-watch", "require-human-review"}


def test_bounded_non_sovereign_language() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "future", "maturationScore": 0.76, "memoryContinuityScore": 0.72},
        false_rows={"tone": {"simulatedLegitimacyScore": 0.50, "trustCompressionScore": 0.48, "prematureConvergenceScore": 0.48}},
        plurality_rows={"tone": {"pluralityRetentionScore": 0.70}},
        gate_rows={"tone": {"successorCaptureRiskScore": 0.42, "couplingStrengthScore": 0.62}},
        support_risk=0.34,
        trust_surface_risk=0.44,
    )
    t = " ".join([d.maturation_context, d.plurality_context, d.false_future_context, d.trust_context, d.commons_context, d.explanation]).lower()
    assert "bounded successor-maturation guidance" in t
    assert "non-coercive" in t
    assert "new epoch confirmed" not in t
    assert "future secured" not in t
    assert "successor order legitimate" not in t
    assert "historical replacement complete" not in t


def test_plurality_false_future_capture_and_watch_behaviors() -> None:
    plurality = module.evaluate_target(
        {"targetId": "plural", "targetType": "future", "maturationScore": 0.66, "memoryContinuityScore": 0.70},
        false_rows={"plural": {"simulatedLegitimacyScore": 0.52, "trustCompressionScore": 0.50, "prematureConvergenceScore": 0.50}},
        plurality_rows={"plural": {"pluralityRetentionScore": 0.70}},
        gate_rows={"plural": {"successorCaptureRiskScore": 0.42, "couplingStrengthScore": 0.62}},
        support_risk=0.34,
        trust_surface_risk=0.44,
    )
    false_future = module.evaluate_target(
        {"targetId": "false", "targetType": "future", "maturationScore": 0.72, "memoryContinuityScore": 0.54},
        false_rows={"false": {"simulatedLegitimacyScore": 0.74, "trustCompressionScore": 0.72, "prematureConvergenceScore": 0.72}},
        plurality_rows={"false": {"pluralityRetentionScore": 0.54}},
        gate_rows={"false": {"successorCaptureRiskScore": 0.42, "couplingStrengthScore": 0.62}},
        support_risk=0.36,
        trust_surface_risk=0.50,
    )
    capture = module.evaluate_target(
        {"targetId": "capture", "targetType": "future", "maturationScore": 0.78, "memoryContinuityScore": 0.74},
        false_rows={"capture": {"simulatedLegitimacyScore": 0.50, "trustCompressionScore": 0.48, "prematureConvergenceScore": 0.48}},
        plurality_rows={"capture": {"pluralityRetentionScore": 0.70}},
        gate_rows={"capture": {"successorCaptureRiskScore": 0.82, "couplingStrengthScore": 0.62}},
        support_risk=0.34,
        trust_surface_risk=0.44,
    )
    watch = module.evaluate_target(
        {"targetId": "watch", "targetType": "future", "maturationScore": 0.72, "memoryContinuityScore": 0.70},
        false_rows={"watch": {"simulatedLegitimacyScore": 0.50, "trustCompressionScore": 0.48, "prematureConvergenceScore": 0.48}},
        plurality_rows={"watch": {"pluralityRetentionScore": 0.70}},
        gate_rows={"watch": {"successorCaptureRiskScore": 0.42, "couplingStrengthScore": 0.74}},
        support_risk=0.36,
        trust_surface_risk=0.50,
    )
    assert plurality.maturation_status == "plurality-retain"
    assert false_future.maturation_status == "false-future-risk"
    assert capture.maturation_status == "capture-risk"
    assert watch.maturation_status == "phase-transition-watch"


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/successor_maturation_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    with pytest.raises(module.SuccessorMaturationInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/successor_maturation_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "future"}]}))
    _write_json(tmp_path / "bridge/false_future_risk_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
