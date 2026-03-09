from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_knowledge_river_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "knowledge_river_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.knowledge_river.fixture",
        "producerCommit": "fixture-bb-0001",
        "generatedAt": "2026-04-09T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-04-09T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "knowledge-river->braid-formalization->bounded-river-audit->publisher-overlay->stewardship",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "Do not canonize a single prestige channel.",
        "commonsIntegrityNotice": "Braided tributaries and dissent must remain visible.",
        "constraintSignatureVersion": "bb-1",
        "constraintSignatureSha256": "sha256:riverbb11",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_MAP_PATH", tmp_path / "bridge/knowledge_river_map.json")
    monkeypatch.setattr(module, "CORRIDOR_BRAIDING_REPORT_PATH", tmp_path / "bridge/corridor_braiding_report.json")
    monkeypatch.setattr(module, "TRIBUTARY_SUPPORT_REGISTRY_PATH", tmp_path / "bridge/tributary_support_registry.json")
    monkeypatch.setattr(module, "RIVER_CAPTURE_RISK_REPORT_PATH", tmp_path / "bridge/river_capture_risk_report.json")
    monkeypatch.setattr(module, "DISCOVERY_NAVIGATION_AUDIT_PATH", tmp_path / "bridge/discovery_navigation_audit.json")
    monkeypatch.setattr(module, "EPISTEMIC_ATTRACTOR_AUDIT_PATH", tmp_path / "bridge/epistemic_attractor_audit.json")
    monkeypatch.setattr(module, "OPERATIONALIZATION_AUDIT_PATH", tmp_path / "bridge/operationalization_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/knowledge_river_audit_v1.schema.json"))
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/knowledge_river_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(
        b / "knowledge_river_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "knowledge-river", "riverCoherence": 0.66, "flowPlurality": 0.64, "riverLegibility": 0.62},
                    {"targetId": "target:a", "targetType": "knowledge-river", "riverCoherence": 0.58, "flowPlurality": 0.56, "riverLegibility": 0.57},
                ]
            }
        ),
    )
    _write_json(
        b / "corridor_braiding_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "braidStability": 0.66, "braidLegibility": 0.63, "corridorRedundancy": 0.61},
                    {"targetId": "target:a", "braidStability": 0.56, "braidLegibility": 0.56, "corridorRedundancy": 0.55},
                ]
            }
        ),
    )
    _write_json(
        b / "tributary_support_registry.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "tributarySupport": 0.62, "dissentPreservation": 0.66, "minorityLegibility": 0.62},
                    {"targetId": "target:a", "tributarySupport": 0.58, "dissentPreservation": 0.60, "minorityLegibility": 0.56},
                ]
            }
        ),
    )
    _write_json(
        b / "river_capture_risk_report.json",
        _artifact(
            {
                "targets": [
                    {
                        "targetId": "target:z",
                        "captureRisk": 0.42,
                        "centralizationPressure": 0.40,
                        "priesthoodPressure": 0.30,
                        "canonClosureRisk": 0.32,
                        "monopolizationRisk": 0.42,
                        "commonsIrrigation": 0.62,
                        "valueAlignmentSupport": 0.63,
                    },
                    {
                        "targetId": "target:a",
                        "captureRisk": 0.46,
                        "centralizationPressure": 0.44,
                        "priesthoodPressure": 0.36,
                        "canonClosureRisk": 0.34,
                        "monopolizationRisk": 0.46,
                        "commonsIrrigation": 0.58,
                        "valueAlignmentSupport": 0.58,
                    },
                ]
            }
        ),
    )
    for name in (
        "discovery_navigation_audit.json",
        "epistemic_attractor_audit.json",
        "operationalization_audit.json",
        "commons_sovereignty_audit.json",
        "civilizational_memory_audit.json",
        "value_alignment_audit.json",
    ):
        _write_json(b / name, _audit_rows([0.3, 0.4]))


def test_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    audit_payload, rec_payload = module.build_outputs()
    assert [x["targetId"] for x in audit_payload["records"]] == ["target:a", "target:z"]
    assert [x["targetId"] for x in rec_payload["recommendations"]] == ["target:a", "target:z"]
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/knowledge_river_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/knowledge_river_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_river_status_coverage() -> None:
    cases = [
        (
            "forming",
            {"riverCoherence": 0.58, "flowPlurality": 0.56, "riverLegibility": 0.56},
            {"braidStability": 0.56, "braidLegibility": 0.55, "corridorRedundancy": 0.56},
            {"tributarySupport": 0.58, "dissentPreservation": 0.60, "minorityLegibility": 0.58},
            {"captureRisk": 0.46, "centralizationPressure": 0.46, "priesthoodPressure": 0.34, "canonClosureRisk": 0.34, "monopolizationRisk": 0.46},
            "river-forming",
        ),
        (
            "stable",
            {"riverCoherence": 0.68, "flowPlurality": 0.66, "riverLegibility": 0.64},
            {"braidStability": 0.66, "braidLegibility": 0.62, "corridorRedundancy": 0.62},
            {"tributarySupport": 0.60, "dissentPreservation": 0.66, "minorityLegibility": 0.62},
            {"captureRisk": 0.44, "centralizationPressure": 0.44, "priesthoodPressure": 0.32, "canonClosureRisk": 0.32, "monopolizationRisk": 0.44},
            "braid-stable",
        ),
        (
            "tributary",
            {"riverCoherence": 0.66, "flowPlurality": 0.64, "riverLegibility": 0.62},
            {"braidStability": 0.62, "braidLegibility": 0.60, "corridorRedundancy": 0.60},
            {"tributarySupport": 0.48, "dissentPreservation": 0.58, "minorityLegibility": 0.58},
            {"captureRisk": 0.44, "centralizationPressure": 0.44, "priesthoodPressure": 0.32, "canonClosureRisk": 0.32, "monopolizationRisk": 0.44},
            "tributary-strengthen",
        ),
        (
            "capture",
            {"riverCoherence": 0.66, "flowPlurality": 0.64, "riverLegibility": 0.62},
            {"braidStability": 0.62, "braidLegibility": 0.60, "corridorRedundancy": 0.60},
            {"tributarySupport": 0.60, "dissentPreservation": 0.62, "minorityLegibility": 0.60},
            {"captureRisk": 0.76, "centralizationPressure": 0.66, "priesthoodPressure": 0.34, "canonClosureRisk": 0.34, "monopolizationRisk": 0.66},
            "capture-risk",
        ),
        (
            "human",
            {"riverCoherence": 0.66, "flowPlurality": 0.64, "riverLegibility": 0.62},
            {"braidStability": 0.62, "braidLegibility": 0.60, "corridorRedundancy": 0.60},
            {"tributarySupport": 0.60, "dissentPreservation": 0.62, "minorityLegibility": 0.60},
            {"captureRisk": 0.66, "centralizationPressure": 0.64, "priesthoodPressure": 0.74, "canonClosureRisk": 0.34, "monopolizationRisk": 0.64},
            "require-human-review",
        ),
    ]
    got = set()
    for tid, row, braid, tributary, capture, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "knowledge-river", **row},
            braid_rows={tid: braid},
            tributary_rows={tid: tributary},
            capture_rows={tid: capture},
            system_risk=0.35,
        )
        got.add(d.river_status)
        assert d.river_status == expected
    assert got == {"river-forming", "braid-stable", "tributary-strengthen", "capture-risk", "require-human-review"}


def test_bounded_language_and_dissent_respect() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "knowledge-river", "riverCoherence": 0.66, "flowPlurality": 0.64, "riverLegibility": 0.62},
        braid_rows={"tone": {"braidStability": 0.64, "braidLegibility": 0.62, "corridorRedundancy": 0.61}},
        tributary_rows={"tone": {"tributarySupport": 0.60, "dissentPreservation": 0.66, "minorityLegibility": 0.62}},
        capture_rows={"tone": {"captureRisk": 0.44, "centralizationPressure": 0.42, "priesthoodPressure": 0.30, "canonClosureRisk": 0.30, "monopolizationRisk": 0.42}},
        system_risk=0.35,
    )
    text = " ".join([d.river_context, d.braid_context, d.tributary_context, d.commons_context, d.explanation]).lower()
    assert "bounded" in text
    assert "do not authorize canonization" in text
    assert "closure of scientific alternatives" in text
    assert "dissent" in d.tributary_context.lower()


def test_capture_risk_and_priesthood_suppression() -> None:
    capture = module.evaluate_target(
        {"targetId": "capture", "targetType": "knowledge-river", "riverCoherence": 0.66, "flowPlurality": 0.64, "riverLegibility": 0.62},
        braid_rows={"capture": {"braidStability": 0.64, "braidLegibility": 0.62, "corridorRedundancy": 0.61}},
        tributary_rows={"capture": {"tributarySupport": 0.60, "dissentPreservation": 0.62, "minorityLegibility": 0.60}},
        capture_rows={"capture": {"captureRisk": 0.76, "centralizationPressure": 0.66, "priesthoodPressure": 0.34, "canonClosureRisk": 0.34, "monopolizationRisk": 0.66}},
        system_risk=0.35,
    )
    priesthood = module.evaluate_target(
        {"targetId": "priesthood", "targetType": "knowledge-river", "riverCoherence": 0.66, "flowPlurality": 0.64, "riverLegibility": 0.62},
        braid_rows={"priesthood": {"braidStability": 0.64, "braidLegibility": 0.62, "corridorRedundancy": 0.61}},
        tributary_rows={"priesthood": {"tributarySupport": 0.60, "dissentPreservation": 0.62, "minorityLegibility": 0.60}},
        capture_rows={"priesthood": {"captureRisk": 0.66, "centralizationPressure": 0.64, "priesthoodPressure": 0.74, "canonClosureRisk": 0.34, "monopolizationRisk": 0.64}},
        system_risk=0.35,
    )
    assert capture.river_status == "capture-risk"
    assert priesthood.river_status == "require-human-review"
    assert capture.target_publisher_action == "suppress"
    assert priesthood.target_publisher_action == "suppress"


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/knowledge_river_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "knowledge-river"}]}))
    with pytest.raises(module.KnowledgeRiverInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/knowledge_river_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "knowledge-river"}]}))
    _write_json(tmp_path / "bridge/corridor_braiding_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
