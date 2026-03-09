from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_discovery_navigation_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "discovery_navigation_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.discovery_navigation.fixture",
        "producerCommit": "fixture-ba-0001",
        "generatedAt": "2026-04-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-04-08T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "vector-field->discovery-audit->corridor-overlay->deliberation",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "Do not auto-pursue or canonize corridors without disclosure.",
        "commonsIntegrityNotice": "Discovery navigation remains bounded and plural.",
        "constraintSignatureVersion": "ba-1",
        "constraintSignatureSha256": "sha256:ababcdcd",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "DISCOVERY_VECTOR_FIELD_PATH", tmp_path / "bridge/discovery_vector_field.json")
    monkeypatch.setattr(module, "CROSS_DOMAIN_BRIDGE_MAP_PATH", tmp_path / "bridge/cross_domain_bridge_map.json")
    monkeypatch.setattr(module, "ENTROPY_REDUCTION_CORRIDOR_PATH", tmp_path / "bridge/entropy_reduction_corridor.json")
    monkeypatch.setattr(module, "DISCOVERY_NAVIGATION_REPORT_PATH", tmp_path / "bridge/discovery_navigation_report.json")
    monkeypatch.setattr(module, "EPISTEMIC_ATTRACTOR_AUDIT_PATH", tmp_path / "bridge/epistemic_attractor_audit.json")
    monkeypatch.setattr(module, "OPERATIONALIZATION_AUDIT_PATH", tmp_path / "bridge/operationalization_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "DISCOVERY_NAVIGATION_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/discovery_navigation_audit_v1.schema.json"))
    monkeypatch.setattr(module, "DISCOVERY_NAVIGATION_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/discovery_navigation_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(b / "discovery_vector_field.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "discovery", "vectorCoherence": 0.64, "noveltyGradient": 0.62}, {"targetId": "target:a", "targetType": "discovery", "vectorCoherence": 0.56, "noveltyGradient": 0.54}]}))
    _write_json(b / "cross_domain_bridge_map.json", _artifact({"targets": [{"targetId": "target:z", "bridgeStrength": 0.64, "bridgeLegibility": 0.62}, {"targetId": "target:a", "bridgeStrength": 0.56, "bridgeLegibility": 0.54}]}))
    _write_json(b / "entropy_reduction_corridor.json", _artifact({"targets": [{"targetId": "target:z", "entropyReductionSignal": 0.64, "deadZoneAdjacency": 0.40}, {"targetId": "target:a", "entropyReductionSignal": 0.58, "deadZoneAdjacency": 0.46}]}))
    _write_json(b / "discovery_navigation_report.json", _artifact({"targets": [{"targetId": "target:z", "overclaimPressure": 0.42, "commonsLegibility": 0.62, "valueAlignmentSupport": 0.62}, {"targetId": "target:a", "overclaimPressure": 0.48, "commonsLegibility": 0.56, "valueAlignmentSupport": 0.56}]}))
    for name in ("epistemic_attractor_audit.json", "operationalization_audit.json", "commons_sovereignty_audit.json", "civilizational_memory_audit.json", "value_alignment_audit.json"):
        _write_json(b / name, _audit_rows([0.3, 0.4]))


def test_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    audit_payload, rec_payload = module.build_outputs()
    assert [x["targetId"] for x in audit_payload["records"]] == ["target:a", "target:z"]
    assert [x["targetId"] for x in rec_payload["recommendations"]] == ["target:a", "target:z"]
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/discovery_navigation_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/discovery_navigation_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_discovery_status_coverage() -> None:
    cases = [
        ("observe", {"vectorCoherence": 0.52, "noveltyGradient": 0.52}, {"bridgeStrength": 0.58, "bridgeLegibility": 0.58}, {"entropyReductionSignal": 0.56, "deadZoneAdjacency": 0.48}, {"overclaimPressure": 0.46, "commonsLegibility": 0.56, "valueAlignmentSupport": 0.56}, "observe"),
        ("explore", {"vectorCoherence": 0.66, "noveltyGradient": 0.64}, {"bridgeStrength": 0.62, "bridgeLegibility": 0.60}, {"entropyReductionSignal": 0.64, "deadZoneAdjacency": 0.44}, {"overclaimPressure": 0.46, "commonsLegibility": 0.60, "valueAlignmentSupport": 0.62}, "explore-bounded"),
        ("bridge", {"vectorCoherence": 0.64, "noveltyGradient": 0.62}, {"bridgeStrength": 0.46, "bridgeLegibility": 0.50}, {"entropyReductionSignal": 0.62, "deadZoneAdjacency": 0.44}, {"overclaimPressure": 0.46, "commonsLegibility": 0.58, "valueAlignmentSupport": 0.58}, "bridge-first"),
        ("dead", {"vectorCoherence": 0.64, "noveltyGradient": 0.62}, {"bridgeStrength": 0.62, "bridgeLegibility": 0.60}, {"entropyReductionSignal": 0.62, "deadZoneAdjacency": 0.76}, {"overclaimPressure": 0.46, "commonsLegibility": 0.58, "valueAlignmentSupport": 0.58}, "dead-zone-risk"),
        ("human", {"vectorCoherence": 0.64, "noveltyGradient": 0.62}, {"bridgeStrength": 0.62, "bridgeLegibility": 0.60}, {"entropyReductionSignal": 0.62, "deadZoneAdjacency": 0.44}, {"overclaimPressure": 0.84, "commonsLegibility": 0.58, "valueAlignmentSupport": 0.58}, "require-human-review"),
    ]
    got = set()
    for tid, row, bridge, corridor, report, expected in cases:
        d = module.evaluate_target({"targetId": tid, "targetType": "discovery", **row}, bridge_rows={tid: bridge}, corridor_rows={tid: corridor}, report_rows={tid: report}, system_risk=0.35)
        got.add(d.discovery_status)
        assert d.discovery_status == expected
    assert got == {"observe", "explore-bounded", "bridge-first", "dead-zone-risk", "require-human-review"}


def test_bounded_language_and_commons_value_propagation() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "discovery", "vectorCoherence": 0.64, "noveltyGradient": 0.62},
        bridge_rows={"tone": {"bridgeStrength": 0.62, "bridgeLegibility": 0.60}},
        corridor_rows={"tone": {"entropyReductionSignal": 0.62, "deadZoneAdjacency": 0.44}},
        report_rows={"tone": {"overclaimPressure": 0.46, "commonsLegibility": 0.60, "valueAlignmentSupport": 0.62}},
        system_risk=0.35,
    )
    t = " ".join([d.vector_context, d.bridge_context, d.corridor_context, d.commons_context, d.explanation]).lower()
    assert "bounded" in t
    assert "do not authorize automatic pursuit" in t
    assert "commonslegibility" in d.commons_context.lower()
    assert "valuealignmentsupport" in d.commons_context.lower()


def test_dead_zone_and_overclaim_suppression() -> None:
    dead = module.evaluate_target(
        {"targetId": "dead", "targetType": "discovery", "vectorCoherence": 0.64, "noveltyGradient": 0.62},
        bridge_rows={"dead": {"bridgeStrength": 0.62, "bridgeLegibility": 0.60}},
        corridor_rows={"dead": {"entropyReductionSignal": 0.62, "deadZoneAdjacency": 0.78}},
        report_rows={"dead": {"overclaimPressure": 0.46, "commonsLegibility": 0.58, "valueAlignmentSupport": 0.58}},
        system_risk=0.35,
    )
    over = module.evaluate_target(
        {"targetId": "over", "targetType": "discovery", "vectorCoherence": 0.64, "noveltyGradient": 0.62},
        bridge_rows={"over": {"bridgeStrength": 0.62, "bridgeLegibility": 0.60}},
        corridor_rows={"over": {"entropyReductionSignal": 0.62, "deadZoneAdjacency": 0.44}},
        report_rows={"over": {"overclaimPressure": 0.84, "commonsLegibility": 0.58, "valueAlignmentSupport": 0.58}},
        system_risk=0.35,
    )
    assert dead.discovery_status == "dead-zone-risk"
    assert over.discovery_status == "require-human-review"
    assert dead.target_publisher_action == "suppress"
    assert over.target_publisher_action == "suppress"


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/discovery_vector_field.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "discovery"}]}))
    with pytest.raises(module.DiscoveryNavigationInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/discovery_vector_field.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "discovery"}]}))
    _write_json(tmp_path / "bridge/cross_domain_bridge_map.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
