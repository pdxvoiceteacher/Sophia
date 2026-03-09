from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_epistemic_attractor_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "epistemic_attractor_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.epistemic_attractor.fixture",
        "producerCommit": "fixture-aw-0001",
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
        "canonicalPhaselock": "attractor-map->topology-audit->overlay->ratification",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "Do not erase contested basins or dead zones without disclosure.",
        "commonsIntegrityNotice": "Epistemic topology remains plural and contestable.",
        "constraintSignatureVersion": "aw-1",
        "constraintSignatureSha256": "sha256:cdcdcdcd",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "EPISTEMIC_ATTRACTOR_MAP_PATH", tmp_path / "bridge/epistemic_attractor_map.json")
    monkeypatch.setattr(module, "KNOWLEDGE_BASIN_REGISTRY_PATH", tmp_path / "bridge/knowledge_basin_registry.json")
    monkeypatch.setattr(module, "DEAD_ZONE_REPORT_PATH", tmp_path / "bridge/dead_zone_report.json")
    monkeypatch.setattr(module, "PARADIGM_SHIFT_FORECAST_PATH", tmp_path / "bridge/paradigm_shift_forecast.json")
    monkeypatch.setattr(module, "THEORY_CORPUS_AUDIT_PATH", tmp_path / "bridge/theory_corpus_audit.json")
    monkeypatch.setattr(module, "EMERGENT_DOMAIN_AUDIT_PATH", tmp_path / "bridge/emergent_domain_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "EPISTEMIC_ATTRACTOR_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/epistemic_attractor_audit_v1.schema.json"))
    monkeypatch.setattr(module, "EPISTEMIC_ATTRACTOR_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/epistemic_attractor_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(bridge / "epistemic_attractor_map.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "epistemic", "attractorStability": 0.68, "recurrenceVisibility": 0.66}, {"targetId": "target:a", "targetType": "epistemic", "attractorStability": 0.60, "recurrenceVisibility": 0.58}]}))
    _write_json(bridge / "knowledge_basin_registry.json", _artifact({"targets": [{"targetId": "target:z", "basinCoherence": 0.68, "basinContestation": 0.40}, {"targetId": "target:a", "basinCoherence": 0.60, "basinContestation": 0.46}]}))
    _write_json(bridge / "dead_zone_report.json", _artifact({"targets": [{"targetId": "target:z", "deadZoneRecurrence": 0.42, "deadZoneOpacity": 0.36, "negativeResultPreservation": 0.66}, {"targetId": "target:a", "deadZoneRecurrence": 0.50, "deadZoneOpacity": 0.40, "negativeResultPreservation": 0.58}]}))
    _write_json(bridge / "paradigm_shift_forecast.json", _artifact({"targets": [{"targetId": "target:z", "paradigmShiftSignal": 0.54, "overclaimPressure": 0.40}, {"targetId": "target:a", "paradigmShiftSignal": 0.60, "overclaimPressure": 0.46}]}))
    for name in ("theory_corpus_audit.json", "emergent_domain_audit.json", "commons_sovereignty_audit.json", "civilizational_memory_audit.json"):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    audit_payload, recommendations_payload = module.build_outputs()
    assert [i["targetId"] for i in audit_payload["records"]] == ["target:a", "target:z"]
    assert [i["targetId"] for i in recommendations_payload["recommendations"]] == ["target:a", "target:z"]
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/epistemic_attractor_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/epistemic_attractor_recommendations_v1.schema.json").read_text())).validate(recommendations_payload)


def test_full_status_coverage() -> None:
    cases = [
        ("stable", {"attractorStability": 0.72, "recurrenceVisibility": 0.70}, {"basinCoherence": 0.70, "basinContestation": 0.40}, {"deadZoneRecurrence": 0.42, "deadZoneOpacity": 0.36, "negativeResultPreservation": 0.70}, {"paradigmShiftSignal": 0.54, "overclaimPressure": 0.40}, "attractor-stable"),
        ("contested", {"attractorStability": 0.60, "recurrenceVisibility": 0.58}, {"basinCoherence": 0.58, "basinContestation": 0.66}, {"deadZoneRecurrence": 0.50, "deadZoneOpacity": 0.44, "negativeResultPreservation": 0.58}, {"paradigmShiftSignal": 0.56, "overclaimPressure": 0.46}, "basin-contested"),
        ("dead", {"attractorStability": 0.60, "recurrenceVisibility": 0.58}, {"basinCoherence": 0.58, "basinContestation": 0.54}, {"deadZoneRecurrence": 0.76, "deadZoneOpacity": 0.74, "negativeResultPreservation": 0.58}, {"paradigmShiftSignal": 0.56, "overclaimPressure": 0.46}, "dead-zone-watch"),
        ("shift", {"attractorStability": 0.60, "recurrenceVisibility": 0.58}, {"basinCoherence": 0.58, "basinContestation": 0.54}, {"deadZoneRecurrence": 0.50, "deadZoneOpacity": 0.40, "negativeResultPreservation": 0.58}, {"paradigmShiftSignal": 0.72, "overclaimPressure": 0.52}, "paradigm-shift-rising"),
        ("human", {"attractorStability": 0.60, "recurrenceVisibility": 0.58}, {"basinCoherence": 0.58, "basinContestation": 0.54}, {"deadZoneRecurrence": 0.50, "deadZoneOpacity": 0.40, "negativeResultPreservation": 0.58}, {"paradigmShiftSignal": 0.86, "overclaimPressure": 0.82}, "require-human-review"),
    ]
    got = set()
    for tid, row, basin, dead, shift, expected in cases:
        d = module.evaluate_target({"targetId": tid, "targetType": "epistemic", **row}, basin_rows={tid: basin}, dead_zone_rows={tid: dead}, shift_rows={tid: shift}, system_risk=0.35)
        got.add(d.epistemic_status)
        assert d.epistemic_status == expected
    assert got == {"attractor-stable", "basin-contested", "dead-zone-watch", "paradigm-shift-rising", "require-human-review"}


def test_bounded_language_and_negative_result_respect() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "epistemic", "attractorStability": 0.62, "recurrenceVisibility": 0.60},
        basin_rows={"tone": {"basinCoherence": 0.62, "basinContestation": 0.54}},
        dead_zone_rows={"tone": {"deadZoneRecurrence": 0.52, "deadZoneOpacity": 0.42, "negativeResultPreservation": 0.30}},
        shift_rows={"tone": {"paradigmShiftSignal": 0.58, "overclaimPressure": 0.48}},
        system_risk=0.35,
    )
    t = " ".join([d.attractor_context, d.basin_context, d.dead_zone_context, d.shift_context, d.explanation]).lower()
    assert "bounded" in t
    assert "do not certify final truth" in t
    assert "negative" in t
    assert "inevitable truth" not in t


def test_dead_zone_and_overclaim_suppression() -> None:
    dead = module.evaluate_target(
        {"targetId": "dead", "targetType": "epistemic", "attractorStability": 0.60, "recurrenceVisibility": 0.58},
        basin_rows={"dead": {"basinCoherence": 0.58, "basinContestation": 0.54}},
        dead_zone_rows={"dead": {"deadZoneRecurrence": 0.80, "deadZoneOpacity": 0.76, "negativeResultPreservation": 0.58}},
        shift_rows={"dead": {"paradigmShiftSignal": 0.56, "overclaimPressure": 0.46}},
        system_risk=0.35,
    )
    over = module.evaluate_target(
        {"targetId": "over", "targetType": "epistemic", "attractorStability": 0.60, "recurrenceVisibility": 0.58},
        basin_rows={"over": {"basinCoherence": 0.58, "basinContestation": 0.54}},
        dead_zone_rows={"over": {"deadZoneRecurrence": 0.50, "deadZoneOpacity": 0.40, "negativeResultPreservation": 0.58}},
        shift_rows={"over": {"paradigmShiftSignal": 0.86, "overclaimPressure": 0.82}},
        system_risk=0.35,
    )
    assert dead.epistemic_status == "dead-zone-watch"
    assert over.epistemic_status == "require-human-review"
    assert over.target_publisher_action == "suppress"


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/epistemic_attractor_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "epistemic"}]}))
    with pytest.raises(module.EpistemicAttractorInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/epistemic_attractor_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "epistemic"}]}))
    _write_json(tmp_path / "bridge/knowledge_basin_registry.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
