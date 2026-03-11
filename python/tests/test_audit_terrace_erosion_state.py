from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_terrace_erosion_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "terrace_erosion_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.terrace_erosion.fixture",
        "producerCommit": "fixture-bg-0001",
        "generatedAt": "2026-10-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-10-08T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "terrace-erosion-map->erosion-audit->overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No coercive transition or centralized replacement.",
        "commonsIntegrityNotice": "Renewal remains plural and bounded.",
        "constraintSignatureVersion": "bg-1",
        "constraintSignatureSha256": "sha256:9898",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "TERRACE_EROSION_MAP_PATH", tmp_path / "bridge/terrace_erosion_map.json")
    monkeypatch.setattr(module, "ORTHODOXY_PRESSURE_REPORT_PATH", tmp_path / "bridge/orthodoxy_pressure_report.json")
    monkeypatch.setattr(module, "RENEWAL_CORRIDOR_REGISTRY_PATH", tmp_path / "bridge/renewal_corridor_registry.json")
    monkeypatch.setattr(module, "EPOCHAL_TRANSITION_FORECAST_PATH", tmp_path / "bridge/epochal_transition_forecast.json")
    monkeypatch.setattr(module, "EPOCHAL_TERRACE_AUDIT_PATH", tmp_path / "bridge/epochal_terrace_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_DELTA_AUDIT_PATH", tmp_path / "bridge/civilizational_delta_audit.json")
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_AUDIT_PATH", tmp_path / "bridge/knowledge_river_audit.json")
    monkeypatch.setattr(module, "TRUST_SURFACE_AUDIT_PATH", tmp_path / "bridge/trust_surface_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "TERRACE_EROSION_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/terrace_erosion_audit_v1.schema.json"))
    monkeypatch.setattr(module, "TERRACE_EROSION_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/terrace_erosion_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(b / "terrace_erosion_map.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "terrace", "localErosionScore": 0.58, "synchronizedErosionScore": 0.50, "pluralityRetentionScore": 0.62}, {"targetId": "target:a", "targetType": "terrace", "localErosionScore": 0.56, "synchronizedErosionScore": 0.48, "pluralityRetentionScore": 0.64}]}))
    _write_json(b / "orthodoxy_pressure_report.json", _artifact({"targets": [{"targetId": "target:z", "orthodoxyPressureScore": 0.56}, {"targetId": "target:a", "orthodoxyPressureScore": 0.52}]}))
    _write_json(b / "renewal_corridor_registry.json", _artifact({"targets": [{"targetId": "target:z", "renewalCorridorStrengthScore": 0.64, "boundedTrustRepairScore": 0.62}, {"targetId": "target:a", "renewalCorridorStrengthScore": 0.66, "boundedTrustRepairScore": 0.64}]}))
    _write_json(b / "epochal_transition_forecast.json", _artifact({"targets": [{"targetId": "target:z", "transitionSignalScore": 0.58, "collapseNarrativeRiskScore": 0.44}, {"targetId": "target:a", "transitionSignalScore": 0.56, "collapseNarrativeRiskScore": 0.42}]}))

    for name in (
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
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/terrace_erosion_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/terrace_erosion_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_erosion_status_coverage() -> None:
    cases = [
        ("local", {"localErosionScore": 0.70, "synchronizedErosionScore": 0.50, "pluralityRetentionScore": 0.62}, {"orthodoxyPressureScore": 0.56}, {"renewalCorridorStrengthScore": 0.58, "boundedTrustRepairScore": 0.60}, {"transitionSignalScore": 0.56, "collapseNarrativeRiskScore": 0.44}, 0.34, 0.44, "erosion-local"),
        ("plurality", {"localErosionScore": 0.58, "synchronizedErosionScore": 0.54, "pluralityRetentionScore": 0.50}, {"orthodoxyPressureScore": 0.60}, {"renewalCorridorStrengthScore": 0.56, "boundedTrustRepairScore": 0.48}, {"transitionSignalScore": 0.56, "collapseNarrativeRiskScore": 0.44}, 0.36, 0.52, "plurality-repair"),
        ("renewal", {"localErosionScore": 0.52, "synchronizedErosionScore": 0.50, "pluralityRetentionScore": 0.66}, {"orthodoxyPressureScore": 0.52}, {"renewalCorridorStrengthScore": 0.74, "boundedTrustRepairScore": 0.68}, {"transitionSignalScore": 0.58, "collapseNarrativeRiskScore": 0.40}, 0.34, 0.44, "renewal-visible"),
        ("orthodoxy", {"localErosionScore": 0.58, "synchronizedErosionScore": 0.56, "pluralityRetentionScore": 0.50}, {"orthodoxyPressureScore": 0.74}, {"renewalCorridorStrengthScore": 0.56, "boundedTrustRepairScore": 0.56}, {"transitionSignalScore": 0.58, "collapseNarrativeRiskScore": 0.44}, 0.36, 0.52, "orthodoxy-risk"),
        ("watch", {"localErosionScore": 0.66, "synchronizedErosionScore": 0.74, "pluralityRetentionScore": 0.62}, {"orthodoxyPressureScore": 0.56}, {"renewalCorridorStrengthScore": 0.60, "boundedTrustRepairScore": 0.60}, {"transitionSignalScore": 0.70, "collapseNarrativeRiskScore": 0.44}, 0.36, 0.52, "phase-transition-watch"),
        ("review", {"localErosionScore": 0.52, "synchronizedErosionScore": 0.52, "pluralityRetentionScore": 0.68}, {"orthodoxyPressureScore": 0.52}, {"renewalCorridorStrengthScore": 0.58, "boundedTrustRepairScore": 0.60}, {"transitionSignalScore": 0.56, "collapseNarrativeRiskScore": 0.44}, 0.34, 0.44, "require-human-review"),
    ]
    got = set()
    for tid, row, orth, renew, trans, support_risk, trust_risk, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "terrace", **row},
            orthodoxy_rows={tid: orth},
            renewal_rows={tid: renew},
            transition_rows={tid: trans},
            support_risk=support_risk,
            trust_surface_risk=trust_risk,
        )
        got.add(d.erosion_status)
        assert d.erosion_status == expected
    assert got == {"erosion-local", "plurality-repair", "renewal-visible", "orthodoxy-risk", "phase-transition-watch", "require-human-review"}


def test_bounded_language_and_no_triumphalist_collapse_narrative() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "terrace", "localErosionScore": 0.56, "synchronizedErosionScore": 0.50, "pluralityRetentionScore": 0.64},
        orthodoxy_rows={"tone": {"orthodoxyPressureScore": 0.54}},
        renewal_rows={"tone": {"renewalCorridorStrengthScore": 0.74, "boundedTrustRepairScore": 0.68}},
        transition_rows={"tone": {"transitionSignalScore": 0.58, "collapseNarrativeRiskScore": 0.42}},
        support_risk=0.34,
        trust_surface_risk=0.44,
    )
    t = " ".join([d.terrace_context, d.orthodoxy_context, d.renewal_context, d.transition_context, d.commons_context, d.explanation]).lower()
    assert "bounded renewal-stewardship guidance" in t
    assert "non-coercive" in t
    assert "civilizational collapse confirmed" not in t
    assert "new age declared" not in t
    assert "inevitable successor order" not in t


def test_synchronized_erosion_orthodoxy_and_renewal_behaviors() -> None:
    sync = module.evaluate_target(
        {"targetId": "sync", "targetType": "terrace", "localErosionScore": 0.66, "synchronizedErosionScore": 0.74, "pluralityRetentionScore": 0.62},
        orthodoxy_rows={"sync": {"orthodoxyPressureScore": 0.56}},
        renewal_rows={"sync": {"renewalCorridorStrengthScore": 0.60, "boundedTrustRepairScore": 0.60}},
        transition_rows={"sync": {"transitionSignalScore": 0.70, "collapseNarrativeRiskScore": 0.44}},
        support_risk=0.36,
        trust_surface_risk=0.52,
    )
    orth = module.evaluate_target(
        {"targetId": "orth", "targetType": "terrace", "localErosionScore": 0.58, "synchronizedErosionScore": 0.56, "pluralityRetentionScore": 0.50},
        orthodoxy_rows={"orth": {"orthodoxyPressureScore": 0.74}},
        renewal_rows={"orth": {"renewalCorridorStrengthScore": 0.56, "boundedTrustRepairScore": 0.56}},
        transition_rows={"orth": {"transitionSignalScore": 0.58, "collapseNarrativeRiskScore": 0.44}},
        support_risk=0.36,
        trust_surface_risk=0.52,
    )
    renew = module.evaluate_target(
        {"targetId": "renew", "targetType": "terrace", "localErosionScore": 0.52, "synchronizedErosionScore": 0.50, "pluralityRetentionScore": 0.66},
        orthodoxy_rows={"renew": {"orthodoxyPressureScore": 0.52}},
        renewal_rows={"renew": {"renewalCorridorStrengthScore": 0.74, "boundedTrustRepairScore": 0.68}},
        transition_rows={"renew": {"transitionSignalScore": 0.58, "collapseNarrativeRiskScore": 0.40}},
        support_risk=0.34,
        trust_surface_risk=0.44,
    )
    assert sync.erosion_status == "phase-transition-watch"
    assert orth.erosion_status == "orthodoxy-risk"
    assert renew.erosion_status == "renewal-visible"


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/terrace_erosion_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "terrace"}]}))
    with pytest.raises(module.TerraceErosionInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/terrace_erosion_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "terrace"}]}))
    _write_json(tmp_path / "bridge/orthodoxy_pressure_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
