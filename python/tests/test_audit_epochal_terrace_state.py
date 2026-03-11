from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_epochal_terrace_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "epochal_terrace_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.epochal_terrace.fixture",
        "producerCommit": "fixture-bf-0001",
        "generatedAt": "2026-09-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-09-08T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "terrace-map->terrace-audit->terrace-overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No canon closure or institutional consolidation.",
        "commonsIntegrityNotice": "Terraces remain plural and repairable.",
        "constraintSignatureVersion": "bf-1",
        "constraintSignatureSha256": "sha256:ababcdcd",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "EPOCHAL_TERRACE_MAP_PATH", tmp_path / "bridge/epochal_terrace_map.json")
    monkeypatch.setattr(module, "STABILITY_PLATEAU_REPORT_PATH", tmp_path / "bridge/stability_plateau_report.json")
    monkeypatch.setattr(module, "INSTITUTIONAL_SEDIMENTATION_REGISTRY_PATH", tmp_path / "bridge/institutional_sedimentation_registry.json")
    monkeypatch.setattr(module, "TERRACE_EROSION_RISK_REPORT_PATH", tmp_path / "bridge/terrace_erosion_risk_report.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_DELTA_AUDIT_PATH", tmp_path / "bridge/civilizational_delta_audit.json")
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_AUDIT_PATH", tmp_path / "bridge/knowledge_river_audit.json")
    monkeypatch.setattr(module, "TRUST_SURFACE_AUDIT_PATH", tmp_path / "bridge/trust_surface_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "EPOCHAL_TERRACE_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/epochal_terrace_audit_v1.schema.json"))
    monkeypatch.setattr(module, "EPOCHAL_TERRACE_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/epochal_terrace_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(b / "epochal_terrace_map.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "terrace", "terraceMaturityScore": 0.66, "pluralityRetentionScore": 0.64, "repairabilityScore": 0.66}, {"targetId": "target:a", "targetType": "terrace", "terraceMaturityScore": 0.60, "pluralityRetentionScore": 0.62, "repairabilityScore": 0.62}]}))
    _write_json(b / "stability_plateau_report.json", _artifact({"targets": [{"targetId": "target:z", "plateauStabilityScore": 0.66, "institutionalEmbedmentScore": 0.62}, {"targetId": "target:a", "plateauStabilityScore": 0.62, "institutionalEmbedmentScore": 0.60}]}))
    _write_json(b / "institutional_sedimentation_registry.json", _artifact({"targets": [{"targetId": "target:z", "sedimentClass": "balanced", "sedimentationOverhardeningScore": 0.40}, {"targetId": "target:a", "sedimentClass": "balanced", "sedimentationOverhardeningScore": 0.44}]}))
    _write_json(b / "terrace_erosion_risk_report.json", _artifact({"targets": [{"targetId": "target:z", "terraceErosionRiskScore": 0.40, "erosionVelocityScore": 0.42}, {"targetId": "target:a", "terraceErosionRiskScore": 0.44, "erosionVelocityScore": 0.46}]}))

    for name in (
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
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/epochal_terrace_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/epochal_terrace_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_terrace_status_coverage() -> None:
    cases = [
        ("forming", {"terraceMaturityScore": 0.60, "pluralityRetentionScore": 0.62, "repairabilityScore": 0.62}, {"plateauStabilityScore": 0.58, "institutionalEmbedmentScore": 0.56}, {"sedimentClass": "balanced", "sedimentationOverhardeningScore": 0.44}, {"terraceErosionRiskScore": 0.44, "erosionVelocityScore": 0.44}, 0.34, 0.42, "terrace-forming"),
        ("stable", {"terraceMaturityScore": 0.74, "pluralityRetentionScore": 0.68, "repairabilityScore": 0.66}, {"plateauStabilityScore": 0.72, "institutionalEmbedmentScore": 0.64}, {"sedimentClass": "balanced", "sedimentationOverhardeningScore": 0.42}, {"terraceErosionRiskScore": 0.40, "erosionVelocityScore": 0.40}, 0.34, 0.44, "plateau-stable"),
        ("plurality", {"terraceMaturityScore": 0.70, "pluralityRetentionScore": 0.50, "repairabilityScore": 0.58}, {"plateauStabilityScore": 0.70, "institutionalEmbedmentScore": 0.78}, {"sedimentClass": "overhardened", "sedimentationOverhardeningScore": 0.76}, {"terraceErosionRiskScore": 0.56, "erosionVelocityScore": 0.58}, 0.36, 0.52, "plurality-repair"),
        ("erosion", {"terraceMaturityScore": 0.68, "pluralityRetentionScore": 0.62, "repairabilityScore": 0.60}, {"plateauStabilityScore": 0.68, "institutionalEmbedmentScore": 0.66}, {"sedimentClass": "overhardened", "sedimentationOverhardeningScore": 0.78}, {"terraceErosionRiskScore": 0.78, "erosionVelocityScore": 0.76}, 0.36, 0.72, "erosion-risk"),
        ("review", {"terraceMaturityScore": 0.40, "pluralityRetentionScore": 0.48, "repairabilityScore": 0.44}, {"plateauStabilityScore": 0.42, "institutionalEmbedmentScore": 0.54}, {"sedimentClass": "balanced", "sedimentationOverhardeningScore": 0.48}, {"terraceErosionRiskScore": 0.50, "erosionVelocityScore": 0.52}, 0.40, 0.50, "require-human-review"),
    ]
    got = set()
    for tid, row, plateau, sediment, erosion, support_risk, trust_risk, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "terrace", **row},
            plateau_rows={tid: plateau},
            sediment_rows={tid: sediment},
            erosion_rows={tid: erosion},
            support_risk=support_risk,
            trust_surface_risk=trust_risk,
        )
        got.add(d.terrace_status)
        assert d.terrace_status == expected
    assert got == {"terrace-forming", "plateau-stable", "plurality-repair", "erosion-risk", "require-human-review"}


def test_bounded_non_sovereign_language() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "terrace", "terraceMaturityScore": 0.72, "pluralityRetentionScore": 0.68, "repairabilityScore": 0.66},
        plateau_rows={"tone": {"plateauStabilityScore": 0.70, "institutionalEmbedmentScore": 0.64}},
        sediment_rows={"tone": {"sedimentClass": "balanced", "sedimentationOverhardeningScore": 0.42}},
        erosion_rows={"tone": {"terraceErosionRiskScore": 0.42, "erosionVelocityScore": 0.42}},
        support_risk=0.34,
        trust_surface_risk=0.44,
    )
    t = " ".join([d.terrace_context, d.plateau_context, d.sedimentation_context, d.erosion_context, d.commons_context, d.explanation]).lower()
    assert "bounded terrace-stewardship guidance" in t
    assert "plural" in t
    assert "repairable" in t
    assert "civilization settled" not in t
    assert "final epoch" not in t
    assert "permanent order" not in t


def test_plurality_repair_trust_surface_and_overhardening() -> None:
    plurality = module.evaluate_target(
        {"targetId": "p", "targetType": "terrace", "terraceMaturityScore": 0.70, "pluralityRetentionScore": 0.50, "repairabilityScore": 0.58},
        plateau_rows={"p": {"plateauStabilityScore": 0.70, "institutionalEmbedmentScore": 0.78}},
        sediment_rows={"p": {"sedimentClass": "overhardened", "sedimentationOverhardeningScore": 0.76}},
        erosion_rows={"p": {"terraceErosionRiskScore": 0.56, "erosionVelocityScore": 0.58}},
        support_risk=0.36,
        trust_surface_risk=0.52,
    )
    erosion = module.evaluate_target(
        {"targetId": "e", "targetType": "terrace", "terraceMaturityScore": 0.68, "pluralityRetentionScore": 0.62, "repairabilityScore": 0.60},
        plateau_rows={"e": {"plateauStabilityScore": 0.68, "institutionalEmbedmentScore": 0.66}},
        sediment_rows={"e": {"sedimentClass": "overhardened", "sedimentationOverhardeningScore": 0.78}},
        erosion_rows={"e": {"terraceErosionRiskScore": 0.78, "erosionVelocityScore": 0.76}},
        support_risk=0.36,
        trust_surface_risk=0.74,
    )
    assert plurality.terrace_status == "plurality-repair"
    assert erosion.terrace_status == "erosion-risk"
    assert erosion.target_publisher_action in {"watch", "suppress"}


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/epochal_terrace_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "terrace"}]}))
    with pytest.raises(module.EpochalTerraceInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/epochal_terrace_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "terrace"}]}))
    _write_json(tmp_path / "bridge/stability_plateau_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
