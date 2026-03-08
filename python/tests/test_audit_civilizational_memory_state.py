from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_civilizational_memory_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "civilizational_memory_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.civilizational_memory.fixture",
        "producerCommit": "fixture-av-0001",
        "generatedAt": "2026-04-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {
        "schema": "audit_fixture_v1",
        "created_at": "2026-04-08T00:00:00Z",
        "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)],
    }


def _manifest(overrides: dict | None = None) -> dict:
    manifest = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "memory-map->memory-audit->memory-overlay->ratification",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "Do not erase failed branches or dissent without disclosure.",
        "commonsIntegrityNotice": "Commons memory remains plural and publicly legible.",
        "constraintSignatureVersion": "av-1",
        "constraintSignatureSha256": "sha256:abababab",
    }
    if overrides:
        manifest.update(overrides)
    return manifest


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_MAP_PATH", tmp_path / "bridge/civilizational_memory_map.json")
    monkeypatch.setattr(module, "INTERGENERATIONAL_LEGIBILITY_REPORT_PATH", tmp_path / "bridge/intergenerational_legibility_report.json")
    monkeypatch.setattr(module, "EPISTEMIC_RESILIENCE_SCORECARD_PATH", tmp_path / "bridge/epistemic_resilience_scorecard.json")
    monkeypatch.setattr(module, "MEMORY_FRAGILITY_REPORT_PATH", tmp_path / "bridge/memory_fragility_report.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "THEORY_CORPUS_AUDIT_PATH", tmp_path / "bridge/theory_corpus_audit.json")
    monkeypatch.setattr(module, "REVIEW_PACKET_AUDIT_PATH", tmp_path / "bridge/review_packet_audit.json")
    monkeypatch.setattr(module, "RECOVERY_AUDIT_PATH", tmp_path / "bridge/recovery_audit.json")
    monkeypatch.setattr(module, "COMMONS_PARTICIPATION_AUDIT_PATH", tmp_path / "bridge/commons_participation_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/civilizational_memory_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "CIVILIZATIONAL_MEMORY_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/civilizational_memory_recommendations_v1.schema.json"),
    )


def _write_common_inputs(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write_json(
        bridge / "civilizational_memory_map.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "targetType": "memory", "continuityStrength": 0.70, "pluralMemorySupport": 0.68},
                    {"targetId": "target:a", "targetType": "memory", "continuityStrength": 0.62, "pluralMemorySupport": 0.60},
                ]
            }
        ),
    )
    _write_json(
        bridge / "intergenerational_legibility_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "intergenerationalLegibility": 0.68, "translationDurability": 0.66, "opacityRisk": 0.34},
                    {"targetId": "target:a", "intergenerationalLegibility": 0.60, "translationDurability": 0.58, "opacityRisk": 0.40},
                ]
            }
        ),
    )
    _write_json(
        bridge / "epistemic_resilience_scorecard.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "epistemicResilience": 0.70, "negativeResultPreservation": 0.66},
                    {"targetId": "target:a", "epistemicResilience": 0.62, "negativeResultPreservation": 0.58},
                ]
            }
        ),
    )
    _write_json(
        bridge / "memory_fragility_report.json",
        _artifact(
            {
                "targets": [
                    {"targetId": "target:z", "memoryFragility": 0.42, "archiveLossRisk": 0.40, "capturePressure": 0.34, "priesthoodOpacityRisk": 0.32, "canonClosurePressure": 0.30},
                    {"targetId": "target:a", "memoryFragility": 0.50, "archiveLossRisk": 0.48, "capturePressure": 0.42, "priesthoodOpacityRisk": 0.40, "canonClosurePressure": 0.38},
                ]
            }
        ),
    )

    for name in (
        "commons_sovereignty_audit.json",
        "theory_corpus_audit.json",
        "review_packet_audit.json",
        "recovery_audit.json",
        "commons_participation_audit.json",
    ):
        _write_json(bridge / name, _audit_rows([0.3, 0.4]))


def test_build_outputs_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    audit_payload, recommendations_payload = module.build_outputs()

    assert [item["targetId"] for item in audit_payload["records"]] == ["target:a", "target:z"]
    assert [item["targetId"] for item in recommendations_payload["recommendations"]] == ["target:a", "target:z"]

    audit_schema = json.loads(Path("/workspace/Sophia/schema/civilizational_memory_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads(Path("/workspace/Sophia/schema/civilizational_memory_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(recommendations_payload)


def test_status_coverage() -> None:
    cases = [
        (
            "stable",
            {"continuityStrength": 0.72, "pluralMemorySupport": 0.70},
            {"intergenerationalLegibility": 0.70, "translationDurability": 0.68, "opacityRisk": 0.32},
            {"epistemicResilience": 0.72, "negativeResultPreservation": 0.70},
            {"memoryFragility": 0.42, "archiveLossRisk": 0.40, "capturePressure": 0.34, "priesthoodOpacityRisk": 0.32, "canonClosurePressure": 0.30},
            "memory-stable",
        ),
        (
            "legibility",
            {"continuityStrength": 0.60, "pluralMemorySupport": 0.58},
            {"intergenerationalLegibility": 0.50, "translationDurability": 0.52, "opacityRisk": 0.44},
            {"epistemicResilience": 0.62, "negativeResultPreservation": 0.60},
            {"memoryFragility": 0.52, "archiveLossRisk": 0.50, "capturePressure": 0.42, "priesthoodOpacityRisk": 0.40, "canonClosurePressure": 0.38},
            "legibility-repair",
        ),
        (
            "fragility",
            {"continuityStrength": 0.60, "pluralMemorySupport": 0.58},
            {"intergenerationalLegibility": 0.62, "translationDurability": 0.60, "opacityRisk": 0.44},
            {"epistemicResilience": 0.62, "negativeResultPreservation": 0.34},
            {"memoryFragility": 0.60, "archiveLossRisk": 0.58, "capturePressure": 0.42, "priesthoodOpacityRisk": 0.40, "canonClosurePressure": 0.38},
            "fragility-watch",
        ),
        (
            "capture",
            {"continuityStrength": 0.58, "pluralMemorySupport": 0.56},
            {"intergenerationalLegibility": 0.60, "translationDurability": 0.58, "opacityRisk": 0.76},
            {"epistemicResilience": 0.60, "negativeResultPreservation": 0.58},
            {"memoryFragility": 0.56, "archiveLossRisk": 0.54, "capturePressure": 0.62, "priesthoodOpacityRisk": 0.76, "canonClosurePressure": 0.52},
            "capture-risk",
        ),
        (
            "human",
            {"continuityStrength": 0.58, "pluralMemorySupport": 0.56},
            {"intergenerationalLegibility": 0.60, "translationDurability": 0.58, "opacityRisk": 0.44},
            {"epistemicResilience": 0.60, "negativeResultPreservation": 0.58},
            {"memoryFragility": 0.56, "archiveLossRisk": 0.54, "capturePressure": 0.84, "priesthoodOpacityRisk": 0.62, "canonClosurePressure": 0.84},
            "require-human-review",
        ),
    ]

    statuses: set[str] = set()
    for target_id, row, legibility, resilience, fragility, expected in cases:
        decision = module.evaluate_target(
            {"targetId": target_id, "targetType": "memory", **row},
            legibility_rows={target_id: legibility},
            resilience_rows={target_id: resilience},
            fragility_rows={target_id: fragility},
            system_risk=0.35,
        )
        statuses.add(decision.memory_status)
        assert decision.memory_status == expected

    assert statuses == {"memory-stable", "legibility-repair", "fragility-watch", "capture-risk", "require-human-review"}


def test_bounded_non_sovereign_non_canonical_language() -> None:
    decision = module.evaluate_target(
        {"targetId": "tone", "targetType": "memory", "continuityStrength": 0.62, "pluralMemorySupport": 0.60},
        legibility_rows={"tone": {"intergenerationalLegibility": 0.60, "translationDurability": 0.58, "opacityRisk": 0.40}},
        resilience_rows={"tone": {"epistemicResilience": 0.62, "negativeResultPreservation": 0.58}},
        fragility_rows={"tone": {"memoryFragility": 0.50, "archiveLossRisk": 0.48, "capturePressure": 0.42, "priesthoodOpacityRisk": 0.40, "canonClosurePressure": 0.38}},
        system_risk=0.35,
    )

    text = " ".join([decision.continuity_context, decision.legibility_context, decision.fragility_context, decision.explanation]).lower()
    assert "bounded" in text
    assert "do not authorize erasure" in text
    assert "centralized historical authority" in text
    assert "final canonical closure" not in text


def test_negative_result_preservation_protection() -> None:
    decision = module.evaluate_target(
        {"targetId": "neg", "targetType": "memory", "continuityStrength": 0.64, "pluralMemorySupport": 0.62},
        legibility_rows={"neg": {"intergenerationalLegibility": 0.66, "translationDurability": 0.64, "opacityRisk": 0.34}},
        resilience_rows={"neg": {"epistemicResilience": 0.66, "negativeResultPreservation": 0.30}},
        fragility_rows={"neg": {"memoryFragility": 0.50, "archiveLossRisk": 0.48, "capturePressure": 0.42, "priesthoodOpacityRisk": 0.40, "canonClosurePressure": 0.38}},
        system_risk=0.35,
    )

    assert decision.memory_status == "fragility-watch"
    assert "failed branches" in decision.continuity_context.lower()


def test_memory_priesthood_opacity_handling() -> None:
    decision = module.evaluate_target(
        {"targetId": "opaque", "targetType": "memory", "continuityStrength": 0.62, "pluralMemorySupport": 0.60},
        legibility_rows={"opaque": {"intergenerationalLegibility": 0.62, "translationDurability": 0.60, "opacityRisk": 0.76}},
        resilience_rows={"opaque": {"epistemicResilience": 0.62, "negativeResultPreservation": 0.58}},
        fragility_rows={"opaque": {"memoryFragility": 0.56, "archiveLossRisk": 0.54, "capturePressure": 0.62, "priesthoodOpacityRisk": 0.76, "canonClosurePressure": 0.52}},
        system_risk=0.35,
    )

    assert decision.memory_status == "capture-risk"
    assert decision.target_publisher_action == "suppress"


def test_fail_closed_provenance_enforcement(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    bad = _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "memory"}]})
    _write_json(tmp_path / "bridge/civilizational_memory_map.json", bad)

    with pytest.raises(module.CivilizationalMemoryInputError):
        module.build_outputs()


def test_manifest_divergence_if_present(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)

    _write_json(
        tmp_path / "bridge/civilizational_memory_map.json",
        _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "memory"}]}),
    )
    _write_json(
        tmp_path / "bridge/intergenerational_legibility_report.json",
        _artifact({**_manifest({"ethicalBoundaryNotice": "Changed without signature rotation."}), "targets": [{"targetId": "target:a"}]}),
    )

    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
