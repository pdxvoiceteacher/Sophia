from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_successor_delta_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "successor_delta_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.successor_delta.fixture",
        "producerCommit": "fixture-bh-0001",
        "generatedAt": "2026-11-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-11-08T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "renewal-braid->successor-delta-audit->overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No institutional overthrow or centralized succession.",
        "commonsIntegrityNotice": "Successor pathways remain plural and bounded.",
        "constraintSignatureVersion": "bh-1",
        "constraintSignatureSha256": "sha256:4545",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "RENEWAL_BRAID_MAP_PATH", tmp_path / "bridge/renewal_braid_map.json")
    monkeypatch.setattr(module, "SUCCESSOR_DELTA_SEED_REPORT_PATH", tmp_path / "bridge/successor_delta_seed_report.json")
    monkeypatch.setattr(module, "PLURALITY_RECOVERY_REGISTRY_PATH", tmp_path / "bridge/plurality_recovery_registry.json")
    monkeypatch.setattr(module, "TRANSITION_COUPLING_REPORT_PATH", tmp_path / "bridge/transition_coupling_report.json")
    monkeypatch.setattr(module, "TERRACE_EROSION_AUDIT_PATH", tmp_path / "bridge/terrace_erosion_audit.json")
    monkeypatch.setattr(module, "EPOCHAL_TERRACE_AUDIT_PATH", tmp_path / "bridge/epochal_terrace_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_DELTA_AUDIT_PATH", tmp_path / "bridge/civilizational_delta_audit.json")
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_AUDIT_PATH", tmp_path / "bridge/knowledge_river_audit.json")
    monkeypatch.setattr(module, "TRUST_SURFACE_AUDIT_PATH", tmp_path / "bridge/trust_surface_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "SUCCESSOR_DELTA_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/successor_delta_audit_v1.schema.json"))
    monkeypatch.setattr(module, "SUCCESSOR_DELTA_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/successor_delta_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(b / "renewal_braid_map.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "renewal", "renewalCorridorStrengthScore": 0.66, "braidSupportScore": 0.64}, {"targetId": "target:a", "targetType": "renewal", "renewalCorridorStrengthScore": 0.64, "braidSupportScore": 0.62}]}))
    _write_json(b / "successor_delta_seed_report.json", _artifact({"targets": [{"targetId": "target:z", "successorSeedStrengthScore": 0.66, "successorCaptureRiskScore": 0.40}, {"targetId": "target:a", "successorSeedStrengthScore": 0.64, "successorCaptureRiskScore": 0.42}]}))
    _write_json(b / "plurality_recovery_registry.json", _artifact({"targets": [{"targetId": "target:z", "pluralityRecoveryScore": 0.66, "suppressedPathwayReopeningScore": 0.64}, {"targetId": "target:a", "pluralityRecoveryScore": 0.64, "suppressedPathwayReopeningScore": 0.62}]}))
    _write_json(b / "transition_coupling_report.json", _artifact({"targets": [{"targetId": "target:z", "transitionCouplingScore": 0.62, "multiTerraceSynchronizationScore": 0.60}, {"targetId": "target:a", "transitionCouplingScore": 0.60, "multiTerraceSynchronizationScore": 0.58}]}))

    for name in (
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
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/successor_delta_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/successor_delta_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_successor_status_coverage() -> None:
    cases = [
        ("braid", {"renewalCorridorStrengthScore": 0.70, "braidSupportScore": 0.66}, {"successorSeedStrengthScore": 0.66, "successorCaptureRiskScore": 0.40}, {"pluralityRecoveryScore": 0.66, "suppressedPathwayReopeningScore": 0.66}, {"transitionCouplingScore": 0.62, "multiTerraceSynchronizationScore": 0.60}, 0.34, 0.44, "renewal-braiding"),
        ("seed", {"renewalCorridorStrengthScore": 0.72, "braidSupportScore": 0.68}, {"successorSeedStrengthScore": 0.74, "successorCaptureRiskScore": 0.40}, {"pluralityRecoveryScore": 0.66, "suppressedPathwayReopeningScore": 0.66}, {"transitionCouplingScore": 0.64, "multiTerraceSynchronizationScore": 0.62}, 0.34, 0.44, "successor-seed-visible"),
        ("plurality", {"renewalCorridorStrengthScore": 0.60, "braidSupportScore": 0.58}, {"successorSeedStrengthScore": 0.62, "successorCaptureRiskScore": 0.40}, {"pluralityRecoveryScore": 0.70, "suppressedPathwayReopeningScore": 0.70}, {"transitionCouplingScore": 0.58, "multiTerraceSynchronizationScore": 0.56}, 0.34, 0.44, "plurality-recovering"),
        ("capture", {"renewalCorridorStrengthScore": 0.72, "braidSupportScore": 0.68}, {"successorSeedStrengthScore": 0.74, "successorCaptureRiskScore": 0.80}, {"pluralityRecoveryScore": 0.66, "suppressedPathwayReopeningScore": 0.66}, {"transitionCouplingScore": 0.64, "multiTerraceSynchronizationScore": 0.62}, 0.34, 0.44, "successor-capture-risk"),
        ("watch", {"renewalCorridorStrengthScore": 0.66, "braidSupportScore": 0.64}, {"successorSeedStrengthScore": 0.66, "successorCaptureRiskScore": 0.40}, {"pluralityRecoveryScore": 0.66, "suppressedPathwayReopeningScore": 0.64}, {"transitionCouplingScore": 0.74, "multiTerraceSynchronizationScore": 0.70}, 0.36, 0.50, "phase-transition-watch"),
        ("review", {"renewalCorridorStrengthScore": 0.58, "braidSupportScore": 0.56}, {"successorSeedStrengthScore": 0.58, "successorCaptureRiskScore": 0.42}, {"pluralityRecoveryScore": 0.58, "suppressedPathwayReopeningScore": 0.56}, {"transitionCouplingScore": 0.58, "multiTerraceSynchronizationScore": 0.56}, 0.34, 0.44, "require-human-review"),
    ]
    got = set()
    for tid, row, seed, plurality, coupling, support_risk, trust_risk, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "renewal", **row},
            seed_rows={tid: seed},
            plurality_rows={tid: plurality},
            coupling_rows={tid: coupling},
            support_risk=support_risk,
            trust_surface_risk=trust_risk,
        )
        got.add(d.successor_status)
        assert d.successor_status == expected
    assert got == {"renewal-braiding", "successor-seed-visible", "plurality-recovering", "successor-capture-risk", "phase-transition-watch", "require-human-review"}


def test_bounded_language_and_non_sovereign_constraints() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "renewal", "renewalCorridorStrengthScore": 0.72, "braidSupportScore": 0.68},
        seed_rows={"tone": {"successorSeedStrengthScore": 0.74, "successorCaptureRiskScore": 0.40}},
        plurality_rows={"tone": {"pluralityRecoveryScore": 0.66, "suppressedPathwayReopeningScore": 0.66}},
        coupling_rows={"tone": {"transitionCouplingScore": 0.64, "multiTerraceSynchronizationScore": 0.62}},
        support_risk=0.34,
        trust_surface_risk=0.44,
    )
    t = " ".join([d.renewal_context, d.seed_context, d.plurality_context, d.coupling_context, d.commons_context, d.explanation]).lower()
    assert "bounded successor-renewal guidance" in t
    assert "non-coercive" in t
    assert "new epoch arrived" not in t
    assert "successor order confirmed" not in t
    assert "historical replacement complete" not in t


def test_renewal_braiding_plurality_capture_and_watch_behaviors() -> None:
    braid = module.evaluate_target(
        {"targetId": "braid", "targetType": "renewal", "renewalCorridorStrengthScore": 0.70, "braidSupportScore": 0.66},
        seed_rows={"braid": {"successorSeedStrengthScore": 0.66, "successorCaptureRiskScore": 0.40}},
        plurality_rows={"braid": {"pluralityRecoveryScore": 0.66, "suppressedPathwayReopeningScore": 0.66}},
        coupling_rows={"braid": {"transitionCouplingScore": 0.62, "multiTerraceSynchronizationScore": 0.60}},
        support_risk=0.34,
        trust_surface_risk=0.44,
    )
    capture = module.evaluate_target(
        {"targetId": "capture", "targetType": "renewal", "renewalCorridorStrengthScore": 0.72, "braidSupportScore": 0.68},
        seed_rows={"capture": {"successorSeedStrengthScore": 0.74, "successorCaptureRiskScore": 0.82}},
        plurality_rows={"capture": {"pluralityRecoveryScore": 0.66, "suppressedPathwayReopeningScore": 0.66}},
        coupling_rows={"capture": {"transitionCouplingScore": 0.64, "multiTerraceSynchronizationScore": 0.62}},
        support_risk=0.34,
        trust_surface_risk=0.44,
    )
    watch = module.evaluate_target(
        {"targetId": "watch", "targetType": "renewal", "renewalCorridorStrengthScore": 0.66, "braidSupportScore": 0.64},
        seed_rows={"watch": {"successorSeedStrengthScore": 0.66, "successorCaptureRiskScore": 0.40}},
        plurality_rows={"watch": {"pluralityRecoveryScore": 0.66, "suppressedPathwayReopeningScore": 0.64}},
        coupling_rows={"watch": {"transitionCouplingScore": 0.74, "multiTerraceSynchronizationScore": 0.70}},
        support_risk=0.36,
        trust_surface_risk=0.50,
    )
    assert braid.successor_status == "renewal-braiding"
    assert capture.successor_status == "successor-capture-risk"
    assert watch.successor_status == "phase-transition-watch"


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/renewal_braid_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "renewal"}]}))
    with pytest.raises(module.SuccessorDeltaInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/renewal_braid_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "renewal"}]}))
    _write_json(tmp_path / "bridge/successor_delta_seed_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
