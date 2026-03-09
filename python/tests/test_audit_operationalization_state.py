from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_operationalization_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "operationalization_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.operationalization.fixture",
        "producerCommit": "fixture-ax-0001",
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
        "canonicalPhaselock": "maturity-map->operationalization-audit->deployment-overlay->deliberation",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No coercive deployment without disclosure and review.",
        "commonsIntegrityNotice": "Operational overlays remain bounded and reviewable.",
        "constraintSignatureVersion": "ax-1",
        "constraintSignatureSha256": "sha256:efefefef",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "OPERATIONAL_MATURITY_MAP_PATH", tmp_path / "bridge/operational_maturity_map.json")
    monkeypatch.setattr(module, "DEPLOYMENT_BOUNDARY_REPORT_PATH", tmp_path / "bridge/deployment_boundary_report.json")
    monkeypatch.setattr(module, "TRANSLATION_RISK_REGISTER_PATH", tmp_path / "bridge/translation_risk_register.json")
    monkeypatch.setattr(module, "OPERATIONALIZATION_GATE_PATH", tmp_path / "bridge/operationalization_gate.json")
    monkeypatch.setattr(module, "EPISTEMIC_ATTRACTOR_AUDIT_PATH", tmp_path / "bridge/epistemic_attractor_audit.json")
    monkeypatch.setattr(module, "EMERGENT_DOMAIN_AUDIT_PATH", tmp_path / "bridge/emergent_domain_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "VALUE_ALIGNMENT_AUDIT_PATH", tmp_path / "bridge/value_alignment_audit.json")
    monkeypatch.setattr(module, "OPERATIONALIZATION_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/operationalization_audit_v1.schema.json"))
    monkeypatch.setattr(module, "OPERATIONALIZATION_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/operationalization_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(b / "operational_maturity_map.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "deployment", "operationalMaturity": 0.64, "safeguardReadiness": 0.62}, {"targetId": "target:a", "targetType": "deployment", "operationalMaturity": 0.56, "safeguardReadiness": 0.56}]}))
    _write_json(b / "deployment_boundary_report.json", _artifact({"targets": [{"targetId": "target:z", "deploymentBoundaryClarity": 0.66, "coerciveAmplificationRisk": 0.40, "deadZoneAdjacency": 0.38}, {"targetId": "target:a", "deploymentBoundaryClarity": 0.58, "coerciveAmplificationRisk": 0.46, "deadZoneAdjacency": 0.44}]}))
    _write_json(b / "translation_risk_register.json", _artifact({"targets": [{"targetId": "target:z", "institutionalTranslationRisk": 0.44, "governanceOverrideRisk": 0.40}, {"targetId": "target:a", "institutionalTranslationRisk": 0.50, "governanceOverrideRisk": 0.46}]}))
    _write_json(b / "operationalization_gate.json", _artifact({"targets": [{"targetId": "target:z", "operationalGateScore": 0.68, "automaticDeploymentSignal": 0.36}, {"targetId": "target:a", "operationalGateScore": 0.60, "automaticDeploymentSignal": 0.42}]}))
    for name in ("epistemic_attractor_audit.json", "emergent_domain_audit.json", "commons_sovereignty_audit.json", "civilizational_memory_audit.json", "value_alignment_audit.json"):
        _write_json(b / name, _audit_rows([0.3, 0.4]))


def test_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    audit_payload, rec_payload = module.build_outputs()
    assert [x["targetId"] for x in audit_payload["records"]] == ["target:a", "target:z"]
    assert [x["targetId"] for x in rec_payload["recommendations"]] == ["target:a", "target:z"]
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/operationalization_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/operationalization_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_status_coverage() -> None:
    cases = [
        ("research", {"operationalMaturity": 0.48, "safeguardReadiness": 0.50}, {"deploymentBoundaryClarity": 0.56, "coerciveAmplificationRisk": 0.42, "deadZoneAdjacency": 0.44}, {"institutionalTranslationRisk": 0.44, "governanceOverrideRisk": 0.40}, {"operationalGateScore": 0.54, "automaticDeploymentSignal": 0.38}, "research-only"),
        ("pilot", {"operationalMaturity": 0.60, "safeguardReadiness": 0.58}, {"deploymentBoundaryClarity": 0.60, "coerciveAmplificationRisk": 0.42, "deadZoneAdjacency": 0.44}, {"institutionalTranslationRisk": 0.44, "governanceOverrideRisk": 0.40}, {"operationalGateScore": 0.60, "automaticDeploymentSignal": 0.38}, "bounded-pilot"),
        ("translation", {"operationalMaturity": 0.62, "safeguardReadiness": 0.60}, {"deploymentBoundaryClarity": 0.62, "coerciveAmplificationRisk": 0.46, "deadZoneAdjacency": 0.76}, {"institutionalTranslationRisk": 0.72, "governanceOverrideRisk": 0.44}, {"operationalGateScore": 0.62, "automaticDeploymentSignal": 0.42}, "translation-risk"),
        ("review", {"operationalMaturity": 0.68, "safeguardReadiness": 0.66}, {"deploymentBoundaryClarity": 0.68, "coerciveAmplificationRisk": 0.44, "deadZoneAdjacency": 0.40}, {"institutionalTranslationRisk": 0.54, "governanceOverrideRisk": 0.44}, {"operationalGateScore": 0.74, "automaticDeploymentSignal": 0.40}, "deployment-review"),
        ("human", {"operationalMaturity": 0.68, "safeguardReadiness": 0.66}, {"deploymentBoundaryClarity": 0.66, "coerciveAmplificationRisk": 0.84, "deadZoneAdjacency": 0.44}, {"institutionalTranslationRisk": 0.58, "governanceOverrideRisk": 0.84}, {"operationalGateScore": 0.74, "automaticDeploymentSignal": 0.84}, "require-human-review"),
    ]
    got = set()
    for tid, row, boundary, translation, gate, expected in cases:
        d = module.evaluate_target({"targetId": tid, "targetType": "deployment", **row}, boundary_rows={tid: boundary}, translation_rows={tid: translation}, gate_rows={tid: gate}, system_risk=0.35)
        got.add(d.operational_status)
        assert d.operational_status == expected
    assert got == {"research-only", "bounded-pilot", "translation-risk", "deployment-review", "require-human-review"}


def test_bounded_non_sovereign_language() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "deployment", "operationalMaturity": 0.60, "safeguardReadiness": 0.58},
        boundary_rows={"tone": {"deploymentBoundaryClarity": 0.60, "coerciveAmplificationRisk": 0.42, "deadZoneAdjacency": 0.44}},
        translation_rows={"tone": {"institutionalTranslationRisk": 0.44, "governanceOverrideRisk": 0.40}},
        gate_rows={"tone": {"operationalGateScore": 0.60, "automaticDeploymentSignal": 0.38}},
        system_risk=0.35,
    )
    t = " ".join([d.maturity_context, d.boundary_context, d.translation_risk_context, d.commons_context, d.explanation]).lower()
    assert "bounded" in t
    assert "do not authorize automatic implementation" in t
    assert "coercive operationalization" in t


def test_dead_zone_adjacency_and_anti_coercion() -> None:
    dead = module.evaluate_target(
        {"targetId": "dead", "targetType": "deployment", "operationalMaturity": 0.62, "safeguardReadiness": 0.60},
        boundary_rows={"dead": {"deploymentBoundaryClarity": 0.62, "coerciveAmplificationRisk": 0.46, "deadZoneAdjacency": 0.78}},
        translation_rows={"dead": {"institutionalTranslationRisk": 0.54, "governanceOverrideRisk": 0.44}},
        gate_rows={"dead": {"operationalGateScore": 0.62, "automaticDeploymentSignal": 0.42}},
        system_risk=0.35,
    )
    coercive = module.evaluate_target(
        {"targetId": "coerce", "targetType": "deployment", "operationalMaturity": 0.66, "safeguardReadiness": 0.64},
        boundary_rows={"coerce": {"deploymentBoundaryClarity": 0.66, "coerciveAmplificationRisk": 0.84, "deadZoneAdjacency": 0.44}},
        translation_rows={"coerce": {"institutionalTranslationRisk": 0.58, "governanceOverrideRisk": 0.84}},
        gate_rows={"coerce": {"operationalGateScore": 0.74, "automaticDeploymentSignal": 0.84}},
        system_risk=0.35,
    )
    assert dead.operational_status == "translation-risk"
    assert coercive.operational_status == "require-human-review"
    assert coercive.target_publisher_action == "suppress"


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/operational_maturity_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "deployment"}]}))
    with pytest.raises(module.OperationalizationInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/operational_maturity_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "deployment"}]}))
    _write_json(tmp_path / "bridge/deployment_boundary_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
