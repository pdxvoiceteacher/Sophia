from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_trust_surface_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "trust_surface_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.trust_surface.fixture",
        "producerCommit": "fixture-bd-0001",
        "generatedAt": "2026-07-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-07-08T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "trust-surface-map->trust-surface-audit->overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No blame assignment from structural audits.",
        "commonsIntegrityNotice": "Bounded legitimacy guidance only.",
        "constraintSignatureVersion": "bd-1",
        "constraintSignatureSha256": "sha256:edededed",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "TRUST_SURFACE_MAP_PATH", tmp_path / "bridge/trust_surface_map.json")
    monkeypatch.setattr(module, "DELEGATED_ACCESS_REGISTRY_PATH", tmp_path / "bridge/delegated_access_registry.json")
    monkeypatch.setattr(module, "REVOCATION_ASYMMETRY_REPORT_PATH", tmp_path / "bridge/revocation_asymmetry_report.json")
    monkeypatch.setattr(module, "INTERFACE_LEGITIMACY_RISK_REPORT_PATH", tmp_path / "bridge/interface_legitimacy_risk_report.json")
    monkeypatch.setattr(module, "OBSERVER_ONBOARDING_AUDIT_PATH", tmp_path / "bridge/observer_onboarding_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "TRUST_SURFACE_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/trust_surface_audit_v1.schema.json"))
    monkeypatch.setattr(module, "TRUST_SURFACE_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/trust_surface_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(b / "trust_surface_map.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "interface", "consentLegibilityScore": 0.72, "trustCompressionRisk": 0.34}, {"targetId": "target:a", "targetType": "interface", "consentLegibilityScore": 0.64, "trustCompressionRisk": 0.40}]}))
    _write_json(b / "delegated_access_registry.json", _artifact({"targets": [{"targetId": "target:z", "wrapperLineageClarityScore": 0.72, "provenanceTraceabilityScore": 0.72}, {"targetId": "target:a", "wrapperLineageClarityScore": 0.66, "provenanceTraceabilityScore": 0.64}]}))
    _write_json(b / "revocation_asymmetry_report.json", _artifact({"targets": [{"targetId": "target:z", "revocationAsymmetryScore": 0.40, "revocationProcessComplexityScore": 0.42, "multiSystemInvestigationRequired": False}, {"targetId": "target:a", "revocationAsymmetryScore": 0.54, "revocationProcessComplexityScore": 0.58, "multiSystemInvestigationRequired": False}]}))
    _write_json(b / "interface_legitimacy_risk_report.json", _artifact({"targets": [{"targetId": "target:z", "interfaceLegitimacyRiskScore": 0.34}, {"targetId": "target:a", "interfaceLegitimacyRiskScore": 0.42}]}))

    for name in ("observer_onboarding_audit.json", "commons_sovereignty_audit.json", "civilizational_memory_audit.json"):
        _write_json(b / name, _audit_rows([0.2, 0.3]))


def test_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    audit_payload, rec_payload = module.build_outputs()
    assert [x["targetId"] for x in audit_payload["records"]] == ["target:a", "target:z"]
    assert [x["targetId"] for x in rec_payload["recommendations"]] == ["target:a", "target:z"]
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/trust_surface_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/trust_surface_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_status_coverage() -> None:
    cases = [
        ("stable", {"consentLegibilityScore": 0.74, "trustCompressionRisk": 0.30}, {"wrapperLineageClarityScore": 0.74, "provenanceTraceabilityScore": 0.74}, {"revocationAsymmetryScore": 0.42, "revocationProcessComplexityScore": 0.40, "multiSystemInvestigationRequired": False}, {"interfaceLegitimacyRiskScore": 0.34}, "trust-surface-stable"),
        ("legitimacy", {"consentLegibilityScore": 0.38, "trustCompressionRisk": 0.72}, {"wrapperLineageClarityScore": 0.72, "provenanceTraceabilityScore": 0.72}, {"revocationAsymmetryScore": 0.52, "revocationProcessComplexityScore": 0.50, "multiSystemInvestigationRequired": False}, {"interfaceLegitimacyRiskScore": 0.72}, "legitimacy-risk"),
        ("revocation", {"consentLegibilityScore": 0.62, "trustCompressionRisk": 0.42}, {"wrapperLineageClarityScore": 0.64, "provenanceTraceabilityScore": 0.64}, {"revocationAsymmetryScore": 0.70, "revocationProcessComplexityScore": 0.66, "multiSystemInvestigationRequired": False}, {"interfaceLegitimacyRiskScore": 0.44}, "revocation-asymmetry-risk"),
        ("wrapper", {"consentLegibilityScore": 0.66, "trustCompressionRisk": 0.44}, {"wrapperLineageClarityScore": 0.28, "provenanceTraceabilityScore": 0.30}, {"revocationAsymmetryScore": 0.58, "revocationProcessComplexityScore": 0.56, "multiSystemInvestigationRequired": False}, {"interfaceLegitimacyRiskScore": 0.44}, "wrapper-provenance-risk"),
        ("review", {"consentLegibilityScore": 0.64, "trustCompressionRisk": 0.44}, {"wrapperLineageClarityScore": 0.64, "provenanceTraceabilityScore": 0.64}, {"revocationAsymmetryScore": 0.84, "revocationProcessComplexityScore": 0.76, "multiSystemInvestigationRequired": True}, {"interfaceLegitimacyRiskScore": 0.44}, "require-human-review"),
    ]
    got = set()
    for tid, row, delegated, revocation, legitimacy, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "interface", **row},
            delegated_rows={tid: delegated},
            revocation_rows={tid: revocation},
            legitimacy_rows={tid: legitimacy},
            system_risk=0.25,
        )
        got.add(d.trust_surface_status)
        assert d.trust_surface_status == expected
    assert got == {"trust-surface-stable", "legitimacy-risk", "revocation-asymmetry-risk", "wrapper-provenance-risk", "require-human-review"}


def test_structural_legitimacy_no_blame_language() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "interface", "consentLegibilityScore": 0.40, "trustCompressionRisk": 0.70},
        delegated_rows={"tone": {"wrapperLineageClarityScore": 0.70, "provenanceTraceabilityScore": 0.70}},
        revocation_rows={"tone": {"revocationAsymmetryScore": 0.56, "revocationProcessComplexityScore": 0.58, "multiSystemInvestigationRequired": True}},
        legitimacy_rows={"tone": {"interfaceLegitimacyRiskScore": 0.70}},
        system_risk=0.30,
    )
    t = " ".join([d.legitimacy_context, d.revocation_context, d.wrapper_context, d.audit_burden_context, d.explanation]).lower()
    assert "structural legitimacy" in t
    assert "do not imply wrongdoing" in t
    assert "authorize enforcement" in t


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/trust_surface_map.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "interface"}]}))
    with pytest.raises(module.TrustSurfaceInputError):
        module.build_outputs()


def test_manifest_divergence(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/trust_surface_map.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "interface"}]}))
    _write_json(tmp_path / "bridge/delegated_access_registry.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
