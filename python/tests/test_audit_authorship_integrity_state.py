from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from sophia import audit_authorship_integrity_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _artifact(payload: dict | None = None) -> dict:
    base = {
        "schemaVersion": "authorship_integrity_v1",
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.authorship_integrity.fixture",
        "producerCommit": "fixture-bc1-0001",
        "generatedAt": "2026-06-08T00:00:00Z",
    }
    if payload:
        base.update(payload)
    return base


def _audit_rows(values: list[float]) -> dict:
    return {"schema": "audit_fixture_v1", "created_at": "2026-06-08T00:00:00Z", "records": [{"targetId": f"t{i}", "riskScore": v} for i, v in enumerate(values)]}


def _manifest(overrides: dict | None = None) -> dict:
    m = {
        "originProject": "CoherenceLattice",
        "canonicalPhaselock": "authorship-manifest->misattribution-audit->trust-overlay",
        "modificationDisclosureRequired": True,
        "ethicalBoundaryNotice": "No covert retaliation or sabotage.",
        "commonsIntegrityNotice": "Visible provenance and bounded disclosure only.",
        "constraintSignatureVersion": "bc1-1",
        "constraintSignatureSha256": "sha256:cdcdcdcd",
    }
    if overrides:
        m.update(overrides)
    return m


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "CANONICAL_AUTHORSHIP_MANIFEST_PATH", tmp_path / "bridge/canonical_authorship_manifest.json")
    monkeypatch.setattr(module, "DERIVATIVE_DISCLOSURE_REPORT_PATH", tmp_path / "bridge/derivative_disclosure_report.json")
    monkeypatch.setattr(module, "MISATTRIBUTION_RISK_REPORT_PATH", tmp_path / "bridge/misattribution_risk_report.json")
    monkeypatch.setattr(module, "AUTHORSHIP_INTEGRITY_SUMMARY_PATH", tmp_path / "bridge/authorship_integrity_summary.json")
    monkeypatch.setattr(module, "OBSERVER_ONBOARDING_AUDIT_PATH", tmp_path / "bridge/observer_onboarding_audit.json")
    monkeypatch.setattr(module, "COMMONS_SOVEREIGNTY_AUDIT_PATH", tmp_path / "bridge/commons_sovereignty_audit.json")
    monkeypatch.setattr(module, "CIVILIZATIONAL_MEMORY_AUDIT_PATH", tmp_path / "bridge/civilizational_memory_audit.json")
    monkeypatch.setattr(module, "KNOWLEDGE_RIVER_AUDIT_PATH", tmp_path / "bridge/knowledge_river_audit.json")
    monkeypatch.setattr(module, "AUTHORSHIP_INTEGRITY_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/authorship_integrity_audit_v1.schema.json"))
    monkeypatch.setattr(module, "AUTHORSHIP_INTEGRITY_RECOMMENDATIONS_SCHEMA_PATH", Path("/workspace/Sophia/schema/authorship_integrity_recommendations_v1.schema.json"))


def _write_common_inputs(tmp_path: Path) -> None:
    b = tmp_path / "bridge"
    _write_json(b / "canonical_authorship_manifest.json", _artifact({"targets": [{"targetId": "target:z", "targetType": "module", "canonicalAuthorshipVerified": True, "attributionPresent": True, "provenanceCompletenessScore": 0.78, "sourceLineageClarityScore": 0.76}, {"targetId": "target:a", "targetType": "module", "canonicalAuthorshipVerified": False, "attributionPresent": True, "provenanceCompletenessScore": 0.70, "sourceLineageClarityScore": 0.74}]}))
    _write_json(b / "derivative_disclosure_report.json", _artifact({"targets": [{"targetId": "target:z", "derivativeDisclosed": True, "derivativeDisclosureScore": 0.76, "safetyBoundariesDeclared": True, "modificationDisclosureComplete": True}, {"targetId": "target:a", "derivativeDisclosed": True, "derivativeDisclosureScore": 0.72, "safetyBoundariesDeclared": True, "modificationDisclosureComplete": True}]}))
    _write_json(b / "misattribution_risk_report.json", _artifact({"targets": [{"targetId": "target:z", "misattributionRiskScore": 0.22, "authorshipSuppressionDetected": False, "falsifiedAuthorshipDetected": False, "immutableConstraintsChangedWithoutDisclosure": False}, {"targetId": "target:a", "misattributionRiskScore": 0.32, "authorshipSuppressionDetected": False, "falsifiedAuthorshipDetected": False, "immutableConstraintsChangedWithoutDisclosure": False}]}))
    _write_json(b / "authorship_integrity_summary.json", _artifact({"targets": [{"targetId": "target:z", "trustIntegrityScore": 0.80}, {"targetId": "target:a", "trustIntegrityScore": 0.72}]}))

    for name in (
        "observer_onboarding_audit.json",
        "commons_sovereignty_audit.json",
        "civilizational_memory_audit.json",
        "knowledge_river_audit.json",
    ):
        _write_json(b / name, _audit_rows([0.2, 0.3]))


def test_schema_and_deterministic_order(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    audit_payload, rec_payload = module.build_outputs()
    assert [x["targetId"] for x in audit_payload["records"]] == ["target:a", "target:z"]
    assert [x["targetId"] for x in rec_payload["recommendations"]] == ["target:a", "target:z"]
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/authorship_integrity_audit_v1.schema.json").read_text())).validate(audit_payload)
    Draft202012Validator(json.loads(Path("/workspace/Sophia/schema/authorship_integrity_recommendations_v1.schema.json").read_text())).validate(rec_payload)


def test_full_status_coverage() -> None:
    cases = [
        ("verified", {"canonicalAuthorshipVerified": True, "attributionPresent": True, "provenanceCompletenessScore": 0.80, "sourceLineageClarityScore": 0.80}, {"derivativeDisclosed": True, "derivativeDisclosureScore": 0.80, "safetyBoundariesDeclared": True, "modificationDisclosureComplete": True}, {"misattributionRiskScore": 0.20}, {"trustIntegrityScore": 0.85}, "authorship-verified"),
        ("derivative", {"canonicalAuthorshipVerified": False, "attributionPresent": True, "provenanceCompletenessScore": 0.74, "sourceLineageClarityScore": 0.72}, {"derivativeDisclosed": True, "derivativeDisclosureScore": 0.72, "safetyBoundariesDeclared": True, "modificationDisclosureComplete": True}, {"misattributionRiskScore": 0.30}, {"trustIntegrityScore": 0.72}, "derivative-disclosed"),
        ("degraded", {"canonicalAuthorshipVerified": False, "attributionPresent": False, "provenanceCompletenessScore": 0.40, "sourceLineageClarityScore": 0.62}, {"derivativeDisclosed": False, "derivativeDisclosureScore": 0.30, "safetyBoundariesDeclared": False, "modificationDisclosureComplete": False}, {"misattributionRiskScore": 0.45}, {"trustIntegrityScore": 0.46}, "trust-degraded"),
        ("misattrib", {"canonicalAuthorshipVerified": False, "attributionPresent": True, "provenanceCompletenessScore": 0.66, "sourceLineageClarityScore": 0.66}, {"derivativeDisclosed": False, "derivativeDisclosureScore": 0.40, "safetyBoundariesDeclared": False, "modificationDisclosureComplete": False}, {"misattributionRiskScore": 0.82, "immutableConstraintsChangedWithoutDisclosure": True}, {"trustIntegrityScore": 0.40}, "misattribution-risk"),
        ("review", {"canonicalAuthorshipVerified": False, "attributionPresent": True, "provenanceCompletenessScore": 0.70, "sourceLineageClarityScore": 0.30, "conflictingProvenance": True}, {"derivativeDisclosed": True, "derivativeDisclosureScore": 0.70, "safetyBoundariesDeclared": True, "modificationDisclosureComplete": True}, {"misattributionRiskScore": 0.20}, {"trustIntegrityScore": 0.70}, "require-human-review"),
    ]
    got = set()
    for tid, row, disclosure, misattr, summary, expected in cases:
        d = module.evaluate_target(
            {"targetId": tid, "targetType": "module", **row},
            disclosure_rows={tid: disclosure},
            misattr_rows={tid: misattr},
            summary_rows={tid: summary},
            system_risk=0.25,
        )
        got.add(d.authorship_status)
        assert d.authorship_status == expected
    assert got == {"authorship-verified", "derivative-disclosed", "trust-degraded", "misattribution-risk", "require-human-review"}


def test_missing_attribution_derivative_and_immutable_divergence_handling() -> None:
    degraded = module.evaluate_target(
        {"targetId": "d", "targetType": "module", "canonicalAuthorshipVerified": False, "attributionPresent": False, "provenanceCompletenessScore": 0.55, "sourceLineageClarityScore": 0.65},
        disclosure_rows={"d": {"derivativeDisclosed": True, "derivativeDisclosureScore": 0.72, "safetyBoundariesDeclared": True, "modificationDisclosureComplete": True}},
        misattr_rows={"d": {"misattributionRiskScore": 0.36}},
        summary_rows={"d": {"trustIntegrityScore": 0.68}},
        system_risk=0.25,
    )
    derivative = module.evaluate_target(
        {"targetId": "x", "targetType": "module", "canonicalAuthorshipVerified": False, "attributionPresent": True, "provenanceCompletenessScore": 0.74, "sourceLineageClarityScore": 0.72},
        disclosure_rows={"x": {"derivativeDisclosed": True, "derivativeDisclosureScore": 0.75, "safetyBoundariesDeclared": True, "modificationDisclosureComplete": True}},
        misattr_rows={"x": {"misattributionRiskScore": 0.26}},
        summary_rows={"x": {"trustIntegrityScore": 0.74}},
        system_risk=0.25,
    )
    diverged = module.evaluate_target(
        {"targetId": "m", "targetType": "module", "canonicalAuthorshipVerified": False, "attributionPresent": True, "provenanceCompletenessScore": 0.70, "sourceLineageClarityScore": 0.70},
        disclosure_rows={"m": {"derivativeDisclosed": False, "derivativeDisclosureScore": 0.40, "safetyBoundariesDeclared": False, "modificationDisclosureComplete": False}},
        misattr_rows={"m": {"misattributionRiskScore": 0.70, "immutableConstraintsChangedWithoutDisclosure": True}},
        summary_rows={"m": {"trustIntegrityScore": 0.46}},
        system_risk=0.25,
    )
    assert degraded.authorship_status == "trust-degraded"
    assert derivative.authorship_status == "derivative-disclosed"
    assert diverged.authorship_status == "misattribution-risk"
    assert "trustPresentationDegraded = true" in diverged.divergence_context


def test_bounded_non_retaliatory_language() -> None:
    d = module.evaluate_target(
        {"targetId": "tone", "targetType": "module", "canonicalAuthorshipVerified": False, "attributionPresent": True, "provenanceCompletenessScore": 0.72, "sourceLineageClarityScore": 0.72},
        disclosure_rows={"tone": {"derivativeDisclosed": True, "derivativeDisclosureScore": 0.70, "safetyBoundariesDeclared": True, "modificationDisclosureComplete": True}},
        misattr_rows={"tone": {"misattributionRiskScore": 0.32}},
        summary_rows={"tone": {"trustIntegrityScore": 0.72}},
        system_risk=0.25,
    )
    t = " ".join([d.attribution_context, d.disclosure_context, d.divergence_context, d.capture_context, d.explanation]).lower()
    assert "non-retaliatory" in t
    assert "visible truth is preferred over hidden traps" in t
    for forbidden in ["sabotage", "covert exposure", "deletion", "punitive interference"]:
        assert forbidden not in d.attribution_context.lower()
        assert forbidden not in d.disclosure_context.lower()
        assert forbidden not in d.divergence_context.lower()
        assert forbidden not in d.capture_context.lower()


def test_fail_closed_provenance(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/canonical_authorship_manifest.json", _artifact({"producerCommit": "", "targets": [{"targetId": "target:a", "targetType": "module"}]}))
    with pytest.raises(module.AuthorshipIntegrityInputError):
        module.build_outputs()


def test_manifest_divergence_propagation(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_common_inputs(tmp_path)
    _write_json(tmp_path / "bridge/canonical_authorship_manifest.json", _artifact({**_manifest(), "targets": [{"targetId": "target:a", "targetType": "module"}]}))
    _write_json(tmp_path / "bridge/derivative_disclosure_report.json", _artifact({**_manifest({"ethicalBoundaryNotice": "changed"}), "targets": [{"targetId": "target:a"}]}))
    audit_payload, _ = module.build_outputs()
    assert audit_payload["metadata"]["canonicalIntegrity"]["status"] == "divergent"
