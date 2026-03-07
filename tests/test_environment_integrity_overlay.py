from __future__ import annotations

import json
from pathlib import Path

from scripts import build_environment_integrity_overlay as mod


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _patch(tmp_path: Path, monkeypatch) -> None:
    bridge = tmp_path / "bridge"
    reg = tmp_path / "registry"
    schema = Path(__file__).resolve().parents[1] / "schema"
    monkeypatch.setattr(mod, "BRIDGE_DIR", bridge)
    monkeypatch.setattr(mod, "REGISTRY_DIR", reg)
    monkeypatch.setattr(mod, "INPUTS", {
        "audit": bridge / "environment_audit.json",
        "recommendations": bridge / "environment_recommendations.json",
        "environment": bridge / "environment_integrity_map.json",
        "anomaly": bridge / "anomaly_domain_map.json",
        "maturity": bridge / "evidence_maturity_report.json",
        "counter": bridge / "counter_hypothesis_map.json",
        "verification_dashboard": reg / "verification_dashboard.json",
        "public_dashboard": reg / "public_record_dashboard.json",
        "symbolic_registry": reg / "symbolic_field_registry.json",
    })
    monkeypatch.setattr(mod, "OUTPUTS", {
        "dashboard": reg / "environment_integrity_dashboard.json",
        "watchlist": reg / "anomaly_watchlist.json",
        "maturity": reg / "evidence_maturity_registry.json",
        "annotations": reg / "counter_hypothesis_annotations.json",
    })
    monkeypatch.setattr(mod, "SCHEMAS", {
        "dashboard": schema / "environment_integrity_dashboard_v1.schema.json",
        "watchlist": schema / "anomaly_watchlist_v1.schema.json",
        "maturity": schema / "evidence_maturity_registry_v1.schema.json",
        "annotations": schema / "counter_hypothesis_annotations_v1.schema.json",
    })

    base = {"schemaVersion": "x", "producerRepo": "Sophia", "producerModule": "tests", "producerCommit": "t", "generatedAt": "2026-04-01T00:00:00Z"}
    _write(bridge / "environment_audit.json", {**base, "records": []})
    _write(bridge / "environment_recommendations.json", {**base, "records": [
        {"targetId": "target:a", "targetPublisherAction": "docket"},
        {"targetId": "target:b", "targetPublisherAction": "watch"},
        {"targetId": "target:c", "targetPublisherAction": "suppress"},
    ]})
    _write(bridge / "environment_integrity_map.json", {**base, "targets": [
        {"targetId": "target:a", "anomalyDomain": "digital", "attackSurfaceClass": "platform", "environmentIntegrityScore": 0.9, "requiresExecutiveReview": False, "provenanceMarkers": ["verification"]},
        {"targetId": "target:b", "anomalyDomain": "mixed", "attackSurfaceClass": "social", "environmentIntegrityScore": 0.3, "requiresExecutiveReview": True, "provenanceMarkers": ["verification", "symbolic"]},
    ]})
    _write(bridge / "anomaly_domain_map.json", {**base, "targets": []})
    _write(bridge / "evidence_maturity_report.json", {**base, "targets": [
        {"targetId": "target:a", "maturityClass": "independently_verified", "maturityScore": 0.8, "missingVerificationSteps": [], "provenanceMarkers": ["public_record"]},
        {"targetId": "target:b", "maturityClass": "artifact", "maturityScore": 0.2, "missingVerificationSteps": ["repeat_test"], "provenanceMarkers": ["public_record"]},
    ]})
    _write(bridge / "counter_hypothesis_map.json", {**base, "targets": [
        {"targetId": "target:a", "primaryHypothesis": "h1", "counterHypotheses": ["h2", "h3"], "recommendedClass": "watch", "provenanceMarkers": ["claim"]},
        {"targetId": "target:b", "primaryHypothesis": "h1", "counterHypotheses": ["h2"], "recommendedClass": "verify", "provenanceMarkers": ["claim"]},
    ]})
    _write(reg / "verification_dashboard.json", {**base, "schemaVersion": "verification_dashboard_v1"})
    _write(reg / "public_record_dashboard.json", {**base, "schemaVersion": "public_record_dashboard_v1"})
    _write(reg / "symbolic_field_registry.json", {**base, "schemaVersion": "symbolic_field_registry_v1"})


def test_overlay_actionable_filter_and_watchlist(tmp_path: Path, monkeypatch) -> None:
    _patch(tmp_path, monkeypatch)
    out = mod.build_outputs()
    mod.validate_outputs(out)

    assert [r["targetId"] for r in out["dashboard"]["actionable"]] == ["target:a"]
    assert [r["targetId"] for r in out["watchlist"]["items"]] == ["target:b"]


def test_reset_clears_markers(tmp_path: Path, monkeypatch) -> None:
    _patch(tmp_path, monkeypatch)
    out = mod.build_outputs(reset=True)
    assert out["dashboard"]["metadataPanel"]["markersCleared"] is True
    assert out["dashboard"]["actionable"] == []
    assert out["watchlist"]["items"] == []
