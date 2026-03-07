from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from python.src.sophia import audit_queue_pressure

REPO = Path(__file__).resolve().parents[1]


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _base_provenance(repo: str = "Sophia-Fixtures", schema: str = "queue_pressure_v1") -> dict[str, str]:
    return {
        "schemaVersion": schema,
        "producerRepo": repo,
        "producerModule": "coherencelattice.queue.tests",
        "producerCommit": "test-queue-1",
        "generatedAt": "2026-03-22T00:00:00Z",
        "created_at": "2026-03-22T00:00:00Z",
    }


def _write_inputs(tmp_path: Path, *, repo: str = "Sophia-Fixtures", schema: str = "queue_pressure_v1") -> None:
    p = _base_provenance(repo=repo, schema=schema)
    _write_json(tmp_path / "queue_pressure_map.json", {**p, "targets": [{"targetId": "q:a", "targetType": "queue", "backlogScore": 0.82, "stalenessScore": 0.4}]})
    _write_json(
        tmp_path / "queue_pressure_summary.json",
        {
            **p,
            "meanBacklogScore": 0.5,
            "meanStalenessScore": 0.5,
            "meanReviewFatigueScore": 0.5,
            "meanDominanceScore": 0.5,
            "meanGamingRiskScore": 0.5,
            "meanHollowPerformanceScore": 0.5,
        },
    )
    _write_json(tmp_path / "review_load_distribution.json", {**p, "targets": [{"targetId": "q:a", "reviewFatigueScore": 0.8, "dominanceScore": 0.4}]})
    _write_json(tmp_path / "goodhart_risk_report.json", {**p, "targets": [{"targetId": "q:a", "gamingRiskScore": 0.2, "hollowPerformanceScore": 0.1}]})


def _patch_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(audit_queue_pressure, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_queue_pressure, "QUEUE_PRESSURE_MAP_PATH", tmp_path / "queue_pressure_map.json")
    monkeypatch.setattr(audit_queue_pressure, "QUEUE_PRESSURE_SUMMARY_PATH", tmp_path / "queue_pressure_summary.json")
    monkeypatch.setattr(audit_queue_pressure, "REVIEW_LOAD_DISTRIBUTION_PATH", tmp_path / "review_load_distribution.json")
    monkeypatch.setattr(audit_queue_pressure, "GOODHART_RISK_REPORT_PATH", tmp_path / "goodhart_risk_report.json")


def test_queue_pressure_outputs_validate_and_sorted() -> None:
    rc = audit_queue_pressure.main([])
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "load_shedding_audit.json").read_text(encoding="utf-8"))
    rec_payload = json.loads((REPO / "bridge" / "load_shedding_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "load_shedding_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads((REPO / "schema" / "load_shedding_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(rec_payload)

    ids = [r["targetId"] for r in audit_payload["records"]]
    assert ids == sorted(ids)


def test_overloaded_queue_handling_present() -> None:
    payload = json.loads((REPO / "bridge" / "load_shedding_audit.json").read_text(encoding="utf-8"))
    statuses = {r["operationalStatus"] for r in payload["records"]}
    assert "overloaded" in statuses or "stalled" in statuses


def test_metric_gaming_status_coverage_present() -> None:
    payload = json.loads((REPO / "bridge" / "load_shedding_audit.json").read_text(encoding="utf-8"))
    statuses = {r["operationalStatus"] for r in payload["records"]}
    assert "gaming-risk" in statuses


def test_bounded_non_mutating_language() -> None:
    audit_payload = json.loads((REPO / "bridge" / "load_shedding_audit.json").read_text(encoding="utf-8"))
    caution = audit_payload.get("caution", "").lower()
    assert "bounded operational guidance" in caution
    assert "do not automatically delete" in caution
    assert "canonically mutate" in caution


def test_unsupported_schema_version_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_inputs(tmp_path, schema="queue_pressure_v0")
    _patch_paths(monkeypatch, tmp_path)

    with pytest.raises(audit_queue_pressure.QueuePressureInputError, match="Unsupported schemaVersion"):
        audit_queue_pressure.build_outputs()


def test_canonical_name_enforcement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_inputs(tmp_path)
    (tmp_path / "queue_pressure_map.json").rename(tmp_path / "queue_map.json")
    _patch_paths(monkeypatch, tmp_path)

    with pytest.raises(audit_queue_pressure.QueuePressureInputError, match="deprecated/ambiguous alternatives"):
        audit_queue_pressure.build_outputs()

    audit_payload, _ = audit_queue_pressure.build_outputs(allow_compatibility_names=True)
    assert audit_payload["metadata"]["inputArtifacts"][0]["sourceMode"] == "compatibility"
