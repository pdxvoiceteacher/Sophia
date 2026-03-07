from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from python.src.sophia import audit_priority_state

REPO = Path(__file__).resolve().parents[1]

EXPECTED_STATUSES = {
    "immediate-review",
    "near-term-review",
    "monitor",
    "defer",
    "freeze-dependent-pathways",
    "require-human-review",
}


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _base_prov(repo: str = "Sophia-Fixtures", version: str = "priority_state_v1") -> dict[str, str]:
    return {
        "schemaVersion": version,
        "producerRepo": repo,
        "producerModule": "coherencelattice.priority.tests",
        "producerCommit": "test-r-1",
        "generatedAt": "2026-03-23T00:00:00Z",
        "created_at": "2026-03-23T00:00:00Z",
    }


def _write_priority_inputs(tmp_path: Path, *, version: str = "priority_state_v1") -> None:
    p = _base_prov(version=version)
    _write_json(tmp_path / "priority_state_map.json", {**p, "targets": [{"targetId": "x", "targetType": "queue", "priorityScore": 0.6, "queuePressureScore": 0.6}]})
    _write_json(
        tmp_path / "priority_state_summary.json",
        {
            **p,
            "meanPriorityScore": 0.5,
            "meanQueuePressureScore": 0.5,
            "meanUrgencyScore": 0.5,
            "meanReversibilityScore": 0.5,
            "meanCaptureRisk": 0.5,
            "meanDominanceRisk": 0.5,
        },
    )
    _write_json(tmp_path / "triage_candidate_map.json", {**p, "targets": [{"targetId": "x", "urgencyScore": 0.5, "reversibilityScore": 0.5}]})
    _write_json(tmp_path / "triage_conflict_report.json", {**p, "targets": [{"targetId": "x", "captureRisk": 0.5, "dominanceRisk": 0.5}]})


def _patch(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(audit_priority_state, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_priority_state, "PRIORITY_STATE_MAP_PATH", tmp_path / "priority_state_map.json")
    monkeypatch.setattr(audit_priority_state, "PRIORITY_STATE_SUMMARY_PATH", tmp_path / "priority_state_summary.json")
    monkeypatch.setattr(audit_priority_state, "TRIAGE_CANDIDATE_MAP_PATH", tmp_path / "triage_candidate_map.json")
    monkeypatch.setattr(audit_priority_state, "TRIAGE_CONFLICT_REPORT_PATH", tmp_path / "triage_conflict_report.json")


def test_priority_outputs_validate_and_sorted() -> None:
    rc = audit_priority_state.main([])
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "triage_audit.json").read_text(encoding="utf-8"))
    rec_payload = json.loads((REPO / "bridge" / "triage_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "triage_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads((REPO / "schema" / "triage_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(rec_payload)

    ids = [r["targetId"] for r in audit_payload["records"]]
    assert ids == sorted(ids)


def test_full_triage_status_coverage() -> None:
    payload = json.loads((REPO / "bridge" / "triage_audit.json").read_text(encoding="utf-8"))
    statuses = {r["triageStatus"] for r in payload["records"]}
    assert statuses == EXPECTED_STATUSES


def test_bounded_non_mutating_language() -> None:
    payload = json.loads((REPO / "bridge" / "triage_audit.json").read_text(encoding="utf-8"))
    caution = payload.get("caution", "").lower()
    assert "bounded ordering guidance" in caution
    assert "do not automatically reconfigure queues" in caution
    assert "canonical truth" in caution


def test_priority_inversion_handling() -> None:
    payload = json.loads((REPO / "bridge" / "triage_audit.json").read_text(encoding="utf-8"))
    rows = {r["targetId"]: r for r in payload["records"]}
    assert rows["triage:irreversible-recovery-002"]["triageStatus"] == "immediate-review"
    assert rows["triage:scenario-warning-003"]["triageStatus"] == "near-term-review"


def test_fail_closed_provenance_enforcement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_priority_inputs(tmp_path, version="priority_state_v0")
    _patch(monkeypatch, tmp_path)
    with pytest.raises(audit_priority_state.PriorityInputError, match="Unsupported schemaVersion"):
        audit_priority_state.build_outputs()


def test_missing_provenance_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_priority_inputs(tmp_path)
    payload = json.loads((tmp_path / "priority_state_map.json").read_text(encoding="utf-8"))
    payload.pop("producerCommit", None)
    _write_json(tmp_path / "priority_state_map.json", payload)
    _patch(monkeypatch, tmp_path)
    with pytest.raises(audit_priority_state.PriorityInputError, match="Missing required provenance fields"):
        audit_priority_state.build_outputs()
