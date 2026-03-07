from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from python.src.sophia import audit_closure_state

REPO = Path(__file__).resolve().parents[1]

EXPECTED_RECOMMENDATIONS = {
    "confirm-closure",
    "keep-open",
    "provisional-close",
    "reopen-for-review",
    "queue-repair",
    "require-human-review",
}


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _base(version: str = "closure_state_v1") -> dict[str, str]:
    return {
        "schemaVersion": version,
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.closure.tests",
        "producerCommit": "test-s-1",
        "generatedAt": "2026-03-24T00:00:00Z",
        "created_at": "2026-03-24T00:00:00Z",
    }


def _write_inputs(tmp_path: Path, *, version: str = "closure_state_v1") -> None:
    p = _base(version)
    _write_json(tmp_path / "closure_state_map.json", {**p, "targets": [{"targetId": "x", "targetType": "case", "closureConfidence": 0.5, "contradictionScore": 0.4}]})
    _write_json(
        tmp_path / "closure_state_summary.json",
        {
            **p,
            "meanClosureConfidence": 0.5,
            "meanContradictionScore": 0.4,
            "meanRepairNeedScore": 0.4,
            "meanReversibilityScore": 0.5,
            "meanReopenSignalScore": 0.4,
            "meanEvidenceQuality": 0.5,
        },
    )
    _write_json(tmp_path / "repair_candidate_map.json", {**p, "targets": [{"targetId": "x", "repairNeedScore": 0.4, "reversibilityScore": 0.5}]})
    _write_json(tmp_path / "reopen_signal_report.json", {**p, "targets": [{"targetId": "x", "reopenSignalScore": 0.4, "evidenceQuality": 0.5}]})


def _patch(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(audit_closure_state, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_closure_state, "CLOSURE_STATE_MAP_PATH", tmp_path / "closure_state_map.json")
    monkeypatch.setattr(audit_closure_state, "CLOSURE_STATE_SUMMARY_PATH", tmp_path / "closure_state_summary.json")
    monkeypatch.setattr(audit_closure_state, "REPAIR_CANDIDATE_MAP_PATH", tmp_path / "repair_candidate_map.json")
    monkeypatch.setattr(audit_closure_state, "REOPEN_SIGNAL_REPORT_PATH", tmp_path / "reopen_signal_report.json")


def test_closure_outputs_validate_and_sorted() -> None:
    assert audit_closure_state.main([]) == 0
    audit_payload = json.loads((REPO / "bridge" / "closure_audit.json").read_text(encoding="utf-8"))
    rec_payload = json.loads((REPO / "bridge" / "closure_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "closure_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads((REPO / "schema" / "closure_recommendations_v1.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(rec_payload)

    ids = [r["targetId"] for r in audit_payload["records"]]
    assert ids == sorted(ids)


def test_full_closure_recommendation_coverage() -> None:
    payload = json.loads((REPO / "bridge" / "closure_audit.json").read_text(encoding="utf-8"))
    recs = {r["closureRecommendation"] for r in payload["records"]}
    assert recs == EXPECTED_RECOMMENDATIONS


def test_bounded_non_mutating_language() -> None:
    payload = json.loads((REPO / "bridge" / "closure_audit.json").read_text(encoding="utf-8"))
    caution = payload.get("caution", "").lower()
    assert "bounded outcome guidance" in caution
    assert "do not automatically reopen, close, or repair" in caution


def test_reopen_vs_repair_distinction() -> None:
    payload = json.loads((REPO / "bridge" / "closure_audit.json").read_text(encoding="utf-8"))
    rows = {r["targetId"]: r for r in payload["records"]}
    assert rows["closure:reopen-evidence-004"]["closureRecommendation"] == "reopen-for-review"
    assert rows["closure:repair-path-005"]["closureRecommendation"] == "queue-repair"


def test_fail_closed_provenance_enforcement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_inputs(tmp_path, version="closure_state_v0")
    _patch(monkeypatch, tmp_path)
    with pytest.raises(audit_closure_state.ClosureInputError, match="Unsupported schemaVersion"):
        audit_closure_state.build_outputs()


def test_missing_provenance_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_inputs(tmp_path)
    payload = json.loads((tmp_path / "closure_state_map.json").read_text(encoding="utf-8"))
    payload.pop("producerCommit", None)
    _write_json(tmp_path / "closure_state_map.json", payload)
    _patch(monkeypatch, tmp_path)
    with pytest.raises(audit_closure_state.ClosureInputError, match="Missing required provenance fields"):
        audit_closure_state.build_outputs()
