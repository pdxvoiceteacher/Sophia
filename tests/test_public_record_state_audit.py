from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from python.src.sophia import audit_public_record_state

REPO = Path(__file__).resolve().parents[1]
EXPECTED_STATUSES = {"sound", "monitor", "ambiguous", "verify-first", "require-human-review"}


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _base(version: str = "public_record_v1") -> dict[str, str]:
    return {
        "schemaVersion": version,
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.public_record.tests",
        "producerCommit": "test-v-1",
        "generatedAt": "2026-03-27T00:00:00Z",
        "created_at": "2026-03-27T00:00:00Z",
    }


def _write_inputs(tmp_path: Path, *, version: str = "public_record_v1") -> None:
    p = _base(version)
    _write_json(tmp_path / "public_record_intake_map.json", {**p, "targets": [{"targetId": "x", "targetType": "record", "recordQuality": 0.5, "claimReliability": 0.5}]})
    _write_json(tmp_path / "entity_graph_map.json", {**p, "targets": [{"targetId": "x", "entityAmbiguity": 0.5, "nodeConsistency": 0.5}]})
    _write_json(tmp_path / "relationship_edge_map.json", {**p, "targets": [{"targetId": "x", "edgeConfidence": 0.5, "edgeAmbiguity": 0.5}]})
    _write_json(tmp_path / "chain_of_custody_report.json", {**p, "targets": [{"targetId": "x", "chainCompleteness": 0.5, "tamperRisk": 0.5}]})


def _patch(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(audit_public_record_state, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_public_record_state, "PUBLIC_RECORD_INTAKE_MAP_PATH", tmp_path / "public_record_intake_map.json")
    monkeypatch.setattr(audit_public_record_state, "ENTITY_GRAPH_MAP_PATH", tmp_path / "entity_graph_map.json")
    monkeypatch.setattr(audit_public_record_state, "RELATIONSHIP_EDGE_MAP_PATH", tmp_path / "relationship_edge_map.json")
    monkeypatch.setattr(audit_public_record_state, "CHAIN_OF_CUSTODY_REPORT_PATH", tmp_path / "chain_of_custody_report.json")


def test_public_record_outputs_validate_and_sorted() -> None:
    assert audit_public_record_state.main([]) == 0

    audit_payload = json.loads((REPO / "bridge" / "public_record_audit.json").read_text(encoding="utf-8"))
    rec_payload = json.loads((REPO / "bridge" / "public_record_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "public_record_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads((REPO / "schema" / "public_record_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(rec_payload)

    ids = [r["targetId"] for r in audit_payload["records"]]
    assert ids == sorted(ids)


def test_full_graph_status_coverage() -> None:
    payload = json.loads((REPO / "bridge" / "public_record_audit.json").read_text(encoding="utf-8"))
    statuses = {r["graphStatus"] for r in payload["records"]}
    assert statuses == EXPECTED_STATUSES


def test_bounded_non_accusatory_language() -> None:
    payload = json.loads((REPO / "bridge" / "public_record_audit.json").read_text(encoding="utf-8"))
    caution = payload.get("caution", "").lower()
    assert "bounded evidence guidance" in caution
    assert "do not accuse" in caution
    assert "automatically publish conclusions" in caution


def test_ambiguous_edge_escalation_handling() -> None:
    payload = json.loads((REPO / "bridge" / "public_record_audit.json").read_text(encoding="utf-8"))
    rows = {r["targetId"]: r for r in payload["records"]}
    assert rows["record:humanreview-005"]["graphStatus"] == "require-human-review"
    assert rows["record:verifyfirst-004"]["graphStatus"] == "verify-first"


def test_fail_closed_provenance_enforcement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_inputs(tmp_path, version="public_record_v0")
    _patch(monkeypatch, tmp_path)
    with pytest.raises(audit_public_record_state.PublicRecordInputError, match="Unsupported schemaVersion"):
        audit_public_record_state.build_outputs()


def test_missing_provenance_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_inputs(tmp_path)
    payload = json.loads((tmp_path / "public_record_intake_map.json").read_text(encoding="utf-8"))
    payload.pop("producerCommit", None)
    _write_json(tmp_path / "public_record_intake_map.json", payload)
    _patch(monkeypatch, tmp_path)
    with pytest.raises(audit_public_record_state.PublicRecordInputError, match="Missing required provenance fields"):
        audit_public_record_state.build_outputs()
