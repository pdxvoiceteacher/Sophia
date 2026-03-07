from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from python.src.sophia import audit_institutional_state

REPO = Path(__file__).resolve().parents[1]


EXPECTED_STATUSES = {
    "stable",
    "monitor",
    "caution",
    "freeze-pathways",
    "require-human-review",
    "preservation-mode",
}


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _base_provenance(repo: str = "Sophia-Fixtures", schema_version: str = "institutional_bridge_v1") -> dict[str, str]:
    return {
        "schemaVersion": schema_version,
        "producerRepo": repo,
        "producerModule": "coherencelattice.institutional.tests",
        "producerCommit": "test-commit-1",
        "generatedAt": "2026-03-07T00:00:00Z",
        "created_at": "2026-03-07T00:00:00Z",
    }


def _write_canonical_inputs(tmp_path: Path, *, repo: str = "Sophia-Fixtures", schema_version: str = "institutional_bridge_v1") -> None:
    prov = _base_provenance(repo=repo, schema_version=schema_version)
    _write_json(
        tmp_path / "institutional_state_map.json",
        {
            **prov,
            "producerModule": "coherencelattice.institutional.state_map",
            "institutions": [{"institutionId": "inst:x", "coherenceScore": 0.9, "pathwayIntegrity": 0.9}],
        },
    )
    _write_json(
        tmp_path / "institutional_state_summary.json",
        {
            **prov,
            "producerModule": "coherencelattice.institutional.state_summary",
            "meanCoherenceScore": 0.6,
            "meanPathwayIntegrity": 0.6,
            "meanConflictScore": 0.4,
            "meanHealthScore": 0.6,
            "meanDecayRisk": 0.4,
        },
    )
    _write_json(
        tmp_path / "institutional_conflict_report.json",
        {
            **prov,
            "producerModule": "coherencelattice.institutional.conflict_report",
            "institutions": [{"institutionId": "inst:x", "conflictScore": 0.1, "unresolvedConflicts": 0}],
        },
    )
    _write_json(
        tmp_path / "institutional_health_projection.json",
        {
            **prov,
            "producerModule": "coherencelattice.institutional.health_projection",
            "institutions": [{"institutionId": "inst:x", "healthScore": 0.9, "decayRisk": 0.1}],
        },
    )


def test_institutional_outputs_validate_and_are_sorted() -> None:
    rc = audit_institutional_state.main([])
    assert rc == 0

    audit_payload = json.loads((REPO / "bridge" / "institutional_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "institutional_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "institutional_audit_v1.schema.json").read_text(encoding="utf-8"))
    recommendations_schema = json.loads(
        (REPO / "schema" / "institutional_recommendations_v1.schema.json").read_text(encoding="utf-8")
    )

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(recommendations_schema).validate(recommendations_payload)

    ids = [row["institutionId"] for row in audit_payload["records"]]
    assert ids == sorted(ids)

    statuses = {row["institutionalStatus"] for row in recommendations_payload["recommendations"]}
    assert statuses == EXPECTED_STATUSES


def test_institutional_outputs_are_bounded_and_non_mutating() -> None:
    audit_payload = json.loads((REPO / "bridge" / "institutional_audit.json").read_text(encoding="utf-8"))
    recommendations_payload = json.loads((REPO / "bridge" / "institutional_recommendations.json").read_text(encoding="utf-8"))

    assert "bounded" in audit_payload.get("caution", "").lower()
    assert "does not mutate canonical truth" in audit_payload.get("caution", "").lower()
    assert "without mutating canonical truth" in recommendations_payload.get("phaselock", "").lower()
    assert "bounded advisory" in recommendations_payload.get("caution", "").lower()


def test_missing_artifact_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_canonical_inputs(tmp_path)
    (tmp_path / "institutional_state_map.json").unlink()
    monkeypatch.setattr(audit_institutional_state, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_STATE_MAP_PATH", tmp_path / "institutional_state_map.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_STATE_SUMMARY_PATH", tmp_path / "institutional_state_summary.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_CONFLICT_REPORT_PATH", tmp_path / "institutional_conflict_report.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_HEALTH_PROJECTION_PATH", tmp_path / "institutional_health_projection.json")

    with pytest.raises(audit_institutional_state.InstitutionalInputError, match="Missing required canonical artifact"):
        audit_institutional_state.build_outputs()


def test_unsupported_schema_version_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_canonical_inputs(tmp_path, schema_version="institutional_bridge_v0")
    monkeypatch.setattr(audit_institutional_state, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_STATE_MAP_PATH", tmp_path / "institutional_state_map.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_STATE_SUMMARY_PATH", tmp_path / "institutional_state_summary.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_CONFLICT_REPORT_PATH", tmp_path / "institutional_conflict_report.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_HEALTH_PROJECTION_PATH", tmp_path / "institutional_health_projection.json")

    with pytest.raises(audit_institutional_state.InstitutionalInputError, match="Unsupported schemaVersion"):
        audit_institutional_state.build_outputs()


def test_provenance_presence_is_required(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_canonical_inputs(tmp_path)
    payload = json.loads((tmp_path / "institutional_state_map.json").read_text(encoding="utf-8"))
    payload.pop("producerCommit", None)
    _write_json(tmp_path / "institutional_state_map.json", payload)
    monkeypatch.setattr(audit_institutional_state, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_STATE_MAP_PATH", tmp_path / "institutional_state_map.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_STATE_SUMMARY_PATH", tmp_path / "institutional_state_summary.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_CONFLICT_REPORT_PATH", tmp_path / "institutional_conflict_report.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_HEALTH_PROJECTION_PATH", tmp_path / "institutional_health_projection.json")

    with pytest.raises(audit_institutional_state.InstitutionalInputError, match="Missing required provenance fields"):
        audit_institutional_state.build_outputs()


def test_fixture_live_mode_distinction(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_canonical_inputs(tmp_path, repo="Sophia")
    mixed_conflict = json.loads((tmp_path / "institutional_conflict_report.json").read_text(encoding="utf-8"))
    mixed_conflict["producerRepo"] = "Sophia-Fixtures"
    _write_json(tmp_path / "institutional_conflict_report.json", mixed_conflict)

    monkeypatch.setattr(audit_institutional_state, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_STATE_MAP_PATH", tmp_path / "institutional_state_map.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_STATE_SUMMARY_PATH", tmp_path / "institutional_state_summary.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_CONFLICT_REPORT_PATH", tmp_path / "institutional_conflict_report.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_HEALTH_PROJECTION_PATH", tmp_path / "institutional_health_projection.json")

    audit_payload, _ = audit_institutional_state.build_outputs()
    assert audit_payload["metadata"]["inputMode"] == "mixed"
    assert "MIXED MODE WARNING" in audit_payload["metadata"]["inputModeWarning"]


def test_canonical_artifact_name_enforcement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_canonical_inputs(tmp_path)
    old_path = tmp_path / "institutional_state_map.json"
    compat_path = tmp_path / "institutional_map.json"
    old_path.rename(compat_path)

    monkeypatch.setattr(audit_institutional_state, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_STATE_MAP_PATH", tmp_path / "institutional_state_map.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_STATE_SUMMARY_PATH", tmp_path / "institutional_state_summary.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_CONFLICT_REPORT_PATH", tmp_path / "institutional_conflict_report.json")
    monkeypatch.setattr(audit_institutional_state, "INSTITUTIONAL_HEALTH_PROJECTION_PATH", tmp_path / "institutional_health_projection.json")

    with pytest.raises(audit_institutional_state.InstitutionalInputError, match="deprecated/ambiguous alternatives"):
        audit_institutional_state.build_outputs()

    audit_payload, _ = audit_institutional_state.build_outputs(allow_compatibility_names=True)
    assert audit_payload["metadata"]["inputArtifacts"][0]["sourceMode"] == "compatibility"
