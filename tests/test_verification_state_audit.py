from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from python.src.sophia import audit_verification_state

REPO = Path(__file__).resolve().parents[1]
EXPECTED_STATUSES = {"verify-now", "near-term-verify", "monitor", "defer", "require-human-review"}


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _base(version: str = "verification_state_v1") -> dict[str, str]:
    return {
        "schemaVersion": version,
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.verification.tests",
        "producerCommit": "test-u-1",
        "generatedAt": "2026-03-26T00:00:00Z",
        "created_at": "2026-03-26T00:00:00Z",
    }


def _write_inputs(tmp_path: Path, *, version: str = "verification_state_v1") -> None:
    p = _base(version)
    _write_json(tmp_path / "claim_type_map.json", {**p, "targets": [{"targetId": "x", "targetType": "claim", "claimConfidence": 0.5, "sensitivityScore": 0.5}]})
    _write_json(tmp_path / "entity_resolution_map.json", {**p, "targets": [{"targetId": "x", "entityAmbiguity": 0.5, "identityCollisionRisk": 0.5}]})
    _write_json(
        tmp_path / "entity_resolution_summary.json",
        {
            **p,
            "meanClaimConfidence": 0.5,
            "meanSensitivityScore": 0.5,
            "meanEntityAmbiguity": 0.5,
            "meanIdentityCollisionRisk": 0.5,
            "meanVerificationUrgency": 0.5,
            "meanContradictionScore": 0.5,
        },
    )
    _write_json(tmp_path / "verification_task_map.json", {**p, "targets": [{"targetId": "x", "verificationUrgency": 0.5, "contradictionScore": 0.5}]})


def _patch(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(audit_verification_state, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_verification_state, "CLAIM_TYPE_MAP_PATH", tmp_path / "claim_type_map.json")
    monkeypatch.setattr(audit_verification_state, "ENTITY_RESOLUTION_MAP_PATH", tmp_path / "entity_resolution_map.json")
    monkeypatch.setattr(audit_verification_state, "ENTITY_RESOLUTION_SUMMARY_PATH", tmp_path / "entity_resolution_summary.json")
    monkeypatch.setattr(audit_verification_state, "VERIFICATION_TASK_MAP_PATH", tmp_path / "verification_task_map.json")


def test_verification_outputs_validate_and_sorted() -> None:
    assert audit_verification_state.main([]) == 0

    audit_payload = json.loads((REPO / "bridge" / "verification_audit.json").read_text(encoding="utf-8"))
    rec_payload = json.loads((REPO / "bridge" / "verification_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "verification_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads((REPO / "schema" / "verification_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(rec_payload)

    ids = [r["targetId"] for r in audit_payload["records"]]
    assert ids == sorted(ids)


def test_full_verification_status_coverage() -> None:
    payload = json.loads((REPO / "bridge" / "verification_audit.json").read_text(encoding="utf-8"))
    statuses = {r["verificationStatus"] for r in payload["records"]}
    assert statuses == EXPECTED_STATUSES


def test_bounded_non_accusatory_language() -> None:
    payload = json.loads((REPO / "bridge" / "verification_audit.json").read_text(encoding="utf-8"))
    caution = payload.get("caution", "").lower()
    assert "bounded evidence-guidance" in caution
    assert "do not accuse" in caution
    assert "automatically resolve identity" in caution


def test_entity_ambiguity_escalation_handling() -> None:
    payload = json.loads((REPO / "bridge" / "verification_audit.json").read_text(encoding="utf-8"))
    rows = {r["targetId"]: r for r in payload["records"]}
    assert rows["verify:human-005"]["verificationStatus"] == "require-human-review"
    assert rows["verify:urgent-001"]["verificationStatus"] == "verify-now"


def test_fail_closed_provenance_enforcement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_inputs(tmp_path, version="verification_state_v0")
    _patch(monkeypatch, tmp_path)
    with pytest.raises(audit_verification_state.VerificationInputError, match="Unsupported schemaVersion"):
        audit_verification_state.build_outputs()


def test_missing_provenance_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_inputs(tmp_path)
    payload = json.loads((tmp_path / "claim_type_map.json").read_text(encoding="utf-8"))
    payload.pop("producerCommit", None)
    _write_json(tmp_path / "claim_type_map.json", payload)
    _patch(monkeypatch, tmp_path)
    with pytest.raises(audit_verification_state.VerificationInputError, match="Missing required provenance fields"):
        audit_verification_state.build_outputs()
