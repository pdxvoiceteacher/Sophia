from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from python.src.sophia import audit_symbolic_field_state

REPO = Path(__file__).resolve().parents[1]

EXPECTED_STATUSES = {
    "stable",
    "monitor",
    "caution",
    "escalate",
    "freeze-dependent-pathways",
    "require-human-review",
}


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _base(version: str = "symbolic_field_v1") -> dict[str, str]:
    return {
        "schemaVersion": version,
        "producerRepo": "Sophia-Fixtures",
        "producerModule": "coherencelattice.symbolic.tests",
        "producerCommit": "test-t-1",
        "generatedAt": "2026-03-25T00:00:00Z",
        "created_at": "2026-03-25T00:00:00Z",
    }


def _write_inputs(tmp_path: Path, *, version: str = "symbolic_field_v1") -> None:
    p = _base(version)
    _write_json(tmp_path / "symbolic_field_state.json", {**p, "targets": [{"targetId": "x", "targetType": "field", "symbolicCoherence": 0.5, "ambiguityScore": 0.5}]})
    _write_json(
        tmp_path / "symbolic_field_summary.json",
        {
            **p,
            "meanSymbolicCoherence": 0.5,
            "meanAmbiguityScore": 0.5,
            "meanTransitionRisk": 0.5,
            "meanVolatilityScore": 0.5,
            "meanEarlyWarningScore": 0.5,
            "meanWarningConfidence": 0.5,
        },
    )
    _write_json(tmp_path / "regime_transition_report.json", {**p, "targets": [{"targetId": "x", "transitionRisk": 0.5, "volatilityScore": 0.5}]})
    _write_json(tmp_path / "early_warning_signal_map.json", {**p, "targets": [{"targetId": "x", "earlyWarningScore": 0.5, "warningConfidence": 0.5}]})


def _patch(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(audit_symbolic_field_state, "BRIDGE_DIR", tmp_path)
    monkeypatch.setattr(audit_symbolic_field_state, "SYMBOLIC_FIELD_STATE_PATH", tmp_path / "symbolic_field_state.json")
    monkeypatch.setattr(audit_symbolic_field_state, "SYMBOLIC_FIELD_SUMMARY_PATH", tmp_path / "symbolic_field_summary.json")
    monkeypatch.setattr(audit_symbolic_field_state, "REGIME_TRANSITION_REPORT_PATH", tmp_path / "regime_transition_report.json")
    monkeypatch.setattr(audit_symbolic_field_state, "EARLY_WARNING_SIGNAL_MAP_PATH", tmp_path / "early_warning_signal_map.json")


def test_symbolic_outputs_validate_and_sorted() -> None:
    assert audit_symbolic_field_state.main([]) == 0

    audit_payload = json.loads((REPO / "bridge" / "symbolic_field_audit.json").read_text(encoding="utf-8"))
    rec_payload = json.loads((REPO / "bridge" / "symbolic_field_recommendations.json").read_text(encoding="utf-8"))

    audit_schema = json.loads((REPO / "schema" / "symbolic_field_audit_v1.schema.json").read_text(encoding="utf-8"))
    rec_schema = json.loads((REPO / "schema" / "symbolic_field_recommendations_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(audit_schema).validate(audit_payload)
    Draft202012Validator(rec_schema).validate(rec_payload)

    ids = [r["targetId"] for r in audit_payload["records"]]
    assert ids == sorted(ids)


def test_full_field_status_coverage() -> None:
    payload = json.loads((REPO / "bridge" / "symbolic_field_audit.json").read_text(encoding="utf-8"))
    statuses = {r["fieldStatus"] for r in payload["records"]}
    assert statuses == EXPECTED_STATUSES


def test_bounded_non_mutating_language() -> None:
    payload = json.loads((REPO / "bridge" / "symbolic_field_audit.json").read_text(encoding="utf-8"))
    caution = payload.get("caution", "").lower()
    assert "bounded interpretive guidance" in caution
    assert "do not automatically mutate memory" in caution
    assert "reconfigure triadic governance" in caution


def test_early_warning_escalation_handling() -> None:
    payload = json.loads((REPO / "bridge" / "symbolic_field_audit.json").read_text(encoding="utf-8"))
    rows = {r["targetId"]: r for r in payload["records"]}
    assert rows["symbolic:human-review-006"]["fieldStatus"] == "require-human-review"
    assert rows["symbolic:escalate-004"]["fieldStatus"] == "escalate"


def test_fail_closed_provenance_enforcement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_inputs(tmp_path, version="symbolic_field_v0")
    _patch(monkeypatch, tmp_path)
    with pytest.raises(audit_symbolic_field_state.SymbolicFieldInputError, match="Unsupported schemaVersion"):
        audit_symbolic_field_state.build_outputs()


def test_missing_provenance_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    _write_inputs(tmp_path)
    payload = json.loads((tmp_path / "symbolic_field_state.json").read_text(encoding="utf-8"))
    payload.pop("producerCommit", None)
    _write_json(tmp_path / "symbolic_field_state.json", payload)
    _patch(monkeypatch, tmp_path)
    with pytest.raises(audit_symbolic_field_state.SymbolicFieldInputError, match="Missing required provenance fields"):
        audit_symbolic_field_state.build_outputs()
