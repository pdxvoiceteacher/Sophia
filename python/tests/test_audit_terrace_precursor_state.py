from __future__ import annotations

import json
from pathlib import Path

import pytest

from sophia import audit_terrace_precursor_state as module


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _configure_paths(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(module, "TERRACE_PRECURSOR_MAP_PATH", tmp_path / "bridge/terrace_precursor_map.json")
    monkeypatch.setattr(module, "TERRACE_PRECURSOR_AUDIT_SCHEMA_PATH", Path("/workspace/Sophia/schema/terrace_precursor_audit_v1.schema.json"))
    monkeypatch.setattr(
        module,
        "TERRACE_PRECURSOR_RECOMMENDATIONS_SCHEMA_PATH",
        Path("/workspace/Sophia/schema/terrace_precursor_recommendations_v1.schema.json"),
    )


def test_build_outputs_flags_expected_patterns(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_json(
        tmp_path / "bridge/terrace_precursor_map.json",
        {
            "generatedAt": "2027-01-01T00:00:00Z",
            "targets": [
                {
                    "targetId": "target:false",
                    "terracePrecursorScore": 0.91,
                    "memoryContinuity": 0.42,
                    "pluralityRetention": 0.58,
                    "deltaS": 0.04,
                    "lambda": -0.01,
                },
                {
                    "targetId": "target:healthy",
                    "terracePrecursorScore": 0.66,
                    "memoryContinuity": 0.78,
                    "pluralityRetention": 0.82,
                    "deltaS": 0.08,
                    "lambda": 0.03,
                },
            ],
        },
    )

    audit_payload, rec_payload = module.build_outputs()

    assert audit_payload["decision"] == "warn"
    types = {f["type"] for f in audit_payload["findings"]}
    assert "false-terrace-risk" in types
    assert "regime-sign-mismatch" in types
    assert "within-bounds" in types

    assert rec_payload["schema"] == "terrace_precursor_recommendations_v1"
    actions = {r["targetPublisherAction"] for r in rec_payload["recommendations"]}
    assert actions <= {"watch", "docket"}


def test_safe_language_and_no_suppress(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    _write_json(
        tmp_path / "bridge/terrace_precursor_map.json",
        {
            "generatedAt": "2027-01-01T00:00:00Z",
            "targets": [
                {
                    "targetId": "target:tone",
                    "terracePrecursorScore": 0.74,
                    "memoryContinuity": 0.70,
                    "pluralityRetention": 0.72,
                    "deltaS": 0.02,
                    "lambda": 0.02,
                }
            ],
        },
    )

    audit_payload, rec_payload = module.build_outputs()
    text = " ".join(
        [
            audit_payload["phaselock"],
            audit_payload["caution"],
            *[f["message"] for f in audit_payload["findings"]],
            *[r["recommendation"] for r in rec_payload["recommendations"]],
        ]
    ).lower()

    assert "bounded advisory guidance" in text
    assert "suppression orders" in text
    assert "epochal closure" in text
    assert "final" not in text
    assert all(r["targetPublisherAction"] in {"watch", "docket"} for r in rec_payload["recommendations"])


def test_missing_or_empty_targets_fail_closed(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    _configure_paths(monkeypatch, tmp_path)
    with pytest.raises(module.TerracePrecursorInputError):
        module.build_outputs()

    _write_json(tmp_path / "bridge/terrace_precursor_map.json", {"targets": []})
    with pytest.raises(module.TerracePrecursorInputError):
        module.build_outputs()
