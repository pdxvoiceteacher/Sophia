from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft7Validator

from sophia.audit_navigation_state import audit_navigation_state


SCHEMA_PATH = Path("/workspace/Sophia/python/src/sophia/schemas/navigation_audit.json")


def test_missing_input_creates_docket(tmp_path: Path) -> None:
    out = tmp_path / "nav_audit.jsonl"
    rows = audit_navigation_state(tmp_path, out)
    assert len(rows) == 1
    res = json.loads(out.read_text(encoding="utf-8").splitlines()[0])
    assert res["finding"] == "navigation.missing"
    assert res["advisory"] == "docket"
    assert res["semanticMode"] == "non-executive"


def test_low_coherence_finding(tmp_path: Path) -> None:
    nav = {
        "chosen_state": {
            "node_a": {"next": "node_b"}
        },
        "artifactLineageHashes": {
            "node_a": {"psi": 0.0025}
        }
    }
    bridge_dir = tmp_path / "bridge"
    bridge_dir.mkdir()
    (bridge_dir / "navigation_state.json").write_text(json.dumps(nav), encoding="utf-8")
    out = tmp_path / "nav_audit.jsonl"
    rows = audit_navigation_state(tmp_path, out)
    assert any(f["finding"] == "navigation.low_coherence" for f in rows)
    res = json.loads(out.read_text(encoding="utf-8").splitlines()[0])
    assert res["severity"] == "info"


def test_jsonl_entries_validate_against_schema(tmp_path: Path) -> None:
    out = tmp_path / "nav_audit.jsonl"
    audit_navigation_state(tmp_path, out)
    validator = Draft7Validator(json.loads(SCHEMA_PATH.read_text(encoding="utf-8")))
    for line in out.read_text(encoding="utf-8").splitlines():
        validator.validate(json.loads(line))
