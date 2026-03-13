from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft7Validator

from sophia.audit.navigation_state import audit_navigation_state


def test_missing_navigation_state(tmp_path):
    bridge = tmp_path / "bridge"
    bridge.mkdir()
    out_file = bridge / "navigation_audit.jsonl"
    audit_navigation_state(tmp_path, out_file)
    lines = out_file.read_text(encoding="utf-8").splitlines()
    assert len(lines) == 1
    rec = json.loads(lines[0])
    assert rec["advisory"] == "docket"
    assert rec["finding"].startswith("navigation.missing")


def test_low_coherence_watch(tmp_path):
    nav = {
        "chosen_state": "node1",
        "artifactLineageHashes": {"psi": 0.05},
    }
    (tmp_path / "bridge").mkdir()
    (tmp_path / "bridge" / "navigation_state.json").write_text(json.dumps(nav), encoding="utf-8")
    out_file = tmp_path / "bridge" / "navigation_audit.jsonl"
    audit_navigation_state(tmp_path, out_file)
    lines = out_file.read_text(encoding="utf-8").splitlines()
    assert len(lines) == 1
    rec = json.loads(lines[0])
    assert rec["finding"] == "navigation.low_coherence"
    assert rec["severity"] == "info"
    assert rec["advisory"] == "watch"


def test_jsonl_entries_validate_against_schema(tmp_path):
    out_file = tmp_path / "bridge" / "navigation_audit.jsonl"
    audit_navigation_state(tmp_path, out_file)
    schema = json.loads(Path("/workspace/Sophia/python/src/sophia/schemas/navigation_audit.json").read_text(encoding="utf-8"))
    validator = Draft7Validator(schema)
    for line in out_file.read_text(encoding="utf-8").splitlines():
        validator.validate(json.loads(line))
