from __future__ import annotations

import json

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
    assert rec["finding"] == "navigation.missing"
    assert rec["semanticMode"] == "non-executive"
    assert "created_at" in rec


def test_empty_chosen_state_watch(tmp_path):
    (tmp_path / "bridge").mkdir()
    (tmp_path / "bridge" / "navigation_state.json").write_text(json.dumps({"chosen_state": {}}), encoding="utf-8")
    out_file = tmp_path / "bridge" / "navigation_audit.jsonl"
    audit_navigation_state(tmp_path, out_file)
    rec = json.loads(out_file.read_text(encoding="utf-8").splitlines()[0])
    assert rec["finding"] == "navigation.empty"
    assert rec["severity"] == "warn"
    assert rec["advisory"] == "watch"


def test_low_coherence_watch(tmp_path):
    nav = {
        "chosen_state": "node1",
        "artifactLineageHashes": {"psi": 0.05}
    }
    (tmp_path / "bridge").mkdir()
    (tmp_path / "bridge" / "navigation_state.json").write_text(json.dumps(nav), encoding="utf-8")
    out_file = tmp_path / "bridge" / "navigation_audit.jsonl"
    audit_navigation_state(tmp_path, out_file)
    rec = json.loads(out_file.read_text(encoding="utf-8").splitlines()[0])
    assert rec["finding"] == "navigation.low_coherence"
    assert rec["severity"] == "info"
    assert rec["advisory"] == "watch"


def test_ok_record_when_not_low_coherence(tmp_path):
    nav = {
        "chosen_state": "node1",
        "artifactLineageHashes": {"psi": 0.6}
    }
    (tmp_path / "bridge").mkdir()
    (tmp_path / "bridge" / "navigation_state.json").write_text(json.dumps(nav), encoding="utf-8")
    out_file = tmp_path / "bridge" / "navigation_audit.jsonl"
    audit_navigation_state(tmp_path, out_file)
    rec = json.loads(out_file.read_text(encoding="utf-8").splitlines()[0])
    assert rec["finding"] == "navigation.ok"
    assert rec["severity"] == "info"
