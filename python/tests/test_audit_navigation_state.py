from __future__ import annotations

import json
from pathlib import Path

from sophia.audit_navigation_state import audit_navigation_state


def test_missing_input_creates_docket(tmp_path: Path) -> None:
    out = tmp_path / "nav_audit.jsonl"
    audit_navigation_state(tmp_path, out)
    res = json.loads(out.read_text(encoding="utf-8").splitlines()[0])
    assert res["decision"] == "fail"
    assert res["findings"][0]["advisory"] == "docket"
    assert res["semanticMode"] == "non-executive"


def test_low_coherence_finding(tmp_path: Path) -> None:
    nav = {
        "chosen_state": {
            "E": 0.05,
            "T": 0.05,
            "psi": 0.0025,
            "delta_s": 0.0,
            "lambda_critical": 0.1,
            "ethical_symmetry": 0.5,
        }
    }
    bridge_dir = tmp_path / "bridge"
    bridge_dir.mkdir()
    (bridge_dir / "navigation_state.json").write_text(json.dumps(nav), encoding="utf-8")
    out = tmp_path / "nav_audit.jsonl"
    audit_navigation_state(tmp_path, out)
    res = json.loads(out.read_text(encoding="utf-8").splitlines()[0])
    assert any(f["finding"] == "navigation.low_coherence" for f in res["findings"])
    assert res["decision"] == "warn"
