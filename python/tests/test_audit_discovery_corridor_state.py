from __future__ import annotations

import json
from pathlib import Path

from sophia.audit_discovery_corridor_state import audit_discovery_corridor_state


def test_missing_input(tmp_path: Path) -> None:
    out = audit_discovery_corridor_state(tmp_path / "missing.json", tmp_path / "out.json")
    assert any(f["id"] == "discovery_corridor.missing" for f in out["findings"])
    assert out["decision"] == "fail"
    assert out["semanticMode"] == "non-executive"


def test_low_potential(tmp_path: Path) -> None:
    dc = {"discoveryCorridors": [{"id": "x1", "strength": 0.05}]}
    inp = tmp_path / "disc.json"
    inp.write_text(json.dumps(dc), encoding="utf-8")
    out = audit_discovery_corridor_state(inp, tmp_path / "out.json")
    assert any(f["id"] == "discovery_corridor.lowPotential" for f in out["findings"])
    assert all(f["advisory"] in ["watch", "docket"] for f in out["findings"])
