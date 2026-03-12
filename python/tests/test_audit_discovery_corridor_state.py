from __future__ import annotations

import json
from pathlib import Path

from sophia.audit_discovery_corridor_state import audit_discovery_corridor_state


def test_discovery_corridor_missing(tmp_path: Path) -> None:
    res = audit_discovery_corridor_state(str(tmp_path / "nonexistent"))
    assert any(f["id"] == "discovery_corridor.missing" for f in res["findings"])


def test_discovery_corridor_low(tmp_path: Path) -> None:
    dc = {"corridors": [{"id": "c1", "strength": 0.05}]}
    tmp_file = tmp_path / "bridge" / "discovery_corridor_map.json"
    tmp_file.parent.mkdir()
    tmp_file.write_text(json.dumps(dc), encoding="utf-8")
    res = audit_discovery_corridor_state(str(tmp_path))
    assert any(f["id"] == "discovery_corridor.lowPotential" for f in res["findings"])
    assert all(f["advisory"] in ["watch", "docket"] for f in res["findings"])
