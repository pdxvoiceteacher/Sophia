from __future__ import annotations

import json
from pathlib import Path

from sophia.audit_discovery_corridor_state import audit_discovery_corridor_state


def test_missing_corridor(tmp_path: Path) -> None:
    audit = audit_discovery_corridor_state(str(tmp_path))
    assert any(f["id"] == "discovery_corridor.missing" for f in audit["findings"])
    assert audit["decision"] == "fail"
    assert audit["semanticMode"] == "non-executive"


def test_low_potential_warning(tmp_path: Path) -> None:
    (tmp_path / "bridge").mkdir()
    data = {"discoveryCorridors": [{"corridorId": "c1", "transfer": 0.05}]}
    (tmp_path / "bridge" / "discovery_corridor_map.json").write_text(json.dumps(data), encoding="utf-8")
    audit_discovery_corridor_state(str(tmp_path), out_file=None)
    result = json.loads((tmp_path / "discovery_corridor_audit.json").read_text(encoding="utf-8"))
    assert any(f["id"] == "discovery_corridor.lowPotential" for f in result["findings"])
    assert result["decision"] == "warn"
