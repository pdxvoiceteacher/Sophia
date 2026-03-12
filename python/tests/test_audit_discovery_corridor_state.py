from __future__ import annotations

import json
from pathlib import Path

from sophia.audit_discovery_corridor_state import audit_discovery_corridor_state


def test_missing_file(tmp_path: Path) -> None:
    res = audit_discovery_corridor_state(str(tmp_path), None)
    assert res["decision"] == "fail"
    assert res["findings"][0]["id"].endswith("missing")
    assert res["findings"][0]["advisory"] == "docket"


def test_low_potential_from_corridors(tmp_path: Path) -> None:
    corr = {
        "corridors": [
            {"id": "a", "strength": 0.05},
            {"id": "b", "strength": 0.5},
        ]
    }
    (tmp_path / "bridge").mkdir(parents=True)
    (tmp_path / "bridge" / "discovery_corridor_map.json").write_text(json.dumps(corr), encoding="utf-8")
    res = audit_discovery_corridor_state(str(tmp_path), None)
    assert res["decision"] == "warn"
    assert any(f["id"].endswith("lowPotential") for f in res["findings"])


def test_pass_when_no_low_corridors(tmp_path: Path) -> None:
    corr = {"corridors": [{"id": "a", "strength": 0.8}]}
    (tmp_path / "bridge").mkdir(parents=True)
    (tmp_path / "bridge" / "discovery_corridor_map.json").write_text(json.dumps(corr), encoding="utf-8")
    out = tmp_path / "corridor_audit.json"
    audit_discovery_corridor_state(str(tmp_path), str(out))
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["decision"] == "pass"
