from __future__ import annotations

import json
from pathlib import Path

from sophia.audit_discovery_corridor_state import audit_discovery_corridor_state


def test_missing_file(tmp_path: Path) -> None:
    res = audit_discovery_corridor_state(str(tmp_path), None)
    assert res["findings"][0]["id"].endswith("missing")
    assert res["findings"][0]["severity"] == "warn"
    assert res["findings"][0]["advisory"] == "docket"


def test_low_potential(tmp_path: Path) -> None:
    corr = {"corridorPotential": 0.1}
    (tmp_path / "bridge").mkdir(parents=True)
    (tmp_path / "bridge" / "discovery_corridor_map.json").write_text(json.dumps(corr), encoding="utf-8")
    res = audit_discovery_corridor_state(str(tmp_path), None)
    assert any(f["id"].endswith("lowPotential") for f in res["findings"])


def test_output_file_alias_and_write(tmp_path: Path) -> None:
    corr = {"corridorPotential": 0.8}
    (tmp_path / "bridge").mkdir(parents=True)
    (tmp_path / "bridge" / "discovery_corridor_map.json").write_text(json.dumps(corr), encoding="utf-8")
    out = tmp_path / "corridor_audit.json"
    audit_discovery_corridor_state(str(tmp_path), str(out))
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["decision"] in {"info", "warn"}
