from __future__ import annotations

import json
from pathlib import Path

from sophia import audit_discovery_corridor_state as module


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def test_discovery_corridor_audit_fail_closed(tmp_path: Path) -> None:
    payload = module.build_outputs(bridge_root=tmp_path / "missing")
    assert payload["decision"] == "warn"
    assert len(payload["findings"]) == 1
    assert payload["findings"][0]["advisory"] == "docket"


def test_discovery_corridor_audit_warns_for_high_potential(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(bridge / "discovery_corridor_map.json", {"corridorPotential": 0.9})
    payload = module.build_outputs(bridge_root=tmp_path)
    assert payload["decision"] == "warn"
    assert payload["findings"][0]["id"] == "corridor.forming"
    assert payload["findings"][0]["advisory"] == "watch"


def test_compat_entrypoint_writes_file(tmp_path: Path) -> None:
    bridge = tmp_path / "bridge"
    _write(bridge / "discovery_corridor_map.json", {"corridorPotential": 0.3})
    out = tmp_path / "discovery_corridor_audit.json"

    module.audit_discovery_corridor_state(str(tmp_path), str(out))
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["findings"][0]["advisory"] in {"watch", "docket"}
