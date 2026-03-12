from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BRIDGE_ROOT = REPO_ROOT
DEFAULT_OUT = REPO_ROOT / "bridge" / "discovery_corridor_audit.json"
SCHEMA_PATH = REPO_ROOT / "schema/sophia/discovery_corridor_audit_v1.schema.json"

AUDIT_SCHEMA = "sophia/discovery_corridor_audit_v1"
CAUTION = (
    "This audit is advisory-only (watch/docket). It does not authorize governance action, "
    "closure, canon formation, or suppression. It supports keep-open stewardship and legibility."
)


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _resolve_bridge_file(bridge_root: Path, filename: str) -> Path | None:
    p1 = bridge_root / filename
    p2 = bridge_root / "bridge" / filename
    if p1.exists():
        return p1
    if p2.exists():
        return p2
    return None


def _extract_corridor_potential(payload: dict[str, Any]) -> float:
    for path in (("corridorPotential",), ("discoveryCorridorMap", "corridorPotential"), ("targets", 0, "corridorPotential")):
        cur: Any = payload
        ok = True
        for p in path:
            if isinstance(p, int):
                if not isinstance(cur, list) or len(cur) <= p:
                    ok = False
                    break
                cur = cur[p]
            else:
                if not isinstance(cur, dict) or p not in cur:
                    ok = False
                    break
                cur = cur[p]
        if ok and isinstance(cur, (int, float)):
            return float(cur)
    return 0.0


def build_outputs(*, bridge_root: Path = DEFAULT_BRIDGE_ROOT) -> dict[str, Any]:
    corridor_path = _resolve_bridge_file(bridge_root, "discovery_corridor_map.json")
    if corridor_path is None:
        payload = {
            "schema": AUDIT_SCHEMA,
            "created_at": _utc_now_iso(),
            "caution": CAUTION,
            "decision": "warn",
            "findings": [
                {
                    "id": "discovery_corridor.missing",
                    "severity": "warn",
                    "type": "audit",
                    "advisory": "docket",
                    "message": "Discovery corridor map missing. Auditing failed closed.",
                    "data": {"expectedFile": "discovery_corridor_map.json"},
                }
            ],
        }
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    corr_map = _load_json(corridor_path)
    potential = _extract_corridor_potential(corr_map)

    if potential < 0.2:
        findings = [
            {
                "id": "discovery_corridor.lowPotential",
                "severity": "warn",
                "type": "audit",
                "advisory": "watch",
                "message": f"Corridor potential is low ({potential:.3f})",
                "data": {"potential": round(potential, 6)},
            }
        ]
        decision = "warn"
    else:
        findings = [
            {
                "id": "discovery_corridor.healthy",
                "severity": "info",
                "type": "audit",
                "advisory": "watch",
                "message": f"Corridor potential is healthy ({potential:.3f})",
                "data": {"potential": round(potential, 6)},
            }
        ]
        decision = "info"

    payload = {
        "schema": AUDIT_SCHEMA,
        "created_at": _utc_now_iso(),
        "caution": CAUTION,
        "decision": decision,
        "findings": findings,
    }
    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
    return payload


def audit_discovery_corridor_state(bridge_root: str, output_file: str | None = None) -> dict[str, Any]:
    result = build_outputs(bridge_root=Path(bridge_root))
    if output_file:
        out = Path(output_file)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", type=Path, default=DEFAULT_BRIDGE_ROOT)
    parser.add_argument("--out", dest="output_file", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--output-file", dest="output_file", type=Path)
    args = parser.parse_args(argv)

    res = audit_discovery_corridor_state(str(args.bridge_root), str(args.output_file))
    print(res["decision"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
