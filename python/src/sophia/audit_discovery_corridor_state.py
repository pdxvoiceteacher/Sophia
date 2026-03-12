from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BRIDGE_ROOT = REPO_ROOT / "bridge"
DEFAULT_OUT = DEFAULT_BRIDGE_ROOT / "discovery_corridor_audit.json"
SCHEMA_PATH = REPO_ROOT / "schema/sophia/discovery_corridor_audit_v1.schema.json"

AUDIT_SCHEMA = "sophia/discovery_corridor_audit_v1"
CAUTION = (
    "This audit is advisory-only (watch/docket). It does not authorize governance action, "
    "closure, canon formation, or suppression. It supports keep-open stewardship and legibility."
)
CORRIDOR_WATCH_THRESHOLD = 0.25
CORRIDOR_WARN_THRESHOLD = 0.50


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _resolve_bridge_file(bridge_root: Path, filename: str) -> Path | None:
    direct = bridge_root / filename
    nested = bridge_root / "bridge" / filename
    if direct.exists():
        return direct
    if nested.exists():
        return nested
    return None


def _extract_corridor_potential(payload: dict[str, Any]) -> float:
    for path in (
        ("corridorPotential",),
        ("discoveryCorridorMap", "corridorPotential"),
        ("targets", 0, "corridorPotential"),
    ):
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
                    "id": "corridor.missingInput",
                    "severity": "warn",
                    "type": "audit",
                    "advisory": "docket",
                    "message": "Missing discovery_corridor_map.json; unable to evaluate corridor formation. Docket for review.",
                    "data": {"expectedFile": "discovery_corridor_map.json"},
                }
            ],
        }
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    corridor = _load_json(corridor_path)
    corridor_potential = _extract_corridor_potential(corridor)

    if corridor_potential >= CORRIDOR_WARN_THRESHOLD:
        decision = "warn"
        findings = [
            {
                "id": "corridor.forming",
                "severity": "warn",
                "type": "audit",
                "advisory": "watch",
                "message": f"Corridor potential is elevated ({corridor_potential:.3f}). Encourage plural exploration; avoid premature consolidation.",
                "data": {"corridorPotential": round(corridor_potential, 6)},
            }
        ]
    elif corridor_potential >= CORRIDOR_WATCH_THRESHOLD:
        decision = "info"
        findings = [
            {
                "id": "corridor.incipient",
                "severity": "info",
                "type": "audit",
                "advisory": "watch",
                "message": f"Corridor potential is present ({corridor_potential:.3f}). Maintain keep-open posture and legibility.",
                "data": {"corridorPotential": round(corridor_potential, 6)},
            }
        ]
    else:
        decision = "info"
        findings = [
            {
                "id": "corridor.low",
                "severity": "info",
                "type": "audit",
                "advisory": "watch",
                "message": f"Corridor potential is low ({corridor_potential:.3f}). No action implied; continue monitoring.",
                "data": {"corridorPotential": round(corridor_potential, 6)},
            }
        ]

    payload = {
        "schema": AUDIT_SCHEMA,
        "created_at": _utc_now_iso(),
        "caution": CAUTION,
        "decision": decision,
        "findings": findings,
    }
    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
    return payload


def audit_discovery_corridor_state(bridge_root: str, out_file: str | None = None) -> dict[str, Any]:
    payload = build_outputs(bridge_root=Path(bridge_root))
    if out_file is not None:
        out_path = Path(out_file)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return payload


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bridge-root", type=Path, required=True)
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = ap.parse_args(argv)

    payload = build_outputs(bridge_root=args.bridge_root)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"[ok] wrote discovery corridor audit: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
