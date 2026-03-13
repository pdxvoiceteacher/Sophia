from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/discovery_corridor_audit_v1.schema.json"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def audit_discovery_corridor_state(bridge_root: str, out_file: str | None = None) -> dict[str, Any]:
    map_path = Path(bridge_root) / "bridge" / "discovery_corridor_map.json"

    try:
        corridors = _load_json(map_path).get("discoveryCorridors", [])
    except FileNotFoundError:
        findings = [
            {
                "id": "discovery_corridor.missing",
                "severity": "warn",
                "type": "audit",
                "advisory": "docket",
                "message": "Discovery corridor map is missing.",
                "data": {},
            }
        ]
        decision = "fail"
    else:
        findings: list[dict[str, Any]] = []
        for corridor in corridors if isinstance(corridors, list) else []:
            if not isinstance(corridor, dict):
                continue
            transfer = corridor.get("transfer")
            if isinstance(transfer, (int, float)) and transfer < 0.1:
                findings.append(
                    {
                        "id": "discovery_corridor.lowPotential",
                        "severity": "warn",
                        "type": "audit",
                        "advisory": "watch",
                        "message": f"Corridor {corridor.get('corridorId')} has low transfer ({transfer}).",
                        "data": {"transfer": float(transfer)},
                    }
                )
        decision = "warn" if findings else "pass"

    audit = {
        "schema": "discovery_corridor_audit_v1",
        "decision": decision,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "caution": "Findings are advisory only. Canonical boundary: non-executive guidance with no authoritative commands.",
        "semanticMode": "non-executive",
        "findings": findings,
    }

    output_path = Path(out_file) if out_file else Path(bridge_root) / "discovery_corridor_audit.json"
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(audit)
    return audit


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    parser.add_argument("--output-file", default=None)
    parser.add_argument("--out", dest="output_file", default=None)
    args = parser.parse_args(argv)

    audit_discovery_corridor_state(args.bridge_root, args.output_file)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
