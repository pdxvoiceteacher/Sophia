from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/discovery_corridor_audit_v1.schema.json"
THRESHOLD_LOW = 0.1


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def audit_discovery_corridor_state(input_path: Path, out_path: Path | None = None) -> dict[str, Any]:
    result: dict[str, Any] = {
        "findings": [],
        "decision": "pass",
        "caution": "Advisory only.",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "semanticMode": "non-executive",
    }

    if not input_path.exists():
        result["decision"] = "fail"
        result["findings"].append(
            {
                "id": "discovery_corridor.missing",
                "severity": "warn",
                "type": "audit",
                "advisory": "docket",
                "message": "Discovery corridor map is missing.",
                "data": {},
            }
        )
    else:
        data = _load_json(input_path)
        corridors = data.get("discoveryCorridors", [])
        if isinstance(corridors, list):
            for cor in corridors:
                if not isinstance(cor, dict):
                    continue
                strength = cor.get("strength", 0)
                if isinstance(strength, (int, float)) and strength < THRESHOLD_LOW:
                    result["findings"].append(
                        {
                            "id": "discovery_corridor.lowPotential",
                            "severity": "info",
                            "type": "audit",
                            "advisory": "watch",
                            "message": f"Corridor {cor.get('id')} has low strength.",
                            "data": {"strength": float(cor.get("strength", 0))},
                        }
                    )

    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(result)

    target = out_path if out_path else input_path.parent / "discovery_corridor_audit.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--in", dest="in_file", required=False)
    parser.add_argument("--out", dest="out_file", required=False)
    args = parser.parse_args(argv)

    audit_discovery_corridor_state(Path(args.in_file or ""), Path(args.out_file) if args.out_file else None)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
