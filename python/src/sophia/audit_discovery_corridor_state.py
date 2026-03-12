from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/discovery_corridor_audit_v1.schema.json"
THRESHOLD_LOW = 0.1


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def audit_discovery_corridor_state(bridge_root: str, out_file: str | None = None) -> dict[str, Any]:
    path = Path(bridge_root) / "bridge" / "discovery_corridor_map.json"
    findings: list[dict[str, Any]] = []

    if not path.exists():
        findings.append(
            {
                "id": "discovery_corridor.missing",
                "severity": "warn",
                "type": "audit",
                "advisory": "docket",
                "message": "Discovery corridor data missing",
                "data": {},
            }
        )
        result = {"findings": findings}
    else:
        data = _load_json(path)
        corridors = data.get("corridors", [])
        if isinstance(corridors, list):
            for corridor in corridors:
                if not isinstance(corridor, dict):
                    continue
                strength = corridor.get("strength", 0)
                if isinstance(strength, (int, float)) and strength < THRESHOLD_LOW:
                    findings.append(
                        {
                            "id": "discovery_corridor.lowPotential",
                            "severity": "warn",
                            "type": "audit",
                            "advisory": "watch",
                            "message": "Low corridor potential",
                            "data": {"id": corridor.get("id")},
                        }
                    )
        result = {"findings": findings}

    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(result)

    if out_file:
        out_path = Path(out_file)
    else:
        out_path = Path(bridge_root) / "discovery_corridor_audit.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    parser.add_argument("--out", dest="out_file", default=None)
    parser.add_argument("--output-file", dest="out_file", default=None)
    args = parser.parse_args(argv)

    audit_discovery_corridor_state(args.bridge_root, args.out_file)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
