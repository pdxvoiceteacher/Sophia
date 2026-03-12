from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BRIDGE_ROOT = REPO_ROOT
DEFAULT_OUT = REPO_ROOT / "bridge" / "discovery_corridor_audit.json"
SCHEMA_PATH = REPO_ROOT / "schema/sophia/discovery_corridor_audit_v1.schema.json"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def audit_discovery_corridor_state(bridge_root: str, output_file: str | None = None) -> dict[str, Any]:
    candidate = Path(bridge_root) / "bridge" / "discovery_corridor_map.json"
    if not candidate.exists():
        findings = [
            {
                "id": "discovery_corridor.missing",
                "severity": "warn",
                "type": "audit",
                "advisory": "docket",
                "message": "Discovery corridor artifact is missing.",
                "data": {},
            }
        ]
        result = {
            "schema": "discovery_corridor_audit_v1",
            "decision": "fail",
            "findings": findings,
            "caution": "Advisory only",
        }
    else:
        data = _load_json(candidate)
        pot = data.get("corridorPotential", 0.0)
        findings: list[dict[str, Any]] = []
        if pot < 0.1:
            findings.append(
                {
                    "id": "discovery_corridor.lowPotential",
                    "severity": "warn",
                    "type": "audit",
                    "advisory": "watch",
                    "message": f"Corridor potential is low ({pot}).",
                    "data": {"corridorPotential": pot},
                }
            )
        result = {
            "schema": "discovery_corridor_audit_v1",
            "decision": "warn" if findings else "pass",
            "findings": findings,
            "caution": "Advisory only",
        }

    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(result)

    if output_file:
        out = Path(output_file)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    parser.add_argument("--out", dest="output_file", default=DEFAULT_OUT)
    parser.add_argument("--output-file", dest="output_file")
    args = parser.parse_args(argv)

    result = audit_discovery_corridor_state(args.bridge_root, str(args.output_file) if args.output_file else None)
    if args.output_file is None:
        print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
