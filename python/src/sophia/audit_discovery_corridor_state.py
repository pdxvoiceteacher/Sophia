from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/discovery_corridor_audit_v1.schema.json"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _resolve_corridor_map(bridge_root: Path) -> Path:
    p1 = bridge_root / "bridge" / "discovery_corridor_map.json"
    p2 = bridge_root / "discovery_corridor_map.json"
    return p1 if p1.exists() else p2


def audit_discovery_corridor_state(bridge_root: str, out_file: str | None = None) -> dict[str, Any]:
    candidate = _resolve_corridor_map(Path(bridge_root))
    if not candidate.exists():
        findings = [
            {
                "id": "discovery_corridor.missing",
                "severity": "warn",
                "type": "audit",
                "advisory": "docket",
                "message": "Discovery corridor map missing.",
                "data": {},
            }
        ]
        envelope = {
            "schema": "discovery_corridor_audit_v1",
            "decision": "fail",
            "findings": findings,
        }
    else:
        data = _load_json(candidate)
        findings: list[dict[str, Any]] = []

        corridors = data.get("corridors", [])
        if isinstance(corridors, list):
            for corridor in corridors:
                if not isinstance(corridor, dict):
                    continue
                strength = corridor.get("strength")
                if isinstance(strength, (int, float)) and strength < 0.1:
                    findings.append(
                        {
                            "id": "discovery_corridor.lowPotential",
                            "severity": "warn",
                            "type": "audit",
                            "advisory": "watch",
                            "message": f"Low corridor potential: {float(strength):.2f}",
                            "data": {"id": corridor.get("id"), "strength": float(strength)},
                        }
                    )

        decision = "pass" if not findings else "warn"
        envelope = {
            "schema": "discovery_corridor_audit_v1",
            "decision": decision,
            "findings": findings,
        }

    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(envelope)

    out_path = Path(out_file) if out_file else Path(bridge_root) / "discovery_corridor_audit.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(envelope, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return envelope


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    parser.add_argument("--out", dest="out_file", default=None)
    parser.add_argument("--output-file", dest="out_file", default=None)
    args = parser.parse_args(argv)

    res = audit_discovery_corridor_state(args.bridge_root, args.out_file)
    if not args.out_file:
        print(json.dumps(res, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
