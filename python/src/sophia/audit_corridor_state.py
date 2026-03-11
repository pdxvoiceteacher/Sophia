from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

CORRIDOR_MAP_PATH = BRIDGE_DIR / "corridor_map.json"
CORRIDOR_AUDIT_OUT = BRIDGE_DIR / "corridor_audit.json"
CORRIDOR_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "corridor_audit_v1.schema.json"

CORRIDOR_EMERGING = 0.72


class CorridorInputError(RuntimeError):
    pass


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _save_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _parse_targets(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows = payload.get("targets")
    return [row for row in rows if isinstance(row, dict)] if isinstance(rows, list) else []


def evaluate_target(target: dict[str, Any]) -> dict[str, Any]:
    target_id = str(target.get("targetId") or "target:unknown")

    if "corridorPotential" not in target:
        return {
            "targetId": target_id,
            "severity": "warn",
            "type": "missing-fields",
            "message": "Missing corridorPotential; fail-closed docket review required.",
            "advisory": "docket",
            "notes": ["review source map completeness"],
        }

    potential = float(target.get("corridorPotential", 0.0)) if isinstance(target.get("corridorPotential"), (int, float)) else 0.0

    if potential >= CORRIDOR_EMERGING:
        return {
            "targetId": target_id,
            "severity": "info",
            "type": "corridor-emerging",
            "message": "Plurality and dissent rising; possible new discovery corridor forming.",
            "advisory": "watch",
            "notes": ["monitor emerging threads"],
        }

    return {
        "targetId": target_id,
        "severity": "info",
        "type": "corridor-stable",
        "message": "Corridor indicators remain stable; continue bounded watch-state monitoring.",
        "advisory": "watch",
        "notes": ["monitor emerging threads"],
    }


def build_outputs() -> dict[str, Any]:
    if not CORRIDOR_MAP_PATH.exists():
        raise CorridorInputError(f"Missing required artifact: {CORRIDOR_MAP_PATH}")

    source = _load_json(CORRIDOR_MAP_PATH)
    targets = _parse_targets(source)
    if not targets:
        raise CorridorInputError("corridor_map.json must contain a non-empty targets list")

    findings = [evaluate_target(target) for target in targets]
    findings = sorted(findings, key=lambda item: (item["targetId"], item["severity"], item["type"]))

    payload = {
        "schema": "corridor_audit_v1",
        "created_at": str(source.get("generatedAt") or "1970-01-01T00:00:00Z"),
        "caution": "Bounded advisory only; no path closure, no governance transfer, no canonical settlement.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": findings,
    }

    Draft202012Validator(_load_json(CORRIDOR_AUDIT_SCHEMA_PATH)).validate(payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia corridor state audit")
    parser.parse_args(argv)

    payload = build_outputs()
    _save_json(CORRIDOR_AUDIT_OUT, payload)
    print(f"Wrote {CORRIDOR_AUDIT_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
