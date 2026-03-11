from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

REBRAID_SIGNAL_MAP_PATH = BRIDGE_DIR / "rebraid_signal_map.json"
REBRAID_AUDIT_OUT = BRIDGE_DIR / "rebraid_audit.json"
REBRAID_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "rebraid_audit_v1.schema.json"

REBRAID_INFO_THRESHOLD = 0.68


class RebraidInputError(RuntimeError):
    pass


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _save_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _parse_targets(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows = payload.get("targets")
    return [r for r in rows if isinstance(r, dict)] if isinstance(rows, list) else []


def _docket_finding(target_id: str, missing: list[str]) -> dict[str, Any]:
    return {
        "id": target_id,
        "severity": "warn",
        "type": "docket-review",
        "message": "Missing or invalid rebraid inputs; fail-closed docket review required.",
        "advisory": "docket",
        "data": {"missingFields": missing, "rebraidPotential": 0.0},
    }


def evaluate_target(target: dict[str, Any]) -> dict[str, Any]:
    target_id = str(target.get("targetId") or "target:unknown")

    required = ("rebraidPotential", "rebraidAlert")
    missing = [k for k in required if k not in target]
    if missing:
        return _docket_finding(target_id, missing)

    potential = target.get("rebraidPotential")
    alert = target.get("rebraidAlert")
    if not isinstance(potential, (int, float)) or not isinstance(alert, bool):
        return _docket_finding(target_id, ["rebraidPotential", "rebraidAlert"])

    if alert or float(potential) >= REBRAID_INFO_THRESHOLD:
        return {
            "id": target_id,
            "severity": "info",
            "type": "rebraiding-emerging",
            "message": "Mutual translation and shared invariants have increased (partial braid forming).",
            "advisory": "watch",
            "data": {"rebraidPotential": round(float(potential), 6)},
        }

    return {
        "id": target_id,
        "severity": "info",
        "type": "within-bounds",
        "message": "Rebraid indicators remain bounded; continue watch-state monitoring without merger claims.",
        "advisory": "watch",
        "data": {"rebraidPotential": round(float(potential), 6)},
    }


def build_outputs() -> dict[str, Any]:
    if not REBRAID_SIGNAL_MAP_PATH.exists():
        raise RebraidInputError(f"Missing required artifact: {REBRAID_SIGNAL_MAP_PATH}")

    source = _load_json(REBRAID_SIGNAL_MAP_PATH)
    targets = _parse_targets(source)
    findings = [_docket_finding("rebraid:map", ["targets"])] if not targets else [evaluate_target(t) for t in targets]
    findings = sorted(findings, key=lambda x: (x["id"], x["severity"], x["type"]))

    payload = {
        "schema": "rebraid_audit_v1",
        "created_at": str(source.get("generatedAt") or "1970-01-01T00:00:00Z"),
        "caution": "Bounded advisory only; findings are watch/docket guidance and do not authorize merger, suppression, or legitimacy closure.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": findings,
    }

    Draft202012Validator(_load_json(REBRAID_AUDIT_SCHEMA_PATH)).validate(payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia rebraid state audit")
    parser.parse_args(argv)

    payload = build_outputs()
    _save_json(REBRAID_AUDIT_OUT, payload)
    print(f"Wrote {REBRAID_AUDIT_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
