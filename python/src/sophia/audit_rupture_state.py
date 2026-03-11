from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

RUPTURE_SIGNAL_MAP_PATH = BRIDGE_DIR / "rupture_signal_map.json"
RUPTURE_AUDIT_OUT = BRIDGE_DIR / "rupture_audit.json"
RUPTURE_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "rupture_audit_v1.schema.json"

RUPTURE_WARN_THRESHOLD = 1.0


class RuptureInputError(RuntimeError):
    pass


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _save_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _parse_targets(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows = payload.get("targets")
    return [r for r in rows if isinstance(r, dict)] if isinstance(rows, list) else []


def _docket_review(target_id: str, missing_fields: list[str]) -> dict[str, Any]:
    return {
        "id": target_id,
        "severity": "warn",
        "type": "docket-review",
        "advisory": "docket",
        "message": "Missing or invalid rupture inputs; fail-closed docket review required.",
        "data": {"missingFields": missing_fields, "ruptureRatio": 0.0},
    }


def evaluate_target(target: dict[str, Any]) -> dict[str, Any]:
    target_id = str(target.get("phaseId") or target.get("targetId") or "target:unknown")

    required = ("ruptureRatio",)
    missing = [f for f in required if f not in target]
    if missing:
        return _docket_review(target_id, missing)

    ratio = target.get("ruptureRatio")
    if not isinstance(ratio, (int, float)):
        return _docket_review(target_id, ["ruptureRatio"])

    if float(ratio) > RUPTURE_WARN_THRESHOLD:
        return {
            "id": target_id,
            "severity": "warn",
            "type": "rupture-risk",
            "advisory": "watch",
            "message": f"Rupture signal high ({float(ratio):.3f}). Cohesion is at risk.",
            "data": {"ruptureRatio": round(float(ratio), 6)},
        }

    return {
        "id": target_id,
        "severity": "info",
        "type": "within-bounds",
        "advisory": "watch",
        "message": "Rupture indicators are bounded; continue watch-state monitoring.",
        "data": {"ruptureRatio": round(float(ratio), 6)},
    }


def build_outputs() -> dict[str, Any]:
    if not RUPTURE_SIGNAL_MAP_PATH.exists():
        raise RuptureInputError(f"Missing required artifact: {RUPTURE_SIGNAL_MAP_PATH}")

    source = _load_json(RUPTURE_SIGNAL_MAP_PATH)
    targets = _parse_targets(source)
    findings = [_docket_review("rupture:map", ["targets"])] if not targets else [evaluate_target(t) for t in targets]
    findings = sorted(findings, key=lambda r: (r["id"], r["severity"], r["type"]))

    payload = {
        "schema": "rupture_audit_v1",
        "created_at": str(source.get("generatedAt") or "1970-01-01T00:00:00Z"),
        "caution": "Bounded advisory only; use watch/docket follow-up and do not infer final legitimacy or closure.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": findings,
    }

    Draft202012Validator(_load_json(RUPTURE_AUDIT_SCHEMA_PATH)).validate(payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia rupture state audit")
    parser.parse_args(argv)

    payload = build_outputs()
    _save_json(RUPTURE_AUDIT_OUT, payload)
    print(f"Wrote {RUPTURE_AUDIT_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
