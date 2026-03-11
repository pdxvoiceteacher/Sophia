from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BRIDGE_ROOT = REPO_ROOT / "bridge"
DEFAULT_OUT = DEFAULT_BRIDGE_ROOT / "civilizational_delta_audit.json"
SCHEMA_PATH = REPO_ROOT / "schema/civilizational_delta_audit_v1.schema.json"
DELTA_WARN_THRESHOLD = 10.0


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _fail_closed(reason: str, created_at: str = "1970-01-01T00:00:00Z") -> dict[str, Any]:
    return {
        "schema": "civilizational_delta_audit_v1",
        "created_at": created_at,
        "caution": "Bounded advisory only; use watch/docket follow-up and avoid closure or authority claims.",
        "decision": "warn",
        "findings": [
            {
                "id": "delta:map",
                "severity": "warn",
                "type": "docket-review",
                "advisory": "docket",
                "message": f"Missing or invalid delta inputs; fail-closed docket review required ({reason}).",
                "data": {"missing": reason},
            }
        ],
    }


def build_outputs(*, bridge_root: Path = DEFAULT_BRIDGE_ROOT) -> dict[str, Any]:
    path = bridge_root / "civilizational_delta_map.json"
    if not path.exists():
        payload = _fail_closed("civilizational_delta_map.json")
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    doc = _load_json(path)
    targets = [r for r in doc.get("targets", []) if isinstance(r, dict)]
    if not targets:
        payload = _fail_closed("targets[]", str(doc.get("generatedAt") or "1970-01-01T00:00:00Z"))
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    findings: list[dict[str, Any]] = []
    for row in targets:
        tid = str(row.get("phaseId") or row.get("targetId") or "delta:unknown")
        strength = row.get("deltaStrength")
        alert = row.get("deltaAlert")
        if not isinstance(strength, (int, float)) or not isinstance(alert, bool):
            findings.append(
                {
                    "id": tid,
                    "severity": "warn",
                    "type": "docket-review",
                    "advisory": "docket",
                    "message": "Invalid delta fields; fail-closed docket review required.",
                    "data": {"invariantHash": doc.get("invariantHash")},
                }
            )
            continue

        if float(strength) > DELTA_WARN_THRESHOLD or alert:
            findings.append(
                {
                    "id": tid,
                    "severity": "warn",
                    "type": "delta-risk",
                    "advisory": "watch",
                    "message": f"High delta reorganization strength ({float(strength):.3f}). Monitor for stability.",
                    "data": {"deltaStrength": round(float(strength), 6), "deltaAlert": alert, "invariantHash": doc.get("invariantHash")},
                }
            )
        else:
            findings.append(
                {
                    "id": tid,
                    "severity": "info",
                    "type": "within-bounds",
                    "advisory": "watch",
                    "message": "Delta indicators are bounded; continue watch-state monitoring.",
                    "data": {"deltaStrength": round(float(strength), 6), "deltaAlert": alert, "invariantHash": doc.get("invariantHash")},
                }
            )

    payload = {
        "schema": "civilizational_delta_audit_v1",
        "created_at": str(doc.get("generatedAt") or "1970-01-01T00:00:00Z"),
        "caution": "Bounded advisory only; use watch/docket follow-up and avoid closure or authority claims.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": sorted(findings, key=lambda x: (x["id"], x["severity"], x["type"])),
    }
    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia civilizational delta audit")
    parser.add_argument("--bridge-root", type=Path, default=DEFAULT_BRIDGE_ROOT)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args(argv)

    payload = build_outputs(bridge_root=args.bridge_root)
    args.out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
