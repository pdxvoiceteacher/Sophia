from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BRIDGE_ROOT = REPO_ROOT / "bridge"
DEFAULT_OUT = DEFAULT_BRIDGE_ROOT / "cascade_audit.json"
SCHEMA_PATH = REPO_ROOT / "schema/cascade_audit_v1.schema.json"

HEALTH_WARN_THRESHOLD = 0.5


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _fail_closed(reason: str, created_at: str = "1970-01-01T00:00:00Z") -> dict[str, Any]:
    return {
        "schema": "cascade_audit_v1",
        "created_at": created_at,
        "caution": "Bounded advisory only; findings are watch/docket guidance and do not authorize closure, suppression, merger, or authority transfer.",
        "decision": "warn",
        "findings": [
            {
                "id": "cascade.missingInput",
                "severity": "warn",
                "type": "audit",
                "advisory": "docket",
                "message": f"Cascade map input missing or invalid; fail-closed review required ({reason}).",
                "data": {},
            }
        ],
    }


def build_outputs(*, bridge_root: Path = DEFAULT_BRIDGE_ROOT) -> dict[str, Any]:
    path = bridge_root / "coherence_cascade_map.json"
    if not path.exists():
        payload = _fail_closed("coherence_cascade_map.json")
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    doc = _load_json(path)
    created_at = str(doc.get("generatedAt") or "1970-01-01T00:00:00Z")

    cascade = doc.get("coherenceCascadeMap")
    if not isinstance(cascade, dict):
        payload = _fail_closed("coherenceCascadeMap", created_at)
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    health = cascade.get("cascadeHealth")
    if not isinstance(health, (int, float)):
        payload = _fail_closed("cascadeHealth", created_at)
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    if float(health) < HEALTH_WARN_THRESHOLD:
        findings = [
            {
                "id": "cascade.healthLow",
                "severity": "warn",
                "type": "audit",
                "advisory": "watch",
                "message": f"Cascade health is low ({float(health):.2f}); knowledge propagation is fragile.",
                "data": {"cascadeHealth": round(float(health), 6)},
            }
        ]
    else:
        findings = [
            {
                "id": "cascade.healthStable",
                "severity": "info",
                "type": "audit",
                "advisory": "watch",
                "message": f"Cascade health is stable ({float(health):.2f}).",
                "data": {"cascadeHealth": round(float(health), 6)},
            }
        ]

    payload = {
        "schema": "cascade_audit_v1",
        "created_at": created_at,
        "caution": "Bounded advisory only; findings are watch/docket guidance and do not authorize closure, suppression, merger, or authority transfer.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": findings,
    }

    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
    return payload


def audit_cascade_state(bridge_root: str, output_file: str) -> None:
    """Compatibility entrypoint used by existing callers/tests."""
    payload = build_outputs(bridge_root=Path(bridge_root))
    Path(output_file).write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia cascade state audit")
    parser.add_argument("--bridge-root", type=Path, default=DEFAULT_BRIDGE_ROOT)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args(argv)

    payload = build_outputs(bridge_root=args.bridge_root)
    args.out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
