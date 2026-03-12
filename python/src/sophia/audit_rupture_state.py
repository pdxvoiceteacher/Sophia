from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BRIDGE_ROOT = REPO_ROOT / "bridge"
DEFAULT_OUT = DEFAULT_BRIDGE_ROOT / "rupture_audit.json"
SCHEMA_PATH = REPO_ROOT / "schema/rupture_audit_v1.schema.json"
RUPTURE_WARN_THRESHOLD = 1.0


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _docket_finding(reason: str) -> dict[str, Any]:
    return {
        "schema": "rupture_audit_v1",
        "created_at": "1970-01-01T00:00:00Z",
        "caution": "Bounded advisory only; use watch/docket follow-up and do not infer final legitimacy or closure.",
        "decision": "warn",
        "findings": [
            {
                "id": "rupture:map",
                "severity": "warn",
                "type": "docket-review",
                "advisory": "docket",
                "message": f"Missing or invalid rupture inputs; fail-closed docket review required ({reason}).",
                "data": {"missing": reason},
            }
        ],
    }


def _extract_targets(doc: dict[str, Any]) -> list[dict[str, Any]]:
    if isinstance(doc.get("ruptureRatio"), (int, float)):
        return [doc]
    rows = doc.get("targets")
    return [r for r in rows if isinstance(r, dict)] if isinstance(rows, list) else []




def _resolve_bridge_root(bridge_root: Path) -> Path:
    nested = bridge_root / "bridge"
    return nested if nested.exists() else bridge_root


def build_outputs(*, bridge_root: Path = DEFAULT_BRIDGE_ROOT) -> dict[str, Any]:
    preferred = bridge_root / "rupture_map.json"
    fallback = bridge_root / "rupture_signal_map.json"
    path = preferred if preferred.exists() else fallback
    if not path.exists():
        payload = _docket_finding("rupture_map.json/rupture_signal_map.json")
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    doc = _load_json(path)
    targets = _extract_targets(doc)
    if not targets:
        payload = _docket_finding("ruptureRatio or targets[]")
        payload["created_at"] = str(doc.get("generatedAt") or "1970-01-01T00:00:00Z")
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    findings: list[dict[str, Any]] = []
    for row in targets:
        rid = str(row.get("phaseId") or row.get("targetId") or "rupture:unknown")
        ratio = row.get("ruptureRatio")
        if not isinstance(ratio, (int, float)):
            findings.append(
                {
                    "id": rid,
                    "severity": "warn",
                    "type": "docket-review",
                    "advisory": "docket",
                    "message": "Invalid ruptureRatio; fail-closed docket review required.",
                    "data": {"invariantHash": doc.get("invariantHash")},
                }
            )
            continue
        if float(ratio) > RUPTURE_WARN_THRESHOLD:
            findings.append(
                {
                    "id": rid,
                    "severity": "warn",
                    "type": "rupture-risk",
                    "advisory": "watch",
                    "message": f"Rupture signal high ({float(ratio):.3f}). Cohesion is at risk.",
                    "data": {"ruptureRatio": round(float(ratio), 6), "invariantHash": doc.get("invariantHash")},
                }
            )
        else:
            findings.append(
                {
                    "id": rid,
                    "severity": "info",
                    "type": "within-bounds",
                    "advisory": "watch",
                    "message": "Rupture indicators are bounded; continue watch-state monitoring.",
                    "data": {"ruptureRatio": round(float(ratio), 6), "invariantHash": doc.get("invariantHash")},
                }
            )

    payload = {
        "schema": "rupture_audit_v1",
        "created_at": str(doc.get("generatedAt") or "1970-01-01T00:00:00Z"),
        "caution": "Bounded advisory only; use watch/docket follow-up and do not infer final legitimacy or closure.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": sorted(findings, key=lambda r: (r["id"], r["severity"], r["type"])),
    }
    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
    return payload


def audit_rupture_state(bridge_root: str, output_file: str | None = None) -> dict[str, Any]:
    """Compatibility entrypoint used by existing callers/tests."""
    payload = build_outputs(bridge_root=_resolve_bridge_root(Path(bridge_root)))
    if output_file is not None:
        Path(output_file).write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia rupture state audit")
    parser.add_argument("--bridge-root", type=Path, default=DEFAULT_BRIDGE_ROOT)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args(argv)

    payload = build_outputs(bridge_root=_resolve_bridge_root(args.bridge_root))
    args.out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
