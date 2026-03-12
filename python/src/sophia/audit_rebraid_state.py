from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BRIDGE_ROOT = REPO_ROOT / "bridge"
DEFAULT_OUT = DEFAULT_BRIDGE_ROOT / "rebraid_audit.json"
SCHEMA_PATH = REPO_ROOT / "schema/rebraid_audit_v1.schema.json"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _resolve_rebraid_map(bridge_root: Path) -> Path | None:
    candidates = [bridge_root / "rebraid_signal_map.json", bridge_root / "bridge/rebraid_signal_map.json"]
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return None


def _docket_finding(reason: str) -> dict[str, Any]:
    return {
        "id": "rebraid.missingInput",
        "severity": "warn",
        "type": "rebraid-alert",
        "advisory": "docket",
        "message": f"Missing or invalid rebraid signal input ({reason}); fail-closed docket review required.",
        "data": {},
    }


def _extract_rebraid_state(source: dict[str, Any]) -> tuple[bool | None, float | None]:
    alert: bool | None = source.get("rebraidAlert") if isinstance(source.get("rebraidAlert"), bool) else None
    strength: float | None = float(source["rebraidStrength"]) if isinstance(source.get("rebraidStrength"), (int, float)) else None

    for key in ("targets", "pairs"):
        rows = source.get(key)
        if not isinstance(rows, list):
            continue
        for row in rows:
            if not isinstance(row, dict):
                continue
            if alert is None and isinstance(row.get("rebraidAlert"), bool):
                alert = row["rebraidAlert"]
            if strength is None:
                if isinstance(row.get("rebraidStrength"), (int, float)):
                    strength = float(row["rebraidStrength"])
                elif isinstance(row.get("rebraidPotential"), (int, float)):
                    strength = float(row["rebraidPotential"])
            if alert is not None and strength is not None:
                return alert, strength

    return alert, strength


def build_outputs(*, bridge_root: Path = DEFAULT_BRIDGE_ROOT) -> dict[str, Any]:
    source_path = _resolve_rebraid_map(bridge_root)
    if source_path is None:
        findings = [_docket_finding("rebraid_signal_map.json")]
        payload = {
            "schema": "rebraid_audit_v1",
            "created_at": "1970-01-01T00:00:00Z",
            "caution": "Bounded advisory only; findings are watch/docket guidance and do not authorize merger, suppression, closure, or authority transfer.",
            "decision": "warn",
            "findings": findings,
        }
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    source = _load_json(source_path)
    created_at = str(source.get("generatedAt") or "1970-01-01T00:00:00Z")

    alert, strength = _extract_rebraid_state(source)
    if alert is None and strength is None:
        findings = [_docket_finding("rebraidAlert/rebraidStrength")]
    elif alert is True:
        findings = [
            {
                "id": "rebraid.alert",
                "severity": "warn",
                "type": "rebraid-alert",
                "advisory": "watch",
                "message": "Rebraid alert is active; monitor rebraid risk and keep-open review pathways.",
                "data": {"rebraidAlert": True, "rebraidStrength": None if strength is None else round(strength, 6)},
            }
        ]
    else:
        findings = [
            {
                "id": "rebraid.normal",
                "severity": "info",
                "type": "rebraid-alert",
                "advisory": "watch",
                "message": "Rebraid signal is not alerting; continue watch-state monitoring.",
                "data": {"rebraidAlert": bool(alert) if alert is not None else False, "rebraidStrength": None if strength is None else round(strength, 6)},
            }
        ]

    payload = {
        "schema": "rebraid_audit_v1",
        "created_at": created_at,
        "caution": "Bounded advisory only; findings are watch/docket guidance and do not authorize merger, suppression, closure, or authority transfer.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": findings,
    }
    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
    return payload


def audit_rebraid_state(bridge_root: str, output_file: str) -> None:
    """Compatibility entrypoint used by existing callers/tests."""
    payload = build_outputs(bridge_root=Path(bridge_root))
    Path(output_file).write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit rebraid state")
    parser.add_argument("--bridge-root", type=Path, default=DEFAULT_BRIDGE_ROOT)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args(argv)

    payload = build_outputs(bridge_root=args.bridge_root)
    args.out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
