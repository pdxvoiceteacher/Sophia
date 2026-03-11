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
        "id": "REBRAID_MISSING",
        "severity": "warn",
        "type": "rebraid",
        "advisory": "docket",
        "message": f"Missing rebraid signal map input; requires executive review ({reason}).",
        "data": {},
    }


def _evaluate_strength(target_id: str, strength: float) -> dict[str, Any]:
    if strength < 0.3:
        return {
            "id": f"REBRAID_WEAK:{target_id}",
            "severity": "info",
            "type": "rebraid",
            "advisory": "watch",
            "message": "Rebraid strength is low; cross-domain reintegration appears limited.",
            "data": {"rebraidStrength": round(strength, 6)},
        }
    return {
        "id": f"REBRAID_STRONG:{target_id}",
        "severity": "warn",
        "type": "rebraid",
        "advisory": "watch",
        "message": "Rebraid strength is high; strong cross-domain convergence detected.",
        "data": {"rebraidStrength": round(strength, 6)},
    }


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

    findings: list[dict[str, Any]] = []
    if isinstance(source.get("rebraidStrength"), (int, float)):
        findings.append(_evaluate_strength("root", float(source["rebraidStrength"])))
    else:
        targets = [r for r in source.get("targets", []) if isinstance(r, dict)] if isinstance(source.get("targets"), list) else []
        for row in targets:
            target_id = str(row.get("targetId") or "target:unknown")
            if isinstance(row.get("rebraidStrength"), (int, float)):
                findings.append(_evaluate_strength(target_id, float(row["rebraidStrength"])))
                continue
            if isinstance(row.get("rebraidPotential"), (int, float)):
                findings.append(_evaluate_strength(target_id, float(row["rebraidPotential"])))

    if not findings:
        findings = [_docket_finding("rebraidStrength/rebraidPotential")]

    payload = {
        "schema": "rebraid_audit_v1",
        "created_at": created_at,
        "caution": "Bounded advisory only; findings are watch/docket guidance and do not authorize merger, suppression, closure, or authority transfer.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": findings,
    }
    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit rebraid state")
    parser.add_argument("--bridge-root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)

    payload = build_outputs(bridge_root=args.bridge_root)
    args.out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
