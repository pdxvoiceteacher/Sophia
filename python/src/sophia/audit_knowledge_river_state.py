from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BRIDGE_ROOT = REPO_ROOT / "bridge"
DEFAULT_OUT = DEFAULT_BRIDGE_ROOT / "knowledge_river_audit.json"
SCHEMA_PATH = REPO_ROOT / "schema/knowledge_river_audit_v1.schema.json"



def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _fail_closed(created_at: str, reason: str) -> dict[str, Any]:
    return {
        "schema": "knowledge_river_audit_v1",
        "created_at": created_at,
        "caution": "Bounded advisory only; use watch/docket follow-up and avoid authority-transfer or closure claims.",
        "decision": "warn",
        "findings": [
            {
                "id": "river:map",
                "severity": "warn",
                "type": "docket-review",
                "advisory": "docket",
                "message": f"Missing or invalid river inputs; fail-closed docket review required ({reason}).",
                "data": {"missing": reason},
            }
        ],
    }




def _resolve_bridge_root(bridge_root: Path) -> Path:
    nested = bridge_root / "bridge"
    return nested if nested.exists() else bridge_root


def build_outputs(*, bridge_root: Path = DEFAULT_BRIDGE_ROOT) -> dict[str, Any]:
    river_path = bridge_root / "knowledge_river_map.json"
    risk_path = bridge_root / "river_capture_risk_report.json"

    if not river_path.exists() or not risk_path.exists():
        payload = _fail_closed("1970-01-01T00:00:00Z", "knowledge_river_map.json or river_capture_risk_report.json")
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    river_doc = _load_json(river_path)
    risk_doc = _load_json(risk_path)
    rivers = [r for r in river_doc.get("rivers", []) if isinstance(r, dict)]
    if not rivers:
        payload = _fail_closed(str(river_doc.get("generatedAt") or "1970-01-01T00:00:00Z"), "rivers[]")
        Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
        return payload

    risk_rows = [r for r in risk_doc.get("rivers", []) if isinstance(r, dict)]
    risk_index = {str(r.get("id") or r.get("riverId")): float(r.get("captureRisk", 0.0)) for r in risk_rows if isinstance(r.get("captureRisk"), (int, float))}

    findings: list[dict[str, Any]] = []
    for river in rivers:
        rid = str(river.get("id") or river.get("riverId") or "river:unknown")
        capture_risk = float(risk_index.get(rid, 0.0))
        strength = float(river.get("riverStrength", 0.0)) if isinstance(river.get("riverStrength"), (int, float)) else 0.0
        if capture_risk >= 0.65:
            findings.append(
                {
                    "id": rid,
                    "severity": "warn",
                    "type": "capture-risk",
                    "advisory": "docket",
                    "message": "River capture risk is elevated; review dissent pathways and keep-open alternatives.",
                    "data": {"riverStrength": round(strength, 6), "captureRisk": round(capture_risk, 6), "invariantHash": river_doc.get("invariantHash")},
                }
            )
        else:
            findings.append(
                {
                    "id": rid,
                    "severity": "info",
                    "type": "within-bounds",
                    "advisory": "watch",
                    "message": "River indicators are within bounded ranges; continue watch-state monitoring.",
                    "data": {"riverStrength": round(strength, 6), "captureRisk": round(capture_risk, 6), "invariantHash": river_doc.get("invariantHash")},
                }
            )

    payload = {
        "schema": "knowledge_river_audit_v1",
        "created_at": str(river_doc.get("generatedAt") or risk_doc.get("generatedAt") or "1970-01-01T00:00:00Z"),
        "caution": "Bounded advisory only; use watch/docket follow-up and avoid authority-transfer or closure claims.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": sorted(findings, key=lambda x: (x["id"], x["severity"], x["type"])),
    }
    Draft202012Validator(_load_json(SCHEMA_PATH)).validate(payload)
    return payload


def audit_knowledge_river_state(bridge_root: str, output_file: str | None = None) -> dict[str, Any]:
    """Compatibility entrypoint used by existing callers/tests."""
    payload = build_outputs(bridge_root=_resolve_bridge_root(Path(bridge_root)))
    if output_file is not None:
        Path(output_file).write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia knowledge river state audit")
    parser.add_argument("--bridge-root", type=Path, default=DEFAULT_BRIDGE_ROOT)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args(argv)

    payload = build_outputs(bridge_root=_resolve_bridge_root(args.bridge_root))
    args.out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
