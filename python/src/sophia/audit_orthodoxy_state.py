from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

ORTHODOXY_MAP_PATH = BRIDGE_DIR / "orthodoxy_map.json"
ORTHODOXY_AUDIT_OUT = BRIDGE_DIR / "orthodoxy_audit.json"
ORTHODOXY_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "orthodoxy_audit_v1.schema.json"

ORTHODOXY_SCORE_WARN = 0.75


class OrthodoxyInputError(RuntimeError):
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

    if "orthodoxyScore" not in target and "orthodoxyAlert" not in target:
        return {
            "targetId": target_id,
            "severity": "warn",
            "type": "missing-fields",
            "message": "Missing orthodoxy fields; fail-closed docket review required.",
            "advisory": "docket",
            "notes": ["review narrative bias", "investigate suppressed alternatives"],
        }

    orthodoxy_score = float(target.get("orthodoxyScore", 0.0)) if isinstance(target.get("orthodoxyScore"), (int, float)) else 0.0
    orthodoxy_alert = bool(target.get("orthodoxyAlert", False))

    if orthodoxy_alert or orthodoxy_score >= ORTHODOXY_SCORE_WARN:
        return {
            "targetId": target_id,
            "severity": "warn",
            "type": "orthodoxy-risk",
            "message": "High capture/plurality collapse detected (false-orthodoxy signature). Watch for coerced coherence.",
            "advisory": "docket",
            "notes": ["review narrative bias", "investigate suppressed alternatives"],
        }

    return {
        "targetId": target_id,
        "severity": "info",
        "type": "within-bounds",
        "message": "Orthodoxy pressure is within bounded plurality-watch ranges.",
        "advisory": "watch",
        "notes": ["monitor dissent visibility"],
    }


def build_outputs() -> dict[str, Any]:
    if not ORTHODOXY_MAP_PATH.exists():
        raise OrthodoxyInputError(f"Missing required artifact: {ORTHODOXY_MAP_PATH}")

    source = _load_json(ORTHODOXY_MAP_PATH)
    targets = _parse_targets(source)
    if not targets:
        raise OrthodoxyInputError("orthodoxy_map.json must contain a non-empty targets list")

    findings = [evaluate_target(target) for target in targets]
    findings = sorted(findings, key=lambda item: (item["targetId"], item["severity"], item["type"]))

    payload = {
        "schema": "orthodoxy_audit_v1",
        "created_at": str(source.get("generatedAt") or "1970-01-01T00:00:00Z"),
        "caution": "Bounded advisory only; no path closure, no governance transfer, no canonical settlement.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": findings,
    }

    Draft202012Validator(_load_json(ORTHODOXY_AUDIT_SCHEMA_PATH)).validate(payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia orthodoxy state audit")
    parser.parse_args(argv)

    payload = build_outputs()
    _save_json(ORTHODOXY_AUDIT_OUT, payload)
    print(f"Wrote {ORTHODOXY_AUDIT_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
