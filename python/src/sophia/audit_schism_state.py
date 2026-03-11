from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
BRIDGE_DIR = REPO_ROOT / "bridge"
SCHEMA_DIR = REPO_ROOT / "schema"

SCHISM_SIGNAL_MAP_PATH = BRIDGE_DIR / "schism_signal_map.json"
SCHISM_AUDIT_OUT = BRIDGE_DIR / "schism_audit.json"
SCHISM_AUDIT_SCHEMA_PATH = SCHEMA_DIR / "schism_audit_v1.schema.json"

SCHISM_WARN_THRESHOLD = 0.72


class SchismInputError(RuntimeError):
    pass


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _save_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def _parse_targets(payload: dict[str, Any]) -> list[dict[str, Any]]:
    targets = payload.get("targets")
    return [t for t in targets if isinstance(t, dict)] if isinstance(targets, list) else []


def _missing_data_finding(target_id: str, missing: list[str]) -> dict[str, Any]:
    return {
        "id": target_id,
        "severity": "warn",
        "type": "missing-data",
        "message": "Missing schism signal fields; fail-closed docket review required.",
        "advisory": "docket",
        "data": {"missingFields": missing},
    }


def evaluate_target(target: dict[str, Any]) -> dict[str, Any]:
    target_id = str(target.get("targetId") or "target:unknown")

    required = ("schismPotential", "sharedPlurality", "schismAlert")
    missing = [k for k in required if k not in target]
    if missing:
        return _missing_data_finding(target_id, missing)

    schism_alert = bool(target.get("schismAlert"))
    schism_potential = float(target.get("schismPotential")) if isinstance(target.get("schismPotential"), (int, float)) else 0.0
    shared_plurality = float(target.get("sharedPlurality")) if isinstance(target.get("sharedPlurality"), (int, float)) else 0.0

    if schism_alert or schism_potential >= SCHISM_WARN_THRESHOLD:
        return {
            "id": target_id,
            "severity": "warn",
            "type": "schism-risk",
            "message": "Rival coherence basins emerging; consider this a bifurcation indicator.",
            "advisory": "docket",
            "data": {
                "schismPotential": round(schism_potential, 6),
                "sharedPlurality": round(shared_plurality, 6),
            },
        }

    return {
        "id": target_id,
        "severity": "info",
        "type": "within-bounds",
        "message": "Schism indicators are within bounded ranges; continue watch-state monitoring.",
        "advisory": "watch",
        "data": {
            "schismPotential": round(schism_potential, 6),
            "sharedPlurality": round(shared_plurality, 6),
        },
    }


def build_outputs() -> dict[str, Any]:
    if not SCHISM_SIGNAL_MAP_PATH.exists():
        raise SchismInputError(f"Missing required artifact: {SCHISM_SIGNAL_MAP_PATH}")

    source = _load_json(SCHISM_SIGNAL_MAP_PATH)
    targets = _parse_targets(source)

    findings = [_missing_data_finding("schism:map", ["targets"]) ] if not targets else [evaluate_target(t) for t in targets]
    findings = sorted(findings, key=lambda x: (x["id"], x["severity"], x["type"]))

    payload = {
        "schema": "schism_audit_v1",
        "created_at": str(source.get("generatedAt") or "1970-01-01T00:00:00Z"),
        "caution": "Bounded advisory only; recommendations are watch/docket signals and do not authorize legitimacy closure.",
        "decision": "warn" if any(f["severity"] == "warn" for f in findings) else "pass",
        "findings": findings,
    }

    Draft202012Validator(_load_json(SCHISM_AUDIT_SCHEMA_PATH)).validate(payload)
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run Sophia schism state audit")
    parser.parse_args(argv)

    payload = build_outputs()
    _save_json(SCHISM_AUDIT_OUT, payload)
    print(f"Wrote {SCHISM_AUDIT_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
