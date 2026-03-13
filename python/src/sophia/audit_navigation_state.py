from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from jsonschema import Draft7Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/navigation_audit_v1.schema.json"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        for row in rows:
            f.write(json.dumps(row, sort_keys=True) + "\n")


def audit_navigation_state(bridge_root: Path, out_file: Path) -> dict[str, Any]:
    """Advisory-only audit for navigation decisions."""
    nav_path = bridge_root / "bridge" / "navigation_state.json"

    if not nav_path.exists():
        findings = [{"finding": "navigation.missing", "severity": "warn", "advisory": "docket"}]
        result = {
            "findings": findings,
            "decision": "fail",
            "caution": "Navigation state missing; review required.",
            "created_at": datetime.now(timezone.utc).isoformat(),
            "semanticMode": "non-executive",
        }
        Draft7Validator(_load_json(SCHEMA_PATH)).validate(result)
        _write_jsonl(out_file, [result])
        return result

    nav = _load_json(nav_path)
    chosen = nav.get("chosen_state", {}) if isinstance(nav, dict) else {}
    findings: list[dict[str, str]] = []

    psi = chosen.get("psi", 0.0) if isinstance(chosen, dict) else 0.0
    if isinstance(psi, (int, float)) and psi < 0.1:
        findings.append(
            {"finding": "navigation.low_coherence", "severity": "warn", "advisory": "watch"}
        )

    decision = "pass" if not findings else "warn"
    result = {
        "findings": findings,
        "decision": decision,
        "caution": "Review navigation if warnings.",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "semanticMode": "non-executive",
    }

    Draft7Validator(_load_json(SCHEMA_PATH)).validate(result)
    _write_jsonl(out_file, [result])
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit navigation state (advisory only).")
    parser.add_argument("--bridge-root", default=".", help="CoherenceLattice root")
    parser.add_argument("--out", required=True, help="Output JSONL file")
    args = parser.parse_args(argv)

    audit_navigation_state(Path(args.bridge_root), Path(args.out))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
