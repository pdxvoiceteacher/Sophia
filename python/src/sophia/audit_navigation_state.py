from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft7Validator

SEMANTIC = "non-executive"
FIELD = "chosen_state"
DOCKET = {"finding": "navigation.missing", "severity": "warn", "advisory": "docket"}
REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "python/src/sophia/schemas/navigation_audit.json"


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        for row in rows:
            f.write(json.dumps(row, sort_keys=True) + "\n")


def audit_navigation_state(bridge_root: Path, out_file: Path) -> list[dict[str, Any]]:
    nav_path = bridge_root / "bridge" / "navigation_state.json"
    findings: list[dict[str, Any]] = []

    if not nav_path.exists():
        findings.append(DOCKET.copy())
    else:
        data = _load_json(nav_path)
        chosen = data.get(FIELD, {}) if isinstance(data, dict) else {}
        if not chosen:
            findings.append(DOCKET.copy())
        elif isinstance(chosen, dict):
            for node, _ in chosen.items():
                psi_val = data.get("artifactLineageHashes", {}).get(node, {}).get("psi", 0)
                if isinstance(psi_val, (int, float)) and psi_val < 0.1:
                    findings.append(
                        {
                            "finding": "navigation.low_coherence",
                            "severity": "info",
                            "advisory": "watch",
                            "target": node,
                        }
                    )

    schema = _load_json(SCHEMA_PATH)
    rows: list[dict[str, Any]] = []
    for finding in findings:
        rec = dict(finding)
        rec["semanticMode"] = SEMANTIC
        Draft7Validator(schema).validate(rec)
        rows.append(rec)

    _write_jsonl(out_file, rows)
    return rows


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit navigation_state.json")
    parser.add_argument("--bridge-root", required=True, help="CoherenceLattice repo root")
    parser.add_argument("--out", required=True, help="Output JSONL file")
    args = parser.parse_args(argv)

    audit_navigation_state(Path(args.bridge_root), Path(args.out))
    print(f"Navigation audit written to {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
