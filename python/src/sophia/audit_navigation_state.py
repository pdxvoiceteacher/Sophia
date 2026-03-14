from __future__ import annotations

import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

NAV_LOW_PSI = 0.10


def advisory_record(
    finding: str,
    severity: str,
    advisory: str,
    target: str | None = None,
) -> dict[str, Any]:
    rec: dict[str, Any] = {
        "finding": finding,
        "severity": severity,
        "advisory": advisory,
        "semanticMode": "non-executive",
        "created_at": datetime.now(UTC).isoformat().replace("+00:00", "Z"),
    }
    if target:
        rec["target"] = target
    return rec


def _write_jsonl_record(out_file: Path, rec: dict[str, Any]) -> None:
    out_file.write_text(json.dumps(rec) + "\n", encoding="utf-8")


def audit_navigation_state(bridge_root: Path, out_file: Path) -> None:
    nav_path = bridge_root / "bridge" / "navigation_state.json"
    out_file.parent.mkdir(parents=True, exist_ok=True)

    if not nav_path.exists():
        _write_jsonl_record(out_file, advisory_record("navigation.missing", "warn", "docket"))
        return

    nav = json.loads(nav_path.read_text(encoding="utf-8"))
    chosen = nav.get("chosen_state")
    if not chosen:
        _write_jsonl_record(out_file, advisory_record("navigation.empty", "warn", "watch"))
        return

    psi = nav.get("artifactLineageHashes", {}).get("psi", 0.0)
    if psi < NAV_LOW_PSI:
        _write_jsonl_record(
            out_file,
            advisory_record("navigation.low_coherence", "info", "watch", target=str(chosen)),
        )
        return

    _write_jsonl_record(out_file, advisory_record("navigation.ok", "info", "watch", target=str(chosen)))


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    audit_navigation_state(Path(args.bridge_root), Path(args.out))
