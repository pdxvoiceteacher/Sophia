from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path

from sophia.schema import validate_json_lines

NAV_LOW_PSI = 0.10


def advisory_record(finding: str, severity: str, advisory: str, target: str | None = None) -> dict[str, str]:
    rec: dict[str, str] = {
        "finding": finding,
        "severity": severity,
        "advisory": advisory,
        "semanticMode": "non-executive",
        "created_at": datetime.now(timezone.utc).isoformat(),
    }
    if target is not None:
        rec["target"] = target
    return rec


def audit_navigation_state(bridge_root: Path, out_file: Path) -> None:
    nav_path = bridge_root / "bridge" / "navigation_state.json"
    out_file.parent.mkdir(parents=True, exist_ok=True)

    if not nav_path.exists():
        rec = advisory_record("navigation.missing", "warn", "docket")
    else:
        nav = json.loads(nav_path.read_text(encoding="utf-8-sig"))
        chosen = nav.get("chosen_state") if isinstance(nav, dict) else None
        if not chosen:
            rec = advisory_record("navigation.empty", "warn", "watch")
        else:
            psi = nav.get("artifactLineageHashes", {}).get("psi", 0.0)
            if isinstance(psi, (int, float)) and psi < NAV_LOW_PSI:
                rec = advisory_record("navigation.low_coherence", "info", "watch", target=str(chosen))
            else:
                rec = advisory_record("navigation.ok", "info", "watch", target=str(chosen))

    out_file.write_text(json.dumps(rec, sort_keys=True) + "\n", encoding="utf-8")
    validate_json_lines(out_file, schema="navigation_audit")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args(argv)
    audit_navigation_state(Path(args.bridge_root), Path(args.out))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
