from __future__ import annotations

import argparse
import json
from pathlib import Path

from sophia.audit.common import advisory_docket, advisory_watch
from sophia.schema import validate_record


def audit_navigation_state(bridge_root: Path, out_file: Path) -> None:
    """
    Reads bridge/navigation_state.json and writes advisory findings (one JSON per line).
    Emits:
      - navigation.missing (docket) if navigation_state is absent or empty
      - navigation.low_coherence (watch) if chosen_state.psi < threshold
    """
    nav_path = bridge_root / "bridge" / "navigation_state.json"
    out_path = Path(out_file)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    findings: list[dict[str, str]] = []

    if not nav_path.exists():
        findings.append(advisory_docket("navigation.missing", "Navigation state missing or empty"))
    else:
        nav = json.loads(nav_path.read_text(encoding="utf-8-sig"))
        chosen = nav.get("chosen_state") if isinstance(nav, dict) else None
        if not chosen:
            findings.append(advisory_docket("navigation.missing", "Navigation state missing or empty"))
        else:
            psi_val = nav.get("artifactLineageHashes", {}).get("psi", 0.0)
            if isinstance(psi_val, (int, float)) and psi_val < 0.1:
                findings.append(
                    advisory_watch(
                        "navigation.low_coherence",
                        f"Low coherence for chosen state ({psi_val:.2f})",
                        target=chosen,
                    )
                )

    schema_path = Path(__file__).parent / "schemas" / "navigation_audit.json"
    with out_path.open("w", encoding="utf-8") as f:
        for rec in findings:
            validate_record(rec, schema_path)
            f.write(json.dumps(rec, sort_keys=True) + "\n")


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
