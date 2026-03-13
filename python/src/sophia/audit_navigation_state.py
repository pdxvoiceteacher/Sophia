from __future__ import annotations

import argparse
import json
from pathlib import Path

from sophia.schema import validate_json_lines


def audit_navigation_state(bridge_root: Path, output_file: Path) -> None:
    nav_path = bridge_root / "bridge" / "navigation_state.json"
    findings: list[dict[str, object]] = []

    if not nav_path.exists():
        findings.append(
            {
                "finding": "navigation.missing",
                "severity": "warn",
                "advisory": "docket",
                "semanticMode": "non-executive",
            }
        )
    else:
        data = json.loads(nav_path.read_text(encoding="utf-8-sig"))
        chosen = data.get("chosen_state") if isinstance(data, dict) else None
        if not chosen:
            findings.append(
                {
                    "finding": "navigation.empty",
                    "severity": "warn",
                    "advisory": "watch",
                    "semanticMode": "non-executive",
                }
            )
        else:
            psi_val = data.get("chosen_state_psi", 0)
            if isinstance(psi_val, (int, float)) and psi_val < 0.1:
                findings.append(
                    {
                        "finding": "navigation.low_coherence",
                        "severity": "info",
                        "advisory": "watch",
                        "semanticMode": "non-executive",
                        "target": str(chosen),
                    }
                )

    output_file.parent.mkdir(parents=True, exist_ok=True)
    with output_file.open("w", encoding="utf-8") as f:
        for record in findings:
            f.write(json.dumps(record, sort_keys=True) + "\n")

    validate_json_lines(output_file, schema="navigation_audit")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit navigation state to advisory JSONL.")
    parser.add_argument("--bridge-root", required=True, type=Path, help="Path to bridge root.")
    parser.add_argument("--out", required=True, type=Path, help="Output JSONL file for audit findings.")
    args = parser.parse_args(argv)
    audit_navigation_state(args.bridge_root, args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
