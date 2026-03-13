import json
from pathlib import Path
from datetime import datetime

NAV_LOW_PSI = 0.10


def advisory_record(finding: str, severity: str, advisory: str, target: str | None = None):
    rec = {
        "finding": finding,
        "severity": severity,
        "advisory": advisory,
        "semanticMode": "non-executive",
        "created_at": datetime.utcnow().isoformat() + "Z"
    }
    if target is not None:
        rec["target"] = target
    return rec


def audit_navigation_state(bridge_root: Path, out_file: Path):
    nav_path = bridge_root / "bridge" / "navigation_state.json"
    out_file.parent.mkdir(parents=True, exist_ok=True)
    if not nav_path.exists():
        rec = advisory_record("navigation.missing", "warn", "docket")
        with open(out_file, "w") as f:
            f.write(json.dumps(rec) + "\n")
        return
    nav = json.loads(nav_path.read_text())
    chosen = nav.get("chosen_state")
    if not chosen:
        rec = advisory_record("navigation.empty", "warn", "watch")
        with open(out_file, "w") as f:
            f.write(json.dumps(rec) + "\n")
        return
    psi = nav.get("artifactLineageHashes", {}).get("psi", 0.0)
    if psi < NAV_LOW_PSI:
        rec = advisory_record("navigation.low_coherence", "info", "watch", target=chosen)
        with open(out_file, "w") as f:
            f.write(json.dumps(rec) + "\n")
        return
    rec = advisory_record("navigation.ok", "info", "watch", target=chosen)
    with open(out_file, "w") as f:
        f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", required=True)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    audit_navigation_state(Path(args.bridge_root), Path(args.out))
