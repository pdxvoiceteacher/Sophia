from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/ai_guidance_v1.schema.json"


def _load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8-sig"))


def build_ai_guidance(bridge_root: str, out_file: str | None = None) -> dict[str, Any]:
    novelty = 0.0
    plurality = 0.0
    humility = 0.5
    requires_review = False

    audit_specs = [
        ("cascade_audit.json", {"cascade.healthLow": 0.5}),
        ("discovery_corridor_audit.json", {"discovery_corridor.lowPotential": 0.3}),
    ]

    root = Path(bridge_root)
    for audit_file, weight_map in audit_specs:
        path = root / "bridge" / audit_file
        if not path.exists():
            continue
        payload = _load_json(path)
        findings = payload.get("findings", []) if isinstance(payload, dict) else []
        if not isinstance(findings, list):
            continue
        for finding in findings:
            if not isinstance(finding, dict):
                continue
            if finding.get("advisory") == "docket":
                requires_review = True
            finding_id = finding.get("id")
            if finding_id == "cascade.healthLow":
                plurality += float(weight_map.get("cascade.healthLow", 0.0))
            if finding_id == "discovery_corridor.lowPotential":
                novelty += float(weight_map.get("discovery_corridor.lowPotential", 0.0))

    guidance = {
        "noveltyWeight": min(novelty, 1.0),
        "pluralityWeight": min(plurality, 1.0),
        "humilityWeight": min(humility, 1.0),
        "requiresHumanReview": requires_review,
    }

    Draft202012Validator(json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))).validate(guidance)

    target = Path(out_file) if out_file else root / "ai_guidance.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(guidance, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return guidance


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    parser.add_argument("--out", dest="out_file", default=None)
    parser.add_argument("--output-file", dest="out_file", default=None)
    args = parser.parse_args(argv)

    build_ai_guidance(args.bridge_root, args.out_file)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
