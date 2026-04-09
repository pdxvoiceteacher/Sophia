from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

from sophia.build_attention_updates import build_attention_updates

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/ai_guidance_v1.schema.json"

MODIFIER_MAP = {
    "cascade.healthLow": ("noveltyWeight", 0.5),
    "capture.riskHigh": ("humilityWeight", 0.5),
    "discovery_corridor.lowPotential": ("pluralityWeight", 0.3),
}


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _load_findings(root: Path) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for audit_name in ["cascade_audit.json", "discovery_corridor_audit.json", "navigation_audit.json"]:
        candidates = [root / audit_name, root / "bridge" / audit_name]
        for path in candidates:
            if not path.exists():
                continue
            data = _load_json(path)
            rows = data.get("findings", []) if isinstance(data, dict) else []
            if isinstance(rows, list):
                findings.extend(item for item in rows if isinstance(item, dict))
            break
    return findings


def build_ai_guidance(bridge_root: str, out_file: str | None = None) -> dict[str, Any]:
    root = Path(bridge_root)
    findings = _load_findings(root)

    novelty = 0.0
    plurality = 0.0
    humility = 0.0
    review = False
    for finding in findings:
        if finding.get("advisory") == "docket":
            review = True
        mapping = MODIFIER_MAP.get(str(finding.get("id")))
        if mapping is None:
            continue
        param, value = mapping
        if param == "noveltyWeight":
            novelty += value
        elif param == "pluralityWeight":
            plurality += value
        elif param == "humilityWeight":
            humility += value

    attention_payload, _ = build_attention_updates(str(root))
    if attention_payload.get("review_priority") in {"watch", "docket"}:
        review = True

    guidance = {
        "noveltyWeight": min(novelty, 1.0),
        "pluralityWeight": min(plurality, 1.0),
        "humilityWeight": min(humility, 1.0),
        "requiresHumanReview": review,
    }

    output_path = Path(out_file) if out_file else root / "ai_guidance.json"
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(guidance, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    Draft202012Validator(json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))).validate(guidance)
    return guidance


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    parser.add_argument("--output-file", default=None)
    parser.add_argument("--out", dest="output_file", default=None)
    args = parser.parse_args(argv)

    guidance = build_ai_guidance(args.bridge_root, args.output_file)
    if not args.output_file:
        print(json.dumps(guidance, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
