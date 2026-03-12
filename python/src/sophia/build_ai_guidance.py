from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parents[3]
SCHEMA_PATH = REPO_ROOT / "schema/sophia/ai_guidance_v1.schema.json"

GUIDANCE_TEMPLATE = {
    "noveltyWeight": 0.5,
    "pluralityWeight": 0.5,
    "humilityWeight": 0.5,
    "requiresHumanReview": False,
}

FINDING_TO_MODIFIER = {
    "cascade.healthLow": {"noveltyWeight": 1.0, "pluralityWeight": 1.0},
    "river.captured": {"humilityWeight": 1.0, "pluralityWeight": 1.0},
}


def _load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8-sig"))


def _resolve_bridge_file(bridge_root: Path, filename: str) -> Path | None:
    p1 = bridge_root / filename
    p2 = bridge_root / "bridge" / filename
    if p1.exists():
        return p1
    if p2.exists():
        return p2
    return None


def build_ai_guidance(bridge_root: str, output_file: str | None = None) -> dict[str, Any]:
    guidance = GUIDANCE_TEMPLATE.copy()

    audit_path = _resolve_bridge_file(Path(bridge_root), "cascade_audit.json")
    audits = _load_json(audit_path) if audit_path else None
    if isinstance(audits, dict):
        for f in audits.get("findings", []) if isinstance(audits.get("findings"), list) else []:
            if not isinstance(f, dict):
                continue
            mod = FINDING_TO_MODIFIER.get(str(f.get("id")))
            if mod:
                guidance.update(mod)
            if str(f.get("advisory")) == "docket":
                guidance["requiresHumanReview"] = True

    Draft202012Validator(json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))).validate(guidance)

    if output_file:
        out = Path(output_file)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(guidance, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return guidance


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-root", default=".")
    parser.add_argument("--out", dest="output_file", default=None)
    parser.add_argument("--output-file", dest="output_file", default=None)
    args = parser.parse_args(argv)

    g = build_ai_guidance(args.bridge_root, args.output_file)
    print(json.dumps(g, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
