#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path

from jsonschema import Draft202012Validator


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--registry", default="config/metric_registry_v1.json")
    ap.add_argument("--schema", default="schema/metric_registry_v1.schema.json")
    ap.add_argument("--artifact", required=True, help="Artifact JSON containing metric provenance map")
    args = ap.parse_args()

    registry = load_json(Path(args.registry))
    schema = load_json(Path(args.schema))
    Draft202012Validator(schema).validate(registry)

    artifact = load_json(Path(args.artifact))
    provenance = artifact.get("metric_provenance") or {}
    errors: list[str] = []

    for metric, rule in registry.get("metrics", {}).items():
        entry = provenance.get(metric)
        if entry is None:
            errors.append(f"missing_metric_provenance:{metric}")
            continue
        for field in rule.get("required_fields", []):
            if field not in entry:
                errors.append(f"missing_field:{metric}:{field}")

    if errors:
        raise SystemExit("metric_registry_check_failed: " + ";".join(errors))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
