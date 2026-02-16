#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path

from jsonschema import Draft202012Validator


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--schema", default="schema/attestations_v1.schema.json")
    ap.add_argument("--path", required=True)
    args = ap.parse_args()

    schema_path = Path(args.schema)
    payload_path = Path(args.path)

    schema = json.loads(schema_path.read_text(encoding="utf-8-sig"))
    payload = json.loads(payload_path.read_text(encoding="utf-8-sig"))
    validator = Draft202012Validator(schema)
    errors = sorted(validator.iter_errors(payload), key=lambda e: str(e.path))
    if errors:
        msg = "; ".join(f"{list(e.path)}: {e.message}" for e in errors)
        raise SystemExit(f"attestation_schema_validation_failed: {msg}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
