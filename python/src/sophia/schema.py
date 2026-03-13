from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from jsonschema import Draft7Validator

SCHEMA_REGISTRY = {
    "navigation_audit": Path(__file__).resolve().parent / "schemas" / "navigation_audit.json",
}


def validate_record(record: dict[str, Any], schema_path: Path) -> None:
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    Draft7Validator(schema).validate(record)


def validate_json_lines(path: Path, schema: str) -> None:
    schema_path = SCHEMA_REGISTRY[schema]
    schema_doc = json.loads(schema_path.read_text(encoding="utf-8"))
    validator = Draft7Validator(schema_doc)
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        validator.validate(json.loads(line))
