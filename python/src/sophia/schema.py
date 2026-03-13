from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from jsonschema import Draft7Validator


def validate_record(record: dict[str, Any], schema_path: Path) -> None:
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    Draft7Validator(schema).validate(record)
