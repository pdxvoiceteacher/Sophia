from __future__ import annotations

import json
from pathlib import Path

import pytest


@pytest.mark.parametrize(
    "schema_name",
    [
        "knowledge_river_audit_v1.schema.json",
        "civilizational_delta_audit_v1.schema.json",
        "rupture_audit_v1.schema.json",
        "rebraid_audit_v1.schema.json",
        "cascade_audit_v1.schema.json",
    ],
)
def test_schema_finding_advisory_is_watch_or_docket(schema_name: str) -> None:
    schema_path = Path("/workspace/Sophia/schema") / schema_name
    schema = json.loads(schema_path.read_text(encoding="utf-8"))

    findings_items = schema["properties"]["findings"]["items"]
    if "$ref" in findings_items:
        ref = findings_items["$ref"]
        assert ref.startswith("#/$defs/")
        def_name = ref.split("/")[-1]
        finding_props = schema["$defs"][def_name]["properties"]
    else:
        finding_props = findings_items["properties"]

    advisory_enum = finding_props["advisory"]["enum"]
    assert advisory_enum == ["watch", "docket"]
