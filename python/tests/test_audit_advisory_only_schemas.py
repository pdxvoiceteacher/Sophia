from __future__ import annotations

import json
from pathlib import Path

import pytest


@pytest.mark.parametrize(
    'schema_path',
    [
        Path('/workspace/Sophia/schema/knowledge_river_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/civilizational_delta_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/rupture_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/rebraid_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/cascade_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/sophia/rebraid_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/sophia/knowledge_river_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/sophia/delta_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/sophia/rupture_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/sophia/discovery_corridor_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/sophia/viability_audit_v1.schema.json'),
        Path('/workspace/Sophia/schema/sophia/navigation_audit_v1.schema.json'),
    ],
)
def test_schema_finding_severity_and_advisory_are_advisory_only(schema_path: Path) -> None:
    schema = json.loads(schema_path.read_text(encoding='utf-8'))

    findings_items = schema['properties']['findings']['items']
    if '$ref' in findings_items:
        ref = findings_items['$ref']
        assert ref.startswith('#/$defs/')
        def_name = ref.split('/')[-1]
        finding_props = schema['$defs'][def_name]['properties']
    else:
        finding_props = findings_items['properties']

    severity_enum = finding_props['severity']['enum']
    advisory_enum = finding_props['advisory']['enum']
    assert set(severity_enum) <= {'info', 'warn'}
    assert set(advisory_enum) <= {'watch', 'docket'}
