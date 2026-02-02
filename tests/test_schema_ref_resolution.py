import json
from pathlib import Path

from jsonschema import Draft202012Validator
from jsonschema.validators import RefResolver


ROOT = Path(__file__).resolve().parents[1]


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_action_schema_ref_resolves():
    schema_dir = ROOT / "schema" / "governance"
    action_schema = load_json(schema_dir / "action.schema.json")
    warrant_schema = load_json(schema_dir / "warrant.schema.json")
    store = {"action.schema.json": action_schema}
    resolver = RefResolver.from_schema(warrant_schema, store=store)
    validator = Draft202012Validator(warrant_schema, resolver=resolver)
    instance = {
        "schema": "warrant_v1",
        "warrant_id": "warrant_demo",
        "decision_id": "decision_demo",
        "created_at_utc": "2026-01-01T00:00:00Z",
        "stakeholder_scope": "global",
        "mvss_policy_ref": "mvss_demo",
        "registry_snapshot_ref": "registry_demo",
        "registry_federation": {"enabled": False, "peers": []},
        "authorized_actions": [
            {
                "action": "backup_state",
                "class": "continuity",
                "target": "sophia_run",
                "constraints": ["time_bound"],
            }
        ],
    }
    errors = sorted(validator.iter_errors(instance), key=lambda e: e.path)
    assert not errors
