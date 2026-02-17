from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]


def _load(name: str) -> dict:
    return json.loads((ROOT / "schema" / name).read_text(encoding="utf-8"))


def test_sonya_handshake_and_attest_schemas_validate_minimal_examples() -> None:
    Draft202012Validator(_load("sonya_handshake_v1.schema.json")).validate(
        {
            "schema": "sonya_handshake_v1",
            "node_id": "node_abcdefgh",
            "pubkeys": {"ed25519_b64u": "abc_DEF-123", "x25519_b64u": "abc_DEF-123"},
            "supported": {"envelopes": ["sealed_envelope_v1"], "signing": ["ed25519"], "hash": ["sha256"]},
            "timestamp_utc": "2026-01-01T00:00:00Z",
        }
    )
    Draft202012Validator(_load("sonya_attest_request_v1.schema.json")).validate(
        {
            "schema": "sonya_attest_request_v1",
            "bundle_hash": "a" * 64,
            "checks_run": ["epoch_replay"],
            "policy_profile": "witness_only",
            "timestamp_utc": "2026-01-01T00:00:00Z",
        }
    )


def test_consensus_summary_schema_validates_minimal_example() -> None:
    Draft202012Validator(_load("consensus_summary_v1.schema.json")).validate(
        {
            "schema": "consensus_summary_v1",
            "bundle_hash": "a" * 64,
            "computed_at_utc": "2026-01-01T00:00:00Z",
            "inputs": {"central_attestations_present": True, "peer_attestations_present": True},
            "central": {"total": 1, "pass": 1, "fail": 0, "pending": 0},
            "peers": {
                "total": 1,
                "pass": 1,
                "fail": 0,
                "pending": 0,
                "weighted_pass": 1.0,
                "weighted_fail": 0.0,
                "weighted_pending": 0.0,
            },
            "consensus": "convergent",
            "policy_gate": {"network_profile": "witness_only", "required_for": ["attest"], "satisfied": True},
        }
    )
