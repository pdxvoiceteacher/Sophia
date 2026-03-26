from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator


def test_default_lens_spec_v1_validates_against_schema() -> None:
    repo = Path(__file__).resolve().parents[2]
    schema = json.loads((repo / "schema/sophia/lens_spec_v1.schema.json").read_text(encoding="utf-8"))
    payload = json.loads((repo / "python/src/sophia/lens/default_lens_spec_v1.json").read_text(encoding="utf-8"))

    Draft202012Validator(schema).validate(payload)


def test_lens_witness_v1_schema_accepts_minimal_record() -> None:
    repo = Path(__file__).resolve().parents[2]
    schema = json.loads((repo / "schema/sophia/lens_witness_v1.schema.json").read_text(encoding="utf-8"))

    payload = {
        "schema_version": "telemetry.lens_witness.v1",
        "event": "lens_witness",
        "timestamp": "2026-03-19T20:10:12Z",
        "run_id": "run-1",
        "target_id": "global",
        "semantic_mode": "non-executive",
        "advisory_only": True,
        "lens": {
            "lens_id": "default_lens_v1",
            "lens_spec_hash": "sha256:" + "a" * 64,
            "policy": "derived_output_only",
        },
        "inputs": [{"path": "bridge/in.json", "hash": "sha256:" + "b" * 64}],
        "outputs": [{"path": "bridge/out.json", "hash": "sha256:" + "c" * 64}],
        "metrics": {"signal_quality": 0.4, "noise_ratio": 0.6},
        "hashes": {
            "canonicalization": "rfc8785_jcs",
            "hash_algorithm": "sha256",
            "witness_hash": "sha256:" + "d" * 64,
        },
    }

    Draft202012Validator(schema).validate(payload)
