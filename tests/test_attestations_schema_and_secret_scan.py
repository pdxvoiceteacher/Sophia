from __future__ import annotations

import json
import re
from pathlib import Path

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN_PATTERNS = [
    re.compile(r"sk-[A-Za-z0-9]{16,}"),
    re.compile(r"(?i)api[_-]?key\s*[:=]\s*[A-Za-z0-9_\-]{8,}"),
    re.compile(r"(?i)bearer\s+[A-Za-z0-9_\-.]{8,}"),
]


def test_attestations_schema_validates_stub_and_list() -> None:
    schema = json.loads((ROOT / "schema" / "attestations_v1.schema.json").read_text(encoding="utf-8-sig"))
    validator = Draft202012Validator(schema)

    stub = {
        "schema": "attestations_v1",
        "submission_id": "sub-1",
        "status": "pending",
        "reviewer": "local_stub",
        "detail": "no_central_url",
    }
    validator.validate(stub)

    bundle = {
        "schema": "attestations_v1",
        "attestations": [
            {
                "submission_id": "sub-2",
                "status": "accepted",
                "reviewer": "reviewer-a",
                "detail": "ok",
            }
        ],
    }
    validator.validate(bundle)


def test_repository_submission_and_attestation_files_have_no_secret_patterns() -> None:
    targets = list(ROOT.rglob("submission.json")) + list(ROOT.rglob("attestations.json"))
    for path in targets:
        # ignore vendored dependency trees for performance/noise
        if "node_modules" in path.parts:
            continue
        text = path.read_text(encoding="utf-8", errors="ignore")
        for pattern in FORBIDDEN_PATTERNS:
            assert not pattern.search(text), f"Forbidden pattern in {path}: {pattern.pattern}"
