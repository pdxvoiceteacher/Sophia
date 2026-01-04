from __future__ import annotations

from pathlib import Path

FILES = [
    "authorities/mappings/80053_families_to_soc2_cc_sample.csv",
    "authorities/mappings/80053_families_to_iso27001_annexA_sample.csv",
]

def test_80053_mapping_placeholders_exist():
    repo = Path(__file__).resolve().parents[1]
    for rel in FILES:
        p = repo / rel
        assert p.exists(), f"Missing mapping file: {rel}"
        head = p.read_text(encoding="utf-8-sig").splitlines()[0].strip()
        assert head.startswith("source_authority"), f"Bad header in {rel}"