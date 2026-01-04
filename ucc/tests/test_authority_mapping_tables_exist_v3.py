from __future__ import annotations
from pathlib import Path

FILES = [
    "authorities/mappings/80053_families_to_soc2_cc_sample.csv",
    "authorities/mappings/80053_families_to_cis_controls_sample.csv",
    "authorities/mappings/samm_practices_to_asvs_sample.csv",
]

def test_mapping_tables_exist_and_have_header_v3():
    repo = Path(__file__).resolve().parents[1]
    for rel in FILES:
        p = repo / rel
        assert p.exists(), f"Missing mapping file: {rel}"
        head = p.read_text(encoding="utf-8-sig").splitlines()[0].strip()
        assert head.startswith("source_authority"), f"Bad header in {rel}: {head}"