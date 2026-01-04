from __future__ import annotations

from pathlib import Path

FILES = [
    "authorities/mappings/top10_to_asvs_sample.csv",
    "authorities/mappings/samm_to_asvs_sample.csv",
    "authorities/mappings/cis_benchmarks_to_cis_controls_sample.csv",
]

def test_mapping_tables_exist_and_have_header_v2():
    repo = Path(__file__).resolve().parents[1]
    for rel in FILES:
        p = repo / rel
        assert p.exists(), f"Missing mapping file: {rel}"
        head = p.read_text(encoding="utf-8-sig").splitlines()[0].strip()
        assert head.startswith("source_authority"), f"Bad header in {rel}: {head}"