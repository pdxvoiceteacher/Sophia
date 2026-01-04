from __future__ import annotations

from pathlib import Path

FILES = [
    "authorities/mappings/cis_v8_to_nist_csf_functions_sample.csv",
    "authorities/mappings/soc2_cc_to_iso27001_annexA_sample.csv",
    "authorities/mappings/asvs_to_cis_sample.csv",
    "authorities/mappings/cobit_to_iso31000_sample.csv",
]

def test_mapping_tables_exist_and_have_header():
    repo = Path(__file__).resolve().parents[1]
    for rel in FILES:
        p = repo / rel
        assert p.exists(), f"Missing mapping file: {rel}"
        head = p.read_text(encoding="utf-8-sig").splitlines()[0].strip()
        assert head.startswith("source_authority"), f"Bad header in {rel}: {head}"