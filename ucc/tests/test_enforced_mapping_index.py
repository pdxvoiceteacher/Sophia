from __future__ import annotations

import json
from pathlib import Path
from ucc.core import run_module

def test_enforced_mapping_index(tmp_path: Path):
    repo = Path(__file__).resolve().parents[1]
    schema = repo / "schema" / "ucc_module.schema.json"
    module_path = repo / "modules" / "mapping_table_validate.yml"
    idx = repo / "authorities" / "mappings" / "index.json"
    data = json.loads(idx.read_text(encoding="utf-8-sig"))
    enforced = data.get("enforced", [])
    assert isinstance(enforced, list) and len(enforced) > 0

    for item in enforced:
        rel = item["path"]
        csv_path = repo / rel.replace("ucc/", "")
        # repo is .../ucc, so strip leading "ucc/" when joining
        if not csv_path.exists():
            csv_path = repo / rel.split("ucc/")[-1]
        assert csv_path.exists(), f"Missing mapping csv: {rel}"

        outdir = tmp_path / ("map_" + csv_path.stem)
        metrics, flags = run_module(module_path, csv_path, outdir, schema)
        assert flags.get("mapping_table_ok") is True
        assert (outdir / "mapping_validation.md").exists()
        assert (outdir / "mapping_validation.csv").exists()