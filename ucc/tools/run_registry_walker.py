from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

def safe_name(s: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", s)

def read_json(p: Path) -> dict:
    return json.loads(p.read_text(encoding="utf-8-sig"))

def run(cmd: list[str], repo_root: Path) -> None:
    print(">>", " ".join(cmd))
    subprocess.run(cmd, cwd=str(repo_root), check=True)

def main() -> int:
    repo_root = Path(__file__).resolve().parents[2]  # .../ucc/tools -> repo root
    ucc_root = repo_root / "ucc"
    py = sys.executable

    idx = ucc_root / "authorities" / "index.json"
    data = read_json(idx)
    auths = data.get("authorities") or data.get("packs") or []
    if not isinstance(auths, list):
        raise SystemExit("authorities index malformed (expected list)")

    out_root = ucc_root / "out" / "registry_walker"
    out_root.mkdir(parents=True, exist_ok=True)

    # 1) Run every authority fixture
    ran = 0
    skipped = 0
    for a in auths:
        if not isinstance(a, dict):
            continue
        aid = a.get("id", "")
        mod = a.get("module", "")
        task = a.get("sample_task", "")
        if not (aid and mod and task):
            skipped += 1
            continue
        outdir = out_root / "packs" / safe_name(aid)
        outdir.mkdir(parents=True, exist_ok=True)
        run([py, "-m", "ucc.cli", "run", str(mod), "--input", str(task), "--outdir", str(outdir)], repo_root)
        ran += 1

    # 2) Validate enforced mapping CSVs
    mindex = ucc_root / "authorities" / "mappings" / "index.json"
    if mindex.exists():
        mdata = read_json(mindex)
        enforced = mdata.get("enforced", [])
        if isinstance(enforced, list):
            for item in enforced:
                rel = item.get("path", "")
                mode = (item.get("mode", "strict") or "strict").lower()
                if not rel:
                    continue

                csv_path = repo_root / rel
                if not csv_path.exists():
                    # fallback if index paths omit repo root
                    csv_path = ucc_root / rel.replace("ucc/", "")
                if not csv_path.exists():
                    raise SystemExit(f"Missing mapping file: {rel}")

                module_path = repo_root / "ucc" / "modules" / ("mapping_table_validate.yml" if mode == "strict" else "mapping_table_validate_loose.yml")
                if not module_path.exists():
                    module_path = repo_root / "ucc" / "modules" / "mapping_table_validate.yml"

                outdir = out_root / "mappings" / safe_name(csv_path.stem)
                outdir.mkdir(parents=True, exist_ok=True)
                run([py, "-m", "ucc.cli", "run", str(module_path), "--input", str(csv_path), "--outdir", str(outdir)], repo_root)

    print(f"Registry walker: ran {ran} authority fixtures; skipped {skipped}.")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())