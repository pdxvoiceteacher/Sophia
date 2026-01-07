from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple

def die(msg: str, code: int = 2) -> None:
    print(f"TAXONOMY VALIDATION FAILED: {msg}")
    raise SystemExit(code)

def read_json(p: Path) -> Any:
    return json.loads(p.read_text(encoding="utf-8"))

def main() -> int:
    repo_root = Path(__file__).resolve().parents[2]
    tax_root = repo_root / "paper" / "schema" / "telemetry_taxonomy"
    reg_path = tax_root / "registry.json"

    if not reg_path.exists():
        die(f"missing registry: {reg_path}")

    reg = read_json(reg_path)
    mods = reg.get("modules", [])
    if not isinstance(mods, list) or not mods:
        die("registry.json has no modules[]")

    seen_ids: Set[str] = set()
    owned_ptrs: Dict[str, str] = {}  # ptr -> engine_id
    artifact_names: Dict[str, str] = {}  # name -> engine_id

    loaded: List[Tuple[str, Path, Dict[str, Any]]] = []

    for item in mods:
        if not isinstance(item, dict):
            die("registry.modules item is not an object")
        eid = item.get("engine_id")
        rel = item.get("path")
        if not isinstance(eid, str) or not isinstance(rel, str):
            die("registry.modules entries require engine_id and path")
        if eid in seen_ids:
            die(f"duplicate engine_id in registry: {eid}")
        seen_ids.add(eid)

        mp = tax_root / rel
        if not mp.exists():
            die(f"module file missing: {mp}")

        m = read_json(mp)
        if m.get("engine_id") != eid:
            die(f"module engine_id mismatch: registry={eid} file={m.get('engine_id')} path={mp}")

        loaded.append((eid, mp, m))

    # Ownership pointer collisions + artifact name collisions
    for eid, mp, m in loaded:
        metrics = m.get("metrics", {})
        owns = (metrics.get("owns") or [])
        if not isinstance(owns, list):
            die(f"{eid}: metrics.owns must be list")

        for ptr in owns:
            if not isinstance(ptr, str):
                die(f"{eid}: metrics.owns contains non-string pointer")
            if ptr in owned_ptrs:
                die(f"ownership collision: {ptr} owned by {owned_ptrs[ptr]} and {eid}")
            owned_ptrs[ptr] = eid

        outputs = m.get("outputs", {})
        arts = (outputs.get("artifacts") or [])
        if not isinstance(arts, list):
            die(f"{eid}: outputs.artifacts must be list")
        for a in arts:
            if not isinstance(a, dict):
                die(f"{eid}: outputs.artifacts contains non-object entry")
            name = a.get("name")
            if not isinstance(name, str) or not name:
                die(f"{eid}: artifact missing name")
            if name in artifact_names:
                die(f"artifact name collision: {name} in {artifact_names[name]} and {eid}")
            artifact_names[name] = eid

        # schema fragment pointers should be strings
        frags = (metrics.get("schema_fragments") or [])
        if not isinstance(frags, list):
            die(f"{eid}: metrics.schema_fragments must be list")
        for fr in frags:
            if not isinstance(fr, dict):
                die(f"{eid}: schema_fragments entry must be object")
            jp = fr.get("json_pointer")
            sch = fr.get("schema")
            if not isinstance(jp, str) or not jp.startswith("/"):
                die(f"{eid}: schema_fragments.json_pointer must be JSON pointer string starting with '/'")
            if not isinstance(sch, dict):
                die(f"{eid}: schema_fragments.schema must be object")

    print("TAXONOMY OK")
    print(f"  modules={len(loaded)}")
    print(f"  owned_pointers={len(owned_ptrs)}")
    print(f"  unique_artifacts={len(artifact_names)}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())