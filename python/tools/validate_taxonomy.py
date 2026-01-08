from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Dict, List, Set, Tuple

WILDCARDS = ("*", "?", "[")  # very small glob heuristic

def die(msg: str, code: int = 2) -> None:
    print(f"TAXONOMY VALIDATION FAILED: {msg}")
    raise SystemExit(code)

def read_json(p: Path) -> Any:
    return json.loads(p.read_text(encoding="utf-8"))

def is_json_pointer(s: Any) -> bool:
    return isinstance(s, str) and s.startswith("/")

def has_wildcard(s: str) -> bool:
    return any(ch in s for ch in WILDCARDS)

def ptr_within_scope(ptr: str, scope: str) -> bool:
    # exact or child pointer
    return ptr == scope or ptr.startswith(scope.rstrip("/") + "/")

def find_owner_scope(owned_scopes: List[Tuple[str, str]], ptr: str) -> Tuple[str, str] | None:
    # returns (scope, owner) for the most-specific matching scope (longest prefix)
    matches = [(s, o) for (s, o) in owned_scopes if ptr_within_scope(ptr, s)]
    if not matches:
        return None
    matches.sort(key=lambda x: len(x[0]), reverse=True)
    return matches[0]

def validate_outputs_block(eid: str, outputs: Any) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    if outputs is None:
        return [], []
    if not isinstance(outputs, dict):
        die(f"{eid}: outputs must be an object")

    run_files = outputs.get("run_files", []) or []
    artifacts = outputs.get("artifacts", []) or []

    if not isinstance(run_files, list):
        die(f"{eid}: outputs.run_files must be a list")
    if not isinstance(artifacts, list):
        die(f"{eid}: outputs.artifacts must be a list")

    def check_entries(kind: str, xs: List[Any]) -> List[Dict[str, Any]]:
        out: List[Dict[str, Any]] = []
        for i, it in enumerate(xs):
            if not isinstance(it, dict):
                die(f"{eid}: outputs.{kind}[{i}] must be an object")
            name = it.get("name")
            path = it.get("path")
            fmt  = it.get("format")
            if not isinstance(name, str) or not name:
                die(f"{eid}: outputs.{kind}[{i}] missing/invalid name")
            if not isinstance(path, str) or not path:
                die(f"{eid}: outputs.{kind}[{i}] missing/invalid path")
            if not isinstance(fmt, str) or not fmt:
                die(f"{eid}: outputs.{kind}[{i}] missing/invalid format")
            out.append({"name": name, "path": path, "format": fmt})
        return out

    return check_entries("run_files", run_files), check_entries("artifacts", artifacts)

def main() -> int:
    repo_root = Path(__file__).resolve().parents[2]
    tax_root = repo_root / "paper" / "schema" / "telemetry_taxonomy"
    reg_path = tax_root / "registry.json"

    if not reg_path.exists():
        die(f"missing registry: {reg_path}")

    reg = read_json(reg_path)
    tv = reg.get("taxonomy_version")
    if not isinstance(tv, str) or not tv:
        die("registry.json missing taxonomy_version")
    sr = reg.get("schema_root")
    if not isinstance(sr, str) or not sr:
        die("registry.json missing schema_root")

    mods = reg.get("modules", [])
    if not isinstance(mods, list) or not mods:
        die("registry.json has no modules[]")

    # Load modules
    seen_ids: Set[str] = set()
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

    # Global collections
    owned_ptrs: Dict[str, str] = {}                 # ptr -> engine_id (exact)
    owned_scopes: List[Tuple[str, str]] = []        # (ptr, engine_id)
    frag_ptrs: Dict[str, str] = {}                  # json_pointer -> engine_id
    artifact_names: Dict[str, str] = {}             # artifact name -> engine_id
    artifact_paths: Dict[str, str] = {}             # artifact path -> engine_id (no wildcards)
    runfile_paths: Dict[str, str] = {}              # run_file path -> engine_id (no wildcards)

    # First pass: validate structure, collect owns + outputs + fragments
    for eid, mp, m in loaded:
        metrics = m.get("metrics", {})
        if not isinstance(metrics, dict):
            die(f"{eid}: metrics must be an object")

        owns = metrics.get("owns", []) or []
        produces = metrics.get("produces", []) or []
        frags = metrics.get("schema_fragments", []) or []

        if not isinstance(owns, list):
            die(f"{eid}: metrics.owns must be a list")
        if not isinstance(produces, list):
            die(f"{eid}: metrics.produces must be a list")
        if not isinstance(frags, list):
            die(f"{eid}: metrics.schema_fragments must be a list")

        for ptr in owns:
            if not is_json_pointer(ptr):
                die(f"{eid}: metrics.owns contains invalid JSON pointer: {ptr!r}")
            if ptr in owned_ptrs:
                die(f"ownership collision: {ptr} owned by {owned_ptrs[ptr]} and {eid}")
            owned_ptrs[ptr] = eid
            owned_scopes.append((ptr, eid))

        # outputs
        run_files, artifacts = validate_outputs_block(eid, m.get("outputs", {}))

        for rf in run_files:
            p = rf["path"]
            if not has_wildcard(p):
                if p in runfile_paths:
                    die(f"run_file path collision: {p} in {runfile_paths[p]} and {eid}")
                runfile_paths[p] = eid

        for a in artifacts:
            name = a["name"]
            if name in artifact_names:
                die(f"artifact name collision: {name} in {artifact_names[name]} and {eid}")
            artifact_names[name] = eid

            p = a["path"]
            if not has_wildcard(p):
                if p in artifact_paths:
                    die(f"artifact path collision: {p} in {artifact_paths[p]} and {eid}")
                artifact_paths[p] = eid

        # fragments: pointer uniqueness + local scope checks later (needs owned_scopes ready)
        for fr in frags:
            if not isinstance(fr, dict):
                die(f"{eid}: schema_fragments entry must be object")
            jp = fr.get("json_pointer")
            sch = fr.get("schema")
            if not is_json_pointer(jp):
                die(f"{eid}: schema_fragments.json_pointer must be JSON pointer string starting with '/'")
            if not isinstance(sch, dict):
                die(f"{eid}: schema_fragments.schema must be object")
            if jp in frag_ptrs:
                die(f"schema_fragments pointer collision: {jp} in {frag_ptrs[jp]} and {eid}")
            frag_ptrs[jp] = eid

    # Second pass: check overlapping ownership (prefix conflicts)
    # Example conflict: A owns /properties/guft and B owns /properties/guft/properties/psi
    all_owned = sorted(owned_scopes, key=lambda x: len(x[0]))
    for i in range(len(all_owned)):
        p, owner_p = all_owned[i]
        for j in range(i + 1, len(all_owned)):
            q, owner_q = all_owned[j]
            if owner_p == owner_q:
                continue
            if ptr_within_scope(q, p):
                die(f"overlapping ownership: {owner_p} owns {p} but {owner_q} owns {q}")

    # Third pass: enforce fragments within the module's owned scope
    for eid, mp, m in loaded:
        metrics = m.get("metrics", {})
        owns = metrics.get("owns", []) or []
        frags = metrics.get("schema_fragments", []) or []
        owns_scopes = [o for o in owns if isinstance(o, str)]

        for fr in frags:
            jp = fr.get("json_pointer")
            assert isinstance(jp, str)
            ok = any(ptr_within_scope(jp, scope) for scope in owns_scopes)
            if not ok:
                die(f"{eid}: schema fragment {jp} is not within any owned scope; owns={owns_scopes}")

    # Fourth pass: enforce produces pointers are under some owned scope (global)
    for eid, mp, m in loaded:
        metrics = m.get("metrics", {})
        produces = metrics.get("produces", []) or []
        for ptr in produces:
            if not is_json_pointer(ptr):
                die(f"{eid}: metrics.produces contains invalid JSON pointer: {ptr!r}")
            hit = find_owner_scope(owned_scopes, ptr)
            if hit is None:
                die(f"{eid}: produces pointer {ptr} has no owning scope in taxonomy")
            # no need to require same-owner; produced-by can differ (that’s the point)

    print("TAXONOMY OK")
    print(f"  modules={len(loaded)}")
    print(f"  owned_scopes={len(owned_ptrs)}")
    print(f"  schema_fragments={len(frag_ptrs)}")
    print(f"  unique_artifacts={len(artifact_names)}")
    print(f"  runfile_paths_checked={len(runfile_paths)}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())