from __future__ import annotations
from pathlib import Path
import re

fp = Path("ucc/src/ucc/verifier_registry.py")
txt = fp.read_text(encoding="utf-8")

# Replace the whole resolve_vk_path function with an absolute-path aware version
pattern = r"def resolve_vk_path\(spec: Dict\[str, Any\]\) -> Optional\[Path\]:.*?\n(?=\n\w|\Z)"
m = re.search(pattern, txt, flags=re.S)
if not m:
    raise SystemExit("Could not find resolve_vk_path() to patch.")

replacement = """def resolve_vk_path(spec: Dict[str, Any]) -> Optional[Path]:
    p = spec.get("vk_path")
    if not p:
        return None
    pth = Path(str(p))
    if pth.is_absolute():
        return pth
    repo_root = Path(__file__).resolve().parents[3]
    return (repo_root / pth).resolve()
"""

txt2 = re.sub(pattern, replacement + "\n", txt, flags=re.S)
fp.write_text(txt2, encoding="utf-8")
print("Patched resolve_vk_path() to support absolute vk_path.")
