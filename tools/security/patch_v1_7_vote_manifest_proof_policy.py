from __future__ import annotations
from pathlib import Path
import re

fp = Path("ucc/src/ucc/vote_manifest.py")
txt = fp.read_text(encoding="utf-8")

# Add parameter proof_policy if missing
if "proof_policy" not in txt.split("def build_vote_manifest",1)[1].split("):",1)[0]:
    txt = txt.replace(
        "extra: Optional[Dict[str, Any]] = None,",
        "proof_policy: Optional[Dict[str, Any]] = None,\n    extra: Optional[Dict[str, Any]] = None,"
    )

# Insert field into manifest dict if missing
if '"proof_policy"' not in txt:
    txt = txt.replace(
        "    if extra:\n        manifest[\"extra\"] = extra\n\n    return manifest",
        "    if proof_policy:\n        manifest[\"proof_policy\"] = proof_policy\n\n    if extra:\n        manifest[\"extra\"] = extra\n\n    return manifest"
    )

fp.write_text(txt, encoding="utf-8")
print("Patched vote_manifest.py to support proof_policy.")
