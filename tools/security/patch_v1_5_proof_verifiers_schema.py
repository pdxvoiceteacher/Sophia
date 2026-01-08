from __future__ import annotations
from pathlib import Path
import re

fp = Path("ucc/src/ucc/proof_verifiers.py")
txt = fp.read_text(encoding="utf-8")

# Ensure import
if "from ucc.public_signal_schemas import validate_public_signals" not in txt:
    txt = txt.replace(
        "from ucc.verifier_registry import DEFAULT_VERIFIER_ID, get_spec, load_registry, resolve_vk_path",
        "from ucc.verifier_registry import DEFAULT_VERIFIER_ID, get_spec, load_registry, resolve_vk_path\nfrom ucc.public_signal_schemas import validate_public_signals"
    )

# Insert validate_public_signals call after spec is computed in verify_envelope
needle = "spec = get_spec(verifier_id, reg)\n"
if needle in txt and "validate_public_signals(public_signals, spec)" not in txt:
    txt = txt.replace(needle, needle + "    validate_public_signals(public_signals, spec)\n")

fp.write_text(txt, encoding="utf-8")
print("Patched proof_verifiers.verify_envelope to validate public_signals schema.")
