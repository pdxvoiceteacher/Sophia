from __future__ import annotations
from pathlib import Path

fp = Path("ucc/src/ucc/vote_tally.py")
txt = fp.read_text(encoding="utf-8")

# Ensure import
if "from ucc.vc_verify import assert_subject_has_valid_vc_if_configured" not in txt:
    if "import os" in txt:
        txt = txt.replace("import os", "import os\n\nfrom ucc.vc_verify import assert_subject_has_valid_vc_if_configured")
    else:
        txt = "from ucc.vc_verify import assert_subject_has_valid_vc_if_configured\n" + txt

# Insert enforcement right after signer_did is verified (first occurrence)
needle = "signer_did = _verify_signed_payload(b)"
marker = "TALLY_VC_ENFORCE"

if marker not in txt:
    if needle not in txt:
        raise SystemExit("Could not find signer_did assignment to patch.")
    txt = txt.replace(
        needle,
        needle + "\n\n                # TALLY_VC_ENFORCE: did_vc electorate membership (config-gated)\n                assert_subject_has_valid_vc_if_configured(subject_did=signer_did, manifest=manifest, repo_root=repo_root)"
    )

fp.write_text(txt, encoding="utf-8")
print("Patched vote_tally.py with VC enforcement after signature verification.")
