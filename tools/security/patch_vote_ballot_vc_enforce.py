from __future__ import annotations
from pathlib import Path

fp = Path("ucc/src/ucc/vote_ballot.py")
txt = fp.read_text(encoding="utf-8")

marker = "VOTE_REGISTRY_ENFORCE"
ins_marker = "VOTE_VC_ENFORCE"

if ins_marker in txt:
    print("vote_ballot.py already has VC enforcement marker.")
    raise SystemExit(0)

if marker not in txt:
    raise SystemExit("Cannot find VOTE_REGISTRY_ENFORCE marker in vote_ballot.py")

snippet = """
            # VOTE_VC_ENFORCE: did_vc electorate membership (if configured with issuer DID + vc_type)
            try:
                from ucc.vc_verify import assert_subject_has_valid_vc_if_configured
                assert_subject_has_valid_vc_if_configured(subject_did=did_obj.did, manifest=manifest, repo_root=repo_root)
            except ImportError:
                pass
""".rstrip() + "\n"

# Insert snippet immediately after the replay protection call site line (enforce_max_ballots...)
needle = "enforce_max_ballots_per_did(outdir / \"ballots\", did_obj.did, max_per_did)"
pos = txt.find(needle)
if pos == -1:
    raise SystemExit("Cannot find replay-protection enforce_max_ballots_per_did call site.")
pos_end = pos + len(needle)

txt = txt[:pos_end] + "\n" + snippet + txt[pos_end:]
fp.write_text(txt, encoding="utf-8")
print("Patched vote_ballot.py with VC enforcement (config-gated).")
