from __future__ import annotations
from pathlib import Path

fp = Path("ucc/src/ucc/vote_ballot.py")
txt = fp.read_text(encoding="utf-8")

marker = "VOTE_VC_ENFORCE_ALWAYS"
if marker in txt:
    print("Already patched.")
    raise SystemExit(0)

needle = "    if sign:\n        _sign_ballot_inplace(ballot, keystore_path=keystore_path)\n"
if needle not in txt:
    # CRLF fallback
    needle = "    if sign:\r\n        _sign_ballot_inplace(ballot, keystore_path=keystore_path)\r\n"
    if needle not in txt:
        raise SystemExit("Could not find sign block to patch.")

snippet = """
    # VOTE_VC_ENFORCE_ALWAYS: did_vc electorate membership (config-gated; runs even if replay limit disabled)
    if sign and anon_mode == "open":
        try:
            from coherenceledger.keystore import KeyStore  # type: ignore
            from ucc.vc_verify import assert_subject_has_valid_vc_if_configured

            ks = KeyStore(path=keystore_path)
            did_obj, _kp = ks.load_keypair()
            assert_subject_has_valid_vc_if_configured(subject_did=did_obj.did, manifest=manifest, repo_root=repo_root)
        except ImportError:
            pass
""".strip("\n") + "\n\n"

txt = txt.replace(needle, "\n" + snippet + needle, 1)
fp.write_text(txt, encoding="utf-8")
print("Patched vote_ballot.py with VOTE_VC_ENFORCE_ALWAYS.")
