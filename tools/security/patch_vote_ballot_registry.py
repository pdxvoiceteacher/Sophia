from __future__ import annotations

from pathlib import Path

TARGET = Path("ucc/src/ucc/vote_ballot.py")
MARKER = "VOTE_REGISTRY_ENFORCE"

SNIPPET_TEMPLATE = r"""
    # __MARKER__: open-mode replay protection (one ballot per DID in strict unless overridden)
    if sign and anon_mode == "open":
        # determine max ballots per DID
        rules = (manifest.get("electorate") or {}).get("rules") or {}
        max_raw = rules.get("max_ballots_per_did", None)

        if max_raw is None:
            max_per_did = 1 if strict else 0
        else:
            try:
                max_per_did = int(max_raw)
            except Exception:
                max_per_did = 1 if strict else 0

        if max_per_did > 0:
            from coherenceledger.keystore import KeyStore  # type: ignore
            from ucc.vote_registry import enforce_max_ballots_per_did

            ks = KeyStore(path=keystore_path)
            did_obj, _kp = ks.load_keypair()
            enforce_max_ballots_per_did(outdir / "ballots", did_obj.did, max_per_did)
""".strip("\n")


def main() -> None:
    if not TARGET.exists():
        raise SystemExit(f"Target not found: {TARGET}")

    txt = TARGET.read_text(encoding="utf-8")
    if MARKER in txt:
        print("Already patched (marker present).")
        return

    needle = "    if sign:\n        _sign_ballot_inplace(ballot, keystore_path=keystore_path)\n"
    if needle not in txt:
        needle = "    if sign:\r\n        _sign_ballot_inplace(ballot, keystore_path=keystore_path)\r\n"
        if needle not in txt:
            raise SystemExit("Could not find the write_ballot() sign block to patch.")

    snippet = SNIPPET_TEMPLATE.replace("__MARKER__", MARKER)

    patched = txt.replace(
        needle,
        "\n" + snippet + "\n\n" + needle,
        1
    )

    TARGET.write_text(patched, encoding="utf-8")
    print("Patched vote_ballot.py with replay-protection enforcement.")


if __name__ == "__main__":
    main()
