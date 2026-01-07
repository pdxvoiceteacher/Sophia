from __future__ import annotations

import argparse
from pathlib import Path

from ucc.vote_ballot_secret import build_secret_commit_and_reveal, write_secret_commit, write_secret_reveal
from ucc.vote_guardrail import ensure_guardrail_passed


def main() -> int:
    ap = argparse.ArgumentParser(description="Cast SECRET ballot v0.1 (commit-reveal, nullifier, no DID signature)")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--manifest-id", required=True)
    ap.add_argument("--choice", required=True)
    ap.add_argument("--reveal-now", action="store_true", help="Write reveal immediately (demo/dev only)")
    args = ap.parse_args()

    outdir = Path(args.outdir)

    # Guardrail must already pass for this vote (cached OK is allowed)
    import os
    strict = os.getenv("COHERENCELEDGER_STRICT","").lower() in {"1","true","yes"}
    # We require you have vote_manifest.json at outdir for caching to work
    manifest_path = outdir / "vote_manifest.json"
    ok = ensure_guardrail_passed(outdir=outdir, manifest_path=manifest_path, strict=strict, allow_cached=True)
    if not ok:
        raise SystemExit("Guardrail FAILED: manifest not compliant.")

    commit, reveal = build_secret_commit_and_reveal(
        manifest_id=args.manifest_id,
        choice=args.choice,
    )

    cp = write_secret_commit(outdir=outdir, commit_doc=commit)
    print(f"Wrote commit: {cp}")

    if args.reveal_now:
        rp = write_secret_reveal(outdir=outdir, reveal_doc=reveal)
        print(f"Wrote reveal: {rp}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
