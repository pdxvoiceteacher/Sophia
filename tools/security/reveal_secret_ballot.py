from __future__ import annotations

import argparse
from pathlib import Path

from ucc.vote_ballot_secret import write_secret_reveal, build_secret_commit_and_reveal


def main() -> int:
    ap = argparse.ArgumentParser(description="Reveal SECRET ballot v0.1 (for a known ballot_id)")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--manifest-id", required=True)
    ap.add_argument("--ballot-id", required=True)
    ap.add_argument("--choice", required=True)
    ap.add_argument("--salt-hex", required=True)
    ap.add_argument("--commitment", required=True)
    args = ap.parse_args()

    outdir = Path(args.outdir)

    reveal = {
        "version": 1,
        "schema_id": "ucc.vote_ballot.secret_reveal.v0_1",
        "ballot_id": args.ballot_id,
        "created_at": __import__("datetime").datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
        "manifest_id": args.manifest_id,
        "choice": args.choice,
        "salt_hex": args.salt_hex,
        "commitment": args.commitment,
    }

    rp = write_secret_reveal(outdir=outdir, reveal_doc=reveal)
    print(f"Wrote reveal: {rp}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
