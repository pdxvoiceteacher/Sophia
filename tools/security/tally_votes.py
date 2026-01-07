from __future__ import annotations

import argparse
from pathlib import Path

from ucc.vote_tally import write_tally_env


def main() -> int:
    ap = argparse.ArgumentParser(description="Tally v0 for Vote Manifest + Ballots")
    ap.add_argument("--outdir", required=True, help="Vote run directory (contains ballots/)")
    ap.add_argument("--manifest", required=True, help="Path to vote_manifest.json")
    ap.add_argument("--verify-ballot-sigs", action="store_true", help="Verify DID signatures on ballots (open only)")
    args = ap.parse_args()

    outdir = Path(args.outdir)
    manifest = Path(args.manifest)

    tally_path = write_tally_env(
        outdir=outdir,
        manifest_path=manifest,
        verify_ballot_signatures=args.verify_ballot_sigs,
    )
    print(f"Wrote: {tally_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
