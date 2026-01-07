from __future__ import annotations

import argparse
import json
from pathlib import Path

from ucc.vote_ballot import build_ballot, load_manifest, write_ballot_env


def main() -> int:
    ap = argparse.ArgumentParser(description="Cast Ballot v0 for a Vote Manifest v0")
    ap.add_argument("--manifest", required=True, help="Path to vote_manifest.json")
    ap.add_argument("--outdir", required=True, help="Vote run directory (same as manifest outdir)")
    ap.add_argument("--ballot-type", default="single_choice", help="single_choice | approval | ranked")
    ap.add_argument("--choice", required=True, help="For single_choice: a string option id/label")
    ap.add_argument("--title", default=None)
    args = ap.parse_args()

    manifest_path = Path(args.manifest)
    manifest = load_manifest(manifest_path)
    manifest_id = manifest.get("manifest_id")
    if not manifest_id:
        raise SystemExit("manifest_id missing in manifest")

    # Minimal selection schema:
    # single_choice -> {"choice": "..."}
    if args.ballot_type == "single_choice":
        selection = {"choice": args.choice}
    elif args.ballot_type == "approval":
        # comma-separated approvals
        selection = {"approve": [x.strip() for x in args.choice.split(",") if x.strip()]}
    elif args.ballot_type == "ranked":
        # comma-separated rank order
        selection = {"rank": [x.strip() for x in args.choice.split(",") if x.strip()]}
    else:
        raise SystemExit(f"Unknown ballot-type: {args.ballot_type}")

    ballot = build_ballot(
        manifest_id=manifest_id,
        ballot_type=args.ballot_type,
        selection=selection,
        title=args.title,
    )

    outdir = Path(args.outdir)
    path = write_ballot_env(outdir=outdir, ballot=ballot, manifest=manifest)

    print(f"Wrote: {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
