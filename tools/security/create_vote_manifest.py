from __future__ import annotations

import argparse
import json
from pathlib import Path

from ucc.vote_manifest import build_vote_manifest, write_vote_manifest_env


def main() -> int:
    ap = argparse.ArgumentParser(description="Create Vote Manifest v0 (purpose-bound) and optionally sign+anchor")
    ap.add_argument("--outdir", required=True, help="Output directory for vote_manifest.json")
    ap.add_argument("--title", required=True)
    ap.add_argument("--purpose-id", required=True)
    ap.add_argument("--purpose-statement", required=True)
    ap.add_argument("--scope", required=True, help="e.g. org.governance | dao.governance | public.deliberation")
    ap.add_argument("--electorate-type", default="did_vc", help="did_vc | token_holders | manual_list")
    ap.add_argument("--anonymity", default="open", help="open | pseudonymous | secret")
    ap.add_argument("--tally", default="plaintext", help="plaintext | encrypted | zk")
    ap.add_argument("--anti-coercion", action="store_true")
    ap.add_argument("--weighting", default="one_person_one_vote", help="one_person_one_vote | token | coherence | quadratic")
    ap.add_argument("--electorate-rules", default="{}", help="JSON dict string")
    ap.add_argument("--weighting-params", default="{}", help="JSON dict string")
    args = ap.parse_args()

    electorate_rules = json.loads(args.electorate_rules)
    weighting_params = json.loads(args.weighting_params)

    manifest = build_vote_manifest(
        title=args.title,
        purpose_id=args.purpose_id,
        purpose_statement=args.purpose_statement,
        scope=args.scope,
        electorate_type=args.electorate_type,
        electorate_rules=electorate_rules,
        anonymity_mode=args.anonymity,
        tally_mode=args.tally,
        anti_coercion=args.anti_coercion,
        weighting_mode=args.weighting,
        weighting_params=weighting_params,
    )

    outdir = Path(args.outdir)
    path = write_vote_manifest_env(outdir=outdir, manifest=manifest)

    print(f"Wrote: {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
