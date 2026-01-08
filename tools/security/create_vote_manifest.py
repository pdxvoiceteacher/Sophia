from __future__ import annotations

import argparse
import json
from pathlib import Path

from ucc.vote_manifest import build_vote_manifest, write_vote_manifest_env


def load_json_dict(arg_value: str, file_value: str | None, label: str) -> dict:
    if file_value:
        p = Path(file_value)
        return json.loads(p.read_text(encoding="utf-8-sig"))

    s = (arg_value or "").strip()
    if s.startswith("@"):
        p = Path(s[1:])
        return json.loads(p.read_text(encoding="utf-8-sig"))

    return json.loads(s) if s else {}


def main() -> int:
    ap = argparse.ArgumentParser(description="Create Vote Manifest v0 and optionally sign+anchor")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--title", required=True)
    ap.add_argument("--purpose-id", required=True)
    ap.add_argument("--purpose-statement", required=True)
    ap.add_argument("--scope", required=True)

    ap.add_argument("--electorate-type", default="did_vc")
    ap.add_argument("--anonymity", default="open")
    ap.add_argument("--tally", default="plaintext")
    ap.add_argument("--anti-coercion", action="store_true")
    ap.add_argument("--weighting", default="one_person_one_vote")

    ap.add_argument("--electorate-rules", default="{}")
    ap.add_argument("--electorate-rules-file", default=None)

    ap.add_argument("--weighting-params", default="{}")
    ap.add_argument("--weighting-params-file", default=None)

    ap.add_argument("--proof-policy", default="{}")
    ap.add_argument("--proof-policy-file", default=None)

    args = ap.parse_args()

    electorate_rules = load_json_dict(args.electorate_rules, args.electorate_rules_file, "electorate-rules")
    weighting_params = load_json_dict(args.weighting_params, args.weighting_params_file, "weighting-params")
    proof_policy = load_json_dict(args.proof_policy, args.proof_policy_file, "proof-policy")

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
        proof_policy=proof_policy if proof_policy else None,
    )

    outdir = Path(args.outdir)
    path = write_vote_manifest_env(outdir=outdir, manifest=manifest)
    print(f"Wrote: {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
