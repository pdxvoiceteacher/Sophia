from __future__ import annotations

import argparse
from pathlib import Path

from ucc.vote_tally_proof import write_tally_proofs
from ucc.vote_guardrail import ensure_guardrail_passed


def main() -> int:
    ap = argparse.ArgumentParser(description="Tally proof envelopes v0.5 (counts by choice_hash)")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--manifest-id", required=True)
    ap.add_argument("--options-file", default=None, help="JSON list of options to map choice_hash -> label")
    args = ap.parse_args()

    outdir = Path(args.outdir)

    import os
    strict = os.getenv("COHERENCELEDGER_STRICT","").lower() in {"1","true","yes"}
    ok = ensure_guardrail_passed(outdir=outdir, manifest_path=outdir/"vote_manifest.json", strict=strict, allow_cached=True)
    if not ok:
        raise SystemExit("Guardrail FAILED.")

    opt = Path(args.options_file) if args.options_file else None
    tp = write_tally_proofs(outdir=outdir, manifest_id=args.manifest_id, options_path=opt)
    print(f"Wrote: {tp}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
