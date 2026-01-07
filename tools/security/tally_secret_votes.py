from __future__ import annotations

import argparse
from pathlib import Path

from ucc.vote_tally_secret import write_tally_secret
from ucc.vote_guardrail import ensure_guardrail_passed


def main() -> int:
    ap = argparse.ArgumentParser(description="Tally SECRET votes v0.1 (commit-reveal + nullifiers)")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--manifest-id", required=True)
    args = ap.parse_args()

    outdir = Path(args.outdir)

    import os
    strict = os.getenv("COHERENCELEDGER_STRICT","").lower() in {"1","true","yes"}
    manifest_path = outdir / "vote_manifest.json"
    ok = ensure_guardrail_passed(outdir=outdir, manifest_path=manifest_path, strict=strict, allow_cached=True)
    if not ok:
        raise SystemExit("Guardrail FAILED: manifest not compliant.")

    tp = write_tally_secret(outdir=outdir, manifest_id=args.manifest_id)
    print(f"Wrote tally: {tp}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
