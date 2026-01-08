from __future__ import annotations

import argparse
from pathlib import Path

from ucc.vote_proof_envelope import build_proof_envelope_from_commit_and_reveal, write_proof_envelope
from ucc.vote_guardrail import ensure_guardrail_passed


def main() -> int:
    ap = argparse.ArgumentParser(description="Generate proof envelope v0.5 from AEAD commit+reveal key (witness)")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--commit", required=True, help="Path to commit_*.json")
    ap.add_argument("--reveal", required=True, help="Path to reveal_*.json (key only)")
    ap.add_argument("--delete-reveal", action="store_true", help="Delete reveal file after proof is written (demo hygiene)")
    args = ap.parse_args()

    outdir = Path(args.outdir)
    commit_path = Path(args.commit)
    reveal_path = Path(args.reveal)

    import os
    strict = os.getenv("COHERENCELEDGER_STRICT","").lower() in {"1","true","yes"}
    ok = ensure_guardrail_passed(outdir=outdir, manifest_path=outdir/"vote_manifest.json", strict=strict, allow_cached=True)
    if not ok:
        raise SystemExit("Guardrail FAILED.")

    import json
    commit = json.loads(commit_path.read_text(encoding="utf-8-sig"))
    reveal = json.loads(reveal_path.read_text(encoding="utf-8-sig"))

    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal)
    pp = write_proof_envelope(outdir=outdir, proof_doc=proof)
    print(f"Wrote proof: {pp}")

    if args.delete_reveal:
        reveal_path.unlink(missing_ok=True)
        print(f"Deleted reveal: {reveal_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
