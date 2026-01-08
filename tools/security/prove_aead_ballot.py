from __future__ import annotations

import argparse
import json
from pathlib import Path

from ucc.vote_proof_envelope import build_proof_envelope_from_commit_and_reveal, write_proof_envelope
from ucc.vote_guardrail import ensure_guardrail_passed


def main() -> int:
    ap = argparse.ArgumentParser(description="Generate proof envelope from AEAD commit+reveal (v1.8 auto verifier selection)")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--commit", required=True)
    ap.add_argument("--reveal", required=True)
    ap.add_argument("--delete-reveal", action="store_true")
    ap.add_argument("--verifier-id", default=None, help="Override verifier id (else uses manifest proof_policy.verifier_id)")
    args = ap.parse_args()

    outdir = Path(args.outdir)
    commit_path = Path(args.commit)
    reveal_path = Path(args.reveal)

    import os
    strict = os.getenv("COHERENCELEDGER_STRICT","").lower() in {"1","true","yes"}

    manifest_path = outdir / "vote_manifest.json"
    ok = ensure_guardrail_passed(outdir=outdir, manifest_path=manifest_path, strict=strict, allow_cached=True)
    if not ok:
        raise SystemExit("Guardrail FAILED.")

    manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
    policy = manifest.get("proof_policy") if isinstance(manifest, dict) else None

    verifier_id = args.verifier_id
    if verifier_id is None:
        if isinstance(policy, dict) and isinstance(policy.get("verifier_id"), str):
            verifier_id = policy["verifier_id"]
        else:
            verifier_id = "stub.sha256.v1"

    commit = json.loads(commit_path.read_text(encoding="utf-8-sig"))
    reveal = json.loads(reveal_path.read_text(encoding="utf-8-sig"))

    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal, verifier_id=verifier_id)
    pp = write_proof_envelope(outdir=outdir, proof_doc=proof)
    print(f"Wrote proof: {pp}")
    print(f"verifier_id={verifier_id}")

    if args.delete_reveal:
        reveal_path.unlink(missing_ok=True)
        print(f"Deleted reveal: {reveal_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
