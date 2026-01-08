from pathlib import Path
import json

from ucc.vote_ballot_aead import build_aead_commit_and_reveal
from ucc.vote_proof_envelope import build_proof_envelope_from_commit_and_reveal, verify_proof_envelope
from ucc.vote_tally_proof import tally_proofs


def test_proof_envelope_roundtrip(tmp_path: Path):
    outdir = tmp_path / "vote"
    mid = "manifest-proof"

    # Build AEAD commit + key-only reveal (v0.4 style)
    commit, reveal = build_aead_commit_and_reveal(manifest_id=mid, plaintext_choice="YES", nullifier_hex="aa"*16)

    # Write into expected dirs
    commits = outdir / "secret_v03" / "commits"
    reveals = outdir / "secret_v03" / "reveals"
    commits.mkdir(parents=True, exist_ok=True)
    reveals.mkdir(parents=True, exist_ok=True)

    cp = commits / f"commit_{commit['ballot_id']}.json"
    rp = reveals / f"reveal_{commit['ballot_id']}.json"
    cp.write_text(json.dumps(commit, sort_keys=True), encoding="utf-8")
    rp.write_text(json.dumps(reveal, sort_keys=True), encoding="utf-8")

    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal)
    assert "verifier_id" in proof; verify_proof_envelope(proof)

    proofs = outdir / "secret_v03" / "proofs"
    proofs.mkdir(parents=True, exist_ok=True)
    pp = proofs / f"proof_{commit['ballot_id']}.json"
    pp.write_text(json.dumps(proof, sort_keys=True), encoding="utf-8")

    # Tally proofs by choice_hash
    t = tally_proofs(outdir=outdir, manifest_id=mid, strict=True, options_path=None)
    assert t["ballots"]["valid"] == 1
    assert sum(t["counts_by_choice_hash"].values()) == 1

