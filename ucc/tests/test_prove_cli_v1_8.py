import json
from pathlib import Path

from ucc.vote_ballot_aead import build_aead_commit_and_reveal
from ucc.vote_proof_envelope import build_proof_envelope_from_commit_and_reveal


def test_manifest_proof_policy_verifier_id_used():
    # This test is conceptual: build_proof_envelope should accept the public verifier id.
    commit, reveal = build_aead_commit_and_reveal(manifest_id="m", plaintext_choice="YES", nullifier_hex="aa"*16)
    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal, verifier_id="stub.sha256.public.pinned.v1")
    assert proof["verifier_id"] == "stub.sha256.public.pinned.v1"
    assert proof["circuit_id"] == "vote_proof_envelope_public.v1"
