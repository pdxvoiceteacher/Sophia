from ucc.vote_ballot_aead import build_aead_commit_and_reveal
from ucc.vote_proof_envelope import build_proof_envelope_from_commit_and_reveal, verify_proof_envelope


def test_public_verifier_uses_public_circuit():
    commit, reveal = build_aead_commit_and_reveal(manifest_id="m", plaintext_choice="YES", nullifier_hex="aa"*16)
    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal, verifier_id="stub.sha256.public.pinned.v1")
    assert proof["circuit_id"] == "vote_proof_envelope_public.v1"
    assert isinstance(proof["circuit_sha256"], str) and len(proof["circuit_sha256"]) == 64

    # Stub proof should verify under stricter schema
    verify_proof_envelope(proof)
