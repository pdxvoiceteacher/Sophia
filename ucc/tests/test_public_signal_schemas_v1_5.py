import pytest

from ucc.verifier_registry import load_registry, get_spec
from ucc.public_signal_schemas import validate_public_signals, PublicSignalsSchemaError
from ucc.vote_ballot_aead import build_aead_commit_and_reveal
from ucc.vote_proof_envelope import build_proof_envelope_from_commit_and_reveal


def test_public_signals_schema_passes_for_real_envelope():
    reg = load_registry()
    spec = get_spec("stub.sha256.v1", reg)

    commit, reveal = build_aead_commit_and_reveal(manifest_id="m", plaintext_choice="YES", nullifier_hex="aa"*16)
    proof = build_proof_envelope_from_commit_and_reveal(commit, reveal, verifier_id="stub.sha256.v1")

    ps = proof["public_signals"]
    validate_public_signals(ps, spec)  # should not raise


def test_public_signals_schema_rejects_missing_field():
    reg = load_registry()
    spec = get_spec("stub.sha256.v1", reg)

    bad = {
        "manifest_id":"m",
        "ballot_id":"b",
        "nullifier_sha256":"0"*64,
        "ciphertext_sha256":"0"*64,
        "aad_sha256":"0"*64,
        # missing choice_hash
        "public_inputs":{
            "format":"snarkjs.public_inputs.v1",
            "version":1,
            "order":["manifest_id"],
            "values":["m"]
        }
    }

    with pytest.raises(PublicSignalsSchemaError):
        validate_public_signals(bad, spec)
