from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from tools.security.swarm_crypto import (
    canonical_sha256_hex,
    envelope_decrypt_for_recipient,
    envelope_encrypt_for_recipient,
    generate_ed25519_keypair,
    generate_x25519_keypair,
    node_id_from_signing_pubkey,
    sign_peer_attestation_payload,
    verify_peer_attestation_payload,
)

ROOT = Path(__file__).resolve().parents[1]


def test_peer_attestation_signature_verifies_and_tamper_fails() -> None:
    priv, pub = generate_ed25519_keypair()
    node_id = node_id_from_signing_pubkey(pub)
    payload = {
        "pubkey": pub,
        "bundle_hash": "abc123",
        "checks_run": ["epoch_replay"],
        "results": {"status": "pass"},
    }
    signed = sign_peer_attestation_payload(
        payload_without_signature=payload,
        private_key_b64=priv,
        signer_node_id=node_id,
    )
    ok, detail = verify_peer_attestation_payload(signed)
    assert ok, detail

    tampered = dict(signed)
    tampered["results"] = {"status": "fail"}
    ok2, detail2 = verify_peer_attestation_payload(tampered)
    assert not ok2
    assert detail2 in {"signed_bytes_hash_mismatch", "signature_invalid"}


def test_vault_bundle_schema_and_envelope_encryption_roundtrip() -> None:
    schema = json.loads((ROOT / "schema" / "vault_bundle_v1.schema.json").read_text(encoding="utf-8"))
    recip_priv, recip_pub = generate_x25519_keypair()
    plaintext = b"sophia-vault-payload"
    aad_meta = {
        "schema_id": "vault_bundle_v1",
        "bundle_hash": canonical_sha256_hex({"payload": "x"}),
        "run_id": "run-1",
        "sender_node_id": "node-a",
        "created_at": "2026-01-01T00:00:00Z",
    }
    envelope = envelope_encrypt_for_recipient(
        plaintext=plaintext,
        recipient_pubkey_b64=recip_pub,
        aad_meta=aad_meta,
    )
    Draft202012Validator(schema).validate(envelope)
    recovered = envelope_decrypt_for_recipient(envelope=envelope, recipient_private_key_b64=recip_priv)
    assert recovered == plaintext


def test_envelope_wrong_recipient_or_tamper_fails() -> None:
    priv_a, pub_a = generate_x25519_keypair()
    priv_b, _pub_b = generate_x25519_keypair()
    envelope = envelope_encrypt_for_recipient(
        plaintext=b"secret",
        recipient_pubkey_b64=pub_a,
        aad_meta={
            "schema_id": "vault_bundle_v1",
            "bundle_hash": "h",
            "run_id": "r",
            "sender_node_id": "s",
            "created_at": "2026-01-01T00:00:00Z",
        },
    )

    failed = False
    try:
        envelope_decrypt_for_recipient(envelope=envelope, recipient_private_key_b64=priv_b)
    except Exception:
        failed = True
    assert failed

    tampered = dict(envelope)
    tampered["aad_meta"] = dict(tampered["aad_meta"])
    tampered["aad_meta"]["run_id"] = "tampered"
    failed_tamper = False
    try:
        envelope_decrypt_for_recipient(envelope=tampered, recipient_private_key_b64=priv_a)
    except Exception:
        failed_tamper = True
    assert failed_tamper
