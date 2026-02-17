from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

from tools.security.swarm_crypto import (
    b64u_decode,
    b64u_encode,
    build_peer_attestation_payload,
    canonical_sha256_hex,
    compute_evidence_bundle_hash,
    generate_ed25519_keypair,
    generate_x25519_keypair,
    kid_from_signing_pubkey,
    node_id_from_signing_pubkey,
    open_envelope_for_recipient,
    seal_envelope,
    sign_peer_attestation_payload,
    verify_peer_attestation_payload,
)

ROOT = Path(__file__).resolve().parents[1]


def test_base64url_no_padding_roundtrip() -> None:
    raw = b"abc123\xff\x00"
    enc = b64u_encode(raw)
    assert "=" not in enc
    assert b64u_decode(enc) == raw


def test_signed_message_peer_attestation_verifies_and_tamper_fails() -> None:
    priv, pub = generate_ed25519_keypair()
    node_id = node_id_from_signing_pubkey(pub)
    kid = kid_from_signing_pubkey(pub)
    payload = build_peer_attestation_payload(
        pubkey_b64u=pub,
        bundle_hash="a" * 64,
        checks_run=["epoch_replay"],
        results={"status": "pass"},
        created_at_utc="2026-01-01T00:00:00Z",
    )
    signed = sign_peer_attestation_payload(
        payload_without_signature=payload,
        private_key_b64u=priv,
        signer_node_id=node_id,
        signer_pubkey_b64u=pub,
        kid=kid,
    )
    ok, detail = verify_peer_attestation_payload(signed)
    assert ok, detail

    tampered = json.loads(json.dumps(signed))
    tampered["payload"]["results"] = {"status": "fail"}
    ok2, _detail2 = verify_peer_attestation_payload(tampered)
    assert not ok2


def test_sealed_envelope_v1_multi_recipient_and_tamper() -> None:
    schema = json.loads((ROOT / "schema" / "sealed_envelope_v1.schema.json").read_text(encoding="utf-8"))

    priv_a, pub_a = generate_x25519_keypair()
    priv_b, pub_b = generate_x25519_keypair()
    priv_wrong, _pub_wrong = generate_x25519_keypair()

    envelope = seal_envelope(
        plaintext=b"vault-delta",
        content_schema="vault_delta_v1",
        content_type="application/json",
        recipients=[
            {"recipient_kid": "kid_aaaaaaaa", "recipient_x25519_pubkey_b64u": pub_a},
            {"recipient_kid": "kid_bbbbbbbb", "recipient_x25519_pubkey_b64u": pub_b},
        ],
        aad_struct={
            "schema_id": "sealed_envelope_v1",
            "bundle_hash": "b" * 64,
            "run_id": "run-1",
            "sender_node_id": "node_sender",
            "created_at": "2026-01-01T00:00:00Z",
        },
    )
    Draft202012Validator(schema).validate(envelope)

    assert open_envelope_for_recipient(
        envelope=envelope,
        recipient_kid="kid_aaaaaaaa",
        recipient_private_key_b64u=priv_a,
    ) == b"vault-delta"
    assert open_envelope_for_recipient(
        envelope=envelope,
        recipient_kid="kid_bbbbbbbb",
        recipient_private_key_b64u=priv_b,
    ) == b"vault-delta"

    wrong_failed = False
    try:
        open_envelope_for_recipient(
            envelope=envelope,
            recipient_kid="kid_aaaaaaaa",
            recipient_private_key_b64u=priv_wrong,
        )
    except Exception:
        wrong_failed = True
    assert wrong_failed

    tampered = json.loads(json.dumps(envelope))
    tampered["crypto"]["aad_b64u"] = b64u_encode(b'{"tampered":true}')
    tamper_failed = False
    try:
        open_envelope_for_recipient(
            envelope=tampered,
            recipient_kid="kid_aaaaaaaa",
            recipient_private_key_b64u=priv_a,
        )
    except Exception:
        tamper_failed = True
    assert tamper_failed


def test_evidence_bundle_hash_is_deterministic_by_sorted_paths() -> None:
    bundle = {
        "artifacts": [
            {"path": "z.txt", "sha256": "f" * 64, "size_bytes": 2},
            {"path": "a.txt", "sha256": "e" * 64, "size_bytes": 1},
        ]
    }
    h1 = compute_evidence_bundle_hash(bundle)
    h2 = compute_evidence_bundle_hash({"artifacts": list(reversed(bundle["artifacts"]))})
    assert h1 == h2
    assert len(h1) == 64


def test_vault_delta_and_evidence_schemas_validate_minimal_examples() -> None:
    vault_schema = json.loads((ROOT / "schema" / "vault_delta_v1.schema.json").read_text(encoding="utf-8"))
    evidence_schema = json.loads((ROOT / "schema" / "evidence_bundle_v1.schema.json").read_text(encoding="utf-8"))

    Draft202012Validator(vault_schema).validate(
        {
            "schema": "vault_delta_v1",
            "vault_id": "vault-1",
            "delta_id": "d1",
            "parent_delta_sha256": None,
            "created_at_utc": "2026-01-01T00:00:00Z",
            "scope": "vault/full",
            "retention": {"min_days": 0, "max_days": 30, "tombstone_after_days": 31},
            "entries": [],
        }
    )

    Draft202012Validator(evidence_schema).validate(
        {
            "schema": "evidence_bundle_v1",
            "bundle_id": "bundle-1",
            "created_at_utc": "2026-01-01T00:00:00Z",
            "producer": {"node_id": "node_abcdefghi", "software": "sophia", "version": "1"},
            "policy": {"network_profile": "witness_only", "share_scopes": ["hashes/*"], "peer_set": []},
            "artifacts": [
                {
                    "path": "attestations.json",
                    "content_type": "application/json",
                    "sha256": canonical_sha256_hex({"x": 1}),
                    "size_bytes": 10,
                    "classification": "evidence",
                    "encrypted": False,
                    "transport": {"transport_sha256": "a" * 64, "transport_size_bytes": 10},
                }
            ],
            "bundle_sha256": "b" * 64,
        }
    )
