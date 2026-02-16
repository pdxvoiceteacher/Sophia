from __future__ import annotations

import base64
import hashlib
import json
import os
from datetime import datetime, timezone
from typing import Any

from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ed25519, x25519
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF

SUITE_ID = "secure_swarm_v1"


def _ensure_json_finite(value: Any) -> None:
    if isinstance(value, float):
        if value != value or value in (float("inf"), float("-inf")):
            raise ValueError("non_finite_float_not_allowed")
    elif isinstance(value, dict):
        for key, nested in value.items():
            if not isinstance(key, str):
                raise ValueError("non_string_json_key_not_allowed")
            _ensure_json_finite(nested)
    elif isinstance(value, list):
        for nested in value:
            _ensure_json_finite(nested)


def canonical_json_bytes(payload: Any) -> bytes:
    """RFC8785-compatible in practice for our payload classes (sorted keys, compact JSON, finite numbers)."""
    _ensure_json_finite(payload)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def canonical_sha256_hex(payload: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def generate_ed25519_keypair() -> tuple[str, str]:
    private_key = ed25519.Ed25519PrivateKey.generate()
    public_key = private_key.public_key()
    private_b64 = base64.b64encode(
        private_key.private_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PrivateFormat.Raw,
            encryption_algorithm=serialization.NoEncryption(),
        )
    ).decode("ascii")
    public_b64 = base64.b64encode(
        public_key.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )
    ).decode("ascii")
    return private_b64, public_b64


def node_id_from_signing_pubkey(pubkey_b64: str) -> str:
    pub = base64.b64decode(pubkey_b64)
    return hashlib.sha256(pub).hexdigest()


def sign_peer_attestation_payload(
    *,
    payload_without_signature: dict[str, Any],
    private_key_b64: str,
    signer_node_id: str,
    schema_id: str = "peer_attestation_v1",
    suite_id: str = SUITE_ID,
) -> dict[str, Any]:
    preimage = dict(payload_without_signature)
    preimage["schema"] = schema_id
    preimage["suite_id"] = suite_id
    preimage["signer_node_id"] = signer_node_id
    preimage.setdefault("created_at", utc_now_iso())
    preimage.setdefault("signature_alg", "ed25519")
    preimage.setdefault("signature_format", "base64")
    preimage.setdefault("pubkey_format", "base64")

    signed_bytes_hash = canonical_sha256_hex(preimage)
    private_key = ed25519.Ed25519PrivateKey.from_private_bytes(base64.b64decode(private_key_b64))
    signature = private_key.sign(canonical_json_bytes(preimage))

    signed = dict(preimage)
    signed["signed_bytes_hash"] = signed_bytes_hash
    signed["signature"] = base64.b64encode(signature).decode("ascii")
    return signed


def verify_peer_attestation_payload(attestation: dict[str, Any]) -> tuple[bool, str]:
    required = {
        "schema",
        "suite_id",
        "signer_node_id",
        "pubkey",
        "pubkey_format",
        "created_at",
        "signature_alg",
        "signature_format",
        "signed_bytes_hash",
        "signature",
    }
    missing = sorted(list(required - set(attestation.keys())))
    if missing:
        return False, f"missing_fields:{','.join(missing)}"
    if attestation.get("signature_alg") != "ed25519":
        return False, "unsupported_signature_alg"
    if attestation.get("signature_format") != "base64":
        return False, "unsupported_signature_format"
    if attestation.get("pubkey_format") != "base64":
        return False, "unsupported_pubkey_format"

    preimage = dict(attestation)
    signature_b64 = preimage.pop("signature", None)
    signed_bytes_hash = preimage.pop("signed_bytes_hash", None)
    if signed_bytes_hash != canonical_sha256_hex(preimage):
        return False, "signed_bytes_hash_mismatch"

    try:
        pub = ed25519.Ed25519PublicKey.from_public_bytes(base64.b64decode(attestation["pubkey"]))
        pub.verify(base64.b64decode(signature_b64), canonical_json_bytes(preimage))
    except Exception:
        return False, "signature_invalid"
    return True, "verified"


def generate_x25519_keypair() -> tuple[str, str]:
    private_key = x25519.X25519PrivateKey.generate()
    public_key = private_key.public_key()
    return (
        base64.b64encode(
            private_key.private_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PrivateFormat.Raw,
                encryption_algorithm=serialization.NoEncryption(),
            )
        ).decode("ascii"),
        base64.b64encode(
            public_key.public_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PublicFormat.Raw,
            )
        ).decode("ascii"),
    )


def _derive_wrap_key(shared_secret: bytes, aad_meta: dict[str, Any]) -> bytes:
    return HKDF(
        algorithm=hashes.SHA256(),
        length=32,
        salt=None,
        info=("secure-swarm-wrap:" + canonical_sha256_hex(aad_meta)).encode("utf-8"),
    ).derive(shared_secret)


def envelope_encrypt_for_recipient(
    *,
    plaintext: bytes,
    recipient_pubkey_b64: str,
    aad_meta: dict[str, Any],
) -> dict[str, Any]:
    dek = os.urandom(32)
    payload_nonce = os.urandom(12)
    wrapped_nonce = os.urandom(12)

    aad = canonical_json_bytes(aad_meta)
    ciphertext = AESGCM(dek).encrypt(payload_nonce, plaintext, aad)

    eph_priv = x25519.X25519PrivateKey.generate()
    eph_pub = eph_priv.public_key()
    recipient_pub = x25519.X25519PublicKey.from_public_bytes(base64.b64decode(recipient_pubkey_b64))
    wrap_key = _derive_wrap_key(eph_priv.exchange(recipient_pub), aad_meta)
    wrapped_dek = AESGCM(wrap_key).encrypt(wrapped_nonce, dek, aad)

    return {
        "schema": "vault_bundle_v1",
        "suite_id": SUITE_ID,
        "enc_alg": "AES-256-GCM",
        "wrap_alg": "X25519+HKDF-SHA256+AES-256-GCM",
        "aad_meta": aad_meta,
        "ciphertext": base64.b64encode(ciphertext).decode("ascii"),
        "payload_nonce": base64.b64encode(payload_nonce).decode("ascii"),
        "ephemeral_pubkey": base64.b64encode(
            eph_pub.public_bytes(encoding=serialization.Encoding.Raw, format=serialization.PublicFormat.Raw)
        ).decode("ascii"),
        "wrapped_dek": base64.b64encode(wrapped_dek).decode("ascii"),
        "wrapped_nonce": base64.b64encode(wrapped_nonce).decode("ascii"),
    }


def envelope_decrypt_for_recipient(
    *,
    envelope: dict[str, Any],
    recipient_private_key_b64: str,
) -> bytes:
    aad_meta = envelope["aad_meta"]
    aad = canonical_json_bytes(aad_meta)
    recipient_priv = x25519.X25519PrivateKey.from_private_bytes(base64.b64decode(recipient_private_key_b64))
    eph_pub = x25519.X25519PublicKey.from_public_bytes(base64.b64decode(envelope["ephemeral_pubkey"]))
    wrap_key = _derive_wrap_key(recipient_priv.exchange(eph_pub), aad_meta)
    dek = AESGCM(wrap_key).decrypt(
        base64.b64decode(envelope["wrapped_nonce"]),
        base64.b64decode(envelope["wrapped_dek"]),
        aad,
    )
    try:
        return AESGCM(dek).decrypt(
            base64.b64decode(envelope["payload_nonce"]),
            base64.b64decode(envelope["ciphertext"]),
            aad,
        )
    except InvalidTag as err:
        raise ValueError("ciphertext_or_aad_tamper_detected") from err
