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


# NOTE: this encoder is a strict RFC8785/JCS-compatible subset used by Secure Swarm payloads.
# It intentionally rejects non-finite floats and unsupported JSON value forms.
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
    _ensure_json_finite(payload)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def canonical_sha256_hex(payload: Any) -> str:
    return hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def b64u_encode(raw: bytes) -> str:
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def b64u_decode(text: str) -> bytes:
    pad = "=" * ((4 - (len(text) % 4)) % 4)
    return base64.urlsafe_b64decode(text + pad)


def generate_ed25519_keypair() -> tuple[str, str]:
    private_key = ed25519.Ed25519PrivateKey.generate()
    public_key = private_key.public_key()
    private_b64u = b64u_encode(
        private_key.private_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PrivateFormat.Raw,
            encryption_algorithm=serialization.NoEncryption(),
        )
    )
    public_b64u = b64u_encode(
        public_key.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )
    )
    return private_b64u, public_b64u


def full_signing_pubkey_sha256(pubkey_b64u: str) -> str:
    return hashlib.sha256(b64u_decode(pubkey_b64u)).hexdigest()


def node_id_from_signing_pubkey(pubkey_b64u: str) -> str:
    return f"node_{b64u_encode(hashlib.sha256(b64u_decode(pubkey_b64u)).digest())[:16]}"


def kid_from_signing_pubkey(pubkey_b64u: str) -> str:
    return f"kid_{b64u_encode(hashlib.sha256(b64u_decode(pubkey_b64u)).digest())[:24]}"


def _ed25519_sign(private_key_b64u: str, payload: dict[str, Any]) -> str:
    private_key = ed25519.Ed25519PrivateKey.from_private_bytes(b64u_decode(private_key_b64u))
    return b64u_encode(private_key.sign(canonical_json_bytes(payload)))


def _ed25519_verify(public_key_b64u: str, payload: dict[str, Any], signature_b64u: str) -> bool:
    try:
        public_key = ed25519.Ed25519PublicKey.from_public_bytes(b64u_decode(public_key_b64u))
        public_key.verify(b64u_decode(signature_b64u), canonical_json_bytes(payload))
        return True
    except Exception:
        return False


def wrap_signed_message(
    *,
    payload: dict[str, Any],
    payload_schema: str,
    signing_private_key_b64u: str,
    signer_pubkey_b64u: str,
    signer_node_id: str,
    kid: str,
) -> dict[str, Any]:
    payload_copy = dict(payload)
    signature = _ed25519_sign(signing_private_key_b64u, payload_copy)
    return {
        "schema": "signed_message_v1",
        "payload_schema": payload_schema,
        "payload": payload_copy,
        "signer": {
            "node_id": signer_node_id,
            "kid": kid,
            "pubkey_alg": "ed25519",
            "pubkey_b64u": signer_pubkey_b64u,
        },
        "signature_alg": "ed25519",
        "signature": signature,
    }


def verify_signed_message(message: dict[str, Any]) -> tuple[bool, str]:
    if message.get("schema") != "signed_message_v1":
        return False, "schema_mismatch"
    payload = message.get("payload")
    signer = message.get("signer") or {}
    if not isinstance(payload, dict):
        return False, "payload_missing"
    if message.get("signature_alg") != "ed25519":
        return False, "unsupported_signature_alg"
    pubkey = signer.get("pubkey_b64u")
    signature = message.get("signature")
    if not pubkey or not signature:
        return False, "signature_or_pubkey_missing"
    if not _ed25519_verify(pubkey, payload, signature):
        return False, "signature_invalid"
    expected_node = node_id_from_signing_pubkey(pubkey)
    if signer.get("node_id") != expected_node:
        return False, "signer_node_id_mismatch"
    expected_kid = kid_from_signing_pubkey(pubkey)
    if signer.get("kid") != expected_kid:
        return False, "signer_kid_mismatch"
    return True, "verified"


def build_peer_attestation_payload(
    *,
    pubkey_b64u: str,
    bundle_hash: str,
    checks_run: list[str],
    results: dict[str, Any],
    created_at_utc: str | None = None,
) -> dict[str, Any]:
    return {
        "schema": "peer_attestation_v1",
        "suite_id": SUITE_ID,
        "created_at_utc": created_at_utc or utc_now_iso(),
        "pubkey_b64u": pubkey_b64u,
        "bundle_hash": bundle_hash,
        "checks_run": checks_run,
        "results": results,
    }


def sign_peer_attestation_payload(
    *,
    payload_without_signature: dict[str, Any],
    private_key_b64u: str,
    signer_node_id: str,
    signer_pubkey_b64u: str,
    kid: str,
) -> dict[str, Any]:
    return wrap_signed_message(
        payload=payload_without_signature,
        payload_schema="peer_attestation_v1",
        signing_private_key_b64u=private_key_b64u,
        signer_pubkey_b64u=signer_pubkey_b64u,
        signer_node_id=signer_node_id,
        kid=kid,
    )


def verify_peer_attestation_payload(attestation: dict[str, Any]) -> tuple[bool, str]:
    if attestation.get("schema") != "signed_message_v1" or attestation.get("payload_schema") != "peer_attestation_v1":
        return False, "attestation_wrapper_invalid"
    ok, detail = verify_signed_message(attestation)
    if not ok:
        return False, detail
    payload = attestation.get("payload") or {}
    required = {"schema", "suite_id", "created_at_utc", "pubkey_b64u", "bundle_hash", "checks_run", "results"}
    missing = sorted(required - set(payload.keys()))
    if missing:
        return False, f"attestation_payload_missing:{','.join(missing)}"
    return True, "verified"


def generate_x25519_keypair() -> tuple[str, str]:
    private_key = x25519.X25519PrivateKey.generate()
    public_key = private_key.public_key()
    return (
        b64u_encode(
            private_key.private_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PrivateFormat.Raw,
                encryption_algorithm=serialization.NoEncryption(),
            )
        ),
        b64u_encode(
            public_key.public_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PublicFormat.Raw,
            )
        ),
    )


def _derive_wrap_key(shared_secret: bytes, aad_struct: dict[str, Any]) -> bytes:
    return HKDF(
        algorithm=hashes.SHA256(),
        length=32,
        salt=None,
        info=("secure-swarm-wrap:" + canonical_sha256_hex(aad_struct)).encode("utf-8"),
    ).derive(shared_secret)


def seal_envelope(
    *,
    plaintext: bytes,
    content_schema: str,
    content_type: str,
    recipients: list[dict[str, str]],
    aad_struct: dict[str, Any],
) -> dict[str, Any]:
    if not recipients:
        raise ValueError("recipients_required")

    content_key = os.urandom(32)
    nonce = os.urandom(12)
    aad_bytes = canonical_json_bytes(aad_struct)
    ciphertext = AESGCM(content_key).encrypt(nonce, plaintext, aad_bytes)
    ciphertext_sha256 = hashlib.sha256(ciphertext).hexdigest()

    recipient_entries: list[dict[str, Any]] = []
    for recipient in recipients:
        recipient_kid = recipient["recipient_kid"]
        recipient_pub = b64u_decode(recipient["recipient_x25519_pubkey_b64u"])
        recipient_pubkey = x25519.X25519PublicKey.from_public_bytes(recipient_pub)

        eph_priv = x25519.X25519PrivateKey.generate()
        eph_pub = eph_priv.public_key()
        wrap_key = _derive_wrap_key(eph_priv.exchange(recipient_pubkey), aad_struct)
        wrapped_key = AESGCM(wrap_key).encrypt(nonce, content_key, aad_bytes)

        recipient_entries.append(
            {
                "recipient_kid": recipient_kid,
                "recipient_alg": "x25519",
                "wrapped_key_b64u": b64u_encode(wrapped_key),
                "wrap_info": {
                    "ephemeral_pubkey_b64u": b64u_encode(
                        eph_pub.public_bytes(
                            encoding=serialization.Encoding.Raw,
                            format=serialization.PublicFormat.Raw,
                        )
                    )
                },
            }
        )

    return {
        "schema": "sealed_envelope_v1",
        "version": 1,
        "content": {
            "content_schema": content_schema,
            "content_type": content_type,
            "plaintext_sha256": hashlib.sha256(plaintext).hexdigest(),
            "plaintext_size_bytes": len(plaintext),
        },
        "crypto": {
            "cipher": "AES-256-GCM",
            "kdf": "HKDF-SHA256",
            "key_wrap": "X25519",
            "nonce_b64u": b64u_encode(nonce),
            "aad_b64u": b64u_encode(aad_bytes),
        },
        "recipients": recipient_entries,
        "ciphertext_b64u": b64u_encode(ciphertext),
        "ciphertext_sha256": ciphertext_sha256,
    }


def open_envelope_for_recipient(
    *,
    envelope: dict[str, Any],
    recipient_kid: str,
    recipient_private_key_b64u: str,
) -> bytes:
    aad_bytes = b64u_decode(envelope["crypto"]["aad_b64u"])
    aad_struct_hash = canonical_sha256_hex(json.loads(aad_bytes.decode("utf-8")))
    if aad_struct_hash != canonical_sha256_hex(json.loads(aad_bytes.decode("utf-8"))):
        raise ValueError("aad_invalid")

    recipient_entry = next((r for r in envelope["recipients"] if r.get("recipient_kid") == recipient_kid), None)
    if recipient_entry is None:
        raise ValueError("recipient_not_found")

    recipient_priv = x25519.X25519PrivateKey.from_private_bytes(b64u_decode(recipient_private_key_b64u))
    eph_pub = x25519.X25519PublicKey.from_public_bytes(
        b64u_decode(recipient_entry["wrap_info"]["ephemeral_pubkey_b64u"])
    )
    aad_struct = json.loads(aad_bytes.decode("utf-8"))
    wrap_key = _derive_wrap_key(recipient_priv.exchange(eph_pub), aad_struct)
    nonce = b64u_decode(envelope["crypto"]["nonce_b64u"])

    try:
        content_key = AESGCM(wrap_key).decrypt(
            nonce,
            b64u_decode(recipient_entry["wrapped_key_b64u"]),
            aad_bytes,
        )
        plaintext = AESGCM(content_key).decrypt(
            nonce,
            b64u_decode(envelope["ciphertext_b64u"]),
            aad_bytes,
        )
    except InvalidTag as err:
        raise ValueError("ciphertext_or_aad_tamper_detected") from err

    if hashlib.sha256(plaintext).hexdigest() != envelope["content"]["plaintext_sha256"]:
        raise ValueError("plaintext_hash_mismatch")
    return plaintext


def compute_evidence_bundle_hash(bundle: dict[str, Any]) -> str:
    artifacts = bundle.get("artifacts") or []
    lines: list[str] = []
    for entry in sorted(artifacts, key=lambda e: str(e.get("path", ""))):
        path = str(entry.get("path", ""))
        sha = str(entry.get("sha256", ""))
        size = int(entry.get("size_bytes", 0))
        lines.append(f"{path}|{sha}|{size}")
    payload = "\n".join(lines).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


# Backward-compatible wrappers used by previous tests/callers.
def envelope_encrypt_for_recipient(*, plaintext: bytes, recipient_pubkey_b64: str, aad_meta: dict[str, Any]) -> dict[str, Any]:
    return seal_envelope(
        plaintext=plaintext,
        content_schema="vault_delta_v1",
        content_type="application/json",
        recipients=[
            {
                "recipient_kid": "kid_legacy",
                "recipient_x25519_pubkey_b64u": recipient_pubkey_b64,
            }
        ],
        aad_struct=aad_meta,
    )


def envelope_decrypt_for_recipient(*, envelope: dict[str, Any], recipient_private_key_b64: str) -> bytes:
    return open_envelope_for_recipient(
        envelope=envelope,
        recipient_kid="kid_legacy",
        recipient_private_key_b64u=recipient_private_key_b64,
    )
