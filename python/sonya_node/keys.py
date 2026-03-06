from __future__ import annotations

import base64
import json
from dataclasses import dataclass
from pathlib import Path

from cryptography.hazmat.primitives.asymmetric.ed25519 import (
    Ed25519PrivateKey,
    Ed25519PublicKey,
)
from cryptography.hazmat.primitives import serialization


@dataclass(slots=True)
class SonyaKeyPair:
    public_key: Ed25519PublicKey
    private_key: Ed25519PrivateKey

    def public_key_b64(self) -> str:
        raw = self.public_key.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw,
        )
        return base64.b64encode(raw).decode("ascii")

    def sign_b64(self, message: bytes) -> str:
        sig = self.private_key.sign(message)
        return base64.b64encode(sig).decode("ascii")


def load_or_generate_keypair(config_dir: Path) -> SonyaKeyPair:
    """
    Load an existing Ed25519 keypair from config_dir/sonya_node_key.json,
    or generate a new one if no file is present.
    """
    key_path = config_dir / "sonya_node_key.json"

    if key_path.exists():
        payload = json.loads(key_path.read_text(encoding="utf-8-sig"))
        pub_b64 = payload.get("public_key", "")
        priv_b64 = payload.get("private_key", "")

        if not pub_b64 or not priv_b64:
            raise ValueError("Incomplete Sonya keypair in sonya_node_key.json")

        pub_raw = base64.b64decode(pub_b64.encode("ascii"))
        priv_raw = base64.b64decode(priv_b64.encode("ascii"))

        private_key = Ed25519PrivateKey.from_private_bytes(priv_raw)
        public_key = Ed25519PublicKey.from_public_bytes(pub_raw)
        return SonyaKeyPair(public_key=public_key, private_key=private_key)

    # Generate new keypair
    private_key = Ed25519PrivateKey.generate()
    public_key = private_key.public_key()

    pub_raw = public_key.public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )
    priv_raw = private_key.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption(),
    )

    payload = {
        "public_key": base64.b64encode(pub_raw).decode("ascii"),
        "private_key": base64.b64encode(priv_raw).decode("ascii"),
    }
    config_dir.mkdir(parents=True, exist_ok=True)
    key_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    return SonyaKeyPair(public_key=public_key, private_key=private_key)
