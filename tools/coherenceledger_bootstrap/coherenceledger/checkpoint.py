from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
import hashlib
import json
from datetime import datetime, timezone

from coherenceledger.ledger import Ledger
from coherenceledger.schemas import LedgerEvent
from coherenceledger.keystore import KeyStore
from coherenceledger.crypto import b64encode


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _sha256(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()


def _is_hex64(s: str) -> bool:
    if not isinstance(s, str) or len(s) != 64:
        return False
    try:
        bytes.fromhex(s)
        return True
    except Exception:
        return False


def merkle_root(leaves: List[bytes]) -> bytes:
    """
    Deterministic Merkle root:
      - if odd number of nodes, duplicate last
      - parent = sha256(left || right)
    """
    if not leaves:
        return _sha256(b"")
    level = list(leaves)
    while len(level) > 1:
        if len(level) % 2 == 1:
            level.append(level[-1])
        nxt: List[bytes] = []
        for i in range(0, len(level), 2):
            nxt.append(_sha256(level[i] + level[i + 1]))
        level = nxt
    return level[0]


def _leaf_from_event(ev: Dict[str, Any]) -> bytes:
    """
    Leaf mode: prefer seal bytes if seal is 64-hex; otherwise hash the canonical line.
    """
    seal = ev.get("seal")
    if _is_hex64(seal):
        return bytes.fromhex(seal)
    # fallback: hash canonical json of the event object
    s = json.dumps(ev, separators=(",", ":"), sort_keys=True, ensure_ascii=False).encode("utf-8")
    return _sha256(s)


def load_ledger_events(ledger_path: Path) -> List[Dict[str, Any]]:
    events: List[Dict[str, Any]] = []
    for line in ledger_path.read_text(encoding="utf-8-sig").splitlines():
        line = line.strip()
        if not line:
            continue
        events.append(json.loads(line))
    return events


def compute_checkpoint(
    *,
    ledger_path: Path,
    start_index: int = 0,
    end_index: Optional[int] = None,
) -> Dict[str, Any]:
    events = load_ledger_events(ledger_path)
    if end_index is None:
        end_index = len(events)
    if not (0 <= start_index <= end_index <= len(events)):
        raise ValueError("invalid checkpoint range")

    window = events[start_index:end_index]
    leaves = [_leaf_from_event(ev) for ev in window]
    root = merkle_root(leaves).hex()

    return {
        "version": 1,
        "checkpoint_id": None,  # filled by caller
        "created_at": _utc_now_iso(),
        "ledger_path": str(ledger_path),
        "range": {"start_index": start_index, "end_index": end_index, "count": len(window)},
        "leaf_mode": "seal_or_hash(event)",
        "hash_alg": "sha256",
        "merkle_root": root,
        "last_seal_in_range": (window[-1].get("seal") if window else None),
    }


def append_checkpoint_event(
    *,
    ledger_path: Path,
    keystore_path: Path,
    start_index: int = 0,
    end_index: Optional[int] = None,
    purpose: str = "ledger.checkpoint",
) -> Tuple[Dict[str, Any], Dict[str, str]]:
    """
    Appends a signed ledger.checkpoint event to the ledger.
    Returns (checkpoint_doc, {event_id, seal}).
    """
    # verify existing chain first
    led = Ledger(path=ledger_path)
    led.verify()

    cp = compute_checkpoint(ledger_path=ledger_path, start_index=start_index, end_index=end_index)

    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()

    # Fill checkpoint_id deterministically via event_id (set after unsigned creation)
    payload = dict(cp)
    payload.pop("checkpoint_id", None)

    ev = LedgerEvent.create_unsigned(
        actor_did=did.did,
        purpose=purpose,
        event_type="ledger.checkpoint",
        payload=payload,
        prev_seal=led.last_seal(),
    )
    sig = kp.sign(ev.signing_payload())
    ev.signature = b64encode(sig)
    ev.public_key_b64 = b64encode(kp.public_bytes_raw())

    # now we know event_id; set checkpoint_id in a receipt doc
    cp["checkpoint_id"] = ev.event_id

    led.append(ev)
    led.verify()

    return cp, {"event_id": ev.event_id, "seal": ev.seal}
