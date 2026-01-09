from pathlib import Path
import json
import importlib.util

import pytest

pytest.importorskip("coherenceledger")

from coherenceledger.keystore import KeyStore
from coherenceledger.ledger import Ledger
from coherenceledger.schemas import LedgerEvent
from coherenceledger.crypto import b64encode
from coherenceledger.checkpoint import append_checkpoint_event


def test_checkpoint_appends_event(tmp_path: Path):
    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / ".secrets").mkdir()
    keystore = repo / ".secrets" / "coherenceledger_keystore.json"
    ledger = repo / "ledger.jsonl"

    ks = KeyStore(path=keystore)
    ks.generate()

    # create a couple dummy events
    led = Ledger(path=ledger)
    did, kp = ks.load_keypair()
    for i in range(3):
        ev = LedgerEvent.create_unsigned(
            actor_did=did.did,
            purpose="test",
            event_type="test.event",
            payload={"i": i},
            prev_seal=led.last_seal(),
        )
        sig = kp.sign(ev.signing_payload())
        ev.signature = b64encode(sig)
        ev.public_key_b64 = b64encode(kp.public_bytes_raw())
        led.append(ev)

    led.verify()

    cp, meta = append_checkpoint_event(ledger_path=ledger, keystore_path=keystore, start_index=0, end_index=None)
    assert meta["event_id"]
    assert meta["seal"]
    assert cp["merkle_root"]
    Ledger(path=ledger).verify()
