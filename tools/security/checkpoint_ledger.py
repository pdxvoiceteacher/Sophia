from __future__ import annotations
import json
from pathlib import Path
import os

from coherenceledger.checkpoint import append_checkpoint_event


def truthy(s: str) -> bool:
    return s.strip().lower() in {"1","true","yes","y","on"}


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser(description="Append a ledger.checkpoint event and write a checkpoint receipt")
    ap.add_argument("--ledger", default=os.getenv("COHERENCELEDGER_LEDGER", "ledger.jsonl"))
    ap.add_argument("--keystore", default=os.getenv("COHERENCELEDGER_KEYSTORE", ".secrets/coherenceledger_keystore.json"))
    ap.add_argument("--start", type=int, default=0)
    ap.add_argument("--end", type=int, default=None)
    ap.add_argument("--purpose", default=os.getenv("COHERENCELEDGER_PURPOSE", "ledger.checkpoint"))
    ap.add_argument("--receipt-dir", default="governance/seals/checkpoints")
    args = ap.parse_args()

    ledger = Path(args.ledger)
    keystore = Path(args.keystore)

    cp, meta = append_checkpoint_event(
        ledger_path=ledger,
        keystore_path=keystore,
        start_index=args.start,
        end_index=args.end,
        purpose=args.purpose,
    )

    outdir = Path(args.receipt_dir)
    outdir.mkdir(parents=True, exist_ok=True)
    receipt_path = outdir / f"checkpoint_{meta['event_id']}.json"
    receipt_path.write_text(json.dumps({"checkpoint": cp, "event": meta}, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

    print(f"Wrote: {receipt_path}")
    print(f"event_id={meta['event_id']}")
    print(f"seal={meta['seal']}")
    print(f"merkle_root={cp['merkle_root']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
