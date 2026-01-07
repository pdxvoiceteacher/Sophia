"""
Tally v0 (purpose-bound to Vote Manifest v0)

Reads:
- vote_manifest.json (required)
- ballots/*.json (0..N)

Produces:
- tally.json (counts by choice)
Optionally:
- DID-signs the tally file
- ledger-anchors the tally file when COHERENCELEDGER_ENABLE is truthy

Design goals:
- Cross-platform (pathlib)
- Deterministic canonicalization for signatures
- BOM-tolerant reads (utf-8-sig)
- Modular: tally works without coherenceledger unless sign/anchor is enabled
"""
from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional
from uuid import uuid4

import hashlib
import json
import os


TALLY_SCHEMA_ID = "ucc.vote_tally.v0"


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _truthy_env(name: str) -> bool:
    return os.getenv(name, "").strip().lower() in {"1", "true", "yes", "y", "on"}


def _canonical_dumps(obj: Any) -> str:
    try:
        from coherenceledger import jcs  # type: ignore
        return jcs.dumps(obj)
    except Exception:
        return json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def _sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def _sha256_file(path: Path) -> str:
    return _sha256_hex(path.read_bytes())


def _safe_relpath(path: Path, base: Optional[Path]) -> str:
    try:
        return str(path.resolve().relative_to(base.resolve())) if base else str(path.resolve())
    except Exception:
        return str(path.resolve())


def load_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8-sig"))


def load_manifest(manifest_path: Path) -> Dict[str, Any]:
    m = load_json(manifest_path)
    if not m.get("manifest_id"):
        raise ValueError("manifest_id missing in vote_manifest.json")
    return m


def load_ballot(ballot_path: Path) -> Dict[str, Any]:
    b = load_json(ballot_path)
    if not b.get("manifest_id"):
        raise ValueError(f"manifest_id missing in ballot: {ballot_path}")
    return b


def _verify_signed_payload(obj: Dict[str, Any]) -> None:
    """
    Verifies a DID signature if present.
    If signature is absent, caller decides whether that is allowed.
    """
    sig = obj.get("signature")
    if not sig:
        raise ValueError("signature missing")

    # Build payload = obj without signature, canonicalized
    body = dict(obj)
    body.pop("signature", None)
    payload = _canonical_dumps(body).encode("utf-8")

    # verify using coherenceledger helpers
    from coherenceledger.crypto import b64decode, load_public_key_raw  # type: ignore

    pub = load_public_key_raw(b64decode(sig["public_key_b64"]))
    pub.verify(b64decode(sig["signature"]), payload)


def tally_ballots(
    *,
    manifest: Dict[str, Any],
    ballot_paths: List[Path],
    verify_ballot_signatures: bool = False,
    strict: bool = False,
) -> Dict[str, Any]:
    """
    Returns tally dict. Does NOT write to disk.
    """
    manifest_id = manifest["manifest_id"]
    anon_mode = (manifest.get("anonymity", {}) or {}).get("mode", "open")

    counts: Dict[str, int] = {}
    seen = 0
    valid = 0
    invalid = 0
    invalid_reasons: List[Dict[str, str]] = []

    type_counts: Dict[str, int] = {}

    for bp in ballot_paths:
        seen += 1
        try:
            b = load_ballot(bp)

            # enforce manifest match
            if b.get("manifest_id") != manifest_id:
                raise ValueError("manifest_id mismatch")

            # optional signature verification (only meaningful for open ballots)
            if verify_ballot_signatures:
                if anon_mode != "open" and strict:
                    raise ValueError(f"manifest anonymity '{anon_mode}' forbids DID ballot signatures in strict mode")
                _verify_signed_payload(b)

            bt = (b.get("ballot") or {}).get("type")
            sel = (b.get("ballot") or {}).get("selection")
            if not bt or sel is None:
                raise ValueError("ballot.type or ballot.selection missing")

            type_counts[bt] = type_counts.get(bt, 0) + 1

            if bt == "single_choice":
                choice = (sel or {}).get("choice")
                if not isinstance(choice, str) or not choice:
                    raise ValueError("single_choice requires selection.choice string")
                counts[choice] = counts.get(choice, 0) + 1

            elif bt == "approval":
                approve = (sel or {}).get("approve", [])
                if not isinstance(approve, list):
                    raise ValueError("approval requires selection.approve list")
                for c in approve:
                    if isinstance(c, str) and c:
                        counts[c] = counts.get(c, 0) + 1

            elif bt == "ranked":
                rank = (sel or {}).get("rank", [])
                if not isinstance(rank, list) or not rank:
                    raise ValueError("ranked requires non-empty selection.rank list")
                first = rank[0]
                if isinstance(first, str) and first:
                    counts[first] = counts.get(first, 0) + 1
            else:
                raise ValueError(f"unsupported ballot type: {bt}")

            valid += 1

        except Exception as e:
            invalid += 1
            invalid_reasons.append({"path": str(bp), "reason": str(e)})

    tally: Dict[str, Any] = {
        "version": 1,
        "schema_id": TALLY_SCHEMA_ID,
        "tally_id": str(uuid4()),
        "created_at": _utc_now_iso(),
        "manifest_id": manifest_id,
        "policy": {
            "manifest_anonymity_mode": anon_mode,
            "verify_ballot_signatures": bool(verify_ballot_signatures),
            "strict": bool(strict),
        },
        "ballots": {
            "seen": seen,
            "valid": valid,
            "invalid": invalid,
            "type_counts": type_counts,
        },
        "counts": counts,
    }

    # include invalid reasons only if asked (avoid leaking paths in some contexts)
    if strict and invalid_reasons:
        tally["invalid_reasons"] = invalid_reasons

    return tally


def _sign_inplace(doc: Dict[str, Any], *, keystore_path: Path) -> None:
    body = dict(doc)
    body.pop("signature", None)

    payload = _canonical_dumps(body).encode("utf-8")
    payload_hash = _sha256_hex(payload)

    from coherenceledger.keystore import KeyStore  # type: ignore
    from coherenceledger.crypto import b64encode  # type: ignore

    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()

    sig = kp.sign(payload)

    doc["signature"] = {
        "did": did.did,
        "public_key_b64": b64encode(kp.public_bytes_raw()),
        "signature": b64encode(sig),
        "signed_payload_sha256": payload_hash,
        "signed_at": _utc_now_iso(),
        "alg": "Ed25519",
        "canon": "canonical-json",
    }


def _anchor_tally_file(
    *,
    tally_path: Path,
    manifest_id: str,
    ledger_path: Path,
    keystore_path: Path,
    repo_root: Optional[Path],
    purpose: str,
) -> Dict[str, str]:
    from coherenceledger.schemas import LedgerEvent  # type: ignore
    from coherenceledger.ledger import Ledger        # type: ignore
    from coherenceledger.keystore import KeyStore    # type: ignore
    from coherenceledger.crypto import b64encode     # type: ignore

    ledger = Ledger(path=ledger_path)
    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()

    payload: Dict[str, Any] = {
        "artifact_type": "ucc.vote_tally",
        "manifest_id": manifest_id,
        "tally_path": _safe_relpath(tally_path, repo_root),
        "tally_sha256": _sha256_file(tally_path),
    }

    ev = LedgerEvent.create_unsigned(
        actor_did=did.did,
        purpose=purpose,
        event_type="ucc.vote_tally.anchor",
        payload=payload,
        prev_seal=ledger.last_seal(),
    )
    sig = kp.sign(ev.signing_payload())
    ev.signature = b64encode(sig)
    ev.public_key_b64 = b64encode(kp.public_bytes_raw())

    ledger.append(ev)
    ledger.verify()
    return {"event_id": ev.event_id, "seal": ev.seal}


def write_tally(
    *,
    outdir: Path,
    manifest_path: Path,
    verify_ballot_signatures: bool = False,
    strict: bool = False,
    sign: bool = False,
    anchor: bool = False,
    repo_root: Optional[Path] = None,
    keystore_path: Optional[Path] = None,
    ledger_path: Optional[Path] = None,
    ledger_purpose: str = "ucc.vote_tally.anchor",
) -> Path:
    """
    Writes outdir/tally.json and optionally signs+anchors it.
    """
    outdir = outdir.resolve()
    outdir.mkdir(parents=True, exist_ok=True)

    repo_root = repo_root.resolve() if repo_root else None
    if repo_root is None:
        repo_root = Path(__file__).resolve().parents[3]

    keystore_path = (keystore_path or (repo_root / ".secrets" / "coherenceledger_keystore.json")).resolve()
    ledger_path = (ledger_path or (repo_root / "ledger.jsonl")).resolve()

    manifest = load_manifest(manifest_path)

    ballots_dir = outdir / "ballots"
    ballot_paths = sorted(ballots_dir.glob("*.json")) if ballots_dir.exists() else []

    tally = tally_ballots(
        manifest=manifest,
        ballot_paths=ballot_paths,
        verify_ballot_signatures=verify_ballot_signatures,
        strict=strict,
    )

    if sign:
        _sign_inplace(tally, keystore_path=keystore_path)

    tally_path = outdir / "tally.json"
    tally_path.write_text(
        json.dumps(tally, ensure_ascii=False, separators=(",", ":"), sort_keys=True),
        encoding="utf-8",
    )

    if anchor:
        _anchor_tally_file(
            tally_path=tally_path,
            manifest_id=manifest["manifest_id"],
            ledger_path=ledger_path,
            keystore_path=keystore_path,
            repo_root=repo_root,
            purpose=ledger_purpose,
        )

    return tally_path


def write_tally_env(*, outdir: Path, manifest_path: Path, verify_ballot_signatures: bool = False) -> Path:
    """
    Env-gated convenience:
      if COHERENCELEDGER_ENABLE -> sign+anchor
      else -> write only
    """
    enable = _truthy_env("COHERENCELEDGER_ENABLE")
    strict = _truthy_env("COHERENCELEDGER_STRICT")
    purpose = os.getenv("COHERENCELEDGER_PURPOSE", "ucc.vote_tally.anchor")

    repo_root = Path(__file__).resolve().parents[3]
    keystore = Path(os.getenv("COHERENCELEDGER_KEYSTORE", str(repo_root / ".secrets" / "coherenceledger_keystore.json")))
    ledger = Path(os.getenv("COHERENCELEDGER_LEDGER", str(repo_root / "ledger.jsonl")))

    if enable and not keystore.exists():
        if strict:
            raise FileNotFoundError(f"CoherenceLedger keystore missing: {keystore}")
        enable = False

    return write_tally(
        outdir=outdir,
        manifest_path=manifest_path,
        verify_ballot_signatures=verify_ballot_signatures,
        strict=strict,
        sign=enable,
        anchor=enable,
        repo_root=repo_root,
        keystore_path=keystore,
        ledger_path=ledger,
        ledger_purpose=purpose,
    )
