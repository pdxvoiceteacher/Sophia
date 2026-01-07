from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional
from uuid import uuid4

import hashlib
import json
import os


TALLY_SCHEMA_ID = "ucc.vote_tally.v1"


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


def load_coherence_registry(path: Path) -> Dict[str, float]:
    """
    Coherence registry format (JSON):
      { "did:key:...": 0.83, "did:key:...": 0.42 }

    Accepts BOM (utf-8-sig). Values are coerced to float.
    """
    if not path.exists():
        return {}
    obj = json.loads(path.read_text(encoding="utf-8-sig"))
    out: Dict[str, float] = {}
    if isinstance(obj, dict):
        for k, v in obj.items():
            try:
                out[str(k)] = float(v)
            except Exception:
                continue
    return out


def _verify_signed_payload(obj: Dict[str, Any]) -> str:
    """
    Verifies a DID signature if present.
    Returns signer DID.
    """
    sig = obj.get("signature")
    if not sig:
        raise ValueError("signature missing")

    body = dict(obj)
    body.pop("signature", None)
    payload = _canonical_dumps(body).encode("utf-8")

    from coherenceledger.crypto import b64decode, load_public_key_raw  # type: ignore

    pub = load_public_key_raw(b64decode(sig["public_key_b64"]))
    pub.verify(b64decode(sig["signature"]), payload)

    did = sig.get("did")
    if not isinstance(did, str) or not did:
        raise ValueError("signature.did missing")
    return did


def _weight_from_coherence(
    *,
    did: str,
    registry: Dict[str, float],
    scale: float,
    cap: float,
) -> float:
    score = float(registry.get(did, 0.0))
    if score < 0:
        score = 0.0
    w = score * scale
    if cap > 0:
        w = min(w, cap)
    return float(w)


def tally_ballots(
    *,
    manifest: Dict[str, Any],
    ballot_paths: List[Path],
    verify_ballot_signatures: bool = False,
    strict: bool = False,
    coherence_registry: Optional[Dict[str, float]] = None,
) -> Dict[str, Any]:
    """
    Returns tally dict. Does NOT write to disk.
    """
    manifest_id = manifest["manifest_id"]
    anon_mode = (manifest.get("anonymity", {}) or {}).get("mode", "open")

    weighting = manifest.get("weighting", {}) if isinstance(manifest.get("weighting"), dict) else {}
    w_mode = weighting.get("mode", "one_person_one_vote")
    w_params = weighting.get("params", {}) if isinstance(weighting.get("params"), dict) else {}

    # Coherence weighting parameters (guardrail enforces cap for public.deliberation in strict)
    scale = float(w_params.get("scale", 1.0)) if w_mode == "coherence" else 1.0
    cap = float(w_params.get("cap", 0.0)) if w_mode == "coherence" else 0.0
    if w_mode == "coherence" and strict and cap <= 0:
        raise ValueError("coherence weighting in strict mode requires weighting.params.cap > 0")

    # Weighted counts are floats; unweighted counts are ints.
    counts: Dict[str, int] = {}
    weighted_counts: Dict[str, float] = {}

    seen = 0
    valid = 0
    invalid = 0
    invalid_reasons: List[Dict[str, str]] = []
    type_counts: Dict[str, int] = {}

    # For coherence weighting, we require signer DID (open ballots only)
    registry = coherence_registry or {}

    for bp in ballot_paths:
        seen += 1
        try:
            b = load_ballot(bp)

            if b.get("manifest_id") != manifest_id:
                raise ValueError("manifest_id mismatch")

            signer_did: Optional[str] = None
            if verify_ballot_signatures or w_mode == "coherence":
                if anon_mode != "open" and strict:
                    raise ValueError(f"manifest anonymity '{anon_mode}' forbids DID ballot signatures in strict mode")
                signer_did = _verify_signed_payload(b)

            bt = (b.get("ballot") or {}).get("type")
            sel = (b.get("ballot") or {}).get("selection")
            if not bt or sel is None:
                raise ValueError("ballot.type or ballot.selection missing")

            type_counts[bt] = type_counts.get(bt, 0) + 1

            def add_choice(choice: str, weight: float) -> None:
                counts[choice] = counts.get(choice, 0) + 1
                weighted_counts[choice] = float(weighted_counts.get(choice, 0.0) + weight)

            # Determine weight per ballot
            if w_mode == "one_person_one_vote":
                weight = 1.0
            elif w_mode == "coherence":
                assert signer_did is not None
                weight = _weight_from_coherence(did=signer_did, registry=registry, scale=scale, cap=cap)
            elif w_mode == "quadratic":
                # placeholder: treat as 1 for now (future: quadratic credits)
                weight = 1.0
            elif w_mode == "token":
                # placeholder: treat as 1 for now (future: token balance)
                weight = 1.0
            else:
                raise ValueError(f"unsupported weighting mode: {w_mode}")

            if bt == "single_choice":
                choice = (sel or {}).get("choice")
                if not isinstance(choice, str) or not choice:
                    raise ValueError("single_choice requires selection.choice string")
                add_choice(choice, weight)

            elif bt == "approval":
                approve = (sel or {}).get("approve", [])
                if not isinstance(approve, list):
                    raise ValueError("approval requires selection.approve list")
                for c in approve:
                    if isinstance(c, str) and c:
                        add_choice(c, weight)

            elif bt == "ranked":
                rank = (sel or {}).get("rank", [])
                if not isinstance(rank, list) or not rank:
                    raise ValueError("ranked requires non-empty selection.rank list")
                first = rank[0]
                if isinstance(first, str) and first:
                    add_choice(first, weight)

            else:
                raise ValueError(f"unsupported ballot type: {bt}")

            valid += 1

        except Exception as e:
            invalid += 1
            invalid_reasons.append({"path": str(bp), "reason": str(e)})

    tally: Dict[str, Any] = {
        "version": 2,
        "schema_id": TALLY_SCHEMA_ID,
        "tally_id": str(uuid4()),
        "created_at": _utc_now_iso(),
        "manifest_id": manifest_id,
        "policy": {
            "manifest_anonymity_mode": anon_mode,
            "verify_ballot_signatures": bool(verify_ballot_signatures),
            "strict": bool(strict),
            "weighting_mode": w_mode,
            "weighting_params": w_params,
        },
        "ballots": {
            "seen": seen,
            "valid": valid,
            "invalid": invalid,
            "type_counts": type_counts,
        },
        "counts": counts,
    }

    # Always include weighted_counts for coherence mode; otherwise omit for stability
    if w_mode == "coherence":
        tally["weighted_counts"] = weighted_counts
        tally["coherence_registry_used"] = True

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
    coherence_registry_path: Optional[Path] = None,
) -> Path:
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

    # Load coherence registry if requested or env provided
    reg_path = coherence_registry_path
    if reg_path is None and os.getenv("COHERENCE_REGISTRY", ""):
        reg_path = Path(os.getenv("COHERENCE_REGISTRY", "")).expanduser()

    registry = load_coherence_registry(reg_path) if reg_path else {}

    tally = tally_ballots(
        manifest=manifest,
        ballot_paths=ballot_paths,
        verify_ballot_signatures=verify_ballot_signatures,
        strict=strict,
        coherence_registry=registry,
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
