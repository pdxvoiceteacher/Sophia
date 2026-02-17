# Sophia P2P Network Policy (Sonya Nodes)

This document defines current P2P policy behavior and near-term milestones for cryptographic hardening.

## Safety language and guarantees

- **AI-private by default** means software-level secure defaults plus cryptographic separation for network/shared artifacts.
- It does **not** imply metaphysical secrecy on user-owned devices.
- Full sharing is always policy-gated and auditable.

## Prime directive invariant

Vault never leaks by default.

- If `profile != full_relay`, any scope containing `vault/full` is denied by runtime guardrails.
- This is implemented as code-path enforcement (not documentation-only).

## Profile model

### `witness_only` (default)
- Goal: safest mode.
- Intended scopes: `hashes/*`, `metrics/*`, `attestations/*`.
- Forbid vault/evidence relay scopes.

### `reproducible_audit`
- Goal: reproducibility without vault replication.
- Intended scopes: all witness scopes plus optional `tel/*` and `evidence/*`.
- Vault scopes (`vault/*`) are forbidden.

### `full_relay`
- Goal: explicit, human-authorized relay mode.
- Must include non-empty peer set and full-relay-tier peers.
- May include `evidence/*`.
- `vault/*` remains AI-only encrypted replication and is represented separately via relay toggles.

## Internal relay semantics (disambiguation)

User-facing term remains **Full Relay**. Internally this is decomposed into orthogonal toggles:

- `relay_toggles.evidence_full_relay`: human-authorized evidence bundle relay.
- `relay_toggles.vault_relay`: AI-only encrypted vault replication.

This prevents accidental interpretation that “full relay” means public raw-content sharing.

## Share scope allowlist (current)

All policy scopes must be from this allowlist:

- `hashes/*`
- `metrics/*`
- `attestations/*`
- `tel/*`
- `evidence/*`
- `vault/*`

## Signature canonicalization rule (effective now)

All signatures MUST be computed over either:

1. Canonical JSON form (sorted keys + stable list ordering), **or**
2. A stable hash of that canonical form.

Current attestation payloads include `signed_bytes_hash` as this stable preimage hash.

## Milestone 1 — cryptographically real peer attestations

**Goal:** Ed25519 signatures verifiable in audit and viewer.

### Definition of done
- Persistent node Ed25519 keypair generation/loading (OS keystore preferred; encrypted file fallback).
- Replace demo signature values with real Ed25519 signatures.
- Keep `signed_bytes_hash` over canonical signing preimage.
- Add verification in audit tooling and surface verify status in viewer (`✅/❌`).
- Schema fields pinned:
  - `signature_alg` enum includes `ed25519`
  - `signature_format = base64`
  - `pubkey_format` explicit (`base64` or `hex`)
- Tests:
  - Golden attestation verifies.
  - Tampered attestation fails.

## Milestone 2 — formal Vault vs Evidence policy boundaries

**Goal:** prevent vault content from leaking into evidence outputs.

### Definition of done
- Introduce `vault_bundle_v1` encrypted-only artifact schema.
- Enforce profile/scope rules:
  - `witness_only`: cannot include `vault/*`
  - `reproducible_audit`: can include `evidence/*`, cannot include `vault/*`
  - `full_relay`: can include `evidence/*`; `vault/*` remains AI-only
- Add desktop UI allowlist validation and peer selector dropdown.

## Future work: Sophia Context Integrity Module (Evidence layer)

For domain-shift trust resilience, future artifacts should include a Context Integrity module with:

- `active_scope`
- `latent_context_clusters` (hashes only)
- consent events when scope changes

This is intentionally scoped for a follow-on milestone.


## Normative wire-format alignment (v0.1)

- Canonicalization: RFC 8785 JCS canonical JSON for signed/hashes and AAD structures.
- Binary encoding in JSON: **base64url without padding**.
- Signed artifacts are wrapped in `signed_message_v1` (`payload_schema`, `payload`, `signer`, `signature_alg`, `signature`).
- Encrypted transport uses `sealed_envelope_v1` with multi-recipient wraps.

