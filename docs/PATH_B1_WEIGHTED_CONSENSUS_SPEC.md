# Path B1 Weighted Consensus Math Spec

## Scope
Path B1 is a simulation-only mathematical extension for weighted peer attestations.

- No governance shift.
- No central dominance relaxation.
- No `consensus_summary_v1` mutation.
- No witness-only freeze regression.

## Definitions
For peer attestations with weights `w_i >= 0` and statuses in `{pass, fail, pending}`:

- `W_total = Σ(w_i)`
- `P = Σ(w_i where status == pass)`
- `F = Σ(w_i where status == fail)`
- `N = Σ(w_i where status == pending)`

Central attestation is unweighted and remains a required dominance signal.

## Path B1 convergence/divergence rules
Given profile in `{reproducible_audit, full_relay}`:

1. **Central dominance is mandatory**: `central_pass == true` is required for convergence.
2. Weighted pass threshold: `P + central_pass >= min_weighted_pass` (plus pending treatment only if policy allows pending-to-satisfy).
3. Fail threshold behavior:
   - if `block_on_any_fail == true` and any weighted fail is present (`F + central_fail > 0`), consensus is divergent.
   - else if `max_weighted_fail` is configured and `F + central_fail > max_weighted_fail`, consensus is divergent.
4. Otherwise, if weighted pass and count thresholds are met, consensus is convergent; else insufficient.

## Invariants
- **Normalization rule**: all simulated weights are finite and non-negative.
- **Weight source rule**: Path B1 weights are simulation-derived only (`uniform`, `linear`, `adversarial`).
- **Central dominance preservation**: no weighted peer distribution can produce convergent consensus when central attestation is non-pass.
- **Witness isolation**: witness-only ignores weighted simulation semantics and continues v1 emission.

## Weight modes (simulation only)
- `uniform`: all peers weight `1.0`, status `pass` by default.
- `linear`: peer `i` has weight `i+1`, status `pass` by default.
- `adversarial`: high-weight minority fail and low-weight majority pass for drift testing.

## Non-goals (deferred)
- Real weight registries.
- Dynamic trust or policy-shift semantics.
- Consumer-side enforcement changes.
