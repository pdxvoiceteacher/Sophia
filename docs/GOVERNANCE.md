# Governance Artifacts & Policy Flow

This document captures the governance artifacts used in Sophia runs and the policy resolution step
that turns an MVSS policy into concrete quorum/pass thresholds for a specific election instance.

## Governance Artifacts

Governance artifacts are stored alongside run outputs and include the following JSON files:

- **Election** (`election.json`): Describes the electorate and ballots, including structured
  multilingual ballot text for accessibility and localization.
- **Tally** (`tally.json`): Aggregates ballot outcomes and records quorum/pass thresholds.
- **Decision** (`decision.json`): Records the final decision, proof bundle, and ledger anchor.
- **Warrant** (`warrant.json`): Grants scoped authorization for actions derived from the decision.

All governance artifacts must include:

- `stakeholder_scope` to declare the electorate boundary.
- `mvss_policy_ref` to tie the election to its governing MVSS policy.
- `registry_federation` placeholders to keep federation-ready metadata aligned with future scaling
  (`{ "enabled": false, "peers": [] }` until federation is enabled).

## Policy Resolution Step

Before minting a tally or decision, resolve the MVSS policy against a registry snapshot so each
election has explicit thresholds.

Run the policy resolver:

```
python tools/sophia/resolve_mvss_policy.py \
  --registry path/to/registry_snapshot.json \
  --policy path/to/mvss_policy.json \
  --stakeholder-scope global \
  --out out/policy_resolution.json
```

The output artifact captures quorum and pass thresholds computed for the election instance. Persist
the output alongside the election bundle.

## Accessibility & Language Justice Commitments

Sophia governance is designed to meet international accessibility expectations:

- **Multilingual ballot text** is required, with structured translations supplied per ballot.
- **Plain language mode** must remain available in the UI to simplify complex governance language.
- **Evidence layer mode** must remain available in the UI for auditing and traceability.
- **Step-by-step mode** ("one thing at a time") must remain available in the UI for focus and
  neurodiversity support.

These commitments apply across governance artifacts and user interfaces to ensure language justice,
inclusive participation, and consistent auditability.
