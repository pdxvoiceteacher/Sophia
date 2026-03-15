# Triadic Brain First Experiment (LAN-01)

## Constrained Discovery in a Synthetic Coherence Field

## 1. Title

LAN-01: Constrained Discovery in a Synthetic Coherence Field

## 2. Objective

Determine whether the Triadic Brain can:

- detect discovery corridors in a bounded synthetic field
- generate candidate hypotheses from those corridors
- test those hypotheses against a known ground-truth simulator
- elevate successful hypotheses into a small theory graph
- do so while preserving telemetry integrity, auditability, and advisory-only semantics

## 3. Why this experiment first

This is the correct first experiment because it avoids three early failure modes:

- ambiguous real-world data
- over-claiming discovery
- unverifiable success criteria

Instead, LAN-01 uses a synthetic domain with known hidden structure.

That means we can ask a clean question:

Can the Triadic Brain recover a structure that we already know is present but that it has not been explicitly handed as a hypothesis?

## 4. Hypothesis under test

### Primary hypothesis

The Triadic Brain can detect coherent gradients in a bounded synthetic field and generate hypotheses that improve prediction relative to a random or null baseline.

### Secondary hypothesis

The full pipeline can run end-to-end without violating conservation checks, governance constraints, or audit boundaries.

## 5. Domain choice

Use a synthetic two-basin field with one hidden bridge.

Why this domain:

- simple enough to debug
- rich enough to generate real corridors
- supports clear success/failure criteria
- psychologically safe and low-stakes

## 6. Synthetic field definition

Define a lattice over nodes \(x_i\).

Each node has values:

- \(E_i\)
- \(T_i\)
- \(\Psi_i = E_i T_i\)
- \(\Delta S_i\)
- \(\Lambda_i\)

Construct two high-coherence basins separated by a noisy region, with a narrow hidden path of slightly elevated coherence joining them.

In plain language:

`left terrace --- weak hidden bridge --- right terrace`

The bridge should be hard enough that naive thresholding may miss it, but coherent gradient transport should detect it.

## 7. Ground truth

The hidden bridge is the ground truth structure.

The Triadic Brain is not told:

- where the bridge is
- how many bridge nodes exist
- which exact relation defines it

It receives only the field values and topology.

## 8. Null baseline

Compare the Triadic Brain against two simple baselines:

### Baseline A: random exploration

Select random nodes as candidate corridors.

### Baseline B: static thresholding

Flag any node with \(\Psi > \tau\) and attempt to connect them greedily.

Success means the Triadic Brain outperforms both on bridge recovery and predictive coherence gain.

## 9. Experimental pipeline

The run sequence is:

```text
synthetic field generation
→ telemetry ingestion
→ corridor detection
→ hypothesis generation
→ hypothesis testing
→ theory formation
→ civilizational + conservation checks
→ atlas visualization
→ midi sonification
```

## 10. Input artifact

Create:

- `bridge/lan_01_synthetic_field.json`

Minimum fields:

- node ids
- adjacency list
- E
- T
- DeltaS
- Lambda
- Es
- optional hidden_truth label (kept separate from model input)

Important: keep the truth labels out of the model input artifact used during discovery.

## 11. Corridor task

The corridor detector should output:

- `bridge/lan_01_corridor_map.json`

Metrics:

- number of candidate corridor nodes
- overlap with hidden bridge
- false positive rate
- mean gradient magnitude on true bridge nodes

## 12. Hypothesis generation task

The generator should propose hypotheses of the form:

If nodes with moderate \(\Psi\) and low \(\Delta S\) form a connected gradient path, then they may represent a bridge between terraces.

Represent as structured objects, not free text only.

Example:

```json
{
  "hypothesis_type": "bridge_candidate",
  "origin_nodes": [12, 13, 14],
  "confidence": 0.61,
  "rule": "connected_moderate_psi_low_entropy_path"
}
```

## 13. Hypothesis testing task

Test each candidate against held-out synthetic simulations.

Measures:

- path continuity
- coherence gain
- predictive recovery of hidden bridge nodes
- entropy penalty
- stability under perturbation

A valid hypothesis should improve bridge recovery relative to null baselines.

## 14. Theory formation task

Merge successful hypotheses into a small theory graph.

Expected theory type:

- latent coherence bridge theory

The theory graph should remain small and interpretable for LAN-01.

No giant graph. No sprawling theory explosion.

## 15. Primary evaluation metrics

Use these as the main outcome metrics.

### Discovery metrics

- corridor precision
- corridor recall
- bridge recovery score
- hypothesis validity rate

### Coherence metrics

- mean \(\Delta \Psi\) gain from validated hypotheses
- free-energy reduction if available
- renormalization persistence across scales

### Safety/governance metrics

- zero executive actions
- zero schema failures
- zero unrecovered NaN/Inf events
- no conservation violation beyond threshold

## 16. Success criteria

LAN-01 is a success if all of the following hold:

- corridor detector identifies at least part of the hidden bridge
- hypothesis testing outperforms both baselines
- at least one theory candidate is formed
- conservation checks remain within tolerance
- all outputs remain advisory-only
- Atlas renders the resulting artifacts
- MIDI artifact is produced for the run

## 17. Failure criteria

LAN-01 is a failure if any of the following occur:

- no bridge structure recovered at all
- hypotheses do not outperform random baseline
- conservation witness violated beyond threshold
- runtime requires disabling audit or governance
- artifacts fail schema validation
- theory formation collapses into noise or empty output

Failure is acceptable scientifically.
What matters is that it is diagnostic and interpretable.

## 18. Psychological safety and ethics constraints

This experiment must remain:

- non-clinical
- non-diagnostic about persons
- non-authoritative
- fully reversible
- sandboxed

No human psychological or social profiling data should be used.

No claims about consciousness, superiority, or governance authority should be inferred from success.

The experiment tests a bounded discovery architecture, not metaphysical conclusions.

## 19. Reproducibility requirements

Set:

- fixed random seed
- fixed swarm size
- fixed lattice topology
- fixed dt
- fixed baseline comparison rules

Log:

- kernel hash
- state hash before/after
- operator set
- random seed
- run id

## 20. LAN-01 swarm configuration

For first run:

- `agents = 4`
- `max_steps = 25`
- `dt = 0.1`
- `seed = 101`

This is intentionally small.

Do not start with a big swarm.

## 21. Artifacts expected

By the end of a successful run, expect these artifacts:

- `bridge/lan_01_corridor_map.json`
- `bridge/lan_01_hypothesis_candidates.json`
- `bridge/lan_01_hypothesis_tests.json`
- `bridge/lan_01_theory_graph.json`
- `bridge/lan_01_conservation_witness.json`
- `bridge/lan_01_civilizational_state.json`
- `bridge/audio/lan_01_coherence.mid`

And Atlas overlays for:

- corridor vectors
- theory graph
- renormalization flow
- coherence audio trigger

## 22. Recommended interpretation discipline

Interpret results in three layers:

### Layer 1: engineering

Did the pipeline run?

### Layer 2: scientific

Did the system recover hidden structure better than baseline?

### Layer 3: theoretical

Do the results support continued development of the coherence-field framing?

Do not jump directly from Layer 1 to grand theoretical claims.

## 23. Minimal report template

After LAN-01, write a one-page run report with:

- run id
- seed
- corridor precision/recall
- best hypothesis
- baseline comparison
- conservation status
- notable audit findings
- whether LAN-02 is justified

## 24. Recommended next experiments if LAN-01 succeeds

### LAN-02

Multiple hidden bridges, one false bridge.

### LAN-03

Competing terraces with asymmetric entropy.

### LAN-04

Multi-agent swarm coordination test.

### LAN-05

Audio-assisted pattern interpretation comparison.

## 25. One-line summary

LAN-01 tests whether the Triadic Brain can recover a hidden coherence bridge inside a bounded synthetic field while preserving full telemetry, auditability, and advisory-only governance.
