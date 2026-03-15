# Triadic Brain LAN Test Protocol v1

*(Local Area Network Experimental Deployment)*

## 1. Purpose

The LAN Test Protocol defines the controlled experimental environment required to run the Triadic Brain system safely during early development.

The protocol ensures:

- reproducibility
- governance compliance
- conservation law stability
- auditability
- rollback capability

The Triadic Brain is treated as a scientific instrument, not a consumer application.

## 2. Experimental Architecture

The LAN test environment consists of three cooperating codex systems.

- **CoherenceLattice** → simulation kernel
- **Sophia** → governance + audit
- **Atlas** → visualization + control

Network layout:

```text
[Simulation Node]
    CoherenceLattice Kernel
          ↓
[Audit Node]
        Sophia
          ↓
[Visualization Node]
          Atlas
```

All communication occurs inside a trusted LAN sandbox.

No internet exposure during protocol runs.

## 3. Test Environment Requirements

Minimum hardware:

- CPU: 8 cores
- RAM: 16 GB
- Disk: 10 GB free
- GPU: optional

Software stack:

- Python 3.11+
- NodeJS 18+
- pytest
- numpy

Repository state:

- CoherenceLattice: master
- Sophia: master
- uvlm-publications: master

## 4. Initial System Validation

Before running any simulation the following checks must pass.

### Kernel Integrity

Run:

```bash
pytest python/tests
```

Expected result:

```text
ALL TESTS PASS
```

### Schema Validation

Validate all artifacts under:

- `schema/`
- `bridge/`
- `telemetry/`

Artifacts must include:

- `coherence_cascade_map.json`
- `river_formation_map.json`
- `corridor_map.json`
- `civilizational_coherence_map.json`

### Telemetry Initialization

The system must create:

- `bridge/tel/tel_events.jsonl`

First entry:

- `event: step_start`
- `semanticMode: non-executive`

## 5. Simulation Control Flow

A complete LAN run follows this pipeline.

```text
telemetry ingestion
      ↓
corridor detection
      ↓
multi-agent discovery swarm
      ↓
hypothesis generation
      ↓
hypothesis testing
      ↓
theory formation
      ↓
paradigm shift engine
      ↓
civilizational coherence monitor
      ↓
renormalization flow
      ↓
conservation law checks
      ↓
Atlas visualization
      ↓
MIDI coherence output
```

## 6. Simulation Launch

Simulation must be started from the Atlas dashboard.

Dashboard controls:

- Start Simulation
- Pause Simulation
- Stop Simulation

Launch sequence:

- `atlas/index.html`

Click:

- Start Simulation

This triggers:

- `kernel.run_simulation()`

## 7. Swarm Size Limits

During LAN testing, the discovery swarm must remain bounded.

Default configuration:

- `agents = 8`
- `max_agents = 16`

Reason:

Prevent runaway exploration or resource exhaustion.

## 8. Telemetry Requirements

Every kernel step must emit telemetry.

Minimum required event:

- `kernel_step_metrics_v3`

Fields required:

- `phi_total`
- `phi_drift`
- `corridor_mass_balance_residual`
- `scale_flux_estimates`

Telemetry location:

- `bridge/tel/tel_events.jsonl`

## 9. Conservation Law Monitoring

The following invariants must be evaluated each step.

### Epistemic Flux Conservation

\[
\Phi = \Psi + P + \Delta S
\]

Check:

- `phi_drift < tolerance`

Tolerance:

- `1e-4`

### Corridor Mass Conservation

Verify:

\[
\sum \text{corridor\_density\_before} = \sum \text{corridor\_density\_after} + \text{sources} - \text{sinks}
\]

Residual threshold:

- `1e-5`

Violation triggers:

- `exception_tag: CORRIDOR_MASS_RESIDUAL_HIGH`
- `severity: warn`

## 10. Cascade / Turbulence Monitoring

The system must compute scale flux across levels.

Expected structure:

- corridor
- river
- terrace

Flux should remain approximately stable across the inertial range.

If plateau fit fails:

- `exception_tag: TURBULENCE_FIT_LOW_R2`
- `severity: watch`

## 11. Civilizational Coherence Monitor

Compute scalar:

\[
S_{civ} = \frac{\Psi \cdot P \cdot T \cdot M \cdot G}{E_t + C}
\]

Regime classification:

- `S_civ > 0.8` → healthy discovery
- `0.5–0.8` → stable terrace
- `0.2–0.5` → orthodoxy drift
- `<0.2` → fragmentation risk

Artifact:

- `bridge/civilizational_coherence_map.json`

## 12. Audio Output Validation

Each simulation cycle generates a MIDI artifact.

Location:

- `bridge/audio/coherence_music.mid`

Mapping:

- `Ψ` → pitch
- `ΔS` → modulation
- `Λ` → percussion density

This allows researchers to hear coherence evolution.

## 13. Atlas Visualization Checks

Atlas must render:

- Corridor vectors
- River flows
- Terrace regions
- Paradigm shifts
- Civilizational coherence
- Renormalization flow

Overlay toggles must be idempotent and reset-safe.

## 14. Rollback Protocol

If any of the following occurs:

- conservation violation
- NaN / Inf values
- governance projection failure

The engine must:

- pause simulation
- emit telemetry error
- restore previous `state_hash`

No uncontrolled continuation allowed.

## 15. Human Control Override

The LAN dashboard must expose:

- Abort Simulation
- Downgrade to Advisory
- Require Human Review

These correspond to:

- `RuntimeControlState`

in the kernel.

## 16. Run Logging

Every simulation run must record:

- `kernel_hash`
- `state_hash_before`
- `state_hash_after`
- operator list
- conservation witnesses
- audit findings

Location:

- `bridge/logs/run_<timestamp>.json`

## 17. Reproducibility Mode

The system must support deterministic replay.

Configuration:

- `random_seed = fixed`
- `agent_count = fixed`
- `dt = fixed`

Replay command:

- `kernel.replay_run(run_id)`

## 18. Termination Conditions

Simulation stops when one of the following occurs:

- `time_limit` reached
- `agent_count` exceeded
- conservation failure
- civilizational rupture detected
- manual abort

## 19. Safety Guarantee

All outputs produced by the system must remain:

- `semanticMode = non-executive`
- `advisory_only = true`

The Triadic Brain never performs executive actions.

## 20. Expected First LAN Outcome

A successful run should produce:

- coherence corridor map
- river formation map
- terrace stabilization regions
- hypothesis generation artifacts
- civilizational coherence map
- coherence audio output

The goal is not immediate scientific discovery.

The goal is verifying that the discovery pipeline operates coherently and reproducibly.

## Final Note

This protocol ensures the Triadic Brain behaves like a scientific instrument rather than an uncontrolled generative system.

Which is exactly what makes the architecture publishable and trustworthy.
