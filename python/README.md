# coherence-sim

This is a lightweight Python simulation harness that mirrors the Lean model:
- τ0..τ3 thresholds
- Ψ = E*T
- classify + adjacency graph
- ΔSyn-based stepPsi and stepET (capped/clamped)

## Experiments

Install local sources and experiment dependencies:

```bash
pip install -e "python[experiments]"
```

Then run experiment scripts from the repo root, for example:

```bash
python python/experiments/konomi_smoke/run_smoke.py --quick
python python/experiments/coherence_music/demo_bhairav.py
```

## Sophia advisory audits and guidance

Two Sophia utilities are available under `python/src/sophia`:

- `sophia.audit_discovery_corridor_state`
  - reads `bridge/discovery_corridor_map.json`
  - writes `discovery_corridor_audit.json`
  - emits advisory-only findings (`severity: info|warn`, `advisory: watch|docket`) and includes `semanticMode: "non-executive"`
- `sophia.build_ai_guidance`
  - reads `cascade_audit.json` and `discovery_corridor_audit.json`
  - writes `ai_guidance.json`
  - emits bounded guidance weights in `[0,1]`

Example CLI usage:

```bash
PYTHONPATH=python/src python -m sophia.audit_discovery_corridor_state --bridge-root . --output-file out/discovery_corridor_audit.json
PYTHONPATH=python/src python -m sophia.build_ai_guidance --bridge-root . --output-file out/ai_guidance.json
```
