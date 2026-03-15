# Triadic Brain Module Dependency Graph

Each kernel module depends only on lower layers.

This ensures safe incremental evolution.

## Dependency DAG

```text
telemetry
│
├── kernel_fields
│
├── corridor_detector
│   └── coherence_pde
│
├── river_formation
│   └── corridor_detector
│
├── terrace_formation
│   └── river_formation
│
├── hypothesis_generator
│   └── corridor_detector
│
├── hypothesis_testing
│   └── hypothesis_generator
│
├── theory_formation
│   └── hypothesis_testing
│
├── paradigm_shift_engine
│   └── theory_formation
│
├── civilizational_monitor
│   └── theory_formation
│
└── planetary_intelligence
    └── civilizational_monitor
```

## Three Codex Responsibilities

### CoherenceLattice Codex

Mathematics + PDE kernels.

```text
coherence/kernel/
    corridor_detector.py
    river_formation.py
    terrace_formation.py
    hypothesis_generator.py
    hypothesis_testing.py
    theory_formation.py
    paradigm_shift_engine.py
    civilizational_monitor.py
    global_coherence_solver.py
```

### Sophia Codex

Auditing + safety + governance.

```text
sophia/
    audit_corridor.py
    audit_river.py
    audit_terrace.py
    audit_paradigm_shift.py
    audit_civilizational_state.py
```

### Atlas Publisher Codex

Visualization layer.

```text
atlas/js/
    corridor_overlay.js
    river_overlay.js
    terrace_overlay.js
    paradigm_shift_overlay.js
    civilizational_overlay.js
```
