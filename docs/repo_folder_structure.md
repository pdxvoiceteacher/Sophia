# Repo Folder Structure (All Three Codexes)

This layout keeps the kernel, governance, and visualization planes cleanly separated while preserving the pipeline already implemented.

## Sophia Codex

_(governance + audit plane)_

```text
Sophia/
│
├── python/
│   └── src/
│       └── sophia/
│
│           ├── audits/
│           │   ├── audit_conservation.py
│           │   ├── audit_corridor_formation.py
│           │   ├── audit_river_formation.py
│           │   ├── audit_terrace_state.py
│           │   ├── audit_global_coherence_field.py
│           │   ├── audit_coherence_gradient_map.py
│           │   └── audit_civilizational_coherence.py
│
│           ├── guidance/
│           │   ├── ai_guidance_builder.py
│           │   └── advisory_rules.py
│
│           ├── telemetry/
│           │   ├── tel_reader.py
│           │   └── tel_validator.py
│
│           └── schemas/
│               ├── audit.schema.json
│               └── advisory.schema.json
│
└── tests/
    ├── test_audit_conservation.py
    ├── test_audit_river.py
    ├── test_audit_terrace.py
    └── test_audit_civilizational.py
```
