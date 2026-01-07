# Telemetry Taxonomy (Engine Modules)

Purpose: prevent drift and accidental undo by declaring, per engine/module:

1) **Artifacts it writes** (files in `run_dir/artifacts/` and/or run-level files).
2) **Metrics keys it owns** (schema authority).
3) **Metrics keys it produces** (it may populate keys owned by another module).
4) **Schema fragments** it contributes (JSON Schema snippets that can be assembled into a full schema).

## Conventions

- `registry.json` lists all engine modules and their file paths.
- Each module file is `modules/<engine_id>.module.json`.
- `metrics.owns[]` is a list of JSON Pointers to the *root schema* location owned by this engine.
  - Example: `/properties/tree_of_life`
- `metrics.produces[]` is a list of JSON Pointers that the engine may populate.
- `metrics.schema_fragments[]` is a list of `{ "json_pointer": "...", "schema": { ... } }`.
  - Only include fragments for keys you own (recommended), but you can document produced keys too.

## Why both “owns” and “produces”?
- “owns” = canonical definition (controls drift + semantic authority).
- “produces” = implementation detail (who populates values).

## Validator
Run:
  python python/tools/validate_taxonomy.py

It checks:
- registry/module file existence
- engine_id matches filename entry
- no duplicate ownership pointers across modules
- no duplicate artifact names across modules (best practice guardrail)

Next step (optional): a schema assembler can merge fragments into `telemetry_v1.schema.json`.