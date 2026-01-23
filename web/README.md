# Sophia Run Viewer (MVP)

This is a static, offline-friendly UI for inspecting Sophia run artifacts.

## Run locally

From the repo root:

```bash
python -m http.server --directory web 8000
```

Then open <http://localhost:8000>.

## What it loads

Required files (from a run folder or ZIP bundle):

- `telemetry.json`
- `sophia_audit.json`
- `sophia_plan.json`

Optional files (if present, the UI will surface them):

- `audit_bundle.json`
- `tel.json`
- `tel_events.jsonl`
- `ucc_tel_events.jsonl`

## How to use

1. Drag a ZIP bundle into the drop zone **or** select a run folder.
2. Pick the run directory from the dropdown.
3. Explore Summary, Dashboard, Evidence, and JSON Viewer tabs.

The UI is designed to degrade gracefully if optional files are missing.
