# Development Environment Notes

## Tauri/Linux build dependencies

Desktop Rust/Tauri checks on Linux require GTK/WebKit system packages (including `pkg-config` and `libglib2.0-dev`).

In this repo CI, desktop build lanes are gated and only run when explicitly requested (`workflow_dispatch` + desktop build input), while Python/Node smoke lanes run by default.

If you need to run desktop checks locally on Debian/Ubuntu:

```bash
sudo apt-get update
sudo apt-get install -y pkg-config libglib2.0-dev libgtk-3-dev libwebkit2gtk-4.1-dev libayatana-appindicator3-dev librsvg2-dev patchelf
```


## Telemetry runner import-time behavior

`tools/telemetry/run_wrapper.py` intentionally performs a small amount of argv/env pre-parse at module import time to support historical script entrypoints (`--out`/`--outdir`, `--emit-tel`, `--emit-tel-events`).

Current stance:
- Keep import-time side effects minimal and deterministic (idempotent file touch, no network/process launch).
- Keep all run orchestration and heavy work inside `main()` / post-run blocks.
- Preserve importability for tests; regressions are covered by `tests/test_run_wrapper_evidence_paths.py` (flag persistence + env/argv output directory behavior).

If this contract changes in future refactors, move pre-parse behavior behind explicit functions and update tests accordingly.
