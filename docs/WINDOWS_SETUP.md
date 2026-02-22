# Windows Setup (Python Tooling)

This repository root is not a standalone Python package (`pip install -e .` is not supported), but it now includes a root convenience requirements file for telemetry/python setup.

Use either of the following bootstrap flows in PowerShell:

```powershell
python -m pip install --upgrade pip
python -m pip install -r requirements.txt
```

Or use the helper script:

```powershell
./scripts/bootstrap_telemetry.ps1
./scripts/bootstrap.ps1
```

Optional developer extras:

```powershell
python -m pip install -r requirements-dev.txt
```

## CLI note: `run_epoch_real.py` vs `run_wrapper.py`

`tools/telemetry/run_epoch_real.py` orchestrates scenario + pipeline execution.

- `--quick`, `--perturbations`, and `--simulate-peers` are pass-through overrides for `tools/telemetry/run_wrapper.py` pipeline settings.

## Python version guidance

Recommended on Windows: Python 3.12 or 3.13.

Newer interpreter versions can lag on binary wheel availability for some dependencies.


## Editable package set

For full telemetry/dev tooling, install editable subpackages:

```powershell
python -m pip install -e ./python -e ./ucc -e ./sophia-core -e ./tools/coherenceledger_bootstrap
```


## Consensus note

`consensus_summary.json` used to remain `insufficient` in single-node local runs because no peer attestations were present.

Current behavior: `run_wrapper` emits a local central attestation (`attestations.json`) with explicit status; policy gate satisfaction requires a convergent consensus outcome backed by a central `pass`.


## CLI smoke checks

Run both invocation forms to catch import-path regressions on Windows:

```powershell
python tools/telemetry/run_wrapper.py -h
python -m tools.telemetry.run_wrapper -h
```


## Search tooling note

If `rg` (ripgrep) is not installed on Windows, use PowerShell `Select-String` as a fallback:

```powershell
Get-ChildItem -Recurse -File | Select-String -Pattern "run_wrapper"
```


## One-shot launcher

Use `scripts/Run-Sophia-Telemetry.ps1` for venv setup, focused tests, and a telemetry run with artifact printout.
