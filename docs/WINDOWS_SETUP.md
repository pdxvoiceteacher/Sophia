# Windows Setup (Python Tooling)

This repository root is not a standalone Python package (no root `pyproject.toml` / `requirements.txt`).

Use the following bootstrap flow in PowerShell:

```powershell
python -m pip install --upgrade pip
python -m pip install -r python/tools/requirements-telemetry.txt
python -m pip install -e python -e ucc -e sophia-core
```

Optional developer extras:

```powershell
python -m pip install -r requirements-dev.txt
```

## CLI note: `run_epoch_real.py` vs `run_wrapper.py`

`tools/telemetry/run_epoch_real.py` orchestrates scenario + pipeline execution.

- `--quick` and `--perturbations` are pass-through overrides for the underlying `tools/telemetry/run_wrapper.py` pipeline settings.

## Python version guidance

Recommended on Windows: Python 3.12 or 3.13.

Newer interpreter versions can lag on binary wheel availability for some dependencies.
