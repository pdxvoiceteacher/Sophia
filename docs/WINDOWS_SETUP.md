# Windows Setup (Telemetry / Secure Swarm)

This repo root is **not** a standalone installable package. Do **not** run `pip install -r requirements.txt` at repo root. Use `python/tools/requirements-telemetry.txt` plus editable monorepo subpackages.

## One-command bootstrap (PowerShell)

From repo root:

```powershell
./scripts/windows/bootstrap_one_shot.ps1
```

This script creates `.venv`, installs telemetry dependencies, installs editable packages (`.\python`, `.\ucc`), runs focused tests, and prints run examples.

## Manual bootstrap (equivalent)

```powershell
python -m venv .venv
.\.venv\Scripts\python.exe -m pip install --upgrade pip
.\.venv\Scripts\python.exe -m pip install -r .\python\tools\requirements-telemetry.txt
.\.venv\Scripts\python.exe -m pip install -e .\python
.\.venv\Scripts\python.exe -m pip install -e .\ucc
```

## Invocation regression checks (both must work)

Both invocation styles are supported. Script-path invocation is stabilized by an in-script `sys.path` bootstrap.

```powershell
python tools\telemetry\run_wrapper.py -h
python -m tools.telemetry.run_wrapper -h
python tools\telemetry\run_epoch_real.py -h
python -m tools.telemetry.run_epoch_real -h
```

## Focused Windows test suite

```powershell
python -m pytest -q tests/test_run_wrapper_evidence_paths.py tests/test_secure_swarm_crypto.py tests/test_secure_swarm_schemas.py tests/test_epoch_real_runner.py tests/test_run_wrapper_invocation.py
```

## Tiny smoke run

```powershell
python tools\telemetry\run_wrapper.py --out out\windows_smoke --quick --perturbations 1 --simulate-peers 2 --simulate-peer-weight-mode uniform
```

## Determinism / governance contract

- Secure Swarm governance/consensus semantics are unchanged.
- Path A freeze invariants remain required.
- Cognition artifacts remain out-of-band and should not alter `evidence_bundle.json` artifact membership.
