# Echo Framework Benchmarks

Echo benchmarks are replay tests that run the same prompt across repeated epochs to check for deterministic behavior and detect **Echo anomalies** (unexpected divergences).

## Windows setup (example)

```powershell
cd C:\DeltaSYN\Sophia
py -3 -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install -U pip setuptools wheel
pip install -r .\python\tools\requirements-telemetry.txt
pip install -e .\python
pip install -e .\ucc
pip install pytest hypothesis httpx numpy rpds
```

`hypothesis`, `httpx`, `numpy`, `rpds`, and `coherenceledger` are optional but recommended if you want to silence import-time warnings/errors during broader test collection.

## Sanity checks

```powershell
python tools\telemetry\run_wrapper.py -h
python -m tools.telemetry.run_wrapper -h
pytest -q tests/test_run_wrapper_invocation.py
```

## Echo benchmark runner

CLI:

- `python tools/telemetry/echo_test_runner.py --prompt "..." --epochs 5 --output-dir ./echo_results`
- `python -m tools.telemetry.echo_test_runner --prompt "..." --epochs 5 --output-dir ./echo_results`

PowerShell multiline example:

```powershell
python tools/telemetry/echo_test_runner.py `
    --prompt "Example Task" `
    --epochs 5 `
    --output-dir .\echo_results
```

The runner writes `epoch_*/` subdirectories, per-epoch telemetry artifacts, and an `echo_summary.json` rollup.

## Interpreting results

- **Deterministic** means matching final output signature and ΔSyn metrics (within a small tolerance).
- **Echo anomalies** indicate differences not explained by expected randomness and should be treated as potential nondeterminism bugs to investigate (not evidence of agency).
