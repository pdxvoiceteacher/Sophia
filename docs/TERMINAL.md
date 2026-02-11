# Sophia Terminal (Desktop)

## Overview
Sophia Terminal is a Tauri desktop shell that starts the local Standards Gateway and embeds the Run Viewer inside a desktop window.

## Development
1. From the repo root, install dependencies inside `desktop/`:
   ```bash
   cd desktop
   npm install
   ```
2. Run the desktop app in dev mode:
   ```bash
   npm run tauri dev
   ```

### Windows prerequisites
See `desktop/README_windows.md` for Windows-specific prerequisites (WebView2, Rust toolchain, Node, Python + venv).

### Windows operator entrypoint
Use the operator-friendly entrypoint script:
```powershell
.\scripts\windows\dev.ps1
```
Use `-LaunchFullStack` to start the full stack after smoke lanes.

### Linux prerequisites (CI/dev)
If you build the desktop app on Linux, install the Tauri dependencies:
```bash
sudo apt-get update
sudo apt-get install -y pkg-config libglib2.0-dev libgtk-3-dev libwebkit2gtk-4.1-dev libayatana-appindicator3-dev librsvg2-dev patchelf
```

### Icon generation (non-binary)
We keep a text-only SVG source at `desktop/src-tauri/icons/icon.svg`. PNG/ICO/ICNS files are generated at build time and ignored by git:
```bash
npm run icons
```
This runs the Tauri icon generator and writes files into `desktop/src-tauri/icons/` without committing binary assets (`icon.png`, `icon.ico`, `icon.icns`).

The app will automatically start the local Standards Gateway and open a window pointed at the embedded Run Viewer.

Configuration is stored in `~/.sophia/config.json` (no secrets stored yet).

Connector panel supports `OpenAIConnector`, `LocalLLMConnector`, and `GrokConnector` stubs with a test connection action. Connector test events are logged to `~/.sophia/connector_tel.jsonl` without secrets.

UCC remote read-only endpoints are exposed at `/ucc/index`, `/ucc/policies`, and `/ucc/schemas`.

## Repo policy (no binary assets)
Binary assets (png/ico/icns/zip/exe/dll) are not tracked in this repo. Generated build outputs should stay in ignored folders or be stored as release artifacts instead of committed to git.
If you must ship binaries, place them under `release_artifacts/` or attach them to GitHub Releases instead of committing them in-tree.

Licensing/tiering scaffold is documented in `docs/MARKET_TIERS.md` with config placeholders in `config/market_tiering.json` and `config/profits_allocation_ledger.json`.

### Binary preflight
Run the binary guard before opening a PR:
```powershell
.\scripts\windows\check_no_binaries.ps1
```

You can also run the combined Windows preflight (sanitizes scripts and runs tests):
```powershell
.\scripts\windows\sanitize_repo.ps1
```

For an all-in-one Windows workflow (bootstrap → sanitize → governance + shutdown smoke → full stack):
```powershell
.\scripts\windows\dev_up.ps1
```

### Git hooks (optional)
Install the pre-commit hook to block binary regressions locally:
```bash
python scripts/install_git_hooks.py
```

### Patch fallback workflow
If PR tooling rejects a change set, you can fall back to patch transfer:
```bash
git format-patch origin/main..HEAD -o /tmp/sophia-patches
git apply /tmp/sophia-patches/*.patch
```

### PR checklist (quick)
- Run `.\scripts\windows\sanitize_repo.ps1`
- Run `.\scripts\windows\preflight_pr.ps1`
- Confirm `git diff --cached --numstat` has no `-	-` lines (binary patches)
- Confirm no new files under `desktop/src-tauri/icons/*.png|*.ico|*.icns`

## Gateway startup
On launch, the desktop shell finds a free port (starting at 8001) and runs:
```
python -m uvicorn tools.sophia.standards_api:app --port <PORT>
```
The selected port is shown in the Connection Panel.


## Windows quick fixes (most common)
If PowerShell scripts fail with "not recognized" or no output, use these first:

```powershell
Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
```

```powershell
Set-Location C:\Users\pdxvo\Documents\Lean\Sophia
& .\scripts\windows\sanitize_repo.ps1
```

Run the Windows doctor helper for actionable checks and next commands:

```powershell
& .\scripts\windows\doctor.ps1
```

## Troubleshooting
- **Port already in use**: the app will increment the port until it finds a free slot (8001 → 8002 → …). If all attempts fail, restart the app after freeing a port.
- **Firewall prompts**: allow local loopback connections for `python` if prompted so the embedded viewer can reach `http://127.0.0.1:<PORT>/sophia/viewer`.
- **Gateway reports Down**: verify Python + `uvicorn` are available in your environment and that the standards API starts from the repo root.


## Frontmatter lock defaults

Local/research workflows default to non-blocking frontmatter checks via environment defaults:
`SOPHIA_FRONTMATTER_PROFILE=research` and `SOPHIA_FRONTMATTER_MODE=warn`.
CI remains strict by explicitly invoking publication enforcement (`--profile publication --mode enforce`) in the smoke workflow.
