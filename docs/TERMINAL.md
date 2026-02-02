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

### Icon generation (non-binary)
We keep a text-only SVG source at `desktop/src-tauri/icons/icon.svg`. PNG/ICO/ICNS files are generated at build time and ignored by git:
```bash
npm run icons
```
This runs the Tauri icon generator and writes files into `desktop/src-tauri/icons/` without committing binary assets (`icon.png`, `icon.ico`, `icon.icns`).

The app will automatically start the local Standards Gateway and open a window pointed at the embedded Run Viewer.

Configuration is stored in `~/.sophia/config.json` (no secrets stored yet).

## Repo policy (no binary assets)
Binary assets (png/ico/icns/zip/exe/dll) are not tracked in this repo. Generated build outputs should stay in ignored folders or be stored as release artifacts instead of committed to git.

### Binary preflight
Run the binary guard before opening a PR:
```powershell
.\scripts\windows\check_no_binaries.ps1
```

### Patch fallback workflow
If PR tooling rejects a change set, you can fall back to patch transfer:
```bash
git format-patch origin/main..HEAD -o /tmp/sophia-patches
git apply /tmp/sophia-patches/*.patch
```

## Gateway startup
On launch, the desktop shell finds a free port (starting at 8001) and runs:
```
python -m uvicorn tools.sophia.standards_api:app --port <PORT>
```
The selected port is shown in the Connection Panel.

## Troubleshooting
- **Port already in use**: the app will increment the port until it finds a free slot (8001 → 8002 → …). If all attempts fail, restart the app after freeing a port.
- **Firewall prompts**: allow local loopback connections for `python` if prompted so the embedded viewer can reach `http://127.0.0.1:<PORT>/sophia/viewer`.
- **Gateway reports Down**: verify Python + `uvicorn` are available in your environment and that the standards API starts from the repo root.
