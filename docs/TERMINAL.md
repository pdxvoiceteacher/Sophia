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

The app will automatically start the local Standards Gateway and open a window pointed at the embedded Run Viewer.

Configuration is stored in `~/.sophia/config.json` (no secrets stored yet).

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
