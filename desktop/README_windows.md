# Sophia Terminal (Windows prerequisites)

## Required tooling
- **Rust toolchain** (stable): https://rustup.rs/
- **Node.js** (LTS) and npm
- **Python 3.10+** with venv support
- **WebView2 runtime** (Microsoft Edge WebView2)

## Optional but recommended
- Git for Windows
- Visual Studio Build Tools (C++ workload) if you hit native build errors

## Quick setup
1. Bootstrap the venv and install Python deps:
   ```powershell
   .\scripts\windows\bootstrap_venv.ps1
   ```
2. Install desktop Node deps:
   ```powershell
   cd desktop
   npm install
   ```
3. Run the desktop shell:
   ```powershell
   npm run tauri dev
   ```

## One-command workflow
Use the repo preflight + smoke workflow:
```powershell
.\scripts\windows\dev_up.ps1
```
