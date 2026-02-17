# Development Environment Notes

## Tauri/Linux build dependencies

Desktop Rust/Tauri checks on Linux require GTK/WebKit system packages (including `pkg-config` and `libglib2.0-dev`).

In this repo CI, desktop build lanes are gated and only run when explicitly requested (`workflow_dispatch` + desktop build input), while Python/Node smoke lanes run by default.

If you need to run desktop checks locally on Debian/Ubuntu:

```bash
sudo apt-get update
sudo apt-get install -y pkg-config libglib2.0-dev libgtk-3-dev libwebkit2gtk-4.1-dev libayatana-appindicator3-dev librsvg2-dev patchelf
```
