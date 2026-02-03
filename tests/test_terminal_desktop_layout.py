from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DESKTOP = ROOT / "desktop"


def test_desktop_layout_exists() -> None:
    required = [
        DESKTOP / "package.json",
        DESKTOP / "src" / "index.html",
        DESKTOP / "src" / "main.js",
        DESKTOP / "src" / "style.css",
        DESKTOP / "src-tauri" / "Cargo.toml",
        DESKTOP / "src-tauri" / "tauri.conf.json",
        DESKTOP / "src-tauri" / "src" / "main.rs",
        DESKTOP / "src-tauri" / "src" / "state.rs",
    ]
    missing = [path for path in required if not path.exists()]
    assert not missing, f"Missing desktop files: {missing}"
