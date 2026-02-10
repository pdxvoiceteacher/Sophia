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


def test_terminal_connector_controls_present() -> None:
    html = (DESKTOP / "src" / "index.html").read_text(encoding="utf-8")
    for element_id in [
        "connector-type",
        "connector-endpoint",
        "connector-model",
        "test-connector",
        "ucc-status",
    ]:
        assert f'id="{element_id}"' in html


def test_windows_operator_scripts_exist() -> None:
    for path in [
        ROOT / "scripts" / "windows" / "dev.ps1",
        ROOT / "scripts" / "windows" / "dev_up.ps1",
    ]:
        assert path.exists(), f"Missing script: {path}"
