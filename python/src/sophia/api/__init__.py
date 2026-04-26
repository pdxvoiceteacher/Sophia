from __future__ import annotations

from pathlib import Path
from typing import Any


def emit_attention_updates(bridge_root: str | Path) -> tuple[dict[str, Any], dict[str, Any]]:
    """Build and persist Sophia attention updates for Publisher consumption."""
    from sophia.build_attention_updates import build_attention_updates
    return build_attention_updates(str(bridge_root))


__all__ = ["emit_attention_updates"]
