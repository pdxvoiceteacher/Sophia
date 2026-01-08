from __future__ import annotations
from ucc.verifier_registry import load_registry

def main() -> int:
    reg = load_registry()
    for k, v in sorted(reg.items()):
        print(f"{k}: kind={v.get('kind')} alg={v.get('alg')} enabled={v.get('enabled', True)}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
