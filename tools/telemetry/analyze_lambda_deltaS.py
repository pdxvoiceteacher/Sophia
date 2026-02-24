from __future__ import annotations
import json
from pathlib import Path
import sys

def load_metrics(telemetry_path: Path) -> dict:
    d = json.loads(telemetry_path.read_text(encoding="utf-8-sig"))
    # adjust if your schema nests differently
    return d.get("coherence_metrics", d.get("coherenceMetrics", d.get("metrics", {})))

def main() -> int:
    if len(sys.argv) < 3:
        print("usage: analyze_lambda_deltaS.py <unguided_telemetry.json> <guided_telemetry.json>")
        return 2

    u = load_metrics(Path(sys.argv[1]))
    g = load_metrics(Path(sys.argv[2]))

    def get(m, k, default=None):
        return m.get(k, default)

    # Minimal invariants: both should exist
    for label, m in [("unguided", u), ("guided", g)]:
        if get(m, "Λ") is None and get(m, "lambda") is None and get(m, "Lambda") is None:
            print(f"{label}: missing Λ")
            return 3
        if get(m, "ΔS") is None and get(m, "deltaS") is None and get(m, "DeltaS") is None:
            print(f"{label}: missing ΔS")
            return 3

    # Normalize key names
    def norm(m):
        return {
            "lambda": m.get("Λ", m.get("lambda", m.get("Lambda"))),
            "deltaS": m.get("ΔS", m.get("deltaS", m.get("DeltaS"))),
        }

    u2, g2 = norm(u), norm(g)

    print("UNGUIDED:", u2)
    print("GUIDED:", g2)

    # Report the normalized metrics and keep the command non-failing for telemetry trend checks.
    # CI assertions should interpret these values rather than forcing a hard failure here.
    print("OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
