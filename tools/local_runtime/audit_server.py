from pathlib import Path
import json

from fastapi import FastAPI
import uvicorn

app = FastAPI(title="Sophia Local Audit", version="0.1.1")


@app.post("/api/audit/civilizational")
def audit():
    path = Path("bridge/telemetry.json")

    if not path.exists():
        return {"status": "no_data", "verdict": "unknown"}

    with open(path, encoding="utf-8") as f:
        t = json.load(f)

    psi = t.get("coherence", 0.0)
    delta_s = t.get("delta_s", 0.0)

    verdict = "pass" if psi >= 0.5 else "review"

    return {
        "status": "ok",
        "verdict": verdict,
        "psi": psi,
        "delta_s": delta_s,
        "advisory": "measure → suggest → NOT enforce",
    }


def main():
    uvicorn.run(app, host="127.0.0.1", port=4174)


if __name__ == "__main__":
    main()
