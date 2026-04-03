from __future__ import annotations

import json
from http.server import BaseHTTPRequestHandler, HTTPServer
from typing import Any, Dict

from sophia.hb02_experiment_audit import audit_hb02_experiment

HOST, PORT = "0.0.0.0", 8787


class Handler(BaseHTTPRequestHandler):
    def _send(self, code: int, obj: Dict[str, Any]) -> None:
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(obj).encode())

    def do_POST(self) -> None:  # noqa: N802
        if self.path != "/audit":
            self._send(404, {"error": "not_found"})
            return

        length = int(self.headers.get("Content-Length", "0"))
        body = self.rfile.read(length)
        packet = json.loads(body.decode() or "{}")

        audit = audit_hb02_experiment(packet)
        self._send(200, {"audit": audit})


def run() -> None:
    httpd = HTTPServer((HOST, PORT), Handler)
    print(f"Sophia audit server on http://{HOST}:{PORT}")
    httpd.serve_forever()


if __name__ == "__main__":
    run()
