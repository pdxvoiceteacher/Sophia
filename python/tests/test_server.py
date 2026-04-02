import json
import threading
from http.client import HTTPConnection
from http.server import HTTPServer

from sophia.server import Handler


def _start_server() -> tuple[HTTPServer, threading.Thread]:
    httpd = HTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=httpd.serve_forever, daemon=True)
    thread.start()
    return httpd, thread


def test_audit_endpoint_returns_audit_payload() -> None:
    httpd, thread = _start_server()
    try:
        conn = HTTPConnection("127.0.0.1", httpd.server_port, timeout=2)
        payload = {
            "baseline": {
                "literal_output": "baseline literal",
                "allegorical_output": "baseline allegorical",
            },
            "conditioned": {
                "literal_output": "conditioned literal",
                "allegorical_output": "conditioned allegorical",
            },
            "true_coherence": "coherent",
            "coherence_context": "present",
        }
        conn.request("POST", "/audit", body=json.dumps(payload))
        response = conn.getresponse()
        body = json.loads(response.read().decode())

        assert response.status == 200
        assert body["audit"]["audit_pass"] is True
    finally:
        httpd.shutdown()
        thread.join(timeout=2)


def test_non_audit_path_returns_not_found() -> None:
    httpd, thread = _start_server()
    try:
        conn = HTTPConnection("127.0.0.1", httpd.server_port, timeout=2)
        conn.request("POST", "/unknown", body="{}")
        response = conn.getresponse()
        body = json.loads(response.read().decode())

        assert response.status == 404
        assert body == {"error": "not_found"}
    finally:
        httpd.shutdown()
        thread.join(timeout=2)
