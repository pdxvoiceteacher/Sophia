from __future__ import annotations

import json
import os
import subprocess
import sys
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator


@dataclass(slots=True)
class SonyaNodeConfig:
    node_id: str
    compute_class: str = "cpu_only"
    telemetry_endpoint: str = "out/sonya_node"
    enabled_task_types: dict[str, bool] = field(default_factory=lambda: {"sophia_echo": True})


class SonyaNodeRuntime:
    def __init__(self, repo_root: Path | None = None, config: SonyaNodeConfig | None = None) -> None:
        self.repo_root = (repo_root or Path(__file__).resolve().parents[2]).resolve()
        self.config = config or self.load_config(self.repo_root)
        self._schema_validator = self._load_schema_validator()

    @classmethod
    def load_config(cls, repo_root: Path) -> SonyaNodeConfig:
        candidates = [repo_root / "config" / "sonya_node_config.json", repo_root / "sonya_node_config.json"]
        for path in candidates:
            if path.exists():
                payload = json.loads(path.read_text(encoding="utf-8-sig"))
                return SonyaNodeConfig(
                    node_id=str(payload.get("node_id") or uuid.uuid4()),
                    compute_class=str(payload.get("compute_class") or "cpu_only"),
                    telemetry_endpoint=str(payload.get("telemetry_endpoint") or "out/sonya_node"),
                    enabled_task_types=dict(payload.get("enabled_task_types") or {"sophia_echo": True}),
                )
        return SonyaNodeConfig(node_id=str(uuid.uuid4()))

    def _load_schema_validator(self) -> Draft202012Validator:
        schema_path = self.repo_root / "schema" / "sonya_node_telemetry.schema.json"
        schema = json.loads(schema_path.read_text(encoding="utf-8-sig"))
        return Draft202012Validator(schema)

    def _invoke_telemetry_wrapper(self, prompt: str, out_dir: Path) -> Path:
        out_dir.mkdir(parents=True, exist_ok=True)
        cmd = [
            sys.executable,
            "tools/telemetry/run_wrapper.py",
            "--out",
            str(out_dir),
            "--quick",
            "--perturbations",
            "1",
        ]
        env = dict(os.environ)
        env["SONYA_NODE_PROMPT"] = prompt
        subprocess.run(cmd, cwd=str(self.repo_root), check=True, capture_output=True, text=True, env=env)
        telemetry_path = out_dir / "telemetry.json"
        if not telemetry_path.exists():
            raise FileNotFoundError(f"Expected telemetry output at {telemetry_path}")
        return telemetry_path

    @staticmethod
    def _extract_metrics(telemetry_payload: dict[str, Any]) -> dict[str, float]:
        src = telemetry_payload.get("metrics") if isinstance(telemetry_payload, dict) else {}
        if not isinstance(src, dict):
            src = {}
        mapping = {
            "E": "E",
            "T": "T",
            "Psi": "Ψ",
            "DeltaS": "ΔS",
            "Lambda": "Λ",
            "Es": "Eₛ",
        }
        metrics: dict[str, float] = {}
        for key, out_key in mapping.items():
            val = src.get(key)
            if isinstance(val, (int, float)):
                metrics[out_key] = float(val)
        return metrics

    def run_local_task(self, prompt: str) -> dict[str, Any]:
        task_id = str(uuid.uuid4())
        timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        task_out_dir = self.repo_root / "out" / "sonya_node" / task_id
        artifacts: list[str] = []
        status = "success"
        metrics: dict[str, float] = {}

        try:
            telemetry_path = self._invoke_telemetry_wrapper(prompt=prompt, out_dir=task_out_dir)
            artifacts.append(str(telemetry_path.relative_to(self.repo_root)).replace("\\", "/"))
            telemetry_payload = json.loads(telemetry_path.read_text(encoding="utf-8-sig"))
            metrics = self._extract_metrics(telemetry_payload)
            for candidate in ["evidence_bundle.json", "consensus_summary.json", "attestations.json"]:
                p = task_out_dir / candidate
                if p.exists():
                    artifacts.append(str(p.relative_to(self.repo_root)).replace("\\", "/"))
        except Exception:
            status = "failed"

        telemetry_record = {
            "schema": "sonya_node_telemetry_v1",
            "node_id": self.config.node_id,
            "task_id": task_id,
            "timestamp": timestamp,
            "metrics": metrics,
            "status": status,
            "artifacts": artifacts,
        }
        self._schema_validator.validate(telemetry_record)

        node_telemetry_dir = self.repo_root / self.config.telemetry_endpoint
        node_telemetry_dir.mkdir(parents=True, exist_ok=True)
        node_telemetry_path = node_telemetry_dir / f"sonya_node_task_{task_id}.json"
        node_telemetry_path.write_text(json.dumps(telemetry_record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

        print(f"Sonya Node {self.config.node_id} ran task {task_id} with status {status}")
        print(f"Sonya telemetry: {node_telemetry_path}")

        return {"record": telemetry_record, "path": node_telemetry_path}
