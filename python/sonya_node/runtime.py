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
        # repo_root is the top-level Sophia repo (where tools/, python/, schema/ live)
        self.repo_root = (repo_root or Path(__file__).resolve().parents[2]).resolve()
        self.config = config or self.load_config(self.repo_root)
        self._schema_validator = self._load_schema_validator()

    @classmethod
    def load_config(cls, repo_root: Path) -> SonyaNodeConfig:
        candidates = [
            repo_root / "config" / "sonya_node_config.json",
            repo_root / "sonya_node_config.json",
        ]
        for path in candidates:
            if path.exists():
                payload = json.loads(path.read_text(encoding="utf-8-sig"))
                return SonyaNodeConfig(
                    node_id=str(payload.get("node_id") or uuid.uuid4()),
                    compute_class=str(payload.get("compute_class") or "cpu_only"),
                    telemetry_endpoint=str(payload.get("telemetry_endpoint") or "out/sonya_node"),
                    enabled_task_types=dict(payload.get("enabled_task_types") or {"sophia_echo": True}),
                )
        # Fallback if no config file is present
        return SonyaNodeConfig(node_id=str(uuid.uuid4()))

    def _load_schema_validator(self) -> Draft202012Validator:
        schema_path = self.repo_root / "schema" / "sonya_node_telemetry.schema.json"
        schema = json.loads(schema_path.read_text(encoding="utf-8-sig"))
        return Draft202012Validator(schema)

    def _invoke_telemetry_wrapper(self, prompt: str, out_dir: Path) -> Path:
        """
        Call the existing telemetry wrapper once, writing outputs under out_dir.
        Expects telemetry.json to be produced there.
        """
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
        # Provide the prompt via environment for the wrapped process, if it wants it
        env["SONYA_NODE_PROMPT"] = prompt
        subprocess.run(cmd, cwd=str(self.repo_root), check=True, capture_output=True, text=True, env=env)
        telemetry_path = out_dir / "telemetry.json"
        if not telemetry_path.exists():
            raise FileNotFoundError(f"Expected telemetry output at {telemetry_path}")
        return telemetry_path

    @staticmethod
    def _extract_metrics(telemetry_payload: dict[str, Any]) -> dict[str, float]:
        """
        Normalize ΔSyn-style metrics from the raw telemetry into the ASCII keys
        expected by CoherenceLattice:

            E, T, Psi, DeltaS, Lambda, Es

        Accepts either ASCII or Greek keys in the source metrics:

            Psi / Ψ
            DeltaS / ΔS
            Lambda / Λ
            Es / Eₛ
        """
        src = telemetry_payload.get("metrics") if isinstance(telemetry_payload, dict) else {}
        if not isinstance(src, dict):
            src = {}

        # Mapping from output key -> list of candidate input keys to check
        key_candidates: dict[str, list[str]] = {
            "E":      ["E"],
            "T":      ["T"],
            "Psi":    ["Psi", "Ψ"],
            "DeltaS": ["DeltaS", "ΔS"],
            "Lambda": ["Lambda", "Λ"],
            "Es":     ["Es", "Eₛ"],
        }

        metrics: dict[str, float] = {}

        for out_key, candidates in key_candidates.items():
            for name in candidates:
                if name in src:
                    val = src.get(name)
                    if isinstance(val, (int, float)):
                        metrics[out_key] = float(val)
                        break  # stop at the first matching candidate

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
            # Record the telemetry.json path relative to repo_root
            artifacts.append(str(telemetry_path.relative_to(self.repo_root)).replace("\\", "/"))
            telemetry_payload = json.loads(telemetry_path.read_text(encoding="utf-8-sig"))
            metrics = self._extract_metrics(telemetry_payload)

            # Capture any other known artifacts (if present)
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
        # Validate against the Sonya telemetry schema
        self._schema_validator.validate(telemetry_record)

        # Write Sonya telemetry to the configured endpoint (e.g. ../CoherenceLattice/telemetry/sonya)
        node_telemetry_dir = self.repo_root / self.config.telemetry_endpoint
        node_telemetry_dir.mkdir(parents=True, exist_ok=True)
        node_telemetry_path = node_telemetry_dir / f"sonya_node_task_{task_id}.json"
        node_telemetry_path.write_text(
            json.dumps(telemetry_record, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )

        print(f"Sonya Node {self.config.node_id} ran task {task_id} with status {status}")
        print(f"Sonya telemetry: {node_telemetry_path}")

        return {"record": telemetry_record, "path": node_telemetry_path}
