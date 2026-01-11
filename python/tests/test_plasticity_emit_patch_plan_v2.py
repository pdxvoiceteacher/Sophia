import json
import subprocess
import sys
from pathlib import Path

def test_emit_patch_plan_v2_uses_action_v2(tmp_path: Path):
    proposal = {
        "schema":"plasticity_tuning_proposal_v1",
        "proposal_id":"pid",
        "created_at_utc":"2026-01-01T00:00:00Z",
        "run_dir":"x",
        "inputs":{"telemetry_path":"x","tel_events_path":None,"ucc_tel_events_path":None,"tel_summary_present":False},
        "measures":{"coherence_metrics":{},"event_counts":{"tel_events_total":0,"ucc_events_total":0,"ucc_errors_total":0},"tel_summary":None},
        "triggers":{"force_proposal":True,"ucc_errors_present":False,"psi_below_threshold":True},
        "recommendations":[
            {
              "id":"r1","kind":"config_tune","target":"config/plasticity/tuning.json:min_psi_threshold",
              "suggestion":"lower","rationale":"thermo-safe","evidence":None,
              "action_v2":{"op":"json_set","path":"config/plasticity/tuning.json","json_path":"min_psi_threshold","value":0.89}
            }
        ],
        "no_action":False
    }
    prop = tmp_path / "proposal.json"
    prop.write_text(json.dumps(proposal, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

    out = tmp_path / "plan.json"
    subprocess.run([sys.executable, "tools/telemetry/emit_patch_plan_v2.py", "--proposal", str(prop), "--out", str(out), "--created-at-utc", "2026-01-01T00:00:00Z"], check=True)
    plan = json.loads(out.read_text(encoding="utf-8"))
    ops = plan.get("operations", [])
    assert len(ops) == 1
    assert ops[0]["op"] == "json_set"
    assert ops[0]["path"] == "config/plasticity/tuning.json"
    assert ops[0]["json_path"] == "min_psi_threshold"
    assert ops[0]["value"] == 0.89
