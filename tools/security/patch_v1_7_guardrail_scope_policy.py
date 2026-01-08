from __future__ import annotations
from pathlib import Path
import re

fp = Path("ucc/src/ucc/vote_guardrail.py")
txt = fp.read_text(encoding="utf-8")

# Ensure import
if "from ucc.vote_scope_policy import scope_policy_violations" not in txt:
    txt = txt.replace("from uuid import uuid4", "from uuid import uuid4\n\nfrom ucc.vote_scope_policy import scope_policy_violations")

# Insert violations extension just before computing passed/report
if "scope_policy_violations" not in txt:
    # Add right before: passed = len(violations) == 0
    txt = txt.replace(
        "    passed = len(violations) == 0",
        "    # v1.7: scope-bound proof/circuit policy\n    violations.extend(scope_policy_violations(manifest, strict=strict))\n\n    passed = len(violations) == 0"
    )

fp.write_text(txt, encoding="utf-8")
print("Patched vote_guardrail.py with v1.7 scope policy enforcement.")
