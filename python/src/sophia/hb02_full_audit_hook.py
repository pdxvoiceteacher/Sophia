from __future__ import annotations

from sophia.hb02_experiment_audit import audit_hb02_experiment


def audit_full_hb02(packet):
    audit = audit_hb02_experiment(packet)

    if not audit["audit_pass"]:
        print("\n⚠️ SOPHIA WARNING:")
        print(audit["findings"])

    return audit
