def audit_hypothesis_tests(artifact):

    findings = []

    for test in artifact["tests"]:

        if test["psi_gain"] < 0:
            findings.append({
                "severity": "warn",
                "advisory": "watch",
                "semanticMode": "non-executive",
                "message": "Hypothesis reduced coherence.",
            })

    return findings
