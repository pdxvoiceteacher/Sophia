# Summary
This coherence run audits the TCHES baseline-vs-lambda comparator artifacts produced by UCC:
comparison.json/.md and audit_bundle.json.

# Assumptions
- Toy ODE model; proxy audit only; not operational advice.
- Audit improves traceability and reviewability; it is not a truth guarantee.

# Limitations
- Comparator metrics depend on the referenced baseline/lambda run CSVs.
- ΔS/Λ are proxy stability checks on paraphrases (not semantic validity).

# Uncertainty
- If comparator outputs change, rerun this audit.

# Disclosure
Research scaffold only. Report issues via GitHub.

# Results
comparison.json records baseline_* and lambda_* metrics and deltas (e.g., delta_warn_LambdaT_steps, delta_mean_Ppump, delta_mean_Qch) and flags such as improved_warn_time.
