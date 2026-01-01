# UCC DEMO (v0.1): Auditable Governance Artifacts in Minutes

This demo shows how UCC produces **auditable control artifacts**:
- schema-validated modules
- deterministic reports
- threshold/checklist tables
- comparative audits (delta reports)
- cryptographic audit bundles (hashes + environment + git commit)

> Safety note: UCC is a research scaffold. Do not run untrusted modules.
> UCC executes only built-in step types (no arbitrary code execution).

---

## 0) Prereqs (local)

From repo root:

```powershell
# Create/activate your existing venv if needed; otherwise skip.
cd C:\Users\pdxvo\Documents\Lean\CoherenceLattice

# Install UCC (editable) into your existing python venv
.\python\.venv\Scripts\python.exe -m pip install -U pip
.\python\.venv\Scripts\python.exe -m pip install -e .\ucc[dev]
