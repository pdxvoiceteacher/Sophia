export const GLOSSARY = {
  "Ψ": "Psi (coherence) — product of evidence and trust metrics.",
  "Λ": "Lambda — instability or entropy pressure in telemetry.",
  "ΔS": "DeltaS — drift distance or state change magnitude.",
  "TEL": "Telemetry event log emitted by runs.",
  "Es": "Evidence strength / signal metric.",
  "audit_bundle": "Audit bundle metadata with hashes and outputs.",
};

export function renderGlossary(container) {
  container.innerHTML = "";
  Object.entries(GLOSSARY).forEach(([term, definition]) => {
    const item = document.createElement("li");
    item.innerHTML = `<strong>${term}</strong>: ${definition}`;
    container.appendChild(item);
  });
}
