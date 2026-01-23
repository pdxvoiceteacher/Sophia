export function renderSummary(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>Load a run to see summary.</p>";
    return;
  }
  const decision = data.derived.decision || "unknown";
  const chipClass = decision.toLowerCase();
  const mode = data.derived.mode || "ci";
  container.innerHTML = `
    <div class="summary-line"><strong>Run ID:</strong> ${data.runDirName}</div>
    <div class="summary-line"><strong>Decision:</strong> <span class="chip ${chipClass}">${decision.toUpperCase()}</span></div>
    <div class="summary-line"><strong>Risk score:</strong> ${data.derived.riskScore ?? "n/a"}</div>
    <div class="summary-line"><strong>Mode:</strong> ${mode}</div>
    <div class="summary-line"><strong>Metrics:</strong> Ψ ${data.derived.metrics.Psi ?? "n/a"}, Λ ${data.derived.metrics.Lambda ?? "n/a"}, ΔS ${data.derived.metrics.DeltaS ?? "n/a"}</div>
  `;
}

export function renderTopRisks(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  if (!data.derived.topRisks.length) {
    container.innerHTML = "<p class='muted'>No top risks found.</p>";
    return;
  }
  container.innerHTML = data.derived.topRisks
    .map(
      (risk) => `
      <div class="summary-line">
        <strong>${risk.type}</strong> — ${risk.summary}
        <div class="detail muted">Severity: ${risk.severity}</div>
      </div>
    `
    )
    .join("");
}

export function renderActions(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  if (!data.derived.recommendedActions.length) {
    container.innerHTML = "<p class='muted'>No recommended actions.</p>";
    return;
  }
  container.innerHTML = data.derived.recommendedActions
    .map(
      (action) => `
      <div class="summary-line">
        <strong>${action.action}</strong>
        <div class="detail muted">Target: ${action.target} • Priority: ${action.priority}</div>
      </div>
    `
    )
    .join("");
}

export function renderArtifacts(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const bundleOutputs = data.auditBundle?.outputs || [];
  container.innerHTML = data.filesIndex
    .map((file) => {
      const bundle = bundleOutputs.find((item) => item.path === file.path);
      const hashInfo = bundle ? ` • hash: ${bundle.hash}` : "";
      return `<div class="summary-line"><strong>${file.path}</strong> (${file.size} bytes${hashInfo})</div>`;
    })
    .join("");
}

export function renderClaims(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const claims = data.telemetry?.claims || [];
  if (!claims.length) {
    container.innerHTML = "<p class='muted'>No claims found.</p>";
    return;
  }
  container.innerHTML = claims
    .map(
      (claim) => `
      <div class="summary-line">
        <strong>${claim.id || "claim"}</strong>: ${claim.statement || claim.notes || ""}
        <div class="detail muted">Type: ${claim.type || "n/a"} • Confidence: ${claim.confidence ?? "n/a"}</div>
      </div>
    `
    )
    .join("");
}

export function renderContradictions(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const contradictions = data.sophiaAudit?.contradiction_clusters || [];
  if (!contradictions.length) {
    container.innerHTML = "<p class='muted'>No contradictions reported.</p>";
    return;
  }
  container.innerHTML = contradictions
    .map(
      (item) => `
      <div class="summary-line">
        <strong>${item.type}</strong>: ${item.why}
        <div class="detail muted">Claims: ${(item.claims_involved || []).join(", ")}</div>
      </div>
    `
    )
    .join("");
}

export function renderEvents(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const summary = data.derived.eventsSummary;
  if (!summary) {
    container.innerHTML = "<p class='muted'>No event streams found.</p>";
    return;
  }
  container.innerHTML = `
    <div class="summary-line"><strong>tel.json</strong>: ${summary.telCount ?? 0} entries</div>
    <div class="summary-line"><strong>tel_events.jsonl</strong>: ${summary.telEventsCount ?? 0} entries</div>
    <div class="summary-line"><strong>ucc_tel_events.jsonl</strong>: ${summary.uccEventsCount ?? 0} entries</div>
  `;
}
