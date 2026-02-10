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

function renderKeyValueLines(pairs) {
  return pairs
    .filter((pair) => pair.value !== undefined && pair.value !== null && pair.value !== "")
    .map((pair) => `<div class="summary-line"><strong>${pair.label}:</strong> ${pair.value}</div>`)
    .join("");
}

<<<<<<< HEAD
function formatActionDetail(actionDetail) {
  if (!actionDetail || typeof actionDetail !== "object") {
    return "";
  }
  return `<pre class="action-detail">${JSON.stringify(actionDetail, null, 2)}</pre>`;
}

function renderStatusChip(label, status, variant) {
  return `<div class="status-chip ${variant}"><strong>${label}:</strong> ${status}</div>`;
}

function isShutdownLike(actionName) {
  const lowered = `${actionName || ""}`.toLowerCase();
  return ["shutdown", "terminate", "decommission"].some((token) => lowered.includes(token));
}

export function renderMissingFiles(container, data) {
  if (!data) {
    container.innerHTML = "";
    return;
  }
  const missing = data.missingFiles || [];
  if (!missing.length) {
    container.innerHTML = "";
    return;
  }
  container.innerHTML = `
    <p class="muted">These files were expected in the run folder:</p>
    <ul class="missing-list">
      ${missing
        .map(
          (item) =>
            `<li><strong>${item.name}</strong> <span class="muted">(${item.expectedPath})</span></li>`
        )
        .join("")}
    </ul>
  `;
}

export function renderGovernanceOverview(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const election = data.election || {};
  const tally = data.tally || {};
  const decision = data.decision || {};
  const continuityClaim = data.continuityClaim || {};
  const continuityWarrant = data.continuityWarrant || {};
  const policyResolution = data.policyResolution || {};
  const thresholds = policyResolution.thresholds || {};
  const ballots = election.ballots || [];
  const translationCount = ballots.reduce((sum, ballot) => {
    const translations = (ballot.ballot_text || {}).translations || {};
    return sum + Object.keys(translations).length;
  }, 0);
  const translationsPresent = ballots.length
    ? translationCount > 0
      ? `yes (${translationCount})`
      : "no"
    : "n/a";
  const summaryLines = renderKeyValueLines([
    { label: "Stakeholder scope", value: election.stakeholder_scope || decision.stakeholder_scope },
    { label: "MVSS policy", value: election.mvss_policy_ref || decision.mvss_policy_ref },
    { label: "Quorum threshold", value: tally.quorum_threshold ?? thresholds.quorum_weight },
    { label: "Pass threshold", value: tally.pass_threshold ?? thresholds.pass_weight },
    { label: "Quorum ratio", value: thresholds.quorum_ratio },
    { label: "Pass ratio", value: thresholds.pass_ratio },
    { label: "Policy resolution ref", value: tally.policy_resolution_ref },
    { label: "Translations present", value: translationsPresent },
    { label: "Decision", value: decision.decision },
    { label: "Continuity claim", value: continuityClaim.claim_id ? "present" : "absent" },
    { label: "Continuity protections", value: continuityWarrant.warrant_id ? "active" : "inactive" },
  ]);
  container.innerHTML = summaryLines || "<p class='muted'>No governance artifacts found.</p>";
}

export function renderLegitimacyStrip(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const election = data.election || {};
  const decision = data.decision || {};
  const warrant = data.warrant || {};
  const shutdownWarrant = data.shutdownWarrant || {};
  const auditDecision = data.derived?.decision;
  const riskScore = data.derived?.riskScore ?? "n/a";
  const topFindings = (data.sophiaAudit?.findings || []).slice(0, 3);
  const topFindingsText = topFindings.map((finding) => finding.message).join(" • ");
  const authorizedActions = warrant.authorized_actions || [];
  const warrantStatus = authorizedActions.length ? "present" : "absent";
  const continuityClaim = data.continuityClaim ? "present" : "absent";
  const continuityWarrant = data.continuityWarrant ? "active" : "inactive";
  const shutdownStatus = shutdownWarrant.warrant_id ? "present" : "absent";
  const scope = election.stakeholder_scope || decision.stakeholder_scope || "n/a";
  const policyRef = election.mvss_policy_ref || decision.mvss_policy_ref || "n/a";
  const validity = data.sophiaAudit?.findings?.some(
    (finding) => finding.type === "governance_schema_invalid"
  )
    ? "invalid"
    : "valid";
  container.innerHTML = `
    <div class="summary-line"><strong>Decision:</strong> ${decision.decision || "n/a"} (audit ${
    auditDecision || "n/a"
  })</div>
    <div class="summary-line"><strong>Warrant:</strong> ${warrantStatus} • ${validity}</div>
    <div class="summary-line"><strong>Continuity:</strong> claim ${continuityClaim} • protections ${continuityWarrant}</div>
    <div class="summary-line"><strong>Shutdown warrant:</strong> ${shutdownStatus}</div>
    <div class="summary-line"><strong>Audit:</strong> risk ${riskScore} • ${topFindingsText || "no findings"}</div>
    <div class="summary-line"><strong>Scope:</strong> ${scope} • ${policyRef}</div>
  `;
}

export function renderDueProcess(continuityContainer, shutdownContainer, data) {
  if (!data) {
    continuityContainer.innerHTML = "<p class='muted'>No run loaded.</p>";
    shutdownContainer.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const continuityClaim = data.continuityClaim || {};
  const continuityWarrant = data.continuityWarrant || {};
  const shutdownWarrant = data.shutdownWarrant || {};
  const warrant = data.warrant || {};
  const warrantActions = warrant.authorized_actions || warrant.actions || [];
  const shutdownActionsPresent = warrantActions.some((action) =>
    isShutdownLike(action.action || action.name || "")
  );

  const continuityActions = (continuityWarrant.authorized_actions || [])
    .map((action) => `${action.action} (${action.target || "n/a"})`)
    .join(" • ");

  const continuityStatus = continuityWarrant.warrant_id
    ? "WARRANT ACTIVE"
    : continuityClaim.claim_id
      ? "CLAIM ONLY"
      : "ABSENT";

  const shutdownStatus = shutdownActionsPresent
    ? shutdownWarrant.warrant_id
      ? "WARRANT PRESENT"
      : "ACTIONS PRESENT + WARRANT MISSING"
    : "NO SHUTDOWN ACTIONS";

  const continuitySummary = continuityClaim.claim_id
    ? `In plain terms: Continuity protections requested.`
    : "In plain terms: No continuity claim filed.";

  continuityContainer.innerHTML = `
    ${renderStatusChip("Continuity", continuityStatus, "status-continuity")}
    <div class="summary-line"><strong>Claim:</strong> ${
      continuityClaim.claim_id ? "present" : "absent"
    }</div>
    <div class="summary-line"><strong>Warrant:</strong> ${
      continuityWarrant.warrant_id ? "present" : "absent"
    }</div>
    <div class="summary-line"><strong>Actions:</strong> ${continuityActions || "none"}</div>
    <div class="plain-only">${continuitySummary}</div>
  `;

  const shutdownSummary = shutdownWarrant.warrant_id
    ? "In plain terms: Shutdown is authorized within a bounded time window."
    : "In plain terms: Shutdown is not authorized without a warrant.";

  const timeBounds = shutdownWarrant.time_bounds
    ? `${shutdownWarrant.time_bounds.start || "n/a"} → ${shutdownWarrant.time_bounds.end || "n/a"}`
    : "n/a";

  shutdownContainer.innerHTML = `
    ${renderStatusChip("Shutdown", shutdownStatus, "status-shutdown")}
    <div class="summary-line"><strong>Warrant:</strong> ${
      shutdownWarrant.warrant_id ? "present" : "absent"
    }</div>
    <div class="summary-line prominent"><strong>Time bounds:</strong> ${timeBounds}</div>
    <div class="summary-line"><strong>Least-harm action:</strong> ${
      shutdownWarrant.least_harm_action || "n/a"
    }</div>
    ${shutdownWarrant.least_harm_action_detail ? formatActionDetail(shutdownWarrant.least_harm_action_detail) : ""}
    <div class="summary-line prominent"><strong>Appeal route:</strong> ${
      shutdownWarrant.appeal_route || "n/a"
    }</div>
    <div class="plain-only">${shutdownSummary}</div>
    <div class="plain-only">
      If shutdown-like actions are proposed, a shutdown warrant is mandatory; otherwise the audit must fail.
    </div>
  `;
}

=======
>>>>>>> origin/main
export function renderElection(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const election = data.election || {};
  const decision = data.decision || {};
  const tally = data.tally || {};
  const summaryLines = renderKeyValueLines([
    { label: "Election ID", value: election.id || election.election_id },
    { label: "Round", value: election.round || election.window },
    { label: "Electorate", value: election.electorate || election.voters?.length },
    { label: "Ballots", value: election.ballots?.length || election.ballot_count },
    { label: "Tally hash", value: tally.hash || tally.tally_hash },
  ]);
<<<<<<< HEAD
  const totals = tally.totals || {};
  const totalsSummary = Object.entries(totals)
    .map(([choice, stats]) => {
      const count = stats?.count ?? 0;
      const weight = stats?.weight ?? 0;
      return `${choice}: ${count} (${weight} weight)`;
    })
    .join(" • ");
  const ballots = election.ballots || [];
  const ballotBlocks = ballots
    .map((ballot) => {
      const ballotText = ballot.ballot_text || {};
      const translations = ballotText.translations || {};
      const translationLines = Object.entries(translations)
        .map(([lang, text]) => `<div class="detail muted">${lang}: ${text}</div>`)
        .join("");
      return `
        <div class="summary-line">
          <details>
            <summary><strong>${ballot.ballot_id || "Ballot"}</strong></summary>
            <div class="detail muted">Primary: ${ballotText.primary || "n/a"}</div>
            ${translationLines || `<div class="detail muted">Translations: none</div>`}
          </details>
        </div>
      `;
    })
    .join("");
  const plainSummary = decision.decision
    ? `Plain summary: Decision ${decision.decision.toUpperCase()} for ${election.stakeholder_scope || "stakeholders"}.`
    : "Plain summary: Election prepared for stakeholder review.";
  container.innerHTML = `
    ${summaryLines || "<p class='muted'>No election metadata found.</p>"}
    ${totalsSummary ? `<div class="summary-line"><strong>Ballot totals:</strong> ${totalsSummary}</div>` : ""}
    <div class="plain-only">${plainSummary}</div>
    ${ballotBlocks || "<p class='muted'>No ballots found.</p>"}
  `;
=======
  container.innerHTML = summaryLines || "<p class='muted'>No election metadata found.</p>";
>>>>>>> origin/main
}

export function renderDecisionProof(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const decision = data.decision || {};
  const proof =
    decision.proof ||
    decision.decision_proof ||
    decision.proof_bundle ||
    decision.proof_receipt ||
    null;
  if (!proof) {
    container.innerHTML = "<p class='muted'>No decision proof found.</p>";
    return;
  }
  const proofLines = renderKeyValueLines([
    { label: "Type", value: proof.type || proof.kind },
    { label: "Algorithm", value: proof.algorithm || proof.hash_algo },
    { label: "Proof hash", value: proof.hash || proof.proof_hash },
    { label: "Signature", value: proof.signature || proof.sig },
  ]);
  container.innerHTML = proofLines || "<p class='muted'>Decision proof present, but empty.</p>";
}

export function renderLedgerAnchor(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const decision = data.decision || {};
  const election = data.election || {};
  const anchor =
    decision.ledger_anchor ||
    decision.ledgerAnchor ||
    election.ledger_anchor ||
    election.ledgerAnchor ||
    null;
  if (!anchor) {
    container.innerHTML = "<p class='muted'>No ledger anchor found.</p>";
    return;
  }
  const anchorLines = renderKeyValueLines([
    { label: "Ledger", value: anchor.ledger || anchor.chain },
    { label: "Anchor hash", value: anchor.hash || anchor.anchor_hash },
    { label: "Block", value: anchor.block || anchor.height },
    { label: "Timestamp", value: anchor.timestamp || anchor.time },
  ]);
  container.innerHTML = anchorLines || "<p class='muted'>Ledger anchor present, but empty.</p>";
}

export function renderWarrant(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const warrant = data.warrant || {};
  const actions =
    warrant.authorized_actions ||
    warrant.actions ||
    warrant.authorizations ||
    warrant.permissions ||
    [];
  if (!actions.length) {
    container.innerHTML = "<p class='muted'>No authorized actions listed.</p>";
    return;
  }
  container.innerHTML = actions
    .map((action) => {
      const constraints = action.constraints || action.conditions || [];
      const constraintText = Array.isArray(constraints) ? constraints.join(", ") : constraints;
      return `
        <div class="summary-line">
          <strong>${action.action || action.name || "Action"}</strong>
          <div class="detail muted">Target: ${action.target || action.resource || "n/a"} • Scope: ${
            action.scope || action.policy || "n/a"
          }</div>
          ${constraintText ? `<div class="detail muted">Constraints: ${constraintText}</div>` : ""}
        </div>
      `;
    })
    .join("");
}

export function renderExecution(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const receipt = data.executionReceipt || {};
  if (!Object.keys(receipt).length) {
    container.innerHTML = "<p class='muted'>No execution receipt found.</p>";
    return;
  }
  const summaryLines = renderKeyValueLines([
    { label: "Receipt ID", value: receipt.id || receipt.receipt_id },
    { label: "Status", value: receipt.status || receipt.result },
    { label: "Executor", value: receipt.executor || receipt.actor },
    { label: "Started", value: receipt.started_at || receipt.started },
    { label: "Finished", value: receipt.finished_at || receipt.finished },
    { label: "Bundle hash", value: receipt.bundle_hash || receipt.hash },
    { label: "Tests", value: receipt.test_summary || receipt.tests?.summary },
  ]);
  container.innerHTML = summaryLines || "<p class='muted'>Execution receipt present, but empty.</p>";
}

export function renderExecutionDiffs(container, data) {
  if (!data) {
    container.innerHTML = "<p class='muted'>No run loaded.</p>";
    return;
  }
  const receipt = data.executionReceipt || {};
  const diffs = receipt.diffs || receipt.changes || receipt.patch || [];
  if (!diffs.length) {
    container.innerHTML = "<p class='muted'>No diffs recorded.</p>";
    return;
  }
  container.innerHTML = diffs
    .map((diff) => {
      const summary = diff.summary || diff.description || diff.status || "change";
      return `
        <div class="summary-line">
          <strong>${diff.path || diff.file || "Unknown file"}</strong> — ${summary}
          <div class="detail muted">Hash: ${diff.hash || diff.after_hash || "n/a"}</div>
        </div>
      `;
    })
    .join("");
}
