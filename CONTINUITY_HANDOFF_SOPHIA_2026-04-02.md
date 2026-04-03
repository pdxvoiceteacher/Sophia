# Sophia Continuity Handoff
## Date: 2026-04-02

---

## Role of this repo

Sophia is the governance and routing organ.

It is responsible for:
- divergence governance
- answer vs novelty routing
- clarification gating
- route confidence / route reason
- deciding whether novelty is sent onward to Atlas

Sophia should remain the arbiter of:
- on-task answer return
- novelty routing
- whether clarification is required
- whether Atlas should be engaged

Sophia should **not** become:
- the primary evidence extractor
- the raw cognition field
- the memory store itself

---

## Verified working in this repo

- `/health`
- `/govern/divergence`
- `/govern/routing`

Outputs written into CoherenceLattice bridge:
- `governance_decision.json`
- `routing_decision.json`

Routing decisions now include:
- `return_track_id`
- `return_reason`
- `novel_track_id`
- `novelty_action`
- `atlas_route_confidence` / `atlas_log_confidence` depending on patch family
- `atlas_route_reason` / `atlas_log_reason`
- clarification fields

---

## Design cautions

### 1. Sophia should govern, not overcompute
Do not move raw extraction/salience logic here.

### 2. Relevance and novelty must remain separate
Sophia should preserve novelty even when answer relevance dominates.

### 3. Clarification is a governance decision
When ambiguity is material, Sophia should decide whether to:
- return answer anyway
- ask clarification
- send novelty onward
- hold for review

---

## Current next step for this repo

### Atlas Retrieval + Prior Injection
Needed here:
- decide whether Atlas prior retrieval should happen for a given run
- decide injection mode:
  - `answer_support`
  - `novel_scope_extension`
  - `background_only`
  - `ignore`

Sophia should govern prior injection rather than CoherenceLattice coercing it.

---

## Presentation protocol for future Echo iterations

For Sophia patches:
- state exactly what routing semantics changed
- show exact resulting JSON decision shape
- include exact verification commands
- never assume CoherenceLattice-side packets already exist without checking
