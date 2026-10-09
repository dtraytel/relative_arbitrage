export const meta = {
  name: 'phase4-implement-round2',
  description: 'Phase 4 round 2: the remaining 20 chunks of verified simplifications, corollary rewrites, twin merges and library re-proofs in eight isolated worktrees, each group reviewed',
  phases: [{ title: 'Implement', detail: 'per group: a chain of implementers, one per remaining chunk' }, { title: 'Review', detail: 'one reviewer per group' }],
}
const SP = '/tmp/claude-0/-home-user-relative-arbitrage/b298b4d9-283e-5a1e-9ff1-6c1924a698bb/scratchpad'
const BASE = 'bc034d3'
const GROUPS = args
const RESULT = {
  type: 'object',
  properties: {
    items: { type: 'array', items: { type: 'object', properties: {
      id: { type: 'string' }, status: { type: 'string', enum: ['done', 'partly-done', 'abandoned', 'skipped', 'already-done'] },
      lines_saved: { type: 'number' }, notes: { type: 'string' } }, required: ['id', 'status', 'lines_saved', 'notes'] } },
    build: { type: 'string', enum: ['OK', 'FAILED', 'NOT-RUN'] },
    commit: { type: 'string' },
    notes: { type: 'string' },
  },
  required: ['items', 'build', 'commit', 'notes'],
}
function context(g) {
  const W = `${SP}/p4/${g.key}`
  return `You work on an Isabelle/HOL formalisation (repository root is your git worktree ${W}, branch p4-${g.key}, based on commit ${BASE}). It is phase 4 of notes/PLAN_RESTRUCTURING_3.md: "clones and verified simplifications". Read the plan's phase 4 section and rules (section 6) once. A first round already merged chunk 0 of groups G2, G3 and G5 into ${BASE} (see the progress log at the end of the plan); some items of your list may therefore already be done or obsolete — check before working, and report them as already-done.
Tools (use absolute paths):
- Build: ${SP}/p4/build.sh ${g.key} [SESSION ...]   builds the worktree's sessions with the worktree's own Isabelle home (only changed sessions and their descendants are rebuilt; with no SESSION argument every session is built). It prints the errors of failed sessions and BUILD: OK / BUILD: FAILED. Builds wait for one of two machine-wide build slots and can take long (a change in Symmetric_Matrix_Spectra or Continuous_Time_Martingales rebuilds everything downstream, about 25 minutes); run them in the foreground with a long timeout (up to 3600000 ms), and first build only the session you edited (e.g. build.sh ${g.key} Continuous_Path_Spaces) before the full build. Session names: Symmetric_Matrix_Spectra, Semicontinuous_Analysis, Second_Order_Viscosity_Analysis, Continuous_Time_Martingales, Wiener_Measure, Continuous_Path_Spaces, Relative_Arbitrage, Relative_Arbitrage_Statement.
- Statement check: python3 ${SP}/p4/stmt_check.py ${W}   lists, against ${BASE}, the facts removed, added, or whose statement text changed.
- To try a proof quickly without rebuilding a session: write a scratch theory under ${SP}/p4/scratch-${g.key}/ importing the theory's parents and run HOME=${SP}/p4/home-${g.key} ${SP}/tools/check_thy.sh <abs path> (it uses your worktree and your heaps; only use it for theories whose parents you have not changed since the last build).
Never edit /home/user/relative_arbitrage or another group's worktree. Never run "isabelle build" yourself with the default HOME.
Rules:
- Keep every fact named in notes/review_3/roots.txt (a roots change needs its own commit with the reason, and only when an item says so); keep the statements of Statement/*.thy unchanged. Never add sorry, oops or axioms.
- A fact you keep keeps exactly its statement (or a stronger one, only if every user still builds). A fact you delete (a twin or special case of a general lemma) must not be in roots.txt, and every use of it in any theory of the worktree must be re-pointed to the survivor (grep -rnw over all .thy files, including prose antiquotations @{thm ...}). You may edit files outside your group's area only to re-point such uses, with minimal edits (other groups edit those files too and the branches are merged later).
- COROLLARY items: keep the name and statement, replace the long proof by a short derivation from the general lemma, placed after the general lemma (moving it within the theory is fine).
- Gated items (gated: true) are pilots: do them, measure net lines saved (git diff --stat) and build time; keep the change only if net lines saved >= half the estimate and no proof got more than twice slower; otherwise revert that item and mark it abandoned with the measurements.
- Prose: update texts that describe what you changed; delete texts that describe deleted lemmas.
- Work item by item; build the session after every few items; when everything builds (full build OK), commit in the worktree with a clear message (what changed, lines saved) ending with these two lines:
Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_019j4751d6XLGjkHf9YnDfgY
  Commit after every few items that build (so an interruption loses little). Never commit a state that does not build. If an item cannot be done within reason, revert it and mark it skipped with the reason.
Your items are in ${SP}/p4/${g.key}-items.json ("items" maps id -> full item: summary, files, facts, general_lemma, evidence with line numbers from the scouting at commit 34e6d91 — re-locate them with grep —, checked_derivation pointing to machine-checked derivations, risk, gated).${g.wip ? `\nAn interrupted earlier attempt at chunk 0 of this group left UNVERIFIED edits on branch p4-${g.key}-wip (one commit on top of 34e6d91; its last build had not passed). You may consult it (git -C ${W} show p4-${g.key}-wip) and reuse parts that are correct, but verify everything.` : ''}`
}
async function runGroup(g) {
  const reports = []
  for (let c = g.start; c < g.chunks; c++) {
    const prev = reports.length ? `\nEarlier chunks of this round (already committed in the worktree):\n${reports.map((r, i) => `chunk ${g.start + i}: ${JSON.stringify(r)}`).join('\n')}\n` : ''
    const r = await agent(`${context(g)}
${prev}
Your task: implement chunk ${c} of ${g.chunks}: the item ids listed in "chunks"[${c}] of ${SP}/p4/${g.key}-items.json. Start with "git -C ${SP}/p4/${g.key} log --oneline -3" and "git status" to see where the worktree is (an interrupted earlier attempt may have left uncommitted edits: inspect them, keep what builds, revert the rest). End with a full build (build.sh ${g.key}) showing BUILD: OK and a commit. Return the per-item results.`,
      { label: `impl:${g.key}:${c}`, phase: 'Implement', schema: RESULT })
    reports.push(r)
  }
  return reports
}
const results = await pipeline(
  GROUPS,
  g => runGroup(g),
  (reports, g) => agent(`${context(g)}

You are the reviewer of group ${g.key} (${g.name}). The implementers' reports:
${reports.map((r, i) => `chunk ${g.start + i}: ${JSON.stringify(r)}`).join('\n')}

Review the branch p4-${g.key} against ${BASE} (git -C ${SP}/p4/${g.key} diff ${BASE} --stat, then the diff itself):
1. Run python3 ${SP}/p4/stmt_check.py ${SP}/p4/${g.key}. Every removed fact must be a twin or special case whose users were all re-pointed (grep the worktree) and must not be in notes/review_3/roots.txt or be a Statement theorem. Every CHANGED statement must be equivalent or stronger; read both versions. Restore anything that violates this.
2. No sorry, oops, axiomatization or ML escape was added (git diff | grep).
3. Gated items: check the measurements support keeping them; revert any that do not meet the gate.
4. Prose describes the new state; no text names a deleted lemma (grep the deleted names in the worktree).
5. A full build (${SP}/p4/build.sh ${g.key}) gives BUILD: OK on the final state; if you changed anything, commit (same trailer lines) after the build passes.
Return the per-item final status (taking your corrections into account) and the final commit.`,
    { label: `review:${g.key}`, phase: 'Review', schema: RESULT })
)
return GROUPS.map((g, i) => ({ group: g.key, review: results[i] }))
