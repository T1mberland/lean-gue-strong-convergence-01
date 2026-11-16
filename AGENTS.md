# AGENTS.md — GUE strong convergence

## Objective

Formalize the (fixed matrix-coefficient dimension) almost-sure strong convergence of normalized GUE in Lean. All completed mathematical results must be kernel-checked: no `sorry`, `admit`, new mathematical axioms, unsafe shortcuts, or statements that quietly assume their intended conclusion.

## Repository boundary — mandatory

- **Only authorized GitHub repository for this project:** `minitimber/lean-gue-strong-convergence`.
- The agent's GitHub account is `minitimber`. Before *any* fetch, push, PR, merge, or other GitHub operation, verify that the repository target is under `minitimber`, and that `origin` points to `minitimber/lean-gue-strong-convergence`. If it does not, STOP Git operations and report the mismatch; never guess, redirect to `T1mberland`, or change credentials.
- All project source changes, branches, PRs, and commits must be in this one target repository. Do not clone, open, browse through GitHub APIs, push to, or modify any other account's repository. This includes `T1mberland` repositories.
- Existing **read-only Lake dependency checkouts** under this project's `.lake/packages/` may be imported and inspected to build the target. Do not modify, commit to, or run arbitrary git commands in a dependency checkout. Standard read-only resolution of **already pinned** dependencies is permitted only if the execution environment allows it. If unavailable, report the blocker; do not work around access restrictions.
- No scanning of sibling directories, `$HOME`, `.ssh`, credentials, tokens, or unrelated projects. Do not change SSH, firewall, sandbox, login, or system settings to obtain access.

## Working method

- Read `CURRENT_TASK.md` after this file; treat detailed Part I/II handoffs as mathematical references, not a simultaneous task list.
- Begin from an up-to-date local `main` of the authorized target, but do substantial development on a focused feature branch. Keep `main` the verified integration branch.
- Prefer existing, actually compiled lemmas in the current repository, Mathlib, or installed read-only Lake dependencies. Check exact types and hypotheses before reuse.
- Choose one small, useful lemma; implement it, compile it, check proof integrity and theorem strength, commit and push a meaningful change, then update `CURRENT_TASK.md` and repeat. Do not spend an entire session repeatedly planning or reading the same files.
- If blocked, record the exact target, error, and gap; try an independent prerequisite rather than repeatedly restating the plan. Never weaken a theorem or add an assumption merely to make it compile.
- Run relevant Lean builds before claiming a theorem verified; run the full build and transitive axiom audit before integration. `#print axioms` is evidence, not by itself a rejection check for bad axioms.

## Git and multi-agent workflow

- Review `git diff` and `git status`; commit focused changes and push every commit to the **verified `minitimber` remote** so progress is visible. Never force-push or discard existing verified work as part of a restart.
- For truly independent parallel tasks, use separate branches and worktrees *inside the authorized project workspace*. Subagents obey exactly the same repository and secret-access boundaries.
- Each subagent may submit a PR to `minitimber/lean-gue-strong-convergence`; only the main agent may integrate changes, after reviewing the PR/diff and confirming Lean builds and proof audits pass.
- Keep incomplete experimental results on feature branches, accurately labeled; never merge unverified work into `main`.

## Autonomous multi-agent orchestration

These instructions apply to the top-level orchestrator.

### Delegation-first execution

- The orchestrator is responsible for planning, delegation, supervision,
  mathematical quality control, and integration.
- After checking the authorized Git remote and reading the current task
  summary, immediately spawn two subagents for independent useful tasks.
- Use the actual `subagent` tool, not merely a written delegation plan.
- Do not postpone delegation until you understand the entire repository.
  Delegate bounded investigations or implementation tasks immediately.
- If delegation is unavailable, report the exact tool/configuration problem.
  Do not silently switch to prolonged single-agent execution.

### Parallelism

- Maintain two productive, non-overlapping workers when feasible.
- Assign each worker a concrete mathematical milestone, distinct files,
  a separate Git branch, and an isolated worktree.
- Check existing worktree and branch ownership before assigning tasks.
- Subagents must obey all repository, security, and proof-integrity rules.
- Start another independent task when a worker finishes, when useful.
- The orchestrator should investigate blockers, verify results, and
  integrate work rather than repeat the workers' investigations.

### Efficient context management

- At startup read only the current summary at the beginning of
  CURRENT_TASK.md (approximately the first 140 lines).
- The remainder is historical reference material, not mandatory reading.
- Read specific historical sections only when relevant.
- Never repeatedly ingest the complete CURRENT_TASK.md.
- Avoid unnecessary repository-wide searches and repeated planning.
- Keep current progress summaries short and verifiable.

### Git and verification

- Preserve the authorized minitimber-only repository boundary.
- Work on feature branches; maintain main as the verified integration branch.
- Commit and push each meaningful, verified milestone.
- Keep incomplete work on its feature branch.
- Run the relevant Lean build and proof-integrity checks.
- Verify mathematical statements, not merely successful compilation.
- Never claim completion while mathematical gaps remain.

### Long-running behavior

- Continue pursuing the mathematical objective autonomously.
- Prefer completed, kernel-checked milestones over reports or plans.
- When blocked, isolate the precise mathematical obstruction and
  redirect available workers toward independent prerequisites.
- Report concise progress, branch names, commits, verified results,
  and remaining obstacles.

