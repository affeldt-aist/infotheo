# Infotheo Project Instructions

## Compilation Safety (CRITICAL)
Each `rocqworker` process uses 2-10+ GB RAM (MathComp imports are huge).
Concurrent compilations WILL crash the machine (24 GB RAM).

Rules:
1. **Before ANY `make` command**: Run `ps aux | grep rocqworker | grep -v grep` — if ANY rocqworker is running, DO NOT compile. Wait or ask the user.
2. **Before ANY `make` command**: Also check `ps aux | grep pet | grep -v grep` — if a `pet` process is running (from rocq-mcp), DO NOT compile. Kill stale `pet` processes first with `kill <pid>`. **NOTE**: Killing `pet` also kills the rocq-mcp MCP server connection — after killing `pet`, the user must run `/mcp` to reconnect before rocq-mcp tools work again.
3. **Always use `make -j1`** (not `-j4`) for single-file compilation — this limits to 1 rocqworker.
4. **Never launch parallel compilation agents** — only one agent should compile at a time.

## Proof Writing Rules (CRITICAL)
- **NEVER use `rewrite !lemma`** (bang `!` modifier) with arithmetic lemmas like `addn1`, `addnA`, `subnK`, etc. The `!` causes exponential rewriting on nat terms and can consume 60+ GB RAM, crashing the machine. Use explicit rewrites instead (e.g., `rewrite addn1 addnA` not `rewrite !addn1 !addnA`).
- `rewrite !lemma` is only safe with lemmas that apply at most a bounded number of times (e.g., `!inE`, `!mem_filter`).
- **NEVER use `lia`** — it is NOT available in this project. Use MathComp nat lemmas.
- **NEVER use `move/eqP` on Prop equalities** from `ltngtP`, `eqVneq`, `leqP`. These already produce Prop `m = n`. Use directly with `subst`/`rewrite`.
- **`ring_scope` warning**: `dumas2017dual/dsdp/dsdp_progress.v` has `Local Open Scope ring_scope`. Use `%N` for nat operations in ranking functions and arithmetic goals.
- **Rewrite order**: When unfolding rank/pose functions, unfold BEFORE substituting extracted equalities. E.g., `rewrite /rank Hi0 -Hjeq /=` not `rewrite -Hjeq /rank`.
- **Use `Show`** to inspect goals, **`apply I`** for type mismatches. Never guess what a goal looks like.
- **Use `apply ` and `exact `** (space, not colon) for better error messages when debugging.

## Proof Debugging Rules (CRITICAL)
- **Use `Show`** to inspect goals — NEVER guess what a goal looks like.
- **Use `apply ` and `exact `** (space, not colon) for better error messages.
- **Use `Locate`, `Check`, `About`, `Print`, `Search`** to find lemmas — don't assume names.
- **Do NOT seek "smarter" strategies** when tactics fail. Fix the failing tactic step directly.

## Revert Discipline (CRITICAL)
**REVERT_COUNT = 0** at the start of each task.

A "revert" is any `git checkout`, `git restore`, or discarding proof work due to complexity.

**Before ANY revert:**
1. **MUST `git commit` first** — preserve all current work, even if broken.
2. Increment REVERT_COUNT.
3. If REVERT_COUNT >= 2 in one round: **STOP reverting**. Instead, revise the strategy to achieve the goal from the current state. Explain what repeatedly failed and propose a new approach.

**This rule applies to both the main agent and all subagents.**

## Agent Permissions
Subagents inherit the parent session's permissions. Before launching long-running
subagents (e.g., `rocq-expert-prover`), verify:
1. `Edit` and `Write` are in `~/.claude/settings.json` allow list (user-level)
2. `Bash(make:*)`, `Bash(rm:*)`, `Bash(ps aux:*)` are in `.claude/settings.local.json` (project-level)
3. If an agent reports permission denials, do NOT resume it — fix permissions first, then launch a fresh agent (resumed agents keep the old permission state)

## Build System
- Single file: `make -j1 <path>.vo`
- Force recompile: `rm -f <path>.vo` first if needed
- Paths: `-R . infotheo -R pgg-smc/... pgg_smc`

## Launching rocq-prover (Best Practices)
When launching `rocq-prover`, the parent MUST include in the prompt:
1. **Pre-built `.vo` dependencies status** — confirm that all imports are already compiled so the agent doesn't waste time on dependency builds.
2. **Exact line range** of the target lemma(s) (e.g., "lines 2340-2380 in pgg_raag.v").
3. **Section context** — list all `Variable`s and `Hypothesis`es in scope for the target lemma.
4. **Budget statement** — e.g., "You have a budget of 60 turns. Use `rocq_check`/`rocq_step_multi` for all intermediate testing. Maximum 2 full-file compilations."
5. **Explicit rocq-mcp reminder** — "Use the 4-phase workflow: `rocq_start` → explore with `rocq_query` → build proof with `rocq_check`/`rocq_step_multi` → apply once to real file."
