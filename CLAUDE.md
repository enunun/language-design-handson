# language-design-handson

A hands-on course in programming language design with operational semantics, built with the `build-handson` skill of `enunun/system-development-skills`.
Learners grow an interpreter for a small functional language, Mini, in Lean 4 over Iterations 0–8. All tests are Lean theorems.
`COURSE.md` is the course plan (conventions, layout, commands, pitfalls) and `docs/ROADMAP.md` is the per-Iteration specification. Read both before changing course material.

# RTK (Rust Token Killer)

Prefix every shell command with `rtk`, including each command in an `&&` chain — it is always safe (a dedicated filter cuts noisy output for tests, builds, git, and more; anything without one passes through unchanged). The full command reference is in the global `~/.claude/RTK.md` (already loaded, if set up). Meta commands: `rtk gain` (savings so far), `rtk discover` (missed opportunities in past sessions), `rtk proxy <cmd>` (run unfiltered, for debugging).

## Working conventions

- Build or change Iterations by following the `build-handson` skill (`system-development-skills:build-handson`). When the plugin is not loaded, read `skills/build-handson/` in `enunun/system-development-skills` directly.
- What an Iteration builds comes only from its section of `docs/ROADMAP.md`; conventions come only from `COURSE.md`. Change either with the user first.
- Iteration N's exercise must equal Iteration N-1's solution, except for the files `mise run check-exercises` ignores.
- Lean is installed by elan in `.devcontainer/Dockerfile`; the version is pinned in `lean-toolchain` at the repository root. Use only Lean core (no Mathlib).
- Prove string-input examples with `decide +kernel`, never `native_decide` (see the pitfalls in `COURSE.md`).
- Prose is Japanese in the である style with `，` and `．`, checked by textlint. Display math goes in ```` ```math ```` blocks.
- Copy every Lean, REPL and command output shown in the material from a real run.
- `git commit` runs the lefthook hooks. If they fail, fix the reported issues. Do not use `--no-verify`.
- Run `mise run check` after making changes.

## Code map

- `iterations/iteration-N/{exercise,solution}/`: one Lake package each (`Mini` library, `MiniTest` test library, `mini` executable), with `README.md`, `TESTLIST.md`, `design/` and `docs/iteration-N.md`.
- `docs/`: `ROADMAP.md`, `tdd.md`, `design.md`, and per-Iteration notes in `docs/lean/` and `docs/semantics/`.
- `scripts/`: material checks run by mise tasks: `check-diagrams.mjs` and `check-math.mjs` (lint), `check-design.mjs` (design documents vs code), `check-exercises.mjs` (exercise vs previous solution).

# Artifact Cleanup

## Golden Rule

**Whenever you produce an artifact, always run the `system-development-skills:finalize-artifacts` skill to clean it up before reporting the work as done.**

An artifact is any deliverable you create or substantially rewrite: documents, READMEs, code and code comments, config files, scripts, commit messages, PR descriptions, and so on.

- Invoke the skill via the Skill tool (`system-development-skills:finalize-artifacts`) after the artifact is written and before the final reply.
- The skill edits the artifact files in place. Do not append a changelog of the cleanup to the artifact; in the final reply, mention what changed in a sentence or two at most unless the user asks for a full report.
- Skip it only for replies that produce no artifact (answering questions, explaining code, running read-only commands).
- Provided by the `enunun/system-development-skills` plugin (see `extraKnownMarketplaces`/`enabledPlugins` in `.claude/settings.json`).
