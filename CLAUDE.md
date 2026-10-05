# language-design-handson

A hands-on course in programming language design using operational semantics.
Each chapter defines a small language in Lean 4 and formally verifies its properties (determinism, progress, preservation, type safety, agreement of big-step and small-step semantics).
The "tests" are the Lean proofs: `lake build Solutions` fails on any `sorry`.

# RTK (Rust Token Killer)

Prefix every shell command with `rtk`, including each command in an `&&` chain — it is always safe (a dedicated filter cuts noisy output for tests, builds, git, and more; anything without one passes through unchanged). The full command reference is in the global `~/.claude/RTK.md` (already loaded, if set up). Meta commands: `rtk gain` (savings so far), `rtk discover` (missed opportunities in past sessions), `rtk proxy <cmd>` (run unfiltered, for debugging).

## Working conventions

- Edit only `Solutions/`. `Handson/` is generated from it by `mise run gen`: lines between `-- 演習ここから` and `-- 演習ここまで` become `sorry`. Never edit `Handson/` by hand.
- Every exercise statement must stay provable without `sorry` in `Solutions/` (`warningAsError` is on for that library).
- Lean is installed by elan in `.devcontainer/Dockerfile`; the version is pinned in `lean-toolchain`. Use only Lean core (no Mathlib).
- Prose (README, Lean doc comments) is Japanese in the である style with `，` and `．`, checked by textlint for Markdown.

- `git commit` runs the lefthook hooks. If they fail, fix the reported issues. Do not use `--no-verify`.

- Run `mise run check` after making changes.

## Code map

- `Solutions/ChN*.lean`: chapter sources with complete proofs. `Solutions.lean` imports them all.
- `Handson/`: generated exercise copies (proofs replaced by `sorry`). `mise run handson` reports which chapters are complete.
- `scripts/gen-handson.mjs`: generator for `Handson/`; `--check` verifies it is in sync.
- `lakefile.toml`, `lean-toolchain`: Lean build configuration.

# Artifact Cleanup

## Golden Rule

**Whenever you produce an artifact, always run the `system-development-skills:finalize-artifacts` skill to clean it up before reporting the work as done.**

An artifact is any deliverable you create or substantially rewrite: documents, READMEs, code and code comments, config files, scripts, commit messages, PR descriptions, and so on.

- Invoke the skill via the Skill tool (`system-development-skills:finalize-artifacts`) after the artifact is written and before the final reply.
- The skill edits the artifact files in place. Do not append a changelog of the cleanup to the artifact; in the final reply, mention what changed in a sentence or two at most unless the user asks for a full report.
- Skip it only for replies that produce no artifact (answering questions, explaining code, running read-only commands).
- Provided by the `enunun/system-development-skills` plugin (see `extraKnownMarketplaces`/`enabledPlugins` in `.claude/settings.json`).
