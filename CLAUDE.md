# CLAUDE.md

## Project: Formalization of Tom Leinster's "Basic Category Theory" in Lean 4

This project formalizes Tom Leinster's textbook *Basic Category Theory* (arXiv:1612.09375) using Lean 4 + mathlib.

- **Lean version**: `v4.30.0` (see `lean-toolchain`)
- **Build**: `lake build`
- **Textbook**: `textbook/` — contains only essential chapter `.tex` files + `macros.tex` (custom notation). All auxiliary files (`.pdf`, `.cls`, `.ind`, front/preface) have been removed. The `.tex` files are the original textbook source and **must never be modified**.

## License

- **Code** (`BasicCategoryTheory/`): Apache 2.0 — see `LICENSE`
- **Textbook** (`textbook/`): CC BY-NC-SA 4.0 by Tom Leinster — see `TEXTBOOK_LICENSE.md`. **Do not edit any `.tex` file in `textbook/`.**

## Project structure

```
BasicCategoryTheory/
├── Basic.lean                                              (imports)
├── Introduction.lean                                       (done)
└── Chapter1_CategoriesFunctorsAndNaturalTransformations/
    ├── Categories.lean                                     (section 1.1, done)
    ├── Functors.lean                                       (section 1.2, done)
    └── NaturalTransformations.lean                         (section 1.3)
```

## Proof decomposition

For complex theorems and exercises, decompose the proof into small, reusable lemmas instead of one long proof:

- **Split long proofs**: if a proof would exceed ~50 lines, extract intermediate statements as separate lemmas. No single theorem should carry hundreds of lines.
- **Name helper lemmas descriptively** (e.g. `exercise_2_2_18a_unit_injective`) so they can be reused by later declarations.
- **One lemma, one purpose**: each helper proves a single clear intermediate step (naturality of a component, injectivity of a map, a triangle identity, etc.).
- **Reuse across items**: if several textbook items share a sub-result, prove it once as a shared lemma and cite it in each.
- **Search before proving**: mathlib has 100k+ theorems — always search for existing lemmas before writing a proof from scratch (see Search tools below).

## Proof development workflow (complex items)

For complex theorems/exercises, develop proofs in two stages:

### Scratch-first (skeleton → parts → combine)

1. Create a scratch file `.claude/scratch/<name>.lean` (gitignored, never imported by the project, deleted after integration).
2. Write the **full decomposition skeleton** there: all helper lemmas and the final statement, proofs as `sorry`. In scratch files `sorry`/`admit` are **allowed** (the edit hook permits them only there); all other rules (no heavy tactics, no comments) apply everywhere.
3. Prove the parts bottom-up with the LSP (`lean_diagnostic_messages`, `lean_goal`); fill in sorries until the file is clean.
4. **Integrate**: copy the declarations into the real section file (the edit hook there blocks `sorry`, and the build/stamp gates enforce it) and delete the scratch file.

### Stuck proofs: multiple sketches + heavy automation for discovery only

When a proof resists 2–3 fix attempts, do not keep iterating on one approach:

1. **Generate several alternative sketches** — write 2–3 different proof sketches (different decomposition, different strategy) as separate declarations in the scratch file or separate scratch files, then keep the best (shortest, most direct, reuses existing lemmas) and delete the rest. The winner must still be self-contained and in the project style.
2. **Use heavy automation in-memory for discovery** — `aesop`/`grind`/`omega` are banned in committed and scratch `.lean` files by the edit hook, but `lean_multi_attempt` evaluates tactics **in memory without editing the file**. Run `grind` (optionally `set_option maxHeartbeats 2000000 in grind`), `omega`, `aesop` there on the stuck goal. If automation closes the goal, inspect how it did it and translate the closed proof into lightweight tactics (`simp`/`rw`/`change`/`exact`/`calc`) for the final code. Never commit the heavy tactics — only their lightweight translation.
3. For nested structure literals inside `fun X => { ... }`, continuation fields must be indented **deeper than the `{`** — shallower indentation makes the parser read the literal as implicit binders and fail with "expected '}'".

### Multi-file sections

When a section is large or has independent parts, split it into one file per part under the section's directory (e.g. `Chapter4_Representables/Definitions.lean`, `Examples.lean`, `Exercises.lean`); the main section file just imports the parts. `lakefile.toml` needs no changes — anything imported by the root `BasicCategoryTheory.lean` is built automatically. File boundaries are agent boundaries: one agent per file, so parts can be formalized in parallel.

### Agent contract (every formalization agent prompt must specify)

- The exact file(s) the agent may edit, and the item list with book numbers to cover.
- Anti-loop rules: one edit → diagnostics → next edit; never repeat a tool call; after 3 failed attempts on a proof move on; max 15 minutes per item; save edits to the file as you go.
- The verification duty: `lean_diagnostic_messages` clean (no errors, no warnings) before reporting.

## Search tools

Available tools for finding mathlib lemmas (via the lean-lsp MCP server):

- `lean_loogle` — pattern search by type signature (e.g. `(F ⊣ G) → ...`, `_ * (_ ^ _)`, `|- _ < _`) — 3 req/30s
- `lean_leansearch` — natural language → mathlib (e.g. "right adjoint full faithful iff counit iso") — 90 req/30s
- `lean_leanfinder` — semantic/conceptual search by mathematical meaning — 10 req/30s
- `lean_state_search` — goal-directed lemma search from a concrete proof state — 6 req/30s
- `lean_local_search` — fast local declaration-name prefix search (use BEFORE trying a lemma name)
- `lean_hammer_premise` — premise suggestions for automation tactics at a goal — 6 req/30s

ALWAYS search for existing lemmas (mathlib or earlier in this project) before proving anything from scratch. If mathlib already provides a lemma, use it directly.

### Local loogle (no rate limits)

A locally-built [loogle](https://github.com/nomeata/loogle) binary provides unlimited pattern search. Installation: clone the repo anywhere (e.g. `~/loogle`), copy this project's `lean-toolchain` into it, and run `lake build` there — loogle MUST be built with the exact toolchain that produced this project's `.olean` files. See README «Setup & Development» for full instructions.

Usage (from the project root, substituting the loogle checkout path):

```bash
# mathlib pattern search (index cached on disk after first run):
lake env <loogle-path>/.lake/build/bin/loogle --module Mathlib "<type pattern>"

# search this project's own declarations:
lake env <loogle-path>/.lake/build/bin/loogle --module BasicCategoryTheory.Chapter2_Adjoints.Adjoints "F ⊣ G"
```

Use it when the MCP `lean_loogle` rate limit (3/30s) is hit, or to search this project's own declarations. Pattern syntax: `_` matches any subexpression, `?a`/`?b` are type variables, `"substring"` matches names, `|- ...` matches the conclusion.

## Parallelization with subagents

When several independent sections are pending on the TODO list, launch one subagent per section (Agent tool with `run_in_background: true`):

- Each subagent works on its own `.lean` file (or its own disjoint section of a file) to avoid conflicts — never let two agents edit the same file simultaneously.
- Each subagent follows the session workflow below (read textbook → formalize → build → verify → independent verification subagent → update README → commit).
- Subagents that need the same mathlib lemmas work independently; they only share the TODO/README state.
- Skippable sections (e.g. historical remarks) can be handled by a quick agent that just marks the README.

## Session workflow — ONE task per session

Every session MUST follow this workflow:

### 1. Read the TODO list
Open `README.md` and locate the TODO list in the "Project Progress" section.

### 2. Find the first incomplete task
Scan top-to-bottom for the first `- [ ]` item. That is the ONE task for this session.

### 3. Do that task
- Read the corresponding section in the textbook (`textbook/`) to understand what needs to be formalized.
- Edit the corresponding `.lean` file. Match the existing code style: each theorem/example/exercise is a separate declaration with a descriptive name (e.g. `example_1_1_5`, `exercise_0_14_a`).
- Keep the copyright header and namespace structure.
- Use `import Mathlib` (the project already depends on mathlib).
- Prefer mathlib's existing definitions (`CategoryTheory.Category`, `IsIso`, etc.) over reinventing them.

### 4. Verify compilation
Run `lake build` and fix any errors. Use the Lean LSP tools (`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`) to debug proofs.

### 5. Self-verify against textbook
Before marking the task done, do a thorough self-check:
- Open the corresponding `.tex` file in `textbook/` and scan **every** definition, theorem, example, lemma, corollary, and exercise in the target section.
- Compare each against the `.lean` file: **every numbered item must have a corresponding declaration** with matching name (e.g. `example_1_1_5`, `exercise_1_1_13`, `lemma_1_2_3`).
- Verify that **type signatures match the textbook statements exactly**. For exercises, ensure the formal statement captures **exactly** what the textbook asks.
- If any item is missing, add it. If an item cannot be formalized (e.g. purely conceptual exercise, missing mathlib definition), skip it silently — no comments.

### 6. Eliminate warnings
Run `lean_diagnostic_messages` and fix all warnings. Warnings should not remain in the final code.

### 7. Independent verification subagent
Launch a subagent whose ONLY job is to verify **the new work of this session** — the files/diff changed in this session (`git status` / `git diff`), never a re-verification of the whole project from scratch. The verifier is **read-only**: it must not edit any file. It reports issues against this checklist:

1. **Completeness** — everything required by the task is present: every numbered item of the target textbook section (definitions, theorems, examples, lemmas, corollaries, exercises) has a corresponding declaration in the new work. Anything absent must fall under the silently-skipped policy (conceptual remarks, open-ended exercises, mathlib-unavailable definitions, unformalized dependencies).
2. **Fidelity to the book** — every new declaration's statement matches the textbook statement **exactly** (compare against `textbook/*.tex`): no weakened or strengthened claims; generalizations (e.g. `Ring` instead of `Field`) are acceptable only if the original statement is a special case.
3. **Proof correctness** — the file compiles without errors; no `sorry`, `admit`, or custom axioms (run `lean_verify` on the new theorems); the proof actually proves the stated statement (no vacuous or over-restricted hypotheses).
4. **Proof quality** — proofs are optimized: lightweight (`fun`, `calc`, `simp`, `rw`, `exact`, `apply`), no heavy automation (`aesop`, `grind`, `omega`), no unnecessary detours or unused hypotheses (no linter warnings), mathlib lemmas used where they exist.
5. **Naming & structure** — declaration names follow `example_X_Y_Z` / `exercise_X_Y_Z` / `lemma_X_Y_Z` / `def_X_Y_Z` and match the **book's numbering exactly**; declarations appear in textbook order; namespace structure and copyright header preserved; no comments in `.lean` files; no warnings (`lean_diagnostic_messages`).

If the verifier reports issues, fix them and re-run the verifier until it passes. When it passes, the verifier MUST finish by running `bash .claude/hooks/stamp-verification.sh` — this hard-checks (no `sorry`/`admit` anywhere, `lake build` succeeds, no warnings in the build log) and writes `.claude/verification-stamp`.

Only then proceed to commit. Hard enforcement (PreToolUse hooks in `.claude/settings.json`, not dependent on prompts):

- **`Edit|Write` is denied** for any path outside the project (the only outside exception is the Claude memory directory), and on `.lean` files it is additionally denied if the new content contains `sorry`, `admit`, `aesop`, `grind`, or `omega` (check: `.claude/hooks/check-lean-edit.sh`).
- **`Read` is denied** for any path outside the project, except the Lean-related locations: the elan toolchain (`~/.elan`), the local loogle checkout (`~/Documents/loogle`), `/tmp` scratch, and the Claude memory directory (check: `.claude/hooks/check-read-path.sh`).
- **`git commit` is denied** if any `.lean` file is changed (staged, unstaged, or untracked) unless the verification stamp exists and matches the current content hash exactly, and the changed files contain no `sorry`/`admit` (check: `.claude/hooks/check-commit.sh`). Commits that touch no `.lean` files (e.g. `[INFRA]` docs) are exempt.

### 8. Mark as done
Once the file compiles with no errors, no `sorry`, and no warnings, update `README.md`:
- Change `- [ ] **Section Name**` → `- [x] **Section Name**`
- If all subsections of a chapter are done, also mark the parent chapter as `[x]`.

### 9. Commit
Use the following commit format:
```
[FORMALIZE] <Chapter>: <brief description of what was formalized>
```
Examples:
```
[FORMALIZE] Introduction: Exercise 0.14a, 0.14b
[FORMALIZE] Chapter 1.1: Examples 1.1.8–1.1.11, Exercises 1.1.13–1.1.15
```
Run:
```bash
git add -A
git commit -m "[FORMALIZE] ..."
```

### 10. Stop
Do NOT start the next task. The session is done.

## Conventions

- **Names**: `example_X_Y_Z` for textbook examples, `exercise_X_Y_Z` for exercises, `lemma_X_Y_Z` for lemmas, `def_X_Y_Z` for custom definitions.
- **Namespaces**: match the chapter/section structure (e.g. `namespace Categories` for §1.1).
- **Copyright header**: include on every `.lean` file:
  ```lean
  -- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
  -- Released under Apache 2.0 license as described in the file LICENSE.
  -- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>
  ```
- **No comments in `.lean` files**: do not write explanatory comments in the code. The declarations should be self-documenting through their names and types.
- **Internet downloads**: anything fetched from the internet (curl/wget, PDFs, archives, external sources) must be stored inside the project under `downloads/` (gitignored) — never in the repo root, the home directory, or anywhere outside the project. After use, delete throwaway files (scratch PDFs, temp archives); keep only what later sessions genuinely need.
- **No warnings**: after `lake build` succeeds, run `lean_diagnostic_messages` and fix any warnings. Warnings must not remain.
- **Lightweight proofs**: use simple, explicit proofs. Prefer:
  - `fun ... => ...` for direct term-mode constructions
  - `rw [...]`, `simp [...]`, `exact ...`, `apply ...` for small tactic blocks
  - `calc` for equational reasoning
  Avoid heavy automation tactics like `grind`, `omega`, `aesop`. If mathlib already provides a lemma (e.g. `isIso_iff_bijective`), use it directly rather than re-proving from scratch.
- **Minimal imports**: when a file is finalized, replace the blanket `import Mathlib` with the minimal import set: append `#min_imports` at the end of the file, rebuild, take the suggested imports from the info diagnostic, apply them, then remove `#min_imports`. Do this after all content of the file is final (it must not be left in the committed code; `exact?`/`apply?`/`#min_imports` and other query commands must not remain in the final code either).
