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

A locally-built loogle binary (same Lean toolchain as this project) provides unlimited pattern search:

```bash
lake env ~/Documents/loogle/.lake/build/bin/loogle --module Mathlib "<type pattern>"
lake env ~/Documents/loogle/.lake/build/bin/loogle --module BasicCategoryTheory.Chapter2_Adjoints.Adjoints "F ⊣ G"
```

Use it when the MCP `lean_loogle` rate limit (3/30s) is hit, or to search this project's own declarations. The Mathlib index is cached on disk; the first query against a new module builds its index.

## Parallelization with subagents

When several independent sections are pending on the TODO list, launch one subagent per section (Agent tool with `run_in_background: true`):

- Each subagent works on its own `.lean` file (or its own disjoint section of a file) to avoid conflicts — never let two agents edit the same file simultaneously.
- Each subagent follows the session workflow below (read textbook → formalize → build → verify → update README → commit).
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

### 7. Mark as done
Once the file compiles with no errors, no `sorry`, and no warnings, update `README.md`:
- Change `- [ ] **Section Name**` → `- [x] **Section Name**`
- If all subsections of a chapter are done, also mark the parent chapter as `[x]`.

### 8. Commit
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

### 9. Stop
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
- **No warnings**: after `lake build` succeeds, run `lean_diagnostic_messages` and fix any warnings. Warnings must not remain.
- **Lightweight proofs**: use simple, explicit proofs. Prefer:
  - `fun ... => ...` for direct term-mode constructions
  - `rw [...]`, `simp [...]`, `exact ...`, `apply ...` for small tactic blocks
  - `calc` for equational reasoning
  Avoid heavy automation tactics like `grind`, `omega`, `aesop`. If mathlib already provides a lemma (e.g. `isIso_iff_bijective`), use it directly rather than re-proving from scratch.
