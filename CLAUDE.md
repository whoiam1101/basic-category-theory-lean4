# CLAUDE.md

## Project: Formalization of Tom Leinster's "Basic Category Theory" in Lean 4

This project formalizes Tom Leinster's textbook *Basic Category Theory* (arXiv:1612.09375) using Lean 4 + mathlib.

- **Lean version**: `v4.30.0` (see `lean-toolchain`)
- **Build**: `lake build`
- **Textbook**: `textbook/arXiv-1612.09375v2/` — contains only essential chapter `.tex` files + `macros.tex` (custom notation). All auxiliary files (`.pdf`, `.cls`, `.ind`, front/preface) have been removed.

## Project structure

```
BasicCategoryTheory/
├── Basic.lean                                              (imports)
├── Introduction.lean                                       (done)
└── Chapter1_CategoriesFunctorsAndNaturalTransformations/
    ├── Categories.lean                                     (section 1.1, done)
    ├── Functors.lean                                       (section 1.2)
    └── NaturalTransformations.lean                         (section 1.3)
```

## Session workflow — ONE task per session

Every session MUST follow this workflow:

### 1. Read the TODO list
Open `README.md` and locate the TODO list in the "Project Progress" section.

### 2. Find the first incomplete task
Scan top-to-bottom for the first `- [ ]` item. That is the ONE task for this session.

### 3. Do that task
- Read the corresponding section in the textbook (`textbook/arXiv-1612.09375v2/`) to understand what needs to be formalized.
- Edit the corresponding `.lean` file. Match the existing code style: each theorem/example/exercise is a separate declaration with a descriptive name (e.g. `example_1_1_5`, `exercise_0_14_a`).
- Keep the copyright header and namespace structure.
- Use `import Mathlib` (the project already depends on mathlib).
- Prefer mathlib's existing definitions (`CategoryTheory.Category`, `IsIso`, etc.) over reinventing them.

### 4. Verify compilation
Run `lake build` and fix any errors. Use the Lean LSP tools (`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`) to debug proofs.

### 5. Self-verify against textbook
Before marking the task done, do a thorough self-check:
- Open the corresponding `.tex` file in `textbook/arXiv-1612.09375v2/` and scan all definitions, theorems, examples, lemmas, and exercises in the target section.
- Compare each against the `.lean` file: every numbered item must have a corresponding declaration with matching name (e.g. `example_1_1_5`, `exercise_1_1_13`).
- Verify that type signatures match the textbook statements. For exercises, ensure the formal statement captures exactly what the textbook asks.
- If any item is missing, add it. If an item cannot be formalized (e.g. purely conceptual exercise, missing mathlib definition), skip it silently — no comments.

### 6. Mark as done
Once the file compiles with no errors and no `sorry`, update `README.md`:
- Change `- [ ] **Section Name**` → `- [x] **Section Name**`

### 7. Commit
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

### 8. Stop
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
- **Lightweight proofs**: use simple, explicit proofs. Prefer:
  - `fun ... => ...` for direct term-mode constructions
  - `rw [...]`, `simp [...]`, `exact ...`, `apply ...` for small tactic blocks
  - `calc` for equational reasoning
  Avoid heavy automation tactics like `grind`, `omega`, `aesop`. If mathlib already provides a lemma (e.g. `isIso_iff_bijective`), use it directly rather than re-proving from scratch.
