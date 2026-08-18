# AGENTS.md

## Project: Formalization of Tom Leinster's "Basic Category Theory" in Lean 4

Mathematically rigorous, computer-verified formalization of Tom Leinster's *Basic Category Theory* (Cambridge Studies in Advanced Mathematics) in Lean 4 (`v4.30.0`) and Mathlib.

---

## 🛠️ Commands

- **Build**: `lake build`
- **Mathlib cache**: `lake exe cache get`
- **Update metrics**: `python3 scripts/update_readme_stats.py`

---

## 📜 Core Rules

1. **Zero `sorry` / `admit`**: Every statement must have a complete, verified proof with zero errors and zero warnings.
2. **Standard axioms only**: Standard Lean 4 / Mathlib axioms only (no custom axioms).
3. **Lightweight tactics**: Prefer `fun ... => ...`, `exact`, `apply`, `rw`, `simp`, `calc`. Check Mathlib before writing custom constructions.
4. **No explanatory comments**: Declarations must be self-documenting via clear names and signatures.
5. **Textbook immutability**: Files in `textbook/` are reference sources and must never be edited.
6. **Naming convention**: Follow textbook numbering (`def_X_Y_Z`, `theorem_X_Y_Z`, `lemma_X_Y_Z`, `example_X_Y_Z`, `exercise_X_Y_Z`).

### Header Template
Every `.lean` file must start with:
```lean
-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>
```

---

## 🔄 Workflow

1. **Read source**: Check `README.md` for the next task (`- [ ]`) and read the corresponding `.tex` section in `textbook/`.
2. **Parallel subagents**: Whenever possible, launch parallel subagents to distribute tasks (e.g. proof discovery, proving independent lemmas/exercises in parallel).
3. **Scratch file development in `tmp/`**:
   - Store all temporary scratch files in `tmp/` (e.g. `tmp/scratch_*.lean`).
   - `tmp/` is gitignored and must never enter the `.git` history.
   - Draft and verify statements and proofs incrementally in `tmp/` using `lake build`.
4. **Assemble & Integrate**:
   - Combine all verified proofs into the designated module under `BasicCategoryTheory/`.
   - Ensure the module is properly imported in `BasicCategoryTheory/Basic.lean`.
   - Clean up any temporary files in `tmp/`.
5. **Final Verification**:
   - Run `lake build` (must finish with 0 errors and 0 warnings).
6. **Update README & Stats**:
   - Mark completed item as `[x]` in `README.md`.
   - Run `python3 scripts/update_readme_stats.py`.
