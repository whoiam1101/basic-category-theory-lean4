# AGENTS.md

## Project: Formalization of Tom Leinster's "Basic Category Theory" in Lean 4

This repository contains a mathematically rigorous, fully computer-verified formalization of Tom Leinster's textbook *Basic Category Theory* (Cambridge Studies in Advanced Mathematics, [arXiv:1612.09375](https://arxiv.org/abs/1612.09375)) using Lean 4 (`v4.30.0`) and Mathlib.

---

## 🛠️ Build & Verification Commands

- **Build everything**: `lake build`
- **Fetch Mathlib cache**: `lake exe cache get`
- **Update README metrics**: `python3 scripts/update_readme_stats.py`

---

## 📜 Core Guidelines & Rules

### 1. Strict Proof Rigor
- **Zero `sorry` / `admit`**: Every formalized statement must have a complete, verified proof. No `sorry` or `admit` may remain in committed Lean files.
- **Standard axioms only**: Rely only on Lean 4 and Mathlib standard axioms (classical logic, propositional extensionality, quotients, classical choice). Do not introduce custom axioms.
- **No compiler warnings**: All code must compile cleanly (`lake build`) with zero errors and zero warnings.

### 2. Lightweight Tactics & Proof Style
- **Lightweight tactics**: Prefer direct, explicit, and lightweight proofs:
  - `fun ... => ...` for direct constructions.
  - `rw [...]`, `simp [...]`, `exact ...`, `apply ...` for tactical proofs.
  - `calc` blocks for equational reasoning.
- **Banned heavy automation**: Do not commit `aesop`, `grind`, or `omega` in final code. If automation is used during discovery, translate the result into lightweight tactic steps.
- **Leverage Mathlib**: Always check Mathlib for existing definitions and lemmas (e.g. `CategoryTheory.Category`, `IsIso`, adjunctions, limits) before writing custom proofs.

### 3. File & Source Integrity
- **Textbook immutability**: All files in `textbook/` (`*.tex`) are original reference sources and **must never be modified**.
- **Licensing**:
  - Code in `BasicCategoryTheory/`: Apache 2.0 (see [LICENSE](LICENSE)).
  - Textbook source in `textbook/`: CC BY-NC-SA 4.0 by Tom Leinster (see [LICENSE-CC-BY-NC-SA.md](LICENSE-CC-BY-NC-SA.md)).
- **No explanatory comments in `.lean` files**: Declarations should be self-documenting through clear names and precise type signatures.
- **File downloads**: Any temporary downloads or external references must go into `downloads/` (gitignored).

---

## 📂 Project Structure & Naming Conventions

```
BasicCategoryTheory/
├── Basic.lean                                              (Root import aggregator)
├── Introduction.lean                                       (Introduction)
├── Chapter1_CategoriesFunctorsAndNaturalTransformations/  (Chapter 1)
├── Chapter2_Adjoints/                                     (Chapter 2)
├── Chapter3_InterludeOnSets/                              (Chapter 3)
├── Chapter4_Representables/                               (Chapter 4)
├── Chapter5_Limits/                                       (Chapter 5)
├── Chapter6_AdjointsRepresentablesAndLimits/              (Chapter 6)
└── Appendix_GAFT/                                         (Appendix)
```

### Naming Conventions
- Match textbook numbering: `theorem_X_Y_Z`, `lemma_X_Y_Z`, `def_X_Y_Z`, `example_X_Y_Z`, `exercise_X_Y_Z` (e.g. `theorem_2_2_5`, `exercise_4_2_1`).
- Multi-part exercises use suffixes: `exercise_0_14_a`, `exercise_0_14_b`.
- Intermediate helper lemmas: use descriptive names (e.g. `exercise_2_2_18a_unit_injective`).
- Namespaces should mirror the chapter/section structure.

### Copyright Header
Every `.lean` file must include the standard header:
```lean
-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>
```

### Proof Decomposition
- Keep individual proofs clean and concise (aim for under ~50 lines). Extract complex intermediate steps into helper lemmas.
- When finalizing a file, replace broad imports with minimal imports using `#min_imports` before removing the command.

---

## 🔄 Agent Workflow (Step-by-Step)

When working on formalization tasks, follow this sequence:

1. **Identify next task**: Check `README.md` under **Project Progress & Detailed Plan** for the next incomplete item (`- [ ]`).
2. **Consult textbook**: Read the corresponding `.tex` section in `textbook/` to examine the mathematical statements and exercises.
3. **Formalize**: Implement definitions, theorems, and proofs in the relevant `BasicCategoryTheory/...` module.
4. **Compile & verify**:
   - Run `lake build` to confirm clean compilation.
   - Ensure zero warnings and zero `sorry`/`admit`.
5. **Update progress & metrics**:
   - Mark the completed item as `[x]` in `README.md`.
   - Run `python3 scripts/update_readme_stats.py` to synchronize README formalization metrics.
6. **Commit**:
   - Format: `[FORMALIZE] <Chapter/Section>: <brief description>`
   - Example: `[FORMALIZE] Chapter 5.2: Colimits, definition and examples`
