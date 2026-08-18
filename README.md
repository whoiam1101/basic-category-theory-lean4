<div align="center">

# Formalization of Tom Leinster's *Basic Category Theory* in Lean 4

[![CI](https://github.com/whoiam1101/basic-category-theory-lean4/actions/workflows/ci.yml/badge.svg)](https://github.com/whoiam1101/basic-category-theory-lean4/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.30.0-blue?logo=lean&logoColor=white)](https://github.com/leanprover/lean4)
[![Mathlib 4](https://img.shields.io/badge/Mathlib_4-compatible-5C5CFF)](https://github.com/leanprover-community/mathlib4)
[![Sorries](https://img.shields.io/badge/sorries-0-brightgreen?logo=checkmarx&logoColor=white)](https://github.com/whoiam1101/basic-category-theory-lean4)
[![Axioms](https://img.shields.io/badge/axioms-standard_only-success)](https://github.com/whoiam1101/basic-category-theory-lean4)
[![Progress](https://img.shields.io/badge/progress-67%25%20(4%2F6%20Chapters)-orange)](https://github.com/whoiam1101/basic-category-theory-lean4#project-progress--todo-list)
[![Textbook](https://img.shields.io/badge/Textbook-arXiv%3A1612.09375-B31B1B.svg)](https://arxiv.org/abs/1612.09375)
[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

*A mathematically rigorous, fully computer-verified formalization of standard category theory in Lean 4.*

</div>

---

This repository contains a comprehensive, non-commercial formalization of Tom Leinster's textbook **"Basic Category Theory"** (Cambridge Studies in Advanced Mathematics, [arXiv:1612.09375](https://arxiv.org/abs/1612.09375)) using the Lean 4 interactive theorem prover and Mathlib 4.

> [!NOTE]
> **Strict Verification Guarantee**: Every theorem is fully formalized without `sorry` or `admit`, relying solely on the standard axioms of Lean 4 and Mathlib (dependent type theory with inductive types, propositional extensionality, quotients, and classical choice).

---

<!-- FORMALIZATION_METRICS_START -->
### 📊 Formalization Metrics & Proof Rigor

<div align="center">

![Progress](https://geps.dev/progress/73?dangerColor=800000&warningColor=ff8000&successColor=00aa00)

| Metric | Verified Value | Details |
| :--- | :---: | :--- |
| 📚 **Completed Chapters** | **4 / 6** (66%) | Ch. 1–4 fully formalized + Introduction |
| 📑 **Checklist Items Done** | **19 / 26** (73%) | Detailed section & exercise coverage |
| 🧮 **Formal Declarations** | **354** | `160` Theorems • `17` Lemmas • `169` Defs • `8` Instances |
| 📝 **Lean 4 Source Lines** | **5,628 LOC** | Verified across `14` modules in `BasicCategoryTheory/` |
| 🛡️ **Incomplete Proofs (`sorry`)** | **`0`** | Zero-sorry strict kernel verification |
| ⚖️ **Axioms Usage** | **Standard Only** | Classical logic & choice (no custom axioms) |
| 🤖 **Automated Checks (CI)** | **Passing** | `lake build`, signed commits, secret scan & zero-sorry gates |

</div>
<!-- FORMALIZATION_METRICS_END -->

---

## 📜 Key Formalized Theorems

| Textbook Reference | Mathematical Statement | Lean Declaration / File | Status |
| :--- | :--- | :--- | :---: |
| **Theorem 1.3.15** | Natural isomorphism and equivalence of categories | [`BasicCategoryTheory.Chapter1`](BasicCategoryTheory/Chapter1_CategoriesFunctorsAndNaturalTransformations/NaturalTransformations.lean) | ✅ Verified |
| **Theorem 2.2.5** | Adjunctions via unit/counit and triangle equations | [`theorem_2_2_5_forward`](BasicCategoryTheory/Chapter2_Adjoints/Adjoints.lean) | ✅ Verified |
| **Corollary 2.2.6** | Right/Left adjoint uniqueness up to unique natural isomorphism | [`corollary_2_2_6`](BasicCategoryTheory/Chapter2_Adjoints/Adjoints.lean) | ✅ Verified |
| **Proposition 2.3.4** | Adjunctions characterized by initial objects in comma categories | [`corollary_2_3_7`](BasicCategoryTheory/Chapter2_Adjoints/Adjoints.lean) | ✅ Verified |
| **Theorem 3.2.1** | Cantor's Theorem (no surjection $A \twoheadrightarrow \mathcal{P}(A)$) | [`theorem_3_2_1`](BasicCategoryTheory/Chapter3_InterludeOnSets/SmallAndLargeCategories.lean) | ✅ Verified |
| **Lemma 4.2.1** | **The Yoneda Lemma** ($\operatorname{Nat}(H_A, X) \cong X(A)$) | [`exercise_4_2_1`](BasicCategoryTheory/Chapter4_Representables/YonedaLemma.lean) | ✅ Verified |
| **Corollary 4.3.1** | Yoneda embedding is full and faithful | [`corollary_4_3_1_isIso_iff`](BasicCategoryTheory/Chapter4_Representables/ConsequencesOfTheYonedaLemma.lean) | ✅ Verified |
| **Corollary 4.3.6** | Isomorphism of representables implies isomorphism of objects | [`corollary_4_3_6`](BasicCategoryTheory/Chapter4_Representables/ConsequencesOfTheYonedaLemma.lean) | ✅ Verified |
| **Corollary 4.3.9** | Cayley's Theorem for small categories / group actions | [`corollary_4_3_9`](BasicCategoryTheory/Chapter4_Representables/ConsequencesOfTheYonedaLemma.lean) | ✅ Verified |
| **Lemma 5.1.35** | Monomorphisms characterized by pullback squares | [`lemma_5_1_35`](BasicCategoryTheory/Chapter5_Limits/LimitsAndExamples.lean) | ✅ Verified |

---

## 📋 Project Progress & Detailed Plan

The formalization maps precisely to the table of contents of Tom Leinster's *Basic Category Theory*.

- [x] **Introduction**
- [x] **1. Categories, functors and natural transformations**
  - [x] **1.1** Categories
  - [x] **1.2** Functors
  - [x] **1.3** Natural transformations
- [x] **2. Adjoints**
  - [x] **2.1** Definition and examples
  - [x] **2.2** Adjunctions via units and counits
  - [x] **2.3** Adjunctions via initial objects
- [x] **3. Interlude on sets**
  - [x] **3.1** Constructions with sets
  - [x] **3.2** Small and large categories
  - [x] **3.3** Historical remarks
- [x] **4. Representables**
  - [x] **4.1** Definitions and examples
  - [x] **4.2** The Yoneda lemma
  - [x] **4.3** Consequences of the Yoneda lemma
- [ ] **5. Limits**
  - [x] **5.1** Limits: definition and examples
  - [x] **5.2** Colimits: definition and examples
  - [ ] **5.3** Interactions between functors and limits
- [ ] **6. Adjoints, representables and limits**
  - [ ] **6.1** Limits in terms of representables and adjoints
  - [ ] **6.2** Limits and colimits of presheaves
  - [ ] **6.3** Interactions between adjoint functors and limits
- [ ] **Appendix: Proof of the general adjoint functor theorem (GAFT)**

---

## 🚀 Setup & Building

### Prerequisites

- [elan](https://github.com/leanprover/elan) — installs the pinned Lean toolchain (`v4.30.0` in `lean-toolchain`).

### Building the Project

```bash
git clone https://github.com/whoiam1101/basic-category-theory-lean4.git
cd basic-category-theory-lean4
lake exe cache get   # Download precompiled Mathlib cache
lake build           # Build and verify all formal proofs
```

`BasicCategoryTheory/Basic.lean` serves as the root import hub; running `lake build` compiles and verifies the entire repository.

---

## ⚖️ License

- **Formalization Code** (`BasicCategoryTheory/`): [Apache 2.0 License](LICENSE).
- **Textbook Content** (`textbook/`): Tom Leinster's **"Basic Category Theory"** ([arXiv:1612.09375](https://arxiv.org/abs/1612.09375)), licensed under [CC BY-NC-SA 4.0](LICENSE-CC-BY-NC-SA.md).
