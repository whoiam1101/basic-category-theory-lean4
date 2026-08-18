<div align="center">

# Formalization of Tom Leinster's *Basic Category Theory* in Lean 4

[![CI](https://github.com/whoiam1101/basic-category-theory-lean4/actions/workflows/ci.yml/badge.svg)](https://github.com/whoiam1101/basic-category-theory-lean4/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.30.0-blue?logo=lean&logoColor=white)](https://github.com/leanprover/lean4)
[![Mathlib 4](https://img.shields.io/badge/Mathlib_4-compatible-5C5CFF)](https://github.com/leanprover-community/mathlib4)
[![Sorries](https://img.shields.io/badge/sorries-0-brightgreen?logo=checkmarx&logoColor=white)](https://github.com/whoiam1101/basic-category-theory-lean4)
[![Axioms](https://img.shields.io/badge/axioms-standard_only-success)](https://github.com/whoiam1101/basic-category-theory-lean4)
[![Progress](https://img.shields.io/badge/progress-100%25%20(6%2F6%20Chapters)-brightgreen)](https://github.com/whoiam1101/basic-category-theory-lean4#project-progress--todo-list)
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

![Progress](https://geps.dev/progress/100?dangerColor=800000&warningColor=ff8000&successColor=00aa00)

| Metric | Verified Value | Details |
| :--- | :---: | :--- |
| 📚 **Completed Chapters** | **6 / 6** (100%) | Ch. 1–6 fully formalized + Introduction |
| 📑 **Checklist Items Done** | **26 / 26** (100%) | Detailed section & exercise coverage |
| 🧮 **Formal Declarations** | **496** | `208` Theorems • `21` Lemmas • `252` Defs • `15` Instances |
| 📝 **Lean 4 Source Lines** | **7,740 LOC** | Verified across `19` modules in `BasicCategoryTheory/` |
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
| **Lemma 5.3.6** | Creation of limits implies preservation of limits | [`lemma_5_3_6_preservesLimits`](BasicCategoryTheory/Chapter5_Limits/InteractionsBetweenFunctorsAndLimits.lean) | ✅ Verified |
| **Proposition 6.1.1** | Limits as representations of the cone functor ($\operatorname{Cone}(-, D) \cong \mathcal{A}(-, \lim D)$) | [`proposition_6_1_1_cone_iso_hom`](BasicCategoryTheory/Chapter6_AdjointsRepresentablesAndLimits/LimitsInTermsOfRepresentablesAndAdjoints.lean) | ✅ Verified |
| **Proposition 6.1.4** | Limit functor as right adjoint to diagonal functor ($\Delta \dashv \lim$) | [`proposition_6_1_4_adjunction`](BasicCategoryTheory/Chapter6_AdjointsRepresentablesAndLimits/LimitsInTermsOfRepresentablesAndAdjoints.lean) | ✅ Verified |
| **Theorem 6.2.9** | **The Density Theorem** (every presheaf is a colimit of representables) | [`theorem_6_2_9_isColimit_density`](BasicCategoryTheory/Chapter6_AdjointsRepresentablesAndLimits/LimitsAndColimitsOfPresheaves.lean) | ✅ Verified |
| **Theorem 6.3.1** | Right adjoints preserve limits, left adjoints preserve colimits | [`theorem_6_3_1_rightAdjoint_preservesLimits`](BasicCategoryTheory/Chapter6_AdjointsRepresentablesAndLimits/InteractionsBetweenAdjointFunctorsAndLimits.lean) | ✅ Verified |
| **Proposition 6.3.7** | Adjoint Functor Theorem for Ordered Sets | [`proposition_6_3_7_oaft_galoisConnection`](BasicCategoryTheory/Chapter6_AdjointsRepresentablesAndLimits/InteractionsBetweenAdjointFunctorsAndLimits.lean) | ✅ Verified |
| **Theorem 6.3.10** | General Adjoint Functor Theorem (GAFT) | [`theorem_6_3_10_gaft_backward`](BasicCategoryTheory/Chapter6_AdjointsRepresentablesAndLimits/InteractionsBetweenAdjointFunctorsAndLimits.lean) | ✅ Verified |
| **Theorem 6.3.20** | Presheaf categories are cartesian closed | [`theorem_6_3_20_presheaf_cartesian_closed`](BasicCategoryTheory/Chapter6_AdjointsRepresentablesAndLimits/InteractionsBetweenAdjointFunctorsAndLimits.lean) | ✅ Verified |
| **Lemma A.1** | Complete category with weakly initial set has initial object | [`lemma_A_1_isInitial_of_isLimit`](BasicCategoryTheory/Appendix_ProofOfTheGeneralAdjointFunctorTheorem.lean) | ✅ Verified |

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
- [x] **5. Limits**
  - [x] **5.1** Limits: definition and examples
  - [x] **5.2** Colimits: definition and examples
  - [x] **5.3** Interactions between functors and limits
- [x] **6. Adjoints, representables and limits**
  - [x] **6.1** Limits in terms of representables and adjoints
  - [x] **6.2** Limits and colimits of presheaves
  - [x] **6.3** Interactions between adjoint functors and limits
- [x] **Appendix: Proof of the general adjoint functor theorem (GAFT)**

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
