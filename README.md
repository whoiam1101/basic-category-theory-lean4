# basic-category-theory-lean4
This repository contains a comprehensive, non-commercial formalization of Tom Leinster's textbook **"Basic Category Theory"** (Cambridge Studies in Advanced Mathematics, [arXiv:1612.09375](https://arxiv.org/abs/1612.09375)) using the Lean 4 interactive theorem prover.

## Project Progress & TODO List

The formalization maps precisely to the table of contents of Tom Leinster's *Basic Category Theory*. Each sub-item tracks the formalization of the corresponding theoretical definitions/theorems, concrete examples, and end-of-chapter exercises.

- [x] **Introduction**
- [x] **1. Categories, functors and natural transformations**
  - [x] **1.1** Categories
  - [x] **1.2** Functors
  - [x] **1.3** Natural transformations
- [ ] **2. Adjoints**
  - [x] **2.1** Definition and examples
  - [x] **2.2** Adjunctions via units and counits
  - [ ] **2.3** Adjunctions via initial objects
- [ ] **3. Interlude on sets**
  - [ ] **3.1** Constructions with sets
  - [ ] **3.2** Small and large categories
  - [ ] **3.3** Historical remarks
- [ ] **4. Representables**
  - [ ] **4.1** Definitions and examples
  - [ ] **4.2** The Yoneda lemma
  - [ ] **4.3** Consequences of the Yoneda lemma
- [ ] **5. Limits**
  - [ ] **5.1** Limits: definition and examples
  - [ ] **5.2** Colimits: definition and examples
  - [ ] **5.3** Interactions between functors and limits
- [ ] **6. Adjoints, representables and limits**
  - [ ] **6.1** Limits in terms of representables and adjoints
  - [ ] **6.2** Limits and colimits of presheaves
  - [ ] **6.3** Interactions between adjoint functors and limits
- [ ] **Appendix: Proof of the general adjoint functor theorem (GAFT)**

Some items from the textbook are **silently skipped** and not reflected in the TODO list. This applies to:
- purely conceptual remarks, discussion paragraphs, and open-ended «find examples» exercises;
- items whose formalization would require definitions or categories not available in mathlib (e.g. the category of fields);
- constructions that depend on results not yet formalized (e.g. the General Adjoint Functor Theorem);
- items that are mathematically straightforward but whose formalization is disproportionately complex and would not add insight.

## License

This project's code (the Lean formalization in `BasicCategoryTheory/`) is licensed under the [Apache 2.0 License](LICENSE).

The textbook content in `textbook/` — Tom Leinster's **"Basic Category Theory"** (Cambridge Studies in Advanced Mathematics, Vol. 143, Cambridge University Press, 2014; [arXiv:1612.09375](https://arxiv.org/abs/1612.09375)) — is licensed under the [Creative Commons Attribution-NonCommercial-ShareAlike 4.0 International License](https://creativecommons.org/licenses/by-nc-sa/4.0/) (CC BY-NC-SA 4.0). See [TEXTBOOK_LICENSE.md](TEXTBOOK_LICENSE.md).
