-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib

namespace Adjoints

universe u v u' v'

open CategoryTheory
open Limits

abbrev def_2_1_1 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) (G : D ⥤ C) := F ⊣ G

noncomputable abbrev example_2_1_3b (k : Type u) [Field k] :
    ModuleCat.free k ⊣ forget (ModuleCat.{u} k) :=
  ModuleCat.adj k

abbrev example_2_1_3c :
    GrpCat.free ⊣ forget GrpCat.{u} :=
  GrpCat.adj

abbrev example_2_1_3d :
    GrpCat.abelianize ⊣ forget₂ CommGrpCat GrpCat.{u} :=
  GrpCat.abelianizeAdj

abbrev example_2_1_3e_U_R :
    forget₂ GrpCat MonCat.{u} ⊣ MonCat.units :=
  GrpCat.forget₂MonAdj

abbrev example_2_1_5_D_U :
    TopCat.discrete ⊣ forget TopCat.{u} :=
  TopCat.adj₁

abbrev example_2_1_5_U_I :
    forget TopCat.{u} ⊣ TopCat.trivial :=
  TopCat.adj₂

noncomputable def example_2_1_6 (B : Type u) : MonoidalCategory.tensorLeft B ⊣ ihom B :=
  ihom.adjunction B

abbrev def_2_1_7_initial {C : Type u} [Category.{v} C] (I : C) := IsInitial I

abbrev def_2_1_7_terminal {C : Type u} [Category.{v} C] (T : C) := IsTerminal T

def lemma_2_1_8_initial {C : Type u} [Category.{v} C] {I I' : C}
    (hI : IsInitial I) (hI' : IsInitial I') : I ≅ I' :=
  hI.uniqueUpToIso hI'

def lemma_2_1_8_terminal {C : Type u} [Category.{v} C] {T T' : C}
    (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T' :=
  hT.uniqueUpToIso hT'

def adjunction_comp {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {E : Type u} [Category.{v} E] {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) : F ⋙ H ⊣ I ⋙ G :=
  adj₁.comp adj₂

theorem exercise_2_1_12 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    ((∀ {A : C} {B B' : D} (g : F.obj A ⟶ B) (q : B ⟶ B'),
      adj.homEquiv A B' (g ≫ q) = adj.homEquiv A B g ≫ G.map q) ∧
     (∀ {A A' : C} {B : D} (p : A' ⟶ A) (f : A ⟶ G.obj B),
      (adj.homEquiv A' B).symm (p ≫ f) = F.map p ≫ (adj.homEquiv A B).symm f)) ↔
    (∀ {A A' : C} {B B' : D} (p : A' ⟶ A) (f : A ⟶ G.obj B) (q : B ⟶ B'),
      (adj.homEquiv A' B').symm (p ≫ f ≫ G.map q) =
      F.map p ≫ (adj.homEquiv A B).symm f ≫ q) := by
  constructor
  · intro ⟨h_nat_a, h_nat_b⟩ A A' B B' p f q
    have h_key : (adj.homEquiv A B').symm (f ≫ G.map q) = (adj.homEquiv A B).symm f ≫ q := by
      apply (adj.homEquiv A B').injective
      rw [Equiv.apply_symm_apply]
      rw [h_nat_a ((adj.homEquiv A B).symm f) q, Equiv.apply_symm_apply]
    calc
      (adj.homEquiv A' B').symm (p ≫ f ≫ G.map q) =
          (adj.homEquiv A' B').symm (p ≫ (f ≫ G.map q)) := by rfl
      _ = F.map p ≫ (adj.homEquiv A B').symm (f ≫ G.map q) := h_nat_b p (f ≫ G.map q)
      _ = F.map p ≫ ((adj.homEquiv A B).symm f ≫ q) := by rw [h_key]
      _ = F.map p ≫ (adj.homEquiv A B).symm f ≫ q := by rfl
  · intro h_single
    constructor
    · intro A B B' g q
      have h := h_single (𝟙 A) (adj.homEquiv A B g) q
      simpa using congrArg (adj.homEquiv A B') h.symm
    · intro A A' B p f
      have h := h_single p f (𝟙 B)
      simpa using h

noncomputable def exercise_2_1_13_left {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {I : C} (hI : IsInitial I) : IsInitial (F.obj I) := by
  haveI : ∀ Y : D, Unique ((F.obj I) ⟶ Y) := by
    intro Y
    refine
      { default := (adj.homEquiv I Y).symm (hI.to (G.obj Y))
        uniq := fun g => ?_ }
    apply (adj.homEquiv I Y).injective
    have : adj.homEquiv I Y g = hI.to (G.obj Y) := hI.hom_ext _ _
    rw [this, Equiv.apply_symm_apply]
  exact IsInitial.ofUnique (F.obj I)

noncomputable def exercise_2_1_13_right {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {T : D}
    (hT : IsTerminal T) : IsTerminal (G.obj T) := by
  haveI : ∀ X : C, Unique (X ⟶ G.obj T) := by
    intro X
    refine
      { default := adj.homEquiv X T (hT.from (F.obj X))
        uniq := fun f => ?_ }
    apply (adj.homEquiv X T).symm.injective
    have : (adj.homEquiv X T).symm f = hT.from (F.obj X) := hT.hom_ext _ _
    rw [this, Equiv.symm_apply_apply]
  exact IsTerminal.ofUnique (G.obj T)

end Adjoints

#min_imports
