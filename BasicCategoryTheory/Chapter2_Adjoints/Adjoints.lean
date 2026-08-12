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

lemma lemma_2_2_2_left_triangle {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : C) :
    F.map (adj.unit.app A) ≫ adj.counit.app (F.obj A) = 𝟙 (F.obj A) :=
  adj.left_triangle_components A

lemma lemma_2_2_2_right_triangle {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (B : D) :
    adj.unit.app (G.obj B) ≫ G.map (adj.counit.app B) = 𝟙 (G.obj B) :=
  adj.right_triangle_components B

def lemma_2_2_4_unit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B : D} (g : F.obj A ⟶ B) :
    adj.homEquiv A B g = adj.unit.app A ≫ G.map g :=
  adj.homEquiv_unit A B g

def lemma_2_2_4_counit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B : D} (f : A ⟶ G.obj B) :
    (adj.homEquiv A B).symm f = F.map f ≫ adj.counit.app B :=
  adj.homEquiv_counit A B f

def theorem_2_2_5_forward {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : Adjunction.CoreUnitCounit F G :=
  Adjunction.CoreUnitCounit.mk adj.unit adj.counit

noncomputable def theorem_2_2_5_reverse {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C}
    (c : Adjunction.CoreUnitCounit F G) : F ⊣ G :=
  Adjunction.mkOfUnitCounit c

theorem corollary_2_2_6 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} :
    Nonempty (F ⊣ G) ↔ Nonempty (Adjunction.CoreUnitCounit F G) := by
  constructor
  · intro h; rcases h with ⟨adj⟩; exact ⟨theorem_2_2_5_forward adj⟩
  · intro h; rcases h with ⟨c⟩; exact ⟨theorem_2_2_5_reverse c⟩

theorem exercise_2_2_10 {A B : Type u} [Preorder A] [Preorder B] (f : A → B) (g : B → A)
    (hf : Monotone f) (hg : Monotone g) :
    ((∀ a b, f a ≤ b ↔ a ≤ g b) ↔ (∀ a, a ≤ g (f a)) ∧ (∀ b, f (g b) ≤ b)) := by
  constructor
  · intro h
    constructor
    · intro a
      apply (h a (f a)).mp
      exact le_refl (f a)
    · intro b
      apply (h (g b) b).mpr
      exact le_refl (g b)
  · intro ⟨h₁, h₂⟩ a b
    constructor
    · intro hfa_le_b
      have ha_gfa : a ≤ g (f a) := h₁ a
      have hgfa_gb : g (f a) ≤ g b := hg hfa_le_b
      exact le_trans ha_gfa hgfa_gb
    · intro ha_gb
      have hfa_fgb : f a ≤ f (g b) := hf ha_gb
      have hfgb_b : f (g b) ≤ b := h₂ b
      exact le_trans hfa_fgb hfgb_b

theorem exercise_2_2_12a {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : (G.Full ∧ G.Faithful) ↔ IsIso adj.counit := by
  constructor
  · intro ⟨hFull, hFaithful⟩
    haveI := hFull; haveI := hFaithful
    exact Adjunction.counit_isIso_of_R_fully_faithful adj
  · intro h
    haveI := h
    have hFF : G.FullyFaithful := Adjunction.fullyFaithfulROfIsIsoCounit adj
    exact ⟨hFF.full, hFF.faithful⟩

noncomputable def exercise_2_2_14 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {S : Type u} [Category.{v} S] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    (Functor.whiskeringLeft D C S).obj G ⊣ (Functor.whiskeringLeft C D S).obj F :=
  Adjunction.whiskerLeft S adj

end Adjoints

#min_imports
