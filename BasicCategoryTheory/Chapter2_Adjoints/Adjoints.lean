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

abbrev def_2_3_1 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {E : Type u} [Category.{v} E] (P : C ⥤ E) (Q : D ⥤ E) :=
  Comma P Q

theorem def_2_3_1_map {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {E : Type u} [Category.{v} E] {P : C ⥤ E} {Q : D ⥤ E} {X Y : Comma P Q}
    (f : X ⟶ Y) : P.map f.left ≫ Y.hom = X.hom ≫ Q.map f.right :=
  f.w

abbrev example_2_3_3_slice {C : Type u} [Category.{v} C] (A : C) :=
  Over A

theorem example_2_3_3_slice_comma {C : Type u} [Category.{v} C] (A : C) :
    Over A = Comma (𝟭 C) (Functor.fromPUnit.{0} A) :=
  rfl

abbrev example_2_3_3_coslice {C : Type u} [Category.{v} C] (A : C) :=
  Under A

theorem example_2_3_3_coslice_comma {C : Type u} [Category.{v} C] (A : C) :
    Under A = Comma (Functor.fromPUnit.{0} A) (𝟭 C) :=
  rfl

abbrev example_2_3_4 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {G : D ⥤ C} (A : C) :=
  StructuredArrow A G

noncomputable def lemma_2_3_5 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : C) :
    IsInitial (StructuredArrow.mk (adj.unit.app A) : StructuredArrow A G) :=
  mkInitialOfLeftAdjoint G adj A

noncomputable def theorem_2_3_6_reverse {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G)
    (hη : ∀ A : C, IsInitial (StructuredArrow.mk (η.app A) : StructuredArrow A G)) :
    F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun g => η.app X ≫ G.map g
          invFun := fun f => ((hη X).to (StructuredArrow.mk f)).right
          left_inv := by
            intro g
            have h := (hη X).hom_ext
              ((hη X).to (StructuredArrow.mk (η.app X ≫ G.map g)))
              (StructuredArrow.homMk' (StructuredArrow.mk (η.app X) : StructuredArrow X G) g)
            simpa using congrArg (fun m : _ => m.right) h
          right_inv := by
            intro f
            exact StructuredArrow.w ((hη X).to (StructuredArrow.mk f)) }
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        let t : F.obj X ⟶ Y := ((hη X).to (StructuredArrow.mk g)).right
        have hcomm : η.app X ≫ G.map t = g := by
          simpa [t] using StructuredArrow.w ((hη X).to (StructuredArrow.mk g))
        have hw : η.app X' ≫ G.map (F.map f ≫ t) = f ≫ g := by
          calc
            η.app X' ≫ G.map (F.map f ≫ t) = η.app X' ≫ G.map (F.map f) ≫ G.map t := by
              simp
            _ = (f ≫ η.app X) ≫ G.map t := by
              simpa using congrArg (fun m : X' ⟶ G.obj (F.obj X) => m ≫ G.map t)
                (η.naturality f).symm
            _ = f ≫ (η.app X ≫ G.map t) := by
              simp
            _ = f ≫ g := by
              exact congrArg (fun m : X ⟶ G.obj Y => f ≫ m) hcomm
        have hm : (hη X').to (StructuredArrow.mk (f ≫ g)) =
            StructuredArrow.homMk (F.map f ≫ t) hw :=
          (hη X').hom_ext _ _
        simpa [t] using congrArg (fun m : _ => m.right) hm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        simp }

lemma adjunction_ext {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} {adj₁ adj₂ : F ⊣ G} (h₁ : adj₁.unit = adj₂.unit)
    (h₂ : adj₁.counit = adj₂.counit) : adj₁ = adj₂ := by
  cases adj₁ with
  | mk unit₁ counit₁ ltr₁ rtr₁ =>
    cases adj₂ with
    | mk unit₂ counit₂ ltr₂ rtr₂ =>
      subst h₁
      subst h₂
      congr

noncomputable def theorem_2_3_6 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} :
    (F ⊣ G) ≃ {η : 𝟭 C ⟶ F ⋙ G // ∀ A : C,
      Nonempty (IsInitial (StructuredArrow.mk (η.app A) : StructuredArrow A G))} :=
  { toFun := fun adj => ⟨adj.unit, fun A => ⟨mkInitialOfLeftAdjoint G adj A⟩⟩
    invFun := fun ⟨η, p⟩ => theorem_2_3_6_reverse (η := η) (hη := fun A => Classical.choice (p A))
    left_inv := by
      intro adj
      apply adjunction_ext
      · ext X
        simp [theorem_2_3_6_reverse]
      · ext Y
        let hη₀ : ∀ A : C,
            IsInitial (StructuredArrow.mk (adj.unit.app A) : StructuredArrow A G) :=
          fun A => Classical.choice (⟨mkInitialOfLeftAdjoint G adj A⟩)
        let m₁ : (StructuredArrow.mk (adj.unit.app (G.obj Y)) : StructuredArrow (G.obj Y) G) ⟶
            (StructuredArrow.mk (𝟙 (G.obj Y)) : StructuredArrow (G.obj Y) G) :=
          (hη₀ (G.obj Y)).to (StructuredArrow.mk (𝟙 (G.obj Y)))
        let m₂ : (StructuredArrow.mk (adj.unit.app (G.obj Y)) : StructuredArrow (G.obj Y) G) ⟶
            (StructuredArrow.mk (𝟙 (G.obj Y)) : StructuredArrow (G.obj Y) G) :=
          StructuredArrow.homMk (adj.counit.app Y) (adj.right_triangle_components Y)
        have hm : m₁ = m₂ := (hη₀ (G.obj Y)).hom_ext m₁ m₂
        change m₁.right = m₂.right
        exact congrArg (fun m : _ => m.right) hm
    right_inv := by
      intro ⟨η, p⟩
      apply Subtype.ext
      apply NatTrans.ext
      funext X
      simp [theorem_2_3_6_reverse] }

theorem corollary_2_3_7 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {G : D ⥤ C} :
    G.IsRightAdjoint ↔ ∀ A : C, HasInitial (StructuredArrow A G) :=
  isRightAdjoint_iff_hasInitial_structuredArrow

theorem exercise_2_3_9 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} :
    F.IsLeftAdjoint ↔ ∀ B : D, HasTerminal (CostructuredArrow F B) :=
  isLeftAdjoint_iff_hasTerminal_costructuredArrow

noncomputable def exercise_2_3_10 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : e.functor ⊣ e.inverse :=
  e.toAdjunction

theorem exercise_2_3_11 {A : Type u} [Category.{v} A] {U : A ⥤ Type u'} {F : Type u' ⥤ A}
    (adj : F ⊣ U) (h : ∃ X : A, ∃ x₁ x₂ : U.obj X, x₁ ≠ x₂) (S : Type u') :
    Function.Injective (adj.unit.app S) := by
  classical
  rcases h with ⟨X, x₁, x₂, hx⟩
  intro s₁ s₂ hs
  by_contra hne
  let f : S ⟶ U.obj X := ↾(fun s => if s = s₁ then x₁ else x₂)
  have hf₁ : f s₁ = x₁ := by simp [f]
  have hf₂ : f s₂ = x₂ := by
    change (if s₂ = s₁ then x₁ else x₂) = x₂
    rw [if_neg (Ne.symm hne)]
  let g : F.obj S ⟶ X := (adj.homEquiv S X).symm f
  have hcomm : adj.unit.app S ≫ U.map g = f := by
    exact (adj.homEquiv_unit S X g).symm.trans (by
      simp [g])
  have hcomm' : ∀ s : S, U.map g (adj.unit.app S s) = f s := by
    intro s
    simpa using congrArg (fun m : S ⟶ U.obj X => m s) hcomm
  have h₁ : x₁ = x₂ := by
    calc
      x₁ = f s₁ := by rw [hf₁]
      _ = U.map g (adj.unit.app S s₁) := (hcomm' s₁).symm
      _ = U.map g (adj.unit.app S s₂) := by rw [hs]
      _ = f s₂ := hcomm' s₂
      _ = x₂ := by rw [hf₂]
  exact hx h₁

noncomputable def exercise_2_3_12 : PartialFun.{u} ≌ Pointed :=
  partialFunEquivPointed

noncomputable def exercise_2_3_12_coslice_functor : Pointed.{u} ⥤ Under PUnit.{u + 1} where
  obj := fun X => Under.mk (↾(fun _ : PUnit.{u + 1} => X.point))
  map := fun {X Y} (f : X ⟶ Y) => @Under.homMk (Type u) _ PUnit.{u + 1}
    (Under.mk (↾(fun _ : PUnit.{u + 1} => X.point)))
    (Under.mk (↾(fun _ : PUnit.{u + 1} => Y.point))) (↾f.toFun) (by
      ext; simpa using f.map_point)
  map_id := fun X => by
    apply StructuredArrow.hom_ext
    rfl
  map_comp := fun f g => by
    apply StructuredArrow.hom_ext
    rfl

noncomputable def exercise_2_3_12_coslice_inverse : Under PUnit.{u + 1} ⥤ Pointed where
  obj := fun X => Pointed.of (X.hom PUnit.unit)
  map := fun {X Y} (f : X ⟶ Y) =>
    ⟨f.right, by
      change f.right (X.hom PUnit.unit) = Y.hom PUnit.unit
      rw [← types_comp_apply]
      rw [show X.hom ≫ Under.Hom.right f = Y.hom from (StructuredArrow.w f)]⟩
  map_id := fun X => by
    apply Pointed.Hom.ext
    rfl
  map_comp := fun f g => by
    apply Pointed.Hom.ext
    rfl

noncomputable def exercise_2_3_12_coslice : Pointed.{u} ≌ Under PUnit.{u + 1} where
  functor := exercise_2_3_12_coslice_functor
  inverse := exercise_2_3_12_coslice_inverse
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    exact Pointed.Hom.ext (by rfl))
  counitIso := NatIso.ofComponents
    (fun X => Under.isoMk (Iso.refl X.right) (by
      change (↾(fun _ : PUnit.{u + 1} => X.hom PUnit.unit) ≫ (Iso.refl X.right).hom) =
        X.hom
      change (↾(fun _ : PUnit.{u + 1} => X.hom PUnit.unit)) = X.hom
      rfl)) (by
    intro X Y f
    exact StructuredArrow.hom_ext _ _ (by rfl))
  functor_unitIso_comp X := by
    exact StructuredArrow.hom_ext _ _ (by rfl)

end Adjoints

#min_imports
