-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib
import Mathlib.CategoryTheory.SingleObj
import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.Functors
import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.NaturalTransformations
import BasicCategoryTheory.Chapter2_Adjoints.Adjoints
import BasicCategoryTheory.Chapter4_Representables.DefinitionsAndExamples
import BasicCategoryTheory.Chapter4_Representables.YonedaLemma
import BasicCategoryTheory.Chapter4_Representables.ConsequencesOfTheYonedaLemma
import BasicCategoryTheory.Chapter5_Limits.LimitsAndExamples

namespace LimitsInTermsOfRepresentablesAndAdjoints

universe u v u' v' w

open CategoryTheory Limits Opposite

abbrev def_6_1_diagonal (I : Type u) [Category.{v} I] (A : Type u') [Category.{v'} A] :
    A ⥤ (I ⥤ A) :=
  Functor.const I

abbrev def_6_1_diagonal_obj {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A] (X : A) :
    I ⥤ A :=
  (Functor.const I).obj X

abbrev def_6_1_cone_functor {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    (D : I ⥤ A) : Aᵒᵖ ⥤ Type (max u v') :=
  (cones I A).obj D

def def_6_1_cone_mk {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    (X : A) (D : I ⥤ A) (π : (Functor.const I).obj X ⟶ D) : Cone D :=
  Cone.mk X π

def proposition_6_1_1_cone_iso_hom {I : Type v} [SmallCategory I] {A : Type u} [Category.{v} A]
    {D : I ⥤ A} (c : Cone D) (hc : IsLimit c) :
    yoneda.obj c.pt ≅ (cones I A).obj D :=
  NatIso.ofComponents
    (fun X => Equiv.toIso (hc.homEquiv (W := unop X)))
    (fun {X Y} f => by
      ext g
      dsimp [cones]
      simp)

def proposition_6_1_1_representation_of_isLimit {I : Type v} [SmallCategory I] {A : Type u}
    [Category.{v} A] {D : I ⥤ A} (c : Cone D) (hc : IsLimit c) :
    Representables.def_4_1_17_representation (def_6_1_cone_functor D) c.pt :=
  proposition_6_1_1_cone_iso_hom c hc

def proposition_6_1_1_cone_of_representation {I : Type v} [SmallCategory I] {A : Type u}
    [Category.{v} A] {D : I ⥤ A} (X : A) (i : yoneda.obj X ≅ (cones I A).obj D) : Cone D :=
  Cone.mk X (i.hom.app (op X) (𝟙 X))

theorem proposition_6_1_1_iso_rinv {I : Type v} [SmallCategory I] {A : Type u} [Category.{v} A]
    {D : I ⥤ A} (X : A) (i : yoneda.obj X ≅ (cones I A).obj D) (s : Cone D) :
    i.hom.app (op s.pt) (i.inv.app (op s.pt) s.π) = s.π := by
  have h := (i.app (op s.pt)).inv_hom_id
  have h_fn := congr_arg (fun (f : ((cones I A).obj D).obj (op s.pt) ⟶
      ((cones I A).obj D).obj (op s.pt)) => (↾f) s.π) h
  dsimp at h_fn
  exact h_fn

theorem proposition_6_1_1_iso_linv {I : Type v} [SmallCategory I] {A : Type u} [Category.{v} A]
    {D : I ⥤ A} (X : A) (i : yoneda.obj X ≅ (cones I A).obj D) (s : Cone D) (m : s.pt ⟶ X) :
    i.inv.app (op s.pt) (i.hom.app (op s.pt) m) = m := by
  have h := (i.app (op s.pt)).hom_inv_id
  have h_fn := congr_arg (fun (f : (yoneda.obj X).obj (op s.pt) ⟶
      (yoneda.obj X).obj (op s.pt)) => (↾f) m) h
  dsimp at h_fn
  exact h_fn

def proposition_6_1_1_isLimit_of_representation {I : Type v} [SmallCategory I] {A : Type u}
    [Category.{v} A] {D : I ⥤ A} (X : A) (i : yoneda.obj X ≅ (cones I A).obj D) :
    IsLimit (proposition_6_1_1_cone_of_representation X i) := by
  refine IsLimit.mk (fun s => (i.inv.app (op s.pt)) s.π) (fun s j => ?_)
    (fun s (m : s.pt ⟶ X) hm => ?_)
  · have hnat := NatTrans.naturality_apply i.hom ((i.inv.app (op s.pt)) s.π).op (𝟙 X)
    dsimp [cones] at hnat ⊢
    rw [Category.comp_id] at hnat
    have h_eq : (Functor.const I).map ((i.inv.app (op s.pt)) s.π) ≫ i.hom.app (op X) (𝟙 X) = s.π :=
      hnat.symm.trans (proposition_6_1_1_iso_rinv X i s)
    exact congr_app h_eq j
  · have hnat := NatTrans.naturality_apply i.hom m.op (𝟙 X)
    dsimp [cones] at hnat ⊢
    rw [Category.comp_id] at hnat
    have h_ext : (Functor.const I).map m ≫ i.hom.app (op X) (𝟙 X) = s.π := by
      ext j
      exact hm j
    have h_m : i.hom.app (op s.pt) m = s.π := hnat.trans h_ext
    have hinj := congr_arg (i.inv.app (op s.pt)) h_m
    rw [proposition_6_1_1_iso_linv X i s m] at hinj
    exact hinj

def proposition_6_1_1_is_representable_of_hasLimit {I : Type v} [SmallCategory I] {A : Type u}
    [Category.{v} A] (D : I ⥤ A) [HasLimit D] :
    Representables.def_4_1_17_is_representable (def_6_1_cone_functor D) :=
  ⟨limit D, ⟨proposition_6_1_1_cone_iso_hom (limit.cone D) (limit.isLimit D)⟩⟩

@[reducible]
def proposition_6_1_1_hasLimit_of_is_representable {I : Type v} [SmallCategory I] {A : Type u}
    [Category.{v} A] (D : I ⥤ A)
    (h : Representables.def_4_1_17_is_representable (def_6_1_cone_functor D)) :
    HasLimit D := by
  rcases h with ⟨X, ⟨i⟩⟩
  exact ⟨⟨proposition_6_1_1_cone_of_representation X i,
    proposition_6_1_1_isLimit_of_representation X i⟩⟩

def corollary_6_1_2_iso {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D : I ⥤ A} {c c' : Cone D} (hc : IsLimit c) (hc' : IsLimit c') : c.pt ≅ c'.pt :=
  hc.conePointUniqueUpToIso hc'

theorem corollary_6_1_2_unique {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D : I ⥤ A} {c c' : Cone D} (hc : IsLimit c) (hc' : IsLimit c') :
    ∃! e : c.pt ≅ c'.pt,
      (∀ j, e.hom ≫ c'.π.app j = c.π.app j) ∧ (∀ j, e.inv ≫ c.π.app j = c'.π.app j) := by
  refine ⟨hc.conePointUniqueUpToIso hc', ⟨fun j => hc.conePointUniqueUpToIso_hom_comp hc' j,
    fun j => hc.conePointUniqueUpToIso_inv_comp hc' j⟩, fun e he => ?_⟩
  apply Iso.ext
  apply hc'.hom_ext
  intro j
  rw [hc.conePointUniqueUpToIso_hom_comp]
  exact he.1 j

def lemma_6_1_3_postcompose {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D D' : I ⥤ A} (c : Cone D) (α : D ⟶ D') : Cone D' where
  pt := c.pt
  π := c.π ≫ α

theorem lemma_6_1_3a_exists_unique {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D D' : I ⥤ A} (α : D ⟶ D') (c : Cone D) (c' : Cone D') (hc' : IsLimit c') :
    ∃! (f : c.pt ⟶ c'.pt), ∀ (j : I), f ≫ c'.π.app j = c.π.app j ≫ α.app j := by
  refine ⟨hc'.lift (lemma_6_1_3_postcompose c α), ?_, ?_⟩
  · intro j
    exact hc'.fac (lemma_6_1_3_postcompose c α) j
  · intro f hf
    apply hc'.hom_ext
    intro j
    rw [hf j]
    exact (hc'.fac (lemma_6_1_3_postcompose c α) j).symm

def lemma_6_1_3a_map {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D D' : I ⥤ A} (α : D ⟶ D') (c : Cone D) (c' : Cone D') (hc' : IsLimit c') : c.pt ⟶ c'.pt :=
  hc'.lift (lemma_6_1_3_postcompose c α)

theorem lemma_6_1_3a_fac {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D D' : I ⥤ A} (α : D ⟶ D') (c : Cone D) (c' : Cone D') (hc' : IsLimit c') (j : I) :
    lemma_6_1_3a_map α c c' hc' ≫ c'.π.app j = c.π.app j ≫ α.app j :=
  hc'.fac (lemma_6_1_3_postcompose c α) j

theorem lemma_6_1_3b {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D D' : I ⥤ A} (α : D ⟶ D') (c : Cone D) (hc : IsLimit c) (c' : Cone D') (hc' : IsLimit c')
    (s₁ : Cone D) (s₂ : Cone D') (s : s₁.pt ⟶ s₂.pt)
    (h_comm : ∀ (j : I), s₁.π.app j ≫ α.app j = s ≫ s₂.π.app j) :
    hc.lift s₁ ≫ lemma_6_1_3a_map α c c' hc' = s ≫ hc'.lift s₂ := by
  apply hc'.hom_ext
  intro j
  have h_lhs : (hc.lift s₁ ≫ lemma_6_1_3a_map α c c' hc') ≫ c'.π.app j = s₁.π.app j ≫ α.app j := by
    rw [Category.assoc, lemma_6_1_3a_fac]
    exact hc.fac_assoc s₁ j (α.app j)
  have h_rhs : (s ≫ hc'.lift s₂) ≫ c'.π.app j = s ≫ s₂.π.app j := by
    rw [Category.assoc, hc'.fac]
  rw [h_lhs, h_rhs, h_comm]

noncomputable abbrev proposition_6_1_4_functor (I : Type u) [Category.{v} I] (A : Type u')
    [Category.{v'} A] [HasLimitsOfShape I A] : (I ⥤ A) ⥤ A :=
  lim

noncomputable def proposition_6_1_4_adjunction (I : Type u) [Category.{v} I] (A : Type u')
    [Category.{v'} A] [HasLimitsOfShape I A] : Functor.const I ⊣ (lim : (I ⥤ A) ⥤ A) :=
  constLimAdj

noncomputable def proposition_6_1_4_homEquiv (I : Type u) [Category.{v} I] (A : Type u')
    [Category.{v'} A] [HasLimitsOfShape I A] (X : A) (D : I ⥤ A) :
    ((Functor.const I).obj X ⟶ D) ≃ (X ⟶ (lim : (I ⥤ A) ⥤ A).obj D) :=
  (proposition_6_1_4_adjunction I A).homEquiv X D

noncomputable def proposition_6_1_4_uniqueness (I : Type u) [Category.{v} I] (A : Type u')
    [Category.{v'} A] [HasLimitsOfShape I A] (R : (I ⥤ A) ⥤ A) (adj : Functor.const I ⊣ R) :
    R ≅ (lim : (I ⥤ A) ⥤ A) :=
  ((proposition_6_1_4_adjunction I A).rightAdjointUniq adj).symm

def exercise_6_1_1_cone_equiv {C : Type u} [Category.{v} C] (A X Y : C) :
    ((Functor.const (Discrete WalkingPair)).obj A ⟶ pair X Y) ≃ (A ⟶ X) × (A ⟶ Y) where
  toFun π := (π.app ⟨WalkingPair.left⟩, π.app ⟨WalkingPair.right⟩)
  invFun := fun (f, g) => {
    app := fun j => match j with
      | ⟨WalkingPair.left⟩ => f
      | ⟨WalkingPair.right⟩ => g
    naturality := fun j j' f' => match j, j', f' with
      | ⟨WalkingPair.left⟩, ⟨WalkingPair.left⟩, _ => by simp
      | ⟨WalkingPair.right⟩, ⟨WalkingPair.right⟩, _ => by simp
  }
  left_inv π := by
    ext ⟨j⟩
    cases j <;> rfl
  right_inv _ := rfl

noncomputable def exercise_6_1_1_cone_prod_equiv {C : Type u} [Category.{v} C]
    [HasBinaryProducts C] (A X Y : C) :
    ((Functor.const (Discrete WalkingPair)).obj A ⟶ pair X Y) ≃ (A ⟶ X ⨯ Y) where
  toFun π := prod.lift (π.app ⟨WalkingPair.left⟩) (π.app ⟨WalkingPair.right⟩)
  invFun f := (exercise_6_1_1_cone_equiv A X Y).symm (f ≫ prod.fst, f ≫ prod.snd)
  left_inv π := by
    apply (exercise_6_1_1_cone_equiv A X Y).injective
    rw [Equiv.apply_symm_apply]
    ext
    · exact prod.lift_fst _ _
    · exact prod.lift_snd _ _
  right_inv f := by
    apply prod.hom_ext
    · simp [prod.lift_fst, exercise_6_1_1_cone_equiv]
    · simp [prod.lift_snd, exercise_6_1_1_cone_equiv]

noncomputable def exercise_6_1_1_adjunction {C : Type u} [Category.{v} C] [HasBinaryProducts C] :
    (Functor.const (Discrete WalkingPair) : C ⥤ Discrete WalkingPair ⥤ C) ⊣ lim :=
  constLimAdj

theorem exercise_6_1_1_prod_map {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    limMap (mapPair (F := pair X Y) (G := pair X' Y') f g) = Limits.prod.map f g := by
  apply prod.hom_ext
  · change limMap (mapPair (F := pair X Y) (G := pair X' Y') f g) ≫
      limit.π (pair X' Y') ⟨WalkingPair.left⟩ = _
    rw [limMap_π, prod.map_fst]
    rfl
  · change limMap (mapPair (F := pair X Y) (G := pair X' Y') f g) ≫
      limit.π (pair X' Y') ⟨WalkingPair.right⟩ = _
    rw [limMap_π, prod.map_snd]
    rfl

def exercise_6_1_2_invariants {G : Type u} [Group G] (D : SingleObj G ⥤ Type u) : Type u :=
  {x : D.obj (SingleObj.star G) // ∀ (g : G),
    D.map (X := SingleObj.star G) (Y := SingleObj.star G) g x = x}

def exercise_6_1_2_invariants_cone {G : Type u} [Group G] (D : SingleObj G ⥤ Type u) :
    Cone D where
  pt := exercise_6_1_2_invariants D
  π := {
    app := fun _ => ↾fun (x : exercise_6_1_2_invariants D) => x.1
    naturality := fun _ _ (g : G) => by
      ext ⟨x, hx⟩
      exact (hx g).symm
  }

def exercise_6_1_2_invariants_isLimit {G : Type u} [Group G] (D : SingleObj G ⥤ Type u) :
    IsLimit (exercise_6_1_2_invariants_cone D) where
  lift s := ↾fun a => ⟨s.π.app (SingleObj.star G) a, fun (g : G) => by
    have h := ConcreteCategory.congr_hom (s.π.naturality
      (X := SingleObj.star G) (Y := SingleObj.star G) g) a
    exact h.symm⟩
  fac _ _ := rfl
  uniq s m hm := by
    ext a
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (hm (SingleObj.star G)) a

def exercise_6_1_2_orbit_rel {G : Type u} [Group G] (D : SingleObj G ⥤ Type u)
    (x y : D.obj (SingleObj.star G)) : Prop :=
  ∃ g : G, D.map (X := SingleObj.star G) (Y := SingleObj.star G) g x = y

def exercise_6_1_2_coinvariants {G : Type u} [Group G] (D : SingleObj G ⥤ Type u) : Type u :=
  Quot (exercise_6_1_2_orbit_rel D)

def exercise_6_1_2_coinvariants_cocone {G : Type u} [Group G] (D : SingleObj G ⥤ Type u) :
    Cocone D where
  pt := exercise_6_1_2_coinvariants D
  ι := {
    app := fun _ => ↾fun (x : D.obj (SingleObj.star G)) =>
      Quot.mk (exercise_6_1_2_orbit_rel D) x
    naturality := fun {j j'} (f : j ⟶ j') => by
      let g : G := f
      ext x
      apply Quot.sound
      refine ⟨g⁻¹, ?_⟩
      have h : (D.map (X := SingleObj.star G) (Y := SingleObj.star G) g ≫
                D.map (X := SingleObj.star G) (Y := SingleObj.star G) g⁻¹) x = x := by
        rw [← D.map_comp]
        have hid : (g : SingleObj.star G ⟶ SingleObj.star G) ≫
            (g⁻¹ : SingleObj.star G ⟶ SingleObj.star G) = 𝟙 _ := by
          rw [SingleObj.comp_as_mul, inv_mul_cancel, SingleObj.id_as_one]
        rw [hid, D.map_id]
        rfl
      exact h
  }

def exercise_6_1_2_coinvariants_isColimit {G : Type u} [Group G] (D : SingleObj G ⥤ Type u) :
    IsColimit (exercise_6_1_2_coinvariants_cocone D) where
  desc s := ↾fun (q : exercise_6_1_2_coinvariants D) =>
    Quot.lift (fun x => s.ι.app (SingleObj.star G) x) (by
      intro x y ⟨g, hg⟩
      have h := ConcreteCategory.congr_hom (s.ι.naturality
        (X := SingleObj.star G) (Y := SingleObj.star G) g) x
      dsimp at h ⊢
      rw [← hg]
      exact h.symm) q
  fac _ _ := rfl
  uniq s m hm := by
    ext (q : exercise_6_1_2_coinvariants D)
    induction q using Quot.ind with
    | mk x =>
      exact ConcreteCategory.congr_hom (hm (SingleObj.star G)) x

end LimitsInTermsOfRepresentablesAndAdjoints
