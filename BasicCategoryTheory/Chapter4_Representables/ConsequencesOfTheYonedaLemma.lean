-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.Functors
import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.NaturalTransformations
import BasicCategoryTheory.Chapter2_Adjoints.Adjoints
import BasicCategoryTheory.Chapter4_Representables.DefinitionsAndExamples
import BasicCategoryTheory.Chapter4_Representables.YonedaLemma
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.ZMod.Basic

namespace Representables

universe u v u' v' u'' v''

open CategoryTheory Opposite Limits

def def_4_3_1_universal_element {C : Type u} [Category.{v} C]
    (X : Cᵒᵖ ⥤ Type v) (A : C) (u : X.obj (op A)) : Prop :=
  ∀ (B : C) (x : X.obj (op B)), ∃! f : B ⟶ A, X.map f.op u = x

theorem corollary_4_3_1_isIso_iff {C : Type u} [Category.{v} C] {A : C} {X : Cᵒᵖ ⥤ Type v}
    (u : X.obj (op A)) :
    IsIso (theorem_4_2_1_ynt u) ↔ def_4_3_1_universal_element X A u := by
  constructor
  · intro h B x
    have hB : IsIso ((theorem_4_2_1_ynt u).app (op B)) :=
      NatIso.isIso_app_of_isIso (theorem_4_2_1_ynt u) (op B)
    have hbij : Function.Bijective ((theorem_4_2_1_ynt u).app (op B)) :=
      (isIso_iff_bijective ((theorem_4_2_1_ynt u).app (op B))).mp hB
    rw [Function.bijective_iff_existsUnique] at hbij
    exact hbij x
  · intro hu
    have hB (B : Cᵒᵖ) : IsIso ((theorem_4_2_1_ynt u).app B) := by
      rcases B with ⟨B⟩
      rw [isIso_iff_bijective]
      rw [Function.bijective_iff_existsUnique]
      exact hu B
    exact NatIso.isIso_of_isIso_app (theorem_4_2_1_ynt u)

noncomputable def corollary_4_3_1_equiv {C : Type u} [Category.{v} C] (A : C) (X : Cᵒᵖ ⥤ Type v) :
    (yoneda.obj A ≅ X) ≃ {u : X.obj (op A) // def_4_3_1_universal_element X A u} where
  toFun iso := ⟨theorem_4_2_1_yel iso.hom, by
    have h : IsIso (theorem_4_2_1_ynt (theorem_4_2_1_yel iso.hom)) := by
      rw [theorem_4_2_1_ynt_yel]
      infer_instance
    exact (corollary_4_3_1_isIso_iff (theorem_4_2_1_yel iso.hom)).mp h⟩
  invFun := fun ⟨u, hu⟩ =>
    letI : IsIso (theorem_4_2_1_ynt u) := (corollary_4_3_1_isIso_iff u).mpr hu
    asIso (theorem_4_2_1_ynt u)
  left_inv iso := by
    apply Iso.ext
    dsimp
    exact theorem_4_2_1_ynt_yel iso.hom
  right_inv := fun ⟨u, hu⟩ => by
    ext
    dsimp
    exact theorem_4_2_1_yel_ynt u

noncomputable def corollary_4_3_1 {C : Type u} [Category.{v} C] (X : Cᵒᵖ ⥤ Type v) :
    (Σ A : C, yoneda.obj A ≅ X) ≃
      (Σ A : C, {u : X.obj (op A) // def_4_3_1_universal_element X A u}) :=
  Equiv.sigmaCongrRight (fun A => corollary_4_3_1_equiv A X)

def def_4_3_2_universal_element {C : Type u} [Category.{v} C]
    (X : C ⥤ Type v) (A : C) (u : X.obj A) : Prop :=
  ∀ (B : C) (x : X.obj B), ∃! f : A ⟶ B, X.map f u = x

theorem corollary_4_3_2_isIso_iff {C : Type u} [Category.{v} C] {A : C} {X : C ⥤ Type v}
    (u : X.obj A) :
    IsIso (exercise_4_2_1_ynt u) ↔ def_4_3_2_universal_element X A u := by
  constructor
  · intro h B x
    have hB : IsIso ((exercise_4_2_1_ynt u).app B) :=
      NatIso.isIso_app_of_isIso (exercise_4_2_1_ynt u) B
    have hbij : Function.Bijective ((exercise_4_2_1_ynt u).app B) :=
      (isIso_iff_bijective ((exercise_4_2_1_ynt u).app B)).mp hB
    rw [Function.bijective_iff_existsUnique] at hbij
    exact hbij x
  · intro hu
    have hB (B : C) : IsIso ((exercise_4_2_1_ynt u).app B) := by
      rw [isIso_iff_bijective]
      rw [Function.bijective_iff_existsUnique]
      exact hu B
    exact NatIso.isIso_of_isIso_app (exercise_4_2_1_ynt u)

noncomputable def corollary_4_3_2_equiv {C : Type u} [Category.{v} C] (A : C) (X : C ⥤ Type v) :
    (coyoneda.obj (op A) ≅ X) ≃ {u : X.obj A // def_4_3_2_universal_element X A u} where
  toFun iso := ⟨exercise_4_2_1_yel iso.hom, by
    have h : IsIso (exercise_4_2_1_ynt (exercise_4_2_1_yel iso.hom)) := by
      rw [exercise_4_2_1_ynt_yel]
      infer_instance
    exact (corollary_4_3_2_isIso_iff (exercise_4_2_1_yel iso.hom)).mp h⟩
  invFun := fun ⟨u, hu⟩ =>
    letI : IsIso (exercise_4_2_1_ynt u) := (corollary_4_3_2_isIso_iff u).mpr hu
    asIso (exercise_4_2_1_ynt u)
  left_inv iso := by
    apply Iso.ext
    dsimp
    exact exercise_4_2_1_ynt_yel iso.hom
  right_inv := fun ⟨u, hu⟩ => by
    ext
    dsimp
    exact exercise_4_2_1_yel_ynt u

noncomputable def corollary_4_3_2 {C : Type u} [Category.{v} C] (X : C ⥤ Type v) :
    (Σ A : C, coyoneda.obj (op A) ≅ X) ≃
      (Σ A : C, {u : X.obj A // def_4_3_2_universal_element X A u}) :=
  Equiv.sigmaCongrRight (fun A => corollary_4_3_2_equiv A X)

def example_4_3_4_functor {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
    (G : D ⥤ C) (A : C) : D ⥤ Type v :=
  G ⋙ coyoneda.obj (op A)

def example_4_3_4_a {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : C) :
    coyoneda.obj (op (F.obj A)) ≅ example_4_3_4_functor G A :=
  lemma_4_1_10 adj A

def example_4_3_4_b {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : C) :
    def_4_3_2_universal_element (example_4_3_4_functor G A) (F.obj A) (adj.unit.app A) := by
  intro B x
  dsimp [example_4_3_4_functor]
  use (adj.homEquiv A B).symm x
  constructor
  · have h := adj.homEquiv_unit A B ((adj.homEquiv A B).symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  · intro f hf
    have h := adj.homEquiv_unit A B f
    have h2 : (adj.homEquiv A B) f = x := by
      rw [h]
      exact hf
    rw [← h2, Equiv.symm_apply_apply]

noncomputable def example_4_3_4_b_isInitial {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : C) :
    IsInitial (StructuredArrow.mk (adj.unit.app A) : StructuredArrow A G) :=
  Adjoints.lemma_2_3_5 adj A

def example_4_3_3_functor (k : Type u) [CommRing k] (S : Type u) :
    ModuleCat.{u} k ⥤ Type u :=
  example_4_3_4_functor (forget (ModuleCat.{u} k)) S

noncomputable def example_4_3_3_a (k : Type u) [CommRing k] (S : Type u) :
    coyoneda.obj (op ((ModuleCat.free k).obj S)) ≅ example_4_3_3_functor k S :=
  example_4_3_4_a (ModuleCat.adj k) S

noncomputable def example_4_3_3_b (k : Type u) [CommRing k] (S : Type u) :
    def_4_3_2_universal_element (example_4_3_3_functor k S) ((ModuleCat.free k).obj S)
      ((ModuleCat.adj k).unit.app S) :=
  example_4_3_4_b (ModuleCat.adj k) S

lemma example_4_3_5_zpow_eval {G : Type*} [Group G]
    (f : Multiplicative ℤ →* G) (n : Multiplicative ℤ) :
    f n = (f (Multiplicative.ofAdd 1)) ^ n.toAdd := by
  have : n = (Multiplicative.ofAdd (1 : ℤ)) ^ n.toAdd := by
    apply Multiplicative.toAdd.injective
    simp
  conv_lhs => rw [this]
  rw [map_zpow]

lemma example_4_3_5_neg_eval {G : Type*} [Group G]
    (f : Multiplicative ℤ →* G) (n : Multiplicative ℤ) :
    f n = (f (Multiplicative.ofAdd (-1 : ℤ))) ^ (-n.toAdd) := by
  have : n = (Multiplicative.ofAdd (-1 : ℤ)) ^ (-n.toAdd) := by
    apply Multiplicative.toAdd.injective
    simp
  conv_lhs => rw [this]
  rw [map_zpow]

def example_4_3_5_equiv (G : GrpCat.{0}) :
    (GrpCat.of (Multiplicative ℤ) ⟶ G) ≃ (forget GrpCat).obj G where
  toFun f := f.hom (Multiplicative.ofAdd (1 : ℤ))
  invFun x := GrpCat.ofHom (NaturalTransformations.zpowGroupHom x)
  left_inv f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro n
    dsimp [NaturalTransformations.zpowGroupHom]
    exact (example_4_3_5_zpow_eval f.hom n).symm
  right_inv x := by
    dsimp [NaturalTransformations.zpowGroupHom]
    exact zpow_one x

def example_4_3_5_pos :
    def_4_3_2_universal_element (forget GrpCat.{0}) (GrpCat.of (Multiplicative ℤ))
      (Multiplicative.ofAdd (1 : ℤ)) := by
  intro G x
  use GrpCat.ofHom (NaturalTransformations.zpowGroupHom x)
  refine ⟨by dsimp [NaturalTransformations.zpowGroupHom]; exact zpow_one x, ?_⟩
  intro f hf
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro (n : Multiplicative ℤ)
  dsimp [NaturalTransformations.zpowGroupHom]
  rw [example_4_3_5_zpow_eval f.hom n]
  exact congr_arg (fun (y : G) => y ^ n.toAdd) hf

def example_4_3_5_neg_hom {G : Type} [Group G] (x : G) : Multiplicative ℤ →* G where
  toFun n := x ^ (-n.toAdd)
  map_one' := by
    simp
  map_mul' := fun a b => by
    dsimp
    rw [neg_add, zpow_add]

def example_4_3_5_neg_equiv (G : GrpCat.{0}) :
    (GrpCat.of (Multiplicative ℤ) ⟶ G) ≃ (forget GrpCat).obj G where
  toFun f := f.hom (Multiplicative.ofAdd (-1 : ℤ))
  invFun x := GrpCat.ofHom (example_4_3_5_neg_hom (x := x))
  left_inv f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro n
    dsimp [example_4_3_5_neg_hom]
    exact (example_4_3_5_neg_eval f.hom n).symm
  right_inv x := by
    dsimp [example_4_3_5_neg_hom]
    change x ^ (-(-1 : ℤ)) = x
    have : -(-1 : ℤ) = 1 := by decide
    rw [this, zpow_one]

def example_4_3_5_neg :
    def_4_3_2_universal_element (forget GrpCat.{0}) (GrpCat.of (Multiplicative ℤ))
      (Multiplicative.ofAdd (-1 : ℤ)) := by
  intro G x
  use GrpCat.ofHom (example_4_3_5_neg_hom (x := x))
  refine ⟨by
    dsimp [example_4_3_5_neg_hom]
    change x ^ (-(-1 : ℤ)) = x
    have : -(-1 : ℤ) = 1 := by decide
    rw [this, zpow_one], ?_⟩
  intro f hf
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro (n : Multiplicative ℤ)
  dsimp [example_4_3_5_neg_hom]
  rw [example_4_3_5_neg_eval f.hom n]
  exact congr_arg (fun (y : G) => y ^ (-n.toAdd)) hf

theorem example_4_3_5_distinct :
    (exercise_4_2_1_ynt (Multiplicative.ofAdd (1 : ℤ)) :
      coyoneda.obj (op (GrpCat.of (Multiplicative ℤ))) ⟶ forget GrpCat.{0}) ≠
    exercise_4_2_1_ynt (Multiplicative.ofAdd (-1 : ℤ)) := by
  intro h
  have h1 := congr_fun (congr_arg
    (fun (α : coyoneda.obj (op (GrpCat.of (Multiplicative ℤ))) ⟶ forget GrpCat) =>
      (α.app (GrpCat.of (Multiplicative ℤ)) : _ → _)) h) (𝟙 (GrpCat.of (Multiplicative ℤ)))
  dsimp [exercise_4_2_1_ynt] at h1
  change Multiplicative.ofAdd (1 : ℤ) = Multiplicative.ofAdd (-1 : ℤ) at h1
  have h2 : (1 : ℤ) = -1 := Multiplicative.ofAdd.injective h1
  have h3 : (1 : ℤ) ≠ -1 := by decide
  exact h3 h2

theorem corollary_4_3_6 (C : Type u) [Category.{v} C] :
    (yoneda : C ⥤ Cᵒᵖ ⥤ Type v).Full ∧ (yoneda : C ⥤ Cᵒᵖ ⥤ Type v).Faithful :=
  ⟨inferInstance, inferInstance⟩

theorem corollary_4_3_6_coyoneda (C : Type u) [Category.{v} C] :
    (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v).Full ∧ (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v).Faithful :=
  ⟨inferInstance, inferInstance⟩

variable {C_ff : Type u} [Category.{v} C_ff] {D_ff : Type u'} [Category.{v'} D_ff]
  (J_ff : C_ff ⥤ D_ff) [J_ff.Full] [J_ff.Faithful]

theorem lemma_4_3_7_a {A A' : C_ff} (f : A ⟶ A') : IsIso f ↔ IsIso (J_ff.map f) :=
  ⟨fun _ => inferInstance, fun _ => isIso_of_reflects_iso f J_ff⟩

noncomputable def lemma_4_3_7_b_iso {A A' : C_ff} (g : J_ff.obj A ≅ J_ff.obj A') : A ≅ A' :=
  J_ff.preimageIso g

theorem lemma_4_3_7_b {A A' : C_ff} (g : J_ff.obj A ≅ J_ff.obj A') :
    ∃! f : A ≅ A', J_ff.mapIso f = g := by
  use J_ff.preimageIso g
  refine ⟨by ext; simp [Functor.preimageIso], ?_⟩
  intro f hf
  rw [← hf]
  ext
  simp [Functor.preimageIso]

noncomputable def lemma_4_3_7_c_equiv (A A' : C_ff) : (A ≅ A') ≃ (J_ff.obj A ≅ J_ff.obj A') where
  toFun := J_ff.mapIso
  invFun := J_ff.preimageIso
  left_inv f := by ext; simp [Functor.preimageIso]
  right_inv g := by ext; simp [Functor.preimageIso]

theorem lemma_4_3_7_c (A A' : C_ff) : Nonempty (A ≅ A') ↔ Nonempty (J_ff.obj A ≅ J_ff.obj A') :=
  ⟨fun ⟨f⟩ => ⟨J_ff.mapIso f⟩, fun ⟨g⟩ => ⟨J_ff.preimageIso g⟩⟩

def example_4_3_8_neg_hom : Multiplicative ℤ →* Multiplicative ℤ where
  toFun n := Multiplicative.ofAdd (-n.toAdd)
  map_one' := by
    simp
  map_mul' := fun a b => by
    apply Multiplicative.toAdd.injective
    simp [add_comm]

def example_4_3_8_neg_iso : GrpCat.of (Multiplicative ℤ) ≅ GrpCat.of (Multiplicative ℤ) where
  hom := GrpCat.ofHom example_4_3_8_neg_hom
  inv := GrpCat.ofHom example_4_3_8_neg_hom
  hom_inv_id := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro n
    dsimp [example_4_3_8_neg_hom]
    apply Multiplicative.toAdd.injective
    simp
  inv_hom_id := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro n
    dsimp [example_4_3_8_neg_hom]
    apply Multiplicative.toAdd.injective
    simp

theorem example_4_3_8_aut_z_cases
    (f : GrpCat.of (Multiplicative ℤ) ≅ GrpCat.of (Multiplicative ℤ)) :
    f = Iso.refl _ ∨ f = example_4_3_8_neg_iso := by
  let f_hom : Multiplicative ℤ →* Multiplicative ℤ := f.hom.hom
  let f_inv : Multiplicative ℤ →* Multiplicative ℤ := f.inv.hom
  have h_comp : (f_hom (Multiplicative.ofAdd (1 : ℤ))).toAdd *
      (f_inv (Multiplicative.ofAdd (1 : ℤ))).toAdd = 1 := by
    have h : (f.hom ≫ f.inv).hom (Multiplicative.ofAdd (1 : ℤ)) = Multiplicative.ofAdd (1 : ℤ) := by
      rw [f.hom_inv_id]
      rfl
    have h2 : (f.hom ≫ f.inv).hom (Multiplicative.ofAdd (1 : ℤ)) =
        f_inv (f_hom (Multiplicative.ofAdd (1 : ℤ))) := rfl
    rw [h2] at h
    have h3 : f_inv (f_hom (Multiplicative.ofAdd (1 : ℤ))) =
        (f_inv (Multiplicative.ofAdd (1 : ℤ))) ^ (f_hom (Multiplicative.ofAdd (1 : ℤ))).toAdd := by
      have h4 : f_hom (Multiplicative.ofAdd (1 : ℤ)) =
          (Multiplicative.ofAdd (1 : ℤ)) ^ (f_hom (Multiplicative.ofAdd (1 : ℤ))).toAdd := by
        apply Multiplicative.toAdd.injective
        simp
      conv_lhs => rw [h4]
      rw [map_zpow]
    rw [h3] at h
    have h5 := congr_arg Multiplicative.toAdd h
    have h6 : ((f_inv (Multiplicative.ofAdd (1 : ℤ))) ^
        (f_hom (Multiplicative.ofAdd (1 : ℤ))).toAdd).toAdd =
        (f_hom (Multiplicative.ofAdd (1 : ℤ))).toAdd *
        (f_inv (Multiplicative.ofAdd (1 : ℤ))).toAdd := by
      simp
    rw [h6] at h5
    exact h5
  have h_cases : (f_hom (Multiplicative.ofAdd (1 : ℤ))).toAdd = 1 ∨
      (f_hom (Multiplicative.ofAdd (1 : ℤ))).toAdd = -1 := by
    have hu : IsUnit (f_hom (Multiplicative.ofAdd (1 : ℤ))).toAdd :=
      ⟨⟨(f_hom (Multiplicative.ofAdd (1 : ℤ))).toAdd, (f_inv (Multiplicative.ofAdd (1 : ℤ))).toAdd,
        h_comp,
        (mul_comm (f_hom (Multiplicative.ofAdd (1 : ℤ))).toAdd
          (f_inv (Multiplicative.ofAdd (1 : ℤ))).toAdd) ▸ h_comp⟩, rfl⟩
    exact Int.isUnit_iff.mp hu
  rcases h_cases with h1 | h1
  · left
    apply Iso.ext
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro (n : Multiplicative ℤ)
    have hn := example_4_3_5_zpow_eval f_hom n
    have h1' : f_hom (Multiplicative.ofAdd (1 : ℤ)) = Multiplicative.ofAdd (1 : ℤ) := by
      apply Multiplicative.toAdd.injective
      exact h1
    change f_hom n = n
    rw [hn, h1']
    apply Multiplicative.toAdd.injective
    simp
  · right
    apply Iso.ext
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro (n : Multiplicative ℤ)
    have hn := example_4_3_5_zpow_eval f_hom n
    have h1' : f_hom (Multiplicative.ofAdd (1 : ℤ)) = Multiplicative.ofAdd (-1 : ℤ) := by
      apply Multiplicative.toAdd.injective
      exact h1
    change f_hom n = example_4_3_8_neg_hom n
    rw [hn, h1']
    dsimp [example_4_3_8_neg_hom]
    apply Multiplicative.toAdd.injective
    simp

def example_4_3_8_aut_z : (GrpCat.of (Multiplicative ℤ) ≅ GrpCat.of (Multiplicative ℤ)) ≃ Bool where
  toFun f :=
    let z : ℤ := (f.hom.hom (Multiplicative.ofAdd (1 : ℤ)) : Multiplicative ℤ).toAdd
    decide (z = 1)
  invFun b := if b then Iso.refl _ else example_4_3_8_neg_iso
  left_inv f := by
    rcases example_4_3_8_aut_z_cases f with rfl | rfl
    · rfl
    · rfl
  right_inv b := by
    cases b <;> rfl

noncomputable def corollary_4_3_9_presheaf_equiv {C : Type u} [Category.{v} C] (A A' : C) :
    (yoneda.obj A ≅ yoneda.obj A') ≃ (A ≅ A') :=
  (lemma_4_3_7_c_equiv (J_ff := yoneda) A A').symm

theorem corollary_4_3_9_presheaf {C : Type u} [Category.{v} C] (A A' : C) :
    Nonempty (yoneda.obj A ≅ yoneda.obj A') ↔ Nonempty (A ≅ A') :=
  (lemma_4_3_7_c (J_ff := yoneda) A A').symm

def unopIsoEquiv {C : Type u} [Category.{v} C] (A A' : C) : (op A ≅ op A') ≃ (A ≅ A') where
  toFun e := e.unop.symm
  invFun e := e.symm.op
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

noncomputable def corollary_4_3_9_copresheaf_equiv {C : Type u} [Category.{v} C] (A A' : C) :
    (coyoneda.obj (op A) ≅ coyoneda.obj (op A')) ≃ (A ≅ A') :=
  (lemma_4_3_7_c_equiv (J_ff := coyoneda) (op A) (op A')).symm.trans (unopIsoEquiv A A')

theorem corollary_4_3_9_copresheaf {C : Type u} [Category.{v} C] (A A' : C) :
    Nonempty (coyoneda.obj (op A) ≅ coyoneda.obj (op A')) ↔ Nonempty (A ≅ A') :=
  ⟨fun ⟨e⟩ => ⟨corollary_4_3_9_copresheaf_equiv A A' e⟩,
   fun ⟨e⟩ => ⟨(corollary_4_3_9_copresheaf_equiv A A').symm e⟩⟩

theorem corollary_4_3_9 {C : Type u} [Category.{v} C] (A A' : C) :
    (Nonempty (yoneda.obj A ≅ yoneda.obj A') ↔ Nonempty (A ≅ A')) ∧
    (Nonempty (A ≅ A') ↔ Nonempty (coyoneda.obj (op A) ≅ coyoneda.obj (op A'))) :=
  ⟨corollary_4_3_9_presheaf A A', (corollary_4_3_9_copresheaf A A').symm⟩

def example_4_3_10_one (A A' : GrpCat.{u}) : (GrpCat.of PUnit ⟶ A) ≃ (GrpCat.of PUnit ⟶ A') where
  toFun _ := 1
  invFun _ := 1
  left_inv f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro ⟨⟩
    rw [map_one, map_one]
  right_inv f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro ⟨⟩
    rw [map_one, map_one]

def example_4_3_10_z_equiv (A : GrpCat.{0}) :
    (GrpCat.of (Multiplicative ℤ) ⟶ A) ≃ (forget GrpCat).obj A :=
  example_4_3_5_equiv A

def example_4_3_10_z (A A' : GrpCat.{0}) :
    Nonempty ((GrpCat.of (Multiplicative ℤ) ⟶ A) ≃ (GrpCat.of (Multiplicative ℤ) ⟶ A')) ↔
      Nonempty ((forget GrpCat).obj A ≃ (forget GrpCat).obj A') := by
  constructor
  · intro ⟨e⟩
    exact ⟨(example_4_3_10_z_equiv A).symm.trans (e.trans (example_4_3_10_z_equiv A'))⟩
  · intro ⟨e⟩
    exact ⟨(example_4_3_10_z_equiv A).trans (e.trans (example_4_3_10_z_equiv A').symm)⟩

def example_4_3_10_mul_to_add (n : ℕ) (A : GrpCat.{0}) :
    (GrpCat.of (Multiplicative (ZMod n)) ⟶ A) ≃
      (AddGrpCat.of (ZMod n) ⟶ AddGrpCat.of (Additive A)) where
  toFun f := AddGrpCat.ofHom f.hom.toAdditive
  invFun f := GrpCat.ofHom f.hom.toMultiplicative
  left_inv _ := rfl
  right_inv _ := rfl

def example_4_3_10_zmod (n : ℕ) (A : GrpCat.{0}) :
    (GrpCat.of (Multiplicative (ZMod n)) ⟶ A) ≃ {x : (forget GrpCat).obj A // x ^ n = 1} :=
  let e1 : (GrpCat.of (Multiplicative (ZMod n)) ⟶ A) ≃
      (AddGrpCat.of (ZMod n) ⟶ AddGrpCat.of (Additive A)) :=
    example_4_3_10_mul_to_add n A
  let e2 : (AddGrpCat.of (ZMod n) ⟶ AddGrpCat.of (Additive A)) ≃
      {g : Additive A // n • g = 0} :=
    Representables.exercise_4_1_3_equiv n (AddGrpCat.of (Additive A))
  let e3 : {g : Additive A // n • g = 0} ≃ {x : (forget GrpCat).obj A // x ^ n = 1} :=
    { toFun := fun ⟨g, hg⟩ => ⟨g.toMul, by
        have : Additive.ofMul (g.toMul ^ n) = n • g := ofMul_pow n g.toMul
        rw [← ofMul_eq_zero, this]
        exact hg⟩
      invFun := fun ⟨x, hx⟩ => ⟨Additive.ofMul x, by
        have : n • Additive.ofMul x = Additive.ofMul (x ^ n) := (ofMul_pow n x).symm
        rw [this, hx]
        rfl⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  e1.trans (e2.trans e3)

def example_4_3_11_equiv (A : Type u) : A ≃ (PUnit.{u + 1} ⟶ A) where
  toFun a := ↾fun _ => a
  invFun f := (f : PUnit.{u + 1} → A) PUnit.unit
  left_inv _ := rfl
  right_inv f := by
    ext ⟨⟩
    rfl

def example_4_3_11_iso (A : Type u) : A ≅ (PUnit.{u + 1} ⟶ A) :=
  Equiv.toIso (example_4_3_11_equiv A)

def example_4_3_11 {A A' : Type u}
    (e : (PUnit.{u + 1} ⟶ A) ≅ (PUnit.{u + 1} ⟶ A')) : A ≅ A' :=
  (example_4_3_11_iso A).trans (e.trans (example_4_3_11_iso A').symm)

def exercise_4_3_4_functor (B : Type u) [Category.{v} B] {C : Type u'} [Category.{v'} C]
    {D : Type u''} [Category.{v''} D] (J : C ⥤ D) : (B ⥤ C) ⥤ (B ⥤ D) where
  obj F := F ⋙ J
  map α := {
    app := fun X => J.map (α.app X)
    naturality := fun X Y f => by
      dsimp
      rw [← J.map_comp, α.naturality, J.map_comp]
  }
  map_id F := by
    ext X
    dsimp
    rw [J.map_id]
  map_comp α β := by
    ext X
    dsimp
    rw [J.map_comp]

instance exercise_4_3_4_a_faithful (B : Type u) [Category.{v} B] {C : Type u'} [Category.{v'} C]
    {D : Type u''} [Category.{v''} D] (J : C ⥤ D) [J.Faithful] :
    (exercise_4_3_4_functor B J).Faithful where
  map_injective {F G} f g h := by
    ext X
    apply J.map_injective
    exact congr_fun (congr_arg NatTrans.app h) X

instance exercise_4_3_4_a_full (B : Type u) [Category.{v} B] {C : Type u'} [Category.{v'} C]
    {D : Type u''} [Category.{v''} D] (J : C ⥤ D) [J.Full] [J.Faithful] :
    (exercise_4_3_4_functor B J).Full where
  map_surjective {F G} θ := by
    refine ⟨{
      app := fun X => J.preimage (θ.app X)
      naturality := fun X Y f => by
        apply J.map_injective
        rw [J.map_comp, J.map_comp, J.map_preimage, J.map_preimage]
        exact θ.naturality f
    }, ?_⟩
    ext X
    dsimp [exercise_4_3_4_functor]
    exact J.map_preimage (θ.app X)

theorem exercise_4_3_4_a (B : Type u) [Category.{v} B] {C : Type u'} [Category.{v'} C]
    {D : Type u''} [Category.{v''} D] (J : C ⥤ D) [J.Full] [J.Faithful] :
    (exercise_4_3_4_functor B J).Full ∧ (exercise_4_3_4_functor B J).Faithful :=
  ⟨inferInstance, inferInstance⟩

noncomputable def exercise_4_3_4_b {B : Type u} [Category.{v} B] {C : Type u'} [Category.{v'} C]
    {D : Type u''} [Category.{v''} D] (J : C ⥤ D) [J.Full] [J.Faithful]
    (G G' : B ⥤ C) (e : G ⋙ J ≅ G' ⋙ J) : G ≅ G' :=
  (exercise_4_3_4_functor B J).preimageIso e

noncomputable def exercise_4_3_4_c {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
    {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' := by
  let J : C ⥤ Cᵒᵖ ⥤ Type v := yoneda
  have e : G ⋙ J ≅ G' ⋙ J :=
    NatIso.ofComponents
      (fun B => NatIso.ofComponents
        (fun A => ((adj1.homEquiv (unop A) B).symm.trans (adj2.homEquiv (unop A) B)).toIso)
        (fun {A A'} f => by
          ext (g : unop A ⟶ G.obj B)
          have h1 := adj1.homEquiv_naturality_left_symm f.unop g
          have h2 := adj2.homEquiv_naturality_left f.unop ((adj1.homEquiv (unop A) B).symm g)
          change (adj2.homEquiv (unop A') B) ((adj1.homEquiv (unop A') B).symm (f.unop ≫ g)) =
            f.unop ≫ (adj2.homEquiv (unop A) B) ((adj1.homEquiv (unop A) B).symm g)
          rw [h1, h2])
        )
      (fun {B B'} g => by
        ext A (h : unop A ⟶ G.obj B)
        have h1 := adj1.homEquiv_naturality_right_symm h g
        have h2 := adj2.homEquiv_naturality_right ((adj1.homEquiv (unop A) B).symm h) g
        change (adj2.homEquiv (unop A) B') ((adj1.homEquiv (unop A) B').symm (h ≫ G.map g)) =
          (adj2.homEquiv (unop A) B) ((adj1.homEquiv (unop A) B).symm h) ≫ G'.map g
        rw [h1, h2])
  exact exercise_4_3_4_b J G G' e

noncomputable def example_4_3_12_right {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
    {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
  exercise_4_3_4_c adj1 adj2

noncomputable def example_4_3_12_left {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
    {G : D ⥤ C} {F F' : C ⥤ D} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' := by
  let J : Dᵒᵖ ⥤ D ⥤ Type v := coyoneda
  have e : (Functor.op F) ⋙ J ≅ (Functor.op F') ⋙ J :=
    NatIso.ofComponents
      (fun A => NatIso.ofComponents
        (fun B => ((adj1.homEquiv (unop A) B).trans (adj2.homEquiv (unop A) B).symm).toIso)
        (fun {B B'} g => by
          ext (h : F.obj (unop A) ⟶ B)
          have h1 := adj1.homEquiv_naturality_right h g
          have h2 := adj2.homEquiv_naturality_right_symm (adj1.homEquiv (unop A) B h) g
          change (adj2.homEquiv (unop A) B').symm ((adj1.homEquiv (unop A) B') (h ≫ g)) =
            (adj2.homEquiv (unop A) B).symm ((adj1.homEquiv (unop A) B) h) ≫ g
          rw [h1, h2])
        )
      (fun {A A'} f => by
        ext B (h : F.obj (unop A) ⟶ B)
        have h1 := adj1.homEquiv_naturality_left f.unop h
        have h2 := adj2.homEquiv_naturality_left_symm f.unop (adj1.homEquiv (unop A) B h)
        change (adj2.homEquiv (unop A') B).symm ((adj1.homEquiv (unop A') B) (F.map f.unop ≫ h)) =
          F'.map f.unop ≫ (adj2.homEquiv (unop A) B).symm ((adj1.homEquiv (unop A) B) h)
        rw [h1, h2])
  have e_iso : Functor.op F ≅ Functor.op F' := exercise_4_3_4_b J (Functor.op F) (Functor.op F') e
  exact (NatIso.removeOp e_iso).symm

noncomputable def example_4_3_13 (k : Type u) [CommRing k] (T T' : ModuleCat.{u} k)
    (e : coyoneda.obj (op T) ≅ coyoneda.obj (op T')) : T ≅ T' :=
  corollary_4_3_9_copresheaf_equiv T T' e

abbrev exercise_4_3_1_a := @lemma_4_3_7_a
abbrev exercise_4_3_1_b := @lemma_4_3_7_b
abbrev exercise_4_3_1_c := @lemma_4_3_7_c

theorem exercise_4_3_2_a (C : Type u) [Category.{v} C] :
    (yoneda : C ⥤ Cᵒᵖ ⥤ Type v).Faithful where
  map_injective {X Y} f g h := by
    have h_app := congr_fun (congr_arg (fun (α : yoneda.obj X ⟶ yoneda.obj Y) =>
      (α.app (op X) : (X ⟶ X) → (X ⟶ Y))) h) (𝟙 X)
    dsimp [yoneda] at h_app
    rw [Category.id_comp, Category.id_comp] at h_app
    exact h_app

theorem exercise_4_3_2_b (C : Type u) [Category.{v} C] :
    (yoneda : C ⥤ Cᵒᵖ ⥤ Type v).Full where
  map_surjective {X Y} α := by
    let f : X ⟶ Y := α.app (op X) (𝟙 X)
    use f
    ext ⟨Z⟩ (g : Z ⟶ X)
    dsimp [yoneda]
    have h := α.naturality_apply g.op (𝟙 X)
    dsimp at h
    rw [Category.comp_id] at h
    exact h.symm

noncomputable def exercise_4_3_2_c {C : Type u} [Category.{v} C] {A : C} {X : Cᵒᵖ ⥤ Type v}
    {u : X.obj (op A)} (hu : def_4_3_1_universal_element X A u) : X ≅ yoneda.obj A :=
  letI : IsIso (theorem_4_2_1_ynt u) := (corollary_4_3_1_isIso_iff u).mpr hu
  (asIso (theorem_4_2_1_ynt u)).symm

end Representables
