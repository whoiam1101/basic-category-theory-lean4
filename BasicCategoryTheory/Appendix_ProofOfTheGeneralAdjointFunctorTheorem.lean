-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Limits.Constructions.WeaklyInitial
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Creates
import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.Categories
import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.Functors
import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.NaturalTransformations
import BasicCategoryTheory.Chapter2_Adjoints.Adjoints
import BasicCategoryTheory.Chapter5_Limits.LimitsAndExamples
import BasicCategoryTheory.Chapter5_Limits.InteractionsBetweenFunctorsAndLimits
import BasicCategoryTheory.Chapter6_AdjointsRepresentablesAndLimits.LimitsInTermsOfRepresentablesAndAdjoints
import BasicCategoryTheory.Chapter6_AdjointsRepresentablesAndLimits.InteractionsBetweenAdjointFunctorsAndLimits

namespace Appendix_ProofOfTheGeneralAdjointFunctorTheorem

universe u v u₁ v₁ u₂ v₂ w w'

open CategoryTheory Limits

theorem theorem_gaft_forward {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) [G.IsRightAdjoint] :
    PreservesLimitsOfSize.{w, w} G ∧ SolutionSetCondition.{w} G :=
  ⟨Adjunction.rightAdjoint_preservesLimits (Adjunction.ofIsRightAdjoint G),
   solutionSetCondition_of_isRightAdjoint G⟩

@[reducible]
noncomputable def theorem_gaft_backward {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    [HasLimits B] (G : B ⥤ A) [PreservesLimitsOfSize.{v₂, v₂} G]
    (hG : SolutionSetCondition.{v₂} G) :
    G.IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_solutionSetCondition G hG

theorem theorem_gaft_of_comma_initials {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (h_init : ∀ X : A, HasInitial (StructuredArrow X G)) :
    G.IsRightAdjoint :=
  isRightAdjointOfStructuredArrowInitials G

noncomputable def lemma_A_1_isInitial_of_isLimit {S : Type v} [Category.{v} S]
    {C : Type u} [Category.{v} C]
    (F : S ⥤ C) [F.Full]
    (hS : ∀ X : C, ∃ s : S, Nonempty (F.obj s ⟶ X))
    (c : Cone F) (hc : IsLimit c) [HasEqualizers C] :
    IsInitial c.pt := by
  have hu : ∀ X : C, Unique (c.pt ⟶ X) := by
    intro X
    let s_desc := (hS X).choose
    let j_desc := (hS X).choose_spec.some
    refine ⟨⟨c.π.app s_desc ≫ j_desc⟩, ?_⟩
    intro f
    have h_eq : ∀ g : c.pt ⟶ X, f = g := by
      intro g
      let E := equalizer f g
      let i : E ⟶ c.pt := equalizer.ι f g
      let s := (hS E).choose
      let h : F.obj s ⟶ E := (hS E).choose_spec.some
      have h_id : c.π.app s ≫ h ≫ i = 𝟙 c.pt := by
        apply hc.hom_ext
        intro s'
        let α : s ⟶ s' := F.preimage (h ≫ i ≫ c.π.app s')
        have hα : F.map α = h ≫ i ≫ c.π.app s' := F.map_preimage (h ≫ i ≫ c.π.app s')
        have h_lhs : (c.π.app s ≫ h ≫ i) ≫ c.π.app s' = c.π.app s' := by
          calc (c.π.app s ≫ h ≫ i) ≫ c.π.app s'
            _ = c.π.app s ≫ (h ≫ i ≫ c.π.app s') := by simp only [Category.assoc]
            _ = c.π.app s ≫ F.map α := by rw [← hα]
            _ = c.π.app s' := c.w α
        have h_rhs : 𝟙 c.pt ≫ c.π.app s' = c.π.app s' := Category.id_comp (c.π.app s')
        exact h_lhs.trans h_rhs.symm
      have hfg : (c.π.app s ≫ h ≫ i) ≫ f = (c.π.app s ≫ h ≫ i) ≫ g := by
        calc (c.π.app s ≫ h ≫ i) ≫ f
          _ = (c.π.app s ≫ h) ≫ i ≫ f := by simp only [Category.assoc]
          _ = (c.π.app s ≫ h) ≫ i ≫ g := by rw [equalizer.condition f g]
          _ = (c.π.app s ≫ h ≫ i) ≫ g := by simp only [Category.assoc]
      rw [h_id] at hfg
      have hf : 𝟙 c.pt ≫ f = f := Category.id_comp f
      have hg : 𝟙 c.pt ≫ g = g := Category.id_comp g
      exact (hf.symm.trans hfg).trans hg
    exact h_eq _
  exact @IsInitial.ofUnique _ _ c.pt hu

theorem lemma_A_1_hasInitial {C : Type u} [Category.{v} C] [HasLimits C]
    {ι : Type v} (S : ι → C) (hS : ∀ X : C, ∃ i, Nonempty (S i ⟶ X)) :
    HasInitial C := by
  have ⟨T, hT⟩ := has_weakly_initial_of_weakly_initial_set_and_hasProducts hS
  exact hasInitial_of_weakly_initial_and_hasWideEqualizers hT

theorem lemma_A_1 {C : Type u} [Category.{v} C] [HasLimits C]
    {ι : Type v} (S : ι → C) (hS : ∀ X : C, ∃ i, Nonempty (S i ⟶ X)) :
    ∃ (I : C), Nonempty (IsInitial I) := by
  haveI : HasInitial C := lemma_A_1_hasInitial S hS
  exact ⟨⊥_ C, ⟨initialIsInitial⟩⟩

noncomputable instance lemma_A_2_proj_createsLimitsOfShape {J : Type w} [Category.{w'} J]
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) [PreservesLimitsOfShape J G] :
    CreatesLimitsOfShape J (StructuredArrow.proj X G) :=
  StructuredArrow.createsLimitsOfShape

noncomputable instance lemma_A_2_proj_createsLimitsOfSize
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) [PreservesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (StructuredArrow.proj X G) :=
  StructuredArrow.createsLimitsOfSize

instance lemma_A_2_comma_hasLimitsOfShape {J : Type w} [Category.{w'} J]
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) [HasLimitsOfShape J B] [PreservesLimitsOfShape J G] :
    HasLimitsOfShape J (StructuredArrow X G) :=
  StructuredArrow.hasLimitsOfShape

instance lemma_A_2_comma_hasLimitsOfSize
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) [HasLimitsOfSize.{w, w'} B] [PreservesLimitsOfSize.{w, w'} G] :
    HasLimitsOfSize.{w, w'} (StructuredArrow X G) :=
  StructuredArrow.hasLimitsOfSize

instance lemma_A_2_comma_complete
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) [HasLimits B] [PreservesLimitsOfSize.{v₂, v₂} G] :
    HasLimitsOfSize.{v₂, v₂} (StructuredArrow X G) :=
  StructuredArrow.hasLimitsOfSize

@[reducible]
noncomputable def theorem_gaft_proof {A : Type u₁} [Category.{v₂} A] {B : Type u₂} [Category.{v₂} B]
    [HasLimits B] (G : B ⥤ A) [PreservesLimitsOfSize.{v₂, v₂} G]
    (h_wi : ∀ X : A, ∃ (ι : Type v₂) (S : ι → StructuredArrow X G),
      ∀ Y : StructuredArrow X G, ∃ i, Nonempty (S i ⟶ Y)) :
    G.IsRightAdjoint := by
  apply theorem_gaft_of_comma_initials
  intro X
  obtain ⟨ι, S, hS⟩ := h_wi X
  haveI : HasLimitsOfSize.{v₂, v₂} (StructuredArrow X G) := lemma_A_2_comma_complete G X
  exact lemma_A_1_hasInitial S hS

def exercise_A_1_a_cone {B : Type u} [Category.{v} B] (I : B) (hI : IsInitial I) :
    Cone (𝟭 B) where
  pt := I
  π := {
    app := fun X => hI.to X
    naturality := fun X Y f => by
      dsimp
      rw [Category.id_comp]
      exact (hI.hom_ext (hI.to X ≫ f) (hI.to Y)).symm
  }

def exercise_A_1_a_isLimit {B : Type u} [Category.{v} B] (I : B) (hI : IsInitial I) :
    IsLimit (exercise_A_1_a_cone I hI) where
  lift s := s.π.app I
  fac s X := by
    dsimp [exercise_A_1_a_cone]
    have h := s.w (hI.to X)
    dsimp at h
    exact h
  uniq s m hm := by
    have h := hm I
    dsimp [exercise_A_1_a_cone] at h
    have h_id : hI.to I = 𝟙 I := hI.hom_ext (hI.to I) (𝟙 I)
    have h_comp : m ≫ 𝟙 I = m := Category.comp_id m
    have hm_to : m ≫ hI.to I = m ≫ 𝟙 I := by rw [h_id]
    exact h_comp.symm.trans (hm_to.symm.trans h)

theorem exercise_A_1_b_proj_id {B : Type u} [Category.{v} B] (c : Cone (𝟭 B)) (hc : IsLimit c) :
    c.π.app c.pt = 𝟙 c.pt := by
  apply hc.hom_ext
  intro X
  have h := c.w (c.π.app X)
  dsimp at h
  have h_id : 𝟙 c.pt ≫ c.π.app X = c.π.app X := Category.id_comp (c.π.app X)
  exact h.trans h_id.symm

def exercise_A_1_b_isInitial {B : Type u} [Category.{v} B] (c : Cone (𝟭 B)) (hc : IsLimit c) :
    IsInitial c.pt := by
  have hu : ∀ X : B, Unique (c.pt ⟶ X) := by
    intro X
    refine ⟨⟨c.π.app X⟩, ?_⟩
    intro f
    have hnat : c.π.app c.pt ≫ f = c.π.app X := c.w f
    have h_id : c.π.app c.pt = 𝟙 c.pt := exercise_A_1_b_proj_id c hc
    have hf : 𝟙 c.pt ≫ f = f := Category.id_comp f
    have h_rw : 𝟙 c.pt ≫ f = c.π.app X := by
      rw [← h_id]
      exact hnat
    exact hf.symm.trans h_rw
  exact @IsInitial.ofUnique _ _ c.pt hu

def exercise_A_2_a_is_weakly_initial {C : Type*} [Preorder C] (S : Set C) : Prop :=
  ∀ c : C, ∃ s ∈ S, s ≤ c

theorem exercise_A_2_a_iff {C : Type*} [Preorder C] (S : Set C) :
    (∀ c : C, ∃ s ∈ S, Nonempty (s ⟶ c)) ↔ (∀ c : C, ∃ s ∈ S, s ≤ c) := by
  constructor
  · intro h c
    obtain ⟨s, hs, ⟨f⟩⟩ := h c
    exact ⟨s, hs, leOfHom f⟩
  · intro h c
    obtain ⟨s, hs, hle⟩ := h c
    exact ⟨s, hs, ⟨homOfLE hle⟩⟩

theorem exercise_A_2_b_isGLB {C : Type*} [Preorder C] (S : Set C) (m : C)
    (hm : IsGLB S m) (hS : ∀ c : C, ∃ s ∈ S, s ≤ c) :
    ∀ c : C, m ≤ c := by
  intro c
  obtain ⟨s, hs, hle⟩ := hS c
  have hm_le_s : m ≤ s := hm.1 hs
  exact hm_le_s.trans hle

theorem exercise_A_2_b_sInf {C : Type*} [CompleteSemilatticeInf C] (S : Set C)
    (hS : ∀ c : C, ∃ s ∈ S, s ≤ c) :
    ∀ c : C, sInf S ≤ c := by
  intro c
  obtain ⟨s, hs, hle⟩ := hS c
  have hsInf_le : sInf S ≤ s := sInf_le hs
  exact hsInf_le.trans hle

theorem exercise_A_2_b_isLeast {C : Type*} [Preorder C] (S : Set C) (m : C)
    (hm : IsGLB S m) (hS : ∀ c : C, ∃ s ∈ S, s ≤ c) :
    IsLeast (Set.univ : Set C) m :=
  ⟨Set.mem_univ m, fun c _ => exercise_A_2_b_isGLB S m hm hS c⟩

def exercise_A_3_a_diagram {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) {I : Type w} [Category.{w'} I]
    (F : I ⥤ StructuredArrow X G) : I ⥤ B :=
  F ⋙ StructuredArrow.proj X G

def exercise_A_3_a_cone {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) {I : Type w} [Category.{w'} I]
    (F : I ⥤ StructuredArrow X G) :
    (Functor.const I).obj X ⟶ exercise_A_3_a_diagram G X F ⋙ G where
  app i := (F.obj i).hom
  naturality i j f := by
    dsimp
    rw [Category.id_comp]
    exact (F.map f).w.symm

def exercise_A_3_a_mk {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) {I : Type w} [Category.{w'} I]
    (E : I ⥤ B) (α : (Functor.const I).obj X ⟶ E ⋙ G) :
    I ⥤ StructuredArrow X G where
  obj i := StructuredArrow.mk (α.app i)
  map {i j} f := StructuredArrow.homMk (E.map f) (by
    have h := α.naturality f
    dsimp at h
    rw [Category.id_comp] at h
    exact h.symm)
  map_id i := by
    apply StructuredArrow.hom_ext
    dsimp
    exact E.map_id i
  map_comp {i j k} f g := by
    apply StructuredArrow.hom_ext
    dsimp
    exact E.map_comp f g

def exercise_A_3_a_iso {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) {I : Type w} [Category.{w'} I]
    (F : I ⥤ StructuredArrow X G) :
    exercise_A_3_a_mk G X (exercise_A_3_a_diagram G X F) (exercise_A_3_a_cone G X F) ≅ F :=
  NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} f => by
    apply CommaMorphism.ext
    · rfl
    · change (F.map f).right ≫ 𝟙 _ = 𝟙 _ ≫ (F.map f).right
      rw [Category.comp_id, Category.id_comp])

theorem exercise_A_3_a_proj {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) {I : Type w} [Category.{w'} I]
    (E : I ⥤ B) (α : (Functor.const I).obj X ⟶ E ⋙ G) :
    exercise_A_3_a_mk G X E α ⋙ StructuredArrow.proj X G = E :=
  rfl

theorem exercise_A_3_a_hom {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) {I : Type w} [Category.{w'} I]
    (E : I ⥤ B) (α : (Functor.const I).obj X ⟶ E ⋙ G) (i : I) :
    ((exercise_A_3_a_mk G X E α).obj i).hom = α.app i :=
  rfl

noncomputable instance exercise_A_3_b_proj_createsLimitsOfShape
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A) {I : Type w} [Category.{w'} I]
    [PreservesLimitsOfShape I G] :
    CreatesLimitsOfShape I (StructuredArrow.proj X G) :=
  StructuredArrow.createsLimitsOfShape

noncomputable instance exercise_A_3_b_proj_createsLimitsOfSize
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (G : B ⥤ A) (X : A)
    [PreservesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (StructuredArrow.proj X G) :=
  StructuredArrow.createsLimitsOfSize

end Appendix_ProofOfTheGeneralAdjointFunctorTheorem
