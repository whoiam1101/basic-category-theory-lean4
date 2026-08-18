-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Types
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.Functors
import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.NaturalTransformations
import BasicCategoryTheory.Chapter2_Adjoints.Adjoints
import BasicCategoryTheory.Chapter4_Representables.DefinitionsAndExamples
import BasicCategoryTheory.Chapter4_Representables.YonedaLemma
import BasicCategoryTheory.Chapter4_Representables.ConsequencesOfTheYonedaLemma
import BasicCategoryTheory.Chapter5_Limits.LimitsAndExamples
import BasicCategoryTheory.Chapter5_Limits.ColimitsAndExamples
import BasicCategoryTheory.Chapter5_Limits.InteractionsBetweenFunctorsAndLimits
import BasicCategoryTheory.Chapter6_AdjointsRepresentablesAndLimits.LimitsInTermsOfRepresentablesAndAdjoints
import BasicCategoryTheory.Chapter6_AdjointsRepresentablesAndLimits.LimitsAndColimitsOfPresheaves

namespace InteractionsBetweenAdjointFunctorsAndLimits

universe u v u' v' u₁ v₁ u₂ v₂ w

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory

@[reducible]
def theorem_6_3_1_leftAdjoint_preservesColimits {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesColimitsOfSize.{w, w} F :=
  Adjunction.leftAdjoint_preservesColimits adj

@[reducible]
def theorem_6_3_1_rightAdjoint_preservesLimits {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesLimitsOfSize.{w, w} G :=
  Adjunction.rightAdjoint_preservesLimits adj

noncomputable def theorem_6_3_1_limitCone_of_rightAdjoint {I : Type w} [Category.{w} I]
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {K : I ⥤ D} (c : Cone K) (hc : IsLimit c) :
    IsLimit (G.mapCone c) := by
  haveI : PreservesLimitsOfSize.{w, w} G := Adjunction.rightAdjoint_preservesLimits adj
  exact isLimitOfPreserves G hc

noncomputable def theorem_6_3_1_colimitCocone_of_leftAdjoint {I : Type w} [Category.{w} I]
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {K : I ⥤ C} (c : Cocone K) (hc : IsColimit c) :
    IsColimit (F.mapCocone c) := by
  haveI : PreservesColimitsOfSize.{w, w} F := Adjunction.leftAdjoint_preservesColimits adj
  exact isColimitOfPreserves F hc

def theorem_6_3_1_adj_cone_iso {I : Type w} [Category.{w} I] {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (K : I ⥤ D) (A : C) :
    ((Functor.const I).obj (F.obj A) ⟶ K) ≃ ((Functor.const I).obj A ⟶ K ⋙ G) where
  toFun π := {
    app := fun j => (adj.homEquiv A (K.obj j)) (π.app j)
    naturality := fun i j f => by
      dsimp
      rw [Category.id_comp]
      have hnat : π.app j = π.app i ≫ K.map f := by
        have h := π.naturality f
        dsimp at h
        rw [Category.id_comp] at h
        exact h
      rw [hnat]
      exact adj.homEquiv_naturality_right (π.app i) (K.map f)
  }
  invFun σ := {
    app := fun j => (adj.homEquiv A (K.obj j)).symm (σ.app j)
    naturality := fun i j f => by
      dsimp
      rw [Category.id_comp]
      have hnat : σ.app j = σ.app i ≫ G.map (K.map f) := by
        have h := σ.naturality f
        dsimp at h
        rw [Category.id_comp] at h
        exact h
      rw [hnat]
      exact adj.homEquiv_naturality_right_symm (σ.app i) (K.map f)
  }
  left_inv π := by
    ext j
    dsimp
    exact (adj.homEquiv A (K.obj j)).left_inv (π.app j)
  right_inv σ := by
    ext j
    dsimp
    exact (adj.homEquiv A (K.obj j)).right_inv (σ.app j)

@[reducible]
def example_6_3_2_forgetful_preservesLimits {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (G : D ⥤ C) [G.IsRightAdjoint] :
    PreservesLimitsOfSize.{w, w} G :=
  Adjunction.rightAdjoint_preservesLimits (Adjunction.ofIsRightAdjoint G)

def example_6_3_3_set_distrib_empty (B : Type u) :
    PEmpty × B ≃ PEmpty where
  toFun := fun ⟨e, _⟩ => e
  invFun := fun e => e.elim
  left_inv := fun ⟨e, _⟩ => e.elim
  right_inv := fun e => e.elim

def example_6_3_3_set_distrib_sum (A₁ A₂ B : Type u) :
    (A₁ ⊕ A₂) × B ≃ (A₁ × B) ⊕ (A₂ × B) where
  toFun := fun (x, b) => match x with
    | Sum.inl a₁ => Sum.inl (a₁, b)
    | Sum.inr a₂ => Sum.inr (a₂, b)
  invFun := fun s => match s with
    | Sum.inl (a₁, b) => (Sum.inl a₁, b)
    | Sum.inr (a₂, b) => (Sum.inr a₂, b)
  left_inv := fun (x, b) => by cases x <;> rfl
  right_inv := fun s => by cases s <;> rfl

def example_6_3_3_set_codist_unit (B : Type u) :
    (B → PUnit) ≃ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ _ => PUnit.unit
  left_inv := fun _ => by funext _; cases PUnit.unit; rfl
  right_inv := fun ⟨⟩ => rfl

def example_6_3_3_set_codist_prod (A₁ A₂ B : Type u) :
    (B → A₁ × A₂) ≃ (B → A₁) × (B → A₂) where
  toFun := fun f => (fun b => (f b).1, fun b => (f b).2)
  invFun := fun (f, g) b => (f b, g b)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[reducible]
noncomputable def example_6_3_4_limit_commutes_with_limit {I : Type w} [Category.{w} I]
    {C : Type u₁} [Category.{v₁} C] [HasLimitsOfShape I C] :
    PreservesLimitsOfSize.{w, w} (lim (J := I) (C := C)) :=
  Adjunction.rightAdjoint_preservesLimits (constLimAdj (C := C) (J := I))

theorem example_6_3_5_no_left_adjoint_of_initial {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [HasInitial C] (G : D ⥤ C) (h_no_init : ∀ X : D, ¬ Nonempty (IsInitial X))
    (h_adj : Nonempty G.IsRightAdjoint) : False := by
  rcases h_adj with ⟨h_right⟩
  haveI := h_right
  let F := G.leftAdjoint
  haveI : PreservesColimitsOfSize.{0, 0} F :=
    Adjunction.leftAdjoint_preservesColimits (Adjunction.ofIsRightAdjoint G)
  have h_init : IsInitial (F.obj (⊥_ C)) := IsInitial.isInitialObj F (⊥_ C) initialIsInitial
  exact h_no_init (F.obj (⊥_ C)) ⟨h_init⟩

abbrev def_6_3_6_complete (C : Type u) [Category.{v} C] : Prop :=
  HasLimits C

abbrev def_6_3_6_cocomplete (C : Type u) [Category.{v} C] : Prop :=
  HasColimits C

def proposition_6_3_7_oaft_left_adjoint_formula {α β : Type*} [Preorder α]
    [CompleteSemilatticeInf β] (u : β → α) (a : α) : β :=
  sInf { b : β | a ≤ u b }

theorem proposition_6_3_7_oaft_galoisConnection {α β : Type*} [Preorder α]
    [CompleteSemilatticeInf β] (u : β → α) (hu_mono : Monotone u)
    (hu_inf : ∀ a : α, a ≤ u (sInf { b : β | a ≤ u b })) :
    GaloisConnection (proposition_6_3_7_oaft_left_adjoint_formula u) u := by
  intro a b
  constructor
  · intro h
    have h1 : a ≤ u (sInf { b' | a ≤ u b' }) := hu_inf a
    have h2 : u (sInf { b' | a ≤ u b' }) ≤ u b := hu_mono h
    exact h1.trans h2
  · intro h
    exact sInf_le h

theorem proposition_6_3_7_oaft_iff_completeLattice {α β : Type*} [CompleteLattice α]
    [CompleteLattice β] (u : β → α) (hu_mono : Monotone u) :
    (∃ l : α → β, GaloisConnection l u) ↔ (∀ s : Set β, u (sInf s) = ⨅ b ∈ s, u b) := by
  constructor
  · rintro ⟨l, gc⟩
    intro s
    exact gc.u_sInf
  · intro hu
    refine ⟨proposition_6_3_7_oaft_left_adjoint_formula u, ?_⟩
    apply proposition_6_3_7_oaft_galoisConnection u hu_mono
    intro a
    rw [hu]
    apply le_iInf
    intro b
    apply le_iInf
    intro hb
    exact hb

theorem example_6_3_8_complete_poset_has_bot {β : Type*} [CompleteLattice β] :
    (sInf (Set.univ : Set β)) = ⊥ :=
  sInf_univ

theorem example_6_3_8_sSup_as_sInf {β : Type*} [CompleteLattice β] (S : Set β) :
    sSup S = sInf { b : β | ∀ s ∈ S, s ≤ b } := by
  apply le_antisymm
  · apply le_sInf
    intro b hb
    exact (sSup_le_iff.2) (fun s hs => hb s hs)
  · apply sInf_le
    intro s hs
    exact le_sSup hs

def def_6_3_9_weakly_initial_family {C : Type u} [Category.{v} C] {ι : Type w} (S : ι → C) : Prop :=
  ∀ X : C, ∃ i : ι, Nonempty (S i ⟶ X)

def def_6_3_9_is_weakly_initial_set {C : Type u} [Category.{v} C] (S : Set C) : Prop :=
  ∀ X : C, ∃ s ∈ S, Nonempty (s ⟶ X)

def def_6_3_9_solution_set_condition {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : D ⥤ C) : Prop :=
  SolutionSetCondition.{v₂} G

theorem theorem_6_3_10_gaft_forward {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : D ⥤ C) [G.IsRightAdjoint] :
    PreservesLimitsOfSize.{w, w} G ∧ SolutionSetCondition.{w} G :=
  ⟨Adjunction.rightAdjoint_preservesLimits (Adjunction.ofIsRightAdjoint G),
   solutionSetCondition_of_isRightAdjoint G⟩

@[reducible]
noncomputable def theorem_6_3_10_gaft_backward {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [HasLimits D] (G : D ⥤ C) [PreservesLimitsOfSize.{v₂, v₂} G]
    (hG : SolutionSetCondition.{v₂} G) :
    G.IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_solutionSetCondition G hG

@[reducible]
noncomputable def theorem_6_3_13_saft {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    [HasLimits D] [WellPowered.{v} D] {P : ObjectProperty D} [ObjectProperty.Small.{v} P]
    (hP : P.IsCoseparating) (G : D ⥤ C) [PreservesLimits G] :
    G.IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating hP G

class def_6_3_15_cartesian_closed (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] :
    Type (max u v) where
  closed : MonoidalClosed C

def def_6_3_15_exp_adjunction {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [MonoidalClosed C] (B : C) :
    tensorLeft B ⊣ ihom B :=
  ihom.adjunction B

def def_6_3_15_exp_hom_equiv {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [MonoidalClosed C] (A B C' : C) :
    (B ⊗ A ⟶ C') ≃ (A ⟶ (ihom B).obj C') :=
  (ihom.adjunction B).homEquiv A C'

@[reducible]
def example_6_3_16_types_cartesian_closed : MonoidalClosed (Type u) :=
  inferInstance

instance theorem_6_3_20_presheaf_cartesian_closed (A : Type u) [Category.{v} A] :
    MonoidalClosed (Aᵒᵖ ⥤ Type (max w v u)) :=
  FunctorToTypes.monoidalClosed

def theorem_6_3_20_exponential_eval {A : Type u} [SmallCategory A]
    (Y Z : Aᵒᵖ ⥤ Type u) (X : A) :
    ((ihom Y).obj Z).obj (op X) ≃ (Y ⊗ (yoneda (C := A)).obj X ⟶ Z) :=
  yonedaEquiv.symm.trans ((ihom.adjunction Y).homEquiv ((yoneda (C := A)).obj X) Z).symm

theorem exercise_6_3_1_a_no_right_adjoint {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (G : C ⥤ D) (X : C) (hX : IsInitial X)
    (hGX : ¬ Nonempty (IsInitial (G.obj X)))
    (h_adj : Nonempty G.IsLeftAdjoint) : False := by
  rcases h_adj with ⟨h_left⟩
  haveI := h_left
  haveI : PreservesColimitsOfSize.{0, 0} G :=
    Adjunction.leftAdjoint_preservesColimits (Adjunction.ofIsLeftAdjoint G)
  have h_init : IsInitial (G.obj X) := IsInitial.isInitialObj G X hX
  exact hGX ⟨h_init⟩

def exercise_6_3_2_a_coyoneda_iso {A : Type u} [Category.{v} A]
    (U : A ⥤ Type v) (F : Type v ⥤ A) (adj : F ⊣ U) :
    coyoneda.obj (op (F.obj PUnit.{v+1})) ≅ U :=
  NatIso.ofComponents (fun X => Equiv.toIso {
    toFun := fun g => (adj.homEquiv PUnit.{v+1} X g) PUnit.unit
    invFun := fun x => (adj.homEquiv PUnit.{v+1} X).symm (↾fun (_ : PUnit.{v+1}) => x)
    left_inv := fun g => by
      have h : (↾fun (_ : PUnit.{v+1}) => (adj.homEquiv PUnit.{v+1} X g) PUnit.unit) =
          adj.homEquiv PUnit.{v+1} X g := by
        ext ⟨⟩
        rfl
      change (adj.homEquiv PUnit.{v+1} X).symm
        (↾fun (_ : PUnit.{v+1}) => (adj.homEquiv PUnit.{v+1} X g) PUnit.unit) = g
      rw [h]
      exact (adj.homEquiv PUnit.{v+1} X).left_inv g
    right_inv := fun x => by
      have h : (adj.homEquiv PUnit.{v+1} X)
          ((adj.homEquiv PUnit.{v+1} X).symm (↾fun (_ : PUnit.{v+1}) => x)) =
          (↾fun (_ : PUnit.{v+1}) => x) :=
        (adj.homEquiv PUnit.{v+1} X).apply_symm_apply (↾fun (_ : PUnit.{v+1}) => x)
      exact congr_arg (fun k => (ConcreteCategory.hom k) PUnit.unit) h
  }) (fun {X Y} f => by
    ext g
    have hnat := adj.homEquiv_naturality_right g f
    exact congr_arg (fun k => (ConcreteCategory.hom k) PUnit.unit) hnat)

@[reducible]
noncomputable def exercise_6_3_2_a_preserves_limits_of_representable {A : Type u} [Category.{v} A]
    (X : A) : PreservesLimitsOfSize.{v, v} (coyoneda.obj (op X)) :=
  inferInstance

def preorder_to_antisymm (α : Type u) [Preorder α] : α ⥤ Antisymmetrization α (· ≤ ·) where
  obj x := Quotient.mk'' x
  map {x y} h := homOfLE h.le

instance preorder_to_antisymm_full (α : Type u) [Preorder α] :
    (preorder_to_antisymm α).Full where
  map_surjective f := ⟨homOfLE f.le, rfl⟩

instance preorder_to_antisymm_faithful (α : Type u) [Preorder α] :
    (preorder_to_antisymm α).Faithful where

instance preorder_to_antisymm_essSurj (α : Type u) [Preorder α] :
    (preorder_to_antisymm α).EssSurj where
  mem_essImage y := Quotient.inductionOn' y (fun a => ⟨a, ⟨Iso.refl _⟩⟩)

noncomputable instance preorder_to_antisymm_isEquivalence (α : Type u) [Preorder α] :
    (preorder_to_antisymm α).IsEquivalence where

noncomputable def exercise_6_3_3_a_preorder_equiv_poset (α : Type u) [Preorder α] :
    α ≌ Antisymmetrization α (· ≤ ·) :=
  (preorder_to_antisymm α).asEquivalence

theorem exercise_6_3_4_d_gaft {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [HasLimits D] (G : D ⥤ C) [PreservesLimitsOfSize.{v₂, v₂} G]
    (hG : SolutionSetCondition.{v₂} G) :
    G.IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_solutionSetCondition G hG

def exercise_6_3_5_exp_equiv {A : Type u} [SmallCategory A]
    [CartesianMonoidalCategory A] [MonoidalClosed A] (B C X : A) :
    (X ⟶ (ihom B).obj C) ≃ (B ⊗ X ⟶ C) :=
  ((ihom.adjunction B).homEquiv X C).symm

def exercise_6_3_5_yoneda_exp_equiv {A : Type u} [SmallCategory A]
    (B C X : A) :
    (yoneda.obj X ⟶ (ihom (yoneda.obj B)).obj (yoneda.obj C)) ≃
    (yoneda.obj B ⊗ yoneda.obj X ⟶ yoneda.obj C) :=
  ((ihom.adjunction (yoneda.obj B)).homEquiv (yoneda.obj X) (yoneda.obj C)).symm

noncomputable def exercise_6_3_6_a_subobject_pullback {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y : C} (f : X ⟶ Y) : Subobject Y ⥤ Subobject X :=
  Subobject.pullback f

noncomputable def exercise_6_3_6_b_subobject_presheaf (C : Type u) [Category.{v} C]
    [HasPullbacks C] : Cᵒᵖ ⥤ Type (max u v) :=
  Subobject.presheaf C

noncomputable def exercise_6_3_6_c_set_subobject_equiv (α : Type u) :
    Subobject α ≃o Set α :=
  Types.subobjectEquivSet α

theorem exercise_6_3_6_c_hasClassifier_iff_representable {C : Type u} [Category.{v} C]
    [HasTerminal C] [HasPullbacks C] :
    HasSubobjectClassifier C ↔ (Subobject.presheaf C).IsRepresentable :=
  hasSubobjectClassifier_iff_isRepresentable

theorem exercise_6_3_7_presheaf_subobject_classifier_iff (A : Type u) [Category.{v} A] :
    HasSubobjectClassifier (Aᵒᵖ ⥤ Type (max u v)) ↔
    (Subobject.presheaf (Aᵒᵖ ⥤ Type (max u v))).IsRepresentable :=
  hasSubobjectClassifier_iff_isRepresentable

end InteractionsBetweenAdjointFunctorsAndLimits
