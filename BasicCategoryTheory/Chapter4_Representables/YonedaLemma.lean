-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.Functors
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Yoneda

namespace Representables

universe u v u' v'

open CategoryTheory Opposite

abbrev def_4_2_presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type v

abbrev def_4_2_yoneda_obj {C : Type u} [Category.{v} C] (A : C) : Cᵒᵖ ⥤ Type v :=
  yoneda.obj A

abbrev def_4_2_maps {C : Type u} [Category.{v} C] (A : C) (X : Cᵒᵖ ⥤ Type v) : Type (max u v) :=
  yoneda.obj A ⟶ X

def theorem_4_2_1_yel {C : Type u} [Category.{v} C] {A : C} {X : Cᵒᵖ ⥤ Type v}
    (α : yoneda.obj A ⟶ X) : X.obj (op A) :=
  α.app (op A) (𝟙 A)

def theorem_4_2_1_ynt {C : Type u} [Category.{v} C] {A : C} {X : Cᵒᵖ ⥤ Type v}
    (x : X.obj (op A)) : yoneda.obj A ⟶ X where
  app B := ↾fun f => X.map f.op x
  naturality B B' g := by
    ext f
    dsimp
    have h := CategoryTheory.Functor.map_comp X f.op g
    change (X.map (f.op ≫ g)) x = (X.map g) ((X.map f.op) x)
    rw [h]
    rfl

theorem theorem_4_2_1_yel_ynt {C : Type u} [Category.{v} C] {A : C} {X : Cᵒᵖ ⥤ Type v}
    (x : X.obj (op A)) :
    theorem_4_2_1_yel (theorem_4_2_1_ynt x) = x := by
  dsimp [theorem_4_2_1_yel, theorem_4_2_1_ynt]
  have h := CategoryTheory.Functor.map_id X (op A)
  change (X.map (𝟙 (op A))) x = x
  rw [h]
  rfl

lemma theorem_4_2_1_recovery {C : Type u} [Category.{v} C] {A B : C} {X : Cᵒᵖ ⥤ Type v}
    (α : yoneda.obj A ⟶ X) (f : B ⟶ A) :
    X.map f.op (α.app (op A) (𝟙 A)) = α.app (op B) f := by
  have h := α.naturality_apply f.op (𝟙 A)
  dsimp at h
  rw [Category.comp_id] at h
  exact h.symm

theorem theorem_4_2_1_ynt_yel {C : Type u} [Category.{v} C] {A : C} {X : Cᵒᵖ ⥤ Type v}
    (α : yoneda.obj A ⟶ X) :
    theorem_4_2_1_ynt (theorem_4_2_1_yel α) = α := by
  ext ⟨B⟩ f
  dsimp [theorem_4_2_1_ynt, theorem_4_2_1_yel]
  exact theorem_4_2_1_recovery α f

def theorem_4_2_1_equiv {C : Type u} [Category.{v} C] (A : C) (X : Cᵒᵖ ⥤ Type v) :
    (yoneda.obj A ⟶ X) ≃ X.obj (op A) where
  toFun := theorem_4_2_1_yel
  invFun := theorem_4_2_1_ynt
  left_inv := theorem_4_2_1_ynt_yel
  right_inv := theorem_4_2_1_yel_ynt

def theorem_4_2_1_iso {C : Type u} [Category.{u} C] (A : C) (X : Cᵒᵖ ⥤ Type u) :
    (yoneda.obj A ⟶ X) ≅ X.obj (op A) :=
  Equiv.toIso (theorem_4_2_1_equiv A X)

theorem theorem_4_2_1_naturality_A {C : Type u} [Category.{v} C] {A B : C} (f : B ⟶ A)
    (X : Cᵒᵖ ⥤ Type v) (α : yoneda.obj A ⟶ X) :
    theorem_4_2_1_yel (yoneda.map f ≫ α) = X.map f.op (theorem_4_2_1_yel α) := by
  dsimp [theorem_4_2_1_yel]
  rw [Category.id_comp]
  exact (theorem_4_2_1_recovery α f).symm

theorem theorem_4_2_1_naturality_X {C : Type u} [Category.{v} C] (A : C) {X X' : Cᵒᵖ ⥤ Type v}
    (θ : X ⟶ X') (α : yoneda.obj A ⟶ X) :
    theorem_4_2_1_yel (α ≫ θ) = θ.app (op A) (theorem_4_2_1_yel α) := by
  rfl

def theorem_4_2_1_functor_hom (C : Type u) [Category.{v} C] :
    Cᵒᵖ × (Cᵒᵖ ⥤ Type v) ⥤ Type (max u v) :=
  yonedaPairing C

def theorem_4_2_1_functor_eval (C : Type u) [Category.{v} C] :
    Cᵒᵖ × (Cᵒᵖ ⥤ Type v) ⥤ Type (max u v) :=
  yonedaEvaluation C

def theorem_4_2_1 (C : Type u) [Category.{v} C] :
    theorem_4_2_1_functor_hom C ≅ theorem_4_2_1_functor_eval C :=
  yonedaLemma C

def exercise_4_2_1_yel {C : Type u} [Category.{v} C] {A : C} {X : C ⥤ Type v}
    (α : coyoneda.obj (op A) ⟶ X) : X.obj A :=
  α.app A (𝟙 A)

def exercise_4_2_1_ynt {C : Type u} [Category.{v} C] {A : C} {X : C ⥤ Type v}
    (x : X.obj A) : coyoneda.obj (op A) ⟶ X where
  app B := ↾fun f => X.map f x
  naturality B B' g := by
    ext f
    dsimp
    have h := CategoryTheory.Functor.map_comp X f g
    change (X.map (f ≫ g)) x = (X.map g) ((X.map f) x)
    rw [h]
    rfl

theorem exercise_4_2_1_yel_ynt {C : Type u} [Category.{v} C] {A : C} {X : C ⥤ Type v}
    (x : X.obj A) :
    exercise_4_2_1_yel (exercise_4_2_1_ynt x) = x := by
  dsimp [exercise_4_2_1_yel, exercise_4_2_1_ynt]
  have h := CategoryTheory.Functor.map_id X A
  change (X.map (𝟙 A)) x = x
  rw [h]
  rfl

lemma exercise_4_2_1_recovery {C : Type u} [Category.{v} C] {A B : C} {X : C ⥤ Type v}
    (α : coyoneda.obj (op A) ⟶ X) (f : A ⟶ B) :
    X.map f (α.app A (𝟙 A)) = α.app B f := by
  have h := α.naturality_apply f (𝟙 A)
  dsimp at h
  rw [Category.id_comp] at h
  exact h.symm

theorem exercise_4_2_1_ynt_yel {C : Type u} [Category.{v} C] {A : C} {X : C ⥤ Type v}
    (α : coyoneda.obj (op A) ⟶ X) :
    exercise_4_2_1_ynt (exercise_4_2_1_yel α) = α := by
  ext B f
  dsimp [exercise_4_2_1_ynt, exercise_4_2_1_yel]
  exact exercise_4_2_1_recovery α f

def exercise_4_2_1_equiv {C : Type u} [Category.{v} C] (A : C) (X : C ⥤ Type v) :
    (coyoneda.obj (op A) ⟶ X) ≃ X.obj A where
  toFun := exercise_4_2_1_yel
  invFun := exercise_4_2_1_ynt
  left_inv := exercise_4_2_1_ynt_yel
  right_inv := exercise_4_2_1_yel_ynt

def exercise_4_2_1_iso {C : Type u} [Category.{u} C] (A : C) (X : C ⥤ Type u) :
    (coyoneda.obj (op A) ⟶ X) ≅ X.obj A :=
  Equiv.toIso (exercise_4_2_1_equiv A X)

theorem exercise_4_2_1_naturality_A {C : Type u} [Category.{v} C] {A B : C} (f : A ⟶ B)
    (X : C ⥤ Type v) (α : coyoneda.obj (op A) ⟶ X) :
    exercise_4_2_1_yel (coyoneda.map f.op ≫ α) = X.map f (exercise_4_2_1_yel α) := by
  dsimp [exercise_4_2_1_yel]
  rw [Category.comp_id]
  exact (exercise_4_2_1_recovery α f).symm

theorem exercise_4_2_1_naturality_X {C : Type u} [Category.{v} C] (A : C) {X X' : C ⥤ Type v}
    (θ : X ⟶ X') (α : coyoneda.obj (op A) ⟶ X) :
    exercise_4_2_1_yel (α ≫ θ) = θ.app A (exercise_4_2_1_yel α) := by
  rfl

def exercise_4_2_1_functor_hom (C : Type u) [Category.{v} C] :
    C × (C ⥤ Type v) ⥤ Type (max u v) :=
  coyonedaPairing C

def exercise_4_2_1_functor_eval (C : Type u) [Category.{v} C] :
    C × (C ⥤ Type v) ⥤ Type (max u v) :=
  coyonedaEvaluation C

def exercise_4_2_1 (C : Type u) [Category.{v} C] :
    exercise_4_2_1_functor_hom C ≅ exercise_4_2_1_functor_eval C :=
  coyonedaLemma C

def exercise_4_2_2_rreg (M : Type u) [Monoid M] : Action (Type u) Mᵐᵒᵖ where
  V := M
  ρ := {
    toFun := fun m => ↾fun (x : M) => x * m.unop
    map_one' := by
      apply End.ext
      ext x
      simp
    map_mul' := fun m n => by
      apply End.ext
      ext x
      dsimp
      exact (mul_assoc x n.unop m.unop).symm
  }

def exercise_4_2_2_a (M : Type u) [Monoid M] :
    (Functors.example_1_2_14 M).functor.obj (yoneda.obj (SingleObj.star M)) ≅
      exercise_4_2_2_rreg M := by
  refine Action.mkIso (Iso.refl _) ?_
  intro m
  apply End.ext
  ext x
  rfl

def exercise_4_2_2_b_hom (M : Type u) [Monoid M] (X : Action (Type u) Mᵐᵒᵖ) (x : X.V) :
    exercise_4_2_2_rreg M ⟶ X where
  hom := ↾fun (m : M) => (X.ρ (MulOpposite.op m)).asHom x
  comm m := by
    ext (a : M)
    change (X.ρ (MulOpposite.op (a * m.unop))).asHom x =
      (X.ρ m).asHom ((X.ρ (MulOpposite.op a)).asHom x)
    have hop : MulOpposite.op (a * m.unop) = m * MulOpposite.op a := rfl
    rw [hop, X.ρ.map_mul]
    rfl

theorem exercise_4_2_2_b_eval (M : Type u) [Monoid M] (X : Action (Type u) Mᵐᵒᵖ)
    (α : exercise_4_2_2_rreg M ⟶ X) (m : M) :
    α.hom m = (X.ρ (MulOpposite.op m)).asHom (α.hom (1 : M)) := by
  have hc := α.comm (MulOpposite.op m)
  have hc_app := congr_fun (congr_arg (fun f : M ⟶ X.V => (f : M → X.V)) hc) (1 : M)
  have h1 : (ConcreteCategory.hom ((exercise_4_2_2_rreg M).ρ (MulOpposite.op m))) (1 : M) = m := by
    change (1 : M) * (MulOpposite.op m).unop = m
    rw [MulOpposite.unop_op, one_mul]
  have hc2 : (ConcreteCategory.hom ((exercise_4_2_2_rreg M).ρ (MulOpposite.op m) ≫ α.hom))
      (1 : M) = α.hom m := by
    change α.hom ((ConcreteCategory.hom ((exercise_4_2_2_rreg M).ρ (MulOpposite.op m)))
      (1 : M)) = α.hom m
    rw [h1]
  rw [← hc2]
  exact hc_app

theorem exercise_4_2_2_b_unique (M : Type u) [Monoid M] (X : Action (Type u) Mᵐᵒᵖ) (x : X.V) :
    ∃! α : exercise_4_2_2_rreg M ⟶ X, α.hom (1 : M) = x := by
  use exercise_4_2_2_b_hom M X x
  dsimp
  refine ⟨by
    change (X.ρ (MulOpposite.op (1 : M))).asHom x = x
    rw [MulOpposite.op_one, X.ρ.map_one]
    rfl, ?_⟩
  intro α hα
  ext (m : M)
  have h := exercise_4_2_2_b_eval M X α m
  rw [hα] at h
  exact h

def exercise_4_2_2_b (M : Type u) [Monoid M] (X : Action (Type u) Mᵐᵒᵖ) :
    (exercise_4_2_2_rreg M ⟶ X) ≃ X.V where
  toFun α := α.hom (1 : M)
  invFun x := exercise_4_2_2_b_hom M X x
  left_inv α := by
    ext (m : M)
    dsimp [exercise_4_2_2_b_hom]
    rw [← exercise_4_2_2_b_eval M X α m]
  right_inv x := by
    dsimp [exercise_4_2_2_b_hom]
    change (X.ρ (MulOpposite.op (1 : M))).asHom x = x
    rw [MulOpposite.op_one, X.ρ.map_one]
    rfl

def exercise_4_2_2_c (M : Type u) [Monoid M] (X : (SingleObj M)ᵒᵖ ⥤ Type u) :
    (yoneda.obj (SingleObj.star M) ⟶ X) ≃ X.obj (op (SingleObj.star M)) :=
  let E := Functors.example_1_2_14 M
  let e1 : (yoneda.obj (SingleObj.star M) ⟶ X) ≃
      (E.functor.obj (yoneda.obj (SingleObj.star M)) ⟶ E.functor.obj X) :=
    E.fullyFaithfulFunctor.homEquiv
  let e2 : (E.functor.obj (yoneda.obj (SingleObj.star M)) ⟶ E.functor.obj X) ≃
      (exercise_4_2_2_rreg M ⟶ E.functor.obj X) :=
    (Iso.homFromEquiv (exercise_4_2_2_a M)).symm
  let e3 : (exercise_4_2_2_rreg M ⟶ E.functor.obj X) ≃ (E.functor.obj X).V :=
    exercise_4_2_2_b M (E.functor.obj X)
  e1.trans (e2.trans e3)

theorem exercise_4_2_2_c_apply (M : Type u) [Monoid M] (X : (SingleObj M)ᵒᵖ ⥤ Type u)
    (α : yoneda.obj (SingleObj.star M) ⟶ X) :
    exercise_4_2_2_c M X α = α.app (op (SingleObj.star M)) (𝟙 (SingleObj.star M)) := by
  rfl

end Representables
