-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.Combinatorics.Quiver.ReflQuiver

namespace Chapter3

open CategoryTheory
open CategoryTheory.Limits

universe u

abbrev setprop_set_category : Category (Type u) :=
  inferInstance

noncomputable def setprop_empty_initial : IsInitial (PEmpty : Type u) :=
  Types.isInitialPEmpty

noncomputable def setprop_one_terminal : IsTerminal (PUnit : Type u) :=
  Types.isTerminalPUnit

def set_iso_distributivity (A B C : Type u) : A × (B ⊕ C) ≃ (A × B) ⊕ (A × C) :=
  Equiv.prodSumDistrib A B C

def set_iso_exponential_sum (A B C : Type u) : (B ⊕ C → A) ≃ (B → A) × (C → A) :=
  Equiv.sumArrowEquivProdArrow B C A

def set_iso_exponential_product (A B C : Type u) : (C → B → A) ≃ (B × C → A) :=
  ((Equiv.curry C B A).symm).trans (Equiv.arrowCongr (Equiv.prodComm C B) (Equiv.refl A))

noncomputable def characteristicFunction {A : Type u} (S : Set A) : A → Bool := by
  classical
  exact fun a => if a ∈ S then true else false

def subsetOfFunction {A : Type u} (f : A → Bool) : Set A :=
  {a | f a = true}

noncomputable def setprop_subsets_characteristic (A : Type u) : Set A ≃ (A → Bool) where
  toFun := characteristicFunction
  invFun := subsetOfFunction
  left_inv := by
    intro S
    funext a
    by_cases h : a ∈ S <;> simp [characteristicFunction, subsetOfFunction]
  right_inv := by
    intro f
    funext a
    by_cases h : f a = true
    · simp [characteristicFunction, subsetOfFunction, h]
    · have hf : f a = false := (Bool.not_eq_true (f a)).mp h
      simp [characteristicFunction, subsetOfFunction, hf]

theorem quotient_projection_surjective {A : Type u} (r : A → A → Prop) :
    Function.Surjective (Quot.mk r) :=
  Quot.exists_rep

theorem quotient_mk_eq_iff {A : Type u} (s : Setoid A) (a a' : A) :
    Quotient.mk s a = Quotient.mk s a' ↔ s a a' :=
  Quotient.eq

noncomputable def quotient_lift_equiv {A B : Type u} (s : Setoid A) :
    {f : A → B // ∀ ⦃a a' : A⦄, s a a' → f a = f a'} ≃ (Quotient s → B) where
  toFun := fun f => Quot.lift f.1 f.2
  invFun := fun g => ⟨g ∘ Quotient.mk s, fun a a' h => congrArg g (Quotient.eq.mpr h)⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext a
    rfl
  right_inv := by
    intro g
    funext q
    induction q using Quot.ind with
    | mk a => rfl

theorem natural_numbers_recursion (X : Type u) (a : X) (r : X → X) :
    ∃! x : ℕ → X, x 0 = a ∧ x ∘ Nat.succ = r ∘ x := by
  refine ⟨Nat.rec a (fun _ y => r y), ⟨rfl, ?_⟩, ?_⟩
  · funext n
    rfl
  · intro x hx
    funext n
    induction n with
    | zero => exact hx.1
    | succ n ih =>
        have hx₂ : ∀ n : ℕ, x (Nat.succ n) = r (x n) := fun n => congrFun hx.2 n
        rw [hx₂ n, ih]

theorem setprop_choice {A B : Type u} (f : A → B) :
    Function.Surjective f ↔ Function.HasRightInverse f :=
  Function.surjective_iff_hasRightInverse

def exercise_3_1_1_diagonal : Type u ⥤ Type u × Type u :=
  Functor.diag (Type u)

def exercise_3_1_1_sum : (Type u × Type u) ⥤ Type u where
  obj := fun X => X.1 ⊕ X.2
  map := fun f => TypeCat.ofHom (Sum.map f.1 f.2)
  map_id := by
    intro X
    ext x
    cases x <;> rfl
  map_comp := by
    intro X Y Z f g
    ext x
    cases x <;> rfl

def exercise_3_1_1_prod : (Type u × Type u) ⥤ Type u where
  obj := fun X => X.1 × X.2
  map := fun f => TypeCat.ofHom (Prod.map f.1 f.2)
  map_id := by
    intro X
    ext x <;> rcases x with ⟨a, b⟩ <;> rfl
  map_comp := by
    intro X Y Z f g
    ext x <;> rcases x with ⟨a, b⟩ <;> rfl

def exercise_3_1_1_left_adj : exercise_3_1_1_sum ⊣ exercise_3_1_1_diagonal :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := fun X => (TypeCat.ofHom Sum.inl, TypeCat.ofHom Sum.inr)
          naturality := by
            intro X Y f
            ext a <;> simp [exercise_3_1_1_diagonal, Functor.diag, exercise_3_1_1_sum] }
      counit :=
        { app := fun X => TypeCat.ofHom (Sum.elim id id)
          naturality := by
            intro X Y g
            ext x
            cases x <;> rfl }
      left_triangle := by
        ext X x
        simp [exercise_3_1_1_diagonal, Functor.diag, exercise_3_1_1_sum]
        cases x <;> rfl
      right_triangle := by
        ext X x <;> dsimp [Functor.whiskerLeft, Functor.whiskerRight, Functor.associator] <;>
          simp [exercise_3_1_1_diagonal, Functor.diag, exercise_3_1_1_sum] <;> rfl }

def exercise_3_1_1_right_adj : exercise_3_1_1_diagonal ⊣ exercise_3_1_1_prod :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := fun X => TypeCat.ofHom (fun x : X => (x, x))
          naturality := by
            intro X Y f
            ext x
            dsimp [exercise_3_1_1_diagonal, Functor.diag, exercise_3_1_1_prod] }
      counit :=
        { app := fun X => (TypeCat.ofHom Prod.fst, TypeCat.ofHom Prod.snd)
          naturality := by
            intro X Y f
            ext a <;> rcases a with ⟨u, v⟩ <;>
              dsimp [exercise_3_1_1_diagonal, Functor.diag, exercise_3_1_1_prod] }
      left_triangle := by
        ext X x <;> dsimp [Functor.whiskerRight, Functor.whiskerLeft, Functor.associator] <;>
          simp [exercise_3_1_1_diagonal, Functor.diag, exercise_3_1_1_prod] <;> rfl
      right_triangle := by
        ext X x
        dsimp [Functor.whiskerLeft, Functor.whiskerRight, Functor.associator]
        simp [exercise_3_1_1_diagonal, Functor.diag, exercise_3_1_1_prod]
        rfl }

structure NatNumberObject : Type (u + 1) where
  carrier : Type u
  point : carrier
  step : carrier → carrier

instance : Category NatNumberObject where
  Hom X Y := {f : X.carrier → Y.carrier // f X.point = Y.point ∧ ∀ x, f (X.step x) = Y.step (f x)}
  id X := ⟨fun x => x, rfl, fun x => rfl⟩
  comp f g := ⟨g.1 ∘ f.1, (congrArg g.1 f.2.1).trans g.2.1, by
    intro x
    exact (congrArg g.1 (f.2.2 x)).trans (g.2.2 (f.1 x))⟩
  id_comp := by
    intro X Y f
    apply Subtype.ext
    funext x
    rfl
  comp_id := by
    intro X Y f
    apply Subtype.ext
    funext x
    rfl
  assoc := by
    intro X Y Z W f g h
    apply Subtype.ext
    funext x
    rfl

def naturalNumberObjectHom (Y : NatNumberObject) : (⟨ℕ, 0, Nat.succ⟩ : NatNumberObject) ⟶ Y :=
  ⟨Nat.rec Y.point (fun _ x => Y.step x), rfl, fun _ => rfl⟩

def exercise_3_1_2 : IsInitial (⟨ℕ, 0, Nat.succ⟩ : NatNumberObject) := by
  refine IsColimit.mk (t := asEmptyCocone (⟨ℕ, 0, Nat.succ⟩ : NatNumberObject))
    (fun s => naturalNumberObjectHom s.pt) ?_ ?_
  · intro s j
    cases j with
    | mk as => cases as
  · intro s m _
    apply Subtype.ext
    funext n
    induction n with
    | zero => exact m.2.1
    | succ n ih =>
        change m.1 (Nat.succ n) = Nat.rec s.pt.point (fun _ x => s.pt.step x) (Nat.succ n)
        have hm : m.1 (Nat.succ n) = s.pt.step (m.1 n) := m.2.2 n
        rw [hm, ih]
        rfl

end Chapter3
