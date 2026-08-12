-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib

namespace Functors

universe u v

open CategoryTheory

abbrev example_1_2_3a : GrpCat.{u} ⥤ Type u := forget GrpCat

abbrev example_1_2_3b_ring : RingCat.{u} ⥤ Type u := forget RingCat

abbrev example_1_2_3b_vect (k : Type u) [Field k] : ModuleCat.{u} k ⥤ Type u :=
  forget (ModuleCat k)

abbrev example_1_2_3c : RingCat.{u} ⥤ AddCommGrpCat.{u} := forget₂ RingCat AddCommGrpCat

noncomputable abbrev example_1_2_4a : Type u ⥤ GrpCat.{u} := GrpCat.free

noncomputable abbrev example_1_2_4b : Type u ⥤ CommRingCat.{u} := CommRingCat.free

noncomputable abbrev example_1_2_4c (k : Type u) [Ring k] : Type u ⥤ ModuleCat.{u} k :=
  ModuleCat.free k

abbrev defn_1_2_10 (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] := Cᵒᵖ ⥤ D

abbrev defn_1_2_15 (A : Type u) [Category.{v} A] := Aᵒᵖ ⥤ Type u

def exercise_1_2_20 {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) {A A' : C}
    (h : A ≅ A') : F.obj A ≅ F.obj A' :=
  F.mapIso h

theorem exercise_1_2_21_obj_map {A B : Type u} [Preorder A] [Preorder B] (F : A ⥤ B) :
    ∀ a a' : A, a ≤ a' → F.obj a ≤ F.obj a' := by
  intro a a' h
  have hhom : a ⟶ a' := homOfLE h
  have hmap : F.obj a ⟶ F.obj a' := F.map hhom
  exact leOfHom hmap

def exercise_1_2_21_map_obj {A B : Type u} [Preorder A] [Preorder B] (f : A → B)
    (hf : ∀ a a', a ≤ a' → f a ≤ f a') : A ⥤ B where
  obj := f
  map {a a'} h := homOfLE (hf a a' (leOfHom h))
  map_id _ := rfl
  map_comp {_ _ _} _ _ := rfl

def exercise_1_2_24a_FA {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A × B ⥤ C) (a : A) : B ⥤ C where
  obj b := F.obj (a, b)
  map {b b'} g := F.map (Prod.mkHom (𝟙 a) g)
  map_id b := F.map_id (a, b)
  map_comp {b b' b''} g h := by
    simpa using (F.map_comp (Prod.mkHom (𝟙 a) g) (Prod.mkHom (𝟙 a) h)).symm

def exercise_1_2_24a_F_B {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A × B ⥤ C) (b : B) : A ⥤ C where
  obj a := F.obj (a, b)
  map {a a'} f := F.map (Prod.mkHom f (𝟙 b))
  map_id a := F.map_id (a, b)
  map_comp {a a' a''} f f' := by
    simpa using (F.map_comp (Prod.mkHom f (𝟙 b)) (Prod.mkHom f' (𝟙 b))).symm

theorem exercise_1_2_24b_i {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A × B ⥤ C) (a : A) (b : B) :
    (exercise_1_2_24a_FA F a).obj b = (exercise_1_2_24a_F_B F b).obj a := rfl

theorem exercise_1_2_24b_ii {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A × B ⥤ C) {a a' : A} {b b' : B} (f : a ⟶ a') (g : b ⟶ b') :
    (exercise_1_2_24a_F_B F b).map f ≫ (exercise_1_2_24a_FA F a').map g =
    (exercise_1_2_24a_FA F a).map g ≫ (exercise_1_2_24a_F_B F b').map f := by
  dsimp [exercise_1_2_24a_FA, exercise_1_2_24a_F_B]
  rw [← F.map_comp, ← F.map_comp]
  simp

noncomputable def exercise_1_2_25 : TopCatᵒᵖ ⥤ RingCat where
  obj X := RingCat.of (C(X.unop, ℝ))
  map {X Y} f :=
    RingCat.ofHom
      { toFun := fun (g : C(X.unop, ℝ)) => g.comp f.unop.hom
        map_one' := by ext x; rfl
        map_mul' := fun g h => by ext x; rfl
        map_zero' := by ext x; rfl
        map_add' := fun g h => by ext x; rfl }
  map_id X := by
    ext g x; rfl
  map_comp {X Y Z} f g := by
    ext h x; rfl

inductive exercise_1_2_26_A : Type
  | a | b
  deriving DecidableEq

instance : Category exercise_1_2_26_A where
  Hom X Y := ULift (PLift (X = Y))
  id X := ULift.up (PLift.up rfl)
  comp {X Y Z} f g := ULift.up (PLift.up (by
    rcases f with ⟨⟨rfl⟩⟩
    rcases g with ⟨⟨rfl⟩⟩
    rfl))

instance {X Y : exercise_1_2_26_A} : Subsingleton (X ⟶ Y) where
  allEq f g := by
    apply ULift.ext f g
    apply Subsingleton.elim

def exercise_1_2_26_F : exercise_1_2_26_A ⥤ PUnit where
  obj _ := PUnit.unit
  map {_ _} _ := 𝟙 PUnit.unit
  map_id _ := rfl
  map_comp {_ _ _} _ _ := by simp

theorem exercise_1_2_26_faithful : Functor.Faithful exercise_1_2_26_F := by
  refine ⟨fun {X Y} f g _ => Subsingleton.elim f g⟩

theorem exercise_1_2_26 : exercise_1_2_26_A.a ≠ exercise_1_2_26_A.b ∧
    exercise_1_2_26_F.map (𝟙 exercise_1_2_26_A.a) =
    exercise_1_2_26_F.map (𝟙 exercise_1_2_26_A.b) := by
  constructor
  · exact exercise_1_2_26_A.noConfusion
  · rfl

end Functors

#min_imports
