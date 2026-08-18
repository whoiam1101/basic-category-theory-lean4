-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Category.TopCat.Adjunctions
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Representables

universe u v u' v'

open CategoryTheory Opposite

abbrev def_4_1_1 {C : Type u} [Category.{v} C] (A : C) : C ⥤ Type v :=
  coyoneda.obj (op A)

def def_4_1_3_is_representable {C : Type u} [Category.{v} C] (X : C ⥤ Type v) : Prop :=
  ∃ A : C, Nonempty (coyoneda.obj (op A) ≅ X)

def def_4_1_3_representation {C : Type u} [Category.{v} C] (X : C ⥤ Type v) (A : C) :=
  coyoneda.obj (op A) ≅ X

def example_4_1_4 : coyoneda.obj (op PUnit) ≅ 𝟭 (Type u) :=
  Coyoneda.punitIso

def lemma_4_1_10 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : C) :
    coyoneda.obj (op (F.obj A)) ≅ G ⋙ coyoneda.obj (op A) :=
  NatIso.ofComponents
    (fun B => (adj.homEquiv A B).toIso)
    (fun {B B'} g => by
      ext f
      dsimp [coyoneda]
      exact adj.homEquiv_naturality_right f g)

def proposition_4_1_11 {C : Type u} [Category.{v} C]
    {F : Type v ⥤ C} {G : C ⥤ Type v} (adj : F ⊣ G) :
    coyoneda.obj (op (F.obj PUnit)) ≅ G :=
  (lemma_4_1_10 adj PUnit).trans
    (Functor.isoWhiskerLeft G Coyoneda.punitIso)

theorem proposition_4_1_11_is_representable {C : Type u} [Category.{v} C]
    {F : Type v ⥤ C} {G : C ⥤ Type v} (adj : F ⊣ G) :
    def_4_1_3_is_representable G :=
  ⟨F.obj PUnit, ⟨proposition_4_1_11 adj⟩⟩

def example_4_1_5_top : coyoneda.obj (op (TopCat.discrete.obj PUnit)) ≅ forget TopCat :=
  proposition_4_1_11 TopCat.adj₁

def example_4_1_5_grp : coyoneda.obj (op (GrpCat.free.obj PUnit)) ≅ forget GrpCat :=
  proposition_4_1_11 GrpCat.adj

def example_4_1_6 : coyoneda.obj (op (Cat.of (Discrete PUnit))) ≅ Cat.objects.{u, u} :=
  NatIso.ofComponents
    (fun C =>
      Equiv.toIso
      { toFun := fun F => F.toFunctor.obj (Discrete.mk PUnit.unit)
        invFun := fun X => Functor.toCatHom (Functor.fromPUnit X)
        left_inv := fun F => by
          apply Cat.ext
          fapply CategoryTheory.Functor.ext
          · intro ⟨⟨⟩⟩
            rfl
          · intro ⟨⟨⟩⟩ ⟨⟨⟩⟩ f
            rcases f with ⟨⟨⟨⟩⟩⟩
            change 𝟙 _ = 𝟙 _ ≫ F.toFunctor.map (𝟙 (Discrete.mk PUnit.unit)) ≫ 𝟙 _
            letI : Category C := C.str
            have h1 : (𝟙 (F.toFunctor.obj (Discrete.mk PUnit.unit)) ≫
                F.toFunctor.map (𝟙 (Discrete.mk PUnit.unit)) ≫
                𝟙 (F.toFunctor.obj (Discrete.mk PUnit.unit))) =
                F.toFunctor.map (𝟙 (Discrete.mk PUnit.unit)) := by
              rw [Category.comp_id, Category.id_comp]
            rw [h1]
            exact (F.toFunctor.map_id (Discrete.mk PUnit.unit)).symm
        right_inv := fun X => rfl })
    (fun {C D} G => by
      ext F
      rfl)

def example_4_1_7 (M : Type u) [Monoid M] : SingleObj M ⥤ Type u :=
  coyoneda.obj (op (SingleObj.star M))

def example_4_1_9_equiv (k : Type u) [CommRing k] (U V W : Type u)
    [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] :
    (TensorProduct k U V →ₗ[k] W) ≃ₗ[k] (U →ₗ[k] V →ₗ[k] W) :=
  (TensorProduct.lift.equiv (RingHom.id k) U V W).symm

def example_4_1_12_top : coyoneda.obj (op (TopCat.discrete.obj PUnit)) ≅ forget TopCat :=
  proposition_4_1_11 TopCat.adj₁

noncomputable def example_4_1_13 (k : Type u) [Field k] :
    coyoneda.obj (op ((ModuleCat.free k).obj PUnit)) ≅ forget (ModuleCat.{u} k) :=
  proposition_4_1_11 (ModuleCat.adj k)

noncomputable def example_4_1_14 :
    coyoneda.obj (op (CommRingCat.of (Polynomial ℤ))) ≅ forget CommRingCat.{0} :=
  NatIso.ofComponents
    (fun R =>
      Equiv.toIso
      { toFun := fun f => f.hom Polynomial.X
        invFun := fun r => CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom R) r)
        left_inv := fun f => by
          apply CommRingCat.hom_ext
          apply Polynomial.ringHom_ext
          · intro a
            dsimp
            rw [Polynomial.eval₂_C]
            have : f.hom.comp Polynomial.C = Int.castRingHom R := Subsingleton.elim _ _
            exact congr_fun (congr_arg DFunLike.coe this.symm) a
          · dsimp
            exact Polynomial.eval₂_X _ _
        right_inv := fun r => by
          dsimp
          exact Polynomial.eval₂_X _ _ })
    (fun {R S} g => by
      ext f
      rfl)

abbrev def_4_1_15 (C : Type u) [Category.{v} C] : Cᵒᵖ ⥤ C ⥤ Type v :=
  coyoneda

abbrev def_4_1_16 {C : Type u} [Category.{v} C] (A : C) : Cᵒᵖ ⥤ Type v :=
  yoneda.obj A

def def_4_1_17_is_representable {C : Type u} [Category.{v} C] (X : Cᵒᵖ ⥤ Type v) : Prop :=
  ∃ A : C, Nonempty (yoneda.obj A ≅ X)

def def_4_1_17_representation {C : Type u} [Category.{v} C] (X : Cᵒᵖ ⥤ Type v) (A : C) :=
  yoneda.obj A ≅ X

def example_4_1_18_functor : Typeᵒᵖ ⥤ Type where
  obj X := Set (unop X)
  map f := ↾fun (s : Set _) => f.unop ⁻¹' s

def example_4_1_18 : yoneda.obj Prop ≅ example_4_1_18_functor :=
  NatIso.ofComponents
    (fun X => Equiv.toIso
      { toFun := fun f => (fun x => f.hom x : Set (unop X))
        invFun := fun s => ↾fun x => (s : Set (unop X)) x
        left_inv := fun f => rfl
        right_inv := fun s => rfl })
    (fun {X Y} f => by
      ext s
      rfl)

def example_4_1_19_opens_functor : TopCatᵒᵖ ⥤ Type where
  obj X := {s : Set X.unop // IsOpen s}
  map {X Y} f := ↾fun (U : {s : Set X.unop // IsOpen s}) =>
    ⟨f.unop.hom ⁻¹' U.1, U.2.preimage f.unop.hom.continuous⟩

def example_4_1_19 : yoneda.obj (TopCat.of Prop) ≅ example_4_1_19_opens_functor :=
  NatIso.ofComponents
    (fun X => Equiv.toIso
      { toFun := fun f => ⟨{x | f.hom x}, continuous_Prop.mp f.hom.continuous⟩
        invFun := fun U => TopCat.ofHom ⟨(· ∈ U.1), isOpen_iff_continuous_mem.mp U.2⟩
        left_inv := fun f => by
          apply TopCat.hom_ext
          ext x
          rfl
        right_inv := fun U => by
          apply Subtype.ext
          ext x
          rfl })
    (fun {X Y} f => by
      ext U
      apply Subtype.ext
      ext x
      rfl)

def example_4_1_20_functor : TopCatᵒᵖ ⥤ Type where
  obj X := ContinuousMap X.unop (TopCat.of ℝ)
  map {X Y} f := ↾fun g => g.comp f.unop.hom

def example_4_1_20 : yoneda.obj (TopCat.of ℝ) ≅ example_4_1_20_functor :=
  NatIso.ofComponents
    (fun X => Equiv.toIso
      { toFun := fun f => f.hom
        invFun := fun g => TopCat.ofHom g
        left_inv := fun f => by
          apply TopCat.hom_ext
          rfl
        right_inv := fun g => rfl })
    (fun {X Y} f => by
      ext g
      rfl)

abbrev def_4_1_21 (C : Type u) [Category.{v} C] : C ⥤ Cᵒᵖ ⥤ Type v :=
  yoneda

abbrev def_4_1_22 (C : Type u) [Category.{v} C] : Cᵒᵖ × C ⥤ Type v :=
  Functor.hom C

abbrev def_4_1_24 {C : Type u} [Category.{v} C] (S A : C) := S ⟶ A

def exercise_4_1_2 {C : Type u} [Category.{v} C] {A A' : C} (e : yoneda.obj A ≅ yoneda.obj A') :
    A ≅ A' :=
  Yoneda.fullyFaithful.preimageIso e

def exercise_4_1_3_equiv (n : ℕ) (G : AddGrpCat) :
    (AddGrpCat.of (ZMod n) ⟶ G) ≃ {g : G // n • g = 0} where
  toFun f := ⟨f.hom 1, by
    have : n • (f.hom 1) = f.hom (n • (1 : ZMod n)) := (map_nsmul f.hom n 1).symm
    rw [this, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero]⟩
  invFun := fun ⟨g, hg⟩ => AddGrpCat.ofHom
    (ZMod.lift n ⟨zmultiplesHom G g, by
      rw [zmultiplesHom_apply, natCast_zsmul]
      exact hg⟩)
  left_inv := fun f => by
    apply AddGrpCat.hom_ext
    ext x
    rcases ZMod.intCast_surjective x with ⟨a, rfl⟩
    dsimp
    rw [ZMod.lift_coe, zmultiplesHom_apply]
    have : ((a : ℤ) : ZMod n) = a • (1 : ZMod n) := by
      simp only [zsmul_eq_mul, mul_one]
    rw [this, map_zsmul]
  right_inv := fun ⟨g, hg⟩ => by
    ext
    dsimp
    have : (1 : ZMod n) = ((1 : ℤ) : ZMod n) := by simp
    rw [this, ZMod.lift_coe, zmultiplesHom_apply, one_zsmul]

def exercise_4_1_3_functor (n : ℕ) : AddGrpCat ⥤ Type where
  obj G := {g : G // n • g = 0}
  map f := ↾fun ⟨g, hg⟩ => ⟨f.hom g, by rw [← map_nsmul, hg, map_zero]⟩

def exercise_4_1_3 (n : ℕ) :
    coyoneda.obj (op (AddGrpCat.of (ZMod n))) ≅ exercise_4_1_3_functor n :=
  NatIso.ofComponents
    (fun G => Equiv.toIso (exercise_4_1_3_equiv n G))
    (fun {G H} f => by
      ext g
      rfl)

noncomputable abbrev exercise_4_1_4 := example_4_1_14

abbrev exercise_4_1_5 := example_4_1_19

inductive WalkingArrow : Type
  | zero
  | one

inductive WalkingArrowHom : WalkingArrow → WalkingArrow → Type
  | id (X : WalkingArrow) : WalkingArrowHom X X
  | arr : WalkingArrowHom .zero .one

instance : Category WalkingArrow where
  Hom := WalkingArrowHom
  id := WalkingArrowHom.id
  comp := fun {X Y Z} f g => match f, g with
    | .id _, g => g
    | .arr, .id _ => .arr
  id_comp := by
    intro X Y f
    match X, Y, f with
    | .zero, .zero, .id .zero => rfl
    | .one, .one, .id .one => rfl
    | .zero, .one, .arr => rfl
  comp_id := by
    intro X Y f
    match X, Y, f with
    | .zero, .zero, .id .zero => rfl
    | .one, .one, .id .one => rfl
    | .zero, .one, .arr => rfl
  assoc := by
    intro W X Y Z f g h
    match W, X, Y, Z, f, g, h with
    | .zero, .zero, .zero, .zero, .id .zero, .id .zero, .id .zero => rfl
    | .zero, .zero, .zero, .one, .id .zero, .id .zero, .arr => rfl
    | .zero, .zero, .one, .one, .id .zero, .arr, .id .one => rfl
    | .zero, .one, .one, .one, .arr, .id .one, .id .one => rfl
    | .one, .one, .one, .one, .id .one, .id .one, .id .one => rfl

def exercise_4_1_6_functor : Cat.{0, 0} ⥤ Type where
  obj C := Σ (X Y : C), (X ⟶ Y)
  map {C D} F := ↾fun ⟨X, Y, f⟩ =>
    ⟨F.toFunctor.obj X, F.toFunctor.obj Y, F.toFunctor.map f⟩

def exercise_4_1_6_equiv (C : Cat.{0, 0}) :
    (Cat.of WalkingArrow ⟶ C) ≃ (Σ (X Y : C), (X ⟶ Y)) where
  toFun F := ⟨F.toFunctor.obj .zero, F.toFunctor.obj .one, F.toFunctor.map WalkingArrowHom.arr⟩
  invFun := fun ⟨X, Y, f⟩ => Functor.toCatHom
    { obj := fun
        | .zero => X
        | .one => Y
      map := fun {A B} h => match A, B, h with
        | .zero, .zero, .id .zero => 𝟙 X
        | .one, .one, .id .one => 𝟙 Y
        | .zero, .one, .arr => f
      map_id := fun
        | .zero => rfl
        | .one => rfl
      map_comp := fun {A B C_1} f1 f2 => match A, B, C_1, f1, f2 with
        | .zero, .zero, .zero, .id .zero, .id .zero => (Category.id_comp _).symm
        | .zero, .zero, .one, .id .zero, .arr => (Category.id_comp _).symm
        | .zero, .one, .one, .arr, .id .one => (Category.comp_id _).symm
        | .one, .one, .one, .id .one, .id .one => (Category.id_comp _).symm }
  left_inv := fun F => by
    apply Cat.ext
    fapply CategoryTheory.Functor.ext
    · intro
      | .zero => rfl
      | .one => rfl
    · intro A B h
      match A, B, h with
      | .zero, .zero, .id .zero =>
        dsimp
        letI : Category C := C.str
        have : 𝟙 (F.toFunctor.obj .zero) ≫ F.toFunctor.map (WalkingArrowHom.id .zero) ≫
            𝟙 (F.toFunctor.obj .zero) = F.toFunctor.map (WalkingArrowHom.id .zero) := by
          rw [Category.comp_id, Category.id_comp]
        change 𝟙 _ = _
        rw [this]
        exact (F.toFunctor.map_id .zero).symm
      | .one, .one, .id .one =>
        dsimp
        letI : Category C := C.str
        have : 𝟙 (F.toFunctor.obj .one) ≫ F.toFunctor.map (WalkingArrowHom.id .one) ≫
            𝟙 (F.toFunctor.obj .one) = F.toFunctor.map (WalkingArrowHom.id .one) := by
          rw [Category.comp_id, Category.id_comp]
        change 𝟙 _ = _
        rw [this]
        exact (F.toFunctor.map_id .one).symm
      | .zero, .one, .arr =>
        dsimp
        letI : Category C := C.str
        have : 𝟙 (F.toFunctor.obj .zero) ≫ F.toFunctor.map WalkingArrowHom.arr ≫
            𝟙 (F.toFunctor.obj .one) = F.toFunctor.map WalkingArrowHom.arr := by
          rw [Category.comp_id, Category.id_comp]
        change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
        rw [this]
  right_inv := fun ⟨X, Y, f⟩ => rfl

def exercise_4_1_6 :
    coyoneda.obj (op (Cat.of WalkingArrow)) ≅ exercise_4_1_6_functor :=
  NatIso.ofComponents
    (fun C => Equiv.toIso (exercise_4_1_6_equiv C))
    (fun {C D} F => by
      ext G
      rfl)

variable {C_adj : Type u} [Category.{v} C_adj] {D_adj : Type u'} [Category.{v} D_adj]

def exercise_4_1_7_left (F : C_adj ⥤ D_adj) : C_adjᵒᵖ × D_adj ⥤ Type v where
  obj p := F.obj (unop p.1) ⟶ p.2
  map f := ↾fun h => F.map f.1.unop ≫ h ≫ f.2

def exercise_4_1_7_right (G : D_adj ⥤ C_adj) : C_adjᵒᵖ × D_adj ⥤ Type v where
  obj p := unop p.1 ⟶ G.obj p.2
  map f := ↾fun h => f.1.unop ≫ h ≫ G.map f.2

def exercise_4_1_7_forward {F : C_adj ⥤ D_adj} {G : D_adj ⥤ C_adj} (adj : F ⊣ G) :
    exercise_4_1_7_left F ≅ exercise_4_1_7_right G :=
  NatIso.ofComponents
    (fun p => Equiv.toIso (adj.homEquiv (unop p.1) p.2))
    (fun {p q} f => by
      ext h
      dsimp [exercise_4_1_7_left, exercise_4_1_7_right]
      rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left])

def exercise_4_1_7_reverse {F : C_adj ⥤ D_adj} {G : D_adj ⥤ C_adj}
    (iso : exercise_4_1_7_left F ≅ exercise_4_1_7_right G) : F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A B => (iso.app (op A, B)).toEquiv
      homEquiv_naturality_left_symm := fun {A' A B} f g => by
        have h := iso.inv.naturality_apply (X := (op A, B)) (Y := (op A', B)) (f.op, 𝟙 B) g
        change (iso.app (op A', B)).toEquiv.symm (f ≫ g ≫ G.map (𝟙 B)) =
          F.map f ≫ (iso.app (op A, B)).toEquiv.symm g ≫ 𝟙 B at h
        rw [G.map_id, Category.comp_id, Category.comp_id] at h
        exact h
      homEquiv_naturality_right := fun {A B B'} f g => by
        have h := iso.hom.naturality_apply (X := (op A, B)) (Y := (op A, B')) (𝟙 (op A), g) f
        change (iso.app (op A, B')).toEquiv (F.map (𝟙 A) ≫ f ≫ g) =
          𝟙 A ≫ (iso.app (op A, B)).toEquiv f ≫ G.map g at h
        rw [F.map_id, Category.id_comp, Category.id_comp] at h
        exact h }

theorem exercise_4_1_7 {F : C_adj ⥤ D_adj} {G : D_adj ⥤ C_adj} :
    Nonempty (F ⊣ G) ↔ Nonempty (exercise_4_1_7_left F ≅ exercise_4_1_7_right G) :=
  ⟨fun ⟨adj⟩ => ⟨exercise_4_1_7_forward adj⟩,
   fun ⟨iso⟩ => ⟨exercise_4_1_7_reverse iso⟩⟩

end Representables
