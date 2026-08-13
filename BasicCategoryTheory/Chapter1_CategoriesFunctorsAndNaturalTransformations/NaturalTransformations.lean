-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.Functors
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.Cardinal.Free

namespace NaturalTransformations

universe u v u' v'

open CategoryTheory

def example_1_3_3 {A : Type u} {B : Type u'} [Category.{v'} B] (F G : Discrete A ⥤ B) :
    (F ⟶ G) ≃ (∀ a : A, F.obj (Discrete.mk a) ⟶ G.obj (Discrete.mk a)) :=
  { toFun := fun α a => α.app (Discrete.mk a),
    invFun := fun f => Discrete.natTrans (fun i => f i.as),
    left_inv := fun α => by
      apply NatTrans.ext
      funext i
      cases i with
      | mk as => rfl,
    right_inv := fun f => by
      funext a
      rfl }

def example_1_3_4 (G : MonCat.{u}) (F H : SingleObj G ⥤ Type u) :
    (F ⟶ H) ≃
      { f : F.obj PUnit.unit → H.obj PUnit.unit //
        ∀ g : G, ∀ x : F.obj PUnit.unit, f (F.map g x) = H.map g (f x) } :=
  { toFun := fun α => ⟨α.app PUnit.unit, fun g x => by
      exact congrFun
        (congrArg (fun h : F.obj PUnit.unit ⟶ H.obj PUnit.unit =>
          (h : F.obj PUnit.unit → H.obj PUnit.unit))
          (α.naturality (X := PUnit.unit) (Y := PUnit.unit) g)) x⟩,
    invFun := fun f =>
      { app := fun X => by
          cases X
          exact (TypeCat.homEquiv (X := F.obj PUnit.unit) (Y := H.obj PUnit.unit)).symm f.1,
        naturality := fun x y g => by
          cases x
          cases y
          apply (TypeCat.homEquiv (X := F.obj PUnit.unit) (Y := H.obj PUnit.unit)).injective
          funext z
          simpa using f.2 g z },
    left_inv := fun α => by
      apply NatTrans.ext
      funext X
      cases X
      rfl,
    right_inv := fun f => by
      apply Subtype.ext
      rfl }

def example_1_3_5_gl (n : ℕ) : CommRingCat.{u} ⥤ MonCat.{u} where
  obj R := MonCat.of (Matrix (Fin n) (Fin n) R)
  map f := MonCat.ofHom
    { toFun := fun A => Matrix.map A f.hom'
      map_one' := by
        ext i j
        simp [Matrix.one_apply]
      map_mul' := by
        intro A B
        ext i j
        simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul] }
  map_id R := by
    ext A i j
    change Matrix.map A (RingHom.id ↑R) i j = A i j
    rfl
  map_comp := by
    intro R S T f g
    ext A i j
    rfl

def example_1_3_5_units : CommRingCat.{u} ⥤ MonCat.{u} where
  obj R := MonCat.of R
  map f := MonCat.ofHom f.hom'.toMonoidHom
  map_id R := by
    ext x
    rfl
  map_comp := by
    intro R S T f g
    ext x
    rfl

def example_1_3_5 (n : ℕ) : example_1_3_5_gl n ⟶ example_1_3_5_units where
  app R := MonCat.ofHom
    { toFun := fun A : Matrix (Fin n) (Fin n) ↑R => Matrix.det A
      map_one' := Matrix.det_one
      map_mul' := Matrix.det_mul }
  naturality := by
    intro R S f
    ext A
    exact Eq.symm (RingHom.map_det f.hom' (A : Matrix (Fin n) (Fin n) ↑R))
def example_1_3_7_0 {B : Type u} [Category.{u} B] :
    Cat.of (Discrete PEmpty ⥤ B) ≅ Cat.of (Discrete PUnit) :=
  let hom : Cat.of (Discrete PEmpty ⥤ B) ⥤ Cat.of (Discrete PUnit) :=
    { obj := fun _ => Discrete.mk PUnit.unit,
      map := fun _ => 𝟙 (Discrete.mk PUnit.unit),
      map_id := fun _ => rfl,
      map_comp := by intro X Y Z α β; rfl }
  let inv : Cat.of (Discrete PUnit) ⥤ Cat.of (Discrete PEmpty ⥤ B) :=
    { obj := fun _ => Discrete.functor (PEmpty.elim : PEmpty → B),
      map := fun _ => 𝟙 (Discrete.functor (PEmpty.elim : PEmpty → B)),
      map_id := fun _ => rfl,
      map_comp := by
        intro X Y Z f g
        apply NatTrans.ext
        funext X'
        cases X' with
        | mk as => cases as }
  { hom := { toFunctor := hom },
    inv := { toFunctor := inv },
    hom_inv_id := by
      apply Cat.Hom.ext
      refine CategoryTheory.Functor.ext ?_ ?_
      · intro F
        apply CategoryTheory.Functor.ext
        · intro X
          exact PEmpty.elim X.as
        · intro X
          exact PEmpty.elim X.as
      · intro F G α
        apply NatTrans.ext
        funext X
        exact PEmpty.elim X.as
    inv_hom_id := by
      apply Cat.Hom.ext
      have hobj : ∀ X : Discrete PUnit, (inv ⋙ hom).obj X = X := by
        intro X
        cases X with
        | mk as =>
          cases as
          rfl
      refine CategoryTheory.Functor.ext hobj ?_
      intro X Y f
      cases X with
      | mk as =>
        cases as
        cases Y with
        | mk as =>
          cases as
          rcases f with ⟨⟨e⟩⟩
          cases e
          rfl }

def example_1_3_8 (G : MonCat.{u}) : (SingleObj G ⥤ Type u) ≌ Action (Type u) G :=
  (Action.functorCategoryEquivalence (Type u) G).symm

def example_1_3_8_right (G : MonCat.{u}) :
    ((SingleObj G)ᵒᵖ ⥤ Type u) ≌ Action (Type u) Gᵐᵒᵖ :=
  Functors.example_1_2_14 G

def example_1_3_9 {A : Type u} [Preorder A] {B : Type u'} [Preorder B] (F G : A ⥤ B) :
    (F ⟶ G) ≃ (∀ a : A, F.obj a ≤ G.obj a) :=
  { toFun := fun α => fun a => (α.app a).le,
    invFun := fun h =>
      { app := fun a => (h a).hom,
        naturality := fun a b f => Subsingleton.elim _ _ },
    left_inv := fun α => by
      apply NatTrans.ext
      rfl,
    right_inv := fun h => by
      funext a
      rfl }

theorem lemma_1_3_11 {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F G : C ⥤ D} (α : F ⟶ G) :
    IsIso α ↔ ∀ X : C, IsIso (α.app X) :=
  NatTrans.isIso_iff_isIso_app α

def example_1_3_13 {A : Type u} {B : Type u'} [Category.{v'} B] (F G : Discrete A ⥤ B) :
    Nonempty (F ≅ G) ↔ ∀ a : A, Nonempty (F.obj (Discrete.mk a) ≅ G.obj (Discrete.mk a)) := by
  constructor
  · intro h a
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact h.some.hom.app (Discrete.mk a)
    · exact h.some.inv.app (Discrete.mk a)
    · exact congrFun (congrArg NatTrans.app h.some.hom_inv_id) (Discrete.mk a)
    · exact congrFun (congrArg NatTrans.app h.some.inv_hom_id) (Discrete.mk a)
  · intro h
    exact ⟨Discrete.natIso (fun i => (h i.as).some)⟩

abbrev FDVect (k : Type u) [Field k] :=
  ObjectProperty.FullSubcategory (fun V : ModuleCat.{u} k => Module.Finite k V)

instance FDVect.finite (k : Type u) [Field k] (V : FDVect.{u} k) : Module.Finite k V.obj :=
  V.2

noncomputable def doubleDualFunctor (k : Type u) [Field k] : FDVect.{u} k ⥤ FDVect.{u} k where
  obj V := ⟨ModuleCat.of k (Module.Dual k (Module.Dual k V.obj)), inferInstance⟩
  map {X Y} f := ObjectProperty.homMk (ModuleCat.ofHom (f.hom.hom.dualMap.dualMap))
  map_id V := by
    apply ObjectProperty.hom_ext
    ext x
    simp [LinearMap.dualMap_id]
  map_comp {X Y Z} f g := by
    apply ObjectProperty.hom_ext
    ext x
    simp [LinearMap.dualMap_comp_dualMap]

noncomputable def example_1_3_14 (k : Type u) [Field k] :
    (𝟭 (FDVect.{u} k) ≅ doubleDualFunctor k) :=
  NatIso.ofComponents
    (fun V =>
      ObjectProperty.isoMk (P := fun W : ModuleCat.{u} k => Module.Finite k W)
        (Module.evalEquiv k V.obj).toModuleIso)
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      exact Module.Dual.eval_naturality (f := f.hom.hom))

theorem propn_1_3_18 {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) [F.IsEquivalence] :
    F.Full ∧ F.Faithful ∧ F.EssSurj := by
  have h_full : F.Full := inferInstance
  have h_faithful : F.Faithful := inferInstance
  have h_esso : F.EssSurj := inferInstance
  exact ⟨h_full, h_faithful, h_esso⟩

theorem propn_1_3_18_converse {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj] : F.IsEquivalence :=
  Functor.IsEquivalence.mk (full := by infer_instance) (faithful := by infer_instance)
    (essSurj := by infer_instance)

noncomputable def cor_1_3_19 {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful] :
    C ≌ F.EssImageSubcategory := by
  have : F.toEssImage.IsEquivalence := Equivalence.fullyFaithfulToEssImage F
  exact Functor.asEquivalence F.toEssImage

noncomputable def example_1_3_20 {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : D ⥤ C) [F.Full] [F.Faithful]
    (h : ∀ X : C, ∃ Y : D, Nonempty (F.obj Y ≅ X)) : D ≌ C := by
  haveI : F.EssSurj := ⟨fun X => h X⟩
  haveI : F.IsEquivalence := propn_1_3_18_converse F
  exact Functor.asEquivalence F

noncomputable section

abbrev oneObjectProperty : ObjectProperty (Cat.{u, 0}) :=
  fun C => Nonempty (Unique C)

abbrev OneObjectCat := oneObjectProperty.FullSubcategory

noncomputable def example_1_3_21_endMap {C D : OneObjectCat.{u}} [Unique C.obj] [Unique D.obj]
    (H : C.obj ⥤ D.obj) : End (default : C.obj) →* End (default : D.obj) where
  toFun f := eqToHom (Unique.eq_default (H.obj (default : C.obj))).symm ≫ H.map f ≫
    eqToHom (Unique.eq_default (H.obj (default : C.obj)))
  map_one' := by
    simp [H.map_id, eqToHom_trans, eqToHom_refl]
  map_mul' f g := by
    simp only [End.mul_def, H.map_comp]
    simp [eqToHom_refl, Category.assoc, Category.id_comp]

noncomputable def example_1_3_21_F : OneObjectCat.{u} ⥤ MonCat.{u} where
  obj C := by
    letI : Unique C.obj := Classical.choice C.property
    exact MonCat.of (End (default : C.obj))
  map {C D} f := by
    letI : Unique C.obj := Classical.choice C.property
    letI : Unique D.obj := Classical.choice D.property
    exact MonCat.ofHom (example_1_3_21_endMap f.hom.toFunctor)
  map_id C := by
    letI : Unique C.obj := Classical.choice C.property
    ext f
    dsimp [example_1_3_21_endMap]
    simp [Category.id_comp, Category.comp_id]
  map_comp {C D E} f g := by
    letI : Unique C.obj := Classical.choice C.property
    letI : Unique D.obj := Classical.choice D.property
    letI : Unique E.obj := Classical.choice E.property
    ext x
    dsimp [example_1_3_21_endMap]
    simp [g.hom.toFunctor.map_comp, eqToHom_map]

noncomputable def example_1_3_21_G : MonCat.{u} ⥤ OneObjectCat.{u} where
  obj M :=
    ⟨Cat.of (SingleObj M), ⟨uniqueOfSubsingleton (α := SingleObj M) (SingleObj.star M)⟩⟩
  map {M N} f := { hom := (SingleObj.mapHom M N f.hom).toCatHom }
  map_id M := by
    apply InducedCategory.hom_ext
    apply Cat.Hom.ext
    rfl
  map_comp {M N P} f g := by
    apply InducedCategory.hom_ext
    apply Cat.Hom.ext
    rfl

noncomputable def example_1_3_21_toSingleObj (C : OneObjectCat.{u}) [Unique C.obj] :
    C.obj ⥤ SingleObj (End (default : C.obj)) where
  obj := fun _ => SingleObj.star (End (default : C.obj))
  map := fun {X Y} f =>
    (eqToHom (Unique.eq_default X).symm ≫ f ≫ eqToHom (Unique.eq_default Y) :
      End (default : C.obj))
  map_id := by
    intro X
    simp [SingleObj.id_as_one]
    rfl
  map_comp := by
    intro X Y Z f g
    simp only [SingleObj.comp_as_mul]
    rw [End.mul_def]
    simp

noncomputable def example_1_3_21_fromSingleObj (C : OneObjectCat.{u}) [Unique C.obj] :
    SingleObj (End (default : C.obj)) ⥤ C.obj where
  obj := fun _ => default
  map := fun f => f
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

noncomputable def example_1_3_21_oneObjectIso (C : OneObjectCat.{u}) [Unique C.obj] :
    C.obj ≅ Cat.of (SingleObj (End (default : C.obj))) where
  hom := (example_1_3_21_toSingleObj C).toCatHom
  inv := (example_1_3_21_fromSingleObj C).toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    dsimp [example_1_3_21_toSingleObj, example_1_3_21_fromSingleObj]
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro X
      exact (Unique.eq_default X).symm
    · intro X Y f
      dsimp [example_1_3_21_toSingleObj, example_1_3_21_fromSingleObj]
  inv_hom_id := by
    apply Cat.Hom.ext
    dsimp [example_1_3_21_toSingleObj, example_1_3_21_fromSingleObj]
    refine CategoryTheory.Functor.hext ?_ ?_
    · intro X
      exact Subsingleton.elim (SingleObj.star (End (default : C.obj))) X
    · intro X Y f
      exact heq_of_eq (by simp)

set_option backward.isDefEq.respectTransparency false in
noncomputable def example_1_3_21_unit_iso :
    𝟭 OneObjectCat.{u} ≅ example_1_3_21_F ⋙ example_1_3_21_G :=
  NatIso.ofComponents
    (fun C =>
      letI : Unique C.obj := Classical.choice C.property
      InducedCategory.isoMk (example_1_3_21_oneObjectIso C))
    (by
      intro X Y f
      apply InducedCategory.hom_ext
      apply Cat.Hom.ext
      letI : Unique X.obj := Classical.choice X.property
      letI : Unique Y.obj := Classical.choice Y.property
      dsimp [example_1_3_21_oneObjectIso, example_1_3_21_toSingleObj, example_1_3_21_endMap,
        example_1_3_21_F, example_1_3_21_G]
      refine CategoryTheory.Functor.ext ?_ ?_
      · intro X'
        rfl
      · intro X' Y' m
        simp [SingleObj.mapHom, f.hom.toFunctor.map_comp, eqToHom_map])
noncomputable def example_1_3_21_counit_app (M : MonCat.{u}) :
    (example_1_3_21_G ⋙ example_1_3_21_F).obj M ≅ M where
  hom := MonCat.ofHom (SingleObj.toEnd M).symm.toMonoidHom
  inv := MonCat.ofHom (SingleObj.toEnd M).toMonoidHom
  hom_inv_id := by
    ext x
    change (SingleObj.toEnd ↑M).toMonoidHom.comp (SingleObj.toEnd ↑M).symm.toMonoidHom x = x
    rw [MonoidHom.comp_apply]
    exact MulEquiv.apply_symm_apply (SingleObj.toEnd ↑M) x
  inv_hom_id := by
    ext x
    change (SingleObj.toEnd ↑M).symm.toMonoidHom.comp (SingleObj.toEnd ↑M).toMonoidHom x = x
    rw [MonoidHom.comp_apply]
    exact MulEquiv.symm_apply_apply (SingleObj.toEnd ↑M) x

set_option backward.isDefEq.respectTransparency false in
noncomputable def example_1_3_21_counit_iso :
    example_1_3_21_G ⋙ example_1_3_21_F ≅ 𝟭 MonCat.{u} :=
  NatIso.ofComponents example_1_3_21_counit_app
    (by
      intro M N f
      ext x
      simp [MonCat.hom_comp, MonoidHom.comp_apply, example_1_3_21_counit_app, example_1_3_21_F,
        example_1_3_21_G, example_1_3_21_endMap, SingleObj.mapHom, SingleObj.toEnd,
        MulEquiv.symm, MulEquiv.toMonoidHom, eqToHom_refl, Equiv.refl])

namespace Example1323

structure GrpArb : Type (u + 1) where
  carrier : Type u
  group : Group carrier

instance : Category.{u, u + 1} GrpArb where
  Hom G H := G.carrier → H.carrier
  id _ := fun x => x
  comp f g := fun x => g (f x)
  id_comp f := by ext x; rfl
  comp_id f := by ext x; rfl
  assoc f g h := by ext x; rfl

abbrev NonemptySet : Type (u + 1) := { S : Type u // Nonempty S }

instance : Category.{u, u + 1} NonemptySet where
  Hom A B := A.1 → B.1
  id _ := fun x => x
  comp f g := fun x => g (f x)
  id_comp f := by ext x; rfl
  comp_id f := by ext x; rfl
  assoc f g h := by ext x; rfl

lemma example_1_3_23_nonempty_group (S : Type u) (h : Nonempty S) :
    Nonempty (Group S) := by
  by_cases hfin : Finite S
  · letI : Fintype S := Fintype.ofFinite S
    have hpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr h
    haveI : NeZero (Fintype.card S) := ⟨Nat.ne_of_gt hpos⟩
    have hcard : Fintype.card S = Fintype.card (ZMod (Fintype.card S)) := by
      rw [ZMod.card]
    letI : Fintype (Multiplicative (ZMod (Fintype.card S))) :=
      ZMod.fintype (Fintype.card S)
    let e : S ≃ Multiplicative (ZMod (Fintype.card S)) := Fintype.equivOfCardEq hcard
    exact ⟨Equiv.group e⟩
  · have hinf : Infinite S := not_finite_iff_infinite.mp hfin
    have hle : Cardinal.aleph0 ≤ Cardinal.mk S := Cardinal.infinite_iff.mp hinf
    have hcard : Cardinal.mk S = Cardinal.mk (FreeGroup S) := by
      haveI : Nonempty S := h
      rw [Cardinal.mk_freeGroup, max_eq_left hle]
    exact ⟨Equiv.group (Classical.choice (Cardinal.eq.mp hcard))⟩

noncomputable def example_1_3_23_U : GrpArb.{u} ⥤ NonemptySet.{u} where
  obj G := by
    letI : Group G.carrier := G.group
    exact ⟨G.carrier, ⟨1⟩⟩
  map f := f
  map_id G := by
    funext x
    rfl
  map_comp f g := by
    funext x
    rfl

instance example_1_3_23_U_full : example_1_3_23_U.Full where
  map_surjective := by
    intro X Y f
    exact ⟨f, rfl⟩

instance example_1_3_23_U_faithful : example_1_3_23_U.Faithful where
  map_injective := by
    intro X Y f g h
    exact h

noncomputable instance example_1_3_23_U_essSurj : example_1_3_23_U.EssSurj where
  mem_essImage := by
    intro S
    dsimp [Functor.essImage]
    letI : Group S.1 := Classical.choice (example_1_3_23_nonempty_group S.1 S.2)
    refine ⟨⟨S.1, inferInstance⟩, ?_⟩
    refine ⟨CategoryTheory.Iso.mk ?_ ?_ ?_ ?_⟩
    · exact fun x => x
    · exact fun x => x
    · funext x
      rfl
    · funext x
      rfl

instance example_1_3_23_U_isEquivalence : example_1_3_23_U.IsEquivalence :=
  Functor.IsEquivalence.mk

noncomputable def example_1_3_23 : GrpArb.{u} ≌ NonemptySet.{u} :=
  Functor.asEquivalence example_1_3_23_U

end Example1323

theorem exercise_1_3_26 {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F G : C ⥤ D} (α : F ⟶ G) :
    IsIso α ↔ ∀ X : C, IsIso (α.app X) :=
  NatTrans.isIso_iff_isIso_app α

lemma exercise_1_3_27_unop_op {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op = F := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro X
    rfl
  · intro X Y f
    simp

lemma exercise_1_3_27_op_unop {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) : F.op.unop = F := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro X
    rfl
  · intro X Y f
    simp

lemma exercise_1_3_27_opInv_opHom (C : Type u) [Category.{v} C] (D : Type u')
    [Category.{v'} D] :
    Functor.opInv C D ⋙ Functor.opHom C D = 𝟭 (Cᵒᵖ ⥤ Dᵒᵖ) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro F
    exact exercise_1_3_27_unop_op F
  · intro F G f
    apply NatTrans.ext
    funext X
    simp

lemma exercise_1_3_27_opHom_opInv (C : Type u) [Category.{v} C] (D : Type u')
    [Category.{v'} D] :
    Functor.opHom C D ⋙ Functor.opInv C D = 𝟭 (C ⥤ D)ᵒᵖ := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro F
    exact congrArg Opposite.op (exercise_1_3_27_op_unop (Opposite.unop F))
  · intro F G f
    apply Quiver.Hom.unop_inj
    apply NatTrans.ext
    funext X
    simp

def exercise_1_3_27 (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] :
    Cat.of (Cᵒᵖ ⥤ Dᵒᵖ) ≅ Cat.of ((C ⥤ D)ᵒᵖ) :=
  { hom := (Functor.opInv C D).toCatHom,
    inv := (Functor.opHom C D).toCatHom,
    hom_inv_id := by
      apply Cat.Hom.ext
      exact exercise_1_3_27_opInv_opHom C D,
    inv_hom_id := by
      apply Cat.Hom.ext
      exact exercise_1_3_27_opHom_opInv C D }

def exercise_1_3_28a (A B : Type u) : A × (A → B) → B :=
  fun ⟨a, f⟩ => f a

def exercise_1_3_28b (A B : Type u) : A → (A → B) → B :=
  fun a f => f a

def exercise_1_3_29_FA {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A × B ⥤ C) (a : A) : B ⥤ C where
  obj b := F.obj (a, b)
  map {b b'} g := F.map (Prod.mkHom (𝟙 a) g)
  map_id b := F.map_id (a, b)
  map_comp {b b' b''} g h := by
    rw [← F.map_comp (Prod.mkHom (𝟙 a) g) (Prod.mkHom (𝟙 a) h)]
    simp

def exercise_1_3_29_FB {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A × B ⥤ C) (b : B) : A ⥤ C where
  obj a := F.obj (a, b)
  map {a a'} f := F.map (Prod.mkHom f (𝟙 b))
  map_id a := F.map_id (a, b)
  map_comp {a a' a''} f f' := by
    rw [← F.map_comp (Prod.mkHom f (𝟙 b)) (Prod.mkHom f' (𝟙 b))]
    simp

theorem exercise_1_3_29 {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F G : A × B ⥤ C)
    (α : ∀ a b, F.obj (a, b) ⟶ G.obj (a, b))
    (h_natural : ∀ {a a' b b'} (f : a ⟶ a') (g : b ⟶ b'),
      F.map (Prod.mkHom f g) ≫ α a' b' = α a b ≫ G.map (Prod.mkHom f g)) :
    (∀ (a : A) {b b' : B} (g : b ⟶ b'),
      (exercise_1_3_29_FA F a).map g ≫ α a b' = α a b ≫ (exercise_1_3_29_FA G a).map g) ∧
    (∀ (b : B) {a a' : A} (f : a ⟶ a'),
      (exercise_1_3_29_FB F b).map f ≫ α a' b = α a b ≫ (exercise_1_3_29_FB G b).map f) := by
  constructor
  · intro a b b' g
    dsimp [exercise_1_3_29_FA]
    simpa using h_natural (𝟙 a) g
  · intro b a a' f
    dsimp [exercise_1_3_29_FB]
    simpa using h_natural f (𝟙 b)

theorem exercise_1_3_29_converse {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F G : A × B ⥤ C)
    (α : ∀ a b, F.obj (a, b) ⟶ G.obj (a, b))
    (hA : ∀ (a : A) {b b' : B} (g : b ⟶ b'),
      (exercise_1_3_29_FA F a).map g ≫ α a b' = α a b ≫ (exercise_1_3_29_FA G a).map g)
    (hB : ∀ (b : B) {a a' : A} (f : a ⟶ a'),
      (exercise_1_3_29_FB F b).map f ≫ α a' b = α a b ≫ (exercise_1_3_29_FB G b).map f)
    {a a' : A} {b b' : B} (f : a ⟶ a') (g : b ⟶ b') :
    F.map (Prod.mkHom f g) ≫ α a' b' = α a b ≫ G.map (Prod.mkHom f g) := by
  have hA' : F.map (Prod.mkHom (𝟙 a') g) ≫ α a' b' = α a' b ≫ G.map (Prod.mkHom (𝟙 a') g) := by
    have h := hA a' g
    dsimp [exercise_1_3_29_FA] at h
    simpa using h
  have hB' : F.map (Prod.mkHom f (𝟙 b)) ≫ α a' b = α a b ≫ G.map (Prod.mkHom f (𝟙 b)) := by
    have h := hB b f
    dsimp [exercise_1_3_29_FB] at h
    simpa using h
  have h_decomp : Prod.mkHom f g = Prod.mkHom f (𝟙 b) ≫ Prod.mkHom (𝟙 a') g := by
    simp
  rw [h_decomp, F.map_comp, G.map_comp]
  calc
    (F.map (Prod.mkHom f (𝟙 b)) ≫ F.map (Prod.mkHom (𝟙 a') g)) ≫ α a' b'
        = F.map (Prod.mkHom f (𝟙 b)) ≫ (F.map (Prod.mkHom (𝟙 a') g) ≫ α a' b') := by
      rw [Category.assoc]
    _ = F.map (Prod.mkHom f (𝟙 b)) ≫ (α a' b ≫ G.map (Prod.mkHom (𝟙 a') g)) := by
      rw [hA']
    _ = (F.map (Prod.mkHom f (𝟙 b)) ≫ α a' b) ≫ G.map (Prod.mkHom (𝟙 a') g) := by
      rw [← Category.assoc]
    _ = (α a b ≫ G.map (Prod.mkHom f (𝟙 b))) ≫ G.map (Prod.mkHom (𝟙 a') g) := by
      rw [hB']
    _ = α a b ≫ (G.map (Prod.mkHom f (𝟙 b)) ≫ G.map (Prod.mkHom (𝟙 a') g)) := by
      rw [Category.assoc]

theorem exercise_1_3_32 {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) : F.IsEquivalence ↔ F.Full ∧ F.Faithful ∧ F.EssSurj := by
  constructor
  · intro h
    have : F.IsEquivalence := h
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · intro ⟨h_full, h_faithful, h_esso⟩
    have : F.Full := h_full
    have : F.Faithful := h_faithful
    have : F.EssSurj := h_esso
    exact Functor.IsEquivalence.mk

abbrev Mat (k : Type u) [Field k] := ℕ

instance matCategory (k : Type u) [Field k] : Category.{u} (Mat k) where
  Hom m n := Matrix (Fin n) (Fin m) k
  id m := 1
  comp f g := g * f
  id_comp f := by
    exact Matrix.mul_one f
  comp_id f := by
    exact Matrix.one_mul f
  assoc f g h := by
    rw [Matrix.mul_assoc]

noncomputable def matToFDVect (k : Type u) [Field k] : Mat k ⥤ FDVect.{u} k where
  obj n := ⟨ModuleCat.of k (Fin n → k), inferInstance⟩
  map {m n} M :=
    ObjectProperty.homMk (ModuleCat.ofHom (M.mulVecLin : (Fin m → k) →ₗ[k] Fin n → k))
  map_id m := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    exact Matrix.mulVecLin_one (n := Fin m)
  map_comp {m n p} f g := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    exact Matrix.mulVecLin_mul g f

noncomputable instance matToFDVect_full (k : Type u) [Field k] : (matToFDVect k).Full :=
  { map_surjective := fun {m n} M => ⟨LinearMap.toMatrix' M.hom.hom, by
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      change Matrix.mulVecLin (LinearMap.toMatrix' M.hom.hom) = M.hom.hom
      rw [← Matrix.toLin'_apply' (M := LinearMap.toMatrix' M.hom.hom)]
      exact Matrix.toLin'_toMatrix' M.hom.hom⟩ }

noncomputable instance matToFDVect_faithful (k : Type u) [Field k] : (matToFDVect k).Faithful :=
  { map_injective := fun {m n} => by
      intro M N h
      apply (Matrix.toLin' (R := k)).injective
      rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
      exact congrArg (fun φ : (matToFDVect k).obj m ⟶ (matToFDVect k).obj n => φ.hom.hom) h }

noncomputable instance matToFDVect_essSurj (k : Type u) [Field k] : (matToFDVect k).EssSurj :=
  { mem_essImage := fun V => by
      refine ⟨(Module.finrank k V.obj : Mat k), ?_⟩
      exact ⟨ObjectProperty.isoMk (P := fun W : ModuleCat.{u} k => Module.Finite k W)
        ((Module.finBasis k V.obj).equivFun.symm.toModuleIso)⟩ }

theorem exercise_1_3_33 (k : Type u) [Field k] :
    Nonempty (Mat k ≌ FDVect.{u} k) := by
  letI : (matToFDVect k).IsEquivalence := Functor.IsEquivalence.mk
  exact ⟨(matToFDVect k).asEquivalence⟩

def exercise_1_3_34_refl (C : Type u) [Category.{v} C] : C ≌ C :=
  CategoryTheory.Equivalence.refl

def exercise_1_3_34_symm {C D : Type u} [Category.{v} C] [Category.{v} D]
    (e : C ≌ D) : D ≌ C :=
  e.symm

def exercise_1_3_34_trans {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    (e₁ : C ≌ D) (e₂ : D ≌ E) : C ≌ E :=
  e₁.trans e₂

end

end NaturalTransformations
