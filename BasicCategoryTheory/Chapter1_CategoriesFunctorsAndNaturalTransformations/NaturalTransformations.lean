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
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Order.Fin.Basic
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

def example_1_3_7_1 {B : Type u} [Category.{u} B] : Cat.of (Discrete PUnit ⥤ B) ≅ Cat.of B :=
  let hom : Cat.of (Discrete PUnit ⥤ B) ⥤ Cat.of B :=
    { obj := fun F => F.obj (Discrete.mk PUnit.unit),
      map := fun α => α.app (Discrete.mk PUnit.unit),
      map_id := fun F => rfl,
      map_comp := fun α β => rfl }
  let inv : Cat.of B ⥤ Cat.of (Discrete PUnit ⥤ B) :=
    { obj := fun X => { obj := fun _ => X,
                        map := fun _ => 𝟙 X,
                        map_id := fun _ => rfl,
                        map_comp := by
                          intro X Y Z f g
                          change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
                          exact (Category.id_comp (X := _) (f := 𝟙 _)).symm },
      map := fun f => { app := fun _ => f,
                        naturality := by
                          intro i j g
                          exact (Category.id_comp f).trans
                            (Category.comp_id f).symm },
      map_id := fun X => by
        apply NatTrans.ext
        funext i
        rfl,
      map_comp := by
        intro X Y Z f g
        apply NatTrans.ext
        funext i
        rfl }
  { hom := { toFunctor := hom },
    inv := { toFunctor := inv },
    hom_inv_id := by
      apply Cat.Hom.ext
      have hobj : ∀ F : Discrete PUnit ⥤ B, (hom ⋙ inv).obj F = F := by
        intro F
        have hobj' : ∀ i : Discrete PUnit, ((hom ⋙ inv).obj F).obj i = F.obj i := by
          intro i
          cases i with
          | mk as =>
            cases as
            rfl
        refine CategoryTheory.Functor.ext hobj' ?_
        intro i j g
        cases i with
        | mk as =>
          cases as
          cases j with
          | mk as =>
            cases as
            rcases g with ⟨⟨e⟩⟩
            cases e
            simp
      refine CategoryTheory.Functor.ext hobj ?_
      intro F G α
      apply NatTrans.ext
      funext ⟨⟨⟩⟩
      have heq1 := @CategoryTheory.eqToHom_app (Discrete PUnit) _ B _
        ((hom ⋙ inv).obj F) F (hobj F) ⟨PUnit.unit⟩
      have heq2 := @CategoryTheory.eqToHom_app (Discrete PUnit) _ B _
        G ((hom ⋙ inv).obj G) (hobj G).symm ⟨PUnit.unit⟩
      change (inv.map (hom.map α)).app ⟨PUnit.unit⟩ =
        (@eqToHom (Discrete PUnit ⥤ B) _ _ _ (hobj F)).app ⟨PUnit.unit⟩ ≫ α.app ⟨PUnit.unit⟩ ≫
        (@eqToHom (Discrete PUnit ⥤ B) _ _ _ (hobj G).symm).app ⟨PUnit.unit⟩
      have h1 : Functor.congr_obj (hobj F) ⟨PUnit.unit⟩ = rfl := Subsingleton.elim _ rfl
      have h2 : Functor.congr_obj (hobj G).symm ⟨PUnit.unit⟩ = rfl := Subsingleton.elim _ rfl
      rw [heq1, heq2, h1, h2]
      change α.app ⟨PUnit.unit⟩ = 𝟙 _ ≫ α.app ⟨PUnit.unit⟩ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    inv_hom_id := by
      apply Cat.Hom.ext
      have hobj : ∀ X : B, (inv ⋙ hom).obj X = X := by
        intro X
        rfl
      refine CategoryTheory.Functor.ext hobj ?_
      intro X Y f
      change f = 𝟙 X ≫ f ≫ 𝟙 Y
      rw [Category.comp_id, Category.id_comp] }

def example_1_3_7_2 {B : Type u} [Category.{u} B] :
    Cat.of (Discrete (Fin 2) ⥤ B) ≅ Cat.of (B × B) :=
  let hom : Cat.of (Discrete (Fin 2) ⥤ B) ⥤ Cat.of (B × B) :=
    { obj := fun F => (F.obj (Discrete.mk 0), F.obj (Discrete.mk 1)),
      map := fun α => (α.app (Discrete.mk 0), α.app (Discrete.mk 1)),
      map_id := fun F => rfl,
      map_comp := fun α β => rfl }
  let inv : Cat.of (B × B) ⥤ Cat.of (Discrete (Fin 2) ⥤ B) :=
    { obj := fun P => Discrete.functor (fun k : Fin 2 => match k.val with
        | 0 => P.1
        | _ => P.2),
      map := fun f =>
        { app := fun i => match i with
            | Discrete.mk ⟨0, _⟩ => f.1
            | Discrete.mk ⟨n+1, _⟩ => f.2
          naturality := by
            intro i j g
            rcases g with ⟨⟨h⟩⟩
            cases i with
            | mk ias =>
              cases j with
              | mk jas =>
                fin_cases ias <;> fin_cases jas <;> (try cases h) <;> simp },
      map_id := by
        intro P
        apply NatTrans.ext
        funext i
        cases i with
        | mk ias => fin_cases ias <;> rfl
      map_comp := by
        intro P Q R f g
        apply NatTrans.ext
        funext i
        cases i with
        | mk ias => fin_cases ias <;> rfl }
  { hom := { toFunctor := hom },
    inv := { toFunctor := inv },
    hom_inv_id := by
      apply Cat.Hom.ext
      have hobj : ∀ F : Discrete (Fin 2) ⥤ B, (hom ⋙ inv).obj F = F := by
        intro F
        have hobj' : ∀ i : Discrete (Fin 2), ((hom ⋙ inv).obj F).obj i = F.obj i := by
          intro i
          cases i with
          | mk ias => fin_cases ias <;> rfl
        refine CategoryTheory.Functor.ext hobj' ?_
        intro i j g
        cases i with
        | mk ias =>
          cases j with
          | mk jas =>
            rcases g with ⟨⟨h⟩⟩
            cases h
            simp
      refine CategoryTheory.Functor.ext hobj ?_
      intro F G α
      apply NatTrans.ext
      funext i
      cases i with
      | mk ias =>
        fin_cases ias
        · have heq1 := @CategoryTheory.eqToHom_app (Discrete (Fin 2)) _ B _
            ((hom ⋙ inv).obj F) F (hobj F) ⟨0⟩
          have heq2 := @CategoryTheory.eqToHom_app (Discrete (Fin 2)) _ B _
            G ((hom ⋙ inv).obj G) (hobj G).symm ⟨0⟩
          change (inv.map (hom.map α)).app ⟨0⟩ =
            (@eqToHom (Discrete (Fin 2) ⥤ B) _ _ _ (hobj F)).app ⟨0⟩ ≫ α.app ⟨0⟩ ≫
            (@eqToHom (Discrete (Fin 2) ⥤ B) _ _ _ (hobj G).symm).app ⟨0⟩
          have h1 : Functor.congr_obj (hobj F) ⟨0⟩ = rfl := Subsingleton.elim _ rfl
          have h2 : Functor.congr_obj (hobj G).symm ⟨0⟩ = rfl := Subsingleton.elim _ rfl
          rw [heq1, heq2, h1, h2]
          change α.app ⟨0⟩ = 𝟙 _ ≫ α.app ⟨0⟩ ≫ 𝟙 _
          rw [Category.id_comp, Category.comp_id]
        · have heq1 := @CategoryTheory.eqToHom_app (Discrete (Fin 2)) _ B _
            ((hom ⋙ inv).obj F) F (hobj F) ⟨1⟩
          have heq2 := @CategoryTheory.eqToHom_app (Discrete (Fin 2)) _ B _
            G ((hom ⋙ inv).obj G) (hobj G).symm ⟨1⟩
          change (inv.map (hom.map α)).app ⟨1⟩ =
            (@eqToHom (Discrete (Fin 2) ⥤ B) _ _ _ (hobj F)).app ⟨1⟩ ≫ α.app ⟨1⟩ ≫
            (@eqToHom (Discrete (Fin 2) ⥤ B) _ _ _ (hobj G).symm).app ⟨1⟩
          have h1 : Functor.congr_obj (hobj F) ⟨1⟩ = rfl := Subsingleton.elim _ rfl
          have h2 : Functor.congr_obj (hobj G).symm ⟨1⟩ = rfl := Subsingleton.elim _ rfl
          rw [heq1, heq2, h1, h2]
          change α.app ⟨1⟩ = 𝟙 _ ≫ α.app ⟨1⟩ ≫ 𝟙 _
          rw [Category.id_comp, Category.comp_id]
    inv_hom_id := by
      apply Cat.Hom.ext
      have hobj : ∀ P : B × B, (inv ⋙ hom).obj P = P := by
        intro P
        rfl
      refine CategoryTheory.Functor.ext hobj ?_
      intro P Q f
      change f = 𝟙 P ≫ f ≫ 𝟙 Q
      rw [Category.comp_id, Category.id_comp] }

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

def zpowGroupHom {G : Type u} [Group G] (g : G) : Multiplicative ℤ →* G where
  toFun n := g ^ n.toAdd
  map_one' := by
    simp
  map_mul' := by
    intro n m
    change g ^ (n.toAdd + m.toAdd) = g ^ n.toAdd * g ^ m.toAdd
    rw [zpow_add]

theorem exercise_1_3_30 {G : Type u} [Group G] (g h : G) :
    Nonempty (SingleObj.mapHom (Multiplicative ℤ) G (zpowGroupHom (G := G) g) ≅
        SingleObj.mapHom (Multiplicative ℤ) G (zpowGroupHom (G := G) h)) ↔
      ∃ x : G, h = x⁻¹ * g * x := by
  constructor
  · intro hIso
    rcases hIso with ⟨α⟩
    let x : G := α.hom.app PUnit.unit
    refine ⟨x⁻¹, ?_⟩
    have hn := α.hom.naturality (X := PUnit.unit) (Y := PUnit.unit)
      (Multiplicative.ofAdd (1 : ℤ))
    change x * g ^ (1 : ℤ) = h ^ (1 : ℤ) * x at hn
    simp only [zpow_one] at hn
    calc
      h = (h * x) * x⁻¹ := by simp
      _ = (x * g) * x⁻¹ := by rw [← hn]
      _ = (x⁻¹)⁻¹ * g * x⁻¹ := by simp [mul_assoc]
  · intro ⟨x, hx⟩
    let y := x⁻¹
    refine ⟨NatIso.ofComponents
      (fun _ =>
        { hom := y,
          inv := y⁻¹,
          hom_inv_id := inv_mul_cancel y,
          inv_hom_id := mul_inv_cancel y })
      (by
        intro X Y f
        cases X; cases Y
        change y * g ^ f.toAdd = h ^ f.toAdd * y
        have h_conj : h = y * g * y⁻¹ := by
          calc
            h = x⁻¹ * g * x := hx
            _ = y * g * y⁻¹ := by simp [y]
        have h_pow : h ^ f.toAdd = y * g ^ f.toAdd * y⁻¹ := by
          rw [h_conj, conj_zpow]
        rw [h_pow, mul_assoc, inv_mul_cancel, mul_one])⟩

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

structure FinBijSet where
  carrier : Type u
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

attribute [instance] FinBijSet.fintype FinBijSet.decidableEq

instance : Category FinBijSet where
  Hom X Y := X.carrier ≃ Y.carrier
  id X := Equiv.refl X.carrier
  comp f g := f.trans g
  id_comp f := by ext x; rfl
  comp_id f := by ext x; rfl
  assoc f g h := by ext x; rfl

def exercise_1_3_31b_sym : FinBijSet ⥤ Type u where
  obj X := Equiv.Perm X.carrier
  map {X Y} e := TypeCat.ofHom (fun (σ : Equiv.Perm X.carrier) => e.symm.trans (σ.trans e))
  map_id X := by
    ext σ x
    rfl
  map_comp f g := by
    ext σ x
    rfl

noncomputable def exercise_1_3_31b_ord : FinBijSet ⥤ Type u where
  obj X := LinearOrder X.carrier
  map {X Y} e := TypeCat.ofHom (fun (L : LinearOrder X.carrier) =>
    letI : LinearOrder X.carrier := L
    LinearOrder.lift' e.symm e.symm.injective)
  map_id X := by
    ext L
    rfl
  map_comp f g := by
    ext L
    rfl

theorem exercise_1_3_31c : ¬ Nonempty (exercise_1_3_31b_sym.{u} ⟶ exercise_1_3_31b_ord.{u}) := by
  rintro ⟨α⟩
  let X : FinBijSet.{u} := ⟨ULift.{u} (Fin 2), inferInstance, inferInstance⟩
  let idX : Equiv.Perm (ULift.{u} (Fin 2)) := Equiv.refl _
  let swap : X ⟶ X := (Equiv.ulift.trans (Equiv.swap (0 : Fin 2) 1)).trans Equiv.ulift.symm
  have hswap : (exercise_1_3_31b_sym.map swap : _ → _) idX = idX := by
    apply Equiv.ext
    intro ⟨x⟩
    fin_cases x <;> rfl
  have hnat := α.naturality swap
  have hspec : α.app X idX = (exercise_1_3_31b_ord.map swap : _ → _) (α.app X idX) := by
    have h1 := congrFun (congrArg (fun m :
      exercise_1_3_31b_sym.obj X ⟶ exercise_1_3_31b_ord.obj X =>
      (m : Equiv.Perm (ULift.{u} (Fin 2)) → LinearOrder (ULift.{u} (Fin 2)))) hnat) idX
    change α.app X ((exercise_1_3_31b_sym.map swap : _ → _) idX) =
      (exercise_1_3_31b_ord.map swap : _ → _) (α.app X idX) at h1
    rw [hswap] at h1
    exact h1
  let L : LinearOrder (ULift.{u} (Fin 2)) := α.app X idX
  let z0 : ULift.{u} (Fin 2) := ⟨0⟩
  let z1 : ULift.{u} (Fin 2) := ⟨1⟩
  have hcomm : @LE.le _ L.toLE z0 z1 ↔ @LE.le _ L.toLE z1 z0 := by
    have h1 : @LE.le _ L.toLE z0 z1 ↔ @LE.le _ (exercise_1_3_31b_ord.map swap L).toLE z0 z1 :=
      (congrArg (fun K : LinearOrder (ULift (Fin 2)) => @LE.le _ K.toLE z0 z1) hspec).to_iff
    have h2 : @LE.le _ (exercise_1_3_31b_ord.map swap L).toLE z0 z1 ↔
        @LE.le _ L.toLE (swap.symm z0) (swap.symm z1) := Iff.rfl
    have hs0 : swap.symm z0 = z1 := rfl
    have hs1 : swap.symm z1 = z0 := rfl
    rw [h1, h2, hs0, hs1]
  have h_le01 : @LE.le _ L.toLE z0 z1 := by
    rcases L.le_total z0 z1 with h | h
    · exact h
    · exact hcomm.mpr h
  have h_le10 : @LE.le _ L.toLE z1 z0 := hcomm.mp h_le01
  have hz : z0 = z1 := L.le_antisymm z0 z1 h_le01 h_le10
  have hne : (0 : Fin 2) ≠ 1 := by decide
  exact hne (congrArg ULift.down hz)

noncomputable def linearOrderEquivFin (α : Type u) [Fintype α] [DecidableEq α] :
    LinearOrder α ≃ (α ≃ Fin (Fintype.card α)) where
  toFun L := (@Fintype.orderIsoFinOfCardEq α L _ _ rfl).symm.toEquiv
  invFun e := LinearOrder.lift' e e.injective
  left_inv L := by
    apply LinearOrder.ext
    intro x y
    exact (@Fintype.orderIsoFinOfCardEq α L _ _ rfl).symm.map_rel_iff
  right_inv e := by
    apply Equiv.ext
    intro x
    letI : LinearOrder α := LinearOrder.lift' e e.injective
    let e_iso : α ≃o Fin (Fintype.card α) := ⟨e, fun {a b} => Iff.rfl⟩
    have hcomp : e_iso.symm.trans (Fintype.orderIsoFinOfCardEq α rfl).symm =
        OrderIso.refl _ := by
      ext i
      exact Fin.coe_orderIso_apply _ i
    have hx : (e_iso.symm.trans (Fintype.orderIsoFinOfCardEq α rfl).symm) (e x) = e x := by
      rw [hcomp]
      rfl
    change (Fintype.orderIsoFinOfCardEq α rfl).symm (e.symm (e x)) = e x at hx
    rw [e.symm_apply_apply] at hx
    exact hx

noncomputable instance exercise_1_3_31d_ord_fintype (X : FinBijSet) :
    Fintype (LinearOrder X.carrier) :=
  Fintype.ofEquiv (X.carrier ≃ Fin (Fintype.card X.carrier)) (linearOrderEquivFin X.carrier).symm

open Classical in
theorem exercise_1_3_31d_ord_card (X : FinBijSet) :
    Fintype.card (LinearOrder X.carrier) = (Fintype.card X.carrier).factorial := by
  have h := @Fintype.card_congr (LinearOrder X.carrier) (X.carrier ≃ Fin (Fintype.card X.carrier))
    (exercise_1_3_31d_ord_fintype X) inferInstance (linearOrderEquivFin X.carrier)
  rw [h, Fintype.card_equiv (Fintype.equivFin X.carrier)]

theorem exercise_1_3_31_conclusion (X : FinBijSet) :
    Nonempty (Equiv.Perm X.carrier ≃ LinearOrder X.carrier) := by
  have h1 : Fintype.card (Equiv.Perm X.carrier) = (Fintype.card X.carrier).factorial :=
    Fintype.card_perm
  have h2 : Fintype.card (LinearOrder X.carrier) = (Fintype.card X.carrier).factorial :=
    exercise_1_3_31d_ord_card X
  exact ⟨Fintype.equivOfCardEq (h1.trans h2.symm)⟩

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
