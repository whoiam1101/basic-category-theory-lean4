-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Products.Bifunctor
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.ContinuousMap.Algebra

namespace Functors

universe u v

open CategoryTheory

abbrev example_1_2_3a : GrpCat.{u} ⥤ Type u := forget GrpCat

abbrev example_1_2_3b_ring : RingCat.{u} ⥤ Type u := forget RingCat

abbrev example_1_2_3b_vect (k : Type u) [Field k] : ModuleCat.{u} k ⥤ Type u :=
  forget (ModuleCat k)

abbrev example_1_2_3c : RingCat.{u} ⥤ AddCommGrpCat.{u} := forget₂ RingCat AddCommGrpCat

def example_1_2_3c_mon : RingCat.{u} ⥤ MonCat.{u} where
  obj R := MonCat.of R
  map f := MonCat.ofHom f.hom.toMonoidHom
  map_id R := by ext x; rfl
  map_comp f g := by ext x; rfl

def example_1_2_3d : AddCommGrpCat.{u} ⥤ GrpCat.{u} where
  obj A := GrpCat.of (Multiplicative A)
  map {A B} f := GrpCat.ofHom
    { toFun := fun a => Multiplicative.ofAdd (f.hom a)
      map_one' := by
        change Multiplicative.ofAdd (f.hom (0 : ↑A)) = 1
        simp [ZeroHomClass.map_zero, ofAdd_zero]
      map_mul' := by
        intro a b
        change Multiplicative.ofAdd (f.hom (a * b)) = Multiplicative.ofAdd (f.hom a) *
          Multiplicative.ofAdd (f.hom b)
        rw [← ofAdd_add]
        congr 1
        exact AddHomClass.map_add (f.hom) a b }
  map_id A := by
    apply GrpCat.ext
    intro x
    change Multiplicative.ofAdd ((𝟙 A : ↑A → ↑A) x) = x
    simp
    rfl
  map_comp f g := by
    apply GrpCat.ext
    intro x
    change Multiplicative.ofAdd ((g.hom.comp f.hom) x) = Multiplicative.ofAdd (g.hom (f.hom x))
    rfl

noncomputable abbrev example_1_2_4a : Type u ⥤ GrpCat.{u} := GrpCat.free

noncomputable abbrev example_1_2_4b : Type u ⥤ CommRingCat.{u} := CommRingCat.free

noncomputable abbrev example_1_2_4c (k : Type u) [Ring k] : Type u ⥤ ModuleCat.{u} k :=
  ModuleCat.free k

noncomputable def example_1_2_6_p1 : MvPolynomial (Fin 3) ℤ :=
  MvPolynomial.C 2 * MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - MvPolynomial.C 3 *
    MvPolynomial.X 2 ^ 2 - 1

noncomputable def example_1_2_6_p2 : MvPolynomial (Fin 3) ℤ :=
  MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0 - MvPolynomial.X 1 ^ 2

noncomputable def example_1_2_6 : CommRingCat.{u} ⥤ Type u where
  obj A :=
    { r : Fin 3 → A //
      MvPolynomial.aeval r example_1_2_6_p1 = 0 ∧ MvPolynomial.aeval r example_1_2_6_p2 = 0 }
  map {A B} f :=
    TypeCat.ofHom (fun r : { s : Fin 3 → A // MvPolynomial.aeval s example_1_2_6_p1 = 0 ∧
        MvPolynomial.aeval s example_1_2_6_p2 = 0 } =>
      ⟨f ∘ r, by
        rcases r with ⟨r, ⟨hr₁, hr₂⟩⟩
        constructor
        · have h : MvPolynomial.aeval (fun i : Fin 3 => (f.hom.toIntAlgHom) (r i))
              example_1_2_6_p1 = 0 := by
            rw [← MvPolynomial.comp_aeval_apply r (f.hom.toIntAlgHom) example_1_2_6_p1, hr₁]
            simp
          simpa using h
        · have h : MvPolynomial.aeval (fun i : Fin 3 => (f.hom.toIntAlgHom) (r i))
              example_1_2_6_p2 = 0 := by
            rw [← MvPolynomial.comp_aeval_apply r (f.hom.toIntAlgHom) example_1_2_6_p2, hr₂]
            simp
          simpa using h⟩)
  map_id A := by
    ext r x
    rfl
  map_comp {A B C} f g := by
    ext r x
    rfl

abbrev example_1_2_7 (G H : Type u) [Monoid G] [Monoid H] :
    (G →* H) ≃ (SingleObj G ⥤ SingleObj H) :=
  SingleObj.mapHom G H

abbrev example_1_2_8 (M : Type u) [Monoid M] :
    Action (Type u) M ≌ SingleObj M ⥤ Type u :=
  Action.functorCategoryEquivalence (Type u) M

abbrev def_1_2_10 (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] := Cᵒᵖ ⥤ D

def example_1_2_12 (k : Type u) [Field k] : (ModuleCat.{u} k)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj V := ModuleCat.of k (Module.Dual k V.unop)
  map {V W} f := ModuleCat.ofHom f.unop.hom.dualMap
  map_id V := by
    change ModuleCat.ofHom ((LinearMap.id : V.unop →ₗ[k] V.unop).dualMap) = 𝟙 _
    rw [LinearMap.dualMap_id]
    rfl
  map_comp {V W Z} f g := by
    change ModuleCat.ofHom ((f.unop.hom.comp g.unop.hom).dualMap) =
      ModuleCat.ofHom ((g.unop.hom.dualMap).comp (f.unop.hom.dualMap))
    rw [← LinearMap.dualMap_comp_dualMap (f := g.unop.hom) (g := f.unop.hom)]

def example_1_2_14_op_equiv (M : Type u) [Monoid M] : (SingleObj M)ᵒᵖ ≌ SingleObj Mᵐᵒᵖ where
  functor :=
    { obj := fun _ => SingleObj.star Mᵐᵒᵖ
      map := fun f => MulOpposite.op (Quiver.Hom.unop f)
      map_id := by intro X; rfl
      map_comp := by intro X Y Z f g; rfl }
  inverse :=
    { obj := fun _ => Opposite.op (SingleObj.star M)
      map := fun f => Quiver.Hom.op (MulOpposite.unop f)
      map_id := by intro X; rfl
      map_comp := by intro X Y Z f g; rfl }
  unitIso := NatIso.ofComponents
      (fun X => { hom := Opposite.op (1 : M),
                  inv := Opposite.op (1 : M),
                  hom_inv_id := by
                    apply Quiver.Hom.unop_inj
                    simp only [unop_comp, unop_id]
                    change (1 : M) * 1 = 1
                    simp
                  inv_hom_id := by
                    apply Quiver.Hom.unop_inj
                    simp only [unop_comp, unop_id]
                    change (1 : M) * 1 = 1
                    simp })
      (by
        intro X Y f
        apply Quiver.Hom.unop_inj
        simp only [unop_comp]
        change f.unop * 1 = 1 * f.unop
        rw [mul_one, one_mul])
  counitIso := NatIso.ofComponents
      (fun X => { hom := (1 : Mᵐᵒᵖ),
                  inv := (1 : Mᵐᵒᵖ),
                  hom_inv_id := by
                    change (1 : Mᵐᵒᵖ) * 1 = 1
                    simp
                  inv_hom_id := by
                    change (1 : Mᵐᵒᵖ) * 1 = 1
                    simp })
      (by
        intro X Y f
        exact (Category.comp_id f).trans (Category.id_comp f).symm)
  functor_unitIso_comp := by
    intro X
    change (1 : Mᵐᵒᵖ) * 1 = 1
    simp

def example_1_2_14 (M : Type u) [Monoid M] :
    (SingleObj M)ᵒᵖ ⥤ Type u ≌ Action (Type u) Mᵐᵒᵖ :=
  (Equivalence.congrLeft (example_1_2_14_op_equiv M)).trans
    (Action.functorCategoryEquivalence (Type u) Mᵐᵒᵖ).symm

abbrev def_1_2_15 (A : Type u) [Category.{v} A] := Aᵒᵖ ⥤ Type u

structure def_1_2_18 (C : Type u) [Category.{v} C] where
  obj : C → Prop
  hom : {A B : C} → obj A → obj B → (A ⟶ B) → Prop
  id_mem : ∀ {A : C} (hA : obj A), hom hA hA (𝟙 A)
  comp_mem : ∀ {A B C : C} (hA : obj A) (hB : obj B) (hC : obj C) {f : A ⟶ B} {g : B ⟶ C},
    hom hA hB f → hom hB hC g → hom hA hC (f ≫ g)

def def_1_2_18_full {C : Type u} [Category.{v} C] (S : def_1_2_18 C) : Prop :=
  ∀ {A B : C} (hA : S.obj A) (hB : S.obj B) (f : A ⟶ B), S.hom hA hB f

instance def_1_2_18.category {C : Type u} [Category.{v} C] (S : def_1_2_18 C) :
    Category {A : C // S.obj A} where
  Hom X Y := { f : X.1 ⟶ Y.1 // S.hom X.2 Y.2 f }
  id X := ⟨𝟙 X.1, S.id_mem X.2⟩
  comp {X Y Z} f g := ⟨f.1 ≫ g.1, S.comp_mem X.2 Y.2 Z.2 f.2 g.2⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

def exercise_1_2_21 {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) {A A' : C}
    (h : A ≅ A') : F.obj A ≅ F.obj A' :=
  F.mapIso h

theorem exercise_1_2_22_obj_map {A B : Type u} [Preorder A] [Preorder B] (F : A ⥤ B) :
    ∀ a a' : A, a ≤ a' → F.obj a ≤ F.obj a' := by
  intro a a' h
  have hhom : a ⟶ a' := homOfLE h
  have hmap : F.obj a ⟶ F.obj a' := F.map hhom
  exact leOfHom hmap

def exercise_1_2_22_map_obj {A B : Type u} [Preorder A] [Preorder B] (f : A → B)
    (hf : ∀ a a', a ≤ a' → f a ≤ f a') : A ⥤ B where
  obj := f
  map {a a'} h := homOfLE (hf a a' (leOfHom h))
  map_id _ := rfl
  map_comp {_ _ _} _ _ := rfl

def exercise_1_2_23 (G : Type u) [Group G] : Cat.of (SingleObj G) ≅ Cat.of (SingleObj Gᵐᵒᵖ) where
  hom := (SingleObj.mapHom G Gᵐᵒᵖ (MulEquiv.inv' G).toMonoidHom).toCatHom
  inv := (SingleObj.mapHom Gᵐᵒᵖ G (MulEquiv.inv' G).symm.toMonoidHom).toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    change SingleObj.mapHom G Gᵐᵒᵖ (MulEquiv.inv' G).toMonoidHom ⋙
        SingleObj.mapHom Gᵐᵒᵖ G (MulEquiv.inv' G).symm.toMonoidHom = 𝟭 (SingleObj G)
    rw [← SingleObj.mapHom_comp]
    rw [← SingleObj.mapHom_id]
    congr 1
    ext x
    exact MulEquiv.symm_apply_apply (MulEquiv.inv' G) x
  inv_hom_id := by
    apply Cat.Hom.ext
    change SingleObj.mapHom Gᵐᵒᵖ G (MulEquiv.inv' G).symm.toMonoidHom ⋙
        SingleObj.mapHom G Gᵐᵒᵖ (MulEquiv.inv' G).toMonoidHom = 𝟭 (SingleObj Gᵐᵒᵖ)
    rw [← SingleObj.mapHom_comp]
    rw [← SingleObj.mapHom_id]
    congr 1
    ext x
    exact MulEquiv.apply_symm_apply (MulEquiv.inv' G) x

lemma exercise_1_2_24_center_s3 : Subgroup.center (Equiv.Perm (Fin 3)) = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hx' : ∀ y : Equiv.Perm (Fin 3), y * x = x * y := Subgroup.mem_center_iff.mp hx
    let t : Equiv.Perm (Fin 3) := Equiv.swap (0 : Fin 3) 1
    let s : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2
    have ht : x * t = t * x := (hx' t).symm
    have hs : x * s = s * x := (hx' s).symm
    apply Subgroup.mem_bot.mpr
    have hx1_of : x 1 = t (x 0) := by
      have h := congrArg (fun f : Equiv.Perm (Fin 3) => f 0) ht
      dsimp [t] at h
      exact h
    have hx2_of : x 2 = s (x 1) := by
      have h := congrArg (fun f : Equiv.Perm (Fin 3) => f 1) hs
      dsimp [s] at h
      exact h
    have hx0_cases : (x 0).val = 0 ∨ (x 0).val = 1 ∨ (x 0).val = 2 := by
      have hlt : (x 0).val < 3 := (x 0).isLt
      interval_cases (x 0).val <;> simp
    rcases hx0_cases with h0 | h1 | h2
    · have hx0 : x 0 = 0 := Fin.ext h0
      have hx1 : x 1 = 1 := by
        rw [hx1_of, hx0]
        rfl
      have hx2 : x 2 = 2 := by
        rw [hx2_of, hx1]
        rfl
      ext i
      fin_cases i <;> simp [hx0, hx1, hx2]
    · have hx0 : x 0 = 1 := Fin.ext h1
      have hx1 : x 1 = 0 := by
        rw [hx1_of, hx0]
        rfl
      have hx2 : x 2 = 0 := by
        rw [hx2_of, hx1]
        rfl
      exfalso
      exact (by decide : (1 : Fin 3) ≠ 2) (x.injective (hx1.trans hx2.symm))
    · have hx0 : x 0 = 2 := Fin.ext h2
      have hx1 : x 1 = 2 := by
        rw [hx1_of, hx0]
        rfl
      exfalso
      exact (by decide : (0 : Fin 3) ≠ 1) (x.injective (hx0.trans hx1.symm))
  · exact bot_le

lemma exercise_1_2_24_center_ulift_bot (G : Type) [Group G]
    (h : Subgroup.center G = ⊥) : Subgroup.center (ULift.{u} G) = ⊥ := by
  apply le_antisymm
  · intro x hx
    rcases x with ⟨a⟩
    have hb : ∀ g : ULift.{u} G, g * ULift.up a = ULift.up a * g := Subgroup.mem_center_iff.mp hx
    have ha : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro b
      simpa using congrArg ULift.down (hb (ULift.up b))
    have ha1 : a = 1 := Subgroup.mem_bot.mp (by simpa [h] using ha)
    exact Subgroup.mem_bot.mpr (by rw [ha1]; rfl)
  · exact bot_le

def exercise_1_2_24_units_to_c2 : ℤˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (if u = 1 then 0 else 1)
  map_one' := rfl
  map_mul' := by
    intro u v
    by_cases hu : u = 1 <;> by_cases hv : v = 1
    · simp [hu, hv]
    · simp [hu, hv]
    · simp [hu, hv]
    · have hu' : u = -1 := (Int.units_eq_one_or u).resolve_left hu
      have hv' : v = -1 := (Int.units_eq_one_or v).resolve_left hv
      simp only [hu', hv']
      rw [← ofAdd_add]
      norm_num
      rw [show (2 : ZMod 2) = 0 by decide]
      simp [ofAdd_zero]

def exercise_1_2_24_sign : Equiv.Perm (Fin 3) →* Multiplicative (ZMod 2) :=
  exercise_1_2_24_units_to_c2.comp Equiv.Perm.sign

lemma exercise_1_2_24_sign_swap :
    exercise_1_2_24_sign (Equiv.swap (0 : Fin 3) 1) = Multiplicative.ofAdd 1 := by
  have hswap : (0 : Fin 3) ≠ 1 := by decide
  simp [exercise_1_2_24_sign, exercise_1_2_24_units_to_c2, Equiv.Perm.sign_swap hswap]

def exercise_1_2_24_embed : Multiplicative (ZMod 2) →* Equiv.Perm (Fin 3) where
  toFun c := if c = 1 then 1 else Equiv.swap (0 : Fin 3) 1
  map_one' := by simp
  map_mul' := by
    intro c d
    fin_cases c <;> fin_cases d <;> decide

theorem exercise_1_2_24 :
    ¬ ∃ F : GrpCat.{u} ⥤ GrpCat.{u},
      ∀ G : GrpCat.{u}, Nonempty (F.obj G ≅ GrpCat.of (Subgroup.center G)) := by
  rintro ⟨F, hF⟩
  let S₃ : GrpCat.{u} := GrpCat.of (ULift.{u} (Equiv.Perm (Fin 3)))
  let C₂ : GrpCat.{u} := GrpCat.of (ULift.{u} (Multiplicative (ZMod 2)))
  have htrivS3 : ∀ x : F.obj S₃, x = 1 := by
    rcases hF S₃ with ⟨φ⟩
    intro x
    have hc : Subgroup.center (ULift.{u} (Equiv.Perm (Fin 3))) = ⊥ :=
      exercise_1_2_24_center_ulift_bot (Equiv.Perm (Fin 3)) exercise_1_2_24_center_s3
    have hx1 : φ.hom x = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp (by simpa [S₃, hc] using (φ.hom x).2)
    have hx' : φ.inv.hom (φ.hom x) = 1 := by
      rw [hx1]
      exact φ.inv.hom.map_one
    have hx'' : x = φ.inv.hom (φ.hom x) := (ConcreteCategory.congr_hom φ.hom_inv_id x).symm
    exact hx''.trans hx'
  let p₀ : Equiv.Perm (Fin 3) →* Multiplicative (ZMod 2) := exercise_1_2_24_sign
  let t₀ : Multiplicative (ZMod 2) →* Equiv.Perm (Fin 3) := exercise_1_2_24_embed
  let p : ULift.{u} (Equiv.Perm (Fin 3)) →* ULift.{u} (Multiplicative (ZMod 2)) :=
    { toFun := fun x => ULift.up (p₀ x.down)
      map_one' := by apply ULift.ext; simp [p₀]
      map_mul' := by intro x y; apply ULift.ext; simp }
  let t : ULift.{u} (Multiplicative (ZMod 2)) →* ULift.{u} (Equiv.Perm (Fin 3)) :=
    { toFun := fun c => ULift.up (t₀ c.down)
      map_one' := by apply ULift.ext; simp [t₀]
      map_mul' := by intro c d; apply ULift.ext; simp }
  have hpt : p.comp t = MonoidHom.id _ := by
    ext x
    rcases x with ⟨c⟩
    fin_cases c
    · simp only [p, t, p₀, t₀]
      exact Multiplicative.ext_iff.mp rfl
    · simp only [p, t, p₀, t₀]
      exact Multiplicative.ext_iff.mp rfl
  have hptG : (GrpCat.ofHom t) ≫ (GrpCat.ofHom p) = 𝟙 C₂ := by
    ext x
    change Multiplicative.toAdd ((p.comp t) x).down =
      Multiplicative.toAdd ((GrpCat.Hom.hom (𝟙 C₂)) x).down
    simpa [GrpCat.coe_id] using congrFun (congrArg (fun f : ULift.{u} (Multiplicative (ZMod 2)) →*
        ULift.{u} (Multiplicative (ZMod 2)) => (f : _ → _)) hpt) x
  have htriv_p : ∀ x : F.obj S₃, (F.map (GrpCat.ofHom p)) x = 1 := by
    intro x
    rw [htrivS3 x]
    exact (F.map (GrpCat.ofHom p)).hom.map_one
  have htriv_t : ∀ x : F.obj C₂, (F.map (GrpCat.ofHom t)) x = 1 := by
    intro x
    exact htrivS3 (F.map (GrpCat.ofHom t) x)
  have htp_triv : ∀ x : F.obj C₂, (F.map (GrpCat.ofHom t) ≫ F.map (GrpCat.ofHom p)) x = 1 := by
    intro x
    calc
      (F.map (GrpCat.ofHom t) ≫ F.map (GrpCat.ofHom p)) x =
          F.map (GrpCat.ofHom p) (F.map (GrpCat.ofHom t) x) := by
        simp
      _ = 1 := htriv_p (F.map (GrpCat.ofHom t) x)
  have htp_id : F.map (GrpCat.ofHom t) ≫ F.map (GrpCat.ofHom p) = 𝟙 (F.obj C₂) := by
    rw [← F.map_comp]
    rw [hptG]
    exact F.map_id C₂
  have hnontriv : ∃ z : F.obj C₂, z ≠ 1 := by
    rcases hF C₂ with ⟨φ⟩
    have hc : Subgroup.center ↑C₂ = ⊤ := by
      simpa [C₂] using
        (CommGroup.center_eq_top : Subgroup.center (ULift.{u} (Multiplicative (ZMod 2))) = ⊤)
    let w : ↥(Subgroup.center ↑C₂) :=
      ⟨ULift.up (Multiplicative.ofAdd (1 : ZMod 2)), by rw [hc]; simp⟩
    have hw_ne : w ≠ 1 := by
      intro h
      have hd : Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
        simpa [w] using congrArg (fun x : ↥(Subgroup.center ↑C₂) => x.1.down) h
      exact (by decide : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1) hd
    refine ⟨φ.inv.hom w, ?_⟩
    intro hz
    apply hw_ne
    have hw_eq : w = φ.hom.hom (φ.inv.hom w) := (ConcreteCategory.congr_hom φ.inv_hom_id w).symm
    rw [hw_eq, hz, map_one]
  rcases hnontriv with ⟨z, hz⟩
  have hz1 : z = 1 := by
    have hz' : (F.map (GrpCat.ofHom t) ≫ F.map (GrpCat.ofHom p)) z = z := by
      simpa using (ConcreteCategory.congr_hom htp_id z)
    exact hz'.symm.trans (htp_triv z)
  exact hz hz1

def exercise_1_2_25a_FA {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A × B ⥤ C) (a : A) : B ⥤ C where
  obj b := F.obj (a, b)
  map {b b'} g := F.map (Prod.mkHom (𝟙 a) g)
  map_id b := F.map_id (a, b)
  map_comp {b b' b''} g h := by
    rw [← F.map_comp (Prod.mkHom (𝟙 a) g) (Prod.mkHom (𝟙 a) h)]; simp

def exercise_1_2_25a_F_B {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A × B ⥤ C) (b : B) : A ⥤ C where
  obj a := F.obj (a, b)
  map {a a'} f := F.map (Prod.mkHom f (𝟙 b))
  map_id a := F.map_id (a, b)
  map_comp {a a' a''} f f' := by
    rw [← F.map_comp (Prod.mkHom f (𝟙 b)) (Prod.mkHom f' (𝟙 b))]; simp

theorem exercise_1_2_25b_i {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A × B ⥤ C) (a : A) (b : B) :
    (exercise_1_2_25a_FA F a).obj b = (exercise_1_2_25a_F_B F b).obj a := rfl

theorem exercise_1_2_25b_ii {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (F : A × B ⥤ C) {a a' : A} {b b' : B} (f : a ⟶ a') (g : b ⟶ b') :
    (exercise_1_2_25a_F_B F b).map f ≫ (exercise_1_2_25a_FA F a').map g =
    (exercise_1_2_25a_FA F a).map g ≫ (exercise_1_2_25a_F_B F b').map f := by
  dsimp [exercise_1_2_25a_FA, exercise_1_2_25a_F_B]
  rw [← F.map_comp, ← F.map_comp]
  simp

lemma exercise_1_2_25c_square {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (FA : A → B ⥤ C) (FB : B → A ⥤ C)
    (h_obj : ∀ a b, (FA a).obj b = (FB b).obj a)
    (h_comm : ∀ {a a'} {b b'} (f : a ⟶ a') (g : b ⟶ b'),
      eqToHom (h_obj a b) ≫ (FB b).map f ≫ eqToHom (h_obj a' b).symm ≫ (FA a').map g =
        (FA a).map g ≫ eqToHom (h_obj a b') ≫ (FB b').map f ≫ eqToHom (h_obj a' b').symm)
    {a a'} {b b'} (f : a ⟶ a') (g : b ⟶ b') :
    (FB b).map f ≫ eqToHom (h_obj a' b).symm ≫ (FA a').map g =
      eqToHom (h_obj a b).symm ≫ (FA a).map g ≫ eqToHom (h_obj a b') ≫ (FB b').map f ≫
        eqToHom (h_obj a' b').symm := by
  calc
    (FB b).map f ≫ eqToHom (h_obj a' b).symm ≫ (FA a').map g =
        eqToHom (h_obj a b).symm ≫
          (eqToHom (h_obj a b) ≫ (FB b).map f ≫ eqToHom (h_obj a' b).symm ≫ (FA a').map g) := by
      simp
    _ = eqToHom (h_obj a b).symm ≫
        ((FA a).map g ≫ eqToHom (h_obj a b') ≫ (FB b').map f ≫ eqToHom (h_obj a' b').symm) := by
      rw [h_comm f g]
    _ = eqToHom (h_obj a b).symm ≫ (FA a).map g ≫ eqToHom (h_obj a b') ≫ (FB b').map f ≫
        eqToHom (h_obj a' b').symm := by
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem exercise_1_2_25c_map_transport {A B C : Type u} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] (F' : A × B ⥤ C) (G1 : A ⥤ C) (G2 : B ⥤ C)
    {b : B} {a' : A}
    (eFB : exercise_1_2_25a_F_B F' b = G1) (eFA : exercise_1_2_25a_FA F' a' = G2)
    {a : A} {b' : B} (f : a ⟶ a') (g : b ⟶ b') :
    (exercise_1_2_25a_F_B F' b).map f ≫ (exercise_1_2_25a_FA F' a').map g =
      eqToHom (congrArg (fun G : A ⥤ C => G.obj a) eFB) ≫ G1.map f ≫
        eqToHom ((congrArg (fun G : A ⥤ C => G.obj a') eFB).symm.trans
          (congrArg (fun G : B ⥤ C => G.obj b) eFA)) ≫ G2.map g ≫
        eqToHom (congrArg (fun G : B ⥤ C => G.obj b') eFA).symm := by
  cases eFB
  cases eFA
  simp

set_option backward.isDefEq.respectTransparency false in
theorem exercise_1_2_25c {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
    (FA : A → B ⥤ C) (FB : B → A ⥤ C)
    (h_obj : ∀ a b, (FA a).obj b = (FB b).obj a)
    (h_comm : ∀ {a a'} {b b'} (f : a ⟶ a') (g : b ⟶ b'),
      eqToHom (h_obj a b) ≫ (FB b).map f ≫ eqToHom (h_obj a' b).symm ≫ (FA a').map g =
        (FA a).map g ≫ eqToHom (h_obj a b') ≫ (FB b').map f ≫ eqToHom (h_obj a' b').symm) :
    ∃! F : A × B ⥤ C,
      (∀ a, exercise_1_2_25a_FA F a = FA a) ∧ (∀ b, exercise_1_2_25a_F_B F b = FB b) := by
  let F : A × B ⥤ C :=
    { obj := fun X => (FA X.1).obj X.2
      map := fun {X Y} f =>
        eqToHom (h_obj X.1 X.2) ≫ (FB X.2).map f.1 ≫ eqToHom (h_obj Y.1 X.2).symm ≫
          (FA Y.1).map f.2
      map_id := by
        rintro ⟨a, b⟩
        simp
      map_comp := by
        intro X Y Z f g
        rcases X with ⟨a, b⟩; rcases Y with ⟨a', b'⟩; rcases Z with ⟨a'', b''⟩
        change eqToHom (h_obj a b) ≫ (FB b).map (f.1 ≫ g.1) ≫ eqToHom (h_obj a'' b).symm ≫
            (FA a'').map (f.2 ≫ g.2) =
          (eqToHom (h_obj a b) ≫ (FB b).map f.1 ≫ eqToHom (h_obj a' b).symm ≫
              (FA a').map f.2) ≫
            (eqToHom (h_obj a' b') ≫ (FB b').map g.1 ≫ eqToHom (h_obj a'' b').symm ≫
              (FA a'').map g.2)
        calc
          eqToHom (h_obj a b) ≫ (FB b).map (f.1 ≫ g.1) ≫ eqToHom (h_obj a'' b).symm ≫
              (FA a'').map (f.2 ≫ g.2)
              = eqToHom (h_obj a b) ≫ (FB b).map f.1 ≫
                  ((FB b).map g.1 ≫ eqToHom (h_obj a'' b).symm ≫ (FA a'').map f.2) ≫
                    (FA a'').map g.2 := by
                simp [Functor.map_comp]
          _ = (eqToHom (h_obj a b) ≫ (FB b).map f.1 ≫ eqToHom (h_obj a' b).symm ≫
                  (FA a').map f.2) ≫
                (eqToHom (h_obj a' b') ≫ (FB b').map g.1 ≫ eqToHom (h_obj a'' b').symm ≫
                  (FA a'').map g.2) := by
              rw [exercise_1_2_25c_square FA FB h_obj h_comm (g.1) (f.2)]
              simp }
  refine ⟨F, ?_, ?_⟩
  · constructor
    · intro a
      apply CategoryTheory.Functor.ext
      · intro b b' g
        simp [F, exercise_1_2_25a_FA]
      · intro b
        rfl
    · intro b
      apply CategoryTheory.Functor.ext
      · intro a a' f
        simp [F, exercise_1_2_25a_F_B]
      · intro a
        exact h_obj a b
  · intro F' hF'
    rcases hF' with ⟨hFA', hFB'⟩
    apply CategoryTheory.Functor.ext
    · intro X Y f
      rcases X with ⟨a, b⟩; rcases Y with ⟨a', b'⟩
      change F'.map (f.1, f.2) = eqToHom (congrArg (fun G : B ⥤ C => G.obj b) (hFA' a)) ≫
        F.map (f.1, f.2) ≫ eqToHom (congrArg (fun G : B ⥤ C => G.obj b') (hFA' a')).symm
      rw [show (f.1, f.2) = Prod.mkHom f.1 (𝟙 b) ≫ Prod.mkHom (𝟙 a') f.2 by simp]
      simp only [F'.map_comp, F.map_comp]
      change (exercise_1_2_25a_F_B F' b).map f.1 ≫ (exercise_1_2_25a_FA F' a').map f.2 =
        eqToHom (congrArg (fun G : B ⥤ C => G.obj b) (hFA' a)) ≫
          (F.map (Prod.mkHom f.1 (𝟙 b)) ≫ F.map (Prod.mkHom (𝟙 a') f.2)) ≫
          eqToHom (congrArg (fun G : B ⥤ C => G.obj b') (hFA' a')).symm
      rw [exercise_1_2_25c_map_transport F' (FB b) (FA a') (hFB' b) (hFA' a') f.1 f.2]
      simp only [F]
      simp
    · intro X
      rcases X with ⟨a, b⟩
      exact congrArg (fun G : B ⥤ C => G.obj b) (hFA' a)

noncomputable def exercise_1_2_26 : TopCatᵒᵖ ⥤ RingCat where
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

inductive exercise_1_2_27_A : Type
  | a | b
  deriving DecidableEq

instance : Category exercise_1_2_27_A where
  Hom X Y := ULift (PLift (X = Y))
  id X := ULift.up (PLift.up rfl)
  comp {X Y Z} f g := ULift.up (PLift.up (by
    rcases f with ⟨⟨rfl⟩⟩
    rcases g with ⟨⟨rfl⟩⟩
    rfl))

instance {X Y : exercise_1_2_27_A} : Subsingleton (X ⟶ Y) where
  allEq f g := by
    apply ULift.ext f g
    apply Subsingleton.elim

def exercise_1_2_27_F : exercise_1_2_27_A ⥤ PUnit where
  obj _ := PUnit.unit
  map {_ _} _ := 𝟙 PUnit.unit
  map_id _ := rfl
  map_comp {_ _ _} _ _ := by simp

theorem exercise_1_2_27_faithful : Functor.Faithful exercise_1_2_27_F := by
  refine ⟨fun {X Y} f g _ => Subsingleton.elim f g⟩

theorem exercise_1_2_27 : exercise_1_2_27_A.a ≠ exercise_1_2_27_A.b ∧
    exercise_1_2_27_F.map (𝟙 exercise_1_2_27_A.a) =
    exercise_1_2_27_F.map (𝟙 exercise_1_2_27_A.b) := by
  constructor
  · exact exercise_1_2_27_A.noConfusion
  · rfl

end Functors
