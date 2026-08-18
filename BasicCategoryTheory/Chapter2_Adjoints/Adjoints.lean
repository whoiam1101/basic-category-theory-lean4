-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Category.PartialFun
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Topology.Category.TopCat.Adjunctions

namespace Adjoints

universe u v u' v'

open CategoryTheory
open Limits

abbrev def_2_1_1 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) (G : D ⥤ C) := F ⊣ G

noncomputable abbrev example_2_1_3b (k : Type u) [Field k] :
    ModuleCat.free k ⊣ forget (ModuleCat.{u} k) :=
  ModuleCat.adj k

abbrev example_2_1_3c :
    GrpCat.free ⊣ forget GrpCat.{u} :=
  GrpCat.adj

abbrev example_2_1_3d :
    GrpCat.abelianize ⊣ forget₂ CommGrpCat GrpCat.{u} :=
  GrpCat.abelianizeAdj

inductive FreeGroupOnMonoid.Rel (M : Type u) [Monoid M] : FreeGroup M → Prop where
  | one : FreeGroupOnMonoid.Rel M (FreeGroup.of 1)
  | mul (x y : M) :
    FreeGroupOnMonoid.Rel M (FreeGroup.of (x * y) * (FreeGroup.of x * FreeGroup.of y)⁻¹)

def FreeGroupOnMonoid.rels (M : Type u) [Monoid M] : Set (FreeGroup M) :=
  setOf (FreeGroupOnMonoid.Rel M)

def FreeGroupOnMonoid (M : Type u) [Monoid M] : Type u :=
  PresentedGroup (FreeGroupOnMonoid.rels M)

instance (M : Type u) [Monoid M] : Group (FreeGroupOnMonoid M) :=
  inferInstanceAs (Group (PresentedGroup (FreeGroupOnMonoid.rels M)))

namespace FreeGroupOnMonoid

def of (M : Type u) [Monoid M] : M →* FreeGroupOnMonoid M where
  toFun x := PresentedGroup.of x
  map_one' := by
    dsimp [FreeGroupOnMonoid]
    exact PresentedGroup.one_of_mem Rel.one
  map_mul' x y := by
    dsimp [FreeGroupOnMonoid]
    exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Rel.mul x y)

theorem lift_rels_subset {M : Type u} [Monoid M] {G : Type u} [Group G] (f : M →* G) :
    ∀ r ∈ rels M, FreeGroup.lift (f : M → G) r = 1 := by
  intro r hr
  cases hr with
  | one =>
    simp only [FreeGroup.lift_apply_of, map_one]
  | mul x y =>
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, f.map_mul, mul_inv_cancel]

def lift {M : Type u} [Monoid M] {G : Type u} [Group G] (f : M →* G) : FreeGroupOnMonoid M →* G :=
  PresentedGroup.toGroup (lift_rels_subset f)

@[simp]
theorem lift_of {M : Type u} [Monoid M] {G : Type u} [Group G] (f : M →* G) (x : M) :
    lift f (of M x) = f x :=
  PresentedGroup.toGroup.of (lift_rels_subset f)

theorem lift_unique {M : Type u} [Monoid M] {G : Type u} [Group G] (f : M →* G)
    (g : FreeGroupOnMonoid M →* G) (h : ∀ x, g (of M x) = f x) : g = lift f := by
  apply PresentedGroup.ext
  intro x
  exact (h x).trans (lift_of f x).symm

end FreeGroupOnMonoid

def MonCat.freeGroup : MonCat.{u} ⥤ GrpCat.{u} where
  obj M := GrpCat.of (FreeGroupOnMonoid M)
  map {M N} f := GrpCat.ofHom (FreeGroupOnMonoid.lift ((FreeGroupOnMonoid.of N).comp f.hom))
  map_id M := by
    apply GrpCat.hom_ext
    rw [GrpCat.hom_ofHom]
    exact (FreeGroupOnMonoid.lift_unique (FreeGroupOnMonoid.of M) (MonoidHom.id _)
      (fun _ => rfl)).symm
  map_comp {M N P} f g := by
    apply GrpCat.hom_ext
    rw [GrpCat.hom_ofHom, GrpCat.hom_comp, GrpCat.hom_ofHom, GrpCat.hom_ofHom]
    apply (FreeGroupOnMonoid.lift_unique _ _ _).symm
    intro x
    simp only [MonoidHom.comp_apply, FreeGroupOnMonoid.lift_of, MonCat.hom_comp]

def MonCat.freeGroupAdj : MonCat.freeGroup.{u} ⊣ forget₂ GrpCat.{u} MonCat.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M G =>
        { toFun := fun f => MonCat.ofHom (f.hom.comp (FreeGroupOnMonoid.of M))
          invFun := fun f => GrpCat.ofHom (FreeGroupOnMonoid.lift (G := G) f.hom)
          left_inv := fun f => by
            apply GrpCat.hom_ext
            rw [GrpCat.hom_ofHom]
            exact (FreeGroupOnMonoid.lift_unique _ _ (fun _ => rfl)).symm
          right_inv := fun f => by
            apply MonCat.hom_ext
            rw [MonCat.hom_ofHom]
            ext x
            exact FreeGroupOnMonoid.lift_of (G := G) f.hom x }
      homEquiv_naturality_left_symm := by
        intro M N G f g
        apply GrpCat.hom_ext
        apply (FreeGroupOnMonoid.lift_unique _ _ _).symm
        intro x
        change (GrpCat.Hom.hom
          (GrpCat.ofHom (FreeGroupOnMonoid.lift ((FreeGroupOnMonoid.of N).comp f.hom)) ≫
            GrpCat.ofHom (FreeGroupOnMonoid.lift (G := G) g.hom))) (FreeGroupOnMonoid.of M x) =
          (f ≫ g).hom x
        rw [GrpCat.hom_comp, GrpCat.hom_ofHom, GrpCat.hom_ofHom]
        simp only [MonoidHom.comp_apply, FreeGroupOnMonoid.lift_of, MonCat.hom_comp] }

instance : MonCat.freeGroup.{u}.IsLeftAdjoint :=
  ⟨_, ⟨MonCat.freeGroupAdj⟩⟩

instance : (forget₂ GrpCat.{u} MonCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨MonCat.freeGroupAdj⟩⟩

abbrev example_2_1_3d_F_U :
    MonCat.freeGroup.{u} ⊣ forget₂ GrpCat.{u} MonCat.{u} :=
  MonCat.freeGroupAdj

abbrev example_2_1_3e_F_U :
    MonCat.freeGroup.{u} ⊣ forget₂ GrpCat.{u} MonCat.{u} :=
  MonCat.freeGroupAdj

abbrev example_2_1_3e_U_R :
    forget₂ GrpCat MonCat.{u} ⊣ MonCat.units :=
  GrpCat.forget₂MonAdj

abbrev example_2_1_5_D_U :
    TopCat.discrete ⊣ forget TopCat.{u} :=
  TopCat.adj₁

abbrev example_2_1_5_U_I :
    forget TopCat.{u} ⊣ TopCat.trivial :=
  TopCat.adj₂

noncomputable def example_2_1_6 (B : Type u) : MonoidalCategory.tensorLeft B ⊣ ihom B :=
  ihom.adjunction B

abbrev def_2_1_7_initial {C : Type u} [Category.{v} C] (I : C) := IsInitial I

abbrev def_2_1_7_terminal {C : Type u} [Category.{v} C] (T : C) := IsTerminal T

theorem lemma_2_1_8_initial {C : Type u} [Category.{v} C] {I I' : C}
    (hI : IsInitial I) (hI' : IsInitial I') : ∃! e : I ≅ I', e = e := by
  refine ⟨hI.uniqueUpToIso hI', rfl, fun e _ => ?_⟩
  apply Iso.ext
  exact hI.hom_ext e.hom (hI.uniqueUpToIso hI').hom

def lemma_2_1_8_terminal {C : Type u} [Category.{v} C] {T T' : C}
    (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T' :=
  hT.uniqueUpToIso hT'

theorem example_2_1_9_initial {C : Type u} [Category.{v} C] (I : C) :
    Nonempty (Functor.fromPUnit.{u, v, u} I ⊣ Functor.star.{u, v, u} C) ↔
      Nonempty (IsInitial I) := by
  constructor
  · intro adj
    rcases adj with ⟨adj⟩
    letI : ∀ Y : C, Unique (I ⟶ Y) := fun Y =>
      { default := (adj.homEquiv ⟨PUnit.unit⟩ Y).invFun (ULift.up (PLift.up (by simp)))
        uniq := fun f => (adj.homEquiv ⟨PUnit.unit⟩ Y).injective (Subsingleton.elim _ _) }
    exact ⟨IsInitial.ofUnique I⟩
  · intro hI
    rcases hI with ⟨hI⟩
    exact ⟨Adjunction.mkOfHomEquiv
      { homEquiv := fun X Y =>
          { toFun := fun _ => ULift.up (PLift.up (by simp))
            invFun := fun _ => hI.to Y
            left_inv := by intro f; exact hI.hom_ext _ _
            right_inv := by intro f; apply Subsingleton.elim }
        homEquiv_naturality_left_symm := by
          intro X' X Y f g
          exact hI.hom_ext _ _
        homEquiv_naturality_right := by
          intro X Y Y' f g
          apply Subsingleton.elim }⟩

theorem example_2_1_9_terminal {C : Type u} [Category.{v} C] (T : C) :
    Nonempty (Functor.star.{u, v, u} C ⊣ Functor.fromPUnit.{u, v, u} T) ↔
      Nonempty (IsTerminal T) := by
  constructor
  · intro adj
    rcases adj with ⟨adj⟩
    letI : ∀ X : C, Unique (X ⟶ T) := fun X =>
      let d : X ⟶ T := (adj.homEquiv X ⟨PUnit.unit⟩).toFun (ULift.up (PLift.up (by simp)))
      { default := d
        uniq := fun f => (adj.homEquiv X ⟨PUnit.unit⟩).symm.injective
          (Subsingleton.elim ((adj.homEquiv X ⟨PUnit.unit⟩).symm f)
            ((adj.homEquiv X ⟨PUnit.unit⟩).symm d)) }
    exact ⟨IsTerminal.ofUnique T⟩
  · intro hT
    rcases hT with ⟨hT⟩
    exact ⟨Adjunction.mkOfHomEquiv
      { homEquiv := fun X Y =>
          { toFun := fun _ => hT.from X
            invFun := fun _ => ULift.up (PLift.up (by simp))
            left_inv := by intro f; apply Subsingleton.elim
            right_inv := by intro f; exact hT.hom_ext _ _ }
        homEquiv_naturality_left_symm := by
          intro X' X Y f g
          apply Subsingleton.elim
        homEquiv_naturality_right := by
          intro X Y Y' f g
          exact hT.hom_ext _ _ }⟩

def adjunction_comp {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {E : Type u} [Category.{v} E] {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) : F ⋙ H ⊣ I ⋙ G :=
  adj₁.comp adj₂

theorem exercise_2_1_14 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    ((∀ {A : C} {B B' : D} (g : F.obj A ⟶ B) (q : B ⟶ B'),
      adj.homEquiv A B' (g ≫ q) = adj.homEquiv A B g ≫ G.map q) ∧
     (∀ {A A' : C} {B : D} (p : A' ⟶ A) (f : A ⟶ G.obj B),
      (adj.homEquiv A' B).symm (p ≫ f) = F.map p ≫ (adj.homEquiv A B).symm f)) ↔
    (∀ {A A' : C} {B B' : D} (p : A' ⟶ A) (f : A ⟶ G.obj B) (q : B ⟶ B'),
      (adj.homEquiv A' B').symm (p ≫ f ≫ G.map q) =
      F.map p ≫ (adj.homEquiv A B).symm f ≫ q) := by
  constructor
  · intro ⟨h_nat_a, h_nat_b⟩ A A' B B' p f q
    have h_key : (adj.homEquiv A B').symm (f ≫ G.map q) = (adj.homEquiv A B).symm f ≫ q := by
      apply (adj.homEquiv A B').injective
      rw [Equiv.apply_symm_apply]
      rw [h_nat_a ((adj.homEquiv A B).symm f) q, Equiv.apply_symm_apply]
    calc
      (adj.homEquiv A' B').symm (p ≫ f ≫ G.map q) =
          (adj.homEquiv A' B').symm (p ≫ (f ≫ G.map q)) := by rfl
      _ = F.map p ≫ (adj.homEquiv A B').symm (f ≫ G.map q) := h_nat_b p (f ≫ G.map q)
      _ = F.map p ≫ ((adj.homEquiv A B).symm f ≫ q) := by rw [h_key]
      _ = F.map p ≫ (adj.homEquiv A B).symm f ≫ q := by rfl
  · intro h_single
    constructor
    · intro A B B' g q
      have h := h_single (𝟙 A) (adj.homEquiv A B g) q
      simpa using congrArg (adj.homEquiv A B') h.symm
    · intro A A' B p f
      have h := h_single p f (𝟙 B)
      simpa using h

noncomputable def exercise_2_1_15_left {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {I : C} (hI : IsInitial I) : IsInitial (F.obj I) := by
  haveI : ∀ Y : D, Unique ((F.obj I) ⟶ Y) := by
    intro Y
    refine
      { default := (adj.homEquiv I Y).symm (hI.to (G.obj Y))
        uniq := fun g => ?_ }
    apply (adj.homEquiv I Y).injective
    have : adj.homEquiv I Y g = hI.to (G.obj Y) := hI.hom_ext _ _
    rw [this, Equiv.apply_symm_apply]
  exact IsInitial.ofUnique (F.obj I)

noncomputable def exercise_2_1_15_right {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {T : D}
    (hT : IsTerminal T) : IsTerminal (G.obj T) := by
  haveI : ∀ X : C, Unique (X ⟶ G.obj T) := by
    intro X
    refine
      { default := adj.homEquiv X T (hT.from (F.obj X))
        uniq := fun f => ?_ }
    apply (adj.homEquiv X T).symm.injective
    have : (adj.homEquiv X T).symm f = hT.from (F.obj X) := hT.hom_ext _ _
    rw [this, Equiv.symm_apply_apply]
  exact IsTerminal.ofUnique (G.obj T)

structure FieldCat where
  carrier : Type u
  [isField : Field carrier]

namespace FieldCat

instance : CoeSort FieldCat (Type u) := ⟨FieldCat.carrier⟩
attribute [instance] FieldCat.isField

def of (K : Type u) [Field K] : FieldCat.{u} := ⟨K⟩

instance : Category FieldCat.{u} where
  Hom K L := K.carrier →+* L.carrier
  id K := RingHom.id K.carrier
  comp f g := RingHom.comp g f

def forget : FieldCat.{u} ⥤ Type u where
  obj K := K.carrier
  map {K L} (f : K ⟶ L) := ↾(f : K.carrier →+* L.carrier).toFun

end FieldCat

lemma two_ne_zero_rat : (2 : ULift.{u} ℚ) ≠ 0 := by
  intro h
  have : (2 : ℚ) = 0 := congrArg ULift.down h
  revert this
  decide

lemma two_eq_zero_zmod2 : (2 : ULift.{u} (ZMod 2)) = 0 := by
  apply ULift.ext
  exact CharP.cast_eq_zero (ZMod 2) 2

lemma no_hom_rat_and_zmod2 (K : Type u) [Field K]
    (f : K →+* ULift.{u} ℚ) (g : K →+* ULift.{u} (ZMod 2)) : False := by
  have h2_K : (2 : K) ≠ 0 := by
    intro h2
    have hf2 : f (2 : K) = 0 := by rw [h2, map_zero]
    have hf2' : f (2 : K) = (2 : ULift.{u} ℚ) := map_ofNat f 2
    rw [hf2'] at hf2
    exact two_ne_zero_rat hf2
  have h_inv : (2 : K) * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2_K
  have hg : g ((2 : K) * (2 : K)⁻¹) = 1 := by rw [h_inv, map_one]
  have hg2 : g ((2 : K) * (2 : K)⁻¹) = 0 := by
    rw [map_mul, map_ofNat, two_eq_zero_zmod2, zero_mul]
  have : (1 : ULift.{u} (ZMod 2)) = 0 := hg.symm.trans hg2
  have h_down : (1 : ZMod 2) = (0 : ZMod 2) := congrArg ULift.down this
  revert h_down
  decide

theorem fieldCat_has_no_initial (X : FieldCat.{u}) : ¬ Nonempty (IsInitial X) := by
  rintro ⟨h_init⟩
  let Y1 := FieldCat.of (ULift.{u} ℚ)
  let Y2 := FieldCat.of (ULift.{u} (ZMod 2))
  have f : X ⟶ Y1 := h_init.to Y1
  have g : X ⟶ Y2 := h_init.to Y2
  exact no_hom_rat_and_zmod2 X.carrier (f : X.carrier →+* ULift.{u} ℚ)
    (g : X.carrier →+* ULift.{u} (ZMod 2))

theorem example_2_1_3e_field_no_left_adjoint (F : Type u ⥤ FieldCat.{u}) :
    ¬ Nonempty (F ⊣ FieldCat.forget.{u}) := by
  rintro ⟨adj⟩
  have h_init : IsInitial (F.obj (⊥_ (Type u))) :=
    exercise_2_1_15_left adj initialIsInitial
  exact fieldCat_has_no_initial (F.obj (⊥_ (Type u))) ⟨h_init⟩

theorem example_2_1_3e_field_not_isRightAdjoint :
    ¬ Nonempty FieldCat.forget.{u}.IsRightAdjoint := by
  rintro ⟨h_adj⟩
  haveI := h_adj
  exact example_2_1_3e_field_no_left_adjoint FieldCat.forget.{u}.leftAdjoint
    ⟨Adjunction.ofIsRightAdjoint FieldCat.forget.{u}⟩

abbrev example_2_1_3_field_no_left_adjoint := @example_2_1_3e_field_no_left_adjoint
abbrev example_2_1_3_field_not_isRightAdjoint := @example_2_1_3e_field_not_isRightAdjoint
abbrev example_2_1_3f_field_no_left_adjoint := @example_2_1_3e_field_no_left_adjoint
abbrev example_2_1_3f_field_not_isRightAdjoint := @example_2_1_3e_field_not_isRightAdjoint

theorem example_2_2_1_unit (k : Type u) [Field k] (S : Type u) (s : S) :
    (example_2_1_3b k).unit.app S s = Finsupp.single s 1 := by
  change (ModuleCat.freeHomEquiv (𝟙 ((ModuleCat.free k).obj S))) s = Finsupp.single s 1
  rfl

theorem example_2_2_1_counit (k : Type u) [Field k] (M : ModuleCat.{u} k)
    (g : (forget (ModuleCat.{u} k)).obj M →₀ k) :
    (example_2_1_3b k).counit.app M g = g.sum (fun v r => r • v) := by
  let A : Type u := (forget (ModuleCat.{u} k)).obj M
  have hc : (example_2_1_3b k).counit.app M =
      ((example_2_1_3b k).homEquiv A M).symm (𝟙 A) := by
    rw [Adjunction.homEquiv_counit]
    simp
  rw [hc, ModuleCat.adj_homEquiv]
  change ((Finsupp.lift M k A (↾(𝟙 A))) g) = g.sum (fun v r => r • v)
  rw [Finsupp.lift_apply]
  rfl

lemma lemma_2_2_2_left_triangle {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : C) :
    F.map (adj.unit.app A) ≫ adj.counit.app (F.obj A) = 𝟙 (F.obj A) :=
  adj.left_triangle_components A

lemma lemma_2_2_2_right_triangle {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (B : D) :
    adj.unit.app (G.obj B) ≫ G.map (adj.counit.app B) = 𝟙 (G.obj B) :=
  adj.right_triangle_components B

def lemma_2_2_4_unit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B : D} (g : F.obj A ⟶ B) :
    adj.homEquiv A B g = adj.unit.app A ≫ G.map g :=
  adj.homEquiv_unit A B g

def lemma_2_2_4_counit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : C} {B : D} (f : A ⟶ G.obj B) :
    (adj.homEquiv A B).symm f = F.map f ≫ adj.counit.app B :=
  adj.homEquiv_counit A B f

def theorem_2_2_5_forward {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : Adjunction.CoreUnitCounit F G :=
  Adjunction.CoreUnitCounit.mk adj.unit adj.counit

noncomputable def theorem_2_2_5_reverse {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C}
    (c : Adjunction.CoreUnitCounit F G) : F ⊣ G :=
  Adjunction.mkOfUnitCounit c

theorem corollary_2_2_6 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} :
    Nonempty (F ⊣ G) ↔ Nonempty (Adjunction.CoreUnitCounit F G) := by
  constructor
  · intro h; rcases h with ⟨adj⟩; exact ⟨theorem_2_2_5_forward adj⟩
  · intro h; rcases h with ⟨c⟩; exact ⟨theorem_2_2_5_reverse c⟩

theorem example_2_2_7_left {A B : Type u} [PartialOrder A] [PartialOrder B] (f : A → B) (g : B → A)
    (hf : Monotone f) (hadj : ∀ a b, f a ≤ b ↔ a ≤ g b) (a : A) :
    f (g (f a)) = f a := by
  have h₁ : ∀ a, a ≤ g (f a) := fun a => (hadj a (f a)).mp (le_refl (f a))
  have h₂ : ∀ b, f (g b) ≤ b := fun b => (hadj (g b) b).mpr (le_refl (g b))
  apply le_antisymm
  · exact h₂ (f a)
  · exact hf (h₁ a)

theorem example_2_2_7_right {A B : Type u} [PartialOrder A] [PartialOrder B] (f : A → B) (g : B → A)
    (hg : Monotone g) (hadj : ∀ a b, f a ≤ b ↔ a ≤ g b) (b : B) :
    g (f (g b)) = g b := by
  have h₁ : ∀ a, a ≤ g (f a) := fun a => (hadj a (f a)).mp (le_refl (f a))
  have h₂ : ∀ b, f (g b) ≤ b := fun b => (hadj (g b) b).mpr (le_refl (g b))
  apply le_antisymm
  · exact hg (h₂ b)
  · exact h₁ (g b)

theorem example_2_2_7_fixed_points {A B : Type u} [PartialOrder A] [PartialOrder B]
    (f : A → B) (g : B → A) (hf : Monotone f) (hg : Monotone g)
    (hadj : ∀ a b, f a ≤ b ↔ a ≤ g b) :
    Nonempty ({a : A // g (f a) = a} ≃ {b : B // f (g b) = b}) := by
  exact
    ⟨{ toFun := fun a => ⟨f a.1, example_2_2_7_left f g hf hadj a.1⟩,
       invFun := fun b => ⟨g b.1, example_2_2_7_right f g hg hadj b.1⟩,
       left_inv := fun a => Subtype.ext a.2,
       right_inv := fun b => Subtype.ext b.2 }⟩

theorem exercise_2_2_10 {A B : Type u} [Preorder A] [Preorder B] (f : A → B) (g : B → A)
    (hf : Monotone f) (hg : Monotone g) :
    ((∀ a b, f a ≤ b ↔ a ≤ g b) ↔ (∀ a, a ≤ g (f a)) ∧ (∀ b, f (g b) ≤ b)) := by
  constructor
  · intro h
    constructor
    · intro a
      apply (h a (f a)).mp
      exact le_refl (f a)
    · intro b
      apply (h (g b) b).mpr
      exact le_refl (g b)
  · intro ⟨h₁, h₂⟩ a b
    constructor
    · intro hfa_le_b
      have ha_gfa : a ≤ g (f a) := h₁ a
      have hgfa_gb : g (f a) ≤ g b := hg hfa_le_b
      exact le_trans ha_gfa hgfa_gb
    · intro ha_gb
      have hfa_fgb : f a ≤ f (g b) := hf ha_gb
      have hfgb_b : f (g b) ≤ b := h₂ b
      exact le_trans hfa_fgb hfgb_b

noncomputable abbrev exercise_2_2_11b_fixGF {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :=
  ObjectProperty.FullSubcategory fun A : C => IsIso (adj.unit.app A)

noncomputable abbrev exercise_2_2_11b_fixFG {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :=
  ObjectProperty.FullSubcategory fun B : D => IsIso (adj.counit.app B)

noncomputable def exercise_2_2_11b_functor {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    exercise_2_2_11b_fixGF adj ⥤ exercise_2_2_11b_fixFG adj where
  obj := fun ⟨A, hA⟩ =>
    ⟨F.obj A, by
      haveI := hA
      exact isIso_of_hom_comp_eq_id (F.map (adj.unit.app A)) (adj.left_triangle_components A)⟩
  map := fun f => { hom := F.map f.hom }
  map_id := by
    intro X
    apply ObjectProperty.hom_ext
    change F.map (𝟙 X.obj) = 𝟙 (F.obj X.obj)
    exact F.map_id X.obj
  map_comp := by
    intro X Y Z f g
    apply ObjectProperty.hom_ext
    change F.map (f.hom ≫ g.hom) = F.map f.hom ≫ F.map g.hom
    exact F.map_comp f.hom g.hom

noncomputable def exercise_2_2_11b_inverse {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    exercise_2_2_11b_fixFG adj ⥤ exercise_2_2_11b_fixGF adj where
  obj := fun ⟨B, hB⟩ =>
    ⟨G.obj B, by
      haveI := hB
      exact isIso_of_comp_hom_eq_id (G.map (adj.counit.app B)) (adj.right_triangle_components B)⟩
  map := fun g => { hom := G.map g.hom }
  map_id := by
    intro X
    apply ObjectProperty.hom_ext
    change G.map (𝟙 X.obj) = 𝟙 (G.obj X.obj)
    exact G.map_id X.obj
  map_comp := by
    intro X Y Z f g
    apply ObjectProperty.hom_ext
    change G.map (f.hom ≫ g.hom) = G.map f.hom ≫ G.map g.hom
    exact G.map_comp f.hom g.hom

noncomputable def exercise_2_2_11b_equiv {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    exercise_2_2_11b_fixGF adj ≌ exercise_2_2_11b_fixFG adj where
  functor := exercise_2_2_11b_functor adj
  inverse := exercise_2_2_11b_inverse adj
  unitIso := NatIso.ofComponents (fun A =>
      letI : IsIso (adj.unit.app A.obj) := A.property
      { hom := { hom := adj.unit.app A.obj }
        inv := { hom := (asIso (adj.unit.app A.obj)).inv }
        hom_inv_id := by
          apply ObjectProperty.hom_ext
          change adj.unit.app A.obj ≫ (asIso (adj.unit.app A.obj)).inv = 𝟙 A.obj
          exact (asIso (adj.unit.app A.obj)).hom_inv_id
        inv_hom_id := by
          apply ObjectProperty.hom_ext
          change (asIso (adj.unit.app A.obj)).inv ≫ adj.unit.app A.obj = 𝟙 (G.obj (F.obj A.obj))
          exact (asIso (adj.unit.app A.obj)).inv_hom_id }) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    change (𝟭 C).map f.hom ≫ adj.unit.app Y.obj = adj.unit.app X.obj ≫ (F ⋙ G).map f.hom
    exact adj.unit.naturality f.hom)
  counitIso := NatIso.ofComponents (fun B =>
      letI : IsIso (adj.counit.app B.obj) := B.property
      { hom := { hom := adj.counit.app B.obj }
        inv := { hom := (asIso (adj.counit.app B.obj)).inv }
        hom_inv_id := by
          apply ObjectProperty.hom_ext
          change adj.counit.app B.obj ≫ (asIso (adj.counit.app B.obj)).inv = 𝟙 (F.obj (G.obj B.obj))
          exact (asIso (adj.counit.app B.obj)).hom_inv_id
        inv_hom_id := by
          apply ObjectProperty.hom_ext
          change (asIso (adj.counit.app B.obj)).inv ≫ adj.counit.app B.obj = 𝟙 B.obj
          exact (asIso (adj.counit.app B.obj)).inv_hom_id }) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    change (G ⋙ F).map f.hom ≫ adj.counit.app Y.obj = adj.counit.app X.obj ≫ (𝟭 D).map f.hom
    exact adj.counit.naturality f.hom)
  functor_unitIso_comp := by
    intro X
    apply ObjectProperty.hom_ext
    change F.map (adj.unit.app X.obj) ≫ adj.counit.app (F.obj X.obj) = 𝟙 (F.obj X.obj)
    exact adj.left_triangle_components X.obj

theorem exercise_2_2_11b {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    Nonempty (exercise_2_2_11b_fixGF adj ≌ exercise_2_2_11b_fixFG adj) :=
  ⟨exercise_2_2_11b_equiv adj⟩

theorem exercise_2_2_12b {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : (G.Full ∧ G.Faithful) ↔ IsIso adj.counit := by
  constructor
  · intro ⟨hFull, hFaithful⟩
    haveI := hFull; haveI := hFaithful
    exact Adjunction.counit_isIso_of_R_fully_faithful adj
  · intro h
    haveI := h
    have hFF : G.FullyFaithful := Adjunction.fullyFaithfulROfIsIsoCounit adj
    exact ⟨hFF.full, hFF.faithful⟩

noncomputable def exercise_2_2_14 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {S : Type u} [Category.{v} S] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    (Functor.whiskeringLeft D C S).obj G ⊣ (Functor.whiskeringLeft C D S).obj F :=
  Adjunction.whiskerLeft S adj

abbrev def_2_3_1 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {E : Type u} [Category.{v} E] (P : C ⥤ E) (Q : D ⥤ E) :=
  Comma P Q

theorem def_2_3_1_map {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {E : Type u} [Category.{v} E] {P : C ⥤ E} {Q : D ⥤ E} {X Y : Comma P Q}
    (f : X ⟶ Y) : P.map f.left ≫ Y.hom = X.hom ≫ Q.map f.right :=
  f.w

abbrev example_2_3_3_slice {C : Type u} [Category.{v} C] (A : C) :=
  Over A

theorem example_2_3_3_slice_comma {C : Type u} [Category.{v} C] (A : C) :
    Over A = Comma (𝟭 C) (Functor.fromPUnit.{0} A) :=
  rfl

abbrev example_2_3_3_coslice {C : Type u} [Category.{v} C] (A : C) :=
  Under A

theorem example_2_3_3_coslice_comma {C : Type u} [Category.{v} C] (A : C) :
    Under A = Comma (Functor.fromPUnit.{0} A) (𝟭 C) :=
  rfl

abbrev example_2_3_4 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {G : D ⥤ C} (A : C) :=
  StructuredArrow A G

noncomputable def lemma_2_3_5 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A : C) :
    IsInitial (StructuredArrow.mk (adj.unit.app A) : StructuredArrow A G) :=
  mkInitialOfLeftAdjoint G adj A

noncomputable def theorem_2_3_6_reverse {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G)
    (hη : ∀ A : C, IsInitial (StructuredArrow.mk (η.app A) : StructuredArrow A G)) :
    F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun g => η.app X ≫ G.map g
          invFun := fun f => ((hη X).to (StructuredArrow.mk f)).right
          left_inv := by
            intro g
            have h := (hη X).hom_ext
              ((hη X).to (StructuredArrow.mk (η.app X ≫ G.map g)))
              (StructuredArrow.homMk' (StructuredArrow.mk (η.app X) : StructuredArrow X G) g)
            simpa using congrArg (fun m : _ => m.right) h
          right_inv := by
            intro f
            exact StructuredArrow.w ((hη X).to (StructuredArrow.mk f)) }
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        let t : F.obj X ⟶ Y := ((hη X).to (StructuredArrow.mk g)).right
        have hcomm : η.app X ≫ G.map t = g := by
          simpa [t] using StructuredArrow.w ((hη X).to (StructuredArrow.mk g))
        have hw : η.app X' ≫ G.map (F.map f ≫ t) = f ≫ g := by
          calc
            η.app X' ≫ G.map (F.map f ≫ t) = η.app X' ≫ G.map (F.map f) ≫ G.map t := by
              simp
            _ = (f ≫ η.app X) ≫ G.map t := by
              simpa using congrArg (fun m : X' ⟶ G.obj (F.obj X) => m ≫ G.map t)
                (η.naturality f).symm
            _ = f ≫ (η.app X ≫ G.map t) := by
              simp
            _ = f ≫ g := by
              exact congrArg (fun m : X ⟶ G.obj Y => f ≫ m) hcomm
        have hm : (hη X').to (StructuredArrow.mk (f ≫ g)) =
            StructuredArrow.homMk (F.map f ≫ t) hw :=
          (hη X').hom_ext _ _
        simpa [t] using congrArg (fun m : _ => m.right) hm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        simp }

lemma adjunction_ext {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} {adj₁ adj₂ : F ⊣ G} (h₁ : adj₁.unit = adj₂.unit)
    (h₂ : adj₁.counit = adj₂.counit) : adj₁ = adj₂ := by
  cases adj₁ with
  | mk unit₁ counit₁ ltr₁ rtr₁ =>
    cases adj₂ with
    | mk unit₂ counit₂ ltr₂ rtr₂ =>
      subst h₁
      subst h₂
      congr

noncomputable def theorem_2_3_6 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} {G : D ⥤ C} :
    (F ⊣ G) ≃ {η : 𝟭 C ⟶ F ⋙ G // ∀ A : C,
      Nonempty (IsInitial (StructuredArrow.mk (η.app A) : StructuredArrow A G))} :=
  { toFun := fun adj => ⟨adj.unit, fun A => ⟨mkInitialOfLeftAdjoint G adj A⟩⟩
    invFun := fun ⟨η, p⟩ => theorem_2_3_6_reverse (η := η) (hη := fun A => Classical.choice (p A))
    left_inv := by
      intro adj
      apply adjunction_ext
      · ext X
        simp [theorem_2_3_6_reverse]
      · ext Y
        let hη₀ : ∀ A : C,
            IsInitial (StructuredArrow.mk (adj.unit.app A) : StructuredArrow A G) :=
          fun A => Classical.choice (⟨mkInitialOfLeftAdjoint G adj A⟩)
        let m₁ : (StructuredArrow.mk (adj.unit.app (G.obj Y)) : StructuredArrow (G.obj Y) G) ⟶
            (StructuredArrow.mk (𝟙 (G.obj Y)) : StructuredArrow (G.obj Y) G) :=
          (hη₀ (G.obj Y)).to (StructuredArrow.mk (𝟙 (G.obj Y)))
        let m₂ : (StructuredArrow.mk (adj.unit.app (G.obj Y)) : StructuredArrow (G.obj Y) G) ⟶
            (StructuredArrow.mk (𝟙 (G.obj Y)) : StructuredArrow (G.obj Y) G) :=
          StructuredArrow.homMk (adj.counit.app Y) (adj.right_triangle_components Y)
        have hm : m₁ = m₂ := (hη₀ (G.obj Y)).hom_ext m₁ m₂
        change m₁.right = m₂.right
        exact congrArg (fun m : _ => m.right) hm
    right_inv := by
      intro ⟨η, p⟩
      apply Subtype.ext
      apply NatTrans.ext
      funext X
      simp [theorem_2_3_6_reverse] }

theorem corollary_2_3_7 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {G : D ⥤ C} :
    G.IsRightAdjoint ↔ ∀ A : C, HasInitial (StructuredArrow A G) :=
  isRightAdjoint_iff_hasInitial_structuredArrow

theorem exercise_2_3_9 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F : C ⥤ D} :
    F.IsLeftAdjoint ↔ ∀ B : D, HasTerminal (CostructuredArrow F B) :=
  isLeftAdjoint_iff_hasTerminal_costructuredArrow

noncomputable def exercise_2_3_10 {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : e.functor ⊣ e.inverse :=
  e.toAdjunction

theorem exercise_2_3_11 {A : Type u} [Category.{v} A] {U : A ⥤ Type u'} {F : Type u' ⥤ A}
    (adj : F ⊣ U) (h : ∃ X : A, ∃ x₁ x₂ : U.obj X, x₁ ≠ x₂) (S : Type u') :
    Function.Injective (adj.unit.app S) := by
  classical
  rcases h with ⟨X, x₁, x₂, hx⟩
  intro s₁ s₂ hs
  by_contra hne
  let f : S ⟶ U.obj X := ↾(fun s => if s = s₁ then x₁ else x₂)
  have hf₁ : f s₁ = x₁ := by simp [f]
  have hf₂ : f s₂ = x₂ := by
    change (if s₂ = s₁ then x₁ else x₂) = x₂
    rw [if_neg (Ne.symm hne)]
  let g : F.obj S ⟶ X := (adj.homEquiv S X).symm f
  have hcomm : adj.unit.app S ≫ U.map g = f := by
    exact (adj.homEquiv_unit S X g).symm.trans (by
      simp [g])
  have hcomm' : ∀ s : S, U.map g (adj.unit.app S s) = f s := by
    intro s
    simpa using congrArg (fun m : S ⟶ U.obj X => m s) hcomm
  have h₁ : x₁ = x₂ := by
    calc
      x₁ = f s₁ := by rw [hf₁]
      _ = U.map g (adj.unit.app S s₁) := (hcomm' s₁).symm
      _ = U.map g (adj.unit.app S s₂) := by rw [hs]
      _ = f s₂ := hcomm' s₂
      _ = x₂ := by rw [hf₂]
  exact hx h₁

noncomputable def exercise_2_3_12 : PartialFun.{u} ≌ Pointed :=
  partialFunEquivPointed

noncomputable def exercise_2_3_12_coslice_functor : Pointed.{u} ⥤ Under PUnit.{u + 1} where
  obj := fun X => Under.mk (↾(fun _ : PUnit.{u + 1} => X.point))
  map := fun {X Y} (f : X ⟶ Y) => @Under.homMk (Type u) _ PUnit.{u + 1}
    (Under.mk (↾(fun _ : PUnit.{u + 1} => X.point)))
    (Under.mk (↾(fun _ : PUnit.{u + 1} => Y.point))) (↾f.toFun) (by
      ext; simpa using f.map_point)
  map_id := fun X => by
    apply StructuredArrow.hom_ext
    rfl
  map_comp := fun f g => by
    apply StructuredArrow.hom_ext
    rfl

noncomputable def exercise_2_3_12_coslice_inverse : Under PUnit.{u + 1} ⥤ Pointed where
  obj := fun X => Pointed.of (X.hom PUnit.unit)
  map := fun {X Y} (f : X ⟶ Y) =>
    ⟨f.right, by
      change f.right (X.hom PUnit.unit) = Y.hom PUnit.unit
      rw [← types_comp_apply]
      rw [show X.hom ≫ Under.Hom.right f = Y.hom from (StructuredArrow.w f)]⟩
  map_id := fun X => by
    apply Pointed.Hom.ext
    rfl
  map_comp := fun f g => by
    apply Pointed.Hom.ext
    rfl

noncomputable def exercise_2_3_12_coslice : Pointed.{u} ≌ Under PUnit.{u + 1} where
  functor := exercise_2_3_12_coslice_functor
  inverse := exercise_2_3_12_coslice_inverse
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    exact Pointed.Hom.ext (by rfl))
  counitIso := NatIso.ofComponents
    (fun X => Under.isoMk (Iso.refl X.right) (by
      change (↾(fun _ : PUnit.{u + 1} => X.hom PUnit.unit) ≫ (Iso.refl X.right).hom) =
        X.hom
      change (↾(fun _ : PUnit.{u + 1} => X.hom PUnit.unit)) = X.hom
      rfl)) (by
    intro X Y f
    exact StructuredArrow.hom_ext _ _ (by rfl))
  functor_unitIso_comp X := by
    exact StructuredArrow.hom_ext _ _ (by rfl)

end Adjoints
