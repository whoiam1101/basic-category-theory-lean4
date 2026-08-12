-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib

namespace Categories

universe u v

open CategoryTheory

abbrev example_1_1_3a : Category (Type u) := inferInstance

abbrev example_1_1_3b : Category GrpCat := inferInstance

abbrev example_1_1_3c : Category RingCat := inferInstance

abbrev example_1_1_3d (k : Type*) [Field k] : Category (ModuleCat k) := inferInstance

abbrev example_1_1_3e : Category TopCat := inferInstance

theorem example_1_1_5 {X Y : Type u} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f :=
  isIso_iff_bijective f

theorem example_1_1_6_group {X Y : GrpCat} (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective ((forget GrpCat).map f) :=
  ConcreteCategory.isIso_iff_bijective f

theorem example_1_1_6_ring {X Y : RingCat} (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective ((forget RingCat).map f) :=
  ConcreteCategory.isIso_iff_bijective f

theorem example_1_1_7_top {X Y : TopCat} (f : X ⟶ Y) :
    IsIso f ↔ IsHomeomorph ((forget TopCat).map f) :=
  TopCat.isIso_iff_isHomeomorph f

open Real in
theorem example_1_1_7 :
    ∃ f : Set.Ico (0 : ℝ) 1 → Circle, Continuous f ∧ Function.Bijective f ∧ ¬IsHomeomorph f := by
  refine ⟨fun t => Circle.exp (2 * π * t), ?_, ?_, ?_⟩
  · exact Circle.exp.continuous.comp <| by fun_prop
  · rw [Function.bijective_iff_existsUnique]
    intro b
    use ⟨Int.fract (Complex.arg b / (2 * π)), Int.fract_nonneg _, Int.fract_lt_one _⟩
    dsimp
    refine ⟨?_, ?_⟩
    · calc Circle.exp (2 * π * Int.fract ((b : ℂ).arg / (2 * π)))
          = Circle.exp ((b : ℂ).arg - ⌊(b : ℂ).arg / (2 * π)⌋ * (2 * π)) := by
            congr 1
            rw [Int.fract]
            field_simp
        _ = Circle.exp (b : ℂ).arg * Circle.exp (-(⌊(b : ℂ).arg / (2 * π)⌋ * (2 * π))) := by
            rw [sub_eq_add_neg, Circle.exp_add]
        _ = Circle.exp (b : ℂ).arg * (Circle.exp (⌊(b : ℂ).arg / (2 * π)⌋ * (2 * π)))⁻¹ := by
            rw [Circle.exp_neg]
        _ = Circle.exp (b : ℂ).arg * 1⁻¹ := by
            rw [Circle.exp_int_mul_two_pi]
        _ = Circle.exp (b : ℂ).arg := by
            rw [inv_one, mul_one]
        _ = b := Circle.argEquiv.left_inv b
    · intro y hy
      rw [←Circle.exp_arg b, Circle.exp_eq_exp] at hy
      obtain ⟨m, h⟩ := hy
      ext
      have h_div : (b : ℂ).arg / (2 * π) = (y : ℝ) - (m : ℝ) := by
        field_simp
        calc (b : ℂ).arg = ((b : ℂ).arg + (m : ℝ) * (2 * π)) - (m : ℝ) * (2 * π) := by ring
          _ = 2 * π * (y : ℝ) - (m : ℝ) * (2 * π) := by rw [← h]
          _ = 2 * π * (y : ℝ) - 2 * π * (m : ℝ) := by ring
          _ = 2 * π * ((y : ℝ) - (m : ℝ)) := by ring
      rw [h_div]
      simp only [Int.fract_sub_intCast]
      exact (Int.fract_eq_self.mpr y.prop).symm
  · intro h_homeo
    have h_equiv : Set.Ico (0 : ℝ) 1 ≃ₜ Circle := IsHomeomorph.homeomorph _ h_homeo
    have h_compact : IsCompact (Set.Ico (0 : ℝ) 1) := by
      have : CompactSpace (Set.Ico (0 : ℝ) 1) := h_equiv.symm.compactSpace
      exact isCompact_iff_compactSpace.mpr this
    rw [isCompact_Ico_iff] at h_compact
    linarith

abbrev example_1_1_8_b_discrete (α : Type u) : Category (Discrete α) := inferInstance

abbrev example_1_1_8_cd_single_obj (M : Type u) [Monoid M] : Category (SingleObj M) := inferInstance

abbrev example_1_1_8_e_preorder (α : Type u) [Preorder α] : Category α := inferInstance

abbrev example_1_1_8_e_partial_order (α : Type u) [PartialOrder α] : Category α := inferInstance

abbrev example_1_1_9_opposite (C : Type u) [Category.{v} C] : Category Cᵒᵖ := inferInstance

abbrev example_1_1_11_product (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] :
    Category (C × D) := inferInstance

theorem exercise_1_1_13 (C : Type u) [Category.{v} C] {A B : C} (f : A ⟶ B) (g h : B ⟶ A)
    (hgf : f ≫ g = 𝟙 A) (hfg : g ≫ f = 𝟙 B)
    (hhf : f ≫ h = 𝟙 A) (hfh : h ≫ f = 𝟙 B) : g = h :=
  calc
    g = 𝟙 B ≫ g := by rw [Category.id_comp]
    _ = (h ≫ f) ≫ g := by rw [← hfh]
    _ = h ≫ (f ≫ g) := by rw [Category.assoc]
    _ = h ≫ 𝟙 A := by rw [hgf]
    _ = h := by rw [Category.comp_id]

theorem exercise_1_1_14_comp (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D]
    {A B C' : C} {A' B' C'' : D}
    (f : A ⟶ B) (g : B ⟶ C') (f' : A' ⟶ B') (g' : B' ⟶ C'') :
    Prod.mkHom f f' ≫ Prod.mkHom g g' = Prod.mkHom (f ≫ g) (f' ≫ g') := rfl

theorem exercise_1_1_14_id (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D]
    (A : C) (A' : D) : 𝟙 (A, A') = Prod.mkHom (𝟙 A) (𝟙 A') := rfl

end Categories

#min_imports
