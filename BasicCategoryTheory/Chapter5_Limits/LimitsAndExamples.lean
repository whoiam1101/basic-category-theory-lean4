-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Biproducts

namespace LimitsAndExamples

universe u v u' v' w

open CategoryTheory Limits

abbrev def_5_1_1_cone {C : Type u} [Category.{v} C] (X Y : C) (P : C) (p₁ : P ⟶ X) (p₂ : P ⟶ Y) :
    BinaryFan X Y := BinaryFan.mk p₁ p₂

def def_5_1_1_is_product {C : Type u} [Category.{v} C] {X Y P : C}
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) : Prop :=
  Nonempty (IsLimit (BinaryFan.mk p₁ p₂))

def def_5_1_1_has_product {C : Type u} [Category.{v} C] (X Y : C) : Prop :=
  HasBinaryProduct X Y

theorem lemma_5_1_2_unique {C : Type u} [Category.{v} C] {X Y : C}
    {c c' : BinaryFan X Y} (hc : IsLimit c) (hc' : IsLimit c') :
    ∃! e : c.pt ≅ c'.pt,
      e.hom ≫ BinaryFan.fst c' = BinaryFan.fst c ∧
      e.hom ≫ BinaryFan.snd c' = BinaryFan.snd c := by
  refine ⟨hc.conePointUniqueUpToIso hc',
    ⟨hc.conePointUniqueUpToIso_hom_comp hc' ⟨WalkingPair.left⟩,
     hc.conePointUniqueUpToIso_hom_comp hc' ⟨WalkingPair.right⟩⟩, fun e he => ?_⟩
  ext
  apply BinaryFan.IsLimit.hom_ext hc'
  · rw [he.1, hc.conePointUniqueUpToIso_hom_comp]
  · rw [he.2, hc.conePointUniqueUpToIso_hom_comp]

def example_5_1_3 (X Y : Type u) :
    IsLimit (Types.binaryProductCone X Y) :=
  Types.binaryProductLimit X Y

noncomputable abbrev example_5_1_4 (X Y : TopCat.{u}) : HasBinaryProduct X Y :=
  inferInstance

noncomputable abbrev example_5_1_5 (R : Type u) [Ring R] (X Y : ModuleCat.{u} R) :
    HasBinaryProduct X Y :=
  inferInstance

theorem example_5_1_6a (x y : ℝ) :
    min x y ≤ x ∧ min x y ≤ y ∧ ∀ a, a ≤ x → a ≤ y → a ≤ min x y :=
  ⟨min_le_left x y, min_le_right x y, fun _ => le_min⟩

theorem example_5_1_6b {S : Type u} (X Y : Set S) :
    X ∩ Y ⊆ X ∧ X ∩ Y ⊆ Y ∧ ∀ A, A ⊆ X → A ⊆ Y → A ⊆ X ∩ Y :=
  ⟨Set.inter_subset_left, Set.inter_subset_right, fun _ => Set.subset_inter⟩

theorem example_5_1_6c (x y : ℕ) :
    x.gcd y ∣ x ∧ x.gcd y ∣ y ∧ ∀ a, a ∣ x → a ∣ y → a ∣ x.gcd y :=
  ⟨Nat.gcd_dvd_left x y, Nat.gcd_dvd_right x y, fun _ => Nat.dvd_gcd⟩

theorem example_5_1_6_meet {α : Type u} [SemilatticeInf α] (x y : α) :
    x ⊓ y ≤ x ∧ x ⊓ y ≤ y ∧ ∀ a, a ≤ x → a ≤ y → a ≤ x ⊓ y :=
  ⟨inf_le_left, inf_le_right, fun _ => le_inf⟩

abbrev def_5_1_7_fan {C : Type u} [Category.{v} C] {I : Type w} (X : I → C)
    (P : C) (p : (i : I) → (P ⟶ X i)) : Fan X :=
  Fan.mk P p

def def_5_1_7_is_product {C : Type u} [Category.{v} C] {I : Type w} {X : I → C}
    (c : Fan X) : Prop :=
  Nonempty (IsLimit c)

def def_5_1_7_has_product {C : Type u} [Category.{v} C] {I : Type w} (X : I → C) : Prop :=
  HasProduct X

theorem example_5_1_8 {α : Type u} [CompleteLattice α] {I : Type w} (x : I → α) :
    (∀ i, ⨅ j, x j ≤ x i) ∧ (∀ a, (∀ i, a ≤ x i) → a ≤ ⨅ j, x j) :=
  ⟨fun i => iInf_le x i, fun _ => le_iInf⟩

def example_5_1_9 {C : Type u} [Category.{v} C] (T : C) :
    IsTerminal T ≃ IsLimit (asEmptyCone T) where
  toFun hT := hT
  invFun hL := hL
  left_inv _ := rfl
  right_inv _ := rfl

def example_5_1_10 (I : Type u) (X : Type u) :
    IsLimit (Fan.mk (I → X) (fun i => (↾fun f => f i))) :=
  Fan.IsLimit.mk _
    (fun s => ↾fun x i => s.proj i x)
    (fun _ _ => rfl)
    (fun s m hm => by
      ext x
      funext i
      exact ConcreteCategory.congr_hom (hm i) x)

abbrev def_5_1_11_fork {C : Type u} [Category.{v} C] {X Y : C} (s t : X ⟶ Y)
    (E : C) (i : E ⟶ X) (h : i ≫ s = i ≫ t) : Fork s t :=
  Fork.ofι i h

def def_5_1_11_is_equalizer {C : Type u} [Category.{v} C] {X Y : C} {s t : X ⟶ Y}
    (c : Fork s t) : Prop :=
  Nonempty (IsLimit c)

def def_5_1_11_has_equalizer {C : Type u} [Category.{v} C] {X Y : C} (s t : X ⟶ Y) : Prop :=
  HasEqualizer s t

def example_5_1_13_set {X Y : Type u} (s t : X ⟶ Y) :
    IsLimit (Fork.ofι (f := s) (g := t) (↾fun (x : {x : X // s x = t x}) => x.1)
      (by ext ⟨_, hx⟩; exact hx)) :=
  Fork.IsLimit.mk _
    (fun s' => ↾fun x => ⟨s'.ι x, ConcreteCategory.congr_hom s'.condition x⟩)
    (fun _ => rfl)
    (fun _ _ hm => by
      ext x
      apply Subtype.ext
      exact ConcreteCategory.congr_hom hm x)

theorem example_5_1_13_simultaneous {X : Type u} {Λ : Type w} {Y : Λ → Type u}
    (s t : (l : Λ) → X → Y l) (x : X) :
    (∀ l, s l x = t l x) ↔ (fun l => s l x) = (fun l => t l x) :=
  ⟨fun h => funext h, fun h l => congrFun h l⟩

noncomputable abbrev example_5_1_14 {X Y : TopCat.{u}} (s t : X ⟶ Y) : HasEqualizer s t :=
  inferInstance

noncomputable abbrev example_5_1_15 {G H : GrpCat.{u}} (θ : G ⟶ H) : HasEqualizer θ 1 :=
  inferInstance

noncomputable abbrev example_5_1_16 {R : Type u} [Ring R] (V W : ModuleCat.{u} R) (s t : V ⟶ W) :
    HasEqualizer s t :=
  inferInstance

abbrev def_5_1_17_cone {C : Type u} [Category.{v} C] {X Y Z : C}
    (s : X ⟶ Z) (t : Y ⟶ Z) (P : C) (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (h : p₁ ≫ s = p₂ ≫ t) :
    PullbackCone s t :=
  PullbackCone.mk p₁ p₂ h

def def_5_1_17_is_pullback {C : Type u} [Category.{v} C] {X Y Z : C}
    {s : X ⟶ Z} {t : Y ⟶ Z} (c : PullbackCone s t) : Prop :=
  Nonempty (IsLimit c)

def def_5_1_17_has_pullback {C : Type u} [Category.{v} C] {X Y Z : C}
    (s : X ⟶ Z) (t : Y ⟶ Z) : Prop :=
  HasPullback s t

noncomputable def example_5_1_19 {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsLimit (Types.pullbackCone f g) :=
  (Types.pullbackLimitCone f g).isLimit

noncomputable abbrev example_5_1_19a {X Y : Type u} (f : X ⟶ Y) (Y' : Set Y) :
    HasPullback f (↾fun (y : ↥Y') => y.1) :=
  inferInstance

noncomputable abbrev example_5_1_19b {Z : Type u} (X Y : Set Z) :
    HasPullback (↾fun (x : ↥X) => x.1) (↾fun (y : ↥Y) => y.1) :=
  inferInstance

abbrev def_5_1_20 {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    (D : I ⥤ A) := D

abbrev def_5_1_21a {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    (D : I ⥤ A) := Cone D

abbrev def_5_1_21b {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D : I ⥤ A} (c : Cone D) := IsLimit c

theorem lemma_5_1_22_unique {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D : I ⥤ A} {c c' : Cone D} (hc : IsLimit c) (hc' : IsLimit c') :
    ∃! e : c.pt ≅ c'.pt, ∀ i : I, e.hom ≫ c'.π.app i = c.π.app i := by
  refine ⟨hc.conePointUniqueUpToIso hc',
    fun i => hc.conePointUniqueUpToIso_hom_comp hc' i, fun e he => ?_⟩
  ext
  apply hc'.hom_ext
  intro i
  rw [hc.conePointUniqueUpToIso_hom_comp]
  exact he i

noncomputable abbrev example_5_1_23a_product {C : Type u} [Category.{v} C] {I : Type w} (X : I → C)
    [HasProduct X] : HasLimit (Discrete.functor X) :=
  inferInstance

noncomputable abbrev example_5_1_23a_terminal (C : Type u) [Category.{v} C] [HasTerminal C]
    (F : Discrete.{0} PEmpty ⥤ C) : HasLimit F :=
  inferInstance

noncomputable abbrev example_5_1_23b_equalizer {C : Type u} [Category.{v} C] {X Y : C} (s t : X ⟶ Y)
    [HasEqualizer s t] : HasLimit (parallelPair s t) :=
  inferInstance

noncomputable abbrev example_5_1_23c_pullback {C : Type u} [Category.{v} C]
    {X Y Z : C} (s : X ⟶ Z) (t : Y ⟶ Z) [HasPullback s t] : HasLimit (cospan s t) :=
  inferInstance

noncomputable abbrev example_5_1_23d_inverse_limit (C : Type u) [Category.{v} C]
    [HasLimitsOfShape ℕᵒᵖ C] (D : ℕᵒᵖ ⥤ C) : HasLimit D :=
  inferInstance

noncomputable abbrev example_5_1_24 {I : Type u} [Category.{v} I] (D : I ⥤ Type u) : HasLimit D :=
  inferInstance

noncomputable def example_5_1_24_isLimit {I : Type u} [Category.{v} I] (D : I ⥤ Type u) :
    IsLimit (Types.limitCone D) :=
  Types.limitConeIsLimit D

noncomputable abbrev example_5_1_25_grp : HasLimits GrpCat.{u} :=
  inferInstance

noncomputable abbrev example_5_1_25_ring : HasLimits RingCat.{u} :=
  inferInstance

noncomputable abbrev example_5_1_25_mod (R : Type u) [Ring R] :
    HasLimits (ModuleCat.{u} R) :=
  inferInstance

noncomputable abbrev example_5_1_26 : HasLimits TopCat.{u} :=
  inferInstance

def def_5_1_27a {I : Type u} [Category.{v} I] (C : Type u') [Category.{v'} C] : Prop :=
  HasLimitsOfShape I C

def def_5_1_27b (C : Type u) [Category.{v} C] : Prop :=
  HasLimits C

def def_5_1_27_finite (C : Type u) [Category.{v} C] : Prop :=
  HasFiniteLimits C

abbrev proposition_5_1_29a (C : Type u) [Category.{v} C]
    [HasProducts.{w} C] [HasEqualizers C] : HasLimitsOfSize.{w, w} C :=
  has_limits_of_hasEqualizers_and_products

abbrev proposition_5_1_29b (C : Type u) [Category.{v} C]
    [HasFiniteProducts C] [HasEqualizers C] : HasFiniteLimits C :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

noncomputable abbrev example_5_1_30 : HasLimits CompHaus.{u} :=
  inferInstance

noncomputable abbrev example_5_1_31 (R : Type u) [Ring R] : HasFiniteLimits (ModuleCat.{u} R) :=
  inferInstance

def def_5_1_32 {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) : Prop :=
  Mono f

theorem example_5_1_33 {X Y : Type u} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f :=
  mono_iff_injective f

theorem example_5_1_34_grp {G H : GrpCat.{u}} (f : G ⟶ H) :
    Mono f ↔ Function.Injective f.hom :=
  GrpCat.mono_iff_injective f

theorem example_5_1_34_mod {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Mono f ↔ Function.Injective f.hom :=
  ModuleCat.mono_iff_injective f

theorem example_5_1_34_ring {R S : RingCat.{u}} (f : R ⟶ S) :
    Mono f ↔ Function.Injective f.hom :=
  ConcreteCategory.mono_iff_injective_of_preservesPullback f

theorem lemma_5_1_35 {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Nonempty (IsLimit (PullbackCone.mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) := by
  constructor
  · intro hf
    exact ⟨PullbackCone.isLimitMkIdId f⟩
  · rintro ⟨hlim⟩
    refine ⟨fun {Z} g h w => ?_⟩
    have hg : hlim.lift (PullbackCone.mk g h w) ≫ 𝟙 X = g :=
      hlim.fac (PullbackCone.mk g h w) WalkingCospan.left
    have hh : hlim.lift (PullbackCone.mk g h w) ≫ 𝟙 X = h :=
      hlim.fac (PullbackCone.mk g h w) WalkingCospan.right
    exact (hg.symm.trans hh)

noncomputable def exercise_5_1_37 {R : Type u} [Ring R] (X Y : ModuleCat.{u} R) :
    IsLimit (ModuleCat.binaryProductLimitCone X Y).cone :=
  (ModuleCat.binaryProductLimitCone X Y).isLimit

def exercise_5_1_38_converse {C : Type u} [Category.{v} C] {E X Y : C}
    {f g : X ⟶ Y} {i : E ⟶ X} (hi : i ≫ f = i ≫ g)
    (h : IsLimit (PullbackCone.mk i i hi : PullbackCone f g)) :
    IsLimit (Fork.ofι i hi) :=
  Fork.IsLimit.mk _
    (fun s => h.lift (PullbackCone.mk s.ι s.ι s.condition))
    (fun s => h.fac (PullbackCone.mk s.ι s.ι s.condition) WalkingCospan.left)
    (fun s m hm => by
      apply PullbackCone.IsLimit.hom_ext h
      · exact hm.trans (h.fac (PullbackCone.mk s.ι s.ι s.condition) WalkingCospan.left).symm
      · exact hm.trans (h.fac (PullbackCone.mk s.ι s.ι s.condition) WalkingCospan.right).symm)

noncomputable def exercise_5_1_39_paste {C : Type u} [Category.{v} C]
    {X₃ Y₁ Y₂ Y₃ : C} {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {i₃ : X₃ ⟶ Y₃}
    (t₂ : PullbackCone g₂ i₃) {i₂ : t₂.pt ⟶ Y₂} (t₁ : PullbackCone g₁ i₂) (hi₂ : i₂ = t₂.fst)
    (H : IsLimit t₂) (H' : IsLimit t₁) : IsLimit (t₂.pasteHoriz t₁ hi₂) :=
  pasteHorizIsPullback hi₂ H H'

noncomputable def exercise_5_1_39_left {C : Type u} [Category.{v} C]
    {X₃ Y₁ Y₂ Y₃ : C} {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {i₃ : X₃ ⟶ Y₃}
    (t₂ : PullbackCone g₂ i₃) {i₂ : t₂.pt ⟶ Y₂} (t₁ : PullbackCone g₁ i₂) (hi₂ : i₂ = t₂.fst)
    (H : IsLimit t₂) (H' : IsLimit (t₂.pasteHoriz t₁ hi₂)) : IsLimit t₁ :=
  leftSquareIsPullback t₁ (hi₂ := hi₂) H H'

theorem exercise_5_1_40a {I : Type u} [Category.{v} I] {C : Type u'} [Category.{v'} C]
    {D : I ⥤ C} {c : Cone D} (hc : IsLimit c) {A : C} {h h' : A ⟶ c.pt}
    (w : ∀ i : I, h ≫ c.π.app i = h' ≫ c.π.app i) : h = h' :=
  hc.hom_ext w

theorem exercise_5_1_40b {X Y : Type u} (x y : X × Y) (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) :
    x = y :=
  Prod.ext h₁ h₂

noncomputable def exercise_5_1_41 {I : Type u} [Category.{v} I] (D : I ⥤ Type u) :
    IsLimit (Types.limitCone D) :=
  Types.limitConeIsLimit D

abbrev exercise_5_1_42a (C : Type u) [Category.{v} C]
    [HasProducts.{w} C] [HasEqualizers C] : HasLimitsOfSize.{w, w} C :=
  has_limits_of_hasEqualizers_and_products

abbrev exercise_5_1_42b (C : Type u) [Category.{v} C]
    [HasFiniteProducts C] [HasEqualizers C] : HasFiniteLimits C :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

abbrev exercise_5_1_43 (C : Type u) [Category.{v} C]
    [HasTerminal C] [HasPullbacks C] : HasFiniteLimits C :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

theorem exercise_5_1_44a {A X X' : Type u} (m : X ⟶ A) (m' : X' ⟶ A)
    [hm : Mono m] [hm' : Mono m'] :
    Nonempty (Over.mk m ≅ Over.mk m') ↔ Set.range m = Set.range m' := by
  have hm_inj : Function.Injective m := (mono_iff_injective m).mp hm
  have hm'_inj : Function.Injective m' := (mono_iff_injective m').mp hm'
  constructor
  · rintro ⟨e⟩
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      have hw : m' (e.hom.left x) = m x := ConcreteCategory.congr_hom (Over.w e.hom) x
      exact ⟨e.hom.left x, hw⟩
    · rintro ⟨x', rfl⟩
      have hw : m (e.inv.left x') = m' x' := ConcreteCategory.congr_hom (Over.w e.inv) x'
      exact ⟨e.inv.left x', hw⟩
  · intro hrange
    have h_to : ∀ x : X, ∃ x' : X', m' x' = m x := by
      intro x
      have : m x ∈ Set.range m' := by
        rw [← hrange]
        exact ⟨x, rfl⟩
      exact this
    have h_inv : ∀ x' : X', ∃ x : X, m x = m' x' := by
      intro x'
      have : m' x' ∈ Set.range m := by
        rw [hrange]
        exact ⟨x', rfl⟩
      exact this
    choose to_fun h_to_eq using h_to
    choose inv_fun h_inv_eq using h_inv
    let hl : (Over.mk m).left ≅ (Over.mk m').left := {
      hom := ↾to_fun
      inv := ↾inv_fun
      hom_inv_id := by
        ext (x : X)
        change inv_fun (to_fun x) = x
        exact hm_inj (by rw [h_inv_eq (to_fun x), h_to_eq x])
      inv_hom_id := by
        ext (x' : X')
        change to_fun (inv_fun x') = x'
        exact hm'_inj (by rw [h_to_eq (inv_fun x'), h_inv_eq x'])
    }
    have hw : hl.hom ≫ m' = m := by
      ext (x : X)
      rw [TypeCat.Fun.toFun_apply, TypeCat.Fun.toFun_apply, types_comp, Function.comp_apply]
      change (ConcreteCategory.hom m') ((↾to_fun) x) = (ConcreteCategory.hom m) x
      rw [TypeCat.ofHom_apply]
      exact h_to_eq x
    exact ⟨Over.isoMk hl hw⟩

theorem exercise_5_1_45 {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Nonempty (IsLimit (PullbackCone.mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) :=
  lemma_5_1_35 f

theorem exercise_5_1_46 {C : Type u} [Category.{v} C] {X Y Z P : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {h : p₁ ≫ f = p₂ ≫ g}
    (c : IsLimit (PullbackCone.mk p₁ p₂ h)) [Mono g] : Mono p₁ :=
  PullbackCone.mono_fst_of_is_pullback_of_mono c

end LimitsAndExamples
