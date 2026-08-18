-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Biproducts

namespace ColimitsAndExamples

universe u v u' v' w

open CategoryTheory Limits

abbrev def_5_2_1_cocone {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    (D : I ⥤ A) := Cocone D

abbrev def_5_2_1_is_colimit {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D : I ⥤ A} (c : Cocone D) := IsColimit c

def def_5_2_1_has_colimit {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    (D : I ⥤ A) : Prop := HasColimit D

theorem lemma_5_2_1_unique {I : Type u} [Category.{v} I] {A : Type u'} [Category.{v'} A]
    {D : I ⥤ A} {c c' : Cocone D} (hc : IsColimit c) (hc' : IsColimit c') :
    ∃! e : c.pt ≅ c'.pt, ∀ i : I, c.ι.app i ≫ e.hom = c'.ι.app i := by
  refine ⟨hc.coconePointUniqueUpToIso hc',
    fun i => hc.comp_coconePointUniqueUpToIso_hom hc' i, fun e he => ?_⟩
  ext
  apply hc.hom_ext
  intro i
  rw [hc.comp_coconePointUniqueUpToIso_hom]
  exact he i

abbrev def_5_2_2_cofan {C : Type u} [Category.{v} C] (X Y : C) (P : C) (i₁ : X ⟶ P) (i₂ : Y ⟶ P) :
    BinaryCofan X Y := BinaryCofan.mk i₁ i₂

def def_5_2_2_is_coproduct {C : Type u} [Category.{v} C] {X Y P : C}
    (i₁ : X ⟶ P) (i₂ : Y ⟶ P) : Prop :=
  Nonempty (IsColimit (BinaryCofan.mk i₁ i₂))

def def_5_2_2_has_coproduct {C : Type u} [Category.{v} C] (X Y : C) : Prop :=
  HasBinaryCoproduct X Y

abbrev def_5_2_2_sum_cofan {C : Type u} [Category.{v} C] {I : Type w} (X : I → C)
    (P : C) (i : (j : I) → (X j ⟶ P)) : Cofan X :=
  Cofan.mk P i

def def_5_2_2_is_sum {C : Type u} [Category.{v} C] {I : Type w} {X : I → C}
    (c : Cofan X) : Prop :=
  Nonempty (IsColimit c)

def def_5_2_2_has_sum {C : Type u} [Category.{v} C] {I : Type w} (X : I → C) : Prop :=
  HasCoproduct X

theorem lemma_5_2_2_unique {C : Type u} [Category.{v} C] {X Y : C}
    {c c' : BinaryCofan X Y} (hc : IsColimit c) (hc' : IsColimit c') :
    ∃! e : c.pt ≅ c'.pt,
      BinaryCofan.inl c ≫ e.hom = BinaryCofan.inl c' ∧
      BinaryCofan.inr c ≫ e.hom = BinaryCofan.inr c' := by
  refine ⟨hc.coconePointUniqueUpToIso hc',
    ⟨hc.comp_coconePointUniqueUpToIso_hom hc' ⟨WalkingPair.left⟩,
     hc.comp_coconePointUniqueUpToIso_hom hc' ⟨WalkingPair.right⟩⟩, fun e he => ?_⟩
  ext
  apply BinaryCofan.IsColimit.hom_ext hc
  · rw [he.1, hc.comp_coconePointUniqueUpToIso_hom]
  · rw [he.2, hc.comp_coconePointUniqueUpToIso_hom]

def example_5_2_3 {C : Type u} [Category.{v} C] (I : C) :
    IsInitial I ≃ IsColimit (asEmptyCocone I) where
  toFun hI := hI
  invFun hC := hC
  left_inv _ := rfl
  right_inv _ := rfl

def example_5_2_4 (X Y : Type u) :
    IsColimit (Types.binaryCoproductCocone X Y) :=
  Types.binaryCoproductColimit X Y

noncomputable def example_5_2_4_fam {I : Type u} (X : I → Type u) :
    IsColimit (Types.coproductColimitCocone X).cocone :=
  (Types.coproductColimitCocone X).isColimit

noncomputable abbrev example_5_2_5 (R : Type u) [Ring R] (X Y : ModuleCat.{u} R) :
    HasBinaryCoproduct X Y :=
  inferInstance

theorem example_5_2_6_join {α : Type u} [SemilatticeSup α] (x y : α) :
    x ≤ x ⊔ y ∧ y ≤ x ⊔ y ∧ ∀ a, x ≤ a → y ≤ a → x ⊔ y ≤ a :=
  ⟨le_sup_left, le_sup_right, fun _ => sup_le⟩

theorem example_5_2_6_complete {α : Type u} [CompleteLattice α] {I : Type w} (x : I → α) :
    (∀ i, x i ≤ ⨆ j, x j) ∧ (∀ a, (∀ i, x i ≤ a) → ⨆ j, x j ≤ a) :=
  ⟨fun i => le_iSup x i, fun _ => iSup_le⟩

theorem example_5_2_6_set {S : Type u} (X Y : Set S) :
    X ⊆ X ∪ Y ∧ Y ⊆ X ∪ Y ∧ ∀ A, X ⊆ A → Y ⊆ A → X ∪ Y ⊆ A :=
  ⟨Set.subset_union_left, Set.subset_union_right, fun _ => Set.union_subset⟩

theorem example_5_2_6_lcm (x y : ℕ) :
    x ∣ x.lcm y ∧ y ∣ x.lcm y ∧ ∀ a, x ∣ a → y ∣ a → x.lcm y ∣ a :=
  ⟨Nat.dvd_lcm_left x y, Nat.dvd_lcm_right x y, fun _ => Nat.lcm_dvd⟩

theorem example_5_2_6_least_nat_div (n : ℕ) : 1 ∣ n :=
  one_dvd n

theorem example_5_2_6_least_set {S : Type u} (X : Set S) : (∅ : Set S) ⊆ X :=
  Set.empty_subset X

abbrev def_5_2_7_cofork {C : Type u} [Category.{v} C] {X Y : C} (s t : X ⟶ Y)
    (Q : C) (p : Y ⟶ Q) (h : s ≫ p = t ≫ p) : Cofork s t :=
  Cofork.ofπ p h

def def_5_2_7_is_coequalizer {C : Type u} [Category.{v} C] {X Y : C} {s t : X ⟶ Y}
    (c : Cofork s t) : Prop :=
  Nonempty (IsColimit c)

def def_5_2_7_has_coequalizer {C : Type u} [Category.{v} C] {X Y : C} (s t : X ⟶ Y) : Prop :=
  HasCoequalizer s t

theorem theorem_5_2_8_quotient_lift {A : Type u} (r : A → A → Prop) {B : Type v}
    (f : A → B) (h : ∀ a b, r a b → f a = f b) :
    ∃! g : Quot r → B, ∀ a : A, g (Quot.mk r a) = f a := by
  refine ⟨Quot.lift f h, fun _ => rfl, fun g' hg' => ?_⟩
  ext q
  induction q using Quot.ind with
  | mk a => exact hg' a

def example_5_2_9 {X Y : Type u} (s t : X ⟶ Y) :
    IsColimit (Cofork.ofπ (f := s) (g := t)
      (↾fun (y : Y) => Quot.mk (fun a b => ∃ x : X, s x = a ∧ t x = b) y)
      (by
        ext x
        apply Quot.sound
        exact ⟨x, rfl, rfl⟩)) :=
  Cofork.IsColimit.mk _
    (fun s' => ↾fun q => Quot.lift (fun y => s'.π y)
      (by
        rintro a b ⟨x, rfl, rfl⟩
        exact ConcreteCategory.congr_hom s'.condition x) q)
    (fun _ => rfl)
    (fun s' m hm => by
      ext q
      induction q using Quot.ind with
      | mk y => exact ConcreteCategory.congr_hom hm y)

noncomputable abbrev example_5_2_9_hasCoequalizer {X Y : Type u} (s t : X ⟶ Y) :
    HasCoequalizer s t :=
  inferInstance

noncomputable abbrev example_5_2_10 {A B : AddCommGrpCat.{u}} (s t : A ⟶ B) :
    HasCoequalizer s t :=
  inferInstance

noncomputable abbrev example_5_2_10_mod {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (s t : M ⟶ N) : HasCoequalizer s t :=
  inferInstance

abbrev def_5_2_11_cocone {C : Type u} [Category.{v} C] {X Y Z : C}
    (s : X ⟶ Y) (t : X ⟶ Z) (P : C) (i₁ : Y ⟶ P) (i₂ : Z ⟶ P) (h : s ≫ i₁ = t ≫ i₂) :
    PushoutCocone s t :=
  PushoutCocone.mk i₁ i₂ h

def def_5_2_11_is_pushout {C : Type u} [Category.{v} C] {X Y Z : C}
    {s : X ⟶ Y} {t : X ⟶ Z} (c : PushoutCocone s t) : Prop :=
  Nonempty (IsColimit c)

def def_5_2_11_has_pushout {C : Type u} [Category.{v} C] {X Y Z : C}
    (s : X ⟶ Y) (t : X ⟶ Z) : Prop :=
  HasPushout s t

noncomputable abbrev example_5_2_12 {X Y Z : Type u} (f : X ⟶ Y) (g : X ⟶ Z) :
    HasPushout f g :=
  inferInstance

def example_5_2_12_isColimit {X Y Z : Type u} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsColimit (Types.Pushout.cocone f g) :=
  Types.Pushout.isColimitCocone f g

def example_5_2_13 {C : Type u} [Category.{v} C] {Y Z P : C} {i₁ : Y ⟶ P} {i₂ : Z ⟶ P}
    {I : C} (hI : IsInitial I) (f : I ⟶ Y) (g : I ⟶ Z) :
    IsColimit (PushoutCocone.mk i₁ i₂ (hI.hom_ext (f ≫ i₁) (g ≫ i₂))) ≃
    IsColimit (BinaryCofan.mk i₁ i₂) where
  toFun hc :=
    BinaryCofan.IsColimit.mk _
      (fun {T} f₁ f₂ => hc.desc (PushoutCocone.mk f₁ f₂ (hI.hom_ext _ _)))
      (fun {T} f₁ f₂ => hc.fac (PushoutCocone.mk f₁ f₂ (hI.hom_ext _ _)) WalkingSpan.left)
      (fun {T} f₁ f₂ => hc.fac (PushoutCocone.mk f₁ f₂ (hI.hom_ext _ _)) WalkingSpan.right)
      (fun {T} f₁ f₂ m hm₁ hm₂ => by
        apply PushoutCocone.IsColimit.hom_ext hc
        · exact hm₁.trans (hc.fac (PushoutCocone.mk f₁ f₂ (hI.hom_ext _ _)) WalkingSpan.left).symm
        · exact hm₂.trans (hc.fac (PushoutCocone.mk f₁ f₂ (hI.hom_ext _ _))
            WalkingSpan.right).symm)
  invFun hc :=
    PushoutCocone.IsColimit.mk _
      (fun s => hc.desc (BinaryCofan.mk (PushoutCocone.inl s) (PushoutCocone.inr s)))
      (fun s => hc.fac (BinaryCofan.mk (PushoutCocone.inl s) (PushoutCocone.inr s))
        ⟨WalkingPair.left⟩)
      (fun s => hc.fac (BinaryCofan.mk (PushoutCocone.inl s) (PushoutCocone.inr s))
        ⟨WalkingPair.right⟩)
      (fun s m hm₁ hm₂ => by
        apply BinaryCofan.IsColimit.hom_ext hc
        · exact hm₁.trans (hc.fac (BinaryCofan.mk (PushoutCocone.inl s) (PushoutCocone.inr s))
            ⟨WalkingPair.left⟩).symm
        · exact hm₂.trans (hc.fac (BinaryCofan.mk (PushoutCocone.inl s) (PushoutCocone.inr s))
            ⟨WalkingPair.right⟩).symm)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

noncomputable abbrev example_5_2_14_top : HasPushouts TopCat.{u} :=
  inferInstance

noncomputable abbrev example_5_2_14_ab : HasPushouts AddCommGrpCat.{u} :=
  inferInstance

noncomputable abbrev example_5_2_15 (C : Type u) [Category.{v} C]
    [HasColimitsOfShape ℕ C] (D : ℕ ⥤ C) : HasColimit D :=
  inferInstance

noncomputable abbrev example_5_2_16 {I : Type u} [Category.{v} I] (D : I ⥤ Type u) :
    HasColimit D :=
  inferInstance

noncomputable def example_5_2_16_isColimit {I : Type u} [Category.{v} I] (D : I ⥤ Type u) :
    IsColimit (Types.colimitCocone D) :=
  Types.colimitCoconeIsColimit D

def def_5_2_17 {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) : Prop :=
  Epi f

theorem example_5_2_18_epi {X Y : Type u} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f :=
  epi_iff_surjective f

theorem example_5_2_18_iso {X Y : Type u} (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective f :=
  isIso_iff_bijective f

theorem example_5_2_19_grp {G H : GrpCat.{u}} (f : G ⟶ H) :
    Epi f ↔ Function.Surjective f.hom :=
  GrpCat.epi_iff_surjective f

theorem example_5_2_19_mod {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Epi f ↔ Function.Surjective f.hom :=
  ModuleCat.epi_iff_surjective f

theorem example_5_2_20 {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [T2Space Z] {f : X → Y} (hf : DenseRange f) {g₁ g₂ : Y → Z}
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (h : g₁ ∘ f = g₂ ∘ f) : g₁ = g₂ :=
  DenseRange.equalizer hf hg₁ hg₂ h

theorem lemma_5_2_21 {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Nonempty (IsColimit (PushoutCocone.mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f)) := by
  constructor
  · intro hf
    exact ⟨PushoutCocone.isColimitMkIdId f⟩
  · rintro ⟨hcolim⟩
    refine ⟨fun {Z} g h w => ?_⟩
    have hg : 𝟙 Y ≫ hcolim.desc (PushoutCocone.mk g h w) = g :=
      hcolim.fac (PushoutCocone.mk g h w) WalkingSpan.left
    have hh : 𝟙 Y ≫ hcolim.desc (PushoutCocone.mk g h w) = h :=
      hcolim.fac (PushoutCocone.mk g h w) WalkingSpan.right
    rw [Category.id_comp] at hg hh
    exact hg.symm.trans hh

theorem exercise_5_2_23_equalizer {C : Type u} [Category.{v} C] {X Y : C} {s t : X ⟶ Y}
    {c : Fork s t} (hc : IsLimit c) :
    IsIso c.ι ↔ s = t := by
  constructor
  · intro hi
    haveI := hi
    have h : c.ι ≫ s = c.ι ≫ t := c.condition
    exact (cancel_epi c.ι).1 h
  · intro hst
    subst hst
    let f : Fork s s := Fork.ofι (𝟙 X) rfl
    have hf : IsLimit f := Fork.IsLimit.mk _ (fun s' => s'.ι) (fun _ => Category.comp_id _)
      (fun s' m hm => by
        calc
          m = m ≫ 𝟙 X := (Category.comp_id m).symm
          _ = m ≫ f.ι := rfl
          _ = s'.ι := hm)
    have h_fac := hc.conePointUniqueUpToIso_hom_comp hf WalkingParallelPair.zero
    have hi : c.ι = (hc.conePointUniqueUpToIso hf).hom := by
      calc
        c.ι = (hc.conePointUniqueUpToIso hf).hom ≫ 𝟙 X := h_fac.symm
        _ = (hc.conePointUniqueUpToIso hf).hom := Category.comp_id _
    rw [hi]
    infer_instance

theorem exercise_5_2_23_coequalizer {C : Type u} [Category.{v} C] {X Y : C} {s t : X ⟶ Y}
    {c : Cofork s t} (hc : IsColimit c) :
    IsIso c.π ↔ s = t := by
  constructor
  · intro hi
    haveI := hi
    have h : s ≫ c.π = t ≫ c.π := c.condition
    exact (cancel_mono c.π).1 h
  · intro hst
    subst hst
    let f : Cofork s s := Cofork.ofπ (𝟙 Y) rfl
    have hf : IsColimit f := Cofork.IsColimit.mk _ (fun s' => s'.π) (fun _ => Category.id_comp _)
      (fun s' m hm => by
        calc
          m = 𝟙 Y ≫ m := (Category.id_comp m).symm
          _ = f.π ≫ m := rfl
          _ = s'.π := hm)
    let e := hc.coconePointUniqueUpToIso hf
    have h_fac : c.π ≫ e.hom = 𝟙 Y :=
      hc.comp_coconePointUniqueUpToIso_hom hf WalkingParallelPair.one
    have hi : c.π = e.inv := by
      calc
        c.π = c.π ≫ 𝟙 c.pt := (Category.comp_id c.π).symm
        _ = c.π ≫ (e.hom ≫ e.inv) := by rw [e.hom_inv_id]
        _ = (c.π ≫ e.hom) ≫ e.inv := by rw [Category.assoc]
        _ = 𝟙 Y ≫ e.inv := congrArg (· ≫ e.inv) h_fac
        _ = e.inv := Category.id_comp _
    rw [hi]
    infer_instance

def exercise_5_2_24_set {X : Type u} (f : X ⟶ X) :
    IsColimit (Cofork.ofπ (f := f) (g := 𝟙 X)
      (↾fun (x : X) => Quot.mk (fun a b => f a = b ∨ f b = a) x)
      (by
        ext x
        apply Quot.sound
        exact Or.inr rfl)) :=
  Cofork.IsColimit.mk _
    (fun s => ↾fun q => Quot.lift (fun x => s.π x)
      (by
        rintro a b (h | h)
        · have hw := ConcreteCategory.congr_hom s.condition a
          have hw' : s.π (f a) = s.π a := hw
          exact hw'.symm.trans (congrArg s.π h)
        · have hw := ConcreteCategory.congr_hom s.condition b
          have hw' : s.π (f b) = s.π b := hw
          exact (congrArg s.π h).symm.trans hw') q)
    (fun _ => rfl)
    (fun s m hm => by
      ext q
      induction q using Quot.ind with
      | mk x => exact ConcreteCategory.congr_hom hm x)

theorem exercise_5_2_25_monoid {M : Type u} [AddMonoid M] (g g' : ℤ →+ M)
    (h : ∀ (n : ℕ), g n = g' n) : g = g' := by
  apply AddMonoidHom.ext
  intro z
  cases z with
  | ofNat n => exact h n
  | negSucc n =>
    have h1 : g (n + 1 : ℤ) + g (Int.negSucc n) = 0 := by
      rw [← map_add]
      have : (n + 1 : ℤ) + Int.negSucc n = 0 := by
        change (n + 1 : ℤ) + -(n + 1 : ℤ) = 0
        exact add_neg_cancel (n + 1 : ℤ)
      rw [this, map_zero]
    have h2 : g (Int.negSucc n) + g (n + 1 : ℤ) = 0 := by
      rw [← map_add]
      have : Int.negSucc n + (n + 1 : ℤ) = 0 := by
        change -(n + 1 : ℤ) + (n + 1 : ℤ) = 0
        exact neg_add_cancel (n + 1 : ℤ)
      rw [this, map_zero]
    have h1' : g' (n + 1 : ℤ) + g' (Int.negSucc n) = 0 := by
      rw [← map_add]
      have : (n + 1 : ℤ) + Int.negSucc n = 0 := by
        change (n + 1 : ℤ) + -(n + 1 : ℤ) = 0
        exact add_neg_cancel (n + 1 : ℤ)
      rw [this, map_zero]
    have h_eq : g (n + 1 : ℤ) = g' (n + 1 : ℤ) := h (n + 1)
    calc
      g (Int.negSucc n) = g (Int.negSucc n) + 0 := by rw [add_zero]
      _ = g (Int.negSucc n) + (g' (n + 1 : ℤ) + g' (Int.negSucc n)) := by rw [h1']
      _ = g (Int.negSucc n) + (g (n + 1 : ℤ) + g' (Int.negSucc n)) := by rw [h_eq]
      _ = (g (Int.negSucc n) + g (n + 1 : ℤ)) + g' (Int.negSucc n) := by rw [add_assoc]
      _ = 0 + g' (Int.negSucc n) := by rw [h2]
      _ = g' (Int.negSucc n) := by rw [zero_add]

theorem exercise_5_2_25_monoid_not_surj : ¬ Function.Surjective (fun (n : ℕ) => (n : ℤ)) := by
  intro hsurj
  rcases hsurj (-1) with ⟨n, hn⟩
  dsimp at hn
  have : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg n
  rw [hn] at this
  revert this
  decide

theorem exercise_5_2_25_ring {R : Type u} [Ring R] (g g' : ℚ →+* R) : g = g' :=
  RingHom.ext_rat g g'

theorem exercise_5_2_25_ring_epi : Epi (RingCat.ofHom (Int.castRingHom ℚ)) := by
  constructor
  intro R g h w
  apply RingCat.hom_ext
  exact RingHom.ext_rat _ _

theorem exercise_5_2_25_ring_not_surj : ¬ Function.Surjective (fun (n : ℤ) => (n : ℚ)) := by
  intro hsurj
  rcases hsurj (1 / 2) with ⟨n, hn⟩
  dsimp at hn
  have h2 : (2 : ℚ) * (n : ℚ) = (2 : ℚ) * (1 / 2) := by rw [hn]
  rw [mul_one_div_cancel (by decide : (2 : ℚ) ≠ 0)] at h2
  have h_int : (2 * n : ℤ) = 1 := by
    exact_mod_cast h2
  have hzero : (2 * n : ℤ) % 2 = 0 :=
    Int.mul_emod_right 2 n
  have hone : (1 : ℤ) % 2 = 1 := rfl
  rw [h_int, hone] at hzero
  revert hzero
  decide

theorem exercise_5_2_26a {A X X' : Type u} (e : A ⟶ X) (e' : A ⟶ X')
    [he : Epi e] [he' : Epi e'] :
    Nonempty (Under.mk e ≅ Under.mk e') ↔ (∀ a₁ a₂, e a₁ = e a₂ ↔ e' a₁ = e' a₂) := by
  have he_surj : Function.Surjective e := (epi_iff_surjective e).mp he
  have he'_surj : Function.Surjective e' := (epi_iff_surjective e').mp he'
  constructor
  · rintro ⟨iso⟩
    intro a₁ a₂
    have hw : e ≫ iso.hom.right = e' := Under.w iso.hom
    have hw_inv : e' ≫ iso.inv.right = e := Under.w iso.inv
    constructor
    · intro h
      have : (e ≫ iso.hom.right) a₁ = (e ≫ iso.hom.right) a₂ := by
        simp only [types_comp, Function.comp_apply, h]
      rw [hw] at this
      exact this
    · intro h
      have : (e' ≫ iso.inv.right) a₁ = (e' ≫ iso.inv.right) a₂ := by
        simp only [types_comp, Function.comp_apply, h]
      rw [hw_inv] at this
      exact this
  · intro heq
    have h_to : ∀ x : X, ∃ x' : X', ∀ a : A, e a = x → e' a = x' := by
      intro x
      rcases he_surj x with ⟨a, rfl⟩
      exact ⟨e' a, fun a' ha' => (heq a' a).mp ha'⟩
    have h_inv : ∀ x' : X', ∃ x : X, ∀ a : A, e' a = x' → e a = x := by
      intro x'
      rcases he'_surj x' with ⟨a, rfl⟩
      exact ⟨e a, fun a' ha' => (heq a' a).mpr ha'⟩
    choose to_fun h_to_eq using h_to
    choose inv_fun h_inv_eq using h_inv
    let hl : (Under.mk e).right ≅ (Under.mk e').right := {
      hom := ↾to_fun
      inv := ↾inv_fun
      hom_inv_id := by
        ext (x : X)
        rcases he_surj x with ⟨a, rfl⟩
        have h1 : to_fun (e a) = e' a := (h_to_eq (e a) a rfl).symm
        have h2 : inv_fun (e' a) = e a := (h_inv_eq (e' a) a rfl).symm
        change inv_fun (to_fun (e a)) = e a
        rw [h1, h2]
      inv_hom_id := by
        ext (x' : X')
        rcases he'_surj x' with ⟨a, rfl⟩
        have h1 : inv_fun (e' a) = e a := (h_inv_eq (e' a) a rfl).symm
        have h2 : to_fun (e a) = e' a := (h_to_eq (e a) a rfl).symm
        change to_fun (inv_fun (e' a)) = e' a
        rw [h1, h2]
    }
    have hw : e ≫ hl.hom = e' := by
      ext (a : A)
      change (ConcreteCategory.hom hl.hom) (e a) = e' a
      rw [TypeCat.ofHom_apply]
      exact (h_to_eq (e a) a rfl).symm
    exact ⟨Under.isoMk hl hw⟩

theorem exercise_5_2_27a_split_to_reg {C : Type u} [Category.{v} C] {X Y : C}
    (f : X ⟶ Y) [IsSplitMono f] : IsRegularMono f :=
  inferInstance

theorem exercise_5_2_27a_reg_to_mono {C : Type u} [Category.{v} C] {X Y : C}
    (f : X ⟶ Y) [IsRegularMono f] : Mono f :=
  inferInstance

abbrev exercise_5_2_27b_ab : IsRegularMonoCategory AddCommGrpCat.{u} :=
  inferInstance

theorem exercise_5_2_27b_not_all_split :
    ¬ ∀ (f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ), Mono f → IsSplitMono f := by
  intro hall
  let two_mul_hom : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
    AddCommGrpCat.ofHom (AddMonoidHom.mulLeft 2)
  have hmono : Mono two_mul_hom := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y h
    dsimp [two_mul_hom] at h
    exact mul_left_cancel₀ (by decide) h
  have hsplit : IsSplitMono two_mul_hom := hall two_mul_hom hmono
  have hw := ConcreteCategory.congr_hom (IsSplitMono.id two_mul_hom) 1
  dsimp [two_mul_hom] at hw
  have h2 : (retraction two_mul_hom).hom (2 * 1 : ℤ) = 1 := hw
  have h_hom : (retraction two_mul_hom).hom (2 * 1 : ℤ) = 2 * (retraction two_mul_hom).hom 1 := by
    have h11 : (2 * 1 : ℤ) = 1 + 1 := rfl
    rw [h11, map_add]
    exact (two_mul ((retraction two_mul_hom).hom 1)).symm
  rw [h_hom] at h2
  have hzero : (2 * (retraction two_mul_hom).hom 1 : ℤ) % 2 = 0 :=
    Int.mul_emod_right 2 ((retraction two_mul_hom).hom 1)
  have hone : (1 : ℤ) % 2 = 1 := rfl
  rw [h2, hone] at hzero
  revert hzero
  decide

theorem exercise_5_2_28a {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ Mono f ∧ IsRegularEpi f := by
  constructor
  · intro h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hmono, hreg⟩
    haveI := hmono
    exact isIso_of_regularEpi_of_mono f (IsRegularEpi.getStruct f)

theorem exercise_5_2_28b_epi_iff_regular {X Y : Type u} (f : X ⟶ Y) :
    Epi f ↔ IsRegularEpi f := by
  constructor
  · intro h
    haveI := h
    haveI : IsSplitEpi f := isSplitEpi_of_epi f
    infer_instance
  · intro h
    haveI := h
    infer_instance

theorem exercise_5_2_28b_regular_iff_split {X Y : Type u} (f : X ⟶ Y) :
    IsRegularEpi f ↔ IsSplitEpi f := by
  constructor
  · intro h
    haveI := h
    haveI : Epi f := inferInstance
    exact isSplitEpi_of_epi f
  · intro h
    haveI := h
    infer_instance

def zmod2_proj : Multiplicative ℤ →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd ((Multiplicative.toAdd x : ℤ) : ZMod 2)
  map_one' := by
    change Multiplicative.ofAdd ((0 : ℤ) : ZMod 2) = 1
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (((Multiplicative.toAdd (x * y) : ℤ) : ZMod 2)) =
      Multiplicative.ofAdd ((Multiplicative.toAdd x : ℤ) : ZMod 2) *
      Multiplicative.ofAdd ((Multiplicative.toAdd y : ℤ) : ZMod 2)
    rw [toAdd_mul, Int.cast_add, ofAdd_add]

theorem exercise_5_2_28c_grp_not_all_split :
    ¬ ∀ {G H : GrpCat.{0}} (f : G ⟶ H), Epi f → IsSplitEpi f := by
  intro hall
  let G : GrpCat.{0} := GrpCat.of (Multiplicative ℤ)
  let H : GrpCat.{0} := GrpCat.of (Multiplicative (ZMod 2))
  let f : G ⟶ H := GrpCat.ofHom zmod2_proj
  have hepi : Epi f := by
    rw [GrpCat.epi_iff_surjective]
    intro y
    have hy : Multiplicative.toAdd y = (0 : ZMod 2) ∨ Multiplicative.toAdd y = (1 : ZMod 2) := by
      generalize Multiplicative.toAdd y = z
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hy with h | h
    · refine ⟨Multiplicative.ofAdd (0 : ℤ), ?_⟩
      change Multiplicative.ofAdd ((0 : ℤ) : ZMod 2) = y
      rw [Int.cast_zero, ← h]
      rfl
    · refine ⟨Multiplicative.ofAdd (1 : ℤ), ?_⟩
      change Multiplicative.ofAdd ((1 : ℤ) : ZMod 2) = y
      rw [Int.cast_one, ← h]
      rfl
  have hsplit : IsSplitEpi f := hall f hepi
  have hw := ConcreteCategory.congr_hom (IsSplitEpi.id f) (Multiplicative.ofAdd (1 : ZMod 2))
  dsimp [f] at hw
  have h_two : (Multiplicative.ofAdd (1 : ZMod 2)) * (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := rfl
  have h_hom_two : (section_ f).hom
      ((Multiplicative.ofAdd (1 : ZMod 2)) * (Multiplicative.ofAdd (1 : ZMod 2))) = 1 := by
    rw [h_two, map_one]
  rw [map_mul] at h_hom_two
  have hk_def : ∃ (k : ℤ),
      (section_ f).hom (Multiplicative.ofAdd (1 : ZMod 2)) = Multiplicative.ofAdd k :=
    ⟨Multiplicative.toAdd ((section_ f).hom (Multiplicative.ofAdd (1 : ZMod 2))), rfl⟩
  rcases hk_def with ⟨k, hk⟩
  have h_add : Multiplicative.ofAdd (k + k) = (1 : Multiplicative ℤ) := by
    calc
      Multiplicative.ofAdd (k + k) = Multiplicative.ofAdd k * Multiplicative.ofAdd k :=
        ofAdd_add k k
      _ = (section_ f).hom (Multiplicative.ofAdd (1 : ZMod 2)) *
          (section_ f).hom (Multiplicative.ofAdd (1 : ZMod 2)) := by rw [hk]
      _ = 1 := h_hom_two
  have hk_zero : k + k = 0 := Multiplicative.ofAdd.injective h_add
  have h_mul : 2 * k = 0 := by rw [two_mul, hk_zero]
  have hk0 : k = 0 := mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (h_mul.trans (mul_zero 2).symm)
  have h_one : (section_ f).hom (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
    rw [hk, hk0]
    rfl
  have hw_app : zmod2_proj ((section_ f).hom (Multiplicative.ofAdd (1 : ZMod 2))) =
      Multiplicative.ofAdd (1 : ZMod 2) := hw
  rw [h_one, map_one] at hw_app
  have : (0 : ZMod 2) = 1 := congrArg Multiplicative.toAdd hw_app
  revert this
  decide

theorem exercise_5_2_29_comp_mono {C : Type u} [Category.{v} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] : Mono (f ≫ g) :=
  inferInstance

theorem exercise_5_2_29_comp_split_mono {C : Type u} [Category.{v} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsSplitMono f] [IsSplitMono g] : IsSplitMono (f ≫ g) :=
  inferInstance

theorem exercise_5_2_29_comp_epi {C : Type u} [Category.{v} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] [Epi g] : Epi (f ≫ g) :=
  inferInstance

theorem exercise_5_2_29_comp_split_epi {C : Type u} [Category.{v} C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsSplitEpi f] [IsSplitEpi g] : IsSplitEpi (f ≫ g) :=
  inferInstance

theorem exercise_5_2_29_pb_mono {C : Type u} [Category.{v} C] {X Y Z P : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {h : p₁ ≫ f = p₂ ≫ g}
    (c : IsLimit (PullbackCone.mk p₁ p₂ h)) [Mono g] : Mono p₁ :=
  PullbackCone.mono_fst_of_is_pullback_of_mono c

def exercise_5_2_29_pb_reg_mono {C : Type u} [Category.{v} C] {X Y Z P : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {h : p₁ ≫ f = p₂ ≫ g}
    (hr : RegularMono g) (c : IsLimit (PullbackCone.mk p₁ p₂ h)) : RegularMono p₁ :=
  regularOfIsPullbackFstOfRegular hr h c

end ColimitsAndExamples
