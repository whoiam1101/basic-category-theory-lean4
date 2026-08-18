-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.Functors
import BasicCategoryTheory.Chapter1_CategoriesFunctorsAndNaturalTransformations.NaturalTransformations
import BasicCategoryTheory.Chapter2_Adjoints.Adjoints
import BasicCategoryTheory.Chapter4_Representables.DefinitionsAndExamples
import BasicCategoryTheory.Chapter4_Representables.YonedaLemma
import BasicCategoryTheory.Chapter4_Representables.ConsequencesOfTheYonedaLemma
import BasicCategoryTheory.Chapter5_Limits.LimitsAndExamples
import BasicCategoryTheory.Chapter5_Limits.ColimitsAndExamples
import BasicCategoryTheory.Chapter5_Limits.InteractionsBetweenFunctorsAndLimits
import BasicCategoryTheory.Chapter6_AdjointsRepresentablesAndLimits.LimitsInTermsOfRepresentablesAndAdjoints

namespace LimitsAndColimitsOfPresheaves

universe u v u' v' u'' v'' w

open CategoryTheory Limits Opposite

noncomputable def def_6_2_1_prod_iso {A : Type u} [Category.{v} A] [HasBinaryProducts A]
    (X Y : A) (W : A) :
    (W ⟶ X ⨯ Y) ≃ (W ⟶ X) × (W ⟶ Y) where
  toFun f := (f ≫ prod.fst, f ≫ prod.snd)
  invFun := fun (f, g) => prod.lift f g
  left_inv f := by
    apply prod.hom_ext
    · rw [prod.lift_fst]
    · rw [prod.lift_snd]
  right_inv := fun (f, g) => by
    dsimp
    ext
    · rw [prod.lift_fst]
    · rw [prod.lift_snd]

noncomputable def def_6_2_2_equalizer_iso {A : Type u} [Category.{v} A] [HasEqualizers A] {X Y : A}
    (s t : X ⟶ Y) (W : A) :
    (W ⟶ equalizer s t) ≃ {f : W ⟶ X // f ≫ s = f ≫ t} where
  toFun f := ⟨f ≫ equalizer.ι s t, by rw [Category.assoc, equalizer.condition, ← Category.assoc]⟩
  invFun := fun ⟨f, hf⟩ => equalizer.lift f hf
  left_inv f := by
    apply equalizer.hom_ext
    rw [equalizer.lift_ι]
  right_inv := fun ⟨f, hf⟩ => by
    apply Subtype.ext
    dsimp
    rw [equalizer.lift_ι]

def lemma_6_2_1_cone_equiv_sections {I : Type v} [SmallCategory I] {A : Type u} [Category.{v} A]
    (D : I ⥤ A) (W : A) :
    ((Functor.const I).obj W ⟶ D) ≃ (D ⋙ coyoneda.obj (op W)).sections where
  toFun π := ⟨fun j => π.app j, fun {j j'} f => by
    dsimp
    have h := π.naturality f
    dsimp at h
    rw [Category.id_comp] at h
    exact h.symm⟩
  invFun s := {
    app := fun j => s.val j
    naturality := fun j j' f => by
      dsimp
      rw [Category.id_comp]
      exact (s.property f).symm
  }
  left_inv π := by
    ext j
    rfl
  right_inv s := by
    ext j
    rfl

noncomputable def lemma_6_2_1_cone_iso_limit {I : Type v} [SmallCategory I]
    {A : Type u} [Category.{v} A] (D : I ⥤ A) (W : A) :
    ((Functor.const I).obj W ⟶ D) ≅ (limit (D ⋙ coyoneda.obj (op W)) : Type v) :=
  (lemma_6_2_1_cone_equiv_sections D W).trans
    (Types.limitEquivSections (D ⋙ coyoneda.obj (op W))).symm |>.toIso

@[reducible]
noncomputable def proposition_6_2_2_preservesLimits {A : Type u} [Category.{v} A] (X : Aᵒᵖ) :
    PreservesLimits (coyoneda.obj X : A ⥤ Type v) :=
  inferInstance

@[reducible]
noncomputable def proposition_6_2_2_dual_preservesLimits {A : Type u} [Category.{v} A] (X : A) :
    PreservesLimits (yoneda.obj X : Aᵒᵖ ⥤ Type v) :=
  inferInstance

noncomputable def remark_6_2_2_coprod_iso {A : Type u} [Category.{v} A]
    [HasBinaryCoproducts A] (X Y : A) (W : A) :
    (X ⨿ Y ⟶ W) ≃ (X ⟶ W) × (Y ⟶ W) where
  toFun f := (coprod.inl ≫ f, coprod.inr ≫ f)
  invFun := fun (f, g) => coprod.desc f g
  left_inv f := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc]
    · rw [coprod.inr_desc]
  right_inv := fun (f, g) => by
    dsimp
    ext
    · rw [coprod.inl_desc]
    · rw [coprod.inr_desc]

abbrev def_6_2_evaluation (A : Type u) [Category.{v} A] (S : Type u') [Category.{v'} S] :
    A ⥤ (A ⥤ S) ⥤ S :=
  evaluation A S

abbrev def_6_2_evaluation_obj {A : Type u} [Category.{v} A] {S : Type u'} [Category.{v'} S]
    (a : A) :
    (A ⥤ S) ⥤ S :=
  (evaluation A S).obj a

def theorem_6_2_3_isLimit_of_evaluation_isLimit {I : Type w} [Category.{w} I]
    {A : Type u} [Category.{v} A] {S : Type u'} [Category.{v'} S]
    {D : I ⥤ A ⥤ S} (c : Cone D)
    (hc : ∀ (a : A), IsLimit (((evaluation A S).obj a).mapCone c)) :
    IsLimit c :=
  evaluationJointlyReflectsLimits c hc

noncomputable def theorem_6_2_3_evaluation_isLimit {I : Type w} [Category.{w} I]
    {A : Type u} [Category.{v} A] {S : Type u'} [Category.{v'} S]
    {D : I ⥤ A ⥤ S} (c : Cone D) (hc : IsLimit c) (a : A)
    [PreservesLimit D ((evaluation A S).obj a)] :
    IsLimit (((evaluation A S).obj a).mapCone c) :=
  isLimitOfPreserves ((evaluation A S).obj a) hc

@[reducible]
noncomputable def corollary_6_2_4_hasLimitsOfShape {I : Type w} [Category.{w} I]
    {A : Type u} [Category.{v} A] {S : Type u'} [Category.{v'} S]
    [HasLimitsOfShape I S] :
    HasLimitsOfShape I (A ⥤ S) :=
  functorCategoryHasLimitsOfShape

@[reducible]
noncomputable def corollary_6_2_4_hasColimitsOfShape {I : Type w} [Category.{w} I]
    {A : Type u} [Category.{v} A] {S : Type u'} [Category.{v'} S]
    [HasColimitsOfShape I S] :
    HasColimitsOfShape I (A ⥤ S) :=
  functorCategoryHasColimitsOfShape

@[reducible]
noncomputable def corollary_6_2_4_preservesLimitsOfShape {I : Type w} [Category.{w} I]
    {A : Type u} [Category.{v} A] {S : Type u'} [Category.{v'} S]
    [HasLimitsOfShape I S] (a : A) :
    PreservesLimitsOfShape I ((evaluation A S).obj a) :=
  inferInstance

@[reducible]
noncomputable def corollary_6_2_4_preservesColimitsOfShape {I : Type w} [Category.{w} I]
    {A : Type u} [Category.{v} A] {S : Type u'} [Category.{v'} S]
    [HasColimitsOfShape I S] (a : A) :
    PreservesColimitsOfShape I ((evaluation A S).obj a) :=
  inferInstance

noncomputable def proposition_6_2_5_limits_commute_left {J : Type u} [Category.{v} J]
    {K : Type u'} [Category.{v'} K] {C : Type u''} [Category.{v''} C]
    [HasLimitsOfShape J C] [HasLimitsOfShape K C] (G : J × K ⥤ C) :
    limit G ≅ limit (Functor.curry.obj G ⋙ lim) :=
  limitIsoLimitCurryCompLim G

noncomputable def proposition_6_2_5_limits_commute_right {J : Type u} [Category.{v} J]
    {K : Type u'} [Category.{v'} K] {C : Type u''} [Category.{v''} C]
    [HasLimitsOfShape J C] [HasLimitsOfShape K C]
    [HasLimitsOfShape (J × K) C] [HasLimitsOfShape (K × J) C]
    (G : J × K ⥤ C) :
    limit G ≅ limit ((Functor.curry.obj G).flip ⋙ lim) :=
  (Functor.Initial.limitIso (Prod.braiding K J).functor G).symm ≪≫
  limitIsoLimitCurryCompLim ((Prod.braiding K J).functor ⋙ G)

noncomputable def proposition_6_2_5_colimits_commute_left {J : Type u} [Category.{v} J]
    {K : Type u'} [Category.{v'} K] {C : Type u''} [Category.{v''} C]
    [HasColimitsOfShape J C] [HasColimitsOfShape K C] (G : J × K ⥤ C) :
    colimit G ≅ colimit (Functor.curry.obj G ⋙ colim) :=
  colimitIsoColimitCurryCompColim G

noncomputable def example_6_2_5_prod_comm {C : Type u} [Category.{v} C]
    (S T : C) [HasBinaryProducts C] :
    S ⨯ T ≅ T ⨯ S :=
  Limits.prod.braiding S T

noncomputable def example_6_2_5_prod_assoc {C : Type u} [Category.{v} C]
    (S T U : C) [HasBinaryProducts C] :
    (S ⨯ T) ⨯ U ≅ S ⨯ (T ⨯ U) :=
  Limits.prod.associator S T U

@[reducible]
noncomputable def corollary_6_2_6_hasLimitsOfSize {A : Type u} [Category.{v} A] :
    HasLimitsOfSize.{v, v} (Aᵒᵖ ⥤ Type v) :=
  functorCategoryHasLimitsOfSize

@[reducible]
noncomputable def corollary_6_2_6_hasColimitsOfSize {A : Type u} [Category.{v} A] :
    HasColimitsOfSize.{v, v} (Aᵒᵖ ⥤ Type v) :=
  functorCategoryHasColimitsOfSize

@[reducible]
noncomputable def corollary_6_2_6_evaluation_preservesLimits {A : Type u} [Category.{v} A]
    (X : Aᵒᵖ) :
    PreservesLimits ((evaluation Aᵒᵖ (Type v)).obj X) :=
  inferInstance

@[reducible]
noncomputable def corollary_6_2_6_evaluation_preservesColimits {A : Type u} [Category.{v} A]
    (X : Aᵒᵖ) :
    PreservesColimits ((evaluation Aᵒᵖ (Type v)).obj X) :=
  inferInstance

@[reducible]
noncomputable def corollary_6_2_7_yoneda_preservesLimits {A : Type u} [Category.{v} A] :
    PreservesLimits (yoneda (C := A)) :=
  inferInstance

noncomputable def example_6_2_7_yoneda_prod {A : Type u} [Category.{v} A]
    [HasBinaryProducts A] (X Y : A) :
    yoneda.obj (X ⨯ Y) ≅ yoneda.obj X ⨯ yoneda.obj Y :=
  PreservesLimitPair.iso yoneda X Y

abbrev def_6_2_8_category_of_elements {A : Type u} [Category.{v} A] (X : Aᵒᵖ ⥤ Type v) :=
  X.Elements

abbrev def_6_2_8_projection {A : Type u} [Category.{v} A] (X : Aᵒᵖ ⥤ Type v) :
    X.Elements ⥤ Aᵒᵖ :=
  CategoryOfElements.π X

def def_6_2_9_density_cocone {A : Type u} [Category.{v} A] (X : Aᵒᵖ ⥤ Type v) :
    Cocone (CostructuredArrow.proj yoneda X ⋙ yoneda) where
  pt := X
  ι := {
    app := fun f => f.hom
    naturality := fun f g h => by
      dsimp
      rw [Category.comp_id, CostructuredArrow.w]
  }

def theorem_6_2_9_isColimit_density {A : Type u} [Category.{v} A] (X : Aᵒᵖ ⥤ Type v) :
    IsColimit (def_6_2_9_density_cocone X) where
  desc s := {
    app := fun Y => ↾fun (x : X.obj Y) =>
      (s.ι.app (CostructuredArrow.mk
        (yonedaEquiv.symm (show X.obj (op (unop Y)) from x)))).app Y (𝟙 (unop Y))
    naturality := fun {Y Z} f => by
      ext x
      dsimp
      let f_elem : CostructuredArrow.mk
          (yonedaEquiv.symm (show X.obj (op (unop Z)) from X.map f x)) ⟶
          CostructuredArrow.mk (yonedaEquiv.symm (show X.obj (op (unop Y)) from x)) :=
        CostructuredArrow.homMk f.unop (by
          ext W g
          dsimp
          rw [yonedaEquiv_symm_app_apply, yonedaEquiv_symm_app_apply]
          rw [op_comp, Functor.map_comp_apply]
          rfl)
      have hnat := NatTrans.congr_app (s.ι.naturality f_elem) Z
      have h_app := congr_fun (congr_arg (fun (k : (yoneda.obj (unop Z)).obj Z ⟶ s.pt.obj Z) =>
        (k : ((yoneda.obj (unop Z)).obj Z) → s.pt.obj Z)) hnat) (𝟙 (unop Z))
      dsimp at h_app
      rw [Category.id_comp] at h_app
      have hnat_app :=
        NatTrans.naturality_apply
          (s.ι.app (CostructuredArrow.mk (yonedaEquiv.symm x))) f (𝟙 (unop Y))
      change (s.ι.app (CostructuredArrow.mk (yonedaEquiv.symm x))).app Z (f.unop ≫ 𝟙 (unop Y)) =
        s.pt.map f ((s.ι.app (CostructuredArrow.mk (yonedaEquiv.symm x))).app Y (𝟙 (unop Y)))
        at hnat_app
      have h_rw := congr_arg (fun (k : unop Z ⟶ unop Y) =>
        (s.ι.app (CostructuredArrow.mk (yonedaEquiv.symm x))).app Z k) (Category.comp_id f.unop)
      dsimp at h_rw
      exact h_app.symm.trans (h_rw.symm.trans hnat_app)
  }
  fac s f := by
    ext Y g
    dsimp
    let g_elem : CostructuredArrow.mk
        (yonedaEquiv.symm (show X.obj (op (unop Y)) from f.hom.app Y g)) ⟶ f :=
      CostructuredArrow.homMk g (by
        ext W k
        dsimp
        rw [yonedaEquiv_symm_app_apply]
        have h_nat := NatTrans.naturality_apply f.hom k.op g
        dsimp at h_nat
        exact h_nat)
    have hnat := NatTrans.congr_app (s.ι.naturality g_elem) Y
    have h_app := congr_fun (congr_arg (fun (k : (yoneda.obj (unop Y)).obj Y ⟶ s.pt.obj Y) =>
      (k : ((yoneda.obj (unop Y)).obj Y) → s.pt.obj Y)) hnat) (𝟙 (unop Y))
    dsimp at h_app
    rw [Category.id_comp] at h_app
    exact h_app.symm
  uniq s m hm := by
    ext Y x
    have h := congr_app
      (hm (CostructuredArrow.mk (yonedaEquiv.symm (show X.obj (op (unop Y)) from x)))) Y
    have h_id := congr_fun (congr_arg (fun (k : (yoneda.obj (unop Y)).obj Y ⟶ s.pt.obj Y) =>
      (k : ((yoneda.obj (unop Y)).obj Y) → s.pt.obj Y)) h) (𝟙 (unop Y))
    dsimp [def_6_2_9_density_cocone] at h_id ⊢
    rw [yonedaEquiv_symm_app_apply, op_id, Functor.map_id_apply] at h_id
    exact h_id

noncomputable def theorem_6_2_9_density_iso {A : Type u} [Category.{v} A] (X : Aᵒᵖ ⥤ Type v) :
    colimit (CostructuredArrow.proj yoneda X ⋙ yoneda) ≅ X :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (theorem_6_2_9_isColimit_density X)

theorem exercise_6_2_1a {A : Type u} [Category.{v} A] {S : Type u'} [Category.{v'} S]
    [HasPullbacks S] {F G : A ⥤ S} (α : F ⟶ G) :
    Mono α ↔ ∀ (X : A), Mono (α.app X) := by
  constructor
  · intro h X
    exact instMonoAppOfFunctor α X
  · intro h
    exact NatTrans.mono_of_mono_app α

theorem exercise_6_2_1b_mono {A : Type u} [Category.{v} A] {F G : Aᵒᵖ ⥤ Type v} (α : F ⟶ G) :
    Mono α ↔ ∀ (X : Aᵒᵖ), Function.Injective (α.app X) := by
  constructor
  · intro h X
    have : Mono (α.app X) := instMonoAppOfFunctor α X
    exact (mono_iff_injective (α.app X)).mp this
  · intro h
    have : ∀ (X : Aᵒᵖ), Mono (α.app X) := fun X => (mono_iff_injective (α.app X)).mpr (h X)
    exact NatTrans.mono_of_mono_app α

theorem exercise_6_2_1b_epi {A : Type u} [Category.{v} A] {F G : Aᵒᵖ ⥤ Type v} (α : F ⟶ G) :
    Epi α ↔ ∀ (X : Aᵒᵖ), Function.Surjective (α.app X) := by
  constructor
  · intro h X
    have : Epi (α.app X) := instEpiAppOfFunctor α X
    exact (epi_iff_surjective (α.app X)).mp this
  · intro h
    have : ∀ (X : Aᵒᵖ), Epi (α.app X) := fun X => (epi_iff_surjective (α.app X)).mpr (h X)
    exact NatTrans.epi_of_epi_app α

lemma lemma_6_2_2_coprod_disjoint {A : Type u} [Category.{v} A] (X Y : Aᵒᵖ ⥤ Type v) (B : Aᵒᵖ)
    (x : X.obj B) (y : Y.obj B) :
    (coprod.inl (X := X) (Y := Y)).app B x ≠ (coprod.inr (X := X) (Y := Y)).app B y := by
  intro h
  let p0 : X ⟶ (Functor.const Aᵒᵖ).obj (ULift.{v} (Fin 2)) := {
    app := fun _ => ↾fun _ => (⟨0⟩ : ULift.{v} (Fin 2))
    naturality := fun _ _ _ => rfl
  }
  let p1 : Y ⟶ (Functor.const Aᵒᵖ).obj (ULift.{v} (Fin 2)) := {
    app := fun _ => ↾fun _ => (⟨1⟩ : ULift.{v} (Fin 2))
    naturality := fun _ _ _ => rfl
  }
  let p : X ⨿ Y ⟶ (Functor.const Aᵒᵖ).obj (ULift.{v} (Fin 2)) :=
    coprod.desc p0 p1
  have h0 : (coprod.inl (X := X) (Y := Y) ≫ p).app B x = (⟨0⟩ : ULift.{v} (Fin 2)) := by
    have hdesc := congr_app (coprod.inl_desc (X := X) (Y := Y) p0 p1) B
    change ((coprod.inl ≫ p).app B : X.obj B → ULift (Fin 2)) x = ⟨0⟩
    rw [hdesc]
    rfl
  have h1 : (coprod.inr (X := X) (Y := Y) ≫ p).app B y = (⟨1⟩ : ULift.{v} (Fin 2)) := by
    have hdesc := congr_app (coprod.inr_desc (X := X) (Y := Y) p0 p1) B
    change ((coprod.inr ≫ p).app B : Y.obj B → ULift (Fin 2)) y = ⟨1⟩
    rw [hdesc]
    rfl
  have heq : (coprod.inl (X := X) (Y := Y) ≫ p).app B x =
      (coprod.inr (X := X) (Y := Y) ≫ p).app B y := by
    have hl : (coprod.inl (X := X) (Y := Y) ≫ p).app B x =
      p.app B ((coprod.inl (X := X) (Y := Y)).app B x) := rfl
    have hr : (coprod.inr (X := X) (Y := Y) ≫ p).app B y =
      p.app B ((coprod.inr (X := X) (Y := Y)).app B y) := rfl
    rw [hl, hr, h]
  rw [h0, h1] at heq
  cases heq

theorem exercise_6_2_2a {A : Type u} [Category.{v} A] (W : A) (X Y : Aᵒᵖ ⥤ Type v)
    (i : yoneda.obj W ≅ X ⨿ Y) :
    (∀ (B : Aᵒᵖ), IsEmpty (X.obj B)) ∨ (∀ (B : Aᵒᵖ), IsEmpty (Y.obj B)) := by
  let p0 : X ⟶ (Functor.const Aᵒᵖ).obj (ULift.{v} (Fin 2)) := {
    app := fun _ => ↾fun _ => (⟨0⟩ : ULift.{v} (Fin 2))
    naturality := fun _ _ _ => rfl
  }
  let p1 : Y ⟶ (Functor.const Aᵒᵖ).obj (ULift.{v} (Fin 2)) := {
    app := fun _ => ↾fun _ => (⟨1⟩ : ULift.{v} (Fin 2))
    naturality := fun _ _ _ => rfl
  }
  let p : X ⨿ Y ⟶ (Functor.const Aᵒᵖ).obj (ULift.{v} (Fin 2)) :=
    coprod.desc p0 p1
  have h_tag : p.app (op W) ((i.hom.app (op W)) (𝟙 W)) = (⟨0⟩ : ULift.{v} (Fin 2)) ∨
               p.app (op W) ((i.hom.app (op W)) (𝟙 W)) = (⟨1⟩ : ULift.{v} (Fin 2)) := by
    rcases (p.app (op W) ((i.hom.app (op W)) (𝟙 W))) with ⟨⟨val, hval⟩⟩
    interval_cases val
    · left; rfl
    · right; rfl
  rcases h_tag with (htag0 | htag1)
  · right
    intro B
    constructor
    intro y
    let f : unop B ⟶ W := (i.inv.app B) ((coprod.inr (X := X) (Y := Y)).app B y)
    have h1 : p.app B ((coprod.inr (X := X) (Y := Y)).app B y) = (⟨1⟩ : ULift.{v} (Fin 2)) := by
      have hdesc := congr_app (coprod.inr_desc (X := X) (Y := Y) p0 p1) B
      change ((coprod.inr ≫ p).app B : Y.obj B → ULift (Fin 2)) y = ⟨1⟩
      rw [hdesc]
      rfl
    have h_hom : (i.hom.app B) f = (coprod.inr (X := X) (Y := Y)).app B y := by
      have hinv := (i.app B).inv_hom_id
      have h_app := congr_fun (congr_arg (fun (k : (X ⨿ Y).obj B ⟶ (X ⨿ Y).obj B) =>
        (k : (X ⨿ Y).obj B → (X ⨿ Y).obj B)) hinv) ((coprod.inr (X := X) (Y := Y)).app B y)
      exact h_app
    have hnat := NatTrans.naturality_apply i.hom f.op (𝟙 W)
    dsimp at hnat
    rw [Category.comp_id] at hnat
    have h_nat_p := NatTrans.naturality_apply p f.op ((i.hom.app (op W)) (𝟙 W))
    have h0 : p.app B ((coprod.inr (X := X) (Y := Y)).app B y) = (⟨0⟩ : ULift.{v} (Fin 2)) := by
      rw [← h_hom, hnat, h_nat_p, htag0]
      rfl
    rw [h1] at h0
    cases h0
  · left
    intro B
    constructor
    intro x
    let f : unop B ⟶ W := (i.inv.app B) ((coprod.inl (X := X) (Y := Y)).app B x)
    have h0 : p.app B ((coprod.inl (X := X) (Y := Y)).app B x) = (⟨0⟩ : ULift.{v} (Fin 2)) := by
      have hdesc := congr_app (coprod.inl_desc (X := X) (Y := Y) p0 p1) B
      change ((coprod.inl ≫ p).app B : X.obj B → ULift (Fin 2)) x = ⟨0⟩
      rw [hdesc]
      rfl
    have h_hom : (i.hom.app B) f = (coprod.inl (X := X) (Y := Y)).app B x := by
      have hinv := (i.app B).inv_hom_id
      have h_app := congr_fun (congr_arg (fun (k : (X ⨿ Y).obj B ⟶ (X ⨿ Y).obj B) =>
        (k : (X ⨿ Y).obj B → (X ⨿ Y).obj B)) hinv) ((coprod.inl (X := X) (Y := Y)).app B x)
      exact h_app
    have hnat := NatTrans.naturality_apply i.hom f.op (𝟙 W)
    dsimp at hnat
    rw [Category.comp_id] at hnat
    have h_nat_p := NatTrans.naturality_apply p f.op ((i.hom.app (op W)) (𝟙 W))
    have h1 : p.app B ((coprod.inl (X := X) (Y := Y)).app B x) = (⟨1⟩ : ULift.{v} (Fin 2)) := by
      rw [← h_hom, hnat, h_nat_p, htag1]
      rfl
    rw [h0] at h1
    cases h1

theorem exercise_6_2_2b {A : Type u} [Category.{v} A] (X Y : A) (W : A) :
    (yoneda.obj W ≅ yoneda.obj X ⨿ yoneda.obj Y) → False := by
  intro i
  rcases exercise_6_2_2a W (yoneda.obj X) (yoneda.obj Y) i with (hX | hY)
  · have hX_op := hX (op X)
    exact hX_op.false (𝟙 X)
  · have hY_op := hY (op Y)
    exact hY_op.false (𝟙 Y)

def exercise_6_2_3_comma_equiv {A : Type u} [Category.{v} A] (X : Aᵒᵖ ⥤ Type v) :
    X.Elementsᵒᵖ ≌ CostructuredArrow yoneda X :=
  CategoryOfElements.costructuredArrowYonedaEquivalence X

def exercise_6_2_4_representable_of_isInitial {A : Type u} [Category.{v} A] (X : Aᵒᵖ ⥤ Type v)
    (E : X.Elements) (hE : Limits.IsInitial E) :
    ∃ (W : A), Nonempty (yoneda.obj W ≅ X) := by
  refine ⟨unop E.1, ⟨NatIso.ofComponents (fun Y => Equiv.toIso {
    toFun := fun f => (X.map f.op) E.2
    invFun := fun y => (hE.to ⟨Y, y⟩).1.unop
    left_inv := fun f => by
      have huniq := hE.hom_ext (hE.to ⟨Y, (X.map f.op) E.2⟩) ⟨f.op, rfl⟩
      have h_val := congr_arg Subtype.val huniq
      dsimp at h_val
      exact congr_arg Opposite.unop h_val
    right_inv := fun y => by
      have hcond := (hE.to ⟨Y, y⟩).2
      exact hcond
  }) (fun {Y Z} g => by
    ext f
    dsimp
    rw [Functor.map_comp_apply])⟩⟩

def exercise_6_2_4_isInitial_of_representable {A : Type u} [Category.{v} A] (X : Aᵒᵖ ⥤ Type v)
    (W : A) (i : yoneda.obj W ≅ X) :
    ∃ (E : X.Elements), Nonempty (Limits.IsInitial E) := by
  let x0 : X.obj (op W) := i.hom.app (op W) (𝟙 W)
  let E : X.Elements := ⟨op W, x0⟩
  refine ⟨E, ⟨Limits.IsInitial.ofUniqueHom (fun ⟨Y, y⟩ => ?_) (fun ⟨Y, y⟩ f => ?_)⟩⟩
  · let f_hom : unop Y ⟶ W := i.inv.app Y y
    refine ⟨f_hom.op, ?_⟩
    dsimp [x0]
    have hnat := NatTrans.naturality_apply i.hom f_hom.op (𝟙 W)
    dsimp at hnat
    rw [Category.comp_id] at hnat
    have hinv := (i.app Y).inv_hom_id
    have h_app := congr_fun (congr_arg (fun (k : X.obj Y ⟶ X.obj Y) =>
      (k : X.obj Y → X.obj Y)) hinv) y
    dsimp at h_app
    rw [← hnat, h_app]
  · apply Subtype.ext
    dsimp
    have hnat := NatTrans.naturality_apply i.hom f.1 (𝟙 W)
    dsimp [x0] at hnat
    rw [Category.comp_id] at hnat
    have hf_cond := f.2
    dsimp [x0] at hf_cond
    have h_m : i.hom.app Y f.1.unop = y := by
      rw [hnat, hf_cond]
    have h_inv_y : i.hom.app Y (i.inv.app Y y) = y := by
      have hinv := (i.app Y).inv_hom_id
      exact congr_fun (congr_arg (fun (k : X.obj Y ⟶ X.obj Y) =>
        (k : X.obj Y → X.obj Y)) hinv) y
    have hinj : Function.Injective (i.hom.app Y) := (i.app Y).toEquiv.injective
    have heq : f.1.unop = (i.inv.app Y) y := hinj (by rw [h_m, h_inv_y])
    exact congr_arg Opposite.op heq

def exercise_6_2_5_slice_equiv {A : Type u} [Category.{v} A] (X : Aᵒᵖ ⥤ Type v) :
    Over X ≌ ((CostructuredArrow yoneda X)ᵒᵖ ⥤ Type v) :=
  overEquivPresheafCostructuredArrow X

noncomputable def exercise_6_2_6_lan_adjunction {A : Type u} [Category.{v} A]
    {B : Type u'} [Category.{v'} B] (F : A ⥤ B) (S : Type u'') [Category.{v''} S]
    [∀ (b : B), HasColimitsOfShape (CostructuredArrow F b) S] :
    F.lan ⊣ (Functor.whiskeringLeft A B S).obj F :=
  F.lanAdjunction S

end LimitsAndColimitsOfPresheaves
