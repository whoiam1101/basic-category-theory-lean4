-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib

namespace InteractionsBetweenFunctorsAndLimits

universe u v u' v' w

open CategoryTheory Limits

def def_5_3_1a_preserves_limits_of_shape {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (J : Type w) [Category.{w} J] (F : C ⥤ D) : Prop :=
  PreservesLimitsOfShape J F

def def_5_3_1a_preserves_colimits_of_shape {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (J : Type w) [Category.{w} J] (F : C ⥤ D) : Prop :=
  PreservesColimitsOfShape J F

def def_5_3_1a_preserves_limit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (F : C ⥤ D) : Prop :=
  PreservesLimit K F

def def_5_3_1a_preserves_colimit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (F : C ⥤ D) : Prop :=
  PreservesColimit K F

def def_5_3_1b_preserves_limits {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) : Prop :=
  PreservesLimitsOfSize.{w, w} F

def def_5_3_1b_preserves_colimits {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) : Prop :=
  PreservesColimitsOfSize.{w, w} F

def def_5_3_1c_reflects_limits_of_shape {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (J : Type w) [Category.{w} J] (F : C ⥤ D) : Prop :=
  ReflectsLimitsOfShape J F

def def_5_3_1c_reflects_colimits_of_shape {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (J : Type w) [Category.{w} J] (F : C ⥤ D) : Prop :=
  ReflectsColimitsOfShape J F

def def_5_3_1c_reflects_limit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (F : C ⥤ D) : Prop :=
  ReflectsLimit K F

def def_5_3_1c_reflects_colimit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (F : C ⥤ D) : Prop :=
  ReflectsColimit K F

def def_5_3_1c_reflects_limits {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) : Prop :=
  ReflectsLimitsOfSize.{w, w} F

def def_5_3_1c_reflects_colimits {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) : Prop :=
  ReflectsColimitsOfSize.{w, w} F

noncomputable def canonical_limit_map {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) {J : Type w} [Category.{w} J]
    (K : J ⥤ C) [HasLimit K] [HasLimit (K ⋙ F)] :
    F.obj (limit K) ⟶ limit (K ⋙ F) :=
  limit.lift (K ⋙ F) (F.mapCone (limit.cone K))

noncomputable def canonical_colimit_map {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) {J : Type w} [Category.{w} J]
    (K : J ⥤ C) [HasColimit K] [HasColimit (K ⋙ F)] :
    colimit (K ⋙ F) ⟶ F.obj (colimit K) :=
  colimit.desc (K ⋙ F) (F.mapCocone (colimit.cocone K))

noncomputable def def_5_3_1_limit_iso {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) {J : Type w} [Category.{w} J]
    (K : J ⥤ C) [PreservesLimit K F] [HasLimit K] :
    F.obj (limit K) ≅ limit (K ⋙ F) :=
  preservesLimitIso F K

noncomputable def def_5_3_1_colimit_iso {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (F : C ⥤ D) {J : Type w} [Category.{w} J]
    (K : J ⥤ C) [PreservesColimit K F] [HasColimit K] :
    F.obj (colimit K) ≅ colimit (K ⋙ F) :=
  preservesColimitIso F K

noncomputable abbrev example_5_3_2_preserves_limits :
    PreservesLimits (forget TopCat.{u}) :=
  inferInstance

noncomputable abbrev example_5_3_2_preserves_colimits :
    PreservesColimits (forget TopCat.{u}) :=
  inferInstance

theorem example_5_3_3_grp_not_preserves_initial :
    ¬ (∀ (I : GrpCat.{0}),
        Nonempty (IsInitial I) → Nonempty (IsInitial ((forget GrpCat).obj I))) := by
  intro h
  have hI : Nonempty (IsInitial (⊥_ GrpCat.{0})) := ⟨initialIsInitial⟩
  have h_set_init : Nonempty (IsInitial ((forget GrpCat).obj (⊥_ GrpCat.{0}))) :=
    h (⊥_ GrpCat.{0}) hI
  rcases h_set_init with ⟨h_init⟩
  let f : (forget GrpCat).obj (⊥_ GrpCat.{0}) ⟶ PEmpty := h_init.to PEmpty
  exact (f (1 : (forget GrpCat).obj (⊥_ GrpCat.{0}))).elim

theorem example_5_3_3_not_preserves_colimits_grp :
    ¬ PreservesColimits (forget GrpCat.{0}) := by
  intro h
  have h_empty_cocone : IsColimit (asEmptyCocone (⊥_ GrpCat.{0})) := initialIsInitial
  have h_map :
      IsColimit ((forget GrpCat.{0}).mapCocone (asEmptyCocone (⊥_ GrpCat.{0}))) :=
    isColimitOfPreserves (forget GrpCat.{0}) h_empty_cocone
  let c_empty : Cocone (Functor.empty GrpCat.{0} ⋙ forget GrpCat.{0}) :=
    { pt := PEmpty, ι := { app := fun x => PEmpty.elim x.as } }
  let f : (forget GrpCat).obj (⊥_ GrpCat.{0}) ⟶ PEmpty := h_map.desc c_empty
  exact (f (1 : (forget GrpCat).obj (⊥_ GrpCat.{0}))).elim

theorem example_5_3_3_not_preserves_colimits_mod :
    ¬ PreservesColimits (forget (ModuleCat.{0} ℤ)) := by
  intro h
  have h_empty_cocone :
      IsColimit (asEmptyCocone (⊥_ (ModuleCat.{0} ℤ))) := initialIsInitial
  have h_map :
      IsColimit ((forget (ModuleCat.{0} ℤ)).mapCocone
        (asEmptyCocone (⊥_ (ModuleCat.{0} ℤ)))) :=
    isColimitOfPreserves (forget (ModuleCat.{0} ℤ)) h_empty_cocone
  let c_empty :
      Cocone (Functor.empty (ModuleCat.{0} ℤ) ⋙ forget (ModuleCat.{0} ℤ)) :=
    { pt := PEmpty, ι := { app := fun x => PEmpty.elim x.as } }
  let f : (forget (ModuleCat.{0} ℤ)).obj (⊥_ (ModuleCat.{0} ℤ)) ⟶ PEmpty :=
    h_map.desc c_empty
  exact (f (0 : (forget (ModuleCat.{0} ℤ)).obj (⊥_ (ModuleCat.{0} ℤ)))).elim

theorem example_5_3_4_unique_group_structure {G₁ G₂ : Type u} [Group G₁] [Group G₂]
    (G : Group (G₁ × G₂))
    (hp₁ : ∀ x y : G₁ × G₂, (G.mul x y).1 = x.1 * y.1)
    (hp₂ : ∀ x y : G₁ × G₂, (G.mul x y).2 = x.2 * y.2) :
    G = Prod.instGroup := by
  apply Group.ext
  funext x y
  ext
  · exact hp₁ x y
  · exact hp₂ x y

noncomputable abbrev example_5_3_4_grp_creates_binary_products :
    CreatesLimitsOfShape (Discrete WalkingPair) (forget GrpCat.{u}) :=
  inferInstance

abbrev def_5_3_5a_creates_limits_of_shape {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (J : Type w) [Category.{w} J] (F : C ⥤ D) :=
  CreatesLimitsOfShape J F

abbrev def_5_3_5a_creates_colimits_of_shape {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (J : Type w) [Category.{w} J] (F : C ⥤ D) :=
  CreatesColimitsOfShape J F

abbrev def_5_3_5a_creates_limit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (F : C ⥤ D) :=
  CreatesLimit K F

abbrev def_5_3_5a_creates_colimit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (F : C ⥤ D) :=
  CreatesColimit K F

abbrev def_5_3_5b_creates_limits {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) :=
  CreatesLimitsOfSize.{w, w} F

abbrev def_5_3_5b_creates_colimits {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) :=
  CreatesColimitsOfSize.{w, w} F

abbrev lemma_5_3_6_hasLimits {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : Type w} [Category.{w} J] (F : C ⥤ D)
    [HasLimitsOfShape J D] [CreatesLimitsOfShape J F] : HasLimitsOfShape J C :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape F

@[reducible]
noncomputable def lemma_5_3_6_preservesLimits {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (J : Type w) [Category.{w} J] (F : C ⥤ D)
    [CreatesLimitsOfShape J F] [HasLimitsOfShape J D] : PreservesLimitsOfShape J F where
  preservesLimit := fun {K} => {
    preserves := fun {c} hc => by
      have h_lift_lim : IsLimit (liftLimit (limit.isLimit (K ⋙ F))) :=
        liftedLimitIsLimit (limit.isLimit (K ⋙ F))
      have e : c ≅ liftLimit (limit.isLimit (K ⋙ F)) :=
        hc.uniqueUpToIso h_lift_lim
      have hF_iso : F.mapCone c ≅ F.mapCone (liftLimit (limit.isLimit (K ⋙ F))) :=
        (Cone.functoriality K F).mapIso e
      have h_orig : F.mapCone (liftLimit (limit.isLimit (K ⋙ F))) ≅ limit.cone (K ⋙ F) :=
        liftedLimitMapsToOriginal (limit.isLimit (K ⋙ F))
      have h_total : F.mapCone c ≅ limit.cone (K ⋙ F) :=
        hF_iso.trans h_orig
      exact ⟨IsLimit.ofIsoLimit (limit.isLimit (K ⋙ F)) h_total.symm⟩
  }

abbrev lemma_5_3_6_hasColimits {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : Type w} [Category.{w} J] (F : C ⥤ D)
    [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColimitsOfShape J C :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape F

@[reducible]
noncomputable def lemma_5_3_6_preservesColimits {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (J : Type w) [Category.{w} J] (F : C ⥤ D)
    [CreatesColimitsOfShape J F] [HasColimitsOfShape J D] : PreservesColimitsOfShape J F where
  preservesColimit := fun {K} => {
    preserves := fun {c} hc => by
      have h_lift_colim : IsColimit (liftColimit (colimit.isColimit (K ⋙ F))) :=
        liftedColimitIsColimit (colimit.isColimit (K ⋙ F))
      have e : c ≅ liftColimit (colimit.isColimit (K ⋙ F)) :=
        hc.uniqueUpToIso h_lift_colim
      have hF_iso : F.mapCocone c ≅ F.mapCocone (liftColimit (colimit.isColimit (K ⋙ F))) :=
        (Cocone.functoriality K F).mapIso e
      have h_orig :
          F.mapCocone (liftColimit (colimit.isColimit (K ⋙ F))) ≅ colimit.cocone (K ⋙ F) :=
        liftedColimitMapsToOriginal (colimit.isColimit (K ⋙ F))
      have h_total : F.mapCocone c ≅ colimit.cocone (K ⋙ F) :=
        hF_iso.trans h_orig
      exact ⟨IsColimit.ofIsoColimit (colimit.isColimit (K ⋙ F)) h_total.symm⟩
  }

def exercise_5_3_1 {C : Type u} [Category.{v} C]
    (P : C → C → C) (p₁ : (X Y : C) → P X Y ⟶ X) (p₂ : (X Y : C) → P X Y ⟶ Y)
    (hP : ∀ X Y : C, IsLimit (BinaryFan.mk (p₁ X Y) (p₂ X Y))) :
    C × C ⥤ C where
  obj XY := P XY.1 XY.2
  map {XY XY'} fg :=
    BinaryFan.IsLimit.lift (hP XY'.1 XY'.2) (p₁ XY.1 XY.2 ≫ fg.1) (p₂ XY.1 XY.2 ≫ fg.2)
  map_id XY := by
    apply BinaryFan.IsLimit.hom_ext (hP XY.1 XY.2)
    · rw [BinaryFan.IsLimit.lift_fst]
      simp
    · rw [BinaryFan.IsLimit.lift_snd]
      simp
  map_comp {XY₁ XY₂ XY₃} fg gh := by
    apply BinaryFan.IsLimit.hom_ext (hP XY₃.1 XY₃.2)
    · rw [BinaryFan.IsLimit.lift_fst]
      dsimp
      rw [Category.assoc]
      have h1 :=
        BinaryFan.IsLimit.lift_fst (hP XY₃.1 XY₃.2) (p₁ XY₂.1 XY₂.2 ≫ gh.1) (p₂ XY₂.1 XY₂.2 ≫ gh.2)
      have h2 :=
        BinaryFan.IsLimit.lift_fst (hP XY₂.1 XY₂.2) (p₁ XY₁.1 XY₁.2 ≫ fg.1) (p₂ XY₁.1 XY₁.2 ≫ fg.2)
      dsimp at h1 h2
      rw [h1]
      conv_rhs => rw [← Category.assoc, h2, Category.assoc]
    · rw [BinaryFan.IsLimit.lift_snd]
      dsimp
      rw [Category.assoc]
      have h1 :=
        BinaryFan.IsLimit.lift_snd (hP XY₃.1 XY₃.2) (p₁ XY₂.1 XY₂.2 ≫ gh.1) (p₂ XY₂.1 XY₂.2 ≫ gh.2)
      have h2 :=
        BinaryFan.IsLimit.lift_snd (hP XY₂.1 XY₂.2) (p₁ XY₁.1 XY₁.2 ≫ fg.1) (p₂ XY₁.1 XY₁.2 ≫ fg.2)
      dsimp at h1 h2
      rw [h1]
      conv_rhs => rw [← Category.assoc, h2, Category.assoc]

def exercise_5_3_2_equiv {C : Type u} [Category.{v} C]
    {X Y P : C} (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsLimit (BinaryFan.mk p₁ p₂)) (A : C) :
    (A ⟶ P) ≃ (A ⟶ X) × (A ⟶ Y) where
  toFun f := (f ≫ p₁, f ≫ p₂)
  invFun gh := BinaryFan.IsLimit.lift hP gh.1 gh.2
  left_inv f := by
    apply BinaryFan.IsLimit.hom_ext hP
    · exact BinaryFan.IsLimit.lift_fst hP (f ≫ p₁) (f ≫ p₂)
    · exact BinaryFan.IsLimit.lift_snd hP (f ≫ p₁) (f ≫ p₂)
  right_inv gh := by
    ext
    · exact BinaryFan.IsLimit.lift_fst hP gh.1 gh.2
    · exact BinaryFan.IsLimit.lift_snd hP gh.1 gh.2

def exercise_5_3_2_functor_prod {C : Type u} [Category.{v} C] (X Y : C) : Cᵒᵖ ⥤ Type v where
  obj A := (A.unop ⟶ X) × (A.unop ⟶ Y)
  map f := ↾fun gh => (f.unop ≫ gh.1, f.unop ≫ gh.2)

def exercise_5_3_2_natIso_fixed {C : Type u} [Category.{v} C]
    {X Y P : C} (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsLimit (BinaryFan.mk p₁ p₂)) :
    yoneda.obj P ≅ exercise_5_3_2_functor_prod X Y :=
  NatIso.ofComponents
    (fun A => Equiv.toIso (exercise_5_3_2_equiv p₁ p₂ hP A.unop))
    (fun {A B} f => by
      ext g
      dsimp [exercise_5_3_2_functor_prod]
      ext
      · dsimp [exercise_5_3_2_equiv]
        rw [Category.assoc]
      · dsimp [exercise_5_3_2_equiv]
        rw [Category.assoc])

@[reducible]
def exercise_5_3_3_reflects_limit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] :
    ReflectsLimit K F :=
  CreatesLimit.toReflectsLimit

@[reducible]
def exercise_5_3_3_reflects_limits_of_shape {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (J : Type w) [Category.{w} J] (F : C ⥤ D)
    [CreatesLimitsOfShape J F] : ReflectsLimitsOfShape J F where
  reflectsLimit := fun {_} => CreatesLimit.toReflectsLimit

@[reducible]
def exercise_5_3_3_reflects_limits {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) [CreatesLimits F] : ReflectsLimits F where
  reflectsLimitsOfShape := fun {_ _} => exercise_5_3_3_reflects_limits_of_shape _ F

noncomputable abbrev exercise_5_3_4a : CreatesLimits (forget GrpCat.{u}) :=
  inferInstance

noncomputable abbrev exercise_5_3_4b_mon : CreatesLimits (forget MonCat.{u}) :=
  inferInstance

noncomputable abbrev exercise_5_3_4b_ring : PreservesLimits (forget RingCat.{u}) :=
  inferInstance

noncomputable abbrev exercise_5_3_4b_mod (R : Type u) [Ring R] :
    PreservesLimits (forget (ModuleCat.{u} R)) :=
  inferInstance

abbrev exercise_5_3_5_has_limit {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (F : C ⥤ D)
    [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K :=
  hasLimit_of_created K F

@[reducible]
noncomputable def exercise_5_3_5_preserves_limit {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {J : Type w} [Category.{w} J]
    (K : J ⥤ C) (F : C ⥤ D) [CreatesLimit K F] [HasLimit (K ⋙ F)] : PreservesLimit K F where
  preserves {c} hc := by
    have h_lift_lim : IsLimit (liftLimit (limit.isLimit (K ⋙ F))) :=
      liftedLimitIsLimit (limit.isLimit (K ⋙ F))
    have e : c ≅ liftLimit (limit.isLimit (K ⋙ F)) :=
      hc.uniqueUpToIso h_lift_lim
    have hF_iso : F.mapCone c ≅ F.mapCone (liftLimit (limit.isLimit (K ⋙ F))) :=
      (Cone.functoriality K F).mapIso e
    have h_orig : F.mapCone (liftLimit (limit.isLimit (K ⋙ F))) ≅ limit.cone (K ⋙ F) :=
      liftedLimitMapsToOriginal (limit.isLimit (K ⋙ F))
    have h_total : F.mapCone c ≅ limit.cone (K ⋙ F) :=
      hF_iso.trans h_orig
    exact ⟨IsLimit.ofIsoLimit (limit.isLimit (K ⋙ F)) h_total.symm⟩

def exercise_5_3_6a_projective_def {B : Type u} [Category.{v} B] (P : B) : Prop :=
  Projective P

theorem exercise_5_3_6a {B : Type u} [Category.{u} B]
    {F : Type u ⥤ B} {G : B ⥤ Type u} (adj : F ⊣ G)
    (hG : ∀ {X Y : B} (f : X ⟶ Y) [Epi f], Epi (G.map f))
    (S : Type u) : Projective (F.obj S) where
  factors {E X} f e he := by
    have hG_epi : Epi (G.map e) := hG e
    have hG_surj : Function.Surjective (G.map e) := (epi_iff_surjective (G.map e)).mp hG_epi
    let g_adj : S ⟶ G.obj X := (adj.homEquiv S X) f
    choose s hs using hG_surj
    have hh : (↾fun x => s (g_adj x)) ≫ G.map e = (adj.homEquiv S X) f := by
      ext x
      exact hs (g_adj x)
    let f' : F.obj S ⟶ E := (adj.homEquiv S E).symm (↾fun x => s (g_adj x))
    refine ⟨f', ?_⟩
    apply (adj.homEquiv S X).injective
    rw [Adjunction.homEquiv_naturality_right]
    dsimp [f']
    rw [Equiv.apply_symm_apply]
    exact hh

theorem exercise_5_3_6b_not_projective :
    ¬ Projective (ModuleCat.of ℤ (ZMod 2)) := by
  intro hP
  let M := ModuleCat.of ℤ ℤ
  let N := ModuleCat.of ℤ (ZMod 2)
  let p : M ⟶ N := ModuleCat.ofHom (Int.castRingHom (ZMod 2)).toAddMonoidHom.toIntLinearMap
  have hepi : Epi p := by
    rw [ModuleCat.epi_iff_surjective]
    intro x
    fin_cases x
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  have hfac := hP.factors (𝟙 N) p
  rcases hfac with ⟨f, hf⟩
  have hw := ConcreteCategory.congr_hom hf (1 : ZMod 2)
  dsimp [p, N, M] at hw
  have h_smul : f.hom ((2 : ℤ) • (1 : ZMod 2)) = (2 : ℤ) • (f.hom (1 : ZMod 2)) :=
    f.hom.map_smul (2 : ℤ) (1 : ZMod 2)
  have h_two_mod : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
  rw [h_two_mod, map_zero] at h_smul
  have h_zero : f.hom (1 : ZMod 2) = 0 := by
    have h_two_ne : (2 : ℤ) ≠ 0 := by decide
    exact smul_eq_zero_iff_right h_two_ne |>.mp h_smul.symm
  rw [h_zero] at hw
  change ((0 : ℤ) : ZMod 2) = 1 at hw
  revert hw
  decide

def exercise_5_3_6c_injective_def {B : Type u} [Category.{v} B] (I : B) : Prop :=
  Injective I

theorem exercise_5_3_6c_vect_injective (K : Type u) [Field K] (V : ModuleCat.{u} K) :
    Injective V where
  factors {X Y} f m hm := by
    have h_inj : Function.Injective m.hom := (ModuleCat.mono_iff_injective m).mp hm
    have h_ker : LinearMap.ker m.hom = ⊥ := LinearMap.ker_eq_bot.mpr h_inj
    rcases LinearMap.exists_leftInverse_of_injective m.hom h_ker with ⟨g, hg⟩
    let g_hom : Y ⟶ X := ModuleCat.ofHom g
    refine ⟨g_hom ≫ f, ?_⟩
    have h_comp : m ≫ g_hom = 𝟙 X := by
      ext x
      exact congr_arg (fun (l : X →ₗ[K] X) => l x) hg
    rw [← Category.assoc, h_comp, Category.id_comp]

theorem exercise_5_3_6c_not_injective :
    ¬ Injective (ModuleCat.of ℤ ℤ) := by
  intro hI
  let Z := ModuleCat.of ℤ ℤ
  let m : Z ⟶ Z := ModuleCat.ofHom (LinearMap.lsmul ℤ ℤ (2 : ℤ))
  have hmono : Mono m := by
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    dsimp [m] at hxy
    have : (2 : ℤ) * x = (2 : ℤ) * y := hxy
    exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) this
  have hfac := hI.factors (𝟙 Z) m
  rcases hfac with ⟨g, hg⟩
  have hw := ConcreteCategory.congr_hom hg (1 : ℤ)
  dsimp [m, Z] at hw
  have h_smul : g.hom ((2 : ℤ) • (1 : ℤ)) = (2 : ℤ) • (g.hom (1 : ℤ)) :=
    g.hom.map_smul (2 : ℤ) (1 : ℤ)
  have h_two : (2 : ℤ) • (1 : ℤ) = (2 : ℤ) := rfl
  rw [h_two] at h_smul
  have h_mul : (2 : ℤ) • (g.hom (1 : ℤ)) = 2 * (g.hom (1 : ℤ)) := rfl
  rw [h_mul] at h_smul
  have h2 : 2 * (g.hom (1 : ℤ)) = 1 := by
    rw [← h_smul, hw]
  have h_mod : (2 * (g.hom (1 : ℤ))) % 2 = 1 % 2 := by rw [h2]
  rw [Int.mul_emod_right] at h_mod
  revert h_mod
  decide

end InteractionsBetweenFunctorsAndLimits
