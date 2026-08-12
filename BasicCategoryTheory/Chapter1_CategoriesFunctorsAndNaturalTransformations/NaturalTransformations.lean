-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib

namespace NaturalTransformations

universe u v u' v'

open CategoryTheory

theorem lemma_1_3_11 {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F G : C ⥤ D} (α : F ⟶ G) :
    IsIso α ↔ ∀ X : C, IsIso (α.app X) :=
  NatTrans.isIso_iff_isIso_app α

theorem exercise_1_3_26 {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] {F G : C ⥤ D} (α : F ⟶ G) :
    IsIso α ↔ ∀ X : C, IsIso (α.app X) :=
  NatTrans.isIso_iff_isIso_app α

def exercise_1_3_27 (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] :
    (Cᵒᵖ ⥤ Dᵒᵖ) ≌ (C ⥤ D)ᵒᵖ :=
  (Functor.opUnopEquiv C D).symm

def exercise_1_3_28a (A B : Type u) : A × (A → B) → B :=
  fun ⟨a, f⟩ => f a

def exercise_1_3_28b (A B : Type u) : A → (A → B) → B :=
  fun a f => f a

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

def exercise_1_3_34_refl (C : Type u) [Category.{v} C] : C ≌ C :=
  CategoryTheory.Equivalence.refl

def exercise_1_3_34_symm {C D : Type u} [Category.{v} C] [Category.{v} D]
    (e : C ≌ D) : D ≌ C :=
  e.symm

def exercise_1_3_34_trans {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    (e₁ : C ≌ D) (e₂ : D ≌ E) : C ≌ E :=
  e₁.trans e₂

end NaturalTransformations

#min_imports
