-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.CompletePartialOrder
import Mathlib.SetTheory.Cardinal.Order

namespace Chapter3

universe u v w

open CategoryTheory

theorem theorem_3_2_1 {A : Type u} {B : Type v} (f : A → B) (g : B → A)
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (A ≃ B) :=
  Function.Embedding.antisymm ⟨f, hf⟩ ⟨g, hg⟩

theorem theorem_3_2_2 (A : Type u) : Cardinal.mk A < Cardinal.mk (Set A) := by
  rw [Cardinal.mk_set]
  exact Cardinal.cantor _

theorem corollary_3_2_3 (A : Type u) : ∃ B : Type u, Cardinal.mk A < Cardinal.mk B :=
  ⟨Set A, theorem_3_2_2 A⟩

theorem proposition_3_2_4 (I : Type u) (A : I → Type u) :
    ∃ B : Type u, ∀ i : I, ¬ Nonempty (A i ≃ B) := by
  refine ⟨Set (Σ i : I, A i), ?_⟩
  intro i
  have h_le : Cardinal.mk (A i) ≤ Cardinal.mk (Σ j : I, A j) :=
    Cardinal.mk_le_of_injective (f := fun a : A i => ⟨i, a⟩) (by
      intro a a' h
      cases h
      rfl)
  have h_lt : Cardinal.mk (Σ j : I, A j) < Cardinal.mk (Set (Σ j : I, A j)) := by
    rw [Cardinal.mk_set]
    exact Cardinal.cantor _
  have h_lt' : Cardinal.mk (A i) < Cardinal.mk (Set (Σ j : I, A j)) := h_le.trans_lt h_lt
  intro ⟨e⟩
  exact (ne_of_lt h_lt') (Cardinal.eq.mpr ⟨e⟩)

abbrev def_3_2_10 := CategoryTheory.Cat

theorem exercise_3_2_12a {A : Type u} (θ : Set A → Set A) (hθ : Monotone θ) :
    ∃ S : Set A, θ S = S := by
  let f : Set A →o Set A := ⟨θ, hθ⟩
  exact ⟨f.lfp, f.map_lfp⟩

theorem exercise_3_2_12b {A B : Type u} (f : A → B) (g : B → A) :
    ∃ S : Set A, g '' (Set.univ \ f '' S) = Sᶜ := by
  classical
  let θ : Set A → Set A := fun T => (g '' (Set.univ \ f '' T))ᶜ
  have hθ : Monotone θ := by
    intro T T' hTT'
    exact Set.compl_subset_compl.mpr
      (Set.image_mono (Set.diff_subset_diff_right (Set.image_mono hTT')))
  rcases exercise_3_2_12a θ hθ with ⟨S, hS⟩
  refine ⟨S, ?_⟩
  conv_rhs => rw [hS.symm]
  dsimp [θ]
  rw [compl_compl]

theorem exercise_3_2_12c {A B : Type u} (f : A → B) (g : B → A)
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (A ≃ B) := by
  obtain ⟨h, hbij⟩ := Function.Embedding.schroeder_bernstein hf hg
  exact ⟨Equiv.ofBijective h hbij⟩

theorem exercise_3_2_13a {A : Type u} (f : A → Set A) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

theorem exercise_3_2_13b (A : Type u) : Cardinal.mk A < Cardinal.mk (Set A) := by
  rw [Cardinal.mk_set]
  exact Cardinal.cantor _

lemma exercise_3_2_14a_unit_injective {C : Type u} [Category.{v} C] {U : C ⥤ Type w}
    (F : Type w ⥤ C) (adj : F ⊣ U) {A₀ : C} {x y : U.obj A₀} (hxy : x ≠ y) :
    ∀ S : Type w, Function.Injective ((adj.unit.app S : S → U.obj (F.obj S))) := by
  classical
  intro S a b h
  by_contra hne
  let hf : S → U.obj A₀ := fun z => if z = a then x else y
  let g : F.obj S ⟶ A₀ := (adj.homEquiv S A₀).symm (TypeCat.ofHom hf)
  have h_factor : hf = fun z =>
      (U.map g : U.obj (F.obj S) → U.obj A₀) ((adj.unit.app S : S → U.obj (F.obj S)) z) := by
    have h1 : (adj.homEquiv S A₀) g = TypeCat.ofHom hf := by
      dsimp [g]
      exact Equiv.apply_symm_apply _ _
    have h2 : (adj.homEquiv S A₀) g = adj.unit.app S ≫ U.map g := rfl
    have h3 : TypeCat.ofHom hf = adj.unit.app S ≫ U.map g := by
      rw [← h1, h2]
    ext z
    have hz : (TypeCat.ofHom hf) z = (adj.unit.app S ≫ U.map g) z :=
      congrFun (congrArg (fun f : S ⟶ U.obj A₀ => (f : S → U.obj A₀)) h3) z
    simpa using hz
  have hfa : hf a = x := by
    dsimp [hf]
    rw [if_pos rfl]
  have hfb : hf b = y := by
    have hba : b ≠ a := fun hba => hne hba.symm
    dsimp [hf]
    exact if_neg hba
  have : x = y := by
    rw [← hfa, ← hfb, congrFun h_factor a, congrFun h_factor b, h]
  exact hxy this

theorem exercise_3_2_14a {C : Type u} [Category.{v} C] {U : C ⥤ Type w}
    (F : Type w ⥤ C) (adj : F ⊣ U) {A₀ : C} {x y : U.obj A₀} (hxy : x ≠ y) :
    ∀ (I : Type w) (A : I → C), ∃ W : C, ∀ i : I, ¬ Nonempty (A i ≅ W) := by
  classical
  intro I A
  let S : Type w := Set (Σ i : I, U.obj (A i))
  refine ⟨F.obj S, ?_⟩
  intro i
  have h_le : Cardinal.mk (U.obj (A i)) ≤ Cardinal.mk (Σ j : I, U.obj (A j)) :=
    Cardinal.mk_le_of_injective (f := fun a : U.obj (A i) => ⟨i, a⟩) (by
      intro a a' h
      cases h
      rfl)
  have h_lt : Cardinal.mk (Σ j : I, U.obj (A j)) <
      Cardinal.mk (Set (Σ j : I, U.obj (A j))) := by
    rw [Cardinal.mk_set]
    exact Cardinal.cantor _
  have h_le2 : Cardinal.mk (Set (Σ j : I, U.obj (A j))) ≤ Cardinal.mk (U.obj (F.obj S)) := by
    apply Cardinal.mk_le_of_injective
    exact exercise_3_2_14a_unit_injective F adj hxy S
  have h_lt' : Cardinal.mk (U.obj (A i)) < Cardinal.mk (U.obj (F.obj S)) :=
    h_le.trans_lt (h_lt.trans_le h_le2)
  intro ⟨e⟩
  exact (ne_of_lt h_lt') (Cardinal.eq.mpr ⟨(U.mapIso e).toEquiv⟩)

def catConnectedComponents : Cat.{u, u} ⥤ Type u where
  obj X := ConnectedComponents X
  map F := TypeCat.ofHom (F.toFunctor.mapConnectedComponents)
  map_id X := by
    ext c
    refine Quotient.inductionOn c ?_
    intro x
    simp
  map_comp F G := by
    ext c
    refine Quotient.inductionOn c ?_
    intro x
    simp

structure Indiscrete (X : Type u) where
  of :: as : X

instance (X : Type u) : Category (Indiscrete X) where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp := by intro X Y f; rfl
  comp_id := by intro X Y f; rfl
  assoc := by intro W X Y Z f g h; rfl

def indiscreteCat : Type u ⥤ Cat.{u, u} where
  obj X := Cat.of (Indiscrete X)
  map f :=
    (Functor.toCatHom
      { obj := fun x => Indiscrete.of (f x.as)
        map := fun _ => PUnit.unit
        map_id := fun _ => rfl
        map_comp := fun _ _ => rfl })
  map_id X := by
    apply Cat.ext
    apply CategoryTheory.Functor.ext
    · intro x y f
      rfl
    · intro x
      cases x
      simp
  map_comp f g := by
    apply Cat.ext
    apply CategoryTheory.Functor.ext
    · intro x y h
      rfl
    · intro x
      simp

noncomputable def catConnectedComponents_typeToCat_homEquiv (X : Cat.{u, u}) (Y : Type u) :
    (catConnectedComponents.obj X ⟶ Y) ≃ (X ⟶ typeToCat.obj Y) :=
  (TypeCat.homEquiv.trans (ConnectedComponents.typeToCatHomEquiv (X : Type u) Y)).trans
    (Cat.Hom.equivFunctor X (Cat.of (Discrete Y))).symm

noncomputable def discrete_objects_homEquiv (X : Type u) (C : Cat.{u, u}) :
    (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) := by
  refine (Cat.Hom.equivFunctor (Cat.of (Discrete X)) C).trans ?_
  refine
    ({ toFun := fun F x => F.obj ⟨x⟩
       invFun := Discrete.functor
       left_inv := by
         intro F
         apply Discrete.functor_ext
         intro i
         rfl
       right_inv := by
         intro f
         rfl } : (Discrete X ⥤ C) ≃ (X → C)).trans TypeCat.homEquiv.symm

noncomputable def objects_indiscrete_homEquiv (C : Cat.{u, u}) (X : Type u) :
    (Cat.objects.obj C ⟶ X) ≃ (C ⟶ indiscreteCat.obj X) := by
  refine (TypeCat.homEquiv.trans ?_).trans (Cat.Hom.equivFunctor C (Cat.of (Indiscrete X))).symm
  exact
    { toFun := fun f =>
        { obj := fun c => Indiscrete.of (f c)
          map := fun _ => PUnit.unit
          map_id := fun _ => rfl
          map_comp := fun _ _ => rfl }
      invFun := fun F c => (F.obj c).as
      left_inv := by
        intro f
        rfl
      right_inv := by
        intro F
        apply CategoryTheory.Functor.ext
        · intro c c' m
          rfl
        · intro c
          change Indiscrete.of ((F.obj c).as) = F.obj c
          cases F.obj c
          rfl }

noncomputable def adj_catConnectedComponents_typeToCat : catConnectedComponents ⊣ typeToCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => catConnectedComponents_typeToCat_homEquiv X Y
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        ext c
        refine Quotient.inductionOn c ?_
        intro x
        change TypeCat.ofHom (ConnectedComponents.liftFunctor X' ((f ≫ g).toFunctor)) ⟦x⟧ =
          (ConnectedComponents.liftFunctor X g.toFunctor)
            (f.toFunctor.mapConnectedComponents ⟦x⟧)
        simp [ConnectedComponents.liftFunctor]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply Cat.ext
        change ConnectedComponents.functorToDiscrete Y' (f ≫ g) =
          ConnectedComponents.functorToDiscrete Y f ⋙ Discrete.functor (Discrete.mk ∘ g)
        apply CategoryTheory.Functor.ext
        · intro c c' m
          apply Subsingleton.elim
        · intro c
          simp [ConnectedComponents.functorToDiscrete, Function.comp] }

noncomputable def adj_typeToCat_objects : typeToCat ⊣ Cat.objects :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X C => discrete_objects_homEquiv X C
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply Cat.ext
        change Discrete.functor (f ≫ g) =
          Discrete.functor (Discrete.mk ∘ f) ⋙ Discrete.functor g
        apply CategoryTheory.Functor.ext
        · intro x y m
          rcases x with ⟨x'⟩
          rcases y with ⟨y'⟩
          rcases m with ⟨⟨h⟩⟩
          have hxy : x' = y' := by simpa using h
          subst hxy
          simp
        · intro x
          simp [Function.comp]
      homEquiv_naturality_right := by
        intro X Y Y' f g
        ext x
        change ((f ≫ g).toFunctor.obj ⟨x⟩) = g.toFunctor.obj (f.toFunctor.obj ⟨x⟩)
        simp }

noncomputable def adj_objects_indiscrete : Cat.objects ⊣ indiscreteCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun C X => objects_indiscrete_homEquiv C X
      homEquiv_naturality_left_symm := by
        intro C' C X f g
        ext c
        change ((f ≫ g).toFunctor.obj c).as = (g.toFunctor.obj (f.toFunctor.obj c)).as
        simp
      homEquiv_naturality_right := by
        intro C X X' f g
        apply Cat.ext
        apply CategoryTheory.Functor.ext
        · intro c c' m
          rfl
        · intro c
          change Indiscrete.of ((f ≫ g) c) = Indiscrete.of (g (f c))
          simp }

abbrev exercise_3_2_16_C := catConnectedComponents

abbrev exercise_3_2_16_D := typeToCat

abbrev exercise_3_2_16_O := Cat.objects

abbrev exercise_3_2_16_I := indiscreteCat

noncomputable def exercise_3_2_16_C_adj_D : exercise_3_2_16_C ⊣ exercise_3_2_16_D :=
  adj_catConnectedComponents_typeToCat

noncomputable def exercise_3_2_16_D_adj_O : exercise_3_2_16_D ⊣ exercise_3_2_16_O :=
  adj_typeToCat_objects

noncomputable def exercise_3_2_16_O_adj_I : exercise_3_2_16_O ⊣ exercise_3_2_16_I :=
  adj_objects_indiscrete

end Chapter3
