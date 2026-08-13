-- Copyright (c) 2026 Samvel Safaryan. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Samvel Safaryan <samvelsafaryan1313@gmail.com>

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.ContinuousMap.Basic

namespace Introduction

universe u v

theorem example_0_1 (X : Type u) : ∃ f : X → Unit, ∀ g : X → Unit, g = f :=
  ⟨fun _ => (), fun g => by apply Subsingleton.elim⟩

theorem example_0_2 (R : Type u) [Ring R] : ∃ f : ℤ →+* R, ∀ g : ℤ →+* R, g = f :=
  ⟨Int.castRingHom R, fun g => by apply Subsingleton.elim⟩

theorem lemma_0_3 (A : Type) [Ring A]
    (h : ∀ R : Type, ∀ [Ring R], ∃ f : A →+* R, ∀ g : A →+* R, g = f) :
    Nonempty (A ≃+* ℤ) := by
  obtain ⟨f₁, hf₁⟩ := example_0_2 A
  obtain ⟨f₂, hf₂⟩ := h ℤ
  have h₁ : f₁.comp f₂ = RingHom.id A := by
    obtain ⟨f₃, hf₃⟩ := h A
    exact Eq.trans (hf₃ <| f₁.comp f₂) (hf₃ <| RingHom.id A).symm
  have h₂ : f₂.comp f₁ = RingHom.id ℤ := by
    obtain ⟨f₃, hf₃⟩ := example_0_2 ℤ
    exact Eq.trans (hf₃ <| f₂.comp f₁) (hf₃ <| RingHom.id ℤ).symm
  exact Nonempty.intro <| RingEquiv.ofRingHom f₂ f₁ h₂ h₁

theorem example_0_4
    {k S V W : Type*} [CommSemiring k]
    [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W]
    (b : Module.Basis S k V) (f : S → W) :
    ∃! g : V →ₗ[k] W, ∀ s : S, g (b s) = f s := by
  use Module.Basis.constr b k f
  simp only [Module.Basis.constr_basis, implies_true, true_and]
  intro g hg
  exact b.ext <| fun s => by rw [hg, b.constr_basis]

theorem example_0_5 (S X : Type*) [TopologicalSpace X] :
    letI : TopologicalSpace S := ⊥
    ∀ (f : S → X), ∃! (g : C(S, X)), (g : S → X) = f :=
  fun f => ⟨@ContinuousMap.mk S X ⊥ ‹_› f continuous_bot, rfl, by exact fun g hg => hg ▸ rfl⟩

def IsUniversalBilinearMap
    (k : Type*) [CommSemiring k]
    (U : Type u) [AddCommMonoid U] [Module k U]
    (V : Type v) [AddCommMonoid V] [Module k V]
    (T : Type (max u v)) [AddCommMonoid T] [Module k T]
    (b : U →ₗ[k] (V →ₗ[k] T)) : Prop :=
  ∀ (W : Type (max u v)) [AddCommMonoid W] [Module k W]
    (f : U →ₗ[k] (V →ₗ[k] W)),
    ∃! g : T →ₗ[k] W, ∀ u v, g (b u v) = f u v

theorem example_0_6
    (k : Type*) [CommSemiring k]
    (U : Type u) [AddCommMonoid U] [Module k U]
    (V : Type v) [AddCommMonoid V] [Module k V] :
    ∃ (T : Type (max u v))
      (_ : AddCommMonoid T)
      (_ : Module k T)
      (b : U →ₗ[k] (V →ₗ[k] T)),
      IsUniversalBilinearMap k U V T b := by
  refine ⟨TensorProduct k U V, inferInstance, inferInstance, TensorProduct.mk k U V, ?_⟩
  · intro W addW modW f
    refine ⟨TensorProduct.lift f, ?_, fun g hg => ?_⟩
    · simp only [TensorProduct.mk_apply, TensorProduct.lift.tmul, implies_true]
    · apply TensorProduct.ext
      ext u v
      exact (hg u v).trans (TensorProduct.lift.tmul u v).symm

theorem lemma_0_7
    {k : Type*} [CommSemiring k]
    {U : Type u} [AddCommMonoid U] [Module k U]
    {V : Type v} [AddCommMonoid V] [Module k V]
    {T : Type (max u v)} [AddCommMonoid T] [Module k T]
    {T' : Type (max u v)} [AddCommMonoid T'] [Module k T']
    (b : U →ₗ[k] (V →ₗ[k] T)) (b' : U →ₗ[k] (V →ₗ[k] T'))
    (h : IsUniversalBilinearMap k U V T b)
    (h' : IsUniversalBilinearMap k U V T' b') :
    ∃! j : T ≃ₗ[k] T', ∀ u v, j (b u v) = b' u v := by
  let φ := Classical.choose <| h T' b'
  have hφ := Classical.choose_spec <| h T' b'
  let ψ := Classical.choose <| h' T b
  have hψ := Classical.choose_spec <| h' T b
  have h₁ : φ ∘ₗ ψ = LinearMap.id :=
    have huniq := (Classical.choose_spec (h' T' b')).2
    (huniq (φ.comp ψ) fun u v => (congr_arg φ (hψ.1 u v)).trans (hφ.1 u v)).trans
      (huniq LinearMap.id fun _ _ => rfl).symm
  have h₂ : ψ ∘ₗ φ = LinearMap.id :=
    have huniq := (Classical.choose_spec (h T b)).2
    (huniq (ψ.comp φ) fun u v => (congr_arg ψ (hφ.1 u v)).trans (hψ.1 u v)).trans
      (huniq LinearMap.id fun _ _ => rfl).symm
  refine ⟨LinearEquiv.ofLinear φ ψ h₁ h₂, ?_, ?_⟩
  · intro u v
    simpa using hφ.1 u v
  · intro j hj
    have h_j_lin : (j : T →ₗ[k] T') = φ := (Classical.choose_spec (h T' b')).2 j hj
    exact LinearEquiv.ext fun x => congrArg (fun (f : T →ₗ[k] T') => f x) h_j_lin

theorem example_0_8 {G H : Type*} [Group G] [Group H] (θ : G →* H) :
    let ι : θ.ker →* G := θ.ker.subtype
    let ε : G →* H := 1
    (∀ x : θ.ker, θ (ι x) = ε (ι x)) ∧
    ∀ (X : Type*) [Group X] (f : X →* G),
      (∀ x, θ (f x) = ε (f x)) →
      ∃! f' : X →* θ.ker, ∀ x, ι (f' x) = f x := by
  dsimp only [Lean.Elab.WF.paramLet, Subgroup.subtype_apply, MonoidHom.one_apply]
  refine ⟨fun x => x.property, fun X _ f h => ⟨f.codRestrict θ.ker h, fun _ => rfl,
    fun g hg => MonoidHom.ext fun x => Subtype.ext (hg x)⟩⟩

def inclusionMap {X : Type*} [TopologicalSpace X]
    {s t : Set X} (h : s ⊆ t) : C(s, t) where
  toFun x := ⟨x.val, h x.property⟩
  continuous_toFun := continuous_inclusion h

def inclusionToSpace {X : Type*} [TopologicalSpace X] (s : Set X) : C(s, X) where
  toFun x := x.val
  continuous_toFun := continuous_subtype_val

open Classical in
theorem example_0_9 {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (h_cov : U ∪ V = Set.univ) :
    let i := inclusionMap (@Set.inter_subset_left X U V)
    let j := inclusionMap (@Set.inter_subset_right X U V)
    let j' := inclusionToSpace U
    let i' := inclusionToSpace V
    ∀ (Y : Type*) [TopologicalSpace Y] (f : C(U, Y)) (g : C(V, Y)),
      (f.comp i = g.comp j) →
      ∃! (h : C(X, Y)), (h.comp j' = f) ∧ (h.comp i' = g) := by
  dsimp only [inclusionMap, inclusionToSpace, Lean.Elab.WF.paramLet]
  intro Y hY f g hfg
  have h_mem_V_of_not_mem_U : ∀ (x : X), x ∉ U → x ∈ V :=
    fun x hx => (h_cov.symm ▸ Set.mem_univ x : x ∈ U ∪ V).resolve_left hx
  let h (x : X) : Y := if hx : x ∈ U then f ⟨x, hx⟩ else g ⟨x, h_mem_V_of_not_mem_U x hx⟩
  have hhf : ∀ (u : U), h u = f u := fun u => dif_pos u.property
  have hhg : ∀ (v : V), h v = g v := fun v =>
    if hv : v.val ∈ U then
      (dif_pos hv).trans <| ContinuousMap.congr_fun hfg ⟨v.val, hv, v.property⟩
    else
      dif_neg hv
  have h_continous : Continuous h := by
    rw [←continuousOn_univ (f := h), ←h_cov]
    refine ContinuousOn.union_of_isOpen ?_ ?_ hU hV
    · apply continuousOn_iff_continuous_restrict.mpr
      have hhf : U.restrict h = f := funext hhf
      exact hhf ▸ f.continuous
    · apply continuousOn_iff_continuous_restrict.mpr
      have hhg : V.restrict h = g := funext hhg
      exact hhg ▸ g.continuous
  refine ⟨⟨h, h_continous⟩, ⟨ContinuousMap.ext hhf, ContinuousMap.ext hhg⟩, fun y ⟨hy₁, hy₂⟩ => ?_⟩
  · exact ContinuousMap.ext fun x =>
      if hx : x ∈ U then
        (ContinuousMap.congr_fun hy₁ ⟨x, hx⟩).trans (hhf ⟨x, hx⟩).symm
      else
        let hxV := h_mem_V_of_not_mem_U x hx
        (ContinuousMap.congr_fun hy₂ ⟨x, hxV⟩).trans (hhg ⟨x, hxV⟩).symm

theorem exercise_0_10 (S : Type*) (X : Type*) [TopologicalSpace X] :
    letI : TopologicalSpace S := ⊤
    ∀ (f : X → S), ∃! (g : C(X, S)), (g : X → S) = f :=
  fun f => ⟨@ContinuousMap.mk X S ‹_› ⊤ f continuous_top, rfl, by exact fun g hg => hg ▸ rfl⟩

theorem exercise_0_11 {G H : Type*} [Group G] [Group H] (θ : G →* H) :
    let ι : θ.ker →* G := θ.ker.subtype
    let ε : G →* H := 1
    (∀ x : θ.ker, θ (ι x) = ε (ι x)) ∧
    ∀ (X : Type*) [Group X] (f : X →* G),
      (∀ x, θ (f x) = ε (f x)) →
      ∃! f' : X →* θ.ker, ∀ x, ι (f' x) = f x := example_0_8 θ

open Classical in
theorem exercise_0_12 {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (h_cov : U ∪ V = Set.univ) :
    let i := inclusionMap (@Set.inter_subset_left X U V)
    let j := inclusionMap (@Set.inter_subset_right X U V)
    let j' := inclusionToSpace U
    let i' := inclusionToSpace V
    ∀ (Y : Type*) [TopologicalSpace Y] (f : C(U, Y)) (g : C(V, Y)),
      (f.comp i = g.comp j) →
      ∃! (h : C(X, Y)), (h.comp j' = f) ∧ (h.comp i' = g) :=
  example_0_9 U V hU hV h_cov

def IsInitialRingWithPoint (A : Type*) [Ring A] (a : A) : Prop :=
  ∀ {R : Type*} [Ring R] (r : R), ∃! φ : A →+* R, φ a = r

open Polynomial in
theorem exercise_0_13_a : IsInitialRingWithPoint ℤ[X] X := by
  intro R _ r
  use (aeval r).toRingHom
  dsimp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  refine ⟨aeval_X r, fun g hg => ?_⟩
  · ext p
    · simp only [eq_intCast]
    · rw [hg, RingHom.coe_coe, aeval_X]

open Polynomial in
theorem exercise_0_13_b {A : Type u} [Ring A] (a : A)
    (h : IsInitialRingWithPoint.{u, u} A a) :
    ∃! ι : ℤ[X] ≃+* A, ι X = a := by
  rcases h (ULift.up (X : ℤ[X])) with ⟨g', hg'_a, hg'_uniq⟩
  rcases exercise_0_13_a a with ⟨f, hf_X, hf_uniq⟩
  let g : A →+* ℤ[X] := ULift.ringEquiv.toRingHom.comp g'
  have hfg : f.comp g = RingHom.id A := by
    have h_apply : (f.comp g) a = a := by
      dsimp [g]
      rw [hg'_a]
      exact hf_X
    have h_uniq : ∀ {x₁ x₂ : A →+* A}, (x₁ a = a) → (x₂ a = a) → x₁ = x₂ := by
      intro x₁ x₂ hx₁ hx₂
      exact (h (R := A) a).unique hx₁ hx₂
    exact h_uniq h_apply rfl
  have hgf : g.comp f = RingHom.id ℤ[X] := by
    apply Polynomial.ringHom_ext
    · simp only [eq_intCast, map_intCast, implies_true]
    · rw [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, hf_X]
      dsimp [g]
      rw [hg'_a]
      rfl
  use RingEquiv.ofRingHom f g hfg hgf
  dsimp
  refine ⟨hf_X, fun y hy => ?_⟩
  · ext x
    rw [RingEquiv.ofRingHom_apply, ←hf_uniq y hy, RingHom.coe_coe]

def IsUniversalCone {k : Type*} [Semiring k]
    {X : Type u} [AddCommMonoid X] [Module k X]
    {Y : Type v} [AddCommMonoid Y] [Module k Y]
    (P : Type*) [AddCommMonoid P] [Module k P]
    (p₁ : P →ₗ[k] X) (p₂ : P →ₗ[k] Y) : Prop :=
  ∀ (V : Type (max u v)) [AddCommMonoid V] [Module k V]
    (f₁ : V →ₗ[k] X) (f₂ : V →ₗ[k] Y),
    ∃! f : V →ₗ[k] P, p₁.comp f = f₁ ∧ p₂.comp f = f₂

theorem exercise_0_14_a {k : Type*} [Semiring k]
    {X : Type u} [AddCommMonoid X] [Module k X]
    {Y : Type v} [AddCommMonoid Y] [Module k Y] :
    ∃ (P : Type (max u v)) (_ : AddCommMonoid P) (_ : Module k P)
      (p₁ : P →ₗ[k] X) (p₂ : P →ₗ[k] Y), IsUniversalCone P p₁ p₂ := by
  refine ⟨X × Y, inferInstance, inferInstance, LinearMap.fst k X Y, LinearMap.snd k X Y, ?_⟩
  · intro V _ _ f₁ f₂
    refine ⟨LinearMap.prod f₁ f₂, ⟨by rfl, by rfl⟩, fun f hf => ?_⟩
    · ext x
      · exact LinearMap.congr_fun hf.1 x
      · exact LinearMap.congr_fun hf.2 x

theorem exercise_0_14_b {k : Type*} [Semiring k]
    {X : Type u} [AddCommMonoid X] [Module k X]
    {Y : Type v} [AddCommMonoid Y] [Module k Y]
    {P : Type (max u v)} [AddCommMonoid P] [Module k P]
    {P' : Type (max u v)} [AddCommMonoid P'] [Module k P']
    (p₁ : P →ₗ[k] X) (p₂ : P →ₗ[k] Y)
    (p₁' : P' →ₗ[k] X) (p₂' : P' →ₗ[k] Y)
    (h : IsUniversalCone P p₁ p₂)
    (h' : IsUniversalCone P' p₁' p₂') :
    ∃ i : P ≃ₗ[k] P', p₁'.comp i.toLinearMap = p₁ ∧ p₂'.comp i.toLinearMap = p₂ := by
  rcases h P' p₁' p₂' with ⟨ψ, ⟨hψ₁, hψ₂⟩, hψ_uniq⟩
  rcases h' P p₁ p₂ with ⟨φ, ⟨hφ₁, hφ₂⟩, hφ_uniq⟩
  rcases h P p₁ p₂ with ⟨idP, ⟨_, _⟩, hidP_uniq⟩
  rcases h' P' p₁' p₂' with ⟨idP', ⟨_, _⟩, hidP'_uniq⟩
  have hψφ : ψ.comp φ = LinearMap.id := by
    have h₁ : p₁.comp (ψ.comp φ) = p₁ := by
      nth_rw 2 [←hφ₁]
      rw [←hψ₁]
      rfl
    have h₂ : p₂.comp (ψ.comp φ) = p₂ := by
      nth_rw 2 [←hφ₂]
      rw [←hψ₂]
      rfl
    have h₃ := hidP_uniq (ψ.comp φ) ⟨h₁, h₂⟩
    have h₄ := hidP_uniq LinearMap.id ⟨rfl, rfl⟩
    exact Eq.trans h₃ h₄.symm
  have hφψ : φ.comp ψ = LinearMap.id := by
    have h₁ : p₁'.comp (φ.comp ψ) = p₁' := by
      nth_rw 2 [←hψ₁]
      rw [←hφ₁]
      rfl
    have h₂ : p₂'.comp (φ.comp ψ) = p₂' := by
      nth_rw 2 [←hψ₂]
      rw [←hφ₂]
      rfl
    have h₃ := hidP'_uniq (φ.comp ψ) ⟨h₁, h₂⟩
    have h₄ := hidP'_uniq LinearMap.id ⟨rfl, rfl⟩
    exact Eq.trans h₃ h₄.symm
  exact ⟨LinearEquiv.ofLinear φ ψ hφψ hψφ, ⟨hφ₁, hφ₂⟩⟩

def IsUniversalCoCone {k : Type*} [Semiring k]
    {X : Type u} [AddCommMonoid X] [Module k X]
    {Y : Type v} [AddCommMonoid Y] [Module k Y]
    (Q : Type*) [AddCommMonoid Q] [Module k Q]
    (q₁ : X →ₗ[k] Q) (q₂ : Y →ₗ[k] Q) : Prop :=
  ∀ (V : Type (max u v)) [AddCommMonoid V] [Module k V]
    (f₁ : X →ₗ[k] V) (f₂ : Y →ₗ[k] V),
    ∃! f : Q →ₗ[k] V, f.comp q₁ = f₁ ∧ f.comp q₂ = f₂

theorem exercise_0_14_c {k : Type*} [Semiring k]
    {X : Type u} [AddCommMonoid X] [Module k X]
    {Y : Type v} [AddCommMonoid Y] [Module k Y] :
    ∃ (Q : Type (max u v)) (_ : AddCommMonoid Q) (_ : Module k Q)
      (q₁ : X →ₗ[k] Q) (q₂ : Y →ₗ[k] Q), IsUniversalCoCone Q q₁ q₂ := by
  refine ⟨X × Y, inferInstance, inferInstance, LinearMap.inl k X Y, LinearMap.inr k X Y, ?_⟩
  · intro V _ _ f₁ f₂
    refine ⟨LinearMap.coprod f₁ f₂, ⟨?_, ?_⟩, fun f hf => ?_⟩
    · apply LinearMap.coprod_inl
    · apply LinearMap.coprod_inr
    · ext x
      · exact LinearMap.congr_fun (hf.1.trans (LinearMap.coprod_inl f₁ f₂).symm) x
      · exact LinearMap.congr_fun (hf.2.trans (LinearMap.coprod_inr f₁ f₂).symm) x

theorem exercise_0_14_d {k : Type*} [Semiring k]
    {X : Type u} [AddCommMonoid X] [Module k X]
    {Y : Type v} [AddCommMonoid Y] [Module k Y]
    {Q : Type (max u v)} [AddCommMonoid Q] [Module k Q]
    {Q' : Type (max u v)} [AddCommMonoid Q'] [Module k Q']
    (q₁ : X →ₗ[k] Q) (q₂ : Y →ₗ[k] Q)
    (q₁' : X →ₗ[k] Q') (q₂' : Y →ₗ[k] Q')
    (h : IsUniversalCoCone Q q₁ q₂)
    (h' : IsUniversalCoCone Q' q₁' q₂') :
    ∃ i : Q ≃ₗ[k] Q', i.toLinearMap.comp q₁ = q₁' ∧ i.toLinearMap.comp q₂ = q₂' := by
  rcases h Q' q₁' q₂' with ⟨ψ, ⟨hψ₁, hψ₂⟩, hψ_uniq⟩
  rcases h' Q q₁ q₂ with ⟨φ, ⟨hφ₁, hφ₂⟩, hφ_uniq⟩
  rcases h Q q₁ q₂ with ⟨idQ, ⟨_, _⟩, hidQ_uniq⟩
  rcases h' Q' q₁' q₂' with ⟨idQ', ⟨_, _⟩, hidQ'_uniq⟩
  have hφψ : φ.comp ψ = LinearMap.id := by
    have h₁ : (φ.comp ψ).comp q₁ = q₁ := by
      nth_rw 2 [←hφ₁]
      rw [←hψ₁]
      rfl
    have h₂ : (φ.comp ψ).comp q₂ = q₂ := by
      nth_rw 2 [←hφ₂]
      rw [←hψ₂]
      rfl
    have h₃ := hidQ_uniq (φ.comp ψ) ⟨h₁, h₂⟩
    have h₄ := hidQ_uniq LinearMap.id ⟨rfl, rfl⟩
    exact Eq.trans h₃ h₄.symm
  have hψφ : ψ.comp φ = LinearMap.id := by
    have h₁ : (ψ.comp φ).comp q₁' = q₁' := by
      nth_rw 2 [←hψ₁]
      rw [←hφ₁]
      rfl
    have h₂ : (ψ.comp φ).comp q₂' = q₂' := by
      nth_rw 2 [←hψ₂]
      rw [←hφ₂]
      rfl
    have h₃ := hidQ'_uniq (ψ.comp φ) ⟨h₁, h₂⟩
    have h₄ := hidQ'_uniq LinearMap.id ⟨rfl, rfl⟩
    exact Eq.trans h₃ h₄.symm
  exact ⟨LinearEquiv.ofLinear ψ φ hψφ hφψ, ⟨hψ₁, hψ₂⟩⟩

end Introduction
