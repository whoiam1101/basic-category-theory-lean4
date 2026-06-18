import Mathlib

open CategoryTheory

namespace Introduction

universe u v

theorem example_0_1 (X : Type u) : ∃ f : X → Unit, ∀ g : X → Unit, g = f :=
  ⟨fun _ => (), fun g => funext fun x => Unit.ext (g x) ()⟩

theorem example_0_2 (R : Type u) [Ring R] : ∃ f : ℤ →+* R, ∀ g : ℤ →+* R, g = f := by
  use Int.castRingHom R
  intro g
  ext n
  rw [eq_intCast g n]
  rfl

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
    ∀ (f : S → X), ∃! (g : C(S, X)), (g : S → X) = f := by
  intro f
  haveI : TopologicalSpace S := ⊥
  exact ⟨@ContinuousMap.mk S X ⊥ ‹_› f continuous_bot, rfl, by exact fun g hg => hg ▸ rfl⟩

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
    refine ⟨TensorProduct.lift f, ?_, ?_⟩
    · simp only [TensorProduct.mk_apply, TensorProduct.lift.tmul, implies_true]
    · intro g hg
      apply TensorProduct.ext
      ext u v
      dsimp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, TensorProduct.lift.tmul]
      exact hg u v

theorem lemma_0_7
    {k : Type*} [CommSemiring k]
    {U : Type u} [AddCommMonoid U] [Module k U]
    {V : Type v} [AddCommMonoid V] [Module k V]
    {T : Type (max u v)} [AddCommMonoid T] [Module k T]
    {T' : Type (max u v)} [AddCommMonoid T'] [Module k T']
    (b : U →ₗ[k] (V →ₗ[k] T)) (b' : U →ₗ[k] (V →ₗ[k] T'))
    (h : IsUniversalBilinearMap k U V T b)
    (h' : IsUniversalBilinearMap k U V T' b') :
    Nonempty (T ≃ₗ[k] T') := by
  let φ := Classical.choose <| h T' b'
  have hφ : (∀ u v, φ (b u v) = b' u v) ∧ (∀ g', (∀ u v, g' (b u v) = b' u v) → g' = φ) :=
    Classical.choose_spec <| h T' b'
  let ψ := Classical.choose <| h' T b
  have hψ : (∀ u v, ψ (b' u v) = b u v) ∧ (∀ g', (∀ u v, g' (b' u v) = b u v) → g' = ψ) :=
    Classical.choose_spec <| h' T b
  have hid' : (∀ u v, (ψ.comp φ) (b u v) = b u v) ∧
      (∀ g' : T →ₗ[k] T, (∀ u v, g' (b u v) = b u v) → g' = ψ.comp φ) := by
    constructor
    · intro u v
      rw [LinearMap.coe_comp, Function.comp_apply, hφ.1 u v, hψ.1 u v]
    · intro g' hg'
      have h'' := (Classical.choose_spec (h T b)).2
      have h1 : g' = Classical.choose (h T b) := h'' g' hg'
      have h2 : ψ.comp φ = Classical.choose (h T b) := h'' (ψ.comp φ) <| fun u v => by
        rw [LinearMap.comp_apply, hφ.1, hψ.1]
      rw [h1, h2]
  have hid'' : (∀ u v, (φ.comp ψ) (b' u v) = b' u v) ∧
      (∀ g' : T' →ₗ[k] T', (∀ u v, g' (b' u v) = b' u v) → g' = φ.comp ψ) := by
    constructor
    · intro u v
      rw [LinearMap.coe_comp, Function.comp_apply, hψ.1 u v, hφ.1 u v]
    · intro g' hg'
      have h'' := (Classical.choose_spec (h' T' b')).2
      have h1 : g' = Classical.choose (h' T' b') := h'' g' hg'
      have h2 : φ.comp ψ = Classical.choose (h' T' b') := h'' (φ.comp ψ) <| fun u v => by
        rw [LinearMap.comp_apply, hψ.1, hφ.1]
      rw [h1, h2]
  have h₁ : φ ∘ₗ ψ = LinearMap.id := by
    have eq1 : LinearMap.id = φ.comp ψ := hid''.2 LinearMap.id <| fun u v => by
      rw [LinearMap.id_coe, id_eq]
    exact eq1.symm
  have h₂ : ψ ∘ₗ φ = LinearMap.id := by
    have eq1 : LinearMap.id = ψ.comp φ := hid'.2 LinearMap.id <| fun u v => by
      rw [LinearMap.id_coe, id_eq]
    exact eq1.symm
  exact Nonempty.intro <| LinearEquiv.ofLinear φ ψ h₁ h₂

theorem example_0_8 {G H : Type*} [Group G] [Group H] (θ : G →* H) :
    let ι : θ.ker →* G := θ.ker.subtype
    let ε : G →* H := 1
    (∀ x : θ.ker, θ (ι x) = ε (ι x)) ∧
    ∀ (X : Type*) [Group X] (f : X →* G),
      (∀ x, θ (f x) = ε (f x)) →
      ∃! f' : X →* θ.ker, ∀ x, ι (f' x) = f x := by
  dsimp only [Lean.Elab.WF.paramLet, Subgroup.subtype_apply, MonoidHom.one_apply]
  refine ⟨?_, ?_⟩
  · simp only [Subtype.forall, MonoidHom.mem_ker, imp_self, implies_true]
  · intro X _ f h
    let f' : X →* θ.ker := {
      toFun := fun x => ⟨f x, by
        rw [MonoidHom.mem_ker]
        exact h x
      ⟩
      map_one' := by simp only [map_one, Subgroup.mk_eq_one]
      map_mul' := fun a b => by simp only [map_mul, MulMemClass.mk_mul_mk]
    }
    use f'
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, implies_true, true_and, f']
    intro g hg
    ext x
    rw [hg x]
    dsimp only [MonoidHom.coe_mk, OneHom.coe_mk]

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
  have h_mem_V_of_not_mem_U : ∀ (x : X), x ∉ U -> x ∈ V := by
    intro x
    have h_all : x ∈ U ∪ V := by
      rw [h_cov]
      exact Set.mem_univ x
    intro hxU
    rcases h_all with hxU' | hxV
    · contradiction
    · exact hxV
  let h (x : X) : Y :=
    if hxU : x ∈ U then
      f ⟨x, hxU⟩
    else
      g ⟨x, h_mem_V_of_not_mem_U x hxU⟩
  have hhf : ∀ (u : U), h u = f u := by
    intro u
    simp only [Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta, h]
  have hhg : ∀ (v : V), h v = g v := by
    intro v
    dsimp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, h]
    split_ifs with hv
    · exact ContinuousMap.congr_fun hfg ⟨v, ⟨hv, v.property⟩⟩
    · rfl
  have h_continous : Continuous h := by
    rw [←continuousOn_univ (f := h), ←h_cov]
    refine ContinuousOn.union_of_isOpen ?_ ?_ hU hV
    · apply continuousOn_iff_continuous_restrict.mpr
      have hhf : U.restrict h = f := funext hhf
      rw [hhf]
      exact f.continuous
    · apply continuousOn_iff_continuous_restrict.mpr
      have hhg : V.restrict h = g := funext hhg
      rw [hhg]
      exact g.continuous
  use ⟨h, h_continous⟩
  dsimp only
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext u
    dsimp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    exact hhf u
  · ext v
    dsimp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    exact hhg v
  · intro y ⟨hy₁, hy₂⟩
    ext x
    dsimp only [ContinuousMap.coe_mk]
    by_cases hxU : x ∈ U
    · rw [hhf ⟨x, hxU⟩]
      exact ContinuousMap.congr_fun hy₁ ⟨x, hxU⟩
    · have hxV : x ∈ V := h_mem_V_of_not_mem_U x hxU
      rw [hhg ⟨x, hxV⟩]
      exact ContinuousMap.congr_fun hy₂ ⟨x, hxV⟩

theorem exercise_0_10 : false := by sorry

theorem exercise_0_11 : false := by sorry

theorem exercise_0_12 : false := by sorry

theorem exercise_0_13_a : false := by sorry

theorem exercise_0_13_b : false := by sorry

theorem exercise_0_14_a : false := by sorry

theorem exercise_0_14_b : false := by sorry

theorem exercise_0_14_c : false := by sorry

theorem exercise_0_14_d : false := by sorry

end Introduction

#min_imports
