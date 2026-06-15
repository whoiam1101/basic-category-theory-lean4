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

namespace Exercises

end Exercises

end Introduction

#min_imports
