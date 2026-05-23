import Mathlib
import Submission.Helpers

namespace Submission

open Set

theorem sturm_separation (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  -- Step 1: W is nonzero on J (and in particular on [a,b])
  have hW_ne : ∀ x ∈ J, y₁ x * deriv y₂ x - y₂ x * deriv y₁ x ≠ 0 :=
    Helpers.wronskian_ne_zero_on_J p q y₁ y₂ J hJ_open hJ_conn hp hy₁ hy₁' hy₂ hy₂' hW
  have hW_ne_ab : ∀ x ∈ Icc a b, y₁ x * deriv y₂ x - y₂ x * deriv y₁ x ≠ 0 :=
    fun x hx => hW_ne x (hJ_sub hx)
  -- Step 2: y₂(a) and y₂(b) have opposite signs
  have hopp : y₂ a * y₂ b < 0 :=
    Helpers.y2_opposite_signs p q y₁ y₂ a b hab J hJ_open hJ_conn hJ_sub hp hy₁ hy₁' hy₂ hy₂' hW hza hzb hne
  -- Step 3: y₂ is continuous on [a,b]
  have hy₂_cont : ContinuousOn y₂ (Icc a b) := by
    apply ContinuousOn.mono _ hJ_sub
    exact fun x hx => (hy₂ x hx).continuousAt.continuousWithinAt
  -- Step 4: Existence - y₂ has a zero in (a,b) by IVT
  obtain ⟨c, hc_mem, hc_zero⟩ := Helpers.exists_zero_of_opposite_signs hab hy₂_cont hopp
  -- Step 5: Uniqueness - at most one zero by strict monotonicity of y₂/y₁
  have huniq := Helpers.at_most_one_zero_of_wronskian_ne_zero y₁ y₂ a b hab J hJ_sub hy₁ hy₂ hne hW_ne_ab
  -- Combine existence and uniqueness
  exact ⟨c, ⟨hc_mem, hc_zero⟩, fun c' ⟨hc'_mem, hc'_zero⟩ => huniq c' hc'_mem c hc_mem hc'_zero hc_zero⟩

end Submission
