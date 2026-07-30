import Submission.SmoothExtension

open Set

noncomputable section

namespace Submission.Helpers

def cauchyIntegrand (K : Set ℂ) (h : ℂ → ℂ)
    (hK0 : ∀ z ∈ K, h z = 0) (w : ℂ) : C(K, ℂ) where
  toFun z := h w * (w - z)⁻¹
  continuous_toFun := by
    by_cases hw : h w = 0
    · simpa only [hw, zero_mul] using
        (continuous_const : Continuous fun _ : K => (0 : ℂ))
    · have hwK : w ∉ K := fun hwK => hw (hK0 w hwK)
      exact continuous_const.mul <|
        (continuous_const.sub continuous_subtype_val).inv₀ fun z hz =>
          hwK (sub_eq_zero.mp hz ▸ z.property)

end Submission.Helpers
