import Submission.CauchyIntegrandContinuous

open Set

noncomputable section

namespace Submission.Helpers

lemma cauchyIntegrand_mem_rationalMaps (K : Set ℂ) (h : ℂ → ℂ)
    (hK0 : ∀ z ∈ K, h z = 0) (w : ℂ) :
    cauchyIntegrand K h hK0 w ∈ rationalMaps K := by
  by_cases hw : h w = 0
  · have hz : cauchyIntegrand K h hK0 w = 0 := by
      ext z
      simp [cauchyIntegrand, hw]
    rw [hz]
    exact (rationalMaps K).zero_mem
  · have hwK : w ∉ K := fun hwK => hw (hK0 w hwK)
    refine ⟨Polynomial.C (h w), Polynomial.C w - Polynomial.X, ?_, ?_⟩
    · intro z
      simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      exact sub_ne_zero.mpr fun hwz => hwK (hwz ▸ z.property)
    · intro z
      simp [cauchyIntegrand, div_eq_mul_inv]

end Submission.Helpers
