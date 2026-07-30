import Submission.RationalMapAdd

noncomputable section

namespace Submission.Helpers

lemma isRationalMap_smul (K : Set ℂ) (c : ℂ) {r : C(K, ℂ)}
    (hr : IsRationalMap K r) :
    IsRationalMap K (c • r) := by
  obtain ⟨p, q, hq, hr⟩ := hr
  refine ⟨Polynomial.C c * p, q, hq, ?_⟩
  intro z
  simp only [ContinuousMap.smul_apply, Polynomial.eval_mul, Polynomial.eval_C,
    hr z, smul_eq_mul]
  rw [mul_div_assoc]

end Submission.Helpers
