import Submission.RationalMapZero

noncomputable section

namespace Submission.Helpers

lemma isRationalMap_add (K : Set ℂ) {r s : C(K, ℂ)}
    (hr : IsRationalMap K r) (hs : IsRationalMap K s) :
    IsRationalMap K (r + s) := by
  obtain ⟨p, q, hq, hr⟩ := hr
  obtain ⟨p', q', hq', hs⟩ := hs
  refine ⟨p * q' + p' * q, q * q', ?_, ?_⟩
  · intro z
    simpa only [Polynomial.eval_mul] using mul_ne_zero (hq z) (hq' z)
  · intro z
    simp only [ContinuousMap.add_apply, Polynomial.eval_add, Polynomial.eval_mul,
      hr z, hs z]
    simpa only [mul_comm] using
      div_add_div (p.eval (z : ℂ)) (p'.eval (z : ℂ)) (hq z) (hq' z)

end Submission.Helpers
