import ChallengeDeps
import Submission.CentralizerLeAdjoinTarget

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Helper lemmas for the diagonal tensor power proof
-/

open scoped TensorProduct

namespace Submission.DiagMapTarget

section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- If e is idempotent and ker(e) ≤ ker(f), then f * e = f. -/
lemma mul_idem_eq_self_of_ker {e f : Module.End R M} (he : e * e = e)
    (hf : LinearMap.ker e ≤ LinearMap.ker f) : f * e = f := by
  ext m
  simp_all +decide [LinearMap.ext_iff]
  have := hf (show e (m - e m) = 0 from by simp +decide [he])
  simp_all +decide [sub_eq_zero]

end

section

variable {R : Type*} [Field R]
  {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]

set_option maxHeartbeats 1600000 in
/-- Any endomorphism factors as unit * idempotent. -/
lemma exists_unit_mul_idem (f : Module.End R M) :
    ∃ (u : (Module.End R M)ˣ) (e : Module.End R M),
      e * e = e ∧ f = ↑u * e :=
  Submission.CentralizerLeAdjoinTarget.exists_unit_mul_idem f

/-- For a non-trivial idempotent, there exists a unit whose inverse
composed with the idempotent is nilpotent. -/
lemma exists_unit_inv_mul_nilpotent (e : Module.End R M) (he : e * e = e)
    (hne0 : e ≠ 0) (hne1 : e ≠ 1) :
    ∃ u : (Module.End R M)ˣ, IsNilpotent (↑u⁻¹ * e) :=
  Submission.CentralizerLeAdjoinTarget.exists_unit_inv_mul_nilpotent e he hne0 hne1

end

end Submission.DiagMapTarget
