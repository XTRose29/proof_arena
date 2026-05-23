import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Idempotent shift lemma

For an idempotent e and a scalar j with j ≠ 0 and 1+j ≠ 0,
the shift e + j • id is a unit with explicit inverse.
-/

variable {R : Type*} [Field R]
  {M : Type*} [AddCommGroup M] [Module R M]

namespace Submission.IdempotentShift

/-
For an idempotent e and scalars j with j ≠ 0 and 1+j ≠ 0,
    the map e + j • id is a unit. The explicit inverse is
    (1+j)⁻¹ • e + j⁻¹ • (id - e).
-/
lemma isUnit_idempotent_add_smul_id (e : Module.End R M)
    (he : e * e = e) (c : R) (hc : c ≠ 0) (hc1 : 1 + c ≠ 0) :
    IsUnit (e + c • (1 : Module.End R M)) := by
  refine' ⟨ ⟨ e + c • 1, ( 1 + c ) ⁻¹ • e + c⁻¹ • ( 1 - e ), _, _ ⟩, rfl ⟩ <;> simp_all +decide [ add_mul, mul_add, mul_assoc ];
  · simp_all +decide [ mul_sub, sub_mul ];
    simp +decide [ ← add_smul, ← smul_assoc, hc1 ];
    rw [ show ( 1 + c ) ⁻¹ + ( 1 + c ) ⁻¹ * c = 1 by linear_combination' inv_mul_cancel₀ hc1 ] ; simp +decide [ add_smul, sub_smul ];
  · simp_all +decide [ add_smul, smul_smul, sub_mul, mul_sub ];
    rw [ ← add_assoc, ← add_smul ];
    rw [ show ( 1 + c ) ⁻¹ + c * ( 1 + c ) ⁻¹ = 1 by linear_combination' mul_inv_cancel₀ hc1 ] ; aesop

end Submission.IdempotentShift
