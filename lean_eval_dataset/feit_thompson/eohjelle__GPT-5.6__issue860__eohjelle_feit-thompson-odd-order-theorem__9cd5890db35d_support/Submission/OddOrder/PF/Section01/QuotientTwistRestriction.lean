import Submission.OddOrder.PF.Section01.InertiaConstituentRestriction

/-!
# Restriction of quotient-character twists

A scalar character pulled back from a quotient is trivial on the normal
subgroup, so twisting does not alter restriction to that subgroup.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical IsMulCommutative

universe u

namespace ClassFunction

variable {T k : Type u} [Group T] [Fintype T]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- Twisting by a scalar character of `T ⧸ K` does not change restriction
to `K`. -/
@[simp]
theorem restrict_mulCharacterTwist_quotient
    (K : Subgroup T) [K.Normal] [IsMulCommutative (T ⧸ K)]
    (chi : MulChar (T ⧸ K) k) (psi : IrreducibleCharacter T k) :
    restrict K
        (IrreducibleCharacter.mulCharacterTwist
          (QuotientGroup.mk' K) chi psi : ClassFunction T k) =
      restrict K (psi : ClassFunction T k) := by
  ext h
  rw [restrict_apply, restrict_apply,
    IrreducibleCharacter.mulCharacterTwist_apply]
  have hq : QuotientGroup.mk' K (h : T) = 1 :=
    (QuotientGroup.eq_one_iff (h : T)).mpr h.property
  rw [hq, map_one, one_mul]

end ClassFunction

end

end Submission.OddOrder.PF
