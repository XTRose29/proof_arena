import Submission.OddOrder.PF.Section01.MulCharacterTwist

/-!
# Induction of a restriction as a scalar-character twist sum

For a normal subgroup with abelian quotient, inducing the restriction of an
irreducible character is the sum of all its twists by scalar characters of
the quotient.  This is the Lean counterpart of the `cfReg` calculation in
the proof of Peterfalvi 1.7(b).
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative

universe u

namespace ClassFunction

variable {T k : Type u} [Group T] [Fintype T]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- Induction of a restricted irreducible character is the sum of its twists
by all scalar characters of an abelian quotient. -/
theorem induce_restrict_eq_sum_mulCharacterTwist
    (K : Subgroup T) [K.Normal] [IsMulCommutative (T ⧸ K)]
    (psi : IrreducibleCharacter T k) :
    induce K (restrict K (psi : ClassFunction T k)) =
      ∑ chi : MulChar (T ⧸ K) k,
        (IrreducibleCharacter.mulCharacterTwist
          (QuotientGroup.mk' K) chi psi : ClassFunction T k) := by
  ext t
  let eval : ClassFunction T k →ₗ[k] k :=
    { toFun := fun f ↦ f t
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  rw [show
    (∑ chi : MulChar (T ⧸ K) k,
      (IrreducibleCharacter.mulCharacterTwist
        (QuotientGroup.mk' K) chi psi : ClassFunction T k)) t =
      ∑ chi : MulChar (T ⧸ K) k,
        IrreducibleCharacter.mulCharacterTwist
          (QuotientGroup.mk' K) chi psi t by
      change eval
        (∑ chi : MulChar (T ⧸ K) k,
          (IrreducibleCharacter.mulCharacterTwist
            (QuotientGroup.mk' K) chi psi : ClassFunction T k)) = _
      exact map_sum eval _ Finset.univ]
  rw [induce_apply_formula]
  simp_rw [IrreducibleCharacter.mulCharacterTwist_apply]
  rw [← Finset.sum_mul]
  rw [sum_mulChar_apply]
  by_cases ht : t ∈ K
  · have hqt : QuotientGroup.mk' K t = 1 :=
      (QuotientGroup.eq_one_iff t).mpr ht
    rw [if_pos hqt]
    have hmem (x : T) : x⁻¹ * t * x ∈ K := by
      simpa using (inferInstance : K.Normal).conj_mem t ht x⁻¹
    simp_rw [dif_pos (hmem _)]
    have hconj (x : T) :
        restrict K (psi : ClassFunction T k) ⟨x⁻¹ * t * x, hmem x⟩ =
          psi t := by
      change psi (x⁻¹ * t * x) = psi t
      simpa using ClassFunction.conj_apply
        (psi : ClassFunction T k) x⁻¹ t
    simp_rw [hconj]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_eq_nat_card,
      K.card_eq_card_quotient_mul_card_subgroup, Nat.cast_mul]
    have hK : (Nat.card K : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp [hK]
  · have hqt : QuotientGroup.mk' K t ≠ 1 :=
      (QuotientGroup.eq_one_iff t).not.mpr ht
    rw [if_neg hqt, zero_mul]
    have hmem (x : T) : x⁻¹ * t * x ∉ K := by
      intro hx
      apply ht
      have := (inferInstance : K.Normal).conj_mem
        (x⁻¹ * t * x) hx x
      simpa [mul_assoc] using this
    simp_rw [dif_neg (hmem _)]
    simp

end ClassFunction

end

end Submission.OddOrder.PF
