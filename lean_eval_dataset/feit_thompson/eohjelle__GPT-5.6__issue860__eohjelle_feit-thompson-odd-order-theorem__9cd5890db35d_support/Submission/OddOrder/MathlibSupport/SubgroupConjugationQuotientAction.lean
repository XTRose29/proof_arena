import Submission.OddOrder.MathlibSupport.CharacteristicQuotientAction

/-!
Conjugation actions of normalizing subgroups on subgroup center quotients.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {A : Type u} [Group A]

/-- A subgroup of the normalizer of `P` acts on `P` by ambient conjugation. -/
abbrev subgroupConjugationAction (P H : Subgroup A)
    (hHP : H ≤ Subgroup.normalizer P) : MulDistribMulAction H P :=
  MulDistribMulAction.compHom P
    (P.normalizerMonoidHom.comp (Subgroup.inclusion hHP))

/-- The subgroup conjugation action is ordinary conjugation after coercion to
the ambient group. -/
theorem coe_subgroupConjugationAction_smul
    (P H : Subgroup A) (hHP : H ≤ Subgroup.normalizer P)
    (h : H) (p : P) :
    letI := subgroupConjugationAction P H hHP
    ((h • p : P) : A) = (h : A) * (p : A) * (h : A)⁻¹ := by
  rfl

/-- The conjugation action of a normalizing subgroup descends to `P / Z(P)`. -/
theorem subgroupConjugationCenterQuotientAction
    (P H : Subgroup A) (hHP : H ≤ Subgroup.normalizer P) :
    letI := subgroupConjugationAction P H hHP
    MulAction.QuotientAction H (Subgroup.center P) := by
  letI := subgroupConjugationAction P H hHP
  exact centerQuotientAction

end Submission.OddOrder.MathlibSupport
