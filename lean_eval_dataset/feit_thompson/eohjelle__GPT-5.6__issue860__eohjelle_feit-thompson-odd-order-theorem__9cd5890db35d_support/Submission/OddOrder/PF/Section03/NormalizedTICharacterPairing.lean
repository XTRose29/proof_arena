import Submission.OddOrder.PF.Section02.NormalizedTIDade

/-!
# Ordinary character pairing for normalized TI induction

For class functions supported on an inverse-stable normalized TI set,
ordinary induction preserves the inverse-argument character pairing.  This is
the version of normalized-TI isometry needed in Peterfalvi Section 3; unlike
the coefficient-star version, it requires no star operation on the coefficient
field.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped Classical

universe u v

/-- Ordinary class-function induction from the relative normalizer of an
inverse-stable normalized TI set preserves the character pairing. -/
theorem normedTI_induce_characterPairing
    {Γ : Type u} [Group Γ] [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (hTI : IsNormalizedTI A G L)
    (hAG1 : A ⊆ (G : Set Γ) \ {(1 : Γ)})
    (hAinv : IsInvStable A)
    (alpha beta : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A})
    (hbeta : beta ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A}) :
    let ddA := normedTI_Dade hTI hAG1
    characterPairing
        (ClassFunction.induce (L.subgroupOf G)
          (ClassFunction.toSubgroupOf L G ddA.2.1 alpha))
        (ClassFunction.induce (L.subgroupOf G)
          (ClassFunction.toSubgroupOf L G ddA.2.1 beta)) =
      characterPairing alpha beta := by
  dsimp only
  let ddA := normedTI_Dade hTI hAG1
  let H : Subgroup G := L.subgroupOf G
  let e : H ≃* L := Subgroup.subgroupOfEquivOfLe ddA.2.1
  let alphaH : ClassFunction H k :=
    ClassFunction.toSubgroupOf L G ddA.2.1 alpha
  let betaH : ClassFunction H k :=
    ClassFunction.toSubgroupOf L G ddA.2.1 beta
  rw [ClassFunction.frobeniusReciprocity]
  have hcard : Nat.card H = Nat.card L := Nat.card_congr e.toEquiv
  have hsum :
      (∑ x : H,
          alphaH x *
            ClassFunction.restrict H (ClassFunction.induce H betaH) x⁻¹) =
        ∑ a : L, alpha a * beta a⁻¹ := by
    apply Fintype.sum_equiv e.toEquiv
    intro x
    by_cases hxA : ((e x : L) : Γ) ∈ A
    · have hxinvA : (((e x)⁻¹ : L) : Γ) ∈ A := by
        simpa only [Subgroup.coe_inv] using (hAinv ((e x : L) : Γ)).2 hxA
      have hind := normedTI_Ind_id hTI hAG1 beta hbeta (e x)⁻¹ hxinvA
      change
        alphaH x * ClassFunction.induce H betaH (x⁻¹ : H) =
          alpha (e x) * beta (e x)⁻¹
      rw [show alphaH x = alpha (e x) by rfl]
      exact congrArg (alpha (e x) * ·) hind
    · have halpha0 : alpha (e x) = 0 :=
        ClassFunction.eq_zero_of_mem_supportedOn halpha hxA
      change
        alphaH x * ClassFunction.induce H betaH (x⁻¹ : H) =
          alpha (e x) * beta (e x)⁻¹
      simp only [show alphaH x = alpha (e x) by rfl, halpha0, zero_mul]
  unfold characterPairing
  rw [hcard, hsum]

end

end Submission.OddOrder.PF
