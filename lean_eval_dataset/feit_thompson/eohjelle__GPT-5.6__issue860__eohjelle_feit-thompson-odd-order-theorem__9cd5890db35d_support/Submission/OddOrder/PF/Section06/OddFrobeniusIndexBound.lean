import Mathlib.Tactic
import Submission.OddOrder.BG.Section03.FrobeniusBasic
import Submission.OddOrder.MathlibSupport.Cardinality

/-!
# The odd-order Frobenius index bound

This dependency-lowered module contains the numerical orbit-counting
estimate used in Peterfalvi Sections 6, 7, and 14.  It depends only on the
Section 3 Frobenius decomposition API and Mathlib arithmetic.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.MathlibSupport

universe u

/-- A numerical fact used in Peterfalvi Sections 6, 7, and 14. -/
theorem odd_Frobenius_index_ler
    {Q : Type u} [Group Q] [Fintype Q]
    (K R : Subgroup Q)
    (hoddQ : Odd (Nat.card Q))
    (hfrob : IsFrobeniusDecomposition K R) :
    (K.index : ℝ) ≤ ((Nat.card K : ℝ) - 1) / 2 := by
  letI : MulDistribMulAction R K := hfrob.conjugationAction
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := R) (X := K))
  have hcard : Nat.card K = 1 + t * Nat.card R := by
    simpa only [t] using hfrob.kernel_card_eq_one_add_orbits_mul_card
  have hoddK : Odd (Nat.card K) := odd_natCard_subgroup K hoddQ
  have hoddR : Odd (Nat.card R) := odd_natCard_subgroup R hoddQ
  have htNe : t ≠ 0 := by
    intro ht
    have hKcard : Nat.card K = 1 := by simpa [ht] using hcard
    exact hfrob.kernel_ne_bot
      (Subgroup.eq_bot_of_card_eq K hKcard)
  have hprodEven : Even (t * Nat.card R) := by
    rcases hoddK with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    omega
  have htEven : Even t := by
    rcases Nat.even_mul.mp hprodEven with ht | hR
    · exact ht
    · exact (Nat.not_even_iff_odd.mpr hoddR hR).elim
  have htTwo : 2 ≤ t := by
    rcases htEven with ⟨m, hm⟩
    have hmPos : 0 < m := by
      by_contra hm0
      have : m = 0 := Nat.eq_zero_of_not_pos hm0
      apply htNe
      omega
    omega
  have hindex : K.index = Nat.card R :=
    hfrob.isComplement.symm.index_eq_card
  have hcardReal :
      (Nat.card K : ℝ) = 1 + (t : ℝ) * (Nat.card R : ℝ) := by
    exact_mod_cast hcard
  have htTwoReal : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast htTwo
  have hRnonneg : (0 : ℝ) ≤ (Nat.card R : ℝ) := by positivity
  rw [hindex, hcardReal]
  have hmul := mul_le_mul_of_nonneg_right htTwoReal hRnonneg
  nlinarith

end

end Submission.OddOrder.PF
