import Submission.OddOrder.BG.Section04.RankTwoMinimalPrimeCoreHall
import Submission.OddOrder.MathlibSupport.FittingRankRestriction
import Submission.OddOrder.MathlibSupport.PiCore
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Bender--Glauberman Theorem 4.20(c), for intermediate factors.

For a cutoff `m`, the normal core supported on primes at least `m` is a
Hall subgroup.  The proof follows the Coq cardinality induction, removing
the least prime divisor through its normal Hall complement at each step.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

/-- `BGsection4.v: rank2_ge_pcore_Hall` (Bender--Glauberman
Theorem 4.20(c), intermediate factors). -/
theorem rank2_ge_pcore_Hall
    {G : Type u} [Group G] [Finite G]
    (m : ℕ) (hodd : Odd (Nat.card G)) (hsol : IsSolvable G)
    (hRank : ∀ q : ℕ, q.Prime →
      ¬ ∃ E : Subgroup (fittingCore G),
        IsElementaryAbelianOfRank q 3 E) :
    IsHall {q : ℕ | m ≤ q} (piCore {q : ℕ | m ≤ q} G) := by
  classical
  let pi : Set ℕ := {q : ℕ | m ≤ q}
  let motive : ℕ → Prop := fun n ↦
    ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K = n →
      Odd (Nat.card K) → IsSolvable K →
      (∀ q : ℕ, q.Prime →
        ¬ ∃ E : Subgroup (fittingCore K),
          IsElementaryAbelianOfRank q 3 E) →
      IsHall pi (piCore pi K)
  suffices hmain : motive (Nat.card G) from by
    simpa [pi] using hmain rfl hodd hsol hRank
  exact Nat.strong_induction_on (p := motive) (Nat.card G) fun n ih ↦ by
    intro K _ _ hcard hoddK hsolK hRankK
    letI : IsSolvable K := hsolK
    by_cases hcore : piCore pi K = ⊤
    · constructor
      · simpa [hcore] using piCore_isPiNumber (G := K) pi
      · rw [hcore]
        simpa using (IsPiNumber.one (pi := piᶜ))

    have hcardNeOne : Nat.card K ≠ 1 := by
      intro hcardOne
      apply hcore
      apply piCore_eq_top_of_isPiNumber
      rw [hcardOne]
      exact IsPiNumber.one

    let p : ℕ := Nat.minFac (Nat.card K)
    have hp : p.Prime := Nat.minFac_prime hcardNeOne
    letI : Fact p.Prime := ⟨hp⟩
    have hpK : p ∣ Nat.card K := Nat.minFac_dvd (Nat.card K)
    have hpmin : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card K → p ≤ q := by
      intro q hq hqK
      exact Nat.minFac_le_of_dvd hq.two_le hqK

    have hpNotPi : p ∉ pi := by
      intro hpPi
      apply hcore
      apply piCore_eq_top_of_isPiNumber
      intro q hq hqK
      change m ≤ q
      exact (show m ≤ p from hpPi).trans (hpmin hq hqK)

    let H : Subgroup K := pPrimeCore p K
    letI : H.Normal := by
      dsimp [H]
      infer_instance
    have hHallH : IsPrimeComplement p H := by
      dsimp [H]
      exact rank2_min_pPrimeCore_Hall hpmin hoddK hsolK hRankK
    have hHneTop : H ≠ ⊤ :=
      hHallH.ne_top_of_dvd_card hp hpK
    have hHcardLt : Nat.card H < Nat.card K :=
      natCard_subgroup_lt_of_ne_top H hHneTop
    have hHcardLtN : Nat.card H < n := by
      simpa [hcard] using hHcardLt

    have hRankH : ∀ q : ℕ, q.Prime →
        ¬ ∃ E : Subgroup (fittingCore H),
          IsElementaryAbelianOfRank q 3 E := by
      intro q hq
      exact no_elementaryAbelian_rank_three_fittingCore_of_normal
        (hRankK q hq)
    have hHallCoreH : IsHall pi (piCore pi H) :=
      ih (Nat.card H) hHcardLtN (K := H) rfl
        (odd_natCard_subgroup H hoddK) (by infer_instance) hRankH

    have hmapCore : (piCore pi H).map H.subtype = piCore pi K := by
      dsimp [H]
      exact map_piCore_pPrimeCore_eq_of_isPrimeComplement hpNotPi hHallH
    obtain ⟨a, ha⟩ := hHallH.exists_index_eq_pow
    have hpComp : IsPiNumber piᶜ p := by
      intro q hq hqp
      have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      subst q
      exact hpNotPi
    have hHindexPi : IsPiNumber piᶜ H.index := by
      rw [ha]
      exact hpComp.pow a

    constructor
    · rw [← hmapCore,
        Subgroup.card_map_of_injective H.subtype_injective]
      exact hHallCoreH.isPiNumber_card
    · rw [← hmapCore, Subgroup.index_map_subtype]
      exact hHallCoreH.isPiNumber_index.mul hHindexPi

end

end Submission.OddOrder.BG.Section04
