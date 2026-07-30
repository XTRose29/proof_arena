import Submission.OddOrder.BG.Section04.RankTwoPrimeCutoffCoreHall
import Submission.OddOrder.MathlibSupport.PCore

/-!
Bender--Glauberman Theorem 4.20(c), for the first factor.

At a maximal prime divisor `p`, the cutoff core supported on primes at least
`p` is a `p`-group.  Its universal property identifies it with the normal
`p`-core, and the Hall index condition is therefore the Sylow condition.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

/-- `BGsection4.v: rank2_max_pcore_Sylow` (Bender--Glauberman
Theorem 4.20(c), first factor). -/
theorem rank2_max_pcore_Sylow
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hpmax : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card G → q ≤ p)
    (hodd : Odd (Nat.card G)) (hsol : IsSolvable G)
    (hRank : ∀ q : ℕ, q.Prime →
      ¬ ∃ E : Subgroup (fittingCore G),
        IsElementaryAbelianOfRank q 3 E) :
    ¬ p ∣ (pCore p G).index := by
  classical
  let pi : Set ℕ := {q : ℕ | p ≤ q}
  let K : Subgroup G := piCore pi G
  have hHallK : IsHall pi K := by
    simpa [pi, K] using rank2_ge_pcore_Hall p hodd hsol hRank

  let S : Sylow p K := Classical.choice Sylow.nonempty
  have hSindexOne : S.index = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hq hqIndex
    have hqK : q ∣ Nat.card K := hqIndex.trans S.index_dvd_card
    have hpq : p ≤ q := hHallK.isPiNumber_card hq hqK
    have hqG : q ∣ Nat.card G :=
      hqK.trans K.card_subgroup_dvd_card
    have hqp : q = p := le_antisymm (hpmax hq hqG) hpq
    subst q
    exact S.not_dvd_index hqIndex
  have hStop : (S : Subgroup K) = ⊤ :=
    Subgroup.index_eq_one.mp hSindexOne
  have hKp : IsPGroup p K :=
    S.isPGroup'.of_equiv
      ((MulEquiv.subgroupCongr hStop).trans Subgroup.topEquiv)

  have hKle : K ≤ pCore p G :=
    le_pCore hKp (by dsimp [K]; infer_instance)
  have hpPi : p ∈ pi := by
    change p ≤ p
    exact le_rfl
  have hPle : pCore p G ≤ K := by
    dsimp [K]
    apply le_piCore (by infer_instance)
    exact IsPGroup.isPiNumber_natCard
      (pCore_isPGroup (p := p) (G := G)) hpPi
  have hcoreEq : K = pCore p G := le_antisymm hKle hPle

  intro hpIndex
  have hpIndex' : p ∣ K.index := by
    simpa [hcoreEq] using hpIndex
  have hpNotPi : p ∈ piᶜ :=
    hHallK.isPiNumber_index (Fact.out : p.Prime) hpIndex'
  exact hpNotPi hpPi

end

end Submission.OddOrder.BG.Section04
