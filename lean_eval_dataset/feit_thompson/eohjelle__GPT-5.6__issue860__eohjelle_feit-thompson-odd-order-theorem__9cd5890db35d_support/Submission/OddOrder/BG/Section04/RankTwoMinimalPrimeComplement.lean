import Submission.OddOrder.BG.Section04.RankTwoPrimeDivisors
import Submission.OddOrder.MathlibSupport.PrimeComplement

/-!
Bender--Glauberman Theorem 4.18(b).

If `p` is the least prime divisor of the order of an odd solvable group with
no elementary abelian `p`-subgroup of rank three, then the `p'`-core is a
Hall `p'`-subgroup.  Theorem 4.18(a) bounds every prime divisor of the
quotient by `p`; minimality gives the reverse bound.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

/-- `BGsection4.v: rank2_min_p_complement` (Bender--Glauberman
Theorem 4.18(b)). -/
theorem rank2_min_p_complement
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hpmin : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card G → p ≤ q)
    (hsol : IsSolvable G)
    (hodd : Odd (Nat.card G))
    (hRank : ¬ ∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 3 E) :
    IsPrimeComplement p (pPrimeCore p G) := by
  refine ⟨(pPrimeCore_coprime_card (G := G) (p := p)).symm, ?_⟩
  let N : Subgroup G := pPrimeCore p G
  have hquotient :
      Nat.card (G ⧸ N) = p ^ (Nat.card (G ⧸ N)).primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro q hq hqdvd
    apply Nat.le_antisymm
    · exact rank2_max_pdiv hsol hodd hRank hq (by simpa [N] using hqdvd)
    · apply hpmin hq
      exact hqdvd.trans N.card_quotient_dvd_card
  refine ⟨(Nat.card (G ⧸ N)).primeFactorsList.length, ?_⟩
  rw [N.index_eq_card]
  exact hquotient

end

end Submission.OddOrder.BG.Section04
