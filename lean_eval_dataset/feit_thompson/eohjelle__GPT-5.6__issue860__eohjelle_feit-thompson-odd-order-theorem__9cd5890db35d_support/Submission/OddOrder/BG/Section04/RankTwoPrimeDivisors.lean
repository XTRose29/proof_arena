import Submission.OddOrder.BG.Section04.RankTwoPGroupAutomorphismPrimes
import Submission.OddOrder.MathlibSupport.FittingPCore
import Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient
import Submission.OddOrder.MathlibSupport.PPrimeQuotientElementaryAbelian

/-!
Bender--Glauberman Theorem 4.18(a).

After quotienting by the `p'`-core, the Fitting subgroup is the `p`-core
and contains its centralizer.  Conjugation therefore accounts for every
non-`p` prime divisor through the automorphism group of that `p`-core, where
the rank-two automorphism bound applies.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

/-- `BGsection4.v: rank2_max_pdiv` (Bender--Glauberman Theorem 4.18(a)). -/
theorem rank2_max_pdiv
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime]
    (hsol : IsSolvable G)
    (hodd : Odd (Nat.card G))
    (hRank : ¬ ∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 3 E)
    (hq : q.Prime)
    (hqdvd : q ∣ Nat.card (G ⧸ pPrimeCore p G)) :
    q ≤ p := by
  classical
  let N : Subgroup G := pPrimeCore p G
  let Q := G ⧸ N
  letI : IsSolvable G := hsol
  letI : IsSolvable Q := isSolvable_quotient_of_isSolvable N
  have hQodd : Odd (Nat.card Q) := by
    exact odd_natCard_quotient N hodd
  have hQrank :
      ¬ ∃ E : Subgroup Q, IsElementaryAbelianOfRank p 3 E := by
    simpa [Q, N] using
      (no_elementaryAbelian_rank_three_quotient_pPrimeCore
        (G := G) (p := p) hsol hRank)
  let R : Subgroup Q := pCore p Q
  have hRp : IsPGroup p R := pCore_isPGroup
  have hRodd : Odd (Nat.card R) := odd_natCard_subgroup R hQodd
  have hRrank :
      ¬ ∃ E : Subgroup R, IsElementaryAbelianOfRank p 3 E := by
    rintro ⟨E, hE⟩
    apply hQrank
    exact ⟨E.map R.subtype,
      hE.map_of_injective R.subtype R.subtype_injective⟩
  by_cases hqp : q = p
  · exact Nat.le_of_eq hqp
  have hqp' : q ≠ p := hqp
  let C : Subgroup Q := Subgroup.centralizer (R : Set Q)
  have hCp : IsPGroup p C := by
    dsimp [C, R]
    apply centralizer_pCore_isPGroup_of_pPrimeCore_eq_bot
    simpa [Q, N] using
      (pPrimeCore_quotient_self_eq_bot (G := G) (p := p))
  obtain ⟨n, hCcard⟩ := hCp.exists_card_eq
  have hqCcop : (Nat.card C).Coprime q := by
    rw [hCcard]
    exact ((Nat.coprime_primes (Fact.out : p.Prime) hq).mpr
      (Ne.symm hqp')).pow_left n
  have hqC : ¬ q ∣ Nat.card C := by
    exact hq.coprime_iff_not_dvd.mp hqCcop.symm
  have hqdvdQ : q ∣ Nat.card Q := by
    simpa [Q, N] using hqdvd
  have hqindex : q ∣ C.index := by
    rw [← C.card_mul_index] at hqdvdQ
    exact (hq.dvd_mul.mp hqdvdQ).resolve_left hqC
  let i : Q →* Subgroup.normalizer (R : Set Q) :=
    { toFun := fun x ↦ ⟨x, by
        rw [R.normalizer_eq_top]
        trivial⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  let rho : Q →* MulAut R := R.normalizerMonoidHom.comp i
  have hrhoker : rho.ker = C := by
    ext x
    change i x ∈ R.normalizerMonoidHom.ker ↔
      x ∈ Subgroup.centralizer (R : Set Q)
    rw [Subgroup.normalizerMonoidHom_ker]
    rfl
  have hqrange : q ∣ Nat.card rho.range := by
    rw [← Subgroup.index_ker rho, hrhoker]
    exact hqindex
  have hqAut : q ∣ Nat.card (MulAut R) :=
    hqrange.trans rho.range.card_subgroup_dvd_card
  exact (prime_dvd_mulAut_of_odd_pgroup_no_rank_three
    hRp hRodd hRrank hq hqAut hqp').2.1.le

end

end Submission.OddOrder.BG.Section04
