import Submission.OddOrder.BG.Section04.RankTwoExponentPrime
import Submission.OddOrder.MathlibSupport.FrattiniPGroup
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
A Frattini-quotient bound for the exponent-`p` critical subgroup in
Bender--Glauberman Theorem 4.17.

The exponent hypothesis matters: an arbitrary odd `p`-group of
elementary-abelian rank at most two can have a three-dimensional Frattini
quotient.  The critical subgroup used in Theorem 4.17 has exponent `p`, and
that is exactly the additional input used below.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

private theorem natCard_le_prime_sq_of_commutative_exponent_prime
    {P : Type u} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P)
    (hcomm : IsMulCommutative P)
    (hexponent : Monoid.exponent P = p)
    (hRank : ¬ ∃ E : Subgroup P,
      IsElementaryAbelianOfRank p 3 E) :
    Nat.card P ≤ p ^ 2 := by
  classical
  letI : IsMulCommutative P := hcomm
  have hpow : ∀ x : P, x ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [hexponent])
  obtain ⟨n, hcard⟩ := hP.exists_card_eq
  have hn : n ≤ 2 := by
    by_contra hnle
    have hthree : 3 ≤ n := by omega
    have htopcard : Nat.card (⊤ : Subgroup P) = p ^ n := by
      simpa using hcard
    obtain ⟨E, _hEtop, _hEnormal, hEcard⟩ :=
      exists_normal_subgroup_card_pow_le hP (⊤ : Subgroup P)
        htopcard hthree
    apply hRank
    refine ⟨E,
      { isPGroup := hP.to_subgroup E
        commutative := inferInstance
        pow_eq_one := ?_
        card_eq := hEcard }⟩
    intro x
    apply Subtype.ext
    exact hpow x
  rw [hcard]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn

/-- The Frattini quotient of the exponent-`p` critical subgroup occurring in
`BGsection4.v: der1_Aut_rank2_pgroup` has cardinality at most `p ^ 2`.

In the commutative branch the group itself is elementary abelian and has
cardinality at most `p ^ 2`.  In the noncommutative branch its nontrivial
commutator lies in the Frattini subgroup, while Proposition 4.8(a) bounds the
group cardinality by `p ^ 3`; the strict quotient drop then gives the result. -/
theorem natCard_quotient_frattini_le_prime_sq_of_exponent_prime_of_no_rank_three
    {P : Type u} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P)
    (hexponent : Monoid.exponent P = p)
    (hRank : ¬ ∃ E : Subgroup P,
      IsElementaryAbelianOfRank p 3 E) :
    Nat.card (P ⧸ frattini P) ≤ p ^ 2 := by
  classical
  by_cases hcomm : IsMulCommutative P
  · have hPcard : Nat.card P ≤ p ^ 2 :=
      natCard_le_prime_sq_of_commutative_exponent_prime
        hP hcomm hexponent hRank
    exact (Nat.le_of_dvd (Nat.card_pos (α := P))
      (frattini P).card_quotient_dvd_card).trans hPcard
  · have hfrattiniNe : frattini P ≠ ⊥ := by
      intro hbot
      have hderived : _root_.commutator P = ⊥ := by
        apply le_bot_iff.mp
        rw [← hbot]
        exact IsPGroup.commutator_le_frattini hP
      exact hcomm ((_root_.commutator_eq_bot_iff P).mp hderived)
    have hcardP : Nat.card P ≤ p ^ 3 :=
      _root_.Submission.OddOrder.BG.Section04.natCard_le_prime_cube_of_exponent_prime_of_no_elementaryAbelian_rank_three
        hP hRank (by rw [hexponent])
    have hcardQlt : Nat.card (P ⧸ frattini P) < p ^ 3 :=
      (natCard_quotient_lt_of_ne_bot (frattini P) hfrattiniNe).trans_le
        hcardP
    have hQp : IsPGroup p (P ⧸ frattini P) :=
      hP.to_quotient (frattini P)
    obtain ⟨n, hcardQ⟩ := hQp.exists_card_eq
    have hn : n ≤ 2 := by
      have hnlt : n < 3 := by
        apply (Nat.pow_lt_pow_iff_right
          (Fact.out : p.Prime).one_lt).mp
        simpa only [hcardQ] using hcardQlt
      omega
    rw [hcardQ]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn

end Submission.OddOrder.MathlibSupport
