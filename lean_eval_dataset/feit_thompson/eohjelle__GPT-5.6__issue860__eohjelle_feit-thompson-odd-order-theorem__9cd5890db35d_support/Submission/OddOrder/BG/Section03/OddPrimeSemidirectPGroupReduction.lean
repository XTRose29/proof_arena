import Submission.OddOrder.BG.Section03.OddPrimeSemidirectHallPartner

/-!
Reduction of Bender-Glauberman Theorem 3.4 to its prime-power kernel case.
-/

namespace Submission.OddOrder.BG.Section03

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

/-- It is enough to prove the odd-prime semidirect representation theorem when
the kernel is a `q`-group. Every other case splits into two proper normalized
subgroups by solvable Hall theory. -/
theorem kernel_commutator_le_representation_ker_of_pGroupCases
    [IsSolvable G]
    (rho : _root_.Representation k G V)
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : _root_.Representation.invariants
      (rho.comp R.subtype : _root_.Representation k R V) = ⊥)
    (ih : OddPrimeSemidirectInductionHypothesis rho)
    (pGroupCase : ∀ q : ℕ, q.Prime → IsPGroup q K → ⁅R, K⁆ ≤ rho.ker) :
    ⁅R, K⁆ ≤ rho.ker := by
  by_cases hK : K = ⊥
  · subst K
    simpa only [Subgroup.commutator_bot_right] using
      (bot_le : (⊥ : Subgroup G) ≤ rho.ker)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt (K.one_lt_card_iff_ne_bot.mpr hK))
  by_cases hKq : IsPGroup q K
  · exact pGroupCase q hq hKq
  · exact kernel_commutator_le_representation_ker_of_not_isPGroup rho
      hKR hnormK hcop hodd hRprime hGcard hfix ih hq hqdvd hKq

end

end Submission.OddOrder.BG.Section03
