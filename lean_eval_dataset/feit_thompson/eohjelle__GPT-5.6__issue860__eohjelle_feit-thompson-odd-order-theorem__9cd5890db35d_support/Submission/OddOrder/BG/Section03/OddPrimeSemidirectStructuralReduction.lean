import Submission.OddOrder.BG.Section03.OddPrimeSemidirectPerfectKernelReduction

/-!
Combined Hall and commutator reductions for Bender-Glauberman Theorem 3.4.
-/

namespace Submission.OddOrder.BG.Section03

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

/-- The Hall and proper-kernel branches reduce Theorem 3.4 to a prime-power
kernel on which the coprime complement acts with `[R,K] = K`. -/
theorem kernel_commutator_le_representation_ker_of_pGroup_perfect_cases
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
    (perfectPGroupCase : ∀ q : ℕ, q.Prime → IsPGroup q K →
      ⁅R, K⁆ = K → ⁅R, K⁆ ≤ rho.ker) :
    ⁅R, K⁆ ≤ rho.ker := by
  apply kernel_commutator_le_representation_ker_of_pGroupCases rho hKR
    hnormK hcop hodd hRprime hGcard hfix ih
  intro q hq hKq
  exact kernel_commutator_le_representation_ker_of_commutator_eq_self_case
    rho hKR hnormK hcop hodd hRprime hGcard hfix ih hKq
      (perfectPGroupCase q hq hKq)

end

end Submission.OddOrder.BG.Section03
