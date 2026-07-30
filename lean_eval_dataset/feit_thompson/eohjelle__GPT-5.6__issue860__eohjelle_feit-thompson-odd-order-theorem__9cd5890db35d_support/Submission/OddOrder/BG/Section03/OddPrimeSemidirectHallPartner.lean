import Submission.OddOrder.BG.Section03.OddPrimeSemidirectHallReduction
import Submission.OddOrder.MathlibSupport.PrimeComplementIntersection

/-!
The solvable Hall-subgroup branch of Bender-Glauberman Theorem 3.4.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

/-- If a prime dividing the kernel order does not make the whole kernel a
`q`-group, solvable Hall theory supplies the second proper normalized subgroup
needed by the proper-kernel induction. -/
theorem kernel_commutator_le_representation_ker_of_not_isPGroup
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
    {q : ℕ} (hq : q.Prime) (hqdvd : q ∣ Nat.card K)
    (hKq : ¬IsPGroup q K) :
    ⁅R, K⁆ ≤ rho.ker := by
  obtain ⟨Q', hQ'lt, _hQ'Hall, hQ'norm, hgenerate⟩ :=
    exists_normalized_primeComplement_intersection hKR hnormK hcop
      hRprime hq hqdvd
  exact kernel_commutator_le_representation_ker_of_hallPartner rho hKR
    hnormK hcop hodd hRprime hGcard hfix ih hq hKq hQ'lt hQ'norm
      (fun Q _hQlt hQsylow _hQnorm => hgenerate Q hQsylow)

end

end Submission.OddOrder.BG.Section03
