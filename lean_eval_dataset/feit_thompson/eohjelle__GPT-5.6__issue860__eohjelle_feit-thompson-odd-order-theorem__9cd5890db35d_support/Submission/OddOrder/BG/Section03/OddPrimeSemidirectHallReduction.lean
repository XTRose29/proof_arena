import Submission.OddOrder.BG.Section03.OddPrimeSemidirectKernelGenerators
import Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow

/-!
The Sylow half of the Hall reduction in Bender-Glauberman Theorem 3.4.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R Q' : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

/-- Once a normalized proper `q'`-Hall partner is available, the prime-order
fixed-point theorem supplies the normalized Sylow `q`-subgroup and the
proper-kernel induction closes the whole mixed commutator. -/
theorem kernel_commutator_le_representation_ker_of_hallPartner
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
    {q : ℕ} (hq : q.Prime) (hKq : ¬IsPGroup q K)
    (hQ'lt : Q' < K)
    (hQ'norm : R ≤ Subgroup.normalizer (Q' : Set G))
    (hgenerate : ∀ Q : Subgroup G,
      Q < K → IsSylowSubgroupOf q Q K →
      R ≤ Subgroup.normalizer (Q : Set G) → K ≤ Q ⊔ Q') :
    ⁅R, K⁆ ≤ rho.ker := by
  obtain ⟨Q, hQlt, hQsylow, hQnorm⟩ :=
    exists_proper_isPGroup_normalized_by_prime_subgroup hq hnormK
      hRprime hcop.symm hKq
  let pair : InvariantKernelGeneratingPair K R :=
    { left := Q
      right := Q'
      left_lt := hQlt
      right_lt := hQ'lt
      le_sup := hgenerate Q hQlt hQsylow hQnorm
      left_normalized := hQnorm
      right_normalized := hQ'norm }
  exact kernel_commutator_le_representation_ker_of_generatingPair rho hKR
    hcop hodd hRprime hGcard hfix ih pair

end

end Submission.OddOrder.BG.Section03
