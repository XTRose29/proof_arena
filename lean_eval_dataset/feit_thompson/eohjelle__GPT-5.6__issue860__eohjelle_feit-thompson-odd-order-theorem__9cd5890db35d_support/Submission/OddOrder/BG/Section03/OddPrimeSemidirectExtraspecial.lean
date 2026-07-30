import Submission.OddOrder.BG.Section03.OddPrimeSemidirectSpecialKernel
import Submission.OddOrder.MathlibSupport.ExtraspecialCyclicFixedVectorNonmodular

/-!
Discharge of the extraspecial branch in Bender-Glauberman Theorem 3.4.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V] [Finite V]

noncomputable section

/-- The extraspecial fixed-vector theorem closes the final faithful branch
of the Section 3 semidirect-product argument. -/
theorem kernel_commutator_le_representation_ker_of_extraspecial_theorem
    [IsSolvable G]
    (rho : Representation k G V)
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : Representation.invariants
      (rho.comp R.subtype : Representation k R V) = ⊥)
    (ih : OddPrimeSemidirectGlobalInductionHypothesis.{u, v, w}
      k (Nat.card G)) :
    ⁅R, K⁆ ≤ rho.ker := by
  apply kernel_commutator_le_representation_ker_of_extraspecial_cases
    rho hKR hnormK hcop hodd hRprime hGcard hfix ih
  intro q hq hKq _hperfect _hKne W _ _ _ sigma _ hsigma hfixsigma
    _hKnonabelian hmapCenter _hcyclicCenter hKextra hcentralizer
  exact (extraspecial_prime_action_invariants_ne_bot_of_card_ne_zero
    hq hKq hKextra hRprime hKR hnormK hcop hodd hGcard hmapCenter
      hcentralizer sigma hsigma) hfixsigma

end

end Submission.OddOrder.BG.Section03
