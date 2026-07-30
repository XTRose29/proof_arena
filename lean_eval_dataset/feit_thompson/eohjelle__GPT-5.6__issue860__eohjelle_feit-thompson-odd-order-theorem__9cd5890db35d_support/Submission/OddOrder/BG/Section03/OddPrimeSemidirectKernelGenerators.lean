import Submission.OddOrder.BG.Section03.OddPrimeSemidirectProperKernel
import Submission.OddOrder.MathlibSupport.CommutatorSup

/-!
The invariant Hall-pair reduction in Bender-Glauberman Theorem 3.4.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R Q Q' : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

/-- The data used from a pair of complementary Hall subgroups of the normal
factor: they are proper, complementarily generate the factor, and are stable
under the acting subgroup. -/
structure InvariantKernelGeneratingPair (K R : Subgroup G) where
  left : Subgroup G
  right : Subgroup G
  left_lt : left < K
  right_lt : right < K
  le_sup : K ≤ left ⊔ right
  left_normalized : R ≤ Subgroup.normalizer (left : Set G)
  right_normalized : R ≤ Subgroup.normalizer (right : Set G)

/-- Once an invariant proper pair generates the kernel, strong induction on
the two smaller semidirect products proves the full mixed commutator bound. -/
theorem kernel_commutator_le_representation_ker_of_generatingPair
    [IsSolvable G]
    (rho : _root_.Representation k G V)
    (hKR : K.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : _root_.Representation.invariants
      (rho.comp R.subtype : _root_.Representation k R V) = ⊥)
    (ih : OddPrimeSemidirectInductionHypothesis rho)
    (pair : InvariantKernelGeneratingPair K R) :
    ⁅R, K⁆ ≤ rho.ker := by
  have hleft : ⁅R, pair.left⁆ ≤ rho.ker :=
    properKernel_commutator_le_representation_ker rho hKR hcop hodd
      hRprime hGcard hfix ih pair.left_lt pair.left_normalized
  have hright : ⁅R, pair.right⁆ ≤ rho.ker :=
    properKernel_commutator_le_representation_ker rho hKR hcop hodd
      hRprime hGcard hfix ih pair.right_lt pair.right_normalized
  exact commutator_le_of_le_sup_of_normal pair.le_sup hleft hright

end

end Submission.OddOrder.BG.Section03
