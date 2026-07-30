import Submission.OddOrder.BG.Section03.OddPrimeSemidirectPGroupReduction
import Submission.OddOrder.MathlibSupport.CoprimePrimeOrderCommutator

/-!
Reduction of Bender-Glauberman Theorem 3.4 to a perfect coprime action on its
prime-power kernel.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

/-- Once the kernel is a `q`-group, proper-kernel induction and coprime
commutator idempotence reduce the representation theorem to the case
`[R,K] = K`. -/
theorem kernel_commutator_le_representation_ker_of_commutator_eq_self_case
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
    {q : ℕ} (_hKq : IsPGroup q K)
    (commutatorEqSelfCase : ⁅R, K⁆ = K → ⁅R, K⁆ ≤ rho.ker) :
    ⁅R, K⁆ ≤ rho.ker := by
  let H : Subgroup G := ⁅R, K⁆
  have hHK : H ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hnormK
  have hnormH : R ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.normalizer_commutator_ge_left R K
  by_cases hH : H = K
  · exact commutatorEqSelfCase hH
  have hHlt : H < K := lt_of_le_of_ne hHK hH
  have hlocal : ⁅R, H⁆ ≤ rho.ker :=
    properKernel_commutator_le_representation_ker rho hKR hcop hodd
      hRprime hGcard hfix ih hHlt hnormH
  rw [commutator_commutator_eq_of_prime_complement hKR hnormK hcop hRprime]
    at hlocal
  exact hlocal

end

end Submission.OddOrder.BG.Section03
