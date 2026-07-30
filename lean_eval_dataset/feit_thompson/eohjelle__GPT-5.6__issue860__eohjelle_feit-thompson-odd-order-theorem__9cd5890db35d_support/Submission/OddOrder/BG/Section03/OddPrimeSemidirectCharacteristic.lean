import Submission.OddOrder.BG.Section03.OddPrimeSemidirectPerfectKernelReduction
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer

/-!
Characteristic subgroups in the faithful prime-power kernel branch of
Bender-Glauberman Theorem 3.4.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

/-- Under a faithful representation, every proper characteristic subgroup of
the prime-power kernel centralizes the prime-order complement. -/
theorem properCharacteristic_map_le_centralizer
    [IsSolvable G]
    (rho : _root_.Representation k G V)
    (hrho : Function.Injective rho)
    (hKR : K.IsComplement' R)
    (hnormK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hodd : Odd (Nat.card G))
    (hRprime : (Nat.card R).Prime)
    (hGcard : (Nat.card G : k) ≠ 0)
    (hfix : _root_.Representation.invariants
      (rho.comp R.subtype : _root_.Representation k R V) = ⊥)
    (ih : OddPrimeSemidirectInductionHypothesis rho)
    (A : Subgroup K) [A.Characteristic] (hA : A < ⊤) :
    A.map K.subtype ≤ Subgroup.centralizer (R : Set G) := by
  let H : Subgroup G := A.map K.subtype
  have hHK : H ≤ K := by
    exact (Subgroup.map_le_range K.subtype A).trans_eq K.range_subtype
  have hHne : H ≠ K := by
    intro hEq
    apply hA.ne
    apply Subgroup.map_injective K.subtype_injective
    change A.map K.subtype = K at hEq
    calc
      A.map K.subtype = K := hEq
      _ = (⊤ : Subgroup K).map K.subtype := by
        rw [← MonoidHom.range_eq_map, K.range_subtype]
  have hHlt : H < K := lt_of_le_of_ne hHK hHne
  have hnormH : R ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer K R A hnormK
  have hlocal : ⁅R, H⁆ ≤ rho.ker :=
    properKernel_commutator_le_representation_ker rho hKR hcop hodd
      hRprime hGcard hfix ih hHlt hnormH
  have hbot : ⁅R, H⁆ = ⊥ := by
    apply le_antisymm
    · simpa [rho.ker_eq_bot hrho] using hlocal
    · exact bot_le
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.commutator_comm]
  exact hbot

end

end Submission.OddOrder.BG.Section03
