import Submission.OddOrder.PF.Section02.DadeExpansion
import Submission.OddOrder.PF.Section02.DadeInducedVirtualCharacter

/-!
# Peterfalvi 2.10: virtual-character form of the Dade expansion

The alternating expansion of the Dade isometry is integral when its input
is a virtual character.  This file records only the resulting virtual
character and its realization; no additional lattice or pairing structure
is asserted.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u v

variable {Γ : Type u} [Group Γ]

/-- The virtual character whose realization is the Dade expansion. -/
noncomputable def Dade_virtualCharacter
    [Fintype Γ]
    {k : Type v} [Field k] [IsAlgClosed k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (α : VirtualCharacter L k) :
    VirtualCharacter G k :=
  -∑ ω : DadeSubsetOrbit ddA,
    ((-1 : ℤ) ^ (Dade_transversal ω : Set Γ).ncard) •
      Dade_ind_vchar_restriction ddA α (Dade_transversal ω)

/-- The Dade isometry of a supported realized virtual character is the
realization of `Dade_virtualCharacter`. -/
theorem Dade_vchar
    [Fintype Γ]
    {k : Type v} [Field k] [IsAlgClosed k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (α : VirtualCharacter L k)
    (hα : VirtualCharacter.realize α ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A}) :
    Dade ddA (VirtualCharacter.realize α) =
      VirtualCharacter.realize (Dade_virtualCharacter ddA α) := by
  rw [Dade_expansion ddA (VirtualCharacter.realize α) hα]
  unfold Dade_virtualCharacter
  rw [VirtualCharacter.realize_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _hω
  rw [map_zsmul, Dade_ind_restriction_vchar]
  rw [← Int.cast_smul_eq_zsmul k, Int.cast_pow]
  norm_num

end

end Submission.OddOrder.PF
