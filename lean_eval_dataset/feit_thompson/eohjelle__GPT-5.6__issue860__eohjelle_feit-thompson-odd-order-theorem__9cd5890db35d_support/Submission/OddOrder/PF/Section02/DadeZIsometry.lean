import Submission.OddOrder.PF.Section02.DadeVirtualCharacter
import Submission.OddOrder.PF.Section02.DadeReciprocity
import Submission.OddOrder.PF.Section02.DadeBasicProperties

/-!
# Peterfalvi 2.10: integral form of the Dade isometry

On virtual characters supported by the Dade set, the Dade map preserves the
star character pairing and is realized by a virtual character supported away
from the identity.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u v

variable {Γ : Type u} [Group Γ]

/-- The source-faithful integral isometry bundle for the Dade map. -/
theorem Dade_Zisometry
    [Fintype Γ]
    {k : Type v} [Field k] [IsAlgClosed k] [CharZero k] [StarRing k]
    {G L : Subgroup Γ} {A : Set Γ} (ddA : DadeHypothesis G L A) :
    (∀ α β : VirtualCharacter L k,
      VirtualCharacter.realize α ∈
        ClassFunction.supportedOn {x : L | (x : Γ) ∈ A} →
      VirtualCharacter.realize β ∈
        ClassFunction.supportedOn {x : L | (x : Γ) ∈ A} →
      starCharacterPairing (Dade ddA (VirtualCharacter.realize α))
          (Dade ddA (VirtualCharacter.realize β)) =
        starCharacterPairing (VirtualCharacter.realize α)
          (VirtualCharacter.realize β)) ∧
    (∀ α : VirtualCharacter L k,
      VirtualCharacter.realize α ∈
        ClassFunction.supportedOn {x : L | (x : Γ) ∈ A} →
      ∃ β : VirtualCharacter G k,
        Dade ddA (VirtualCharacter.realize α) =
            VirtualCharacter.realize β ∧
          VirtualCharacter.realize β ∈
            ClassFunction.supportedOn {x : G | x ≠ 1}) := by
  constructor
  · intro α β hα hβ
    exact Dade_isometry ddA
      (VirtualCharacter.realize α) (VirtualCharacter.realize β) hα hβ
  · intro α hα
    refine ⟨Dade_virtualCharacter ddA α, Dade_vchar ddA α hα, ?_⟩
    rw [← Dade_vchar ddA α hα]
    exact Dade_cfun ddA (VirtualCharacter.realize α)

end

end Submission.OddOrder.PF
