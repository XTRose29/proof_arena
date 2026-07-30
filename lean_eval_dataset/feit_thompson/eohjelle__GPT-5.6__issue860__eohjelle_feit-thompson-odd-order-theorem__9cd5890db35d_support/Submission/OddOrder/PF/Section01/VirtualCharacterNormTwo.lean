import Submission.OddOrder.PF.Section01.VirtualCharacter

/-!
Norm-two virtual characters.

This file transfers the elementary norm-two classification of the integral
coefficient lattice to realized virtual characters. The augmentation-zero
hypothesis is what forces the two nonzero coefficients to have opposite signs.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

variable (G : Type u) (k : Type v) [Group G] [Field k]

namespace VirtualCharacter

variable {G k}

/--
A norm-two, augmentation-zero virtual character is a signed difference of two
distinct irreducible basis characters, at the coefficient level.
-/
theorem eq_signed_irreducible_difference_of_normSq_eq_two
    (f : VirtualCharacter G k) (hnorm : normSq f = 2) (hsum : coeffSum f = 0) :
    ∃ (chi psi : IrreducibleCharacter G k) (ε : ℤ), chi ≠ psi ∧ IsSign ε ∧
      f = ε • (Finsupp.single chi 1 - Finsupp.single psi 1) :=
  eq_sign_smul_single_sub_single_of_normSq_eq_two f hnorm hsum

/--
After realization, a norm-two, augmentation-zero virtual character is a signed
difference of two distinct irreducible characters.
-/
theorem realize_eq_signed_irreducible_difference_of_normSq_eq_two
    (f : VirtualCharacter G k) (hnorm : normSq f = 2) (hsum : coeffSum f = 0) :
    ∃ (chi psi : IrreducibleCharacter G k) (ε : ℤ), chi ≠ psi ∧ IsSign ε ∧
      realize f = (ε : k) •
        ((chi : ClassFunction G k) - (psi : ClassFunction G k)) := by
  classical
  obtain ⟨chi, psi, ε, hne, hε, hf⟩ :=
    eq_signed_irreducible_difference_of_normSq_eq_two f hnorm hsum
  refine ⟨chi, psi, ε, hne, hε, ?_⟩
  rw [hf]
  simp [smul_sub]

section Orthogonality

variable [Fintype G] [IsAlgClosed k] [CharZero k]

/-- Squared lattice norm agrees with the self-pairing after realization. -/
theorem characterPairing_realize_self (f : VirtualCharacter G k) :
    characterPairing (realize f) (realize f) = (normSq f : k) := by
  simpa [normSq] using characterPairing_realize f f

/-- A realized norm-two virtual character has self-pairing two. -/
theorem characterPairing_realize_self_eq_two
    (f : VirtualCharacter G k) (hnorm : normSq f = 2) :
    characterPairing (realize f) (realize f) = (2 : k) := by
  rw [characterPairing_realize_self, hnorm]
  norm_num

/--
The two irreducible constituents in the norm-two classification have pairing
coefficients `ε` and `-ε`, respectively.
-/
theorem exists_irreducible_pairings_of_normSq_eq_two
    (f : VirtualCharacter G k) (hnorm : normSq f = 2) (hsum : coeffSum f = 0) :
    ∃ (chi psi : IrreducibleCharacter G k) (ε : ℤ), chi ≠ psi ∧ IsSign ε ∧
      characterPairing (chi : ClassFunction G k) (realize f) = (ε : k) ∧
      characterPairing (psi : ClassFunction G k) (realize f) = (-ε : k) := by
  classical
  obtain ⟨chi, psi, ε, hne, hε, hf⟩ :=
    eq_signed_irreducible_difference_of_normSq_eq_two f hnorm hsum
  refine ⟨chi, psi, ε, hne, hε, ?_, ?_⟩
  · rw [characterPairing_irreducible_realize, hf]
    simp [hne]
  · rw [characterPairing_irreducible_realize, hf]
    simp [hne]

end Orthogonality

end VirtualCharacter

end

end Submission.OddOrder.PF
