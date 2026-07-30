import Submission.OddOrder.PF.Section01.NormalSubgroupConstituentKernels

/-!
# Irreducible constituent expansions

Peterfalvi 1.7 uses the finite set of irreducible constituents of an
induced character and expands that character over precisely those
constituents.  Character completeness already gives the expansion over all
irreducibles; this file packages its finite support and removes the zero
coefficients.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace ClassFunction

variable {G k : Type u}
  [Group G] [Field k] [IsAlgClosed k] [CharZero k]

/-- The finite set of irreducible constituents of a class function. -/
def constituents [Fintype G] (f : ClassFunction G k) :
    Finset (IrreducibleCharacter G k) := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact Finset.univ.filter fun chi ↦ chi.IsConstituent f

@[simp]
theorem mem_constituents_iff [Fintype G]
    (f : ClassFunction G k) (chi : IrreducibleCharacter G k) :
    chi ∈ constituents f ↔ chi.IsConstituent f := by
  classical
  simp [constituents]

theorem not_mem_constituents_iff [Fintype G]
    (f : ClassFunction G k) (chi : IrreducibleCharacter G k) :
    chi ∉ constituents f ↔
      characterPairing f (chi : ClassFunction G k) = 0 := by
  rw [mem_constituents_iff]
  unfold IrreducibleCharacter.IsConstituent
  simp only [not_ne_iff]

/-- A class function is the sum of its irreducible constituents, weighted
by their character pairings.  This is the Lean form of source
`cfun_sum_constt`. -/
theorem sum_constituents_eq [Fintype G]
    (f : ClassFunction G k) :
    (∑ chi ∈ constituents f,
        characterPairing (chi : ClassFunction G k) f •
          (chi : ClassFunction G k)) = f := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  calc
    _ = irreducibleCharacterExpansion f := by
      rw [irreducibleCharacterExpansion, constituents, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro chi _
      by_cases hchi : chi.IsConstituent f
      · simp only [hchi, if_true]
      · have hzero' :
            characterPairing f (chi : ClassFunction G k) = 0 :=
          not_ne_iff.mp hchi
        have hzero :
            characterPairing (chi : ClassFunction G k) f = 0 :=
          (characterPairing_comm (chi : ClassFunction G k) f).trans hzero'
        simp only [hchi, if_false, hzero, zero_smul]
    _ = f := irreducibleCharacterExpansion_eq f

end ClassFunction

end

end Submission.OddOrder.PF
