import Submission.OddOrder.PF.Section01.InertiaConstituentInjection

/-!
# Constituents of an injectively indexed irreducible sum

An injective finite family of irreducible characters with nonzero
coefficients has exactly that family as its constituent set.  This packages
the orthogonality calculation needed for the image clause of Peterfalvi
1.7(a).
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [IsAlgClosed k] [CharZero k]

/-- The constituents of a finite injective irreducible sum with nonzero
coefficients are precisely its summands. -/
theorem constituents_sum_injective_irreducibles
    {I : Type*} [Fintype I]
    (A : I → IrreducibleCharacter G k) (hA : Function.Injective A)
    (c : I → k) (hc : ∀ i, c i ≠ 0) :
    constituents
        (∑ i : I, c i • (A i : ClassFunction G k)) =
      Finset.univ.image A := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  ext chi
  rw [mem_constituents_iff, Finset.mem_image]
  unfold IrreducibleCharacter.IsConstituent
  constructor
  · intro hchi
    by_contra hnot
    push Not at hnot
    apply hchi
    rw [characterPairing_comm]
    change IrreducibleCharacter.pairingLeft
      (chi : ClassFunction G k)
        (∑ i : I, c i • (A i : ClassFunction G k)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    change c i * characterPairing
      (chi : ClassFunction G k) (A i : ClassFunction G k) = 0
    rw [IrreducibleCharacter.characterPairing_eq_zero]
    · exact mul_zero _
    · exact fun heq ↦ hnot i (Finset.mem_univ i) heq.symm
  · rintro ⟨i, _, hi⟩
    rw [characterPairing_comm]
    change IrreducibleCharacter.pairingLeft
      (chi : ClassFunction G k)
        (∑ j : I, c j • (A j : ClassFunction G k)) ≠ 0
    rw [map_sum]
    have hsum :
        ∑ j : I,
            IrreducibleCharacter.pairingLeft
              (chi : ClassFunction G k)
              (c j • (A j : ClassFunction G k)) = c i := by
      rw [Finset.sum_eq_single i]
      · rw [map_smul]
        change c i * characterPairing
          (chi : ClassFunction G k) (A i : ClassFunction G k) = c i
        rw [hi, IrreducibleCharacter.characterPairing_self, mul_one]
      · intro j _ hji
        rw [map_smul]
        change c j * characterPairing
          (chi : ClassFunction G k) (A j : ClassFunction G k) = 0
        rw [IrreducibleCharacter.characterPairing_eq_zero, mul_zero]
        intro heq
        apply hji
        apply hA
        exact heq.symm.trans hi.symm
      · simp
    rw [hsum]
    exact hc i

end ClassFunction

end

end Submission.OddOrder.PF
