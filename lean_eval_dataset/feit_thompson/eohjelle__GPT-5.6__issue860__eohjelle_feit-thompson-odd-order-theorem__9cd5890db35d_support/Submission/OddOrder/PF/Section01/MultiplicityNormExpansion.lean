import Submission.OddOrder.PF.Section01.InducedRepresentationNonzero

/-!
# Character norms as natural-number multiplicity sums

This file supplies the two algebraic expansions used in Peterfalvi 1.7(a).
The norm of a realized character is the sum of squares of its constituent
multiplicities.  More generally, the norm of a finite sum of realized
characters is the double sum of those multiplicities weighted by dimensions
of equivariant Hom spaces.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Field k] [Fintype G] [CharZero k]

/-- The self-pairing of a finite natural linear combination of realized
characters is its Hom-dimension Gram form. -/
theorem selfPairing_sum_realized
    {I : Type*} (s : Finset I) (m : I → ℕ) (W : I → FDRep k G) :
    characterPairing
        (∑ i ∈ s, (m i : k) • ofRepresentation (W i).ρ)
        (∑ i ∈ s, (m i : k) • ofRepresentation (W i).ρ) =
      ((∑ i ∈ s, ∑ j ∈ s,
          m i * m j * Module.finrank k (W j ⟶ W i) : ℕ) : k) := by
  calc
    characterPairing
        (∑ i ∈ s, (m i : k) • ofRepresentation (W i).ρ)
        (∑ i ∈ s, (m i : k) • ofRepresentation (W i).ρ) =
      ∑ i ∈ s, ∑ j ∈ s,
        (m i : k) * (m j : k) *
          characterPairing (ofRepresentation (W i).ρ)
            (ofRepresentation (W j).ρ) := by
      let Z : ClassFunction G k :=
        ∑ i ∈ s, (m i : k) • ofRepresentation (W i).ρ
      change characterPairing Z Z = _
      calc
        characterPairing Z Z = ∑ i ∈ s,
            characterPairing
              ((m i : k) • ofRepresentation (W i).ρ) Z := by
          change characterPairingRight Z Z = _
          dsimp only [Z]
          rw [map_sum]
          rfl
        _ = ∑ i ∈ s, ∑ j ∈ s,
            characterPairing
              ((m i : k) • ofRepresentation (W i).ρ)
              ((m j : k) • ofRepresentation (W j).ρ) := by
          apply Finset.sum_congr rfl
          intro i _
          change characterPairingLeft
            ((m i : k) • ofRepresentation (W i).ρ) Z = _
          dsimp only [Z]
          rw [map_sum]
          rfl
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [characterPairing_smul_left, characterPairing_smul_right]
          ring
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (m i : k) * (m j : k) *
          (Module.finrank k (W j ⟶ W i) : k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [FDRep.characterPairing_ofRepresentation_eq_finrank_hom]
    _ = ((∑ i ∈ s, ∑ j ∈ s,
        m i * m j * Module.finrank k (W j ⟶ W i) : ℕ) : k) := by
      simp only [Nat.cast_sum, Nat.cast_mul]

variable [IsAlgClosed k]

/-- The norm of a realized character is the sum of the squares of its
natural constituent multiplicities. -/
theorem realized_selfPairing_eq_sum_sq_multiplicity (V : FDRep k G) :
    characterPairing (ofRepresentation V.ρ) (ofRepresentation V.ρ) =
      ((∑ chi ∈ constituents (ofRepresentation V.ρ),
          chi.multiplicity V * chi.multiplicity V : ℕ) : k) := by
  let F : ClassFunction G k := ofRepresentation V.ρ
  have hpair (chi : IrreducibleCharacter G k) :
      characterPairing (chi : ClassFunction G k) F =
        (chi.multiplicity V : k) := by
    rw [characterPairing_comm]
    exact chi.characterPairing_ofRepresentation_eq_multiplicity V
  calc
    characterPairing F F =
        characterPairing
          (∑ chi ∈ constituents F,
            characterPairing (chi : ClassFunction G k) F •
              (chi : ClassFunction G k)) F := by
      rw [sum_constituents_eq]
    _ = ∑ chi ∈ constituents F,
        characterPairing (chi : ClassFunction G k) F *
          characterPairing (chi : ClassFunction G k) F := by
      change characterPairingRight F
        (∑ chi ∈ constituents F,
          characterPairing (chi : ClassFunction G k) F •
            (chi : ClassFunction G k)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro chi _
      rw [map_smul]
      rfl
    _ = ∑ chi ∈ constituents F,
        (chi.multiplicity V : k) * (chi.multiplicity V : k) := by
      apply Finset.sum_congr rfl
      intro chi _
      rw [hpair]
    _ = ((∑ chi ∈ constituents F,
        chi.multiplicity V * chi.multiplicity V : ℕ) : k) := by
      simp only [Nat.cast_sum, Nat.cast_mul]

end ClassFunction

end

end Submission.OddOrder.PF
