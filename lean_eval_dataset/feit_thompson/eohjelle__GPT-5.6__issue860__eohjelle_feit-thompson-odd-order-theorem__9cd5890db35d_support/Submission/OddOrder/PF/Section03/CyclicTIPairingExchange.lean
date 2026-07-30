import Submission.OddOrder.PF.Section03.CyclicTIIsometry

/-!
# The cyclic-TI pairing exchange identity

This file ports Peterfalvi (3.7), `cycTIiso_cfdot_exchange`.  The proof uses
only the agreement of the cyclic-TI isometry with induction on the supported
subspace and the hypothesis that the other class function vanishes on the
cyclic-TI set.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {G W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

omit [IsAlgClosed k] [CharZero k] in
private theorem characterPairing_sub_right'
    {H : Type u} [Group H] [Fintype H]
    (z f g : ClassFunction H k) :
    characterPairing z (f - g) =
      characterPairing z f - characterPairing z g := by
  change characterPairingLeft z (f - g) = _
  exact map_sub (characterPairingLeft z) f g

namespace CyclicTIIsometryData

/-- Subgroup-copy form of Peterfalvi (3.7).  This is the reusable core of
`pairing_exchange`; its vanishing hypothesis is stated in precisely the form
needed after Frobenius reciprocity. -/
theorem pairing_exchange_subgroupOf
    {h : CyclicTIHypothesis G W W₁ W₂ defW}
    (iso : CyclicTIIsometryData (k := k) h)
    {psi : ClassFunction G k}
    (hpsi : ClassFunction.restrict (W.subgroupOf G) psi ∈
      ClassFunction.vanishingOn h.cyclicTISetInSubgroupOf)
    (i₁ i₂ : IrreducibleCharacter W₁ k)
    (j₁ j₂ : IrreducibleCharacter W₂ k) :
    characterPairing psi
          (iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i₁ j₁ :
              ClassFunction W k)) +
        characterPairing psi
          (iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i₂ j₂ :
              ClassFunction W k)) =
      characterPairing psi
          (iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i₁ j₂ :
              ClassFunction W k)) +
        characterPairing psi
          (iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i₂ j₁ :
              ClassFunction W k)) := by
  let phi : ClassFunction W k :=
    (IrreducibleCharacter.cyclicTICharacter defW i₁ j₁ :
        ClassFunction W k) +
      (IrreducibleCharacter.cyclicTICharacter defW i₂ j₂ :
        ClassFunction W k) -
      (IrreducibleCharacter.cyclicTICharacter defW i₁ j₂ :
        ClassFunction W k) -
      (IrreducibleCharacter.cyclicTICharacter defW i₂ j₁ :
        ClassFunction W k)
  have hphi :
      phi ∈ ClassFunction.supportedOn (cyclicTISetInW W W₁ W₂) := by
    letI : IsCyclic W₁ := h.left_cyclic
    letI : IsCyclic W₂ := h.right_cyclic
    rw [ClassFunction.mem_supportedOn_iff]
    intro w hw
    obtain ⟨⟨x, y⟩, rfl⟩ := defW.mulEquiv.surjective w
    dsimp only [phi]
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply,
      IrreducibleCharacter.cyclicTICharacter_mulEquiv]
    rw [mem_cyclicTISetInW, defW.mulEquiv_mem_left_iff,
      defW.mulEquiv_mem_right_iff] at hw
    by_cases hx : x = 1
    · simp [hx]
    · have hy : y = 1 := by
        by_contra hy
        exact hw ⟨hy, hx⟩
      simp [hy]
  have hphiSubgroupOf :
      ClassFunction.toSubgroupOf W G h.le_group phi ∈
        ClassFunction.supportedOn h.cyclicTISetInSubgroupOf := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro w hw
    change phi (Subgroup.subgroupOfEquivOfLe h.le_group w) = 0
    exact ClassFunction.eq_zero_of_mem_supportedOn hphi hw
  have hinducedZero :
      characterPairing (h.induceClassFunction phi) psi = 0 := by
    change characterPairing
      (ClassFunction.induce (W.subgroupOf G)
        (ClassFunction.toSubgroupOf W G h.le_group phi)) psi = 0
    rw [ClassFunction.frobeniusReciprocity]
    apply characterPairing_eq_zero_of_disjoint_of_invStable_left
      disjoint_compl_right h.cyclicTISetInSubgroupOf_invStable
      hphiSubgroupOf
    simpa only [ClassFunction.vanishingOn_eq_supportedOn_compl] using hpsi
  have hmapZero : characterPairing psi (iso.linearMap phi) = 0 := by
    rw [iso.induce_supported phi hphi]
    calc
      characterPairing psi (h.induceClassFunction phi) =
          characterPairing (h.induceClassFunction phi) psi :=
        characterPairing_comm _ _
      _ = 0 := hinducedZero
  dsimp only [phi] at hmapZero
  simp only [map_add, map_sub, characterPairing_add_right,
    characterPairing_sub_right'] at hmapZero
  rw [sub_sub, sub_eq_zero] at hmapZero
  exact hmapZero

/-- Peterfalvi (3.7), Coq's `cycTIiso_cfdot_exchange`: pairing with a class
function that vanishes on the cyclic-TI set satisfies the four-corner
exchange identity. -/
theorem pairing_exchange
    {h : CyclicTIHypothesis G W W₁ W₂ defW}
    (iso : CyclicTIIsometryData (k := k) h)
    {psi : ClassFunction G k}
    (hpsi : Set.EqOn
      (fun w : W ↦ psi ⟨w, h.le_group w.property⟩) 0
      (cyclicTISetInW W W₁ W₂))
    (i₁ i₂ : IrreducibleCharacter W₁ k)
    (j₁ j₂ : IrreducibleCharacter W₂ k) :
    characterPairing psi
          (iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i₁ j₁ :
              ClassFunction W k)) +
        characterPairing psi
          (iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i₂ j₂ :
              ClassFunction W k)) =
      characterPairing psi
          (iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i₁ j₂ :
              ClassFunction W k)) +
        characterPairing psi
          (iso.linearMap
            (IrreducibleCharacter.cyclicTICharacter defW i₂ j₁ :
              ClassFunction W k)) := by
  apply iso.pairing_exchange_subgroupOf ?_ i₁ i₂ j₁ j₂
  rw [ClassFunction.mem_vanishingOn_iff]
  intro w hw
  change psi (w : G) = 0
  simpa using (hpsi hw)

end CyclicTIIsometryData

end

end Submission.OddOrder.PF
