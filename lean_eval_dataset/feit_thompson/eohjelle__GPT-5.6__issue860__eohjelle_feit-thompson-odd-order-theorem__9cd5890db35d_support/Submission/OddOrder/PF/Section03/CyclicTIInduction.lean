import Submission.OddOrder.PF.Section01.IrreducibleCharacterTransport
import Submission.OddOrder.PF.Section01.OddConjugateIrreducible
import Submission.OddOrder.PF.Section01.VirtualCharacterInduction
import Submission.OddOrder.PF.Section03.CyclicTIGroupFacts
import Submission.OddOrder.PF.Section03.NormalizedTICharacterPairing

/-!
# Induction from the cyclic-TI normalizer

This file specializes normalized-TI induction to the set
`W \ (W₁ ∪ W₂)` from Peterfalvi Section 3.  It packages the canonical
subgroup-copy adapters once, so the later isometry construction can use a
single linear map from class functions on `W` to class functions on `G`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped Classical

universe u

namespace CyclicTIHypothesis

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
variable [Field k] [CharZero k]
variable {G W W₁ W₂ : Subgroup Gamma}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

omit [Fintype Gamma] in
/-- The cyclic-TI set lies in the ambient group `G` and excludes the
identity. -/
theorem set_subset_group_diff_one
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    cyclicTISet W W₁ W₂ ⊆ (G : Set Gamma) \ {(1 : Gamma)} := by
  intro x hx
  exact ⟨h.le_group (cyclicTISet_subset W W₁ W₂ hx),
    (cyclicTISet_subset_diff_one W W₁ W₂ hx).2⟩

omit [Fintype Gamma] in
/-- The cyclic-TI set in the common ambient group is inverse-stable. -/
theorem ambientSet_invStable
    (_h : CyclicTIHypothesis G W W₁ W₂ defW) :
    IsInvStable (cyclicTISet W W₁ W₂) := by
  intro x
  rw [mem_cyclicTISet, mem_cyclicTISet]
  simp only [Subgroup.inv_mem_iff]

/-- Canonical class-function induction from `W` to `G`, through the copy of
`W` represented by `W.subgroupOf G`. -/
def induceClassFunction
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    ClassFunction W k →ₗ[k] ClassFunction G k :=
  (ClassFunction.induce (W.subgroupOf G)).comp
    (ClassFunction.toSubgroupOf W G h.le_group)

omit [CharZero k] in
@[simp]
theorem induceClassFunction_apply
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (alpha : ClassFunction W k) (g : G) :
    h.induceClassFunction alpha g =
      ClassFunction.induce (W.subgroupOf G)
        (ClassFunction.toSubgroupOf W G h.le_group alpha) g :=
  rfl

/-- On the cyclic-TI set, canonical induction agrees with the source class
function. -/
theorem induceClassFunction_apply_of_mem
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (alpha : ClassFunction W k)
    (halpha : alpha ∈
      ClassFunction.supportedOn (cyclicTISetInW W W₁ W₂))
    (w : W) (hw : w ∈ cyclicTISetInW W W₁ W₂) :
    h.induceClassFunction alpha ⟨w, h.le_group w.property⟩ = alpha w := by
  change alpha ∈ ClassFunction.supportedOn
    {x : W | (x : Gamma) ∈ cyclicTISet W W₁ W₂} at halpha
  change ((ClassFunction.induce (W.subgroupOf G))
    (ClassFunction.toSubgroupOf W G h.le_group alpha))
      ⟨w, h.le_group w.property⟩ = alpha w
  exact normedTI_Ind_id h.normedTI h.set_subset_group_diff_one
    alpha halpha w hw

/-- Ordinary induction from the cyclic-TI normalizer preserves the ordinary
inverse-argument character pairing on supported class functions. -/
theorem characterPairing_induceClassFunction
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (alpha beta : ClassFunction W k)
    (halpha : alpha ∈
      ClassFunction.supportedOn (cyclicTISetInW W W₁ W₂))
    (hbeta : beta ∈
      ClassFunction.supportedOn (cyclicTISetInW W W₁ W₂)) :
    characterPairing (h.induceClassFunction alpha)
        (h.induceClassFunction beta) =
      characterPairing alpha beta := by
  change alpha ∈ ClassFunction.supportedOn
    {x : W | (x : Gamma) ∈ cyclicTISet W W₁ W₂} at halpha
  change beta ∈ ClassFunction.supportedOn
    {x : W | (x : Gamma) ∈ cyclicTISet W W₁ W₂} at hbeta
  exact normedTI_induce_characterPairing h.normedTI
    h.set_subset_group_diff_one h.ambientSet_invStable
    alpha beta halpha hbeta

omit [CharZero k] in
private theorem characterPairing_toSubgroupOf
    (hWG : W ≤ G) (alpha beta : ClassFunction W k) :
    characterPairing
        (ClassFunction.toSubgroupOf W G hWG alpha)
        (ClassFunction.toSubgroupOf W G hWG beta) =
      characterPairing alpha beta := by
  let H : Subgroup G := W.subgroupOf G
  let e : H ≃* W := Subgroup.subgroupOfEquivOfLe hWG
  have hcard : Nat.card H = Nat.card W := Nat.card_congr e.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv e.toEquiv
  intro x
  rfl

/-- Frobenius reciprocity against the trivial character, in the exact form
used by the cyclic-TI isometry construction.  No support hypothesis is
needed. -/
theorem characterPairing_induceClassFunction_trivial
    [IsAlgClosed k]
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (alpha : ClassFunction W k) :
    characterPairing (h.induceClassFunction alpha)
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
          ClassFunction G k) =
      characterPairing alpha
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W k) :
          ClassFunction W k) := by
  change characterPairing
      (ClassFunction.induce (W.subgroupOf G)
        (ClassFunction.toSubgroupOf W G h.le_group alpha))
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
        ClassFunction G k) = _
  rw [ClassFunction.frobeniusReciprocity]
  have htriv :
      ClassFunction.restrict (W.subgroupOf G)
          ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
            ClassFunction G k) =
        ClassFunction.toSubgroupOf W G h.le_group
          ((IrreducibleCharacter.trivial : IrreducibleCharacter W k) :
            ClassFunction W k) := by
    ext x
    simp
  rw [htriv]
  exact characterPairing_toSubgroupOf h.le_group alpha
    ((IrreducibleCharacter.trivial : IrreducibleCharacter W k) :
      ClassFunction W k)

section VirtualCharacter

variable [IsAlgClosed k]

/-- Transport virtual characters from `W` to its canonical subgroup copy in
`G`, reindexing irreducible characters along the canonical group
equivalence. -/
def transportVirtualCharacter
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    VirtualCharacter W k ≃+ VirtualCharacter (W.subgroupOf G) k :=
  Finsupp.domCongr
    (IrreducibleCharacter.equivOfMulEquiv
      (Subgroup.subgroupOfEquivOfLe h.le_group))

/-- Realization of virtual-character transport is the canonical class
function transport to `W.subgroupOf G`. -/
theorem realize_transportVirtualCharacter
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (f : VirtualCharacter W k) :
    VirtualCharacter.realize (h.transportVirtualCharacter f) =
      ClassFunction.toSubgroupOf W G h.le_group
        (VirtualCharacter.realize f) := by
  classical
  induction f using Finsupp.induction with
  | zero => simp [transportVirtualCharacter]
  | single_add chi z f hchi hz ih =>
      have hsingle :
          h.transportVirtualCharacter
              (Finsupp.single chi z : VirtualCharacter W k) =
            Finsupp.single
              (IrreducibleCharacter.comapMulEquiv
                (Subgroup.subgroupOfEquivOfLe h.le_group) chi) z := by
        simp [transportVirtualCharacter,
          IrreducibleCharacter.equivOfMulEquiv,
          Finsupp.domCongr_apply, Finsupp.equivMapDomain_single]
      rw [map_add, map_add, VirtualCharacter.realize_add, map_add, ih]
      congr 1
      rw [hsingle, VirtualCharacter.realize_single,
        VirtualCharacter.realize_single]
      ext x
      simp [IrreducibleCharacter.comapMulEquiv_apply]

/-- Induction on virtual characters specialized to the cyclic-TI subgroup
copy. -/
def induceVirtualCharacter
    (h : CyclicTIHypothesis G W W₁ W₂ defW) :
    VirtualCharacter W k →+ VirtualCharacter G k :=
  (VirtualCharacter.induce (W.subgroupOf G)).comp
    h.transportVirtualCharacter.toAddMonoidHom

/-- The specialized virtual-character induction realizes to
`induceClassFunction`. -/
theorem realize_induceVirtualCharacter
    (h : CyclicTIHypothesis G W W₁ W₂ defW)
    (f : VirtualCharacter W k) :
    VirtualCharacter.realize (h.induceVirtualCharacter f) =
      h.induceClassFunction (VirtualCharacter.realize f) := by
  rw [induceVirtualCharacter, AddMonoidHom.comp_apply,
    VirtualCharacter.realize_induce]
  change ClassFunction.induce (W.subgroupOf G)
      (VirtualCharacter.realize (h.transportVirtualCharacter f)) = _
  rw [realize_transportVirtualCharacter]
  rfl

end VirtualCharacter

end CyclicTIHypothesis

end

end Submission.OddOrder.PF
