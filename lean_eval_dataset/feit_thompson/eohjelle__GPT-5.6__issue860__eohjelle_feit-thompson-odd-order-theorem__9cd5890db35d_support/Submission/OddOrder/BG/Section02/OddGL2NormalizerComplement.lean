import Mathlib.GroupTheory.Transfer
import Submission.OddOrder.MathlibSupport.CrossPrimeCommutatorCentralizer

/-!
The Burnside-transfer branch of `BGsection2.der1_odd_GL2_charf`.

When the derived subgroup of the normalizer of a Sylow `q`-subgroup is a
`p`-group for `p != q`, the Sylow subgroup is central in its normalizer.
Burnside transfer then supplies a normal `q`-complement in the ambient group.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- A Sylow subgroup is centralized by its ambient normalizer when that
normalizer has derived subgroup of a different prime-power order. -/
theorem normalizer_le_centralizer_of_commutator_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (Q : Sylow q G)
    (hcomm : IsPGroup p (_root_.commutator (Subgroup.normalizer (Q : Set G))))
    (hpq : p ≠ q) :
    Subgroup.normalizer Q ≤ Subgroup.centralizer (Q : Set G) := by
  let N : Subgroup G := Subgroup.normalizer Q
  let QN : Sylow q N := Q.subtype Q.le_normalizer
  letI : QN.Normal := Subgroup.normal_in_normalizer
  have hcent : (⊤ : Subgroup N) ≤ Subgroup.centralizer (QN : Set N) :=
    le_centralizer_of_normal_isPGroup_of_commutator_isPGroup
      QN QN.isPGroup' hcomm hpq
  intro n hn x hx
  exact congrArg Subtype.val
    (hcent (Set.mem_univ ⟨n, hn⟩) ⟨x, Q.le_normalizer hx⟩ hx)

/-- Burnside's normal-complement conclusion for the proper-normalizer branch
of the odd two-dimensional linear-group argument. -/
theorem exists_normal_complement_of_normalizer_commutator_isPGroup
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (Q : Sylow q G)
    (hcomm : IsPGroup p (_root_.commutator (Subgroup.normalizer (Q : Set G))))
    (hpq : p ≠ q) :
    ∃ K : Subgroup G, K.Normal ∧ K.IsComplement' (Q : Subgroup G) := by
  let hcent := normalizer_le_centralizer_of_commutator_isPGroup Q hcomm hpq
  let K : Subgroup G := (MonoidHom.transferSylow Q hcent).ker
  have hK : K.IsComplement' (Q : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' Q hcent
  exact ⟨K, inferInstance, hK⟩

end Submission.OddOrder.BG.Section02
