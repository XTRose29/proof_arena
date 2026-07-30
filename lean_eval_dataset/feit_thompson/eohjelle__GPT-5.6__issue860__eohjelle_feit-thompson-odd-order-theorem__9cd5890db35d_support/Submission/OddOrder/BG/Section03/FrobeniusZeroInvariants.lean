import Mathlib.GroupTheory.Commutator.Basic
import Submission.OddOrder.BG.Section03.FrobeniusRepresentation

/-!
The zero-fixed-space contrapositive of Bender-Glauberman Lemma 3.3.
-/

namespace Submission.OddOrder.BG.Section03

universe u v w

variable {G : Type u} [Group G] [Fintype G]
variable {K R : Subgroup G}
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

namespace IsFrobeniusDecomposition

/-- If the complement-fixed space is zero in coprime characteristic, the
whole Frobenius kernel acts trivially. -/
theorem kernel_le_representation_ker_of_invariants_eq_bot
    (h : IsFrobeniusDecomposition K R)
    (rho : _root_.Representation k G V)
    (hcard : (Nat.card K : k) ≠ 0)
    (hfix : _root_.Representation.invariants
      (rho.comp R.subtype : _root_.Representation k R V) = ⊥) :
    K ≤ rho.ker := by
  classical
  by_contra hker
  apply (h.complement_invariants_ne_bot rho ?_ hker) hfix
  simpa [Nat.card_eq_fintype_card] using hcard

/-- Consequently, the mixed commutator of the complement and kernel lies in
the representation kernel. -/
theorem commutator_le_representation_ker_of_invariants_eq_bot
    (h : IsFrobeniusDecomposition K R)
    (rho : _root_.Representation k G V)
    (hcard : (Nat.card K : k) ≠ 0)
    (hfix : _root_.Representation.invariants
      (rho.comp R.subtype : _root_.Representation k R V) = ⊥) :
    ⁅R, K⁆ ≤ rho.ker := by
  letI : K.Normal := h.kernel_normal
  exact (Subgroup.commutator_le_right R K).trans
    (h.kernel_le_representation_ker_of_invariants_eq_bot rho hcard hfix)

omit [Fintype G] in
/-- A nonzero ambient group cardinal in the coefficient field implies the
same for every subgroup cardinal. -/
theorem subgroup_natCard_cast_ne_zero_of_group_natCard_cast_ne_zero
    (H : Subgroup G) (hG : (Nat.card G : k) ≠ 0) :
    (Nat.card H : k) ≠ 0 := by
  intro hzero
  apply hG
  rw [← H.card_mul_index, Nat.cast_mul, hzero, zero_mul]

/-- Ambient-characteristic form used in the induction for Theorem 3.4. -/
theorem commutator_le_representation_ker_of_invariants_eq_bot_of_group_card
    (h : IsFrobeniusDecomposition K R)
    (rho : _root_.Representation k G V)
    (hGcard : (Fintype.card G : k) ≠ 0)
    (hfix : _root_.Representation.invariants
      (rho.comp R.subtype : _root_.Representation k R V) = ⊥) :
    ⁅R, K⁆ ≤ rho.ker := by
  have hGcard' : (Nat.card G : k) ≠ 0 := by
    simpa [Nat.card_eq_fintype_card] using hGcard
  have hKcard' : (Nat.card K : k) ≠ 0 :=
    subgroup_natCard_cast_ne_zero_of_group_natCard_cast_ne_zero K hGcard'
  apply h.commutator_le_representation_ker_of_invariants_eq_bot rho
  · exact hKcard'
  · exact hfix

end IsFrobeniusDecomposition

end

end Submission.OddOrder.BG.Section03
