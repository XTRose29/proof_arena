import Mathlib

/-!
Centers and normal subgroups of finite `p`-groups.

The main result is the standard fixed-point lemma that every nontrivial normal
subgroup of a finite `p`-group meets the center nontrivially.  It is the
orbit-counting input to the self-centralizing normal abelian subgroup argument.
-/

namespace Submission.OddOrder.MathlibSupport

open MulAction

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A nontrivial normal subgroup of a finite `p`-group has nontrivial
intersection with the center. -/
theorem normal_inf_center_ne_bot (hG : IsPGroup p G) (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : N ⊓ Subgroup.center G ≠ ⊥ := by
  letI : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN
  have hNp : IsPGroup p N := hG.to_subgroup N
  obtain ⟨n, hn, hcardN⟩ := hNp.nontrivial_iff_card.mp (by infer_instance)
  have hpN : p ∣ Nat.card N := by
    rw [hcardN]
    exact dvd_pow_self p hn.ne'
  have hConj : IsPGroup p (ConjAct G) := hG.of_equiv ConjAct.toConjAct
  have hpFixed : p ∣ Nat.card (fixedPoints (ConjAct G) N) :=
    Nat.modEq_zero_iff_dvd.mp
      ((hConj.card_modEq_card_fixedPoints N).symm.trans hpN.modEq_zero_nat)
  let oneFixed : fixedPoints (ConjAct G) N := ⟨1, by simp⟩
  have hfixedNonempty : Nonempty (fixedPoints (ConjAct G) N) :=
    ⟨oneFixed⟩
  have hfixedCard : 1 < Nat.card (fixedPoints (ConjAct G) N) :=
    (Fact.out (p := p.Prime)).one_lt.trans_le
      (Nat.le_of_dvd (Finite.card_pos_iff.mpr hfixedNonempty) hpFixed)
  haveI : Nontrivial (fixedPoints (ConjAct G) N) :=
    Finite.one_lt_card_iff_nontrivial.mp hfixedCard
  obtain ⟨x, hx⟩ := exists_ne oneFixed
  apply (Subgroup.nontrivial_iff_ne_bot (N ⊓ Subgroup.center G)).mp
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨x.1.1, ⟨x.1.2, ?_⟩, ?_⟩
  · apply Subgroup.mem_center_iff.mpr
    intro g
    have hfix := mem_fixedPoints.mp x.2 (ConjAct.toConjAct g)
    have hfixVal := congrArg Subtype.val hfix
    rw [ConjAct.Subgroup.val_conj_smul, ConjAct.toConjAct_smul] at hfixVal
    exact mul_inv_eq_iff_eq_mul.mp hfixVal
  · intro hxOne
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact hxOne

/-- Equality form of `normal_inf_center_ne_bot`. -/
theorem normal_inf_center_eq_bot_iff (hG : IsPGroup p G) (N : Subgroup G) [N.Normal] :
    N ⊓ Subgroup.center G = ⊥ ↔ N = ⊥ := by
  constructor
  · contrapose!
    exact normal_inf_center_ne_bot hG N
  · rintro rfl
    simp

end Submission.OddOrder.MathlibSupport
