import Submission.OddOrder.BG.Section04.MetacyclicOmegaOne
import Submission.OddOrder.MathlibSupport.MetacyclicSubgroups
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial

/-!
Cyclicity of disjoint nontrivial factors in an odd metacyclic `p`-group.

This isolates the omega-one cardinality argument used in part (c) of
Bender--Glauberman Theorem 4.12.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

variable {P : Type u} [Group P] [Finite P]
variable {p : ℕ} [Fact p.Prime]

/-- Omega-one is nontrivial in a nontrivial finite `p`-group. -/
private theorem omegaOne_ne_bot_of_isPGroup'
    {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) (hcard : Nat.card Q ≠ 1) :
    omegaOne p Q ≠ ⊥ := by
  have hpCard : p ∣ Nat.card Q := hQ.card_eq_or_dvd.resolve_left hcard
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' p hpCard
  have hxne : x ≠ 1 := by
    intro hx
    rw [hx, orderOf_one] at hxorder
    exact (Fact.out : p.Prime).ne_one hxorder.symm
  have hxpow : x ^ p = 1 := by
    rw [← hxorder]
    exact pow_orderOf_eq_one x
  intro homega
  have hxmem : x ∈ omegaOne p Q := mem_omegaOne_of_pow_eq_one p hxpow
  rw [homega] at hxmem
  exact hxne (Subgroup.mem_bot.mp hxmem)

/-- In a noncyclic odd metacyclic `p`-group, two disjoint nontrivial
subgroups are cyclic.  Their omega-one subgroups inject by multiplication
into the rank-two omega-one subgroup of the ambient group. -/
theorem isCyclic_pair_of_disjoint_of_isMetacyclic
    (hP : IsPGroup p P) (hodd : Odd (Nat.card P))
    (hmeta : IsMetacyclic P) (hnotcyclic : ¬ IsCyclic P)
    (T C : Subgroup P) (hdis : Disjoint T C)
    (hTne : T ≠ ⊥) (hCne : C ≠ ⊥) :
    IsCyclic T ∧ IsCyclic C := by
  classical
  let OT : Subgroup P := (omegaOne p T).map T.subtype
  let OC : Subgroup P := (omegaOne p C).map C.subtype
  have hOTleT : OT ≤ T := Subgroup.map_subtype_le (omegaOne p T)
  have hOCleC : OC ≤ C := Subgroup.map_subtype_le (omegaOne p C)
  have hdisOmega : Disjoint OT OC :=
    Disjoint.mono hOTleT hOCleC hdis
  have hOTleOmega : OT ≤ omegaOne p P := map_omegaOne_le p T.subtype
  have hOCleOmega : OC ≤ omegaOne p P := map_omegaOne_le p C.subtype
  let mulOmega : OT × OC → omegaOne p P := fun z ↦
    ⟨(z.1 : P) * (z.2 : P),
      (omegaOne p P).mul_mem (hOTleOmega z.1.property)
        (hOCleOmega z.2.property)⟩
  have hmulOmegaInj : Function.Injective mulOmega := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisOmega
    exact congrArg (fun z : omegaOne p P ↦ (z : P)) hxy
  have hcardMul : Nat.card OT * Nat.card OC ≤ Nat.card (omegaOne p P) := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective mulOmega hmulOmegaInj
  have hElemP : IsElementaryAbelianOfRank p 2 (omegaOne p P) :=
    omegaOne_isElementaryAbelian_rank_two_of_isMetacyclic
      hmeta hP hodd hnotcyclic
  have hTp : IsPGroup p T := hP.to_subgroup T
  have hCp : IsPGroup p C := hP.to_subgroup C
  have hTodd : Odd (Nat.card T) :=
    hodd.of_dvd_nat T.card_subgroup_dvd_card
  have hCodd : Odd (Nat.card C) :=
    hodd.of_dvd_nat C.card_subgroup_dvd_card
  have hOmegaTne : omegaOne p T ≠ ⊥ :=
    omegaOne_ne_bot_of_isPGroup' hTp
      (T.one_lt_card_iff_ne_bot.mpr hTne).ne'
  have hOmegaCne : omegaOne p C ≠ ⊥ :=
    omegaOne_ne_bot_of_isPGroup' hCp
      (C.one_lt_card_iff_ne_bot.mpr hCne).ne'
  have hOTone : 1 < Nat.card OT := by
    rw [show Nat.card OT = Nat.card (omegaOne p T) by
      exact Subgroup.card_map_of_injective T.subtype_injective]
    exact (omegaOne p T).one_lt_card_iff_ne_bot.mpr hOmegaTne
  have hOCone : 1 < Nat.card OC := by
    rw [show Nat.card OC = Nat.card (omegaOne p C) by
      exact Subgroup.card_map_of_injective C.subtype_injective]
    exact (omegaOne p C).one_lt_card_iff_ne_bot.mpr hOmegaCne
  constructor
  · by_contra hTcyclic
    have hOmegaTcard : Nat.card OT = p ^ 2 := by
      calc
        Nat.card OT = Nat.card (omegaOne p T) :=
          Subgroup.card_map_of_injective T.subtype_injective
        _ = p ^ 2 :=
          (omegaOne_isElementaryAbelian_rank_two_of_isMetacyclic
            (isMetacyclic_subgroup hmeta T) hTp hTodd hTcyclic).card_eq
    rw [hOmegaTcard, hElemP.card_eq] at hcardMul
    exact (not_lt_of_ge hcardMul)
      (lt_mul_of_one_lt_right (pow_pos (Fact.out : p.Prime).pos 2) hOCone)
  · by_contra hCcyclic
    have hOmegaCcard : Nat.card OC = p ^ 2 := by
      calc
        Nat.card OC = Nat.card (omegaOne p C) :=
          Subgroup.card_map_of_injective C.subtype_injective
        _ = p ^ 2 :=
          (omegaOne_isElementaryAbelian_rank_two_of_isMetacyclic
            (isMetacyclic_subgroup hmeta C) hCp hCodd hCcyclic).card_eq
    rw [hOmegaCcard, hElemP.card_eq] at hcardMul
    exact (not_lt_of_ge hcardMul)
      (lt_mul_of_one_lt_left (pow_pos (Fact.out : p.Prime).pos 2) hOTone)

end

end Submission.OddOrder.BG.Section04
