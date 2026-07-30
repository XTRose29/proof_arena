import Submission.OddOrder.MathlibSupport.Solvability
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Proper-kernel restriction data for the induction in Bender-Glauberman
Theorem 3.4.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R H : Subgroup G}

omit [Finite G] in
/-- A proper subgroup of the normal factor, normalized by the complement,
is complementary to the same complement inside the subgroup they generate. -/
theorem properKernel_subgroupOf_isComplement
    (hKR : K.IsComplement' R) (hHK : H ≤ K)
    (hnorm : R ≤ Subgroup.normalizer (H : Set G)) :
    (H.subgroupOf (R ⊔ H)).IsComplement' (R.subgroupOf (R ⊔ H)) := by
  let J : Subgroup G := R ⊔ H
  let HJ : Subgroup J := H.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  letI : HJ.Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  have hdis : Disjoint HJ RJ := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp
        (Disjoint.mono hHK le_rfl hKR.disjoint)]
      exact ⟨hx.1, hx.2⟩
    exact Subgroup.mem_bot.mp hxbot
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  have hnormJ : RJ ≤ Subgroup.normalizer (HJ : Set J) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : HJ.Normal)]
    exact le_top
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left HJ RJ hnormJ]
  have hsup : HJ ⊔ RJ = ⊤ := by
    change H.subgroupOf J ⊔ R.subgroupOf J = ⊤
    rw [← Subgroup.subgroupOf_sup (show H ≤ J from le_sup_right)
      (show R ≤ J from le_sup_left)]
    simp [J, sup_comm]
  rw [hsup]
  rfl

omit [Finite G] in
/-- The subgroup form of an included factor has the same cardinality. -/
theorem natCard_subgroupOf_eq {J L : Subgroup G} (hLJ : L ≤ J) :
    Nat.card (L.subgroupOf J) = Nat.card L := by
  have hc := Subgroup.card_map_of_injective
    (K := L.subgroupOf J) J.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hLJ] at hc
  exact hc.symm

/-- Replacing the normal factor by a proper normalized subgroup strictly
decreases the generated semidirect-product order. -/
theorem natCard_sup_lt_of_properKernel
    (hKR : K.IsComplement' R) (hHK : H < K)
    (hnorm : R ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card (↑(R ⊔ H)) < Nat.card G := by
  let J : Subgroup G := R ⊔ H
  let HJ : Subgroup J := H.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  have hcomp : HJ.IsComplement' RJ := by
    simpa [J, HJ, RJ] using
      properKernel_subgroupOf_isComplement hKR hHK.le hnorm
  have hcardHJ : Nat.card HJ = Nat.card H :=
    natCard_subgroupOf_eq (show H ≤ J from le_sup_right)
  have hcardRJ : Nat.card RJ = Nat.card R :=
    natCard_subgroupOf_eq (show R ≤ J from le_sup_left)
  have hcardHlt : Nat.card H < Nat.card K := by
    have hle : Nat.card H ≤ Nat.card K := Subgroup.card_le_of_le hHK.le
    exact lt_of_le_of_ne hle fun heq ↦
      hHK.ne (Subgroup.eq_of_le_of_card_ge hHK.le heq.ge)
  have hRpos : 0 < Nat.card R := Nat.card_pos
  rw [← hcomp.card_mul, hcardHJ, hcardRJ,
    ← hKR.card_mul]
  exact Nat.mul_lt_mul_of_pos_right hcardHlt hRpos

omit [Finite G] in
/-- Coprimality of the two factors descends to the proper-kernel
restriction. -/
theorem natCard_coprime_subgroupOf_properKernel
    (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hHK : H ≤ K) :
    Nat.Coprime
      (Nat.card (H.subgroupOf (R ⊔ H)))
      (Nat.card (R.subgroupOf (R ⊔ H))) := by
  rw [natCard_subgroupOf_eq (show H ≤ R ⊔ H from le_sup_right),
    natCard_subgroupOf_eq (show R ≤ R ⊔ H from le_sup_left)]
  exact hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hHK)

omit [Finite G] in
/-- Oddness descends to the generated proper-kernel subgroup. -/
theorem odd_natCard_sup (hodd : Odd (Nat.card G)) :
    Odd (Nat.card (↑(R ⊔ H))) :=
  hodd.of_dvd_nat (show Subgroup G from R ⊔ H).card_subgroup_dvd_card

omit [Finite G] in
/-- Solvability descends to the generated proper-kernel subgroup. -/
theorem isSolvable_sup [IsSolvable G] : IsSolvable (↑(R ⊔ H)) :=
  isSolvable_subgroup_of_isSolvable (R ⊔ H)

end Submission.OddOrder.BG.Section03
