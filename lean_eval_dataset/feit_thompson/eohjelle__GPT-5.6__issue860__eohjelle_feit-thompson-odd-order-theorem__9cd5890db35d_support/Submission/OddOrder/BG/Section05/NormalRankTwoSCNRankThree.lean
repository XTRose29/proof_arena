import Submission.OddOrder.BG.Section05.SCNRankThree
import Submission.OddOrder.MathlibSupport.NormalSubgroupPowerSeries
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial
import Submission.OddOrder.MathlibSupport.SCNExistence
import Submission.OddOrder.MathlibSupport.SubgroupCardinality
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
Bender--Glauberman Lemma 5.1(b).
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Extract an ambient-normal elementary-abelian rank-three subgroup from an
SCN subgroup of rank at least three.  This is the `Ohm_1(C)` and
`normal_pgroup` paragraph in the Coq proof of Lemma 5.1(b). -/
private theorem exists_normal_elementaryAbelian_rank_three_of_scn
    (hG : IsPGroup p G) {C : Subgroup G}
    (hC : Submission.OddOrder.BG.Section04.IsSCNAtLeastRank p 3 C) :
    ∃ B : Subgroup G, B.Normal ∧ IsElementaryAbelianOfRank p 3 B := by
  obtain ⟨hSCN, F, hFC, hF⟩ := hC
  have hCnormal : C.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    exact top_unique hSCN.le_normalizer
  letI : C.Normal := hCnormal
  letI : IsMulCommutative C := hSCN.commutative
  let M : Subgroup G := (omegaOne p C).map C.subtype
  have hMnormal : M.Normal := by
    dsimp [M]
    infer_instance
  letI : M.Normal := hMnormal
  have hMcomm : IsMulCommutative M := by
    dsimp [M]
    infer_instance
  have hMpow : ∀ x : M, x ^ p = 1 := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨xC, hxOmega, hx⟩
    apply Subtype.ext
    change x ^ p = 1
    rw [← hx]
    simpa using congrArg Subtype.val
      (omegaOne_pow_eq_one_of_mul_closed p
        (fun a b ha hb ↦ by rw [mul_pow, ha, hb, one_mul]) hxOmega)
  have hMelem : IsElementaryAbelianGroup p M :=
    { isPGroup := hG.to_subgroup M
      commutative := hMcomm
      pow_eq_one := hMpow }
  have hFM : F ≤ M := by
    intro x hxF
    let xC : C := ⟨x, hFC hxF⟩
    have hxCp : xC ^ p = 1 := by
      apply Subtype.ext
      change x ^ p = 1
      exact congrArg Subtype.val (hF.pow_eq_one ⟨x, hxF⟩)
    exact ⟨xC, mem_omegaOne_of_pow_eq_one p hxCp, rfl⟩
  obtain ⟨n, hMcard⟩ := hMelem.isPGroup.exists_card_eq
  have hpows : p ^ 3 ≤ p ^ n := by
    simpa only [hF.card_eq, hMcard] using Subgroup.card_le_of_le hFM
  have hn : 3 ≤ n :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpows
  obtain ⟨B, hBM, hBnormal, hBcard⟩ :=
    exists_normal_subgroup_card_pow_le hG M hMcard hn
  letI : IsMulCommutative M := hMcomm
  have hBcomm : IsMulCommutative B := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val
      (mul_comm (⟨x, hBM x.2⟩ : M) (⟨y, hBM y.2⟩ : M))
  have hBpow : ∀ x : B, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    change (x : G) ^ p = 1
    exact congrArg Subtype.val (hMpow ⟨x, hBM x.2⟩)
  exact ⟨B, hBnormal,
    { isPGroup := hG.to_subgroup B
      commutative := hBcomm
      pow_eq_one := hBpow
      card_eq := hBcard }⟩

/-- `BGsection5.v: normal_p2Elem_SCN3` (Bender--Glauberman Lemma 5.1(b)). -/
theorem normal_p2Elem_SCN3
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    {E : Subgroup G} (hE : IsElementaryAbelianOfRank p 2 E)
    (hEnormal : E.Normal) :
    ∃ C : Subgroup G,
      Submission.OddOrder.BG.Section04.IsSCNAtLeastRank p 3 C ∧ E ≤ C := by
  obtain ⟨C₀, hC₀⟩ := rank3_SCN3 hG hodd hRank3
  obtain ⟨B, hBnormal, hB⟩ :=
    exists_normal_elementaryAbelian_rank_three_of_scn hG hC₀
  letI : E.Normal := hEnormal
  letI : B.Normal := hBnormal
  let CBE : Subgroup G := centralizerWithin B E
  have hCBEnormal : CBE.Normal := by
    dsimp [CBE, centralizerWithin]
    infer_instance
  letI : CBE.Normal := hCBEnormal
  let D : Subgroup G := E ⊔ CBE
  have hDnormal : D.Normal := by
    dsimp [D]
    infer_instance
  letI : D.Normal := hDnormal
  have hDclosure :
      D = Subgroup.closure ((E : Set G) ∪ (CBE : Set G)) := by
    apply le_antisymm
    · apply sup_le
      · intro x hx
        exact Subgroup.subset_closure (Or.inl hx)
      · intro x hx
        exact Subgroup.subset_closure (Or.inr hx)
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · exact (show E ≤ E ⊔ CBE from le_sup_left) hx
      · exact (show CBE ≤ E ⊔ CBE from le_sup_right) hx
  have hDcomm : IsMulCommutative D := by
    rw [hDclosure]
    apply Subgroup.isMulCommutative_closure
    intro x hx y hy
    rcases hx with hxE | hxC <;> rcases hy with hyE | hyC
    · letI : IsMulCommutative E := hE.commutative
      exact congrArg Subtype.val
        (mul_comm (⟨x, hxE⟩ : E) (⟨y, hyE⟩ : E))
    · exact (mem_centralizerWithin.mp hyC).2 x hxE
    · exact ((mem_centralizerWithin.mp hxC).2 y hyE).symm
    · letI : IsMulCommutative B := hB.commutative
      exact congrArg Subtype.val
        (mul_comm (⟨x, (mem_centralizerWithin.mp hxC).1⟩ : B)
          (⟨y, (mem_centralizerWithin.mp hyC).1⟩ : B))
  have hDpow : ∀ x : D, x ^ p = 1 := by
    intro x
    have hxprod : (x : G) ∈ (E : Set G) * (CBE : Set G) := by
      rw [← Subgroup.normal_mul E CBE]
      exact x.2
    rcases hxprod with ⟨e, he, c, hc, hx⟩
    apply Subtype.ext
    change (x : G) ^ p = 1
    rw [← hx]
    have hec : Commute e c := (mem_centralizerWithin.mp hc).2 e he
    rw [hec.mul_pow]
    have hep : e ^ p = 1 :=
      congrArg Subtype.val (hE.pow_eq_one ⟨e, he⟩)
    have hcp : c ^ p = 1 :=
      congrArg Subtype.val
        (hB.pow_eq_one ⟨c, (mem_centralizerWithin.mp hc).1⟩)
    rw [hep, hcp, one_mul]
  have hDelem : IsElementaryAbelianGroup p D :=
    { isPGroup := hG.to_subgroup D
      commutative := hDcomm
      pow_eq_one := hDpow }
  have hDcard : p ^ 2 < Nat.card D := by
    by_contra hnot
    have hDle : Nat.card D ≤ p ^ 2 := Nat.le_of_not_gt hnot
    have hED : E ≤ D := le_sup_left
    have hED_eq : E = D := by
      apply Subgroup.eq_of_le_of_card_ge hED
      simpa only [hE.card_eq] using hDle
    have hCBE_E : CBE ≤ E := by
      rw [hED_eq]
      exact le_sup_right
    have hCBEcard : p ^ 2 ≤ Nat.card CBE :=
      Submission.OddOrder.BG.Section04.prime_sq_le_natCard_centralizerWithin
        hB hE
    have hCBEeq : CBE = E := by
      apply Subgroup.eq_of_le_of_card_ge hCBE_E
      simpa only [hE.card_eq] using hCBEcard
    have hEB : E ≤ B := by
      rw [← hCBEeq]
      exact centralizerWithin_le_left B E
    have hB_CBE : B ≤ CBE := by
      intro b hb
      refine ⟨hb, ?_⟩
      intro e he
      letI : IsMulCommutative B := hB.commutative
      exact congrArg Subtype.val
        (mul_comm (⟨e, hEB he⟩ : B) (⟨b, hb⟩ : B))
    have hBCBE : B = CBE :=
      le_antisymm hB_CBE (centralizerWithin_le_left B E)
    have hpows : p ^ 3 = p ^ 2 := by
      rw [← hB.card_eq, hBCBE, hCBEeq, hE.card_eq]
    have : (3 : ℕ) = 2 :=
      Nat.pow_right_injective (Fact.out : p.Prime).two_le hpows
    omega
  obtain ⟨n, hDcardPow⟩ := hDelem.isPGroup.exists_card_eq
  have hpows : p ^ 2 < p ^ n := by simpa only [hDcardPow] using hDcard
  have hn : 3 ≤ n := by
    have : 2 < n :=
      (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpows
    omega
  obtain ⟨F, hFD, _hFnormal, hFcard⟩ :=
    exists_normal_subgroup_card_pow_le hG D hDcardPow hn
  letI : IsMulCommutative D := hDcomm
  have hFcomm : IsMulCommutative F := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val
      (mul_comm (⟨x, hFD x.2⟩ : D) (⟨y, hFD y.2⟩ : D))
  have hFpow : ∀ x : F, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    change (x : G) ^ p = 1
    exact congrArg Subtype.val (hDpow ⟨x, hFD x.2⟩)
  have hF : IsElementaryAbelianOfRank p 3 F :=
    { isPGroup := hG.to_subgroup F
      commutative := hFcomm
      pow_eq_one := hFpow
      card_eq := hFcard }
  obtain ⟨C, hDC, hC⟩ :=
    exists_isSCN_top_containing hG D ⟨hDnormal, hDcomm⟩
  exact ⟨C, ⟨hC, F, hFD.trans hDC, hF⟩, (le_sup_left : E ≤ D).trans hDC⟩

end Submission.OddOrder.BG.Section05
