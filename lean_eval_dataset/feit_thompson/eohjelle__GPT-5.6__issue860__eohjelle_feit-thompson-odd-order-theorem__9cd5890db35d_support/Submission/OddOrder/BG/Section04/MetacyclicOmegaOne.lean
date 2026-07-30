import Submission.OddOrder.BG.Section04.ExponentOmegaOneRankTwo
import Submission.OddOrder.BG.Section04.OddPGroupRankOne
import Submission.OddOrder.MathlibSupport.Metacyclic
import Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal

/-!
Bender--Glauberman Lemma 4.10.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection4.v: Ohm1_metacyclic_p2Elem` (Bender--Glauberman Lemma
4.10).  A finite odd noncyclic metacyclic `p`-group has elementary-abelian
first omega subgroup of rank two. -/
theorem omegaOne_isElementaryAbelian_rank_two_of_isMetacyclic
    (hmeta : IsMetacyclic G)
    (hG : IsPGroup p G)
    (hodd : Odd (Nat.card G))
    (hnotcyclic : ¬ IsCyclic G) :
    IsElementaryAbelianOfRank p 2 (omegaOne p G) := by
  classical
  rcases hmeta with ⟨S, hSnormal, hScyclic, hQcyclic⟩
  letI : S.Normal := hSnormal
  letI : IsCyclic S := hScyclic
  letI : IsCyclic (G ⧸ S) := hQcyclic
  let q : G →* G ⧸ S := QuotientGroup.mk' S
  have hQp : IsPGroup p (G ⧸ S) := hG.to_quotient S
  have hQneOne : Nat.card (G ⧸ S) ≠ 1 := by
    intro hQcard
    letI : Subsingleton (G ⧸ S) :=
      (Nat.card_eq_one_iff_unique.mp hQcard).1
    have hStop : S = ⊤ :=
      QuotientGroup.subgroup_eq_top_of_subsingleton S inferInstance
    apply hnotcyclic
    have htopCyclic : IsCyclic (⊤ : Subgroup G) :=
      hStop ▸ hScyclic
    exact Subgroup.topEquiv.isCyclic.mp htopCyclic
  have hOmegaQCard : Nat.card (omegaOne p (G ⧸ S)) = p :=
    card_omegaOne_of_isCyclic_isPGroup Fact.out hQp hQneOne
  let T : Subgroup G := (omegaOne p (G ⧸ S)).comap q
  letI : T.Normal := by
    dsimp [T]
    infer_instance
  have hST : S ≤ T := by
    intro x hx
    change q x ∈ omegaOne p (G ⧸ S)
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hqx]
    exact (omegaOne p (G ⧸ S)).one_mem
  let ST : Subgroup T := S.subgroupOf T
  letI : ST.Normal := by
    dsimp [ST]
    infer_instance
  have hTmap : T.map q = omegaOne p (G ⧸ S) := by
    dsimp [T, q]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective S) (omegaOne p (G ⧸ S))
  let eT : T ⧸ ST ≃* omegaOne p (G ⧸ S) :=
    (QuotientGroup.liftEquiv ST (q.subgroupMap_surjective T) (by
      dsimp [ST, q]
      rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])).trans
      (MulEquiv.subgroupCongr hTmap)
  have hTquotientCard : Nat.card (T ⧸ ST) = p := by
    calc
      Nat.card (T ⧸ ST) = Nat.card (omegaOne p (G ⧸ S)) :=
        Nat.card_congr eT.toEquiv
      _ = p := hOmegaQCard
  obtain ⟨s, hs⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hScyclic
  let sT : T := ⟨s, hST s.property⟩
  have hzpowers : Subgroup.zpowers sT = ST := by
    apply le_antisymm
    · apply Subgroup.zpowers_le.mpr
      exact s.property
    · intro x hx
      let xS : S := ⟨x, hx⟩
      have hxgen : xS ∈ Subgroup.zpowers s := by
        rw [hs]
        trivial
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hxgen
      apply Subgroup.mem_zpowers_iff.mpr
      refine ⟨z, ?_⟩
      apply Subtype.ext
      exact congrArg (fun y : S ↦ (y : G)) hz
  have hindex : (Subgroup.zpowers sT).index = p := by
    rw [hzpowers, Subgroup.index_eq_card]
    exact hTquotientCard
  let W : Subgroup G := (omegaOne p T).map T.subtype
  have hWG : W ≤ omegaOne p G := by
    dsimp [W]
    exact map_omegaOne_le p T.subtype
  have hGW : omegaOne p G ≤ W := by
    apply omegaOne_le p W
    intro x hx
    have hxT : x ∈ T := by
      change q x ∈ omegaOne p (G ⧸ S)
      apply mem_omegaOne_of_pow_eq_one p
      simpa only [map_pow, map_one] using congrArg q hx
    let xT : T := ⟨x, hxT⟩
    have hxTpow : xT ^ p = 1 := by
      apply Subtype.ext
      exact hx
    exact ⟨xT, mem_omegaOne_of_pow_eq_one p hxTpow, rfl⟩
  have hOmegaEq : W = omegaOne p G := le_antisymm hWG hGW
  have hTp : IsPGroup p T := hG.to_subgroup T
  have hTodd : Odd (Nat.card T) :=
    hodd.of_dvd_nat T.card_subgroup_dvd_card
  have hTneOne : Nat.card T ≠ 1 := by
    have hpDvdT : p ∣ Nat.card T := by
      have hfactor := Subgroup.card_eq_card_quotient_mul_card_subgroup ST
      rw [hTquotientCard] at hfactor
      refine ⟨Nat.card ST, ?_⟩
      rw [hfactor]
    intro hTcard
    rw [hTcard] at hpDvdT
    exact (Fact.out : p.Prime).not_dvd_one hpDvdT
  have hTnotcyclic : ¬ IsCyclic T := by
    intro hTcyclic
    letI : IsCyclic T := hTcyclic
    have hOmegaTCard : Nat.card (omegaOne p T) = p :=
      card_omegaOne_of_isCyclic_isPGroup Fact.out hTp hTneOne
    have hWCard : Nat.card W = p := by
      calc
        Nat.card W = Nat.card (omegaOne p T) := by
          dsimp [W]
          exact Subgroup.card_map_of_injective T.subtype_injective
        _ = p := hOmegaTCard
    have hOmegaGCard : Nat.card (omegaOne p G) = p := by
      rw [← hOmegaEq]
      exact hWCard
    have hnoRankTwo :
        ¬ ∃ E : Subgroup G, IsElementaryAbelianOfRank p 2 E := by
      rintro ⟨E, hE⟩
      have hEOmega : E ≤ omegaOne p G := by
        intro x hx
        exact mem_omegaOne_of_pow_eq_one p (by
          simpa using congrArg Subtype.val (hE.pow_eq_one ⟨x, hx⟩))
      have hcardE := Subgroup.card_le_of_le hEOmega
      rw [hE.card_eq, hOmegaGCard] at hcardE
      have hpLtSq : p < p ^ 2 := by
        rw [pow_two]
        exact lt_mul_of_one_lt_right
          (Fact.out : p.Prime).pos (Fact.out : p.Prime).one_lt
      exact (not_le_of_gt hpLtSq) hcardE
    exact hnotcyclic
      ((odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two hG hodd).mpr
        hnoRankTwo)
  have hElemT : IsElementaryAbelianOfRank p 2 (omegaOne p T) :=
    omegaOne_isElementaryAbelian_rank_two_of_cyclic_subgroup_index_prime
      hTp hTodd hTnotcyclic sT hindex
  have hElemW : IsElementaryAbelianOfRank p 2 W := by
    dsimp [W]
    exact isElementaryAbelianOfRank_map_of_injective hElemT T.subtype
      T.subtype_injective
  rw [← hOmegaEq]
  exact hElemW

end

end Submission.OddOrder.BG.Section04
