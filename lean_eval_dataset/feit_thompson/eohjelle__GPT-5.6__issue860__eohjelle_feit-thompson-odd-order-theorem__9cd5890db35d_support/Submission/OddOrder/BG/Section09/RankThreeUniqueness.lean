import Submission.OddOrder.BG.Section08.FittingRankThreeSCN
import Submission.OddOrder.BG.Section09.AnyCentralizerRankThreeUniqueness
import Submission.OddOrder.BG.Section09.SCNRankThreeUniqueness
import Submission.OddOrder.MathlibSupport.AbelianPGroupRankThreeConverse
import Submission.OddOrder.MathlibSupport.PMaxElemExistence

/-!
# Bender--Glauberman Theorem 9.6

The three final consequences of the Section 9 uniqueness theorem.  As in
the rest of this port, MathComp's numerical finite-group rank hypotheses are
stated directly as the existence of elementary-abelian subgroups of the
corresponding cardinal rank.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section08
open Submission.OddOrder.MathlibSupport

universe u

private theorem not_isCyclic_of_elementaryAbelian_rank_three
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElementaryAbelianOfRank p 3 E) :
    ¬ IsCyclic E := by
  intro hcyclic
  letI : IsCyclic E := hcyclic
  letI := Fintype.ofFinite E
  classical
  have hle : Nat.card E ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hE.pow_eq_one, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le
        (α := E) (Fact.out : p.Prime).pos)
  have hlt : p < p ^ 3 := by
    simpa using
      (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt
        (by omega : (1 : ℕ) < 3))
  exact (not_lt_of_ge (hE.card_eq ▸ hle)) hlt

/-- `BGsection9.v: rank3_Uniqueness` (Theorem 9.6, first assertion).

The existential elementary-abelian hypothesis is the proposition-valued
form of MathComp's numerical condition `'r(K) >= 3`. -/
theorem rank3_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {K : Subgroup G}
    (hKproper : K < ⊤)
    (hRank3 : ∃ p : ℕ, p.Prime ∧
      HasElementaryAbelianRankAtLeast p 3 K) :
    K ∈ minSimple_uniq_max_groups (G := G) := by
  classical
  rcases hRank3 with ⟨p, hp, B, hBK, hB⟩
  letI : Fact p.Prime := ⟨hp⟩

  have hBp : IsPGroup p B := hB.isPGroup
  obtain ⟨P, hBP⟩ := hBp.exists_le_sylow
  have hRankP : HasElementaryAbelianRankAtLeast p 3
      (P : Subgroup G) :=
    ⟨B, hBP, hB⟩
  obtain ⟨A, hSCNA, hRankA⟩ :=
    exists_scn_rank_three_of_hasElementaryAbelianRankAtLeast
      (P : Subgroup G) P.isPGroup' (mFT_odd (P : Subgroup G)) hRankP

  have hAp : IsPGroup p A :=
    IsPGroup.to_le P.isPGroup' hSCNA.le_sylow
  have hAcomm : IsMulCommutative A := hSCNA.commutative
  have hGroupRankA : 3 ≤ Group.rank A :=
    group_rank_ge_three_of_exists_elementaryAbelian_rank_three_le
      A hAp hAcomm hRankA
  have hAuniq : A ∈ minSimple_uniq_max_groups (G := G) :=
    SCN_3_Uniqueness ⟨P, hSCNA, hGroupRankA⟩

  have hBcentral : B ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hB.commutative
  have hRankCB : HasElementaryAbelianRankAtLeast p 3
      (Subgroup.centralizer (B : Set G)) :=
    ⟨B, hBcentral, hB⟩
  have hBuniq : B ∈ minSimple_uniq_max_groups (G := G) :=
    any_cent_rank3_Uniqueness hAcomm hAp hRankA hAuniq hBp
      (not_isCyclic_of_elementaryAbelian_rank_three hB) hRankCB
  exact uniq_mmaxS hBK hKproper hBuniq

/-- `BGsection9.v: cent_rank3_Uniqueness`
(Theorem 9.6, second assertion). -/
theorem cent_rank3_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {K : Subgroup G}
    (hRankK : ∃ p : ℕ, p.Prime ∧
      HasElementaryAbelianRankAtLeast p 2 K)
    (hRankC : ∃ p : ℕ, p.Prime ∧
      HasElementaryAbelianRankAtLeast p 3
        (Subgroup.centralizer (K : Set G))) :
    K ∈ minSimple_uniq_max_groups (G := G) := by
  have hKne : K ≠ ⊥ := by
    obtain ⟨p, hp, E, hEK, hE⟩ := hRankK
    letI : Fact p.Prime := ⟨hp⟩
    intro hKbot
    rw [hKbot] at hEK
    exact hE.ne_bot (eq_bot_iff.mpr hEK)
  have hCproper : Subgroup.centralizer (K : Set G) < ⊤ :=
    mFT_cent_proper K hKne
  have hCuniq : Subgroup.centralizer (K : Set G) ∈
      minSimple_uniq_max_groups (G := G) :=
    rank3_Uniqueness hCproper hRankC
  have hKcentralC :
      K ≤ Subgroup.centralizer
        (Subgroup.centralizer (K : Set G) : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    exact le_rfl
  exact cent_uniq_Uniqueness hCuniq hKcentralC hRankK

private theorem exists_elementaryAbelian_rank_three_of_lt
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A E : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hE : IsElementaryAbelianGroup p E)
    (hAE : A < E) :
    ∃ F : Subgroup G,
      F ≤ E ∧ IsElementaryAbelianOfRank p 3 F := by
  obtain ⟨n, hEcard⟩ := hE.isPGroup.exists_card_eq
  have hpowlt : p ^ 2 < p ^ n := by
    simpa only [hA.card_eq, hEcard] using
      natCard_subgroup_lt_of_lt hAE
  have hn : 3 ≤ n := by
    by_contra hnot
    have hnle : n ≤ 2 := by omega
    exact (not_lt_of_ge
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnle)) hpowlt
  have hpThreeLe : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn
  obtain ⟨F₀, hF₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card
      (G := E) (Fact.out : p.Prime) hE.isPGroup hpThreeLe
  have hF₀ : IsElementaryAbelianOfRank p 3 F₀ := by
    letI : IsMulCommutative E := hE.commutative
    refine
      { isPGroup := hE.isPGroup.to_subgroup F₀
        commutative := by infer_instance
        pow_eq_one := ?_
        card_eq := hF₀card }
    intro x
    apply Subtype.ext
    exact hE.pow_eq_one (x : E)
  let F : Subgroup G := F₀.map E.subtype
  exact ⟨F, Subgroup.map_subtype_le F₀,
    hF₀.map_of_injective E.subtype E.subtype_injective⟩

/-- `BGsection9.v: nonmaxElem2_Uniqueness`
(Theorem 9.6, final observation). -/
theorem nonmaxElem2_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hA_not_max : ¬ IsPMaxElem p (⊤ : Subgroup G) A) :
    A ∈ minSimple_uniq_max_groups (G := G) := by
  obtain ⟨E, hEmax, hAE⟩ :=
    exists_isPMaxElem_ge
      (⟨le_top, hA.toIsElementaryAbelianGroup⟩ :
        IsPElementaryIn p (⊤ : Subgroup G) A)
  have hAneE : A ≠ E := by
    intro hAEeq
    apply hA_not_max
    simpa [hAEeq] using hEmax
  have hAEproper : A < E := lt_of_le_of_ne hAE hAneE
  obtain ⟨F, hFE, hF⟩ :=
    exists_elementaryAbelian_rank_three_of_lt
      hA hEmax.elementary hAEproper

  have hEcentralA : E ≤ Subgroup.centralizer (A : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    exact hAE.trans
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        hEmax.elementary.commutative)
  have hRankA : ∃ q : ℕ, q.Prime ∧
      HasElementaryAbelianRankAtLeast q 2 A :=
    ⟨p, Fact.out, A, le_rfl, hA⟩
  have hRankC : ∃ q : ℕ, q.Prime ∧
      HasElementaryAbelianRankAtLeast q 3
        (Subgroup.centralizer (A : Set G)) :=
    ⟨p, Fact.out, F, hFE.trans hEcentralA, hF⟩
  exact cent_rank3_Uniqueness hRankA hRankC

end Submission.OddOrder.BG.Section09
