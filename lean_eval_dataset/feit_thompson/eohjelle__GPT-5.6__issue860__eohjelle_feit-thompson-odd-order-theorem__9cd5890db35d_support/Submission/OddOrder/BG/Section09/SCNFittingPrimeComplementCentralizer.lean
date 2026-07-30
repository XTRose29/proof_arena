import Submission.OddOrder.BG.Section09.NoncyclicCentralizerUniqueness
import Submission.OddOrder.BG.Section09.SCNRankThreeSylowNormalizer
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCocyclicCentralizerGeneration
import Submission.OddOrder.MathlibSupport.RankTwoNormalCentralizer

/-!
# Bender--Glauberman Lemma 9.5: the prime-complement Fitting centralizer

This file ports the `cDP0` block of `BGsection9.v`.  Under the non-uniqueness
hypothesis for a rank-three SCN subgroup, the commutator of a Sylow subgroup
with its normalizer centralizes the mapped `p'`-core of the Fitting subgroup
of every relevant maximal subgroup.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

private theorem isMulCommutative_of_le
    {G : Type u} [Group G] {B C : Subgroup G}
    (hB : IsMulCommutative B) (hCB : C ≤ B) :
    IsMulCommutative C := by
  letI : IsMulCommutative B := hB
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  change (x : G) * (y : G) = (y : G) * (x : G)
  exact congrArg Subtype.val
    (mul_comm (⟨x, hCB x.2⟩ : B) (⟨y, hCB y.2⟩ : B))

private theorem not_isCyclic_of_elementaryAbelian_rank_three
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElementaryAbelianOfRank p 3 E) :
    ¬ IsCyclic E := by
  classical
  intro hcyclic
  letI : IsCyclic E := hcyclic
  letI := Fintype.ofFinite E
  have hle : Nat.card E ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hE.pow_eq_one, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := E) hp.pos)
  have hlt : p < p ^ 3 := by
    simpa using Nat.pow_lt_pow_right hp.one_lt (by omega : 1 < 3)
  exact (not_lt_of_ge (hE.card_eq ▸ hle)) hlt

/-- A cocyclic subgroup of an elementary-abelian group of rank three is
noncyclic. -/
private theorem not_isCyclic_of_rank_three_of_isCyclic_quotient
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {B C : Subgroup G}
    (hB : IsElementaryAbelianOfRank p 3 B) (hCB : C ≤ B)
    (hCnormal : (C.subgroupOf B).Normal)
    (hquotCyclic : IsCyclic (B ⧸ C.subgroupOf B)) :
    ¬ IsCyclic C := by
  classical
  intro hCcyclic
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsCyclic C := hCcyclic
  letI : (C.subgroupOf B).Normal := hCnormal
  letI : IsCyclic (B ⧸ C.subgroupOf B) := hquotCyclic
  have hCpow : ∀ x : C, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    change (x : G) ^ p = 1
    exact congrArg Subtype.val (hB.pow_eq_one (⟨x, hCB x.2⟩ : B))
  have hquotPow : ∀ x : B ⧸ C.subgroupOf B, x ^ p = 1 := by
    intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf B) x
    rw [← map_pow, hB.pow_eq_one, map_one]
  letI := Fintype.ofFinite C
  letI := Fintype.ofFinite (B ⧸ C.subgroupOf B)
  have hCcard : Nat.card C ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hCpow, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := C) hp.pos)
  have hquotCard : Nat.card (B ⧸ C.subgroupOf B) ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hquotPow, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le
        (α := B ⧸ C.subgroupOf B) hp.pos)
  have hfactor : Nat.card B =
      Nat.card (B ⧸ C.subgroupOf B) * Nat.card C := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
      natCard_subgroupOf_eq hCB]
  have hle : p ^ 3 ≤ p ^ 2 := by
    rw [← hB.card_eq, hfactor, pow_two]
    exact Nat.mul_le_mul hquotCard hCcard
  have hlt : p ^ 2 < p ^ 3 :=
    Nat.pow_lt_pow_right hp.one_lt (by omega)
  exact (not_lt_of_ge hle) hlt

/-- `BGsection9.v: cDP0`, the centralizer block in the proof of
Bender--Glauberman Lemma 9.5. -/
theorem sylow_commutator_le_centralizer_fitting_pPrimeCore_of_scn_not_unique
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A : Subgroup G}
    (hSCN : IsSCN (P : Subgroup G) A)
    (hRankA : 3 ≤ Group.rank A)
    (hnotuniq : A ∉ minSimple_uniq_max_groups (G := G)) :
    ∀ {M : Subgroup G}, M ∈ minSimple_max_groups (G := G) →
      Subgroup.centralizer (A : Set G) ≤ M →
      let D := (pPrimeCore p (fittingWithin M)).map
        (fittingWithin M).subtype
      ⁅(P : Subgroup G),
          Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ ≤
        Subgroup.centralizer (D : Set G) := by
  classical
  intro M hM hCAM
  dsimp only
  let F : Subgroup G := fittingWithin M
  let D : Subgroup G := (pPrimeCore p F).map F.subtype
  let P0 : Subgroup G :=
    ⁅(P : Subgroup G),
      Subgroup.normalizer ((P : Subgroup G) : Set G)⁆

  have hAp : IsPGroup p A :=
    IsPGroup.to_le P.isPGroup' hSCN.le_sylow
  obtain ⟨E, hEA, hE⟩ :=
    exists_elementaryAbelian_rank_three_le_of_group_rank
      A hAp hSCN.commutative hRankA
  have hEncyc : ¬ IsCyclic E :=
    not_isCyclic_of_elementaryAbelian_rank_three Fact.out hE

  have hFM : F ≤ M := by
    simpa only [F] using fittingWithin_le M
  have hDF : D ≤ F := by
    dsimp only [D]
    exact Subgroup.map_subtype_le _
  have hDM : D ≤ M := hDF.trans hFM
  have hMDnorm : M ≤ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      F M (pPrimeCore p F) (by
        simpa only [F] using fittingWithin_le_normalizer M)
  have hNPM : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M :=
    normalizer_sylow_le_maximal_of_scn_not_unique
      P hSCN hRankA hnotuniq hM hCAM
  have hPM : (P : Subgroup G) ≤ M :=
    Subgroup.le_normalizer.trans hNPM
  have hAM : A ≤ M := hSCN.le_sylow.trans hPM
  have hEDnorm : E ≤ Subgroup.normalizer (D : Set G) :=
    hEA.trans (hAM.trans hMDnorm)

  have hDcard : Nat.card D = Nat.card (pPrimeCore p F) := by
    dsimp only [D]
    exact Subgroup.card_map_of_injective F.subtype_injective
  have hDprime : Nat.Coprime p (Nat.card D) := by
    rw [hDcard]
    exact pPrimeCore_coprime_card
  have hDEcop : Nat.Coprime (Nat.card D) (Nat.card E) := by
    rw [hE.card_eq]
    exact hDprime.symm.pow_right 3
  have hDsol : IsSolvable D :=
    mFT_sol (lt_of_le_of_lt hDM (mmax_proper hM))

  have hP0P : P0 ≤ (P : Subgroup G) := by
    dsimp only [P0]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp le_rfl
  have hP0p : IsPGroup p P0 :=
    IsPGroup.to_le P.isPGroup' hP0P

  apply Subgroup.le_centralizer_iff.mp
  apply le_of_centralizerWithin_cocyclic_le_of_coprime_abelian_solvable
    hE.commutative hEncyc hEDnorm hDEcop hDsol
  intro C hCE hCnormal hECcyclic
  have hCncyc : ¬ IsCyclic C :=
    not_isCyclic_of_rank_three_of_isCyclic_quotient
      Fact.out hE hCE hCnormal hECcyclic
  have hCelem : IsPElementaryIn p M C := by
    refine ⟨hCE.trans (hEA.trans hAM), ?_⟩
    refine
      { isPGroup := IsPGroup.to_le hE.isPGroup hCE
        commutative := isMulCommutative_of_le hE.commutative hCE
        pow_eq_one := ?_ }
    intro c
    apply Subtype.ext
    change (c : G) ^ p = 1
    exact congrArg Subtype.val
      (hE.pow_eq_one (⟨c, hCE c.2⟩ : E))

  obtain ⟨x, hxC, hxne, hxnotM⟩ :
      ∃ x : G, x ∈ C ∧ x ≠ 1 ∧
        ¬ Subgroup.centralizer ({x} : Set G) ≤ M := by
    by_contra hnone
    have hall : ∀ x : G, x ∈ C → x ≠ 1 →
        Subgroup.centralizer ({x} : Set G) ≤ M := by
      intro x hxC hxne
      by_contra hxnot
      exact hnone ⟨x, hxC, hxne, hxnot⟩
    have hCuniq : C ∈ minSimple_uniq_max_groups (G := G) :=
      noncyclic_cent1_sub_Uniqueness hM hCelem hCncyc hall
    exact hnotuniq
      (uniq_mmaxS (hCE.trans hEA) (mFT_pgroup_proper A hAp) hCuniq)

  obtain ⟨L, hL, hCxL⟩ :=
    mmax_exists (Subgroup.centralizer ({x} : Set G))
      (mFT_cent1_proper hxne)
  have hLM : L ≠ M := by
    intro hEq
    apply hxnotM
    simpa only [hEq] using hCxL
  have hxA : x ∈ A := hEA (hCE hxC)
  have hCAL : Subgroup.centralizer (A : Set G) ≤ L := by
    refine (Subgroup.centralizer_le ?_).trans hCxL
    exact Set.singleton_subset_iff.mpr hxA
  have hNPL : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ L :=
    normalizer_sylow_le_maximal_of_scn_not_unique
      P hSCN hRankA hnotuniq hL hCAL

  let H : Subgroup G := L ⊓ M
  have hNPH : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ H := by
    exact le_inf hNPL hNPM
  have hPH : (P : Subgroup G) ≤ H :=
    Subgroup.le_normalizer.trans hNPH
  have hP0H : P0 ≤ H := hP0P.trans hPH
  let P0H : Subgroup H := P0.subgroupOf H
  have hP0Hder : P0H ≤ _root_.commutator H := by
    have hmapped : P0H.map H.subtype ≤
        (_root_.commutator H).map H.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le hP0H,
        H.map_subtype_commutator]
      exact Subgroup.commutator_mono hPH hNPH
    exact (Subgroup.map_le_map_iff_of_injective
      H.subtype_injective).mp hmapped

  let DL : Subgroup G := L ⊓ D
  have hDLH : DL ≤ H := by
    dsimp only [DL, H]
    exact le_inf inf_le_left (inf_le_right.trans hDM)
  let DLH : Subgroup H := DL.subgroupOf H
  have hDnormalM : (D.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hMDnorm
  letI : (D.subgroupOf M).Normal := hDnormalM
  have hDLHnormal : DLH.Normal := by
    dsimp only [DLH, DL, H]
    exact Subgroup.inf_subgroupOf_inf_normal_of_right L D M

  have hDLHrank : ∀ q : ℕ, q.Prime →
      ¬ ∃ Q : Subgroup DLH, IsElementaryAbelianOfRank q 3 Q := by
    intro q hq
    rintro ⟨Q, hQ⟩
    let QH : Subgroup H := Q.map DLH.subtype
    let QG : Subgroup G := QH.map H.subtype
    have hQH : IsElementaryAbelianOfRank q 3 QH := by
      dsimp only [QH]
      exact hQ.map_of_injective DLH.subtype DLH.subtype_injective
    have hQG : IsElementaryAbelianOfRank q 3 QG := by
      dsimp only [QG]
      exact hQH.map_of_injective H.subtype H.subtype_injective
    have hQHDLH : QH ≤ DLH := by
      dsimp only [QH]
      exact Subgroup.map_subtype_le Q
    have hQGDL : QG ≤ DL := by
      dsimp only [QG]
      rw [← Subgroup.map_subgroupOf_eq_of_le hDLH]
      exact Subgroup.map_mono hQHDLH
    have hQGL : QG ≤ L := hQGDL.trans inf_le_left
    have hQGF : QG ≤ F := hQGDL.trans (inf_le_right.trans hDF)
    have hQGM : QG ≤ M := hQGF.trans hFM
    letI : Fact q.Prime := ⟨hq⟩
    have hQGuniq : QG ∈ minSimple_uniq_max_groups (G := G) :=
      any_rank3_Fitting_Uniqueness hM ⟨QG, hQGF, hQG⟩
        hQG.isPGroup ⟨QG, le_rfl, hQG⟩
    have hQGdef :
        minSimple_max_groups_of (G := G) (QG : Set G) = {M} :=
      def_uniq_mmax hQGuniq hM hQGM
    exact hLM (eq_uniq_mmax hQGdef hL hQGL)

  have hP0Hp : IsPGroup p P0H :=
    hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe hP0H).symm
  have hDLHprime : Nat.Coprime p (Nat.card DLH) := by
    rw [natCard_subgroupOf_eq hDLH]
    exact hDprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨n, hP0Hcard⟩ := hP0Hp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card DLH) (Nat.card P0H) := by
    rw [hP0Hcard]
    exact hDLHprime.symm.pow_right n
  have hP0Hcent : P0H ≤ Subgroup.centralizer (DLH : Set H) :=
    le_centralizer_of_le_commutator_of_no_rank_three
      (mFT_odd H)
      (mFT_sol (lt_of_le_of_lt (show H ≤ L by exact inf_le_left)
        (mmax_proper hL)))
      hDLHnormal hDLHrank hP0Hder hcop
  have hP0centDL : P0 ≤ Subgroup.centralizer (DL : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    let zH : H := ⟨z, hP0H hz⟩
    let dH : H := ⟨d, hDLH hd⟩
    have hzH : zH ∈ P0H := hz
    have hdH : dH ∈ DLH := hd
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (hP0Hcent hzH) dH hdH)

  have hCDL : centralizerWithin D C ≤ DL := by
    apply le_inf
    · calc
        centralizerWithin D C ≤
            Subgroup.centralizer (C : Set G) := inf_le_right
        _ ≤ Subgroup.centralizer ({x} : Set G) := by
          apply Subgroup.centralizer_le
          exact Set.singleton_subset_iff.mpr hxC
        _ ≤ L := hCxL
    · exact centralizerWithin_le_left D C
  apply Subgroup.le_centralizer_iff.mp
  exact hP0centDL.trans (Subgroup.centralizer_le hCDL)

end Submission.OddOrder.BG.Section09
