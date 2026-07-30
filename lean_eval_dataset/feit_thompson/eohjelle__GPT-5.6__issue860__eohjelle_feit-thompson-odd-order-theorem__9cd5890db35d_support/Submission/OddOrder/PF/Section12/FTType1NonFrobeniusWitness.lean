import Submission.OddOrder.PF.Section12.FTType1Coherence
import Submission.OddOrder.PF.Section08.FTSupportPartition
import Submission.OddOrder.MathlibSupport.AbelianPGroupRankThreeConverse
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable
import Submission.OddOrder.MathlibSupport.SolvableHallContainment
import Submission.OddOrder.MathlibSupport.OmegaOne
import Mathlib.Tactic

/-!
# Peterfalvi (12.9): the non-Frobenius type-I witness

This phase constructs the rank-two witness used by the non-Frobenius
contradiction in Peterfalvi Section 12.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-- The expanded form of the source assertion that the `p`-rank is exactly
two. -/
def HasPRankExactlyTwo12 (p : ℕ) (P : Subgroup G) : Prop :=
  HasElementaryAbelianRankAtLeast p 2 P ∧
    ¬ HasElementaryAbelianRankAtLeast p 3 P

/-- The hypotheses fixed before Peterfalvi (12.9). -/
structure FTType1NonFrobeniusContext
    (p : ℕ) (M P0 : Subgroup G) : Prop where
  p_prime : p.Prime
  inductive_hypothesis :
    ∀ {q : ℕ} {N : Subgroup G},
      q.Prime → q < p →
        N ∈ minSimple_max_groups (G := G) →
          FTtype N = 1 →
            HasElementaryAbelianRankAtLeast q 2 N →
              q ∈ primeSupport (Nat.card (Fitting_core N))
  M_type_context : FTType1Context M
  p_rank_gt_one : HasElementaryAbelianRankAtLeast p 2 M
  core_p_prime : IsPPrimeSubgroup p (Fitting_core M)
  sylow_P0 : IsSylowSubgroupOf p P0 M

/-- The data extracted in Peterfalvi (12.9). -/
structure NonFrobeniusFTType1Witness
    (p : ℕ) (M P0 : Subgroup G) : Type where
  P0_abelian : IsMulCommutative P0
  P0_rank_two : HasPRankExactlyTwo12 p P0
  L : Subgroup G
  L_maximal : L ∈ minSimple_max_groups (G := G)
  P0_le_FTcore : P0 ≤ FTcore L
  x : G
  x_mem_omega : x ∈ (omegaOne p P0).map P0.subtype
  x_ne_one : x ≠ 1
  core_centralizer_not_le_derived :
    ¬ centralizerWithin (Fitting_core M) (Subgroup.zpowers x) ≤
        derivedWithin (Fitting_core M)
  normalizer_le_M :
    Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ M
  centralizer_not_le_L : ¬ centralizerOfElement8 x ≤ L

/-- Move an elementary abelian subgroup witnessing ambient rank into a fixed
Sylow subgroup. -/
private theorem elementaryAbelian_le_fixed_sylow12
    {p n : ℕ} [Fact p.Prime] {P M : Subgroup G}
    (hP : IsSylowSubgroupOf p P M)
    (hRank : HasElementaryAbelianRankAtLeast p n M) :
    ∃ E : Subgroup G, E ≤ P ∧ IsElementaryAbelianOfRank p n E := by
  classical
  obtain ⟨PM, rfl⟩ := hP
  obtain ⟨A, hA_le_M, hA⟩ := hRank
  let AM : Subgroup M := A.subgroupOf M
  have hAMrank : IsElementaryAbelianOfRank p n AM :=
    hA.subgroupOf hA_le_M
  obtain ⟨Q, hAQ⟩ := hAMrank.isPGroup.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M Q PM
  let B : Subgroup M := AM.map (MulAut.conj m).toMonoidHom
  have hQmap :
      (Q : Subgroup M).map (MulAut.conj m).toMonoidHom =
        (PM : Subgroup M) := by
    change MulAut.conj m • (Q : Subgroup M) = (PM : Subgroup M)
    rw [← Sylow.coe_subgroup_smul, hm]
  have hBPM : B ≤ (PM : Subgroup M) :=
    (Subgroup.map_mono hAQ).trans_eq hQmap
  have hB : IsElementaryAbelianOfRank p n B :=
    hAMrank.map_of_injective (MulAut.conj m).toMonoidHom
      (MulAut.conj m).injective
  let E : Subgroup G := B.map M.subtype
  exact ⟨E, Subgroup.map_mono hBPM,
    hB.map_of_injective M.subtype M.subtype_injective⟩

/-- A nontrivial finite solvable group properly contains its derived subgroup,
written in the ambient-group representation used by the PF files. -/
private theorem derivedWithin_strict_of_solvable12
    (K : Subgroup G) (hK : K ≠ ⊥) (hsol : IsSolvable K) :
    derivedWithin K < K := by
  letI : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hK
  let D : Subgroup K := _root_.commutator K
  have hD : D < (⊤ : Subgroup K) := by
    letI : IsSolvable K := hsol
    simpa only [D] using
      (IsSolvable.commutator_lt_top_of_nontrivial K)
  have hmap :=
    (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).2 hD
  simpa only [derivedWithin, D, ← MonoidHom.range_eq_map,
    K.range_subtype] using hmap

/-- `PFsection12.v: non_Frobenius_FTtype1_witness`, Peterfalvi (12.9). -/
theorem non_Frobenius_FTtype1_witness
    {p : ℕ} {M P0 : Subgroup G}
    (ctx : FTType1NonFrobeniusContext p M P0) :
    Nonempty (NonFrobeniusFTType1Witness p M P0) := by
  classical
  let K := Fitting_core M
  letI : Fact p.Prime := ⟨ctx.p_prime⟩

  have hP0M : P0 ≤ M := by
    obtain ⟨PM, hPM⟩ := ctx.sylow_P0
    rw [hPM]
    exact Subgroup.map_subtype_le (PM : Subgroup M)
  have hP0p : IsPGroup p P0 := ctx.sylow_P0.isPGroup
  obtain ⟨a, hP0card⟩ := hP0p.exists_card_eq
  have hKP0cop : Nat.Coprime (Nat.card K) (Nat.card P0) := by
    rw [hP0card]
    exact ctx.core_p_prime.symm.pow_right a

  obtain ⟨E, hEP0, hE⟩ :=
    elementaryAbelian_le_fixed_sylow12
      ctx.sylow_P0 ctx.p_rank_gt_one

  /- Put `P0` inside a complement to the Fitting core, so the type-I facts
  apply directly to a Sylow subgroup represented by `P0`. -/
  let KM : Subgroup M := K.subgroupOf M
  let P0M : Subgroup M := P0.subgroupOf M
  have hKMnormal : KM.Normal := by
    dsimp only [KM, K]
    infer_instance
  letI : KM.Normal := hKMnormal
  have hKMcard : Nat.card KM = Nat.card K :=
    natCard_subgroupOf_eq (Fcore_sub M)
  have hP0Mcard : Nat.card P0M = Nat.card P0 :=
    natCard_subgroupOf_eq hP0M
  have hKHall : Nat.Coprime (Nat.card KM) KM.index := by
    simpa only [KM, K] using (Fcore_Hall M).coprime_card_index
  have hKM_P0M : Nat.Coprime (Nat.card KM) (Nat.card P0M) := by
    simpa only [hKMcard, hP0Mcard] using hKP0cop
  letI : IsSolvable M := mmax_sol ctx.M_type_context.maxL
  obtain ⟨C, hKC, hP0C⟩ :=
    exists_right_complement_ge_of_coprime hKHall hKM_P0M
  let U : Subgroup G := C.map M.subtype
  have hUM : U ≤ M := Subgroup.map_subtype_le C
  have hP0U : P0 ≤ U := by
    intro z hz
    exact ⟨⟨z, hP0M hz⟩, hP0C hz, rfl⟩
  have hUsubM : U.subgroupOf M = C := by
    change (C.map M.subtype).comap M.subtype = C
    exact Subgroup.comap_map_eq_self_of_injective
      M.subtype_injective C
  have hsdM : IsInternalSemidirectProductIn K U M := by
    refine ⟨Fcore_sub M, hUM, ?_, ?_⟩
    · infer_instance
    · simpa only [KM, hUsubM] using hKC

  obtain ⟨PM, hPM⟩ := ctx.sylow_P0
  have hP0subM : P0.subgroupOf M = (PM : Subgroup M) := by
    rw [hPM]
    exact Subgroup.comap_map_eq_self_of_injective
      M.subtype_injective (PM : Subgroup M)
  have hpP0indexM : ¬ p ∣ P0.relIndex M := by
    change ¬ p ∣ (P0.subgroupOf M).index
    rw [hP0subM]
    exact PM.not_dvd_index
  have hpP0indexU : ¬ p ∣ P0.relIndex U := by
    intro hp
    apply hpP0indexM
    rw [← P0.relIndex_mul_relIndex U M hP0U hUM]
    exact hp.trans (dvd_mul_right _ _)
  have hP0Up : IsPGroup p (P0.subgroupOf U) :=
    hP0p.comap_subtype
  let PU : Sylow p U := hP0Up.toSylow hpP0indexU
  have htypeFacts :=
    FTtypeI_II_facts 1 M U ctx.M_type_context.maxL
      ctx.M_type_context.type_one (by
        simpa [derivedSeriesWithin8, ← MonoidHom.range_eq_map,
          M.range_subtype] using hsdM)
      (by omega : 0 < 1 ∧ 1 ≤ 2)
  obtain ⟨hPUcomm, hPUrank⟩ :=
    htypeFacts.sylow_abelian_rank_le_two p PU
  have hPU : (PU : Subgroup U) = P0.subgroupOf U := rfl
  rw [hPU] at hPUcomm hPUrank
  let eP0 : P0.subgroupOf U ≃* P0 :=
    Subgroup.subgroupOfEquivOfLe hP0U
  have hP0comm : IsMulCommutative P0 := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply eP0.symm.injective
    exact isMulCommutative_iff.mp hPUcomm (eP0.symm x) (eP0.symm y)
  have hP0rankLe : Group.rank P0 ≤ 2 := by
    rw [Group.rank_congr eP0.symm]
    exact hPUrank
  have hNoRankThree :
      ¬ HasElementaryAbelianRankAtLeast p 3 P0 := by
    rintro ⟨A, hAP0, hA⟩
    have hrankThree : 3 ≤ Group.rank P0 :=
      group_rank_ge_three_of_exists_elementaryAbelian_rank_three_le
        P0 hP0p hP0comm ⟨A, hAP0, hA⟩
    omega
  have hP0rankTwo : HasPRankExactlyTwo12 p P0 :=
    ⟨⟨E, hEP0, hE⟩, hNoRankThree⟩

  /- Select a maximal subgroup whose FT-core contains a conjugate of a
  Sylow `p`-subgroup, then conjugate it back so that it contains `P0`. -/
  have hpG : p ∈ primeSupport (Nat.card G) := by
    refine ⟨ctx.p_prime, ?_⟩
    have hpE : p ∣ Nat.card E := by
      rw [hE.card_eq]
      exact dvd_pow_self p (by omega : 2 ≠ 0)
    exact hpE.trans E.card_subgroup_dvd_card
  have hsupportPartition := FT_Dade_support_partition (G := G)
  rw [hsupportPartition.1] at hpG
  obtain ⟨L0, hL0max, hpL0core⟩ := hpG
  let Core0 := FTcore L0
  let S0 : Sylow p Core0 := Sylow.nonempty.some
  let Q0 : Subgroup G := (S0 : Subgroup Core0).map Core0.subtype
  have hQ0p : IsPGroup p Q0 := S0.isPGroup'.map Core0.subtype
  have hpCore0index : ¬ p ∣ Core0.index := by
    intro hp
    exact (FTcore_facts L0 hL0max).ftCore_hall_G.isPiNumber_index
      ctx.p_prime hp hpL0core
  have hpQ0index : ¬ p ∣ Q0.index := by
    dsimp only [Q0]
    rw [Subgroup.index_map_subtype]
    exact ctx.p_prime.not_dvd_mul S0.not_dvd_index hpCore0index
  let QG : Sylow p G := hQ0p.toSylow hpQ0index
  obtain ⟨PG, hP0PG⟩ := hP0p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PG QG
  have hconjP0Q0 : ∀ z : G, z ∈ P0 → g * z * g⁻¹ ∈ Q0 := by
    intro z hz
    have hz : (MulAut.conj g) z ∈ (g • PG : Sylow p G) :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (hP0PG hz)
    rw [hg] at hz
    exact hz
  let L := conjugateSubgroup8 L0 g⁻¹
  have hLmax : L ∈ minSimple_max_groups (G := G) :=
    (mmaxJ L0 (MulAut.conj g⁻¹)).2 hL0max
  have hFTcoreL :
      FTcore L = conjugateSubgroup8 (FTcore L0) g⁻¹ := by
    simpa only [L, conjugateSubgroup8, conjugateSubgroup16] using
      FTcoreJ L0 g⁻¹
  have hP0core : P0 ≤ FTcore L := by
    rw [hFTcoreL]
    intro z hz
    refine ⟨g * z * g⁻¹, ?_, ?_⟩
    · exact (Subgroup.map_subtype_le (S0 : Subgroup Core0))
        (hconjP0Q0 z hz)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

  /- The rank-two elementary abelian subgroup cannot have all of its
  nonidentity centralizers trapped in the derived core. -/
  have hKne : K ≠ ⊥ := by
    simpa only [K] using mmax_Fcore_neq1 ctx.M_type_context.maxL
  have hKsol : IsSolvable K := by
    letI : Group.IsNilpotent K := Fcore_nil M
    infer_instance
  have hKder : derivedWithin K < K :=
    derivedWithin_strict_of_solvable12 K hKne hKsol
  have hEnormK : E ≤ Subgroup.normalizer (K : Set G) :=
    (hEP0.trans hP0M).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M))
  have hKEcop : Nat.Coprime (Nat.card K) (Nat.card E) := by
    rw [hE.card_eq]
    exact ctx.core_p_prime.symm.pow_right 2
  have hex : ∃ x : G, x ∈ E ∧ x ≠ 1 ∧
      ¬ centralizerWithin K (Subgroup.zpowers x) ≤ derivedWithin K := by
    by_contra hall
    push_neg at hall
    have hgenerated : K ≤ derivedWithin K :=
      le_of_centralizerWithin_zpowers_le_of_coprime_abelian_solvable
        hE.commutative (hE.not_isCyclic ctx.p_prime) hEnormK hKEcop
        hKsol hall
    exact (not_le_of_gt hKder) hgenerated
  obtain ⟨x, hxE, hx1, hxcent⟩ := hex
  have hxP0 : x ∈ P0 := hEP0 hxE
  have hxOmega : x ∈ (omegaOne p P0).map P0.subtype := by
    refine ⟨⟨x, hxP0⟩, ?_, rfl⟩
    apply mem_omegaOne_of_pow_eq_one p
    apply Subtype.ext
    change x ^ p = 1
    exact congrArg (fun y : E => (y : G))
      (hE.pow_eq_one ⟨x, hxE⟩)

  have hcentNe :
      centralizerWithin K (Subgroup.closure ({x} : Set G)) ≠ ⊥ := by
    intro hbot
    apply hxcent
    rw [Subgroup.zpowers_eq_closure, hbot]
    exact bot_le
  have hxU : ({x} : Set G) ⊆ subgroupNonidentity U := by
    intro y hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨hP0U hxP0, hx1⟩
  have huniq0 := htypeFacts.subgroup_centralizer_unique
    ({x} : Set G) (Set.singleton_nonempty x) hxU hcentNe
  have huniq : minSimple_max_groups_of (G := G)
      (centralizerOfElement8 x : Set G) = {M} := by
    simpa only [centralizerOfElement8, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure] using huniq0
  have hZne : Subgroup.zpowers x ≠ (⊥ : Subgroup G) := by
    intro hbot
    exact hx1 (Subgroup.zpowers_eq_bot.mp hbot)
  have hZp : IsPGroup p (Subgroup.zpowers x) :=
    hE.isPGroup.to_le (Subgroup.zpowers_le.mpr hxE)
  have hZproper : Subgroup.zpowers x < (⊤ : Subgroup G) :=
    mFT_pgroup_proper (Subgroup.zpowers x) hZp
  have hnormProper :
      Subgroup.normalizer (Subgroup.zpowers x : Set G) <
        (⊤ : Subgroup G) :=
    mFT_norm_proper (Subgroup.zpowers x) hZne hZproper
  have hnormM : Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ M :=
    sub_uniq_mmax huniq
      (Subgroup.centralizer_le_normalizer (Subgroup.zpowers x : Set G))
      hnormProper
  have hcentNotL : ¬ centralizerOfElement8 x ≤ L := by
    intro hcentL
    have hLM : L = M := eq_uniq_mmax huniq hLmax hcentL
    have hP0K : P0 ≤ K := by
      change P0 ≤ Fitting_core M
      rw [← FTcore_type1 M ctx.M_type_context.type_one]
      simpa only [hLM] using hP0core
    have hpK : p ∣ Nat.card K := by
      have hpE : p ∣ Nat.card E := by
        rw [hE.card_eq]
        exact dvd_pow_self p (by omega : 2 ≠ 0)
      exact hpE.trans (Subgroup.card_dvd_of_le (hEP0.trans hP0K))
    exact (ctx.p_prime.coprime_iff_not_dvd.mp ctx.core_p_prime) hpK

  exact ⟨{
    P0_abelian := hP0comm
    P0_rank_two := hP0rankTwo
    L := L
    L_maximal := hLmax
    P0_le_FTcore := hP0core
    x := x
    x_mem_omega := hxOmega
    x_ne_one := hx1
    core_centralizer_not_le_derived := hxcent
    normalizer_le_M := hnormM
    centralizer_not_le_L := hcentNotL }⟩

end

end Submission.OddOrder.PF
