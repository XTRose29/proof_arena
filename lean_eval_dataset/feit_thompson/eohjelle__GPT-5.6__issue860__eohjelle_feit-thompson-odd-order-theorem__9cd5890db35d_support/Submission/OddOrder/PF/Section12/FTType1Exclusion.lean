import Submission.OddOrder.PF.Section12.FTType1NonFrobenius
import Submission.OddOrder.BG.Section04.OddPGroupRankOne

/-!
# Peterfalvi Section 12: exclusion of the all-type-I alternative

This file proves Peterfalvi (12.7), which turns a type-I maximal subgroup
into a Frobenius group with Fitting kernel, and Peterfalvi (12.17), which
rules out the possibility that every maximal subgroup has type I.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped Classical

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## Type-I maximal subgroups are Frobenius -/

/-- The induction step behind Peterfalvi (12.7): a prime supporting an
elementary abelian rank-two subgroup of a type-I maximal subgroup must occur
in its Fitting core. -/
private theorem rankTwo_prime_mem_fittingCore12 :
    ∀ (p : ℕ), p.Prime →
      ∀ {M : Subgroup G},
        M ∈ minSimple_max_groups (G := G) →
          FTtype M = 1 →
            HasElementaryAbelianRankAtLeast p 2 M →
              p ∈ primeSupport (Nat.card (Fitting_core M)) := by
  classical
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
      intro hp M hM htype hrank
      letI : Fact p.Prime := ⟨hp⟩
      by_contra hpFitting
      have hpCard : ¬ p ∣ Nat.card (Fitting_core M) := by
        intro hdiv
        exact hpFitting ⟨hp, hdiv⟩
      have hPPrime : IsPPrimeSubgroup p (Fitting_core M) :=
        hp.coprime_iff_not_dvd.mpr hpCard
      let P : Sylow p M := Sylow.nonempty.some
      let P₀ : Subgroup G := (P : Subgroup M).map M.subtype
      have hSylow : IsSylowSubgroupOf p P₀ M := ⟨P, rfl⟩
      let ctx : FTType1NonFrobeniusContext p M P₀ :=
        { p_prime := hp
          inductive_hypothesis := by
            intro q N hq hqp hN hNtype hNrank
            exact ih q hqp hq hN hNtype hNrank
          M_type_context := ⟨hM, htype⟩
          p_rank_gt_one := hrank
          core_p_prime := hPPrime
          sylow_P0 := hSylow }
      exact FTtype1_nonFrobenius_contradiction ctx

/-- `PFsection12.v: FTtype1_Frobenius`, Peterfalvi (12.7). -/
theorem FTtype1_Frobenius
    (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (htype : FTtype M = 1) :
    ∃ U : Subgroup G, IsFrobeniusIn (Fitting_core M) U M := by
  classical
  obtain ⟨U, hTypeI⟩ := (FTtypeP 1 M hM).mpr htype
  have hTypeF : of_typeF M U := hTypeI.1
  have hUM : U ≤ M := hTypeF.2.2.1.2.1
  have hComplement := hTypeF.2.2.1.2.2.2
  have hcoprime :
      Nat.Coprime (Nat.card (Fitting_core M)) (Nat.card U) := by
    have hHall := (Fcore_Hall M).coprime_card_index
    rw [hComplement.symm.index_eq_card] at hHall
    simpa only [MathlibSupport.natCard_subgroupOf_eq (Fcore_sub M),
      MathlibSupport.natCard_subgroupOf_eq hUM] using hHall
  refine ⟨U, (typeF_context M U hTypeF).frobenius_iff_zgroup.mpr ?_⟩
  intro p hp P
  have hPodd : Odd (Nat.card P) :=
    Odd.of_dvd_nat (mFT_odd U)
      (P : Subgroup U).card_subgroup_dvd_card
  apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
    P.isPGroup' hPodd).mpr
  rintro ⟨E, hErank⟩
  let EU : Subgroup U := E.map (P : Subgroup U).subtype
  let EG : Subgroup G := EU.map U.subtype
  have hEUrank : IsElementaryAbelianOfRank p 2 EU :=
    hErank.map_of_injective (P : Subgroup U).subtype
      (P : Subgroup U).subtype_injective
  have hEGrank : IsElementaryAbelianOfRank p 2 EG :=
    hEUrank.map_of_injective U.subtype U.subtype_injective
  have hEGM : EG ≤ M := (Subgroup.map_subtype_le EU).trans hUM
  have hRankM : HasElementaryAbelianRankAtLeast p 2 M :=
    ⟨EG, hEGM, hEGrank⟩
  have hpFitting :=
    rankTwo_prime_mem_fittingCore12 p Fact.out hM htype hRankM
  have hpE : p ∣ Nat.card E := by
    rw [hErank.card_eq]
    exact dvd_pow_self p (by omega : 2 ≠ 0)
  have hpU : p ∣ Nat.card U :=
    (hpE.trans E.card_subgroup_dvd_card).trans
      (P : Subgroup U).card_subgroup_dvd_card
  exact (Nat.not_coprime_of_dvd_of_dvd
    (Fact.out : p.Prime).one_lt hpFitting.2 hpU) hcoprime

/-! ## The coherent Frobenius partition contradiction -/

/-- Conjugacy in the ambient group preserves the order of the canonical
Feit--Thompson core. -/
private theorem natCard_FTcore_eq_of_conjugate12
    {M N : Subgroup G}
    (hMN : AreConjugateSubgroupsWithin (⊤ : Subgroup G) M N) :
    Nat.card (FTcore M) = Nat.card (FTcore N) := by
  induction hMN with
  | rel M N h =>
      rcases h with ⟨x, -, rfl⟩
      rw [FTcoreJ, Subgroup.card_map_of_injective (MulAut.conj x).injective]
  | refl M => rfl
  | symm M N _ ih => exact ih.symm
  | trans M N L _ _ hMN hNL => exact hMN.trans hNL

/-- If every maximal subgroup has type I, the Fitting core of each maximal
subgroup is a normalized TI set. -/
private theorem fittingCore_normalizedTI_of_all_type_one12
    (hall : all_FTtype1 (G := G))
    {L : Subgroup G}
    (hL : L ∈ minSimple_max_groups (G := G)) :
    IsNormalizedTI
      (subgroupNonidentity (Fitting_core L)) (⊤ : Subgroup G) L := by
  apply isNormalizedTI_iff_mem_conj.mpr
  have hnonempty :
      (subgroupNonidentity (Fitting_core L)).Nonempty := by
    obtain ⟨x, hx, hxOne⟩ :=
      (Fitting_core L).bot_or_exists_ne_one.resolve_left
        (Fcore_structure hL).Fcore_ne_bot
    exact ⟨x, hx, hxOne⟩
  refine ⟨hnonempty, le_top, ?_⟩
  intro x hx z _hz
  constructor
  · intro hxz
    have hxSupport0 : x ∈ FTsupport0 L := Fcore_sub_FTsupp0 hL hx
    have hxzSupport0 : conjugateElement16 x z⁻¹ ∈ FTsupport0 L := by
      simpa [conjugateElement16, MulAut.conj_apply, mul_assoc] using
        (Fcore_sub_FTsupp0 hL hxz)
    let facts := FTsupport_facts L hL
    obtain ⟨y, hyL, hconj⟩ :=
      facts.fusion_control x hxSupport0 z⁻¹ hxzSupport0
    have hcentralizer : centralizerOfElement8 x ≤ L := by
      by_contra hnot
      let data := facts.element_data x ⟨hxSupport0, hnot⟩
      let N : Subgroup G := elementNormalizer15 x
      have hNmax : N ∈ minSimple_max_groups (G := G) :=
        (mem_uniq_mmax data.unique_maximal_centralizer).1
      have hNtype : FTtype N = 1 := hall N hNmax
      obtain ⟨E, hFrob⟩ := FTtype1_Frobenius N hNmax hNtype
      let frobCtx : FTFrobeniusContext N :=
        { maxL := hNmax
          frobenius := ⟨E, hFrob⟩ }
      have hxCore : x ∈ subgroupNonidentity (Fitting_core N) := by
        rw [← FTsupp_Frobenius frobCtx]
        exact data.support_not_support1.1
      apply data.support_not_support1.2
      rw [FTsupp1_type1 N hNtype]
      exact hxCore
    have hconj' : z⁻¹ * x * z = y * x * y⁻¹ := by
      simpa [conjugateElement16, MulAut.conj_apply] using hconj
    have hcomm : Commute (y⁻¹ * z⁻¹) x := by
      show (y⁻¹ * z⁻¹) * x = x * (y⁻¹ * z⁻¹)
      calc
        (y⁻¹ * z⁻¹) * x = y⁻¹ * (z⁻¹ * x * z) * z⁻¹ := by
          group
        _ = y⁻¹ * (y * x * y⁻¹) * z⁻¹ := by rw [hconj']
        _ = x * (y⁻¹ * z⁻¹) := by group
    have hyzL : y⁻¹ * z⁻¹ ∈ L := by
      apply hcentralizer
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
      exact (hcomm.zpow_right n).symm
    rw [show z = (y⁻¹ * z⁻¹)⁻¹ * y⁻¹ by group]
    exact L.mul_mem (L.inv_mem hyzL) (L.inv_mem hyL)
  · intro hzL
    have hnormalizes : z ∈ Subgroup.normalizer (Fitting_core L : Set G) :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub L)).mp
        (Fcore_normal L)) hzL
    refine ⟨((Subgroup.mem_set_normalizer_iff''.mp hnormalizes x).1 hx.1),
      ?_⟩
    intro hOne
    apply hx.2
    simpa [mul_assoc] using congrArg (fun t ↦ z * t * z⁻¹) hOne

/-- A normalized-TI Dade support is just the corresponding conjugacy
support. -/
private theorem dadeSupport_eq_classSupport12
    {Q : Type*} [Group Q] [Finite Q]
    {D L : Subgroup Q} {A : Set Q}
    (ddA : DadeHypothesis D L A)
    (hTI : IsNormalizedTI A D L) :
    Dade_support ddA = classSupportWithin D A := by
  have hsignalizer : ∀ a : Q, a ∈ A → DadeSignalizer ddA a = ⊥ :=
    ((Dade_normedTI_P ddA).mp hTI).2
  ext x
  constructor
  · rintro ⟨a, ha, z, hz, g, hg, hzx⟩
    rcases Set.mem_mul.mp hz with ⟨s, hs, b, hb, hsb⟩
    have hsOne : s = 1 := by
      rw [hsignalizer a ha] at hs
      simpa using hs
    have hbEq : b = a := Set.mem_singleton_iff.mp hb
    subst s
    subst b
    simp only [one_mul] at hsb
    subst z
    exact ⟨a, ha, g, hg, hzx⟩
  · rintro ⟨a, ha, g, hg, hax⟩
    refine ⟨a, ha, a, ?_, g, hg, hax⟩
    exact Set.mem_mul.mpr
      ⟨1, (DadeSignalizer ddA a).one_mem,
        a, Set.mem_singleton a, one_mul a⟩

/-- `PFsection12.v: not_all_FTtype1`, Peterfalvi (12.17). -/
theorem not_all_FTtype1 : ¬ all_FTtype1 (G := G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  intro hall
  obtain ⟨hprime, hcoreCoprime, _hcard, _hinjective, hpartition, _hpair⟩ :=
    FT_Dade_support_partition (G := G)
  let spec := mmax_transversalP (G := G)
  let I := {L : Subgroup G // L ∈ mmax_transversal (⊤ : Subgroup G)}
  letI : Fintype I := Fintype.ofFinite I
  let L : I → Subgroup G := fun i ↦ i.1
  let H : I → Subgroup G := fun i ↦ Fitting_core (L i)
  have hmax (i : I) : L i ∈ minSimple_max_groups (G := G) :=
    spec.subset_maximal i.2
  have htype (i : I) : FTtype (L i) = 1 := hall (L i) (hmax i)
  choose E hFrob using fun i : I ↦
    FTtype1_Frobenius (L i) (hmax i) (htype i)
  have hHL (i : I) : H i ≤ L i := by
    simpa only [H] using Fcore_sub (L i)
  have hEL (i : I) : E i ≤ L i := by
    have hle := (hFrob i).2.1.2.1
    simpa only [(hFrob i).1] using hle
  have hFrobenius (i : I) :
      L i ≤ (⊤ : Subgroup G) ∧ IsSolvable (L i) ∧
        IsFrobeniusDecomposition
          ((H i).subgroupOf (L i)) ((E i).subgroupOf (L i)) := by
    refine ⟨le_top, mmax_sol (hmax i), ?_⟩
    have hdecomp := (hFrob i).2.2
    rw [(hFrob i).1] at hdecomp
    simpa only [H] using hdecomp
  have hTI (i : I) :
      IsNormalizedTI (subgroupNonidentity (H i))
        (⊤ : Subgroup G) (L i) := by
    simpa only [H] using
      fittingCore_normalizedTI_of_all_type_one12 hall (hmax i)
  have hcoprime (i j : I) (hij : i ≠ j) :
      Nat.Coprime (Nat.card (H i)) (Nat.card (H j)) := by
    have hnotConjugate : ¬ FTAmbientConjugate (L i) (L j) := by
      rintro ⟨g, hg⟩
      have hwithin : AreConjugateSubgroupsWithin
          (⊤ : Subgroup G) (L i) (L j) :=
        Relation.EqvGen.rel _ _ ⟨g, Subgroup.mem_top g, hg⟩
      apply hij
      exact Subtype.ext (spec.conjugacy_injective i.2 j.2 hwithin)
    simpa only [H, FTcore_type1 (L i) (htype i),
      FTcore_type1 (L j) (htype j)] using
        hcoreCoprime (hmax i) (hmax j) hnotConjugate
  have hInonempty : Nonempty I := by
    obtain ⟨M, hM⟩ := any_mmax (G := G)
    obtain ⟨N, hN, -⟩ := spec.representative hM
    exact ⟨⟨N, hN⟩⟩
  letI : Nonempty I := hInonempty
  have hIcard : 2 ≤ Nat.card I := by
    by_contra hltTwo
    have hcardOne : Nat.card I = 1 := by
      have hpositive : 0 < Nat.card I := Nat.card_pos
      omega
    letI : Subsingleton I := (Nat.card_eq_one_iff_unique.mp hcardOne).1
    let i₀ : I := Classical.choice hInonempty
    have hallPrimes (p : ℕ) (hpG : p ∈ primeSupport (Nat.card G)) :
        p ∈ primeSupport (Nat.card (H i₀)) := by
      rw [hprime] at hpG
      obtain ⟨M, hM, hpM⟩ := hpG
      obtain ⟨N, hN, hMN⟩ := spec.representative hM
      let iN : I := ⟨N, hN⟩
      have hiN : iN = i₀ := Subsingleton.elim _ _
      have hcardCore := natCard_FTcore_eq_of_conjugate12 hMN
      have hpN : p ∈ primeSupport (Nat.card (FTcore N)) := by
        rw [← hcardCore]
        exact hpM
      have hNmax : N ∈ minSimple_max_groups (G := G) :=
        spec.subset_maximal hN
      have hNtype : FTtype N = 1 := hall N hNmax
      rw [FTcore_type1 N hNtype] at hpN
      have hNeq : N = L i₀ := congrArg Subtype.val hiN
      simpa only [H, hNeq] using hpN
    let K : Subgroup G := H i₀
    have hHall : IsHall (primeSupport (Nat.card K)) K := by
      simpa only [K, H] using
        (FTcore_facts (L i₀) (hmax i₀)).fittingCore_hall_G
    have hindexOne : K.index = 1 := by
      by_contra hindex
      let p := Nat.minFac K.index
      have hp : p.Prime := Nat.minFac_prime hindex
      have hpIndex : p ∣ K.index := Nat.minFac_dvd _
      have hpG : p ∈ primeSupport (Nat.card G) :=
        ⟨hp, hpIndex.trans K.index_dvd_card⟩
      exact (hHall.isPiNumber_index hp hpIndex (hallPrimes p hpG)).elim
    have hKtop : K = ⊤ := Subgroup.index_eq_one.mp hindexOne
    have hLtop : L i₀ = ⊤ := by
      apply top_unique
      have hKL : K ≤ L i₀ := by
        simpa only [K] using hHL i₀
      simpa only [hKtop] using hKL
    exact (mmax_proper (hmax i₀)).ne hLtop
  have hsupport (i : I) :
      classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity (H i)) =
        FT_Dade1_support (L i) := by
    have hTI1 : IsNormalizedTI (FTsupport1 (L i))
        (⊤ : Subgroup G) (L i) := by
      rw [FTsupp1_type1 (L i) (htype i)]
      exact hTI i
    calc
      classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity (H i)) =
          classSupportWithin (⊤ : Subgroup G) (FTsupport1 (L i)) := by
            rw [FTsupp1_type1 (L i) (htype i)]
      _ = Dade_support (FT_Dade1_hyp (L i) (hmax i)) :=
        (dadeSupport_eq_classSupport12
          (FT_Dade1_hyp (L i) (hmax i)) hTI1).symm
      _ = FT_Dade1_support (L i) := FT_Dade1_supportE (L i) (hmax i)
  have hcover :
      (⋃ i : I, classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity (H i))) = nonidentitySet G := by
    calc
      (⋃ i : I, classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity (H i))) =
          ⋃ i : I, FT_Dade1_support (L i) := by
            apply Set.iUnion_congr
            exact hsupport
      _ = ⋃₀ (ftFirstDadeSupportFamily (G := G)) := by
        ext x
        simp [ftFirstDadeSupportFamily, I, L]
      _ = nonidentitySet G := (hpartition hall).1
  have hremainder :
      coherentFrobeniusRemainder (⊤ : Subgroup G) H = {1} := by
    unfold coherentFrobeniusRemainder
    rw [hcover]
    ext x
    simp [nonidentitySet]
  exact (no_coherent_Frobenius_partition
    (⊤ : Subgroup G) (mFT_odd (⊤ : Subgroup G)) hIcard
    L H E hHL hEL hFrobenius hTI hcoprime) hremainder

end

end Submission.OddOrder.PF
