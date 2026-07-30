import Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary
import Submission.OddOrder.PF.Section08.FTTypePContext

/-!
# Peterfalvi Section 8: core and support facts

This module packages the one-maximal-subgroup consequences of the
Bender--Glauberman summaries.  It establishes the Hall and Sylow-normalizer
properties of the FT core, transports Summary B to complements of the first
two FT types, specializes Summary II to `FTsupport0`, and identifies the
normalizers of the three canonical FT supports.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open FTContextInternal
open scoped BigOperators Classical Pointwise IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## Public conclusion interfaces -/

/-- The three assertions of Peterfalvi (8.11). -/
structure FTCoreFacts (M : Subgroup G) : Prop where
  fittingCore_hall_G :
    IsHall (primeSupport (Nat.card (Fitting_core M))) (Fitting_core M)
  ftCore_hall_G :
    IsHall (primeSupport (Nat.card (FTcore M))) (FTcore M)
  sylow_normalizer_le : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G),
    IsSylowWithin8 p S (FTcore M) → S ≠ ⊥ →
      Subgroup.normalizer (S : Set G) ≤ M

/-- The conclusions of Peterfalvi (8.12) in the type-I/type-II range. -/
structure FTTypeI_IIFacts (M U : Subgroup G) : Prop where
  sylow_abelian_rank_le_two :
    ∀ (p : ℕ) [Fact p.Prime] (S : Sylow p U),
      IsMulCommutative (S : Subgroup U) ∧
        Group.rank (S : Subgroup U) ≤ 2
  subgroup_centralizer_unique : ∀ (X : Set G),
    X.Nonempty → X ⊆ subgroupNonidentity U →
      centralizerWithin (Fitting_core M) (Subgroup.closure X) ≠ ⊥ →
      minSimple_max_groups_of (G := G)
        (Subgroup.centralizer X : Set G) = {M}
  support_difference_normalizedTI :
    FTsupport M \ FTsupport1 M ≠ ∅ →
      IsNormalizedTI (FTsupport M \ FTsupport1 M) ⊤ M

/-- Peterfalvi (8.13), in the witness-bearing sort of Summary II. -/
abbrev FTSupportFacts (M : Subgroup G) : Type u :=
  BGSummaryIIConclusion M (FTsupport0 M)

/-! ## The FT core -/

/-- Peterfalvi (8.11). -/
theorem FTcore_facts (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTCoreFacts M := by
  have hFcoreSigma : Fitting_core M ≤ sigmaCore M :=
    Fcore_sub_Msigma hM
  have hSigmaM : sigmaCore M ≤ M := sigmaCore_le M
  have hFcoreHallSigma :
      IsHall (primeSupport (Nat.card (Fitting_core M)))
        ((Fitting_core M).subgroupOf (sigmaCore M)) :=
    isHall_subgroupOf_of_le8 hFcoreSigma hSigmaM (Fcore_Hall M)
  refine
    { fittingCore_hall_G :=
        isHall_of_isHall_subgroupOf8 hFcoreSigma
          (fun _ hp ↦
            (sigmaCore_isPiNumber M) hp.1
              (hp.2.trans (Subgroup.card_dvd_of_le hFcoreSigma)))
          hFcoreHallSigma (Msigma_Hall_G hM)
      ftCore_hall_G := ?_
      sylow_normalizer_le := ?_ }
  · rw [def_FTcore hM]
    exact isHall_primeSupport (sigmaCore M)
      (Msigma_Hall_G hM).coprime_card_index
  · intro p hp S hSylow hSne
    rw [def_FTcore hM] at hSylow
    rcases hSylow with ⟨P, rfl⟩
    let PG : Subgroup G :=
      (P : Subgroup (sigmaCore M)).map (sigmaCore M).subtype
    have hPGp : IsPGroup p PG :=
      P.isPGroup'.map (sigmaCore M).subtype
    have hPGleSigma : PG ≤ sigmaCore M := Subgroup.map_subtype_le _
    have hPGne : PG ≠ ⊥ := by simpa only [PG] using hSne
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPGne
    have hpSigmaCard : p ∣ Nat.card (sigmaCore M) := by
      have hpx : p ∣ orderOf (x : G) := by
        simpa using hPGp.dvd_orderOf hx1
      have hxorder : orderOf (x : G) ∣ Nat.card (sigmaCore M) := by
        simpa using orderOf_dvd_natCard
          (⟨(x : G), hPGleSigma x.property⟩ : sigmaCore M)
      exact hpx.trans hxorder
    have hpSigma : p ∈ sigmaPrimes M :=
      (Msigma_Hall_G hM).isPiNumber_card Fact.out hpSigmaCard
    obtain ⟨Q, hQ⟩ :=
      exists_sylow_eq_map_of_sylow_hall8 Fact.out
        (Msigma_Hall_G hM) hpSigma P
    have hQM : (Q : Subgroup G) ≤ M := by
      rw [hQ]
      exact (Subgroup.map_subtype_le _).trans (sigmaCore_le M)
    let QM : Sylow p M := Q.subtype hQM
    have hambient : ambientSylow M QM = PG := by
      dsimp only [QM, ambientSylow, PG]
      rw [Sylow.coe_subtype,
        Subgroup.map_subgroupOf_eq_of_le hQM, hQ]
    simpa only [hambient] using norm_sigma_Sylow hpSigma QM

/-! ## Types I and II -/

/-- Peterfalvi (8.12). -/
theorem FTtypeI_II_facts
    (n : ℕ) (M U : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (htype : FTtype M = n)
    (hdecomp : IsInternalSemidirectProductIn (Fitting_core M) U
      (derivedSeriesWithin8 M (n - 1))) :
    0 < n ∧ n ≤ 2 → FTTypeI_IIFacts M U := by
  intro hn
  have hn12 : n = 1 ∨ n = 2 := by
    clear htype hdecomp
    omega
  have htype12 : FTtype M = 1 ∨ FTtype M = 2 := by
    rw [htype]
    exact hn12
  have hFcoreSigma : Fitting_core M = sigmaCore M :=
    ((Fcore_eq_FTcore hM).2
      (htype12.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))).trans
        (def_FTcore hM)
  have hterm : derivedSeriesWithin8 M (n - 1) = FTder M := by
    rcases hn12 with hn1 | hn2
    · have htype1 : FTtype M = 1 := htype.trans hn1
      rw [hn1]
      simp [derivedSeriesWithin8, FTder, ftDerived, htype1,
        ← MonoidHom.range_eq_map, M.range_subtype]
    · have htype2 : FTtype M = 2 := htype.trans hn2
      rw [hn2]
      simp [derivedSeriesWithin8, FTder, ftDerived, htype2,
        derivedWithin]
  have htermM : derivedSeriesWithin8 M (n - 1) ≤ M := by
    unfold derivedSeriesWithin8
    exact Subgroup.map_subtype_le _
  have hUM : U ≤ M := hdecomp.2.1.trans htermM
  obtain ⟨V, K, hComplV⟩ := kappa_witness hM
  have hsdV := sdprod_FTder hM hComplV
  have hcardUV : Nat.card U = Nat.card V := by
    calc
      Nat.card U =
          Nat.card (U.subgroupOf (derivedSeriesWithin8 M (n - 1))) :=
        (MathlibSupport.natCard_subgroupOf_eq hdecomp.2.1).symm
      _ = ((Fitting_core M).subgroupOf
            (derivedSeriesWithin8 M (n - 1))).index :=
        hdecomp.2.2.2.symm.index_eq_card.symm
      _ = ((sigmaCore M).subgroupOf (FTder M)).index := by
        rw [hFcoreSigma, hterm]
      _ = Nat.card (V.subgroupOf (FTder M)) :=
        hsdV.2.2.2.symm.index_eq_card
      _ = Nat.card V :=
        MathlibSupport.natCard_subgroupOf_eq hsdV.2.1
  have hindexUV :
      (U.subgroupOf M).index = (V.subgroupOf M).index := by
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.card_pos (α := U.subgroupOf M))
    calc
      (U.subgroupOf M).index * Nat.card (U.subgroupOf M) =
          Nat.card M := (U.subgroupOf M).index_mul_card
      _ = (V.subgroupOf M).index * Nat.card (V.subgroupOf M) :=
        (V.subgroupOf M).index_mul_card.symm
      _ = (V.subgroupOf M).index * Nat.card (U.subgroupOf M) := by
        rw [MathlibSupport.natCard_subgroupOf_eq hUM,
          MathlibSupport.natCard_subgroupOf_eq hComplV.U_le_M,
          hcardUV]
  have hHallU :
      IsHall (sigmaKappaPrimes M)ᶜ (U.subgroupOf M) := by
    constructor
    · have hpi := hComplV.hall_U.isPiNumber_card
      rw [MathlibSupport.natCard_subgroupOf_eq hComplV.U_le_M] at hpi
      rwa [MathlibSupport.natCard_subgroupOf_eq hUM, hcardUV]
    · simpa only [hindexUV] using
        hComplV.hall_U.isPiNumber_index
  obtain ⟨x, hx⟩ :=
    exists_map_conj_eq_of_isHall_of_isSolvable
      (mmax_sol hM) hComplV.hall_U hHallU
  have hVx : conjugateSubgroup8 V (x : G) = U :=
    ambient_conjugate_eq_of_subgroupOf8 hComplV.U_le_M hUM x hx
  let e : G ≃* G := MulAut.conj (x : G)
  let Kx : Subgroup G := conjugateSubgroup8 K (x : G)
  have hMfix : conjugateSubgroup8 M (x : G) = M :=
    conjugateSubgroup8_eq_self_of_mem_normalizer
      (Subgroup.le_normalizer x.property)
  have hKxM : Kx ≤ M := by
    change conjugateSubgroup8 K (x : G) ≤ M
    exact (Subgroup.map_mono hComplV.K_le_M).trans_eq hMfix
  have hcardKx : Nat.card Kx = Nat.card K := by
    dsimp only [Kx]
    rw [conjugateSubgroup8,
      Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective]
  have hcardKxM :
      Nat.card (Kx.subgroupOf M) = Nat.card (K.subgroupOf M) := by
    rw [MathlibSupport.natCard_subgroupOf_eq hKxM,
      MathlibSupport.natCard_subgroupOf_eq hComplV.K_le_M, hcardKx]
  have hindexKxM :
      (Kx.subgroupOf M).index = (K.subgroupOf M).index := by
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.card_pos (α := Kx.subgroupOf M))
    calc
      (Kx.subgroupOf M).index * Nat.card (Kx.subgroupOf M) =
          Nat.card M := (Kx.subgroupOf M).index_mul_card
      _ = (K.subgroupOf M).index * Nat.card (K.subgroupOf M) :=
        (K.subgroupOf M).index_mul_card.symm
      _ = (K.subgroupOf M).index * Nat.card (Kx.subgroupOf M) := by
        rw [hcardKxM]
  have hHallKx : IsHall (kappaPrimes M) (Kx.subgroupOf M) := by
    constructor
    · simpa only [hcardKxM] using
        hComplV.hall_K.isPiNumber_card
    · simpa only [hindexKxM] using
        hComplV.hall_K.isPiNumber_index
  obtain ⟨E, hE⟩ := hComplV.product_is_group
  let Ex : Subgroup G := conjugateSubgroup8 E (x : G)
  have hprod : (Ex : Set G) = (U : Set G) * (Kx : Set G) := by
    ext z
    constructor
    · intro hz
      have hzmap : z ∈ E.map e.toMonoidHom := by
        change z ∈ E.map e.toMonoidHom at hz
        exact hz
      have hzpre : e.symm z ∈ E := Subgroup.mem_map_equiv.mp hzmap
      have hzpreSet : e.symm z ∈ (E : Set G) := hzpre
      rw [hE] at hzpreSet
      rcases hzpreSet with ⟨v, hv, k, hk, hvk⟩
      refine ⟨e v, ?_, e k, ?_, ?_⟩
      · have hev : e v ∈ conjugateSubgroup8 V (x : G) := by
          change e v ∈ V.map e.toMonoidHom
          exact Subgroup.mem_map_of_mem e.toMonoidHom hv
        rwa [hVx] at hev
      · change e k ∈ K.map e.toMonoidHom
        exact Subgroup.mem_map_of_mem e.toMonoidHom hk
      · simpa using congrArg e hvk
    · rintro ⟨u, hu, k, hk, rfl⟩
      have huMap : u ∈ V.map e.toMonoidHom := by
        change u ∈ conjugateSubgroup8 V (x : G)
        rw [hVx]
        exact hu
      have hkMap : k ∈ K.map e.toMonoidHom := by
        change k ∈ K.map e.toMonoidHom at hk
        exact hk
      have huv : e.symm u ∈ V := Subgroup.mem_map_equiv.mp huMap
      have hkk : e.symm k ∈ K := Subgroup.mem_map_equiv.mp hkMap
      have hpreSet : e.symm (u * k) ∈ (E : Set G) := by
        rw [hE]
        exact ⟨e.symm u, huv, e.symm k, hkk, by simp⟩
      have hpre : e.symm (u * k) ∈ E := hpreSet
      have hmap : u * k ∈ E.map e.toMonoidHom :=
        Subgroup.mem_map_equiv.mpr hpre
      change u * k ∈ E.map e.toMonoidHom
      exact hmap
  have hComplU : KappaComplement M U Kx :=
    { U_le_M := hUM
      hall_U := hHallU
      K_le_M := hKxM
      hall_K := hHallKx
      product_is_group := ⟨Ex, hprod⟩ }
  have hBG := BGsummaryB hM hComplU
  refine
    { sylow_abelian_rank_le_two := hBG.sylow_abelian_rank_le_two
      subgroup_centralizer_unique := ?_
      support_difference_normalizedTI := ?_ }
  · intro X hXne hXU hcent
    let Y : Subgroup G := Subgroup.closure X
    have hYU : Y ≤ U := by
      apply (Subgroup.closure_le U).mpr
      intro y hy
      exact (hXU hy).1
    have hYne : Y ≠ ⊥ := by
      obtain ⟨y, hyX⟩ := hXne
      intro hYbot
      have hyY : y ∈ Y := Subgroup.subset_closure hyX
      have hyOne : y = 1 := Subgroup.mem_bot.mp (hYbot ▸ hyY)
      exact (hXU hyX).2 hyOne
    have hcentSigma : centralizerWithin (sigmaCore M) Y ≠ ⊥ := by
      simpa only [Y, hFcoreSigma] using hcent
    have hunique :=
      hBG.subgroup_centralizer_unique hYU hYne hcentSigma
    simpa only [Y, Subgroup.centralizer_closure] using hunique
  · intro hdiff
    have hne : FTsupport M ≠ FTsupport1 M := by
      intro heq
      apply hdiff
      rw [heq, Set.sdiff_self]
    exact hBG.support_difference_normalizedTI hne

/-! ## Summary II and canonical support normalizers -/

/-- Peterfalvi (8.13), specialized to `FTsupport0 M`. -/
noncomputable def FTsupport_facts (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTSupportFacts M :=
  BGsummaryII M (FTsupport0 M) hM (Or.inr rfl)

/-- A support lying between `FTsupport1` and `FTsupport0` has maximal
normalizer. -/
private theorem normalizer_eq_of_support_bounds
    (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    {A : Set G}
    (hNorm : M ≤ Subgroup.normalizer A)
    (hOne : FTsupport1 M ⊆ A)
    (hOuter : A ⊆ FTsupport0 M) :
    Subgroup.normalizer A = M := by
  apply mmax_normal_subset hM
  · intro x hx
    exact (FTsupp0_sub M (hOuter hx)).1
  · exact hNorm
  · intro hAone
    obtain ⟨x, hx⟩ : (FTsupport1 M).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr (FTsupp1_neq0 hM)
    have hxOne : x = 1 := by
      simpa using hAone (hOne hx)
    exact hx.2 hxOne

/-- Peterfalvi (8.15), for `FTsupport1`. -/
theorem norm_FTsupp1 (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Subgroup.normalizer (FTsupport1 M) = M :=
  normalizer_eq_of_support_bounds M hM (FTsupp1_norm M)
    Set.Subset.rfl (FTsupp1_sub0 hM)

/-- Peterfalvi (8.15), for `FTsupport`. -/
theorem norm_FTsupp (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Subgroup.normalizer (FTsupport M) = M :=
  normalizer_eq_of_support_bounds M hM (FTsupp_norm M)
    (FTsupp1_sub hM) (FTsupp_sub0 M)

/-- Peterfalvi (8.15), for `FTsupport0`. -/
theorem norm_FTsupp0 (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Subgroup.normalizer (FTsupport0 M) = M :=
  normalizer_eq_of_support_bounds M hM (FTsupp0_norm M)
    (FTsupp1_sub0 hM) Set.Subset.rfl

end

end Submission.OddOrder.PF
