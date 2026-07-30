import Submission.OddOrder.BG.Section14.PartitionAndSignalizers
import Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary
import Submission.OddOrder.PF.Section07.CoherentFrobeniusPartition
import Submission.OddOrder.PF.Section08.FTTypeContexts
import Submission.OddOrder.PF.Section08.FTPrimeDadeCoherence

/-!
# Peterfalvi Section 8: the global Dade-support partition

This file ports `PFsection8.v`, lines 924--1132: Peterfalvi Theorem 8.17,
Lemma 8.18, and the first-support disjointness corollary used in Section 12.

The source transversal `'M^G` is represented by the canonical choice
`mmax_transversal (⊤ : Subgroup G)`.  In particular, the three mapped
declarations below have only their source hypotheses: all support and
centralizer calculations are obtained from `BGsummaryD`, `BGsummaryE`,
`FTsupport_facts`, and the Dade hypotheses proved earlier in Section 8.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open FTContextInternal
open scoped BigOperators Classical Pointwise

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## Source notation and elementary transport -/

/-- Ambient conjugacy of subgroups, the proposition written
`gval L \in M :^: G` in the source. -/
abbrev FTAmbientConjugate (M L : Subgroup G) : Prop :=
  AreConjugateSubgroups M L

/-- The family `PG` in Theorem 8.17, using the canonical transversal. -/
def ftFirstDadeSupportFamily : Set (Set G) :=
  FT_Dade1_support '' mmax_transversal (⊤ : Subgroup G)

/-- The exceptional support `VG` in Theorem 8.17(c). -/
def ftCyclicExceptionalSupport
    (W W₁ W₂ : Subgroup G) : Set G :=
  classSupportWithin (⊤ : Subgroup G) (cyclicTISet W W₁ W₂)

private theorem ftSupportPartition_ambient_refl (M : Subgroup G) :
    FTAmbientConjugate M M := by
  refine ⟨1, ?_⟩
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_one, one_mul, mul_one]

private theorem ftSupportPartition_ambient_symm
    {M L : Subgroup G} :
    FTAmbientConjugate M L → FTAmbientConjugate L M := by
  rintro ⟨x, rfl⟩
  refine ⟨x⁻¹, ?_⟩
  rw [Subgroup.map_map]
  ext y
  simp [MulAut.conj_apply, mul_assoc]

private theorem ftSupportPartition_ambient_trans
    {M L H : Subgroup G} :
    FTAmbientConjugate M L → FTAmbientConjugate L H →
      FTAmbientConjugate M H := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩
  refine ⟨y * x, ?_⟩
  rw [Subgroup.map_map]
  ext z
  simp [MulAut.conj_apply, mul_assoc]

private theorem ftSupportPartition_within_top_of_ambient
    {M L : Subgroup G} (hML : FTAmbientConjugate M L) :
    AreConjugateSubgroupsWithin (⊤ : Subgroup G) M L := by
  rcases hML with ⟨x, hx⟩
  exact Relation.EqvGen.rel _ _ ⟨x, Subgroup.mem_top x, hx⟩

private theorem ftSupportPartition_ambient_of_within_top
    {M L : Subgroup G}
    (hML : AreConjugateSubgroupsWithin (⊤ : Subgroup G) M L) :
    FTAmbientConjugate M L := by
  induction hML with
  | rel M L h =>
      rcases h with ⟨x, -, hx⟩
      exact ⟨x, hx⟩
  | refl M => exact ftSupportPartition_ambient_refl M
  | symm M L _ ih => exact ftSupportPartition_ambient_symm ih
  | trans M L H _ _ hML hLH =>
      exact ftSupportPartition_ambient_trans hML hLH

private theorem ftSupportPartition_conjugate_inv
    (M : Subgroup G) (x : G) :
    conjugateSubgroup8 (conjugateSubgroup8 M x) x⁻¹ = M := by
  unfold conjugateSubgroup8
  rw [Subgroup.map_map]
  ext y
  simp [MulAut.conj_apply, mul_assoc]

private theorem ftSupportPartition_semidirect_sup_eq
    {N H K : Subgroup G} (h : IsInternalSemidirectProductIn N H K) :
    N ⊔ H = K := by
  apply le_antisymm (sup_le h.1 h.2.1)
  intro k hk
  let kK : K := ⟨k, hk⟩
  obtain ⟨⟨n, a⟩, hna⟩ := h.2.2.2.2 kK
  have hnN : (n : G) ∈ N := n.property
  have haH : (a : G) ∈ H := a.property
  have hnaG : (n : G) * (a : G) = k := congrArg Subtype.val hna
  rw [← hnaG]
  exact Subgroup.mul_mem_sup hnN haH

private theorem ftSupportPartition_directProduct_sup_eq
    {A B W : Subgroup G} (h : IsInternalDirectProductIn A B W) :
    A ⊔ B = W := by
  apply le_antisymm (sup_le h.left_le h.right_le)
  intro w hw
  let wW : W := ⟨w, hw⟩
  obtain ⟨⟨a, b⟩, hab⟩ := h.complement.2 wW
  have haA : (a : G) ∈ A := a.property
  have hbB : (b : G) ∈ B := b.property
  have habG : (a : G) * (b : G) = w := congrArg Subtype.val hab
  rw [← habG]
  exact Subgroup.mul_mem_sup haA hbB

private theorem ftSupportPartition_isHall_subgroupOf_map
    {H L : Subgroup G} (hLH : L ≤ H)
    {pi : Set ℕ} (hL : IsHall pi (L.subgroupOf H))
    (e : G ≃* G) :
    IsHall pi
      ((L.map e.toMonoidHom).subgroupOf
        (H.map e.toMonoidHom)) := by
  rw [← subgroupOf_map_mulEquiv8 hLH e]
  exact isHall_map_mulEquiv8 (e.subgroupMap H) hL

private theorem ftSupportPartition_ftDer_le (M : Subgroup G) :
    FTder M ≤ M := by
  by_cases htype : FTtype M = 1
  · simp [FTder, ftDerived, htype]
  · rw [show FTder M = derivedWithin M by
      simp [FTder, ftDerived, htype]]
    unfold derivedWithin
    exact Subgroup.map_subtype_le _

/-! ## Identifying the sigma cover with the first Dade support -/

private theorem ftSupportPartition_signalizer_eq
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    {x : G} (hx : x ∈ FTsupport1 M) :
    ftSignalizer x = FTsignalizer M x := by
  have hxSigma : x ∈ subgroupNonidentity (sigmaCore M) := by
    refine ⟨?_, hx.2⟩
    rw [← def_FTcore hM]
    exact hx.1
  by_cases hcent : centralizerOfElement8 x ≤ M
  · rw [FTsignalizer, if_pos hcent]
    have hCM : elementCentralizerWithin M x = elementCentralizer x := by
      apply le_antisymm inf_le_right
      intro z hz
      exact ⟨hcent hz, hz⟩
    have hsd := ((BGsummaryD hM).signalizer hxSigma).centralizer_sdprod
    have hcomp := hsd.2.2.2.symm
    rw [hCM, Subgroup.subgroupOf_self] at hcomp
    have hsub :
        (ftSignalizer x).subgroupOf (elementCentralizer x) = ⊥ :=
      Subgroup.isComplement'_top_left.mp hcomp
    have hdis : Disjoint (ftSignalizer x) (elementCentralizer x) :=
      Subgroup.subgroupOf_eq_bot.mp hsub
    apply le_antisymm
    · exact (le_inf le_rfl hsd.1).trans hdis.le_bot
    · exact bot_le
  · rw [FTsignalizer, if_neg hcent]
    have hesc := (BGsummaryD hM).escaping_centralizer hxSigma hcent
    have hbase : ftSignalizerBase x = elementNormalizer15 x := by
      rfl
    simp only [ftSignalizer, hbase, hesc.normalizer_Fcore_eq_sigma]

private theorem ftSupportPartition_sigma_class_eq_first
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    classSupportWithin (⊤ : Subgroup G) (sigmaCover M) =
      FT_Dade1_support M := by
  ext g
  constructor
  · rintro ⟨a, ⟨x, hxSigma, hx1, r, hr, rfl⟩, z, hz, rfl⟩
    have hxA1 : x ∈ FTsupport1 M := by
      refine ⟨?_, hx1⟩
      rw [def_FTcore hM]
      exact hxSigma
    have hrFT : r ∈ FTsignalizer M x := by
      rw [← ftSupportPartition_signalizer_eq hM hxA1]
      exact hr
    have hcomm : Commute x r :=
      (Subgroup.mem_centralizer_iff.mp
        (cent_FT_signalizer x) r hr).symm
    refine ⟨x, hxA1, r * x, ?_, z, hz, ?_⟩
    · exact ⟨r, hrFT, x, Set.mem_singleton x, rfl⟩
    · rw [hcomm.eq]
  · rintro ⟨x, hxA1, a, ha, z, hz, rfl⟩
    rcases ha with ⟨r, hr, y, hy, rfl⟩
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    have hrGlobal : r ∈ ftSignalizer x := by
      rw [ftSupportPartition_signalizer_eq hM hxA1]
      exact hr
    have hcomm : Commute x r :=
      (Subgroup.mem_centralizer_iff.mp
        (cent_FT_signalizer x) r hrGlobal).symm
    refine ⟨x * r, ?_, z, hz, ?_⟩
    · refine ⟨x, ?_, hxA1.2, r, hrGlobal, rfl⟩
      rw [← def_FTcore hM]
      exact hxA1.1
    · rw [hcomm.eq]

private theorem ftSupportPartition_first_eq_of_ambient
    {M L : Subgroup G} (hML : FTAmbientConjugate M L) :
    FT_Dade1_support M = FT_Dade1_support L := by
  rcases hML with ⟨x, rfl⟩
  exact (FT_Dade1_supportJ M x).symm

private theorem ftSupportPartition_family_eq_cover :
    ftFirstDadeSupportFamily (G := G) =
      pTypeSupportCover (G := G) := by
  ext A
  constructor
  · rintro ⟨M, hMrep, rfl⟩
    have hM := (mmax_transversalP (G := G)).subset_maximal hMrep
    refine ⟨M, hM, ?_⟩
    exact ftSupportPartition_sigma_class_eq_first hM
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨L, hLrep, hML⟩ :=
      (mmax_transversalP (G := G)).representative hM
    have hconj := ftSupportPartition_ambient_of_within_top hML
    refine ⟨L, hLrep, ?_⟩
    exact (ftSupportPartition_first_eq_of_ambient hconj).symm.trans
      (ftSupportPartition_sigma_class_eq_first hM).symm

private theorem ftSupportPartition_class_disjoint
    {M L : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hL : L ∈ minSimple_max_groups (G := G))
    (hnot : ¬ FTAmbientConjugate M L) :
    Disjoint
      (classSupportWithin (⊤ : Subgroup G) (sigmaCover M))
      (classSupportWithin (⊤ : Subgroup G) (sigmaCover L)) := by
  apply Set.disjoint_left.2
  intro q hqM hqL
  rcases hqM with ⟨a, ha, x, -, rfl⟩
  rcases hqL with ⟨b, hb, y, -, hy⟩
  let Mx := conjugateSubgroup8 M x⁻¹
  let Ly := conjugateSubgroup8 L y⁻¹
  have hMx : Mx ∈ minSimple_max_groups (G := G) :=
    (mmaxJ M (MulAut.conj x⁻¹)).2 hM
  have hLy : Ly ∈ minSimple_max_groups (G := G) :=
    (mmaxJ L (MulAut.conj y⁻¹)).2 hL
  have hnotRaw : ∀ z : G,
      Ly ≠ Mx.map (MulAut.conj z).toMonoidHom := by
    intro z heq
    apply hnot
    have hMMx : FTAmbientConjugate M Mx := ⟨x⁻¹, rfl⟩
    have hMxLy : FTAmbientConjugate Mx Ly := ⟨z, heq⟩
    have hLLy : FTAmbientConjugate L Ly := ⟨y⁻¹, rfl⟩
    exact ftSupportPartition_ambient_trans
      (ftSupportPartition_ambient_trans hMMx hMxLy)
      (ftSupportPartition_ambient_symm hLLy)
  have hdis := sigma_support_disjoint hMx hLy hnotRaw
  apply Set.disjoint_left.mp hdis
  · change x⁻¹ * a * x ∈ sigmaCover Mx
    dsimp only [Mx]
    change x⁻¹ * a * x ∈
      sigmaCover (conjugateSubgroup16 M x⁻¹)
    rw [sigma_supportJ]
    exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  · change x⁻¹ * a * x ∈ sigmaCover Ly
    dsimp only [Ly]
    change x⁻¹ * a * x ∈
      sigmaCover (conjugateSubgroup16 L y⁻¹)
    rw [sigma_supportJ]
    refine ⟨b, hb, ?_⟩
    simpa [MulAut.conj_apply] using hy

/-! ## Peterfalvi Theorem 8.17 -/

/-- `PFsection8.v: FT_Dade_support_partition`, Peterfalvi Theorem 8.17. -/
theorem FT_Dade_support_partition :
    primeSupport (Nat.card G) =
        {p : Nat | ∃ M : Subgroup G,
          M ∈ minSimple_max_groups (G := G) ∧
            p ∈ primeSupport (Nat.card (ftCore M))} ∧
    (∀ {M L : Subgroup G},
      M ∈ minSimple_max_groups (G := G) →
      L ∈ minSimple_max_groups (G := G) →
      ¬ FTAmbientConjugate M L →
        Nat.Coprime (Nat.card (ftCore M)) (Nat.card (ftCore L))) ∧
    (∀ {M : Subgroup G},
      M ∈ minSimple_max_groups (G := G) →
        (FT_Dade1_support M).ncard =
          (Nat.card (ftCore M) - 1) * M.index) ∧
    let PG := ftFirstDadeSupportFamily (G := G)
    Set.InjOn FT_Dade1_support
        (mmax_transversal (⊤ : Subgroup G)) ∧
      (all_FTtype1 (G := G) →
        IsSetPartition PG (nonidentitySet G)) ∧
      ∀ (S T W W₁ W₂ : Subgroup G)
        (defW : IsInternalDirectProductIn W₁ W₂ W),
        typeP_pair S T W W₁ W₂ defW →
          IsSetPartition
              ({ftCyclicExceptionalSupport W W₁ W₂} ∪ PG)
              (nonidentitySet G) ∧
            ftCyclicExceptionalSupport W W₁ W₂ ∉ PG := by
  classical
  let summary := BGsummaryE (G := G)
  have hprime :
      primeSupport (Nat.card G) =
        {p : Nat | ∃ M : Subgroup G,
          M ∈ minSimple_max_groups (G := G) ∧
            p ∈ primeSupport (Nat.card (ftCore M))} := by
    ext p
    constructor
    · intro hp
      obtain ⟨M, hM, hpSigma⟩ := summary.prime_sigma hp
      refine ⟨M, hM, ?_⟩
      change p ∈ primeSupport (Nat.card (FTcore M))
      rw [def_FTcore hM, pi_Msigma hM]
      exact hpSigma
    · rintro ⟨M, -, hp⟩
      exact ⟨hp.1, hp.2.trans
        (natCard_subgroup_dvd_natCard (ftCore M))⟩
  have hcoprime : ∀ {M L : Subgroup G},
      M ∈ minSimple_max_groups (G := G) →
      L ∈ minSimple_max_groups (G := G) →
      ¬ FTAmbientConjugate M L →
        Nat.Coprime (Nat.card (ftCore M)) (Nat.card (ftCore L)) := by
    intro M L hM hL hnot
    have hdis := summary.sigma_disjoint hM hL hnot
    apply Nat.coprime_of_dvd
    intro p hp hpM hpL
    have hpSigmaM : p ∈ sigmaPrimes M := by
      rw [← pi_Msigma hM, ← def_FTcore hM]
      exact ⟨hp, hpM⟩
    have hpSigmaL : p ∈ sigmaPrimes L := by
      rw [← pi_Msigma hL, ← def_FTcore hL]
      exact ⟨hp, hpL⟩
    exact Set.disjoint_left.mp hdis hpSigmaM hpSigmaL
  have hcard : ∀ {M : Subgroup G},
      M ∈ minSimple_max_groups (G := G) →
        (FT_Dade1_support M).ncard =
          (Nat.card (ftCore M) - 1) * M.index := by
    intro M hM
    rw [← ftSupportPartition_sigma_class_eq_first hM,
      summary.support_card hM]
    change (Nat.card (sigmaCore M) - 1) * M.index =
      (Nat.card (FTcore M) - 1) * M.index
    rw [def_FTcore hM]
  have hinjective : Set.InjOn FT_Dade1_support
      (mmax_transversal (⊤ : Subgroup G)) := by
    intro M hMrep L hLrep hsupport
    let spec := mmax_transversalP (G := G)
    have hM := spec.subset_maximal hMrep
    have hL := spec.subset_maximal hLrep
    apply spec.conjugacy_injective hMrep hLrep
    by_contra hnotWithin
    have hnotAmbient : ¬ FTAmbientConjugate M L := by
      intro hconj
      exact hnotWithin
        (ftSupportPartition_within_top_of_ambient hconj)
    have hdis := ftSupportPartition_class_disjoint hM hL hnotAmbient
    obtain ⟨x, hx1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (Msigma_neq1 hM)
    have hxSigma : (x : G) ∈ sigmaCore M := x.property
    have hxG1 : (x : G) ≠ 1 := by
      intro hx
      exact hx1 (Subtype.ext hx)
    have hxCover : (x : G) ∈ sigmaCover M :=
      ⟨x, hxSigma, hxG1, 1, (ftSignalizer (x : G)).one_mem, by simp⟩
    have hxClassM :
        (x : G) ∈ classSupportWithin (⊤ : Subgroup G) (sigmaCover M) :=
      ⟨x, hxCover, 1, Subgroup.mem_top 1, by simp⟩
    have hclassEq :
        classSupportWithin (⊤ : Subgroup G) (sigmaCover M) =
          classSupportWithin (⊤ : Subgroup G) (sigmaCover L) :=
      (ftSupportPartition_sigma_class_eq_first hM).trans
        (hsupport.trans
          (ftSupportPartition_sigma_class_eq_first hL).symm)
    exact Set.disjoint_left.mp hdis hxClassM (hclassEq ▸ hxClassM)
  have hfamily := ftSupportPartition_family_eq_cover (G := G)
  have hallTypeOne : all_FTtype1 (G := G) →
      IsSetPartition (ftFirstDadeSupportFamily (G := G))
        (nonidentitySet G) := by
    intro htype
    have hPempty : typePMaximalSubgroups (G := G) = ∅ := by
      ext M
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hMP
      exact ((FTtype_Pmax hMP.1).mp hMP) (htype M hMP.1)
    rw [hfamily]
    exact (mFT_partition (G := G)).1 hPempty
  have hpairPartition : ∀ (S T W W₁ W₂ : Subgroup G)
      (defW : IsInternalDirectProductIn W₁ W₂ W),
      typeP_pair S T W W₁ W₂ defW →
        IsSetPartition
            ({ftCyclicExceptionalSupport W W₁ W₂} ∪
              ftFirstDadeSupportFamily (G := G))
            (nonidentitySet G) ∧
          ftCyclicExceptionalSupport W W₁ W₂ ∉
            ftFirstDadeSupportFamily (G := G) := by
    intro S T W W₁ W₂ defW hpair
    obtain ⟨U, hTypeP⟩ := typeP_pairW S T W W₁ W₂ defW hpair
    have hSnot1 := FTtypeP_neq1 S U W W₁ W₂ defW
      hpair.S_maximal hTypeP
    have hSP : S ∈ typePMaximalSubgroups (G := G) :=
      (FTtype_Pmax hpair.S_maximal).2 hSnot1
    obtain ⟨U₀, K, hCompl⟩ := kappa_witness hpair.S_maximal
    have hKne : K ≠ ⊥ := by
      intro hKbot
      have hF :=
        (trivg_kappa hpair.S_maximal hCompl.K_le_M hCompl.hall_K).1
          hKbot
      exact hSnot1 ((FTtype_Fmax hpair.S_maximal).1 hF)
    have hStructure := kappa_structure hpair.S_maximal hCompl
    have hleft : sigmaCore S ⊔ U₀ = derivedWithin S :=
      ftSupportPartition_semidirect_sup_eq
        (hStructure.derived_decomposition hKne)
    have hKdecomp :
        IsInternalSemidirectProductIn (derivedWithin S) K S := by
      rw [← hleft]
      exact hStructure.sigmaU_K_sdprod
    obtain ⟨x, hxS, hxK⟩ :=
      of_typeP_compl_conj S U W W₁ W₂ defW hTypeP K hKdecomp
    have hSfix : conjugateSubgroup8 S x⁻¹ = S :=
      conjugateSubgroup8_eq_self_of_mem_normalizer
        ((Subgroup.le_normalizer (S.inv_mem hxS)))
    have hKback : conjugateSubgroup8 K x⁻¹ = W₁ := by
      rw [← hxK]
      exact ftSupportPartition_conjugate_inv W₁ x
    have hHallW₁ : IsHall (kappaPrimes S) (W₁.subgroupOf S) := by
      have hmap := ftSupportPartition_isHall_subgroupOf_map
        hCompl.K_le_M hCompl.hall_K (MulAut.conj x⁻¹)
      change K.map (MulAut.conj x⁻¹).toMonoidHom = W₁ at hKback
      change S.map (MulAut.conj x⁻¹).toMonoidHom = S at hSfix
      rw [hKback, hSfix] at hmap
      exact hmap
    obtain ⟨V, hComplW₁⟩ :=
      ex_kappa_compl hpair.S_maximal hTypeP.1.2.1.1 hHallW₁
    have hSummary := BGsummaryC hpair.S_maximal hComplW₁
      hTypeP.1.2.2.1
    have hPartner : pTypePartner S W₁ = W₂ := by
      unfold pTypePartner
      apply le_antisymm
      · intro z hz
        have hzF : z ∈ Fitting_core S := hSummary.partner_le_Fcore hz
        have hzCent : z ∈ centralizerWithin (Fitting_core S) W₁ :=
          ⟨hzF, hz.2⟩
        rw [typeP_cent_core_compl S U W W₁ W₂ defW hTypeP] at hzCent
        exact hzCent
      · intro z hz
        have hzCent : z ∈ centralizerWithin (Fitting_core S) W₁ := by
          rw [typeP_cent_core_compl S U W W₁ W₂ defW hTypeP]
          exact hz
        exact ⟨Fcore_sub_Msigma hpair.S_maximal hzCent.1, hzCent.2⟩
    have hExceptional :
        ftCyclicExceptionalSupport W W₁ W₂ =
          pTypeExceptionalSupport S W₁ := by
      unfold ftCyclicExceptionalSupport pTypeExceptionalSupport
      congr 1
      unfold pTypeTISet pTypeJoin cyclicTISet
      rw [hPartner, ftSupportPartition_directProduct_sup_eq defW]
    rw [hfamily, hExceptional]
    exact (mFT_partition (G := G)).2 S W₁ hSP
      hTypeP.1.2.1.1 hHallW₁
  exact ⟨hprime, hcoprime, hcard,
    hinjective, hallTypeOne, hpairPartition⟩

/-! ## The first-support partition consequence -/

private theorem ftSupportPartition_first_disjoint
    {M L : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hL : L ∈ minSimple_max_groups (G := G))
    (hnot : ¬ FTAmbientConjugate M L) :
    Disjoint (FT_Dade1_support M) (FT_Dade1_support L) := by
  classical
  obtain ⟨R, hRrep, hMR⟩ :=
    (mmax_transversalP (G := G)).representative hM
  obtain ⟨Q, hQrep, hLQ⟩ :=
    (mmax_transversalP (G := G)).representative hL
  have hMRambient := ftSupportPartition_ambient_of_within_top hMR
  have hLQambient := ftSupportPartition_ambient_of_within_top hLQ
  have hRQ : R ≠ Q := by
    intro hRQ
    apply hnot
    exact ftSupportPartition_ambient_trans hMRambient
      (ftSupportPartition_ambient_symm (hRQ.symm ▸ hLQambient))
  rcases (FT_Dade_support_partition (G := G)) with
    ⟨-, -, -, hinj, hAllPartition, hPairPartition⟩
  have hsupportNe : FT_Dade1_support R ≠ FT_Dade1_support Q := by
    intro heq
    exact hRQ (hinj hRrep hQrep heq)
  have hdisRQ : Disjoint (FT_Dade1_support R) (FT_Dade1_support Q) := by
    rcases FTtypeP_pair_cases (G := G) with hAll | hPair
    · exact (hAllPartition hAll).2.1
        ⟨R, hRrep, rfl⟩ ⟨Q, hQrep, rfl⟩ hsupportNe
    · rcases hPair with
        ⟨S, T, U, W, W₁, W₂, defW, hpair⟩
      exact (hPairPartition S T W W₁ W₂ defW hpair).1.2.1
        (Or.inr ⟨R, hRrep, rfl⟩)
        (Or.inr ⟨Q, hQrep, rfl⟩) hsupportNe
  rw [ftSupportPartition_first_eq_of_ambient hMRambient,
    ftSupportPartition_first_eq_of_ambient hLQambient]
  exact hdisRQ

private theorem ftSupportPartition_support_subset_Dade
    (M : Subgroup G) (A : Set G) :
    A ⊆ FT_Dade_support M A := by
  intro x hx
  refine ⟨x, hx, x, ?_, 1, Subgroup.mem_top 1, by simp⟩
  exact ⟨1, (FTsignalizer M x).one_mem,
    x, Set.mem_singleton x, by simp⟩

private theorem ftSupportPartition_right_factor_zpowers
    {r x : G} (hcomm : Commute r x)
    (hcop : (orderOf r).Coprime (orderOf x)) :
    x ∈ Subgroup.zpowers (r * x) := by
  let e₀ := Nat.chineseRemainder hcop 0 1
  let e : ℕ := e₀
  have her : e ≡ 0 [MOD orderOf r] := e₀.property.1
  have hex : e ≡ 1 [MOD orderOf x] := e₀.property.2
  have hrpow : r ^ e = 1 := pow_eq_one_iff_modEq.mpr her
  have hxpow : x ^ e = x := by
    simpa using (pow_eq_pow_iff_modEq.mpr hex : x ^ e = x ^ 1)
  have hpow : (r * x) ^ e = x := by
    rw [hcomm.mul_pow, hrpow, hxpow, one_mul]
  have hmem : (r * x) ^ e ∈ Subgroup.zpowers (r * x) :=
    Subgroup.npow_mem_zpowers (r * x) e
  exact Eq.mp
    (congrArg (fun y : G ↦ y ∈ Subgroup.zpowers (r * x)) hpow)
    hmem

/-! ## Peterfalvi Lemma 8.18 -/

/-- `PFsection8.v: FT_Dade_support_disjoint`, Peterfalvi Lemma 8.18. -/
theorem FT_Dade_support_disjoint
    {S T : Subgroup G}
    (hS : S ∈ minSimple_max_groups (G := G))
    (hT : T ∈ minSimple_max_groups (G := G))
    (hnot : ¬ FTAmbientConjugate S T) :
    ((FTsupports S T ↔
        ¬ Disjoint (ftSupport1 S) (ftSupport T)) ∧
      ∀ x : G, x ∈ ftSupport1 S ∩ ftSupport T →
        ¬ centralizerOfElement8 x ≤ S ∧
          centralizerOfElement8 x ≤ T) ∧
    (((∃ x : G, FTsupports S (conjugateSubgroup8 T x)) ↔
        ¬ Disjoint (FT_Dade1_support S) (FT_Dade_full_support T)) ∧
      (Disjoint (FT_Dade1_support S) (FT_Dade_full_support T) ∨
        Disjoint (FT_Dade1_support T) (FT_Dade_full_support S))) := by
  classical
  have part_a2 : ∀ {M L : Subgroup G},
      M ∈ minSimple_max_groups (G := G) →
      L ∈ minSimple_max_groups (G := G) →
      ¬ FTAmbientConjugate M L →
      ∀ x : G, x ∈ ftSupport1 M ∩ ftSupport L →
        ¬ centralizerOfElement8 x ≤ M ∧
          centralizerOfElement8 x ≤ L := by
    intro M L hM hL hnotML x hx
    rcases hx with ⟨hxM1, hxL⟩
    rcases (FT_Dade_support_partition (G := G)) with
      ⟨-, hcoreCoprime, -, -, -, -⟩
    have hcopCore := hcoreCoprime hM hL hnotML
    have hcopOrder :
        (orderOf x).Coprime (Nat.card (ftCore L)) :=
      hcopCore.coprime_dvd_left
        ((ftCore M).orderOf_dvd_natCard hxM1.1)
    change x ∈ ftSupport L at hxL
    rcases Set.mem_iUnion.mp hxL with ⟨z, hxL⟩
    rcases Set.mem_iUnion.mp hxL with ⟨hzL1, hxCent⟩
    have hxNotCoreL : x ∉ ftCore L := by
      intro hxCoreL
      have horderOne : orderOf x = 1 :=
        Nat.eq_one_of_dvd_coprimes hcopOrder dvd_rfl
          ((ftCore L).orderOf_dvd_natCard hxCoreL)
      exact hxM1.2 (orderOf_eq_one_iff.mp horderOne)
    have htypeLe : FTtype L ≤ 2 := by
      by_contra hnotLe
      have hgt : 2 < FTtype L := by omega
      have hxL1 : x ∈ FTsupport1 L := by
        rw [← FTsupp_eq1 hL hgt]
        change x ∈ ftSupport L
        exact Set.mem_iUnion.2
          ⟨z, Set.mem_iUnion.2 ⟨hzL1, hxCent⟩⟩
      exact hxNotCoreL hxL1.1
    have htypePos : 0 < FTtype L := (FTtype_range L).1
    have htype12 : FTtype L = 1 ∨ FTtype L = 2 := by omega
    have hFcoreSigma : Fitting_core L = sigmaCore L :=
      ((Fcore_eq_FTcore hL).2
        (htype12.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))).trans
          (def_FTcore hL)
    obtain ⟨U, K, hCompl⟩ := kappa_witness hL
    have hsd := sdprod_FTder hL hCompl
    have hUOutside :
        IsPiNumber (sigmaKappaPrimes L)ᶜ (Nat.card U) := by
      simpa only [MathlibSupport.natCard_subgroupOf_eq hCompl.U_le_M] using
        hCompl.hall_U.isPiNumber_card
    let pi := (primeSupport (Nat.card (sigmaCore L)))ᶜ
    have hHallU : IsHall pi (U.subgroupOf (FTder L)) := by
      constructor
      · rw [MathlibSupport.natCard_subgroupOf_eq hsd.2.1]
        intro p hp hpU hpSigma
        have hpOutside := hUOutside hp hpU
        exact hpOutside (Or.inl (by
          rw [← pi_Msigma hL]
          exact hpSigma))
      · dsimp only [pi]
        rw [hsd.2.2.2.index_eq_card,
          MathlibSupport.natCard_subgroupOf_eq hsd.1]
        simpa only [compl_compl] using
          (IsPiNumber.primeSupport_self :
            IsPiNumber (primeSupport (Nat.card (sigmaCore L)))
              (Nat.card (sigmaCore L)))
    have hcopSigma :
        (orderOf x).Coprime (Nat.card (sigmaCore L)) := by
      simpa [← def_FTcore hL] using hcopOrder
    have hxPi : IsPiNumber pi (Nat.card (Subgroup.zpowers x)) := by
      rw [Nat.card_zpowers]
      intro p hp hpOrder hpSigma
      exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp, hpOrder, hpSigma.2⟩) hcopSigma
    have hFTderL : FTder L ≤ L := ftSupportPartition_ftDer_le L
    have hsolFTder : IsSolvable (FTder L) := by
      letI : IsSolvable L := mmax_sol hL
      exact isSolvable_of_injective
        (Subgroup.inclusion hFTderL) (Subgroup.inclusion_injective hFTderL)
    obtain ⟨y, hcycleUy, hUyFT, -, -, -, -⟩ :=
      exists_ambient_isHall_map_conj_ge_of_isSolvable
        (Subgroup.zpowers_le.mpr hxCent.1.1) hsd.2.1
        hsolFTder hxPi hHallU
    let Uy := conjugateSubgroup8 U (y : G)
    have hSigmaNorm :
        L ≤ Subgroup.normalizer (sigmaCore L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le L)).1
        (sigmaCore_normal L)
    have hSigmaFix : conjugateSubgroup8 (sigmaCore L) (y : G) =
        sigmaCore L :=
      conjugateSubgroup8_eq_self_of_mem_normalizer
        (hSigmaNorm (hFTderL y.property))
    have hFTderFix : conjugateSubgroup8 (FTder L) (y : G) = FTder L :=
      conjugateSubgroup8_eq_self_of_mem_normalizer
        (Subgroup.le_normalizer y.property)
    have hsdUy :
        IsInternalSemidirectProductIn (sigmaCore L) Uy (FTder L) := by
      have hmap := semidirect_map_mulEquiv8 hsd
        (MulAut.conj (y : G))
      change (sigmaCore L).map (MulAut.conj (y : G)).toMonoidHom =
        sigmaCore L at hSigmaFix
      change (FTder L).map (MulAut.conj (y : G)).toMonoidHom =
        FTder L at hFTderFix
      rw [hSigmaFix, hFTderFix] at hmap
      exact hmap
    have hterm :
        derivedSeriesWithin8 L (FTtype L - 1) = FTder L := by
      rcases htype12 with htype1 | htype2
      · simp [derivedSeriesWithin8, FTder, ftDerived, htype1,
          ← MonoidHom.range_eq_map, L.range_subtype]
      · simp [derivedSeriesWithin8, FTder, ftDerived, htype2,
          derivedWithin]
    have hdecomp : IsInternalSemidirectProductIn
        (Fitting_core L) Uy
        (derivedSeriesWithin8 L (FTtype L - 1)) := by
      rw [hFcoreSigma, hterm]
      exact hsdUy
    have hFacts := FTtypeI_II_facts (FTtype L) L Uy hL rfl
      hdecomp ⟨htypePos, htypeLe⟩
    have hxUy : x ∈ Uy :=
      hcycleUy (Subgroup.mem_zpowers x)
    have hXsub : ({x} : Set G) ⊆ subgroupNonidentity Uy := by
      intro a ha
      have hax : a = x := Set.mem_singleton_iff.mp ha
      subst a
      exact ⟨hxUy, hxM1.2⟩
    have hzF : z ∈ Fitting_core L := by
      rw [hFcoreSigma, ← def_FTcore hL]
      exact hzL1.1
    have hzCentClosure :
        z ∈ centralizerWithin (Fitting_core L)
          (Subgroup.closure ({x} : Set G)) := by
      refine ⟨hzF, ?_⟩
      show z ∈ Subgroup.centralizer
        (Subgroup.closure ({x} : Set G) : Set G)
      rw [Subgroup.centralizer_closure]
      apply Subgroup.mem_centralizer_iff.mpr
      intro a ha
      have hax : a = x := Set.mem_singleton_iff.mp ha
      subst a
      exact (hxCent.1.2 z (Subgroup.mem_zpowers z)).symm
    have hcentNe : centralizerWithin (Fitting_core L)
        (Subgroup.closure ({x} : Set G)) ≠ ⊥ := by
      intro hbot
      exact hzL1.2 (Subgroup.mem_bot.mp (hbot ▸ hzCentClosure))
    have huniq0 := hFacts.subgroup_centralizer_unique
      ({x} : Set G) (Set.singleton_nonempty x) hXsub hcentNe
    have huniq : minSimple_max_groups_of (G := G)
        (centralizerOfElement8 x : Set G) = {L} := by
      simpa only [centralizerOfElement8, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure] using huniq0
    have hLmem : L ∈ minSimple_max_groups_of (G := G)
        (centralizerOfElement8 x : Set G) := by
      rw [huniq]
      exact Set.mem_singleton L
    refine ⟨?_, hLmem.2⟩
    intro hcentM
    have hMmem : M ∈ minSimple_max_groups_of (G := G)
        (centralizerOfElement8 x : Set G) := ⟨hM, hcentM⟩
    have hML : M = L := by
      rw [huniq] at hMmem
      exact Set.mem_singleton_iff.mp hMmem
    apply hnotML
    subst L
    exact ftSupportPartition_ambient_refl M
  have part_a1 : ∀ {M L : Subgroup G},
      M ∈ minSimple_max_groups (G := G) →
      L ∈ minSimple_max_groups (G := G) →
      ¬ FTAmbientConjugate M L →
        (FTsupports M L ↔
          ¬ Disjoint (ftSupport1 M) (ftSupport L)) := by
    intro M L hM hL hnotML
    constructor
    · rintro ⟨x, hxM, hCxM, hCxL⟩ hdis
      let facts := FTsupport_facts M hM
      have hxOuter : x ∈ outerExceptionalSet M (FTsupport0 M) :=
        ⟨FTsupp_sub0 M hxM, hCxM⟩
      have hxM1 := facts.exceptional_subset_support1 hxOuter
      let data := facts.element_data x hxOuter
      have hLmem : L ∈ minSimple_max_groups_of (G := G)
          (elementCentralizer x : Set G) := ⟨hL, hCxL⟩
      have hLN : L = elementNormalizer15 x := by
        rw [data.unique_maximal_centralizer] at hLmem
        exact Set.mem_singleton_iff.mp hLmem
      have hxL : x ∈ FTsupport L := by
        rw [hLN]
        exact data.support_not_support1.1
      exact Set.disjoint_left.mp hdis hxM1 hxL
    · intro hnotDis
      rw [Set.not_disjoint_iff] at hnotDis
      obtain ⟨x, hxM1, hxL⟩ := hnotDis
      have hcontrol := part_a2 hM hL hnotML x ⟨hxM1, hxL⟩
      exact ⟨x, FTsupp1_sub hM hxM1, hcontrol.1, hcontrol.2⟩
  have part_b : ∀ {M L : Subgroup G},
      M ∈ minSimple_max_groups (G := G) →
      L ∈ minSimple_max_groups (G := G) →
      ¬ FTAmbientConjugate M L →
        ((∃ x : G, FTsupports M (conjugateSubgroup8 L x)) ↔
          ¬ Disjoint (FT_Dade1_support M)
            (FT_Dade_full_support L)) := by
    intro M L hM hL hnotML
    constructor
    · rintro ⟨a, hsupp⟩ hdis
      have hLa : conjugateSubgroup8 L a ∈
          minSimple_max_groups (G := G) :=
        (mmaxJ L (MulAut.conj a)).2 hL
      have hnotMLa : ¬ FTAmbientConjugate M (conjugateSubgroup8 L a) := by
        intro hconj
        apply hnotML
        exact ftSupportPartition_ambient_trans hconj
          (ftSupportPartition_ambient_symm ⟨a, rfl⟩)
      have hraw := (part_a1 hM hLa hnotMLa).1 hsupp
      rw [Set.not_disjoint_iff] at hraw
      obtain ⟨x, hxM, hxLa⟩ := hraw
      have hxDM : x ∈ FT_Dade1_support M :=
        ftSupportPartition_support_subset_Dade M (FTsupport1 M) hxM
      have hxDLa : x ∈ FT_Dade_full_support (conjugateSubgroup8 L a) :=
        ftSupportPartition_support_subset_Dade
          (conjugateSubgroup8 L a) (FTsupport (conjugateSubgroup8 L a)) hxLa
      rw [FT_Dade_supportJ L a] at hxDLa
      exact Set.disjoint_left.mp hdis hxDM hxDLa
    · intro hnotDis
      rw [Set.not_disjoint_iff] at hnotDis
      obtain ⟨q, hqM, hqL⟩ := hnotDis
      rcases hqM with ⟨x₁, hx₁M, u, hu, a, -, hua⟩
      rcases hqL with ⟨x₂, hx₂L, v, hv, b, -, hvb⟩
      by_cases hcent₂ : centralizerOfElement8 x₂ ≤ L
      · rw [FTsignalizer, if_pos hcent₂] at hv
        rcases hv with ⟨r₂, hr₂, y₂, hy₂, rfl⟩
        have hr₂one : r₂ = 1 := Subgroup.mem_bot.mp hr₂
        have hy₂x₂ : y₂ = x₂ := Set.mem_singleton_iff.mp hy₂
        subst r₂
        subst y₂
        simp only [one_mul] at hvb
        rcases hu with ⟨r, hr, y₁, hy₁, rfl⟩
        have hy₁x₁ : y₁ = x₁ := Set.mem_singleton_iff.mp hy₁
        subst y₁
        let c : G := a * b⁻¹
        have hconj : (MulAut.conj c) x₂ = r * x₁ := by
          rw [MulAut.conj_apply]
          dsimp only [c]
          calc
            (a * b⁻¹) * x₂ * (a * b⁻¹)⁻¹ =
                a * (b⁻¹ * x₂ * b) * a⁻¹ := by group
            _ = a * q * a⁻¹ := by rw [hvb]
            _ = r * x₁ := by rw [← hua]; group
        have hrDade : r ∈ DadeSignalizer (FT_Dade1_hyp M hM) x₁ := by
          rw [def_FTsignalizer1 M hM hx₁M]
          exact hr
        have hcomm : Commute r x₁ :=
          (Dade_signalizer_cent (FT_Dade1_hyp M hM)
            x₁ hrDade x₁ (Subgroup.mem_zpowers x₁)).symm
        have hx₁CM : x₁ ∈ elementCentralizerWithin M x₁ := by
          refine ⟨FTcore_sub M hx₁M.1, ?_⟩
          intro z hz
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          exact ((Commute.refl x₁).zpow_left n).eq
        have hcop := Dade_coprime (FT_Dade1_hyp M hM) hx₁M hx₁M
        have hcopOrder : (orderOf r).Coprime (orderOf x₁) :=
          (hcop.coprime_dvd_left
            ((DadeSignalizer (FT_Dade1_hyp M hM) x₁).orderOf_dvd_natCard
              hrDade)).coprime_dvd_right
                ((elementCentralizerWithin M x₁).orderOf_dvd_natCard hx₁CM)
        have hx₁pow : x₁ ∈ Subgroup.zpowers (r * x₁) :=
          ftSupportPartition_right_factor_zpowers hcomm hcopOrder
        let Lc := conjugateSubgroup8 L c
        have hLc : Lc ∈ minSimple_max_groups (G := G) :=
          (mmaxJ L (MulAut.conj c)).2 hL
        have hnotMLc : ¬ FTAmbientConjugate M Lc := by
          intro hconjMLc
          apply hnotML
          exact ftSupportPartition_ambient_trans hconjMLc
            (ftSupportPartition_ambient_symm ⟨c, rfl⟩)
        have hprodSupport : r * x₁ ∈ FTsupport Lc := by
          dsimp only [Lc]
          change r * x₁ ∈ FTsupport (conjugateSubgroup16 L c)
          rw [FTsuppJ L c]
          exact ⟨x₂, hx₂L, hconj⟩
        change r * x₁ ∈ ftSupport Lc at hprodSupport
        rcases Set.mem_iUnion.mp hprodSupport with ⟨z, hprodSupport⟩
        rcases Set.mem_iUnion.mp hprodSupport with ⟨hzLc1, hprodCent⟩
        have hx₁Der : x₁ ∈ FTder Lc :=
          (Subgroup.zpowers_le.mpr hprodCent.1.1) hx₁pow
        have hx₁Cent : x₁ ∈ elementCentralizerWithin (FTder Lc) z := by
          refine ⟨hx₁Der, ?_⟩
          intro t ht
          have hcommProd : Commute t (r * x₁) :=
            hprodCent.1.2 t ht
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx₁pow
          rw [← hn]
          exact (hcommProd.zpow_right n).eq
        have hx₁Lc : x₁ ∈ FTsupport Lc := by
          change x₁ ∈ ftSupport Lc
          exact Set.mem_iUnion.2
            ⟨z, Set.mem_iUnion.2
              ⟨hzLc1, ⟨hx₁Cent, hx₁M.2⟩⟩⟩
        have hraw : ¬ Disjoint (FTsupport1 M) (FTsupport Lc) := by
          rw [Set.not_disjoint_iff]
          exact ⟨x₁, hx₁M, hx₁Lc⟩
        exact ⟨c, (part_a1 hM hLc hnotMLc).2 hraw⟩
      · have hx₂Outer : x₂ ∈ outerExceptionalSet L (FTsupport0 L) :=
          ⟨FTsupp_sub0 L hx₂L, hcent₂⟩
        have hx₂L1 :=
          (FTsupport_facts L hL).exceptional_subset_support1 hx₂Outer
        have hqL1 : q ∈ FT_Dade1_support L :=
          ⟨x₂, hx₂L1, v, hv, b, Subgroup.mem_top b, hvb⟩
        have hqM1 : q ∈ FT_Dade1_support M :=
          ⟨x₁, hx₁M, u, hu, a, Subgroup.mem_top a, hua⟩
        exact (Set.disjoint_left.mp
          (ftSupportPartition_first_disjoint hM hL hnotML) hqM1 hqL1).elim
  have no_reverse_of_support : ∀ {M L : Subgroup G},
      M ∈ minSimple_max_groups (G := G) →
      L ∈ minSimple_max_groups (G := G) →
      ¬ FTAmbientConjugate M L →
      FTsupports M L →
        ∀ x : G, ¬ FTsupports L (conjugateSubgroup8 M x) := by
    intro M L hM hL hnotML hsupp x hsuppReverse
    rcases hsupp with ⟨y, hyM, hCyM, hCyL⟩
    let facts := FTsupport_facts M hM
    have hyOuter : y ∈ outerExceptionalSet M (FTsupport0 M) :=
      ⟨FTsupp_sub0 M hyM, hCyM⟩
    let data := facts.element_data y hyOuter
    have hLmem : L ∈ minSimple_max_groups_of (G := G)
        (elementCentralizer y : Set G) := ⟨hL, hCyL⟩
    have hLN : L = elementNormalizer15 y := by
      rw [data.unique_maximal_centralizer] at hLmem
      exact Set.mem_singleton_iff.mp hLmem
    have htypeL : FTtype L = 1 ∨ FTtype L = 2 := by
      rw [hLN]
      exact data.type_one_or_two
    have hFcoreL : Fitting_core L = FTcore L :=
      (Fcore_eq_FTcore hL).2
        (htypeL.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))
    let Mx := conjugateSubgroup8 M x
    have hMx : Mx ∈ minSimple_max_groups (G := G) :=
      (mmaxJ M (MulAut.conj x)).2 hM
    have hnotLMx : ¬ FTAmbientConjugate L Mx := by
      intro hconj
      apply hnotML
      exact ftSupportPartition_ambient_symm
        (ftSupportPartition_ambient_trans hconj
          (ftSupportPartition_ambient_symm ⟨x, rfl⟩))
    have hrawReverse := (part_a1 hL hMx hnotLMx).1 hsuppReverse
    apply hrawReverse
    apply Set.disjoint_left.2
    intro q hqL1 hqMx
    dsimp only [Mx] at hqMx
    change q ∈ FTsupport (conjugateSubgroup16 M x) at hqMx
    rw [FTsuppJ M x] at hqMx
    rcases hqMx with ⟨z, hzM, rfl⟩
    change z ∈ ftSupport M at hzM
    rcases Set.mem_iUnion.mp hzM with ⟨a, hzM⟩
    rcases Set.mem_iUnion.mp hzM with ⟨haM1, hzCent⟩
    let C := elementCentralizerWithin (FTder M) a
    let e : G ≃* G := MulAut.conj x
    have hzMap : e z ∈ C.map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hzCent.1
    have hCle : C ≤ elementCentralizerWithin M a :=
      centralizerWithin_mono_left (ftSupportPartition_ftDer_le M)
    have hcopLarge : Nat.Coprime (Nat.card (Fitting_core L))
        (Nat.card (elementCentralizerWithin M a)) := by
      rw [hLN]
      exact data.centralizer_coprime a (FTsupp1_sub0 hM haM1)
    have hcopSmall : Nat.Coprime (Nat.card (Fitting_core L))
        (Nat.card C) :=
      hcopLarge.coprime_dvd_right (Subgroup.card_dvd_of_le hCle)
    have hqF : e z ∈ Fitting_core L := by
      rw [hFcoreL]
      exact hqL1.1
    have horderF : orderOf (e z) ∣ Nat.card (Fitting_core L) :=
      (Fitting_core L).orderOf_dvd_natCard hqF
    have horderC : orderOf (e z) ∣ Nat.card C := by
      have hmapOrder := (C.map e.toMonoidHom).orderOf_dvd_natCard hzMap
      have hcard : Nat.card (C.map e.toMonoidHom) = Nat.card C :=
        Subgroup.card_map_of_injective e.injective
      rw [hcard] at hmapOrder
      exact hmapOrder
    have horderOne : orderOf (e z) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcopSmall horderF horderC
    exact hqL1.2 (orderOf_eq_one_iff.mp horderOne)
  have horiented :
      Disjoint (FT_Dade1_support S) (FT_Dade_full_support T) ∨
        Disjoint (FT_Dade1_support T) (FT_Dade_full_support S) := by
    by_cases hST : Disjoint (FT_Dade1_support S) (FT_Dade_full_support T)
    · exact Or.inl hST
    by_cases hTS : Disjoint (FT_Dade1_support T) (FT_Dade_full_support S)
    · exact Or.inr hTS
    exfalso
    obtain ⟨x, hsuppSTx⟩ := (part_b hS hT hnot).2 hST
    let Tx := conjugateSubgroup8 T x
    have hTx : Tx ∈ minSimple_max_groups (G := G) :=
      (mmaxJ T (MulAut.conj x)).2 hT
    have hnotSTx : ¬ FTAmbientConjugate S Tx := by
      intro hconj
      apply hnot
      exact ftSupportPartition_ambient_trans hconj
        (ftSupportPartition_ambient_symm ⟨x, rfl⟩)
    have hnotTxS : ¬ FTAmbientConjugate Tx S := by
      exact fun h ↦ hnotSTx (ftSupportPartition_ambient_symm h)
    have hTSx : ¬ Disjoint (FT_Dade1_support Tx)
        (FT_Dade_full_support S) := by
      rw [FT_Dade1_supportJ T x]
      exact hTS
    obtain ⟨z, hsuppReverse⟩ :=
      (part_b hTx hS hnotTxS).2 hTSx
    exact no_reverse_of_support hS hTx hnotSTx hsuppSTx z hsuppReverse
  exact ⟨⟨part_a1 hS hT hnot, part_a2 hS hT hnot⟩,
    ⟨part_b hS hT hnot, horiented⟩⟩

/-! ## First-support corollary -/

/-- `PFsection8.v: FT_Dade1_support_disjoint`.

First Dade supports of nonconjugate maximal subgroups are disjoint. -/
theorem FT_Dade1_support_disjoint
    {S T : Subgroup G}
    (hS : S ∈ minSimple_max_groups (G := G))
    (hT : T ∈ minSimple_max_groups (G := G))
    (hnot : ¬ FTAmbientConjugate S T) :
    Disjoint (FT_Dade1_support S) (FT_Dade1_support T) :=
  ftSupportPartition_first_disjoint hS hT hnot

end

end Submission.OddOrder.PF
