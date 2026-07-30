import Submission.OddOrder.PF.Section01.IrreducibleCharacterTransport
import Submission.OddOrder.PF.Section01.OddConjugateIrreducible
import Submission.OddOrder.PF.Section02.DadeRestriction
import Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset
import Submission.OddOrder.PF.Section08.FTSupportFacts

/-!
# Peterfalvi Section 8: the FT Dade construction

This module builds the canonical Dade hypothesis from the outer FT support,
restricts it to the three support sets used later, identifies the resulting
signalizers and supports, and proves conjugation invariance of the explicit
FT Dade supports.
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
open scoped BigOperators Classical Pointwise IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## Conjugation covariance of the FT signalizer -/

private theorem map_centralizerWithin_equiv
    (D S : Subgroup G) (e : G ≃* G) :
    (centralizerWithin D S).map e.toMonoidHom =
      centralizerWithin (D.map e.toMonoidHom) (S.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mpr hy.1, ?_⟩
    intro z hz
    have hz' : e.symm z ∈ S := Subgroup.mem_map_equiv.mp hz
    simpa using congrArg e (hy.2 (e.symm z) hz')
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mp hy.1, ?_⟩
    intro z hz
    have hz' : e z ∈ S.map e.toMonoidHom :=
      (Subgroup.mem_map_iff_mem e.injective).mpr hz
    simpa using congrArg e.symm (hy.2 (e z) hz')

private theorem map_centralizer_equiv
    (A : Subgroup G) (e : G ≃* G) :
    (Subgroup.centralizer (A : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (A.map e.toMonoidHom : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : e.symm z ∈ A := Subgroup.mem_map_equiv.mp hz
    simpa using congrArg e
      (Subgroup.mem_centralizer_iff.mp hy (e.symm z) hz')
  · intro hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : e z ∈ A.map e.toMonoidHom :=
      (Subgroup.mem_map_iff_mem e.injective).mpr hz
    simpa using congrArg e.symm
      (Subgroup.mem_centralizer_iff.mp hy (e z) hz')

private theorem elementNormalizer_conj (y x : G) :
    elementNormalizer15 ((MulAut.conj x) y) =
      conjugateSubgroup8 (elementNormalizer15 y) x := by
  simpa only [elementNormalizer15, conjugateSubgroup8] using
    (FT_signalizer_baseJ y x)

/-- Conjugation covariance of the Peterfalvi signalizer. -/
theorem FTsignalizerJ (M : Subgroup G) (x y : G) :
    FTsignalizer (conjugateSubgroup8 M x) ((MulAut.conj x) y) =
      conjugateSubgroup8 (FTsignalizer M y) x := by
  let e : G ≃* G := MulAut.conj x
  have hcent :
      centralizerOfElement8 (e y) =
        conjugateSubgroup8 (centralizerOfElement8 y) x := by
    change Subgroup.centralizer (Subgroup.zpowers (e y) : Set G) =
      (Subgroup.centralizer (Subgroup.zpowers y : Set G)).map e.toMonoidHom
    have hey : e.toMonoidHom y = e y := rfl
    rw [← hey, ← MonoidHom.map_zpowers e.toMonoidHom y]
    exact (map_centralizer_equiv (Subgroup.zpowers y) e).symm
  unfold FTsignalizer
  rw [hcent]
  by_cases hle : centralizerOfElement8 y ≤ M
  · have hle' :
        conjugateSubgroup8 (centralizerOfElement8 y) x ≤
          conjugateSubgroup8 M x :=
      (Subgroup.map_le_map_iff_of_injective e.injective).mpr hle
    rw [if_pos hle', if_pos hle]
    simp [conjugateSubgroup8]
  · have hle' :
        ¬ conjugateSubgroup8 (centralizerOfElement8 y) x ≤
          conjugateSubgroup8 M x := by
      intro h
      exact hle ((Subgroup.map_le_map_iff_of_injective e.injective).mp h)
    rw [if_neg hle', if_neg hle]
    have hN := elementNormalizer_conj y x
    have hmap := map_centralizerWithin_equiv
      (Fitting_core (elementNormalizer15 y)) (Subgroup.zpowers y) e
    rw [hN]
    change centralizerWithin
        (Fitting_core ((elementNormalizer15 y).map e.toMonoidHom))
        (Subgroup.zpowers (e y)) =
      (centralizerWithin (Fitting_core (elementNormalizer15 y))
        (Subgroup.zpowers y)).map e.toMonoidHom
    have hey : e.toMonoidHom y = e y := rfl
    rw [← hey, FcoreJ, ← MonoidHom.map_zpowers e.toMonoidHom y]
    exact hmap.symm

/-! ## The four Dade hypotheses and their signalizers -/

private theorem isFTSignalizer (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    IsDadeSignalizer (⊤ : Subgroup G) M (FTsupport0 M)
      (FTsignalizer M) := by
  intro a ha
  by_cases hcent : centralizerOfElement8 a ≤ M
  · have hCM :
        centralizerWithin M (Subgroup.zpowers a) =
          centralizerOfElement8 a := by
      apply le_antisymm
      · exact inf_le_right
      · intro z hz
        exact ⟨hcent hz, hz⟩
    have hCG :
        centralizerWithin (⊤ : Subgroup G) (Subgroup.zpowers a) =
          centralizerOfElement8 a := by
      simp [centralizerWithin]
    rw [FTsignalizer, if_pos hcent, hCM, hCG]
    refine ⟨bot_le, le_rfl, ?_, ?_⟩
    · rw [Subgroup.bot_subgroupOf]
      infer_instance
    · rw [Subgroup.bot_subgroupOf]
      exact Subgroup.isComplement'_bot_left.mpr
        (Subgroup.subgroupOf_eq_top.mpr le_rfl)
  · have hdata := (FTsupport_facts M hM).element_data a ⟨ha, hcent⟩
    rw [FTsignalizer, if_neg hcent]
    simpa [centralizerWithin] using hdata.centralizer_decomposition

/-- The outer FT support satisfies the Dade hypothesis. -/
theorem FT_Dade0_hyp (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    DadeHypothesis (⊤ : Subgroup G) M (FTsupport0 M) := by
  let facts := FTsupport_facts M hM
  refine ⟨⟨?_, ?_⟩, le_top, ?_, ?_, FTsignalizer M, ?_, ?_⟩
  · intro x hx
    exact (FTsupp0_sub M hx).1
  · rw [norm_FTsupp0 M hM]
  · intro hOne
    exact (FTsupp0_sub M hOne).2 rfl
  · intro x hx y hy hxy
    rcases hxy with ⟨g, _hg, rfl⟩
    have hy' : conjugateElement16 x g⁻¹ ∈ FTsupport0 M := by
      simpa [conjugateElement16, MulAut.conj_apply] using hy
    obtain ⟨z, hzM, hz⟩ := facts.fusion_control x hx g⁻¹ hy'
    refine ⟨z⁻¹, M.inv_mem hzM, ?_⟩
    simpa [conjugateElement16, MulAut.conj_apply] using hz.symm
  · exact isFTSignalizer M hM
  · intro a ha b hb
    by_cases hcent : centralizerOfElement8 a ≤ M
    · rw [FTsignalizer, if_pos hcent, Subgroup.card_bot]
      exact Nat.coprime_one_left _
    · have hdata := (FTsupport_facts M hM).element_data a ⟨ha, hcent⟩
      have hcop := hdata.centralizer_coprime b hb
      rw [FTsignalizer, if_neg hcent]
      exact hcop.coprime_dvd_left
        (Subgroup.card_dvd_of_le
          (centralizerWithin_le_left
            (Fitting_core (elementNormalizer15 a))
            (Subgroup.zpowers a)))

/-- Restriction of the outer hypothesis to the full FT support. -/
noncomputable def FT_Dade_hyp (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    DadeHypothesis (⊤ : Subgroup G) M (FTsupport M) :=
  restr_Dade_hyp (FT_Dade0_hyp M hM)
    (FTsupp_sub0 M) (FTsupp_norm M)

/-- Restriction of the outer hypothesis to the first FT support. -/
noncomputable def FT_Dade1_hyp (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    DadeHypothesis (⊤ : Subgroup G) M (FTsupport1 M) :=
  restr_Dade_hyp (FT_Dade0_hyp M hM)
    (FTsupp1_sub0 hM) (FTsupp1_norm M)

private theorem normalizes_nonidentity
    {K M : Subgroup G}
    (h : M ≤ Subgroup.normalizer (K : Set G)) :
    M ≤ Subgroup.normalizer (subgroupNonidentity K) := by
  intro g hg
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro y
  have hK := Subgroup.mem_set_normalizer_iff.mp (h hg) y
  simp only [mem_subgroupNonidentity]
  constructor
  · rintro ⟨hyK, hy1⟩
    exact ⟨hK.mp hyK, by
      intro hconj
      apply hy1
      calc
        y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [hconj]; simp⟩
  · rintro ⟨hyK, hconj1⟩
    exact ⟨hK.mpr hyK, by
      intro hy1
      subst y
      simpa using hconj1⟩

/-- Restriction of the outer hypothesis to the nonidentity Fitting core. -/
noncomputable def FT_DadeF_hyp (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    DadeHypothesis (⊤ : Subgroup G) M
      (subgroupNonidentity (Fitting_core M)) := by
  have hFNorm : M ≤ Subgroup.normalizer (Fitting_core M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
      (Fcore_normal M)
  exact restr_Dade_hyp (FT_Dade0_hyp M hM)
    (Fcore_sub_FTsupp0 hM) (normalizes_nonidentity hFNorm)

/-- The canonical signalizer of the outer FT Dade hypothesis. -/
theorem def_FTsignalizer0 (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    {a : G} (ha : a ∈ FTsupport0 M) :
    DadeSignalizer (FT_Dade0_hyp M hM) a = FTsignalizer M a :=
  def_Dade_signalizer (FT_Dade0_hyp M hM)
    (FTsignalizer M) (isFTSignalizer M hM) ha

/-- The canonical signalizer after restriction to `FTsupport M`. -/
theorem def_FTsignalizer (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    {a : G} (ha : a ∈ FTsupport M) :
    DadeSignalizer (FT_Dade_hyp M hM) a = FTsignalizer M a := by
  simpa [FT_Dade_hyp] using
    (restr_Dade_signalizer (FT_Dade0_hyp M hM)
      (FTsupp_sub0 M) (FTsupp_norm M) (FTsignalizer M)
      (fun {_a} ha0 ↦ def_FTsignalizer0 M hM ha0) ha)

/-- The canonical signalizer after restriction to `FTsupport1 M`. -/
theorem def_FTsignalizer1 (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    {a : G} (ha : a ∈ FTsupport1 M) :
    DadeSignalizer (FT_Dade1_hyp M hM) a = FTsignalizer M a := by
  simpa [FT_Dade1_hyp] using
    (restr_Dade_signalizer (FT_Dade0_hyp M hM)
      (FTsupp1_sub0 hM) (FTsupp1_norm M) (FTsignalizer M)
      (fun {_a} ha0 ↦ def_FTsignalizer0 M hM ha0) ha)

/-- The canonical signalizer after restriction to the nonidentity Fitting core. -/
theorem def_FTsignalizerF (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    {a : G} (ha : a ∈ subgroupNonidentity (Fitting_core M)) :
    DadeSignalizer (FT_DadeF_hyp M hM) a = FTsignalizer M a := by
  have hFNorm : M ≤ Subgroup.normalizer (Fitting_core M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
      (Fcore_normal M)
  simpa [FT_DadeF_hyp] using
    (restr_Dade_signalizer (FT_Dade0_hyp M hM)
      (Fcore_sub_FTsupp0 hM) (normalizes_nonidentity hFNorm)
      (FTsignalizer M)
      (fun {_a} ha0 ↦ def_FTsignalizer0 M hM ha0) ha)

/-! ## Agreement of the restricted Dade maps -/

/-- The full-support restriction agrees with the outer Dade map. -/
theorem FT_DadeE (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (alpha : ClassFunction M ℂ)
    (halpha : alpha ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M}) :
    Dade (FT_Dade_hyp M hM) alpha =
      Dade (FT_Dade0_hyp M hM) alpha := by
  simpa [FT_Dade_hyp, restr_Dade] using
    (restr_DadeE (FT_Dade0_hyp M hM)
      (FTsupp_sub0 M) (FTsupp_norm M) alpha halpha)

/-- The first-support restriction agrees with the outer Dade map. -/
theorem FT_Dade1E (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (alpha : ClassFunction M ℂ)
    (halpha : alpha ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport1 M}) :
    Dade (FT_Dade1_hyp M hM) alpha =
      Dade (FT_Dade0_hyp M hM) alpha := by
  simpa [FT_Dade1_hyp, restr_Dade] using
    (restr_DadeE (FT_Dade0_hyp M hM)
      (FTsupp1_sub0 hM) (FTsupp1_norm M) alpha halpha)

/-- The Fitting-core restriction agrees with the outer Dade map. -/
theorem FT_DadeF_E (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (alpha : ClassFunction M ℂ)
    (halpha : alpha ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ subgroupNonidentity (Fitting_core M)}) :
    Dade (FT_DadeF_hyp M hM) alpha =
      Dade (FT_Dade0_hyp M hM) alpha := by
  have hFNorm : M ≤ Subgroup.normalizer (Fitting_core M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
      (Fcore_normal M)
  simpa [FT_DadeF_hyp, restr_Dade] using
    (restr_DadeE (FT_Dade0_hyp M hM)
      (Fcore_sub_FTsupp0 hM) (normalizes_nonidentity hFNorm)
      alpha halpha)

/-! ## Identification of Dade supports -/

/-- The outer Dade support is the explicit outer FT Dade support. -/
theorem FT_Dade0_supportE (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Dade_support (FT_Dade0_hyp M hM) = FT_Dade0_support M := by
  ext g
  constructor
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, ha, ?_⟩
    change g ∈ classSupportWithin (⊤ : Subgroup G)
      ((DadeSignalizer (FT_Dade0_hyp M hM) a : Set G) * ({a} : Set G)) at hg
    change g ∈ classSupportWithin (⊤ : Subgroup G)
      ((FTsignalizer M a : Set G) * ({a} : Set G))
    rwa [def_FTsignalizer0 M hM ha] at hg
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, ha, ?_⟩
    change g ∈ classSupportWithin (⊤ : Subgroup G)
      ((DadeSignalizer (FT_Dade0_hyp M hM) a : Set G) * ({a} : Set G))
    change g ∈ classSupportWithin (⊤ : Subgroup G)
      ((FTsignalizer M a : Set G) * ({a} : Set G)) at hg
    rwa [def_FTsignalizer0 M hM ha]

private theorem restricted_support_eq (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (A : Set G) (hA0 : A ⊆ FTsupport0 M)
    (hNorm : M ≤ Subgroup.normalizer A) :
    Dade_support (restr_Dade_hyp (FT_Dade0_hyp M hM) hA0 hNorm) =
      FT_Dade_support M A := by
  ext g
  constructor
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, ha, ?_⟩
    change g ∈ classSupportWithin (⊤ : Subgroup G)
      ((DadeSignalizer
          (restr_Dade_hyp (FT_Dade0_hyp M hM) hA0 hNorm) a : Set G) *
        ({a} : Set G)) at hg
    change g ∈ classSupportWithin (⊤ : Subgroup G)
      ((FTsignalizer M a : Set G) * ({a} : Set G))
    rwa [restr_Dade_signalizer (FT_Dade0_hyp M hM)
      hA0 hNorm (FTsignalizer M)
      (fun {_a} ha0 ↦ def_FTsignalizer0 M hM ha0) ha] at hg
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, ha, ?_⟩
    change g ∈ classSupportWithin (⊤ : Subgroup G)
      ((DadeSignalizer
          (restr_Dade_hyp (FT_Dade0_hyp M hM) hA0 hNorm) a : Set G) *
        ({a} : Set G))
    change g ∈ classSupportWithin (⊤ : Subgroup G)
      ((FTsignalizer M a : Set G) * ({a} : Set G)) at hg
    rwa [restr_Dade_signalizer (FT_Dade0_hyp M hM)
      hA0 hNorm (FTsignalizer M)
      (fun {_a} ha0 ↦ def_FTsignalizer0 M hM ha0) ha]

/-- The Dade support after restriction to `FTsupport M`. -/
theorem FT_Dade_supportE (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Dade_support (FT_Dade_hyp M hM) = FT_Dade_full_support M := by
  simpa [FT_Dade_hyp] using
    (restricted_support_eq M hM (FTsupport M)
      (FTsupp_sub0 M) (FTsupp_norm M))

/-- The Dade support after restriction to `FTsupport1 M`. -/
theorem FT_Dade1_supportE (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Dade_support (FT_Dade1_hyp M hM) = FT_Dade1_support M := by
  simpa [FT_Dade1_hyp] using
    (restricted_support_eq M hM (FTsupport1 M)
      (FTsupp1_sub0 hM) (FTsupp1_norm M))

/-- The Dade support after restriction to the nonidentity Fitting core. -/
theorem FT_DadeF_supportE (M : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Dade_support (FT_DadeF_hyp M hM) =
      FT_Dade_support M (subgroupNonidentity (Fitting_core M)) := by
  have hFNorm : M ≤ Subgroup.normalizer (Fitting_core M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
      (Fcore_normal M)
  simpa [FT_DadeF_hyp] using
    (restricted_support_eq M hM
      (subgroupNonidentity (Fitting_core M))
      (Fcore_sub_FTsupp0 hM) (normalizes_nonidentity hFNorm))

/-! ## Conjugation invariance of the explicit supports -/

private theorem classSupport_top_conjugate
    (S : Set G) (x : G) :
    classSupportWithin (⊤ : Subgroup G) (conjugateSet8 S x) =
      classSupportWithin (⊤ : Subgroup G) S := by
  ext g
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, k, _hk, rfl⟩
    refine ⟨s, hs, x⁻¹ * k, by simp, ?_⟩
    dsimp [MulAut.conj_apply]
    group
  · rintro ⟨s, hs, k, _hk, rfl⟩
    refine ⟨(MulAut.conj x) s, ⟨s, hs, rfl⟩, x * k, by simp, ?_⟩
    dsimp [MulAut.conj_apply]
    group

private theorem signalizerCoset_conj (M : Subgroup G) (x y : G) :
    conjugateSet8 ((FTsignalizer M y : Set G) * ({y} : Set G)) x =
      (FTsignalizer (conjugateSubgroup8 M x) ((MulAut.conj x) y) : Set G) *
        ({(MulAut.conj x) y} : Set G) := by
  rw [FTsignalizerJ]
  unfold conjugateSet8 conjugateSubgroup8
  rw [Set.image_mul, Subgroup.coe_map, Set.image_singleton]
  change
    ((MulAut.conj x).toMonoidHom '' (FTsignalizer M y : Set G)) *
        ({(MulAut.conj x) y} : Set G) =
      ((MulAut.conj x).toMonoidHom '' (FTsignalizer M y : Set G)) *
        ({(MulAut.conj x) y} : Set G)
  rfl

private theorem dadeSupport_conj (M : Subgroup G) (A : Set G) (x : G) :
    FT_Dade_support (conjugateSubgroup8 M x) (conjugateSet8 A x) =
      FT_Dade_support M A := by
  ext g
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hg⟩
    refine ⟨a, ha, ?_⟩
    rw [← signalizerCoset_conj M x a] at hg
    rwa [classSupport_top_conjugate] at hg
  · rintro ⟨a, ha, hg⟩
    refine ⟨(MulAut.conj x) a, ⟨a, ha, rfl⟩, ?_⟩
    rw [← signalizerCoset_conj M x a]
    rwa [classSupport_top_conjugate]

/-- Conjugation invariance of the outer FT Dade support. -/
theorem FT_Dade0_supportJ (M : Subgroup G) (x : G) :
    FT_Dade0_support (conjugateSubgroup8 M x) = FT_Dade0_support M := by
  have hs : FTsupport0 (conjugateSubgroup8 M x) =
      conjugateSet8 (FTsupport0 M) x := by
    simpa only [conjugateSubgroup8, conjugateSet8, conjugateSubgroup16,
      conjugateSet] using FTsupp0J M x
  change FT_Dade_support (conjugateSubgroup8 M x)
      (FTsupport0 (conjugateSubgroup8 M x)) =
    FT_Dade_support M (FTsupport0 M)
  rw [hs]
  exact dadeSupport_conj M (FTsupport0 M) x

/-- Conjugation invariance of the first FT Dade support. -/
theorem FT_Dade1_supportJ (M : Subgroup G) (x : G) :
    FT_Dade1_support (conjugateSubgroup8 M x) = FT_Dade1_support M := by
  have hs : FTsupport1 (conjugateSubgroup8 M x) =
      conjugateSet8 (FTsupport1 M) x := by
    simpa only [conjugateSubgroup8, conjugateSet8, conjugateSubgroup16,
      conjugateSet] using FTsupp1J M x
  change FT_Dade_support (conjugateSubgroup8 M x)
      (FTsupport1 (conjugateSubgroup8 M x)) =
    FT_Dade_support M (FTsupport1 M)
  rw [hs]
  exact dadeSupport_conj M (FTsupport1 M) x

/-- Conjugation invariance of the full FT Dade support. -/
theorem FT_Dade_supportJ (M : Subgroup G) (x : G) :
    FT_Dade_full_support (conjugateSubgroup8 M x) =
      FT_Dade_full_support M := by
  have hs : FTsupport (conjugateSubgroup8 M x) =
      conjugateSet8 (FTsupport M) x := by
    simpa only [conjugateSubgroup8, conjugateSet8, conjugateSubgroup16,
      conjugateSet] using FTsuppJ M x
  change FT_Dade_support (conjugateSubgroup8 M x)
      (FTsupport (conjugateSubgroup8 M x)) =
    FT_Dade_support M (FTsupport M)
  rw [hs]
  exact dadeSupport_conj M (FTsupport M) x

end

end Submission.OddOrder.PF
