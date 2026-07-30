import Submission.OddOrder.BG.Section16.TypeClassification
import Submission.OddOrder.BG.Section16.SupportConjugation

/-!
# Bender--Glauberman Section 16: support consequences

This compatibility facade re-exports the Section 16 type-classification and
support-conjugation phases, and proves the remaining support inclusions and
nontriviality statements used by downstream sections.
-/

namespace Submission.OddOrder.BG.Section16

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

private theorem core_le_ftDerived
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTcore M ≤ FTder M := by
  by_cases h1 : FTtype M = 1
  · simpa [FTder, ftDerived, h1] using FTcore_sub M
  · simpa [FTder, ftDerived, h1] using FTcore_sub_der1 hM

private theorem mem_own_centralizerWithin
    {D : Subgroup G} {x : G} (hxD : x ∈ D) :
    x ∈ elementCentralizerWithin D x := by
  refine ⟨hxD, ?_⟩
  intro z hz
  rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
  exact ((Commute.refl x).zpow_left n).eq

/-- `BGsection16.v: FTsupp1_sub`. -/
theorem FTsupp1_sub
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTsupport1 M ⊆ FTsupport M := by
  classical
  rintro x ⟨hxCore, hxne⟩
  simp only [FTsupport, ftSupport, Set.mem_iUnion]
  refine ⟨x, ⟨hxCore, hxne⟩, ?_⟩
  exact ⟨mem_own_centralizerWithin (core_le_ftDerived hM hxCore), hxne⟩

/-- `BGsection16.v: FTsupp1_sub0`. -/
theorem FTsupp1_sub0
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTsupport1 M ⊆ FTsupport0 M :=
  (FTsupp1_sub hM).trans (FTsupp_sub0 M)

/-- `BGsection16.v: FTsupp1_neq0`. -/
theorem FTsupp1_neq0
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTsupport1 M ≠ ∅ := by
  obtain ⟨x, hxne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (FTcore_neq1 hM)
  have hxne' : (x : G) ≠ 1 := fun hx ↦ hxne (Subtype.ext hx)
  exact Set.nonempty_iff_ne_empty.mp ⟨x, x.property, hxne'⟩

/-- `BGsection16.v: FTsupp_neq0`. -/
theorem FTsupp_neq0
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTsupport M ≠ ∅ := by
  exact Set.nonempty_iff_ne_empty.mp
    ((Set.nonempty_iff_ne_empty.mpr (FTsupp1_neq0 hM)).mono (FTsupp1_sub hM))

/-- `BGsection16.v: FTsupp0_neq0`. -/
theorem FTsupp0_neq0
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTsupport0 M ≠ ∅ := by
  exact Set.nonempty_iff_ne_empty.mp
    ((Set.nonempty_iff_ne_empty.mpr (FTsupp_neq0 hM)).mono (FTsupp_sub0 M))

/-- `BGsection16.v: Fcore_sub_FTsupp1`. -/
theorem Fcore_sub_FTsupp1
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    subgroupNonidentity (Fitting_core M) ⊆ FTsupport1 M := by
  rintro x ⟨hx, hxne⟩
  exact ⟨Fcore_sub_FTcore hM hx, hxne⟩

/-- `BGsection16.v: Fcore_sub_FTsupp`. -/
theorem Fcore_sub_FTsupp
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    subgroupNonidentity (Fitting_core M) ⊆ FTsupport M :=
  (Fcore_sub_FTsupp1 hM).trans (FTsupp1_sub hM)

/-- `BGsection16.v: Fcore_sub_FTsupp0`. -/
theorem Fcore_sub_FTsupp0
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    subgroupNonidentity (Fitting_core M) ⊆ FTsupport0 M :=
  (Fcore_sub_FTsupp1 hM).trans (FTsupp1_sub0 hM)

private theorem fittingWithin_le_ftDerived
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hfit : FittingStructure M) :
    fittingWithin M ≤ FTder M := by
  by_cases hP : M ∈ typePMaximalSubgroups (G := G)
  · have hne : FTtype M ≠ 1 := (FTtype_Pmax hM).mp hP
    simpa [FTder, ftDerived, hne] using hfit.typeP_fitting_le_derived hP
  · have h1 : FTtype M = 1 := by
      by_contra hne
      exact hP ((FTtype_Pmax hM).mpr hne)
    simpa [FTder, ftDerived, h1] using fittingWithin_le M

private theorem fitting_core_mul_centralizer
    {M : Subgroup G}
    (hfit : FittingStructure M)
    {z : G} (hz : z ∈ fittingWithin M) :
    ∃ a ∈ Fitting_core M,
      ∃ b ∈ centralizerWithin M (Fitting_core M), a * b = z := by
  let H := Fitting_core M
  let C := centralizerWithin M H
  have hcomm : ∀ a ∈ H, ∀ b ∈ C, Commute a b := by
    simpa only [H, C] using hfit.Fcore_centralizer_commute
  have hHC : H ≤ Subgroup.centralizer (C : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm a ha b hb).eq.symm
  have hnorm : H ≤ Subgroup.normalizer (C : Set G) :=
    hHC.trans (Subgroup.centralizer_le_normalizer (C : Set G))
  have hzSup : z ∈ H ⊔ C := by
    rw [hfit.Fcore_join_centralizer]
    exact hz
  have hzMul : z ∈ (H : Set G) * (C : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H C hnorm]
    exact hzSup
  rcases hzMul with ⟨a, ha, b, hb, hab⟩
  exact ⟨a, ha, b, hb, hab⟩

/-- `BGsection16.v: Fitting_sub_FTsupp`. -/
theorem Fitting_sub_FTsupp
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    subgroupNonidentity (fittingWithin M) ⊆ FTsupport M := by
  classical
  have hfit := Fitting_structure hM
  rintro xy ⟨hxyFit, hxyNe⟩
  obtain ⟨a, ha, b, hb, hab⟩ :=
    fitting_core_mul_centralizer hfit hxyFit
  have hcomm : ∀ z ∈ Fitting_core M,
      ∀ c ∈ centralizerWithin M (Fitting_core M), Commute z c :=
    hfit.Fcore_centralizer_commute
  obtain ⟨z, hzCore, hzNe, hzComm⟩ :
      ∃ z : G, z ∈ Fitting_core M ∧ z ≠ 1 ∧ Commute z xy := by
    by_cases ha1 : a = 1
    · obtain ⟨z, hzNeSubtype⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp (mmax_Fcore_neq1 hM)
      have hzNe : (z : G) ≠ 1 := fun hz ↦ hzNeSubtype (Subtype.ext hz)
      refine ⟨z, z.property, hzNe, ?_⟩
      rw [← hab, ha1, one_mul]
      exact hcomm z z.property b hb
    · refine ⟨a, ha, ha1, ?_⟩
      rw [← hab]
      exact (Commute.refl a).mul_right (hcomm a ha b hb)
  simp only [FTsupport, ftSupport, Set.mem_iUnion]
  refine ⟨z, ⟨Fcore_sub_FTcore hM hzCore, hzNe⟩, ?_⟩
  refine ⟨⟨fittingWithin_le_ftDerived hM hfit hxyFit, ?_⟩, hxyNe⟩
  intro w hw
  rcases Subgroup.mem_zpowers_iff.mp hw with ⟨n, rfl⟩
  exact (hzComm.zpow_left n).eq

/-- `BGsection16.v: Fitting_sub_FTsupp0`. -/
theorem Fitting_sub_FTsupp0
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    subgroupNonidentity (fittingWithin M) ⊆ FTsupport0 M :=
  (Fitting_sub_FTsupp hM).trans (FTsupp_sub0 M)

/-- `BGsection16.v: FTsupp_eq1`. -/
theorem FTsupp_eq1
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hgt : 2 < FTtype M) :
    FTsupport M = FTsupport1 M := by
  apply Set.Subset.antisymm
  · intro y hy
    simp only [FTsupport, ftSupport, Set.mem_iUnion] at hy
    rcases hy with ⟨x, hxCore, hy⟩
    have hder : FTder M = FTcore M := by
      have hne : FTtype M ≠ 1 := by omega
      simpa [FTder, ftDerived, hne] using (FTcore_eq_der1 hM hgt).symm
    exact ⟨hder ▸ hy.1.1, hy.2⟩
  · exact FTsupp1_sub hM

end

end Submission.OddOrder.BG.Section16
