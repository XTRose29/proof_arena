import Submission.OddOrder.BG.Section16.TypeDefinitions

/-!
# Bender--Glauberman Section 16: type classification

This module classifies maximal subgroups by the kappa-complement data and
identifies the Feit--Thompson core with the sigma core.
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

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## Kappa complements and preliminary maximal-subgroup types -/

/-- `BGsection16.v: trivgFmax`. -/
theorem trivgFmax
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) :
    M ∈ typeFMaximalSubgroups (G := G) ↔ K = ⊥ :=
  (trivg_kappa hM hCompl.K_le_M hCompl.hall_K).symm

/-- `BGsection16.v: trivgPmax`. -/
theorem trivgPmax
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) :
    M ∈ typePMaximalSubgroups (G := G) ↔ K ≠ ⊥ := by
  simp only [typePMaximalSubgroups, Set.mem_diff, hM, true_and,
    trivgFmax hM hCompl]

/-- `BGsection16.v: FmaxP`. -/
theorem FmaxP
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) :
    M ∈ typeFMaximalSubgroups (G := G) ↔ K = ⊥ ∧ U ≠ ⊥ := by
  constructor
  · intro hF
    refine ⟨(trivgFmax hM hCompl).mp hF, ?_⟩
    intro hU
    have hP1 : M ∈ typeP1MaximalSubgroups (G := G) :=
      (trivg_kappa_compl hM hCompl).mp hU
    exact hP1.1.2 hF
  · exact fun h ↦ (trivgFmax hM hCompl).mpr h.1

/-- `BGsection16.v: P1maxP`. -/
theorem P1maxP
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) :
    M ∈ typeP1MaximalSubgroups (G := G) ↔ K ≠ ⊥ ∧ U = ⊥ := by
  constructor
  · intro hP1
    refine ⟨?_, (trivg_kappa_compl hM hCompl).mpr hP1⟩
    intro hK
    exact hP1.1.2 ((trivgFmax hM hCompl).mpr hK)
  · exact fun h ↦ (trivg_kappa_compl hM hCompl).mp h.2

/-- `BGsection16.v: P2maxP`. -/
theorem P2maxP
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) :
    M ∈ typeP2MaximalSubgroups (G := G) ↔ K ≠ ⊥ ∧ U ≠ ⊥ := by
  constructor
  · rintro ⟨hP, hnotP1⟩
    refine ⟨(trivgPmax hM hCompl).mp hP, ?_⟩
    intro hU
    exact hnotP1 ((trivg_kappa_compl hM hCompl).mp hU)
  · rintro ⟨hK, hU⟩
    refine ⟨(trivgPmax hM hCompl).mpr hK, ?_⟩
    intro hP1
    exact hU ((trivg_kappa_compl hM hCompl).mpr hP1)

/-! ## Numerical Feit--Thompson type -/

/-- Every maximal subgroup has a kappa complement. -/
theorem kappa_witness
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    ∃ U K : Subgroup G, KappaComplement M U K := by
  obtain ⟨K, hKle, hKHall⟩ :=
    Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
      (mmax_sol hM) (kappaPrimes M)
  obtain ⟨U, hCompl⟩ := ex_kappa_compl hM hKle hKHall
  exact ⟨U, K, hCompl⟩

/-- `BGsection16.v: FTtype_Fmax`, Lemma 16.1(a). -/
theorem FTtype_Fmax
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    M ∈ typeFMaximalSubgroups (G := G) ↔ FTtype M = 1 := by
  classical
  rw [show M ∈ typeFMaximalSubgroups (G := G) ↔
      IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) by
    simp [typeFMaximalSubgroups, hM]]
  change IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) ↔ ftType M = 1
  unfold ftType
  split_ifs <;> simp_all

/-- The complementary preliminary class consists exactly of types other than
one. -/
theorem FTtype_Pmax
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    M ∈ typePMaximalSubgroups (G := G) ↔ FTtype M ≠ 1 := by
  simp [typePMaximalSubgroups, hM, FTtype_Fmax hM]

private theorem semidirect_right_bot_iff_left_top
    {A B K : Subgroup G}
    (h : IsInternalSemidirectProductIn A B K) :
    B = ⊥ ↔ A = K := by
  constructor
  · intro hB
    apply le_antisymm h.1
    have htop := h.2.2.2.sup_eq_top
    rw [hB, Subgroup.bot_subgroupOf, sup_bot_eq] at htop
    exact Subgroup.subgroupOf_eq_top.mp htop
  · intro hA
    have hcomp := h.2.2.2
    rw [hA, Subgroup.subgroupOf_self] at hcomp
    have hBsub : B.subgroupOf K = ⊥ :=
      Subgroup.isComplement'_top_left.mp hcomp
    have hBK : Disjoint B K := Subgroup.subgroupOf_eq_bot.mp hBsub
    exact le_antisymm ((le_inf le_rfl h.2.1).trans hBK.le_bot) bot_le

/-- `BGsection16.v: FTtype_P2max`, Lemma 16.1(b). -/
theorem FTtype_P2max
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    M ∈ typeP2MaximalSubgroups (G := G) ↔ FTtype M = 2 := by
  obtain ⟨U, K, hCompl⟩ := kappa_witness hM
  have hStructure := kappa_structure hM hCompl
  constructor
  · intro hP2
    have hKU := (P2maxP hM hCompl).mp hP2
    have hnotF : ¬ IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) :=
      fun hpi ↦ hP2.1.2 ⟨hM, hpi⟩
    have hnotEq : sigmaCore M ≠ derivedWithin M := by
      intro hEq
      have hsd := hStructure.derived_decomposition hKU.1
      exact hKU.2 ((semidirect_right_bot_iff_left_top hsd).mpr hEq)
    simp [FTtype, ftType, hnotF, hnotEq]
  · intro hType
    have hnotF : ¬ IsPiNumber (kappaPrimes M)ᶜ (Nat.card M) := by
      intro hpi
      have hTypeOne : FTtype M = 1 := by simp [FTtype, ftType, hpi]
      omega
    have hnotEq : sigmaCore M ≠ derivedWithin M := by
      intro hEq
      have hImpossible := hType
      simp [FTtype, ftType, hnotF, hEq] at hImpossible
      split_ifs at hImpossible <;> omega
    have hP : M ∈ typePMaximalSubgroups (G := G) :=
      ⟨hM, fun hF ↦ hnotF hF.2⟩
    refine ⟨hP, ?_⟩
    intro hP1
    have hU : U = ⊥ := (trivg_kappa_compl hM hCompl).mpr hP1
    have hK : K ≠ ⊥ := ((P1maxP hM hCompl).mp hP1).1
    exact hnotEq ((semidirect_right_bot_iff_left_top
      (hStructure.derived_decomposition hK)).mp hU)

/-- `BGsection16.v: FTtype_P1max`, Lemma 16.1(c,d), P1 part. -/
theorem FTtype_P1max
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    M ∈ typeP1MaximalSubgroups (G := G) ↔
      2 < FTtype M ∧ FTtype M ≤ 5 := by
  constructor
  · intro hP1
    have hnotOne : FTtype M ≠ 1 := (FTtype_Pmax hM).mp hP1.1
    have hnotTwo : FTtype M ≠ 2 := fun hTwo ↦
      ((FTtype_P2max hM).mpr hTwo).2 hP1
    have hRange := FTtype_range M
    omega
  · rintro ⟨hgt, _⟩
    have hP : M ∈ typePMaximalSubgroups (G := G) :=
      (FTtype_Pmax hM).mpr (by omega)
    by_contra hnotP1
    have hP2 : M ∈ typeP2MaximalSubgroups (G := G) := ⟨hP, hnotP1⟩
    have hTwo := (FTtype_P2max hM).mp hP2
    omega

/-! ## Identification and normalizers of the alternative core -/

/-- `BGsection16.v: Msigma_eq_der1`. -/
theorem Msigma_eq_der1
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hP1 : M ∈ typeP1MaximalSubgroups (G := G)) :
    sigmaCore M = derivedWithin M := by
  obtain ⟨U, K, hCompl⟩ := kappa_witness hM
  have hData := (P1maxP hM hCompl).mp hP1
  have hsd := (kappa_structure hM hCompl).derived_decomposition hData.1
  exact (semidirect_right_bot_iff_left_top hsd).mp hData.2

/-- `BGsection16.v: def_FTcore`: for a maximal subgroup the alternative
core is its sigma core. -/
theorem def_FTcore
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTcore M = sigmaCore M := by
  by_cases hSmall : FTtype M ≤ 2
  · have hnotP1 : M ∉ typeP1MaximalSubgroups (G := G) := by
      intro hP1
      exact (Nat.not_lt_of_ge hSmall) ((FTtype_P1max hM).mp hP1).1
    have hNotP1Type :
        M ∈ typeFMaximalSubgroups (G := G) ∪
          typeP2MaximalSubgroups (G := G) := by
      by_cases hF : M ∈ typeFMaximalSubgroups (G := G)
      · exact Or.inl hF
      · exact Or.inr ⟨⟨hM, hF⟩, hnotP1⟩
    have hSigmaNil : Group.IsNilpotent (sigmaCore M) :=
      notP1type_Msigma_nil hNotP1Type
    have hFitSigma : Fitting_core M = sigmaCore M :=
      (Fcore_eq_Msigma hM).mpr hSigmaNil
    have hCoreFit : FTcore M = Fitting_core M := by
      simp [FTcore, ftCore, (FTtype_range M).1, hSmall]
    exact hCoreFit.trans hFitSigma
  · have hLarge : 2 < FTtype M := Nat.lt_of_not_ge hSmall
    have hP1 : M ∈ typeP1MaximalSubgroups (G := G) :=
      (FTtype_P1max hM).mpr ⟨hLarge, (FTtype_range M).2⟩
    exact (FTcore_type_gt2 M hLarge).trans (Msigma_eq_der1 hM hP1).symm

/-- `BGsection16.v: FTcore_sub_der1`. -/
theorem FTcore_sub_der1
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTcore M ≤ derivedWithin M := by
  rw [def_FTcore hM]
  exact Msigma_der1 hM

/-- `BGsection16.v: Fcore_sub_FTcore`. -/
theorem Fcore_sub_FTcore
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Fitting_core M ≤ FTcore M := by
  rw [def_FTcore hM]
  exact Fcore_sub_Msigma hM

/-- `BGsection16.v: mmax_Fcore_neq1`. -/
theorem mmax_Fcore_neq1
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Fitting_core M ≠ ⊥ :=
  (Fcore_structure hM).Fcore_ne_bot

/-- `BGsection16.v: mmax_Fitting_neq1`. -/
theorem mmax_Fitting_neq1
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    fittingWithin M ≠ ⊥ := by
  intro hFitting
  apply mmax_Fcore_neq1 hM
  apply le_antisymm
  · simpa [hFitting] using Fcore_sub_Fitting M
  · exact bot_le

/-- `BGsection16.v: FTcore_neq1`. -/
theorem FTcore_neq1
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    FTcore M ≠ ⊥ := by
  intro hCore
  apply mmax_Fcore_neq1 hM
  apply le_antisymm
  · simpa [hCore] using Fcore_sub_FTcore hM
  · exact bot_le

/-- `BGsection16.v: norm_mmax_Fcore`. -/
theorem norm_mmax_Fcore
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Subgroup.normalizer (Fitting_core M : Set G) = M :=
  mmax_normal hM (Fcore_sub M) (Fcore_normal M) (mmax_Fcore_neq1 hM)

/-- `BGsection16.v: norm_FTcore`. -/
theorem norm_FTcore
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Subgroup.normalizer (FTcore M : Set G) = M :=
  mmax_normal hM (FTcore_normal M).1 (FTcore_normal M).2 (FTcore_neq1 hM)

/-- `BGsection16.v: norm_mmax_Fitting`. -/
theorem norm_mmax_Fitting
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Subgroup.normalizer (fittingWithin M : Set G) = M :=
  mmax_normal hM (fittingWithin_le M) (fittingWithin_subgroupOf_normal M)
    (mmax_Fitting_neq1 hM)

/-! ## Equality cases for the Fitting and alternative cores -/

/-- `BGsection16.v: Fcore_eq_FTcore`, Lemma 16.1(f). -/
theorem Fcore_eq_FTcore
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Fitting_core M = FTcore M ↔
      FTtype M = 1 ∨ FTtype M = 2 ∨ FTtype M = 5 := by
  classical
  constructor
  · intro hCores
    have hFitSigma : Fitting_core M = sigmaCore M :=
      hCores.trans (def_FTcore hM)
    by_cases hPi : IsPiNumber (kappaPrimes M)ᶜ (Nat.card M)
    · exact Or.inl (by simp [FTtype, ftType, hPi])
    by_cases hSigma : sigmaCore M ≠ derivedWithin M
    · exact Or.inr (Or.inl (by simp [FTtype, ftType, hPi, hSigma]))
    · exact Or.inr (Or.inr (by
        simp [FTtype, ftType, hPi, hSigma, hFitSigma]))
  · rintro (hOne | hTwo | hFive)
    · exact (FTcore_type1 M hOne).symm
    · exact (FTcore_type2 M hTwo).symm
    · have hFitSigma : Fitting_core M = sigmaCore M := by
        by_contra hne
        have hFive' := hFive
        change ftType M = 5 at hFive'
        unfold ftType at hFive'
        split_ifs at hFive' <;> simp_all
      exact hFitSigma.trans (def_FTcore hM).symm

/-- `BGsection16.v: Fcore_neq_FTcore`, Lemma 16.1(c), second part. -/
theorem Fcore_neq_FTcore
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G)) :
    Fitting_core M ≠ FTcore M ↔
      FTtype M = 3 ∨ FTtype M = 4 := by
  constructor
  · intro hne
    have hRange := FTtype_range M
    have hNotEqualType :
        ¬ (FTtype M = 1 ∨ FTtype M = 2 ∨ FTtype M = 5) :=
      fun h ↦ hne ((Fcore_eq_FTcore hM).mpr h)
    omega
  · intro hType hEq
    have hEqualType := (Fcore_eq_FTcore hM).mp hEq
    omega

/-- `BGsection16.v: FTcore_eq_der1`. -/
theorem FTcore_eq_der1
    {M : Subgroup G}
    (_hM : M ∈ minSimple_max_groups (G := G))
    (hgt : 2 < FTtype M) :
    FTcore M = derivedWithin M :=
  FTcore_type_gt2 M hgt

end

end Submission.OddOrder.BG.Section16
