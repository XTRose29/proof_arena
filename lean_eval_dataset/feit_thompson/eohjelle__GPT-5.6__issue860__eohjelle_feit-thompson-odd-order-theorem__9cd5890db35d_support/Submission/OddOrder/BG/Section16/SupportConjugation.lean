import Submission.OddOrder.BG.Section16.TypeDefinitions

/-!
# Bender--Glauberman Section 16: conjugation and normalization of supports

This module proves that the Section 16 type, core, and support constructions
are invariant under conjugation, and records their basic containment and
normalization properties.
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
open scoped Pointwise IsMulCommutative commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

abbrev conjugateSubgroup16 (M : Subgroup G) (x : G) : Subgroup G :=
  M.map (MulAut.conj x).toMonoidHom

/-! ## Transport of the type and core -/

private theorem derivedWithin_map_equiv16
    (M : Subgroup G) (e : G ≃* G) :
    derivedWithin (M.map e.toMonoidHom) =
      (derivedWithin M).map e.toMonoidHom := by
  let eM : M ≃* M.map e.toMonoidHom := e.subgroupMap M
  have hcomm :
      (_root_.commutator M).map eM.toMonoidHom =
        _root_.commutator (M.map e.toMonoidHom) := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr eM.surjective]
    rfl
  unfold derivedWithin
  rw [← hcomm, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem map_equiv_eq_iff16
    (A B : Subgroup G) (e : G ≃* G) :
    A.map e.toMonoidHom = B.map e.toMonoidHom ↔ A = B := by
  constructor
  · intro h
    apply le_antisymm
    · exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h.le
    · exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h.ge
  · exact congrArg (fun K : Subgroup G ↦ K.map e.toMonoidHom)

/-- `BGsection16.v: FTtypeJ`. -/
theorem FTtypeJ (M : Subgroup G) (x : G) :
    FTtype (conjugateSubgroup16 M x) = FTtype M := by
  classical
  let e : G ≃* G := MulAut.conj x
  have hkappa :
      kappaPrimes (M.map e.toMonoidHom) = kappaPrimes M := by
    ext p
    simpa [e] using (kappaJ M x (p := p))
  have hcard : Nat.card (M.map e.toMonoidHom) = Nat.card M :=
    Subgroup.card_map_of_injective e.injective
  have hsigma :
      sigmaCore (M.map e.toMonoidHom) =
        (sigmaCore M).map e.toMonoidHom := by
    simpa [e] using sigmaCore_conj M x
  have hderived :
      derivedWithin (M.map e.toMonoidHom) =
        (derivedWithin M).map e.toMonoidHom :=
    derivedWithin_map_equiv16 M e
  have hfitting :
      Fitting_core (M.map e.toMonoidHom) =
        (Fitting_core M).map e.toMonoidHom :=
    Fitting_core_map_mulEquiv M e
  have hsigmaDerived :
      sigmaCore (M.map e.toMonoidHom) =
          derivedWithin (M.map e.toMonoidHom) ↔
        sigmaCore M = derivedWithin M := by
    rw [hsigma, hderived]
    exact map_equiv_eq_iff16 (sigmaCore M) (derivedWithin M) e
  have hsigmaDerivedNe :
      sigmaCore (M.map e.toMonoidHom) ≠
          derivedWithin (M.map e.toMonoidHom) ↔
        sigmaCore M ≠ derivedWithin M :=
    not_congr hsigmaDerived
  have hfittingSigma :
      Fitting_core (M.map e.toMonoidHom) =
          sigmaCore (M.map e.toMonoidHom) ↔
        Fitting_core M = sigmaCore M := by
    rw [hfitting, hsigma]
    exact map_equiv_eq_iff16 (Fitting_core M) (sigmaCore M) e
  have habstract :
      fittingCoreQuotientAbelian (M.map e.toMonoidHom) ↔
        fittingCoreQuotientAbelian M := by
    unfold fittingCoreQuotientAbelian
    rw [hsigma, derivedWithin_map_equiv16, hfitting]
    exact Subgroup.map_le_map_iff_of_injective e.injective
  change ftType (M.map e.toMonoidHom) = ftType M
  unfold ftType
  simp only [hkappa, hcard, hsigmaDerivedNe, hfittingSigma, habstract]

/-- `BGsection16.v: FTcoreJ`. -/
theorem FTcoreJ (M : Subgroup G) (x : G) :
    FTcore (conjugateSubgroup16 M x) =
      conjugateSubgroup16 (FTcore M) x := by
  classical
  unfold FTcore ftCore
  rw [FTtypeJ]
  split_ifs
  · exact FcoreJ M x
  · exact derivedWithin_map_equiv16 M (MulAut.conj x)

/-! ## Transport of the supports -/

private theorem centralizerWithin_map_equiv16
    (D A : Subgroup G) (e : G ≃* G) :
    (centralizerWithin D A).map e.toMonoidHom =
      centralizerWithin (D.map e.toMonoidHom)
        (A.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mpr hy.1, ?_⟩
    intro a ha
    have ha' : e.symm a ∈ A := Subgroup.mem_map_equiv.mp ha
    simpa using congrArg e (hy.2 (e.symm a) ha')
  · intro hy
    refine ⟨Subgroup.mem_map_equiv.mp hy.1, ?_⟩
    intro a ha
    have hea : e a ∈ A.map e.toMonoidHom :=
      Subgroup.mem_map_equiv.mpr (by simpa using ha)
    simpa using congrArg e.symm (hy.2 (e a) hea)

private theorem elementCentralizerWithin_map_equiv16
    (D : Subgroup G) (a : G) (e : G ≃* G) :
    (elementCentralizerWithin D a).map e.toMonoidHom =
      elementCentralizerWithin (D.map e.toMonoidHom) (e a) := by
  change
    (centralizerWithin D (Subgroup.zpowers a)).map e.toMonoidHom =
      centralizerWithin (D.map e.toMonoidHom)
        (Subgroup.zpowers (e a))
  rw [centralizerWithin_map_equiv16, MonoidHom.map_zpowers]
  simp only [MulEquiv.coe_toMonoidHom]

private theorem subgroupNonidentity_map_equiv16
    (H : Subgroup G) (e : G ≃* G) :
    subgroupNonidentity (H.map e.toMonoidHom) =
      e '' subgroupNonidentity H := by
  ext y
  constructor
  · rintro ⟨hyH, hy1⟩
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    refine ⟨Subgroup.mem_map_equiv.mp hyH, ?_⟩
    intro heq
    apply hy1
    rw [← e.apply_symm_apply y, heq, map_one]
  · rintro ⟨z, ⟨hzH, hz1⟩, rfl⟩
    refine ⟨Subgroup.mem_map_equiv.mpr (by simpa using hzH), ?_⟩
    intro heq
    apply hz1
    exact e.injective (by simpa using heq)

/-- `BGsection16.v: FTsupp1J`. -/
theorem FTsupp1J (M : Subgroup G) (x : G) :
    FTsupport1 (conjugateSubgroup16 M x) =
      conjugateSet x (FTsupport1 M) := by
  change
    subgroupNonidentity (FTcore (conjugateSubgroup16 M x)) =
      (MulAut.conj x) '' subgroupNonidentity (FTcore M)
  rw [FTcoreJ]
  exact subgroupNonidentity_map_equiv16 (FTcore M) (MulAut.conj x)

private theorem FTderJ (M : Subgroup G) (x : G) :
    FTder (conjugateSubgroup16 M x) =
      conjugateSubgroup16 (FTder M) x := by
  classical
  unfold FTder ftDerived
  rw [FTtypeJ]
  split_ifs
  · rfl
  · exact derivedWithin_map_equiv16 M (MulAut.conj x)

/-- `BGsection16.v: FTsuppJ`. -/
theorem FTsuppJ (M : Subgroup G) (x : G) :
    FTsupport (conjugateSubgroup16 M x) =
      conjugateSet x (FTsupport M) := by
  classical
  let e : G ≃* G := MulAut.conj x
  unfold FTsupport ftSupport
  rw [FTsupp1J, FTderJ]
  change
    (⋃ y ∈ e '' FTsupport1 M,
      subgroupNonidentity
        (elementCentralizerWithin
          ((FTder M).map e.toMonoidHom) y)) =
      e '' (⋃ y ∈ FTsupport1 M,
        subgroupNonidentity (elementCentralizerWithin (FTder M) y))
  rw [Set.biUnion_image]
  simp_rw [← elementCentralizerWithin_map_equiv16,
    subgroupNonidentity_map_equiv16]
  rw [← Set.image_iUnion₂]

/-! ## The enlarged support and basic containments -/

/-- `BGsection16.v: FTsupp0J`. -/
theorem FTsupp0J (M : Subgroup G) (x : G) :
    FTsupport0 (conjugateSubgroup16 M x) =
      conjugateSet x (FTsupport0 M) := by
  classical
  let e : G ≃* G := MulAut.conj x
  let pi := primeSupport (Nat.card (FTder M))
  have hpi :
      primeSupport
          (Nat.card (FTder (conjugateSubgroup16 M x))) = pi := by
    rw [FTderJ, Subgroup.card_map_of_injective e.injective]
  have hmixed :
      {y : G | y ∈ conjugateSubgroup16 M x ∧
        ¬ IsPiNumber pi (orderOf y) ∧
        ¬ IsPiNumber piᶜ (orderOf y)} =
        e '' {y : G | y ∈ M ∧
          ¬ IsPiNumber pi (orderOf y) ∧
          ¬ IsPiNumber piᶜ (orderOf y)} := by
    ext y
    constructor
    · rintro ⟨hyM, hypi, hypic⟩
      have horder : orderOf (e.symm y) = orderOf y :=
        orderOf_injective e.symm.toMonoidHom e.symm.injective y
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      exact ⟨Subgroup.mem_map_equiv.mp hyM,
        by simpa [horder] using hypi,
        by simpa [horder] using hypic⟩
    · rintro ⟨y, ⟨hyM, hypi, hypic⟩, rfl⟩
      have horder : orderOf (e y) = orderOf y :=
        orderOf_injective e.toMonoidHom e.injective y
      exact ⟨Subgroup.mem_map_of_mem e.toMonoidHom hyM,
        by simpa [horder] using hypi,
        by simpa [horder] using hypic⟩
  unfold FTsupport0 ftSupport0
  dsimp only
  rw [hpi, FTsuppJ, hmixed]
  change
    e '' FTsupport M ∪
        e '' {y : G | y ∈ M ∧
          ¬ IsPiNumber pi (orderOf y) ∧
          ¬ IsPiNumber piᶜ (orderOf y)} =
      e '' (FTsupport M ∪
        {y : G | y ∈ M ∧
          ¬ IsPiNumber pi (orderOf y) ∧
          ¬ IsPiNumber piᶜ (orderOf y)})
  rw [Set.image_union]

private theorem FTder_le16 (M : Subgroup G) : FTder M ≤ M := by
  by_cases htype : FTtype M = 1
  · simp [FTder, ftDerived, htype]
  · rw [show FTder M = derivedWithin M by
      simp [FTder, ftDerived, htype]]
    unfold derivedWithin
    exact Subgroup.map_subtype_le (_root_.commutator M)

/-- `BGsection16.v: FTsupp_sub0`. -/
theorem FTsupp_sub0 (M : Subgroup G) :
    FTsupport M ⊆ FTsupport0 M :=
  Set.subset_union_left

/-- `BGsection16.v: FTsupp0_sub`. -/
theorem FTsupp0_sub (M : Subgroup G) :
    FTsupport0 M ⊆ subgroupNonidentity M := by
  classical
  intro x hx
  rcases hx with hxSupport | hxMixed
  · simp only [FTsupport, ftSupport, Set.mem_iUnion] at hxSupport
    rcases hxSupport with ⟨y, hy, hxy⟩
    exact ⟨FTder_le16 M hxy.1.1, hxy.2⟩
  · refine ⟨hxMixed.1, ?_⟩
    intro hx1
    subst x
    exact hxMixed.2.1 (by
      simpa using
        (IsPiNumber.one
          (pi := primeSupport (Nat.card (FTder M)))))

/-- `BGsection16.v: FTsupp_sub`. -/
theorem FTsupp_sub (M : Subgroup G) :
    FTsupport M ⊆ subgroupNonidentity M :=
  (FTsupp_sub0 M).trans (FTsupp0_sub M)

/-! ## Normalization of the supports -/

/-- `BGsection16.v: FTsupp1_norm`. -/
theorem FTsupp1_norm (M : Subgroup G) :
    M ≤ Subgroup.normalizer (FTsupport1 M) := by
  intro x hxM
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  have hMconj : conjugateSubgroup16 M x = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer hxM)
  simpa [hMconj, conjugateSet, MulAut.conj_apply] using
    (FTsupp1J M x).symm

/-- `BGsection16.v: FTsupp_norm`. -/
theorem FTsupp_norm (M : Subgroup G) :
    M ≤ Subgroup.normalizer (FTsupport M) := by
  intro x hxM
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  have hMconj : conjugateSubgroup16 M x = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer hxM)
  simpa [hMconj, conjugateSet, MulAut.conj_apply] using
    (FTsuppJ M x).symm

/-- `BGsection16.v: FTsupp0_norm`. -/
theorem FTsupp0_norm (M : Subgroup G) :
    M ≤ Subgroup.normalizer (FTsupport0 M) := by
  intro x hxM
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  have hMconj : conjugateSubgroup16 M x = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer hxM)
  simpa [hMconj, conjugateSet, MulAut.conj_apply] using
    (FTsupp0J M x).symm

end

end Submission.OddOrder.BG.Section16
