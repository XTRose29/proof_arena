import Submission.OddOrder.PF.Section02.DadeInductionExpansion
import Submission.OddOrder.PF.Section02.DadeExpansionOrbitAveraging
import Submission.OddOrder.PF.Section02.DadeBasicProperties
import Submission.OddOrder.PF.Section02.DadeCoverTI
import Submission.OddOrder.PF.Section02.DadeSupportPartition

/-!
# Peterfalvi 2.10: expansion of the Dade isometry

This file completes the port of Coq `PFsection2.v`, theorem
`Dade_expansion`.  The proof first replaces the sum over representatives by
the corresponding orbit average over all nonempty subsets of `A`.  At a
point of the Dade support, the explicit induction formula then reduces the
claim to a finite alternating subset sum.  Its non-singleton terms cancel
under the private insertion/erasure involution below.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u v

variable {Γ : Type u} [Group Γ]

private def DadeSingletonSubset
    {A : Set Γ} (a : Γ) (ha : a ∈ A) : DadeSubset A :=
  ⟨{a}, Set.singleton_subset_iff.mpr ha, Set.singleton_nonempty a⟩

private theorem mem_normalizer_insert_self
    (a : Γ) {B : Set Γ} (haB : a ∈ Subgroup.normalizer B) :
    a ∈ Subgroup.normalizer (insert a B) := by
  rw [Subgroup.mem_set_normalizer_iff'']
  intro x
  constructor
  · intro hx
    rcases hx with rfl | hxB
    · simp
    · exact Set.mem_insert_of_mem _
        ((Subgroup.mem_set_normalizer_iff''.mp haB x).mp hxB)
  · intro hx
    rcases hx with hxa | hxB
    · have : x = a := by
        calc
          x = a * (a⁻¹ * x * a) * a⁻¹ := by group
          _ = a * a * a⁻¹ := by rw [hxa]
          _ = a := by group
      subst x
      exact Set.mem_insert a B
    · exact Set.mem_insert_of_mem _
        ((Subgroup.mem_set_normalizer_iff''.mp haB x).mpr hxB)

private theorem mem_normalizer_sdiff_singleton_self
    (a : Γ) {B : Set Γ} (haB : a ∈ Subgroup.normalizer B) :
    a ∈ Subgroup.normalizer (B \ {a}) := by
  rw [Subgroup.mem_set_normalizer_iff'']
  intro x
  constructor
  · rintro ⟨hxB, hxa⟩
    refine ⟨(Subgroup.mem_set_normalizer_iff''.mp haB x).mp hxB, ?_⟩
    intro heq
    apply hxa
    rw [Set.mem_singleton_iff] at heq ⊢
    calc
      x = a * (a⁻¹ * x * a) * a⁻¹ := by group
      _ = a * a * a⁻¹ := by rw [heq]
      _ = a := by group
  · rintro ⟨hxB, hxa⟩
    refine ⟨(Subgroup.mem_set_normalizer_iff''.mp haB x).mpr hxB, ?_⟩
    intro heq
    apply hxa
    rw [Set.mem_singleton_iff] at heq ⊢
    subst x
    simp

private def DadeSubsetToggle
    {A : Set Γ} (a : Γ) (ha : a ∈ A) (B : DadeSubset A) :
    DadeSubset A :=
  if haB : a ∈ (B : Set Γ) then
    if hB : (B : Set Γ) = {a} then B
    else
      ⟨(B : Set Γ) \ {a},
        fun _ hx ↦ B.property.1 hx.1,
        by
          by_contra hne
          rw [Set.not_nonempty_iff_eq_empty] at hne
          apply hB
          apply Set.Subset.antisymm
          · intro x hx
            by_contra hxa
            have : x ∈ (B : Set Γ) \ {a} :=
              ⟨hx, by simpa [Set.mem_singleton_iff] using hxa⟩
            rw [hne] at this
            exact this
          · simpa [Set.singleton_subset_iff]
            using haB⟩
  else
    ⟨insert a (B : Set Γ),
      Set.insert_subset ha B.property.1,
      ⟨a, Set.mem_insert a (B : Set Γ)⟩⟩

omit [Group Γ] in
private theorem coe_DadeSubsetToggle
    {A : Set Γ} (a : Γ) (ha : a ∈ A) (B : DadeSubset A) :
    (DadeSubsetToggle a ha B : Set Γ) =
      if _ : a ∈ (B : Set Γ) then
        if (B : Set Γ) = {a} then (B : Set Γ) else (B : Set Γ) \ {a}
      else insert a (B : Set Γ) := by
  by_cases haB : a ∈ (B : Set Γ)
  · by_cases hB : (B : Set Γ) = {a} <;> simp [DadeSubsetToggle, haB, hB]
  · simp [DadeSubsetToggle, haB]

private theorem DadeSubsetToggle_involutive
    {A : Set Γ} (a : Γ) (ha : a ∈ A) :
    Function.Involutive (DadeSubsetToggle a ha) := by
  intro B
  apply Subtype.ext
  by_cases haB : a ∈ (B : Set Γ)
  · by_cases hB : (B : Set Γ) = {a}
    · simp [coe_DadeSubsetToggle, hB]
    · have haErase : a ∉ (B : Set Γ) \ {a} := by simp
      have htoggle : (DadeSubsetToggle a ha B : Set Γ) =
          (B : Set Γ) \ {a} := by
        simp [coe_DadeSubsetToggle, haB, hB]
      rw [coe_DadeSubsetToggle, htoggle, dif_neg haErase]
      exact Set.insert_sdiff_self_of_mem haB
  · have haInsert : a ∈ insert a (B : Set Γ) := Set.mem_insert _ _
    have hInsert : insert a (B : Set Γ) ≠ {a} := by
      intro h
      obtain ⟨b, hbB⟩ := B.property.2
      have hbEq : b = a := by
        have : b ∈ ({a} : Set Γ) := h ▸ Set.mem_insert_of_mem a hbB
        simpa using this
      exact haB (hbEq ▸ hbB)
    have htoggle : (DadeSubsetToggle a ha B : Set Γ) =
        insert a (B : Set Γ) := by
      simp [coe_DadeSubsetToggle, haB]
    rw [coe_DadeSubsetToggle, htoggle, dif_pos haInsert, if_neg hInsert]
    ext x
    simp [haB]

private def DadeSubsetToggleEquiv
    {A : Set Γ} (a : Γ) (ha : a ∈ A) : DadeSubset A ≃ DadeSubset A :=
  (DadeSubsetToggle_involutive a ha).toPerm

private theorem DadeSubsetToggle_mem_complement
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (a : Γ) (ha : a ∈ A)
    (B : DadeSubset A)
    (haC : a ∈ DadeSetComplement ddA B) :
    a ∈ DadeSetComplement ddA (DadeSubsetToggle a ha B) := by
  refine ⟨haC.1, ?_⟩
  by_cases haB : a ∈ (B : Set Γ)
  · by_cases hB : (B : Set Γ) = {a}
    · simpa [DadeSubsetToggle, haB, hB] using haC.2
    · change a ∈ Subgroup.normalizer
        ((DadeSubsetToggle a ha B : DadeSubset A) : Set Γ)
      rw [coe_DadeSubsetToggle, dif_pos haB, if_neg hB]
      exact mem_normalizer_sdiff_singleton_self a haC.2
  · change a ∈ Subgroup.normalizer
      ((DadeSubsetToggle a ha B : DadeSubset A) : Set Γ)
    rw [coe_DadeSubsetToggle, dif_neg haB]
    exact mem_normalizer_insert_self a haC.2

private theorem DadeSubsetToggle_mem_complement_iff
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (a : Γ) (ha : a ∈ A)
    (B : DadeSubset A) :
    a ∈ DadeSetComplement ddA (DadeSubsetToggle a ha B) ↔
      a ∈ DadeSetComplement ddA B := by
  constructor
  · intro h
    have := DadeSubsetToggle_mem_complement ddA a ha
      (DadeSubsetToggle a ha B) h
    simpa only [DadeSubsetToggle_involutive a ha B] using this
  · exact DadeSubsetToggle_mem_complement ddA a ha B

private theorem DadeConjugators_ncard_eq_normalizer
    [Fintype Γ]
    {D N : Subgroup Γ} {S : Set Γ}
    (hTI : IsNormalizedTI S D N) (g : D)
    (hg : (g : Γ) ∈ classSupportWithin D S) :
    (DadeConjugators g S).ncard = Nat.card N := by
  rcases hg with ⟨u, huS, x, hxD, hux⟩
  change x⁻¹ * u * x = (g : Γ) at hux
  let xD : D := ⟨x, hxD⟩
  have hND : N ≤ D := fun n hn ↦ (hTI.2.1 hn).1
  let ND : Subgroup D := N.subgroupOf D
  have hset : DadeConjugators g S =
      (fun n : ND ↦ xD⁻¹ * (n : D)) '' (Set.univ : Set ND) := by
    ext y
    constructor
    · intro hy
      change (y : Γ)⁻¹ * (g : Γ) * (y : Γ) ∈ S at hy
      have hxyD : x * (y : Γ) ∈ D := D.mul_mem hxD y.property
      have hxyS : (x * (y : Γ))⁻¹ * u * (x * (y : Γ)) ∈ S := by
        rw [show (x * (y : Γ))⁻¹ * u * (x * (y : Γ)) =
            (y : Γ)⁻¹ * (x⁻¹ * u * x) * (y : Γ) by group,
          hux]
        exact hy
      have hxyN : x * (y : Γ) ∈ N :=
        ((isNormalizedTI_iff_mem_conj.mp hTI).2.2 huS hxyD).mp hxyS
      let n : ND := ⟨⟨x * (y : Γ), hxyD⟩, hxyN⟩
      refine ⟨n, Set.mem_univ n, ?_⟩
      apply Subtype.ext
      dsimp [n, xD]
      group
    · rintro ⟨n, _hn, rfl⟩
      change (((xD⁻¹ * (n : D) : D) : Γ))⁻¹ *
          (g : Γ) * ((xD⁻¹ * (n : D) : D) : Γ) ∈ S
      have hnD : ((n : D) : Γ) ∈ D := (n : D).property
      have hnS : (((n : D) : Γ))⁻¹ * u * ((n : D) : Γ) ∈ S :=
        ((isNormalizedTI_iff_mem_conj.mp hTI).2.2 huS hnD).mpr n.property
      convert hnS using 1
      rw [← hux]
      dsimp [xD]
      group
  rw [hset, Set.ncard_image_of_injective,
    Set.ncard_univ]
  · exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hND).toEquiv
  · exact (Equiv.mulLeft xD⁻¹).injective.comp Subtype.coe_injective

private theorem DadeConjugators_ncard_smul
    [Fintype Γ]
    {D H : Subgroup Γ} (hHD : H ≤ D)
    (g : D) (T : Set Γ) (h : H) :
    let conjugationAction := subgroupConjugationActionOnAmbient H
    letI : SMul H Γ := conjugationAction.toSMul
    letI : MulAction H Γ := conjugationAction.toMulAction
    letI : MulAction H (Set Γ) := Set.mulActionSet
    (DadeConjugators g (h • T)).ncard =
      (DadeConjugators g T).ncard := by
  let conjugationAction := subgroupConjugationActionOnAmbient H
  letI : SMul H Γ := conjugationAction.toSMul
  letI : MulAction H Γ := conjugationAction.toMulAction
  letI : MulAction H (Set Γ) := Set.mulActionSet
  let hD : D := ⟨(h : Γ), hHD h.property⟩
  have hmem (y : D) :
      y ∈ DadeConjugators g (h • T) ↔
        y * hD ∈ DadeConjugators g T := by
    change ((y : Γ)⁻¹ * (g : Γ) * (y : Γ) ∈ h • T) ↔
      (((y * hD : D) : Γ))⁻¹ * (g : Γ) *
        ((y * hD : D) : Γ) ∈ T
    constructor
    · rintro ⟨z, hzT, hzy⟩
      change (h : Γ) * z * (h : Γ)⁻¹ =
        (y : Γ)⁻¹ * (g : Γ) * (y : Γ) at hzy
      convert hzT using 1
      calc
        (((y * hD : D) : Γ))⁻¹ * (g : Γ) *
            ((y * hD : D) : Γ) =
            (h : Γ)⁻¹ *
              ((y : Γ)⁻¹ * (g : Γ) * (y : Γ)) *
              (h : Γ) := by
          dsimp [hD]
          group
        _ = (h : Γ)⁻¹ *
              ((h : Γ) * z * (h : Γ)⁻¹) * (h : Γ) := by
          rw [hzy]
        _ = z := by group
    · intro hy
      refine ⟨(((y * hD : D) : Γ))⁻¹ * (g : Γ) *
          ((y * hD : D) : Γ), hy, ?_⟩
      change (h : Γ) *
          ((((y * hD : D) : Γ))⁻¹ * (g : Γ) *
            ((y * hD : D) : Γ)) * (h : Γ)⁻¹ =
        (y : Γ)⁻¹ * (g : Γ) * (y : Γ)
      dsimp [hD]
      group
  have hbij : Set.BijOn (fun y : D ↦ y * hD)
      (DadeConjugators g (h • T)) (DadeConjugators g T) := by
    refine ⟨?_, (Equiv.mulRight hD).injective.injOn, ?_⟩
    · intro y hy
      exact (hmem y).mp hy
    · intro z hz
      refine ⟨z * hD⁻¹, ?_, by simp⟩
      exact (hmem (z * hD⁻¹)).mpr (by simpa using hz)
  exact hbij.ncard_eq

private theorem DadeConjugators_ncard_partition_orbit
    [Fintype Γ]
    {D H : Subgroup Γ} (hHD : H ≤ D)
    (g : D) (T S : Set Γ)
    (hpart :
      let conjugationAction := subgroupConjugationActionOnAmbient H
      letI : SMul H Γ := conjugationAction.toSMul
      letI : MulAction H Γ := conjugationAction.toMulAction
      letI : MulAction H (Set Γ) := Set.mulActionSet
      IsSetPartition (MulAction.orbit H T) S) :
    let conjugationAction := subgroupConjugationActionOnAmbient H
    letI : SMul H Γ := conjugationAction.toSMul
    letI : MulAction H Γ := conjugationAction.toMulAction
    letI : MulAction H (Set Γ) := Set.mulActionSet
    (DadeConjugators g S).ncard =
      (MulAction.orbit H T).ncard * (DadeConjugators g T).ncard := by
  let conjugationAction := subgroupConjugationActionOnAmbient H
  letI : SMul H Γ := conjugationAction.toSMul
  letI : MulAction H Γ := conjugationAction.toMulAction
  letI : MulAction H (Set Γ) := Set.mulActionSet
  have hunion : DadeConjugators g S =
      ⋃ B ∈ MulAction.orbit H T, DadeConjugators g B := by
    ext x
    constructor
    · intro hx
      change (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈ S at hx
      rw [← hpart.1] at hx
      rcases Set.mem_sUnion.mp hx with ⟨B, hB, hxB⟩
      exact Set.mem_iUnion₂.mpr ⟨B, hB, hxB⟩
    · intro hx
      rcases Set.mem_iUnion₂.mp hx with ⟨B, hB, hxB⟩
      change (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈ S
      rw [← hpart.1]
      exact Set.mem_sUnion.mpr ⟨B, hB, hxB⟩
  have hpair : (MulAction.orbit H T).PairwiseDisjoint
      (fun B ↦ DadeConjugators g B) := by
    rw [Set.pairwiseDisjoint_iff]
    intro B hB C hC hinter
    rcases hinter with ⟨x, hxB, hxC⟩
    exact (Set.pairwiseDisjoint_iff.mp hpart.2.1)
      hB hC ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hxB, hxC⟩
  have horbitfinite : (MulAction.orbit H T).Finite := Set.toFinite _
  have hblock (B : Set Γ) (hB : B ∈ MulAction.orbit H T) :
      (DadeConjugators g B).ncard = (DadeConjugators g T).ncard := by
    rcases hB with ⟨h, rfl⟩
    exact DadeConjugators_ncard_smul hHD g T h
  rw [hunion]
  calc
    (⋃ B ∈ MulAction.orbit H T, DadeConjugators g B).ncard =
        ∑ᶠ B ∈ MulAction.orbit H T,
          (DadeConjugators g B).ncard :=
      horbitfinite.ncard_biUnion
        (fun B _ ↦ Set.toFinite (DadeConjugators g B)) hpair
    _ = ∑ᶠ _B ∈ MulAction.orbit H T,
        (DadeConjugators g T).ncard :=
      finsum_mem_congr rfl hblock
    _ = (∑ᶠ _B ∈ MulAction.orbit H T, (1 : ℕ)) *
        (DadeConjugators g T).ncard := by
      rw [finsum_mem_mul' (fun _ : Set Γ ↦ 1)
        (DadeConjugators g T).ncard horbitfinite]
      simp
    _ = (MulAction.orbit H T).ncard *
        (DadeConjugators g T).ncard := by
      rw [finsum_one]

private theorem Dade_set_signalizer_le_G
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A) :
    DadeSetSignalizer ddA B ≤ G := by
  obtain ⟨a, haB⟩ := B.property.2
  have hHa : Dade_set_signalizer ddA (B : Set Γ) ≤
      DadeSignalizer ddA a := iInf_le_of_le ⟨a, haB⟩ le_rfl
  exact hHa.trans (Dade_signalizer_sub ddA a)

private theorem Dade_complement_mem_signalizer_normalizer
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A)
    (b : DadeSetComplement ddA B) :
    (b : Γ) ∈ Subgroup.normalizer
      (DadeSetSignalizer ddA B : Set Γ) := by
  let M := DadeSetNormalizer ddA B
  let N : Subgroup M := (DadeSetSignalizer ddA B).subgroupOf M
  let hsd := Dade_set_sdprod_subtype ddA B
  letI : N.Normal := by simpa [N, M] using hsd.2.2.1
  let bM : M := ⟨(b : Γ), hsd.2.1 b.property⟩
  rw [Subgroup.mem_set_normalizer_iff'']
  intro n
  constructor
  · intro hn
    let nM : M := ⟨n, hsd.1 hn⟩
    have hnN : nM ∈ N := hn
    have hconj : bM⁻¹ * nM * bM ∈ N :=
      (inferInstance : N.Normal).conj_mem' nM hnN bM
    exact hconj
  · intro hn
    let cM : M := ⟨(b : Γ)⁻¹ * n * (b : Γ), hsd.1 hn⟩
    have hcN : cM ∈ N := hn
    have hconj : bM * cM * bM⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem cM hcN bM
    change (b : Γ) * ((b : Γ)⁻¹ * n * (b : Γ)) * (b : Γ)⁻¹ ∈
      DadeSetSignalizer ddA B at hconj
    have heq : (b : Γ) * ((b : Γ)⁻¹ * n * (b : Γ)) *
        (b : Γ)⁻¹ = n := by group
    rwa [heq] at hconj

private theorem DadeConjugators_ncard_fixed_coset_factor
    [Fintype Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A)
    (g : G) {b : Γ} (hbA : b ∈ A)
    (hbC : b ∈ DadeSetComplement ddA B) :
    (DadeConjugators g
        ((DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ))).ncard =
      (centralizerWithin (DadeSetSignalizer ddA B)
          (Subgroup.zpowers b)).relIndex (DadeSetSignalizer ddA B) *
        (DadeConjugators g
          ((centralizerWithin (DadeSetSignalizer ddA B)
              (Subgroup.zpowers b) : Set Γ) * ({b} : Set Γ))).ncard := by
  let HB := DadeSetSignalizer ddA B
  let C := centralizerWithin HB (Subgroup.zpowers b)
  let bC : DadeSetComplement ddA B := ⟨b, hbC⟩
  have hHBG : HB ≤ G := Dade_set_signalizer_le_G ddA B
  have hbNorm : b ∈ Subgroup.normalizer (HB : Set Γ) :=
    Dade_complement_mem_signalizer_normalizer ddA B bC
  obtain ⟨a, haB⟩ := B.property.2
  have haA : a ∈ A := B.property.1 haB
  have hHBHa : HB ≤ DadeSignalizer ddA a :=
    iInf_le_of_le ⟨a, haB⟩ le_rfl
  have hbCL : b ∈ centralizerWithin L (Subgroup.zpowers b) := by
    refine ⟨hbC.1, ?_⟩
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.refl b).zpow_left n).eq
  have hcop : Nat.Coprime (Nat.card HB) (orderOf b) := by
    apply (Dade_coprime ddA haA hbA).coprime_dvd_left
      (Subgroup.card_dvd_of_le hHBHa) |>.coprime_dvd_right
    simpa only [Subgroup.orderOf_mk] using
      (orderOf_dvd_natCard
        (⟨b, hbCL⟩ : centralizerWithin L (Subgroup.zpowers b)))
  let conjugationAction := subgroupConjugationActionOnAmbient HB
  letI : SMul HB Γ := conjugationAction.toSMul
  letI : MulAction HB Γ := conjugationAction.toMulAction
  letI : MulAction HB (Set Γ) := Set.mulActionSet
  have hpart :
      IsSetPartition
          (MulAction.orbit HB ((C : Set Γ) * ({b} : Set Γ)))
          ((HB : Set Γ) * ({b} : Set Γ)) ∧
        (MulAction.orbit HB
          ((C : Set Γ) * ({b} : Set Γ))).ncard = C.relIndex HB :=
    partition_cent_rcoset HB b hbNorm hcop
  have hcount := DadeConjugators_ncard_partition_orbit
    hHBG g ((C : Set Γ) * ({b} : Set Γ))
      ((HB : Set Γ) * ({b} : Set Γ)) hpart.1
  change (DadeConjugators g
      ((HB : Set Γ) * ({b} : Set Γ))).ncard =
    (MulAction.orbit HB
      ((C : Set Γ) * ({b} : Set Γ))).ncard *
      (DadeConjugators g
        ((C : Set Γ) * ({b} : Set Γ))).ncard at hcount
  rw [hpart.2] at hcount
  simpa [HB, C] using hcount

private theorem relIndex_mul_natCard
    [Finite Γ] {C H : Subgroup Γ} (hCH : C ≤ H) :
    C.relIndex H * Nat.card C = Nat.card H := by
  change (C.subgroupOf H).index * Nat.card C = Nat.card H
  rw [← Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe hCH).toEquiv]
  exact (C.subgroupOf H).index_mul_card

private theorem natCard_DadeSetNormalizer_eq_mul
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A) :
    Nat.card (DadeSetNormalizer ddA B) =
      Nat.card (DadeSetSignalizer ddA B) *
        Nat.card (DadeSetComplement ddA B) := by
  let M := DadeSetNormalizer ddA B
  let H : Subgroup M := (DadeSetSignalizer ddA B).subgroupOf M
  let K : Subgroup M := (DadeSetComplement ddA B).subgroupOf M
  have hsd := Dade_set_sdprod_subtype ddA B
  have hHcard : Nat.card H = Nat.card (DadeSetSignalizer ddA B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsd.1).toEquiv
  have hKcard : Nat.card K = Nat.card (DadeSetComplement ddA B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsd.2.1).toEquiv
  rw [← hHcard, ← hKcard]
  simpa [M, H, K] using hsd.2.2.2.card_mul.symm

private theorem Dade_orbit_average
    [Fintype Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k] [CharZero k]
    (ddA : DadeHypothesis G L A)
    (f : DadeSubset A → k)
    (hf :
      letI : MulAction L (DadeSubset A) :=
        dadeSubsetConjugationAction ddA
      ∀ (x : L) (B : DadeSubset A), f (x • B) = f B) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    ∑ omega : DadeSubsetOrbit ddA, f (Dade_transversal omega) =
      ∑ B : DadeSubset A,
        f B / ((MulAction.stabilizer L B).index : k) := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  symm
  calc
    (∑ B : DadeSubset A,
        f B / ((MulAction.stabilizer L B).index : k)) =
        ∑ z : Σ omega : DadeSubsetOrbit ddA,
            MulAction.orbitRel.Quotient.orbit omega,
          f z.2 /
            ((MulAction.stabilizer L (z.2 : DadeSubset A)).index : k) := by
      refine Fintype.sum_equiv
        (MulAction.selfEquivSigmaOrbits' L (DadeSubset A))
        (fun B : DadeSubset A ↦
          f B / ((MulAction.stabilizer L B).index : k))
        (fun z ↦
          f z.2 /
            ((MulAction.stabilizer L (z.2 : DadeSubset A)).index : k)) ?_
      intro B
      rfl
    _ = ∑ omega : DadeSubsetOrbit ddA,
          ∑ B : MulAction.orbitRel.Quotient.orbit omega,
            f B /
              ((MulAction.stabilizer L (B : DadeSubset A)).index : k) := by
      exact Fintype.sum_sigma
        (fun z : Σ omega : DadeSubsetOrbit ddA,
            MulAction.orbitRel.Quotient.orbit omega ↦
          f z.2 /
            ((MulAction.stabilizer L
              (z.2 : DadeSubset A)).index : k))
    _ = ∑ omega : DadeSubsetOrbit ddA,
          f (Dade_transversal omega) := by
      apply Fintype.sum_congr
      intro omega
      have hterm : ∀ B : MulAction.orbitRel.Quotient.orbit omega,
          f (B : DadeSubset A) /
              ((MulAction.stabilizer L (B : DadeSubset A)).index : k) =
            f (Dade_transversal omega) /
              ((MulAction.stabilizer L
                (Dade_transversal omega)).index : k) := by
        intro B
        have hB : (B : DadeSubset A) ∈
            MulAction.orbit L (Dade_transversal omega) := by
          rw [← DadeSubsetOrbit.orbit_eq_transversal
            (ddA := ddA) omega]
          exact B.property
        obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp hB
        have hfun : f (B : DadeSubset A) =
            f (Dade_transversal omega) := by
          rw [← hx, hf]
        have hindex :
            (MulAction.stabilizer L (B : DadeSubset A)).index =
              (MulAction.stabilizer L
                (Dade_transversal omega)).index := by
          rw [MulAction.index_stabilizer, MulAction.index_stabilizer, ← hx,
            MulAction.orbit_smul]
        rw [hfun, hindex]
      simp_rw [hterm]
      rw [Finset.sum_const, Finset.card_univ,
        Set.fintypeCard_eq_ncard,
        DadeSubsetOrbit.orbit_eq_transversal (ddA := ddA) omega,
        ← MulAction.index_stabilizer L (Dade_transversal omega),
        nsmul_eq_mul]
      exact mul_div_cancel₀ _
        (Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite)

private def DadeExpansionLocalTerm
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (g : G) (b : Γ)
    (B : DadeSubset A) : k :=
  if b ∈ DadeSetComplement ddA B then
    ((-1 : k) ^ (B : Set Γ).ncard /
        (Nat.card (DadeSetSignalizer ddA B) : k)) *
      ((DadeConjugators g
        ((DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ))).ncard : k)
  else 0

private theorem DadeExpansionLocalTerm_add_toggle_of_notMem
    [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (g : G) {b : Γ} (hbA : b ∈ A)
    (B : DadeSubset A) (hbB : b ∉ (B : Set Γ)) :
    DadeExpansionLocalTerm (k := k) ddA g b B +
      DadeExpansionLocalTerm ddA g b (DadeSubsetToggle b hbA B) = 0 := by
  let T := DadeSubsetToggle b hbA B
  let H := DadeSetSignalizer ddA B
  let C := centralizerWithin H (Subgroup.zpowers b)
  have hTset : (T : Set Γ) = insert b (B : Set Γ) := by
    simp [T, coe_DadeSubsetToggle, hbB]
  have hTcard : (T : Set Γ).ncard = (B : Set Γ).ncard + 1 := by
    rw [hTset, Set.ncard_insert_of_notMem hbB]
  have hsignal : DadeSetSignalizer ddA T = C := by
    change Dade_set_signalizer ddA (T : Set Γ) = C
    rw [hTset]
    exact Dade_setU1 ddA B.property.1 B.property.2 hbA
  have hcomp : b ∈ DadeSetComplement ddA T ↔
      b ∈ DadeSetComplement ddA B := by
    simpa [T] using
      (DadeSubsetToggle_mem_complement_iff ddA b hbA B)
  by_cases hbC : b ∈ DadeSetComplement ddA B
  · have hbTC : b ∈ DadeSetComplement ddA T := hcomp.mpr hbC
    have hcountNat :=
      DadeConjugators_ncard_fixed_coset_factor ddA B g hbA hbC
    have hcount :
        ((DadeConjugators g
          ((H : Set Γ) * ({b} : Set Γ))).ncard : k) =
          (C.relIndex H : k) *
            ((DadeConjugators g
              ((C : Set Γ) * ({b} : Set Γ))).ncard : k) := by
      exact_mod_cast hcountNat
    have hcardNat : C.relIndex H * Nat.card C = Nat.card H :=
      relIndex_mul_natCard
        (centralizerWithin_le_left H (Subgroup.zpowers b))
    have hcard :
        (C.relIndex H : k) * (Nat.card C : k) =
          (Nat.card H : k) := by
      exact_mod_cast hcardNat
    have hi0 : (C.relIndex H : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
    have hC0 : (Nat.card C : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    unfold DadeExpansionLocalTerm
    rw [if_pos hbC, if_pos hbTC, hTcard, hsignal]
    change ((-1 : k) ^ (B : Set Γ).ncard / (Nat.card H : k)) *
          ((DadeConjugators g
            ((H : Set Γ) * ({b} : Set Γ))).ncard : k) +
        ((-1 : k) ^ ((B : Set Γ).ncard + 1) /
          (Nat.card C : k)) *
          ((DadeConjugators g
            ((C : Set Γ) * ({b} : Set Γ))).ncard : k) = 0
    rw [hcount, ← hcard]
    field_simp [hi0, hC0]
    ring
  · have hbTC : b ∉ DadeSetComplement ddA T :=
      fun h ↦ hbC (hcomp.mp h)
    unfold DadeExpansionLocalTerm
    rw [if_neg hbC, if_neg hbTC, zero_add]

private theorem DadeSubsetToggle_singleton
    {A : Set Γ} {b : Γ} (hbA : b ∈ A) :
    DadeSubsetToggle b hbA (DadeSingletonSubset b hbA) =
      DadeSingletonSubset b hbA := by
  apply Subtype.ext
  simp [coe_DadeSubsetToggle, DadeSingletonSubset]

private theorem DadeSubsetToggle_ne_self
    {A : Set Γ} {b : Γ} (hbA : b ∈ A) (B : DadeSubset A)
    (hB : B ≠ DadeSingletonSubset b hbA) :
    DadeSubsetToggle b hbA B ≠ B := by
  intro heq
  have hsets := congrArg (fun C : DadeSubset A ↦ (C : Set Γ)) heq
  by_cases hbB : b ∈ (B : Set Γ)
  · have hBset : (B : Set Γ) ≠ {b} := by
      intro h
      apply hB
      apply Subtype.ext
      simpa [DadeSingletonSubset] using h
    rw [coe_DadeSubsetToggle, dif_pos hbB, if_neg hBset] at hsets
    have : b ∈ (B : Set Γ) \ {b} := hsets.symm ▸ hbB
    exact this.2 (Set.mem_singleton b)
  · rw [coe_DadeSubsetToggle, dif_neg hbB] at hsets
    exact hbB (hsets ▸ Set.mem_insert b (B : Set Γ))

private theorem DadeSubsetToggle_ne_singleton
    {A : Set Γ} {b : Γ} (hbA : b ∈ A) (B : DadeSubset A)
    (hB : B ≠ DadeSingletonSubset b hbA) :
    DadeSubsetToggle b hbA B ≠ DadeSingletonSubset b hbA := by
  intro htoggle
  apply hB
  calc
    B = DadeSubsetToggle b hbA (DadeSubsetToggle b hbA B) :=
      (DadeSubsetToggle_involutive b hbA B).symm
    _ = DadeSubsetToggle b hbA (DadeSingletonSubset b hbA) :=
      congrArg (DadeSubsetToggle b hbA) htoggle
    _ = DadeSingletonSubset b hbA := DadeSubsetToggle_singleton hbA

private theorem DadeExpansionLocalTerm_add_toggle
    [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (g : G) {b : Γ} (hbA : b ∈ A)
    (B : DadeSubset A) (hB : B ≠ DadeSingletonSubset b hbA) :
    DadeExpansionLocalTerm (k := k) ddA g b B +
      DadeExpansionLocalTerm ddA g b (DadeSubsetToggle b hbA B) = 0 := by
  by_cases hbB : b ∈ (B : Set Γ)
  · let T := DadeSubsetToggle b hbA B
    have hBset : (B : Set Γ) ≠ {b} := by
      intro h
      apply hB
      apply Subtype.ext
      simpa [DadeSingletonSubset] using h
    have hbT : b ∉ (T : Set Γ) := by
      simp [T, coe_DadeSubsetToggle, hbB, hBset]
    have hcancel := DadeExpansionLocalTerm_add_toggle_of_notMem
      (k := k) ddA g hbA T hbT
    rw [show DadeSubsetToggle b hbA T = B by
      exact DadeSubsetToggle_involutive b hbA B] at hcancel
    simpa [add_comm] using hcancel
  · exact DadeExpansionLocalTerm_add_toggle_of_notMem
      ddA g hbA B hbB

private theorem DadeExpansionLocalTerm_sum_erase_singleton
    [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (g : G) {b : Γ} (hbA : b ∈ A) :
    ∑ B ∈ (Finset.univ : Finset (DadeSubset A)).erase
        (DadeSingletonSubset b hbA),
      DadeExpansionLocalTerm (k := k) ddA g b B = 0 := by
  apply Finset.sum_involution
      (fun B _hB ↦ DadeSubsetToggle b hbA B)
  · intro B hB
    exact DadeExpansionLocalTerm_add_toggle ddA g hbA B
      (Finset.mem_erase.mp hB).1
  · intro B hB _hterm
    exact DadeSubsetToggle_ne_self hbA B (Finset.mem_erase.mp hB).1
  · intro B hB
    rw [Finset.mem_erase]
    exact ⟨DadeSubsetToggle_ne_singleton hbA B
      (Finset.mem_erase.mp hB).1, Finset.mem_univ _⟩
  · intro B _hB
    exact DadeSubsetToggle_involutive b hbA B

private theorem DadeExpansionLocalTerm_singleton
    [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (g : G) {b : Γ} (hbA : b ∈ A)
    (hg : (g : Γ) ∈ Dade_support1 ddA b) :
    DadeExpansionLocalTerm (k := k) ddA g b
        (DadeSingletonSubset b hbA) =
      -(Nat.card (centralizerWithin L (Subgroup.zpowers b)) : k) := by
  let B := DadeSingletonSubset b hbA
  let H := DadeSignalizer ddA b
  let CG := centralizerWithin G (Subgroup.zpowers b)
  let CL := centralizerWithin L (Subgroup.zpowers b)
  change DadeExpansionLocalTerm (k := k) ddA g b B =
    -(Nat.card CL : k)
  have hbC : b ∈ DadeSetComplement ddA B := by
    refine ⟨ddA.1.1 hbA, ?_⟩
    change b ∈ Subgroup.normalizer ({b} : Set Γ)
    have hnormEmpty : b ∈ Subgroup.normalizer (∅ : Set Γ) := by
      rw [Subgroup.mem_set_normalizer_iff'']
      intro x
      simp
    simpa using mem_normalizer_insert_self b hnormEmpty
  have hsignal : DadeSetSignalizer ddA B = H := by
    change Dade_set_signalizer ddA (B : Set Γ) = H
    simp [B, DadeSingletonSubset, Dade_set_signalizer, H]
  have hcountNat :
      (DadeConjugators g ((H : Set Γ) * ({b} : Set Γ))).ncard =
        Nat.card CG := by
    exact DadeConjugators_ncard_eq_normalizer
      (Dade_cover_TI ddA hbA) g hg
  have hsd : IsInternalSemidirectProductIn H CL CG := by
    simpa [H, CL, CG] using Dade_sdprod ddA hbA
  have hHcard : Nat.card (H.subgroupOf CG) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsd.1).toEquiv
  have hCLcard : Nat.card (CL.subgroupOf CG) = Nat.card CL :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsd.2.1).toEquiv
  have hCGcardNat : Nat.card H * Nat.card CL = Nat.card CG := by
    rw [← hHcard, ← hCLcard]
    exact hsd.2.2.2.card_mul
  have hCGcard : (Nat.card H : k) * (Nat.card CL : k) =
      (Nat.card CG : k) := by
    exact_mod_cast hCGcardNat
  have hH0 : (Nat.card H : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hBcard : (B : Set Γ).ncard = 1 := by
    simp [B, DadeSingletonSubset]
  unfold DadeExpansionLocalTerm
  rw [if_pos hbC, hsignal, hBcard, hcountNat, ← hCGcard]
  norm_num [div_eq_mul_inv]

private theorem DadeExpansionLocalTerm_sum
    [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (g : G) {b : Γ} (hbA : b ∈ A)
    (hg : (g : Γ) ∈ Dade_support1 ddA b) :
    ∑ B : DadeSubset A, DadeExpansionLocalTerm (k := k) ddA g b B =
      -(Nat.card (centralizerWithin L (Subgroup.zpowers b)) : k) := by
  let S := DadeSingletonSubset b hbA
  calc
    (∑ B : DadeSubset A,
        DadeExpansionLocalTerm (k := k) ddA g b B) =
        DadeExpansionLocalTerm ddA g b S +
          ∑ B ∈ (Finset.univ : Finset (DadeSubset A)).erase S,
            DadeExpansionLocalTerm ddA g b B := by
      symm
      exact Finset.add_sum_erase Finset.univ
        (DadeExpansionLocalTerm (k := k) ddA g b) (Finset.mem_univ S)
    _ = -(Nat.card
          (centralizerWithin L (Subgroup.zpowers b)) : k) + 0 := by
      rw [show DadeExpansionLocalTerm (k := k) ddA g b S =
          -(Nat.card
            (centralizerWithin L (Subgroup.zpowers b)) : k) by
        exact DadeExpansionLocalTerm_singleton ddA g hbA hg,
        show (∑ B ∈ (Finset.univ : Finset (DadeSubset A)).erase S,
          DadeExpansionLocalTerm (k := k) ddA g b B) = 0 by
          exact DadeExpansionLocalTerm_sum_erase_singleton ddA g hbA]
    _ = -(Nat.card
          (centralizerWithin L (Subgroup.zpowers b)) : k) := add_zero _

private theorem centralizerWithin_map_equiv_DadeExpansion
    {D S : Subgroup Γ} (e : Γ ≃* Γ)
    (hD : D.map e.toMonoidHom = D) :
    (centralizerWithin D S).map e.toMonoidHom =
      centralizerWithin D (S.map e.toMonoidHom) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy
    refine ⟨?_, ?_⟩
    · have hyMap : y ∈ D.map e.toMonoidHom :=
        Subgroup.mem_map_equiv.mpr hy.1
      rwa [hD] at hyMap
    · intro z hz
      have hz' : e.symm z ∈ S := Subgroup.mem_map_equiv.mp hz
      have hcomm := hy.2 (e.symm z) hz'
      simpa using congrArg e hcomm
  · intro hy
    refine ⟨?_, ?_⟩
    · have hyMap : y ∈ D.map e.toMonoidHom := by
        rw [hD]
        exact hy.1
      exact Subgroup.mem_map_equiv.mp hyMap
    · intro z hz
      have hzMap : e z ∈ S.map e.toMonoidHom :=
        (Subgroup.mem_map_iff_mem e.injective).mpr hz
      have hcomm := hy.2 (e z) hzMap
      simpa using congrArg e.symm hcomm

private theorem natCard_centralizerWithin_conj
    [Finite Γ]
    (L : Subgroup Γ) (a : Γ) (y : L) :
    Nat.card
        (centralizerWithin L
          (Subgroup.zpowers ((y : Γ)⁻¹ * a * (y : Γ)))) =
      Nat.card (centralizerWithin L (Subgroup.zpowers a)) := by
  let e : Γ ≃* Γ := MulAut.conj (y : Γ)⁻¹
  have hLmap : L.map e.toMonoidHom = L := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact Subgroup.le_normalizer (L.inv_mem y.property)
  have hmap :
      (centralizerWithin L (Subgroup.zpowers a)).map e.toMonoidHom =
        centralizerWithin L
          (Subgroup.zpowers ((y : Γ)⁻¹ * a * (y : Γ))) := by
    have h := centralizerWithin_map_equiv_DadeExpansion
      (S := Subgroup.zpowers a) e hLmap
    simpa [MonoidHom.map_zpowers, e] using h
  calc
    Nat.card
        (centralizerWithin L
          (Subgroup.zpowers ((y : Γ)⁻¹ * a * (y : Γ)))) =
        Nat.card
          ((centralizerWithin L (Subgroup.zpowers a)).map e.toMonoidHom) :=
      by rw [hmap]
    _ = Nat.card (centralizerWithin L (Subgroup.zpowers a)) :=
      (Nat.card_congr
        ((centralizerWithin L (Subgroup.zpowers a)).equivMapOfInjective
          e.toMonoidHom e.injective).toEquiv).symm

private theorem DadeExpansionCount_alternating_sum
    [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (g : G)
    {a : Γ} (ha : a ∈ A) (hg : (g : Γ) ∈ Dade_support1 ddA a) :
    ∑ B : DadeSubset A,
        (((-1 : k) ^ (B : Set Γ).ncard /
          (Nat.card (DadeSetSignalizer ddA B) : k)) *
            DadeIndExpansionCount ddA B g a) =
      -(Nat.card L : k) := by
  let CL := centralizerWithin L (Subgroup.zpowers a)
  have hswap :
      (∑ B : DadeSubset A,
          (((-1 : k) ^ (B : Set Γ).ncard /
            (Nat.card (DadeSetSignalizer ddA B) : k)) *
              DadeIndExpansionCount ddA B g a)) =
        ∑ b : Γ, if b ∈ conjugacyClassWithin L a then
          ∑ B : DadeSubset A,
            DadeExpansionLocalTerm (k := k) ddA g b B
        else 0 := by
    unfold DadeIndExpansionCount DadeNormalizerConjugacySlice
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hbclass : b ∈ conjugacyClassWithin L a
    · rw [if_pos hbclass]
      apply Finset.sum_congr rfl
      intro B _hB
      by_cases hbC : b ∈ DadeSetComplement ddA B
      · rw [if_pos ⟨hbC, hbclass⟩]
        unfold DadeExpansionLocalTerm
        rw [if_pos hbC]
      · rw [if_neg (fun h ↦ hbC h.1)]
        unfold DadeExpansionLocalTerm
        rw [if_neg hbC, mul_zero]
    · rw [if_neg hbclass]
      apply Finset.sum_eq_zero
      intro B _hB
      rw [if_neg (fun h ↦ hbclass h.2), mul_zero]
  rw [hswap]
  have hlocal (b : Γ) (hbclass : b ∈ conjugacyClassWithin L a) :
      (∑ B : DadeSubset A,
          DadeExpansionLocalTerm (k := k) ddA g b B) =
        -(Nat.card CL : k) := by
    rcases hbclass with ⟨y, hyL, rfl⟩
    have hbA : y⁻¹ * a * y ∈ A :=
      (Subgroup.mem_set_normalizer_iff''.mp (ddA.1.2 hyL) a).mp ha
    have hgb : (g : Γ) ∈ Dade_support1 ddA (y⁻¹ * a * y) := by
      rw [Dade_support1_id ddA a y hyL]
      exact hg
    rw [DadeExpansionLocalTerm_sum ddA g hbA hgb,
      natCard_centralizerWithin_conj L a ⟨y, hyL⟩]
  have hpoint : ∀ b : Γ,
      (if b ∈ conjugacyClassWithin L a then
          ∑ B : DadeSubset A,
            DadeExpansionLocalTerm (k := k) ddA g b B
        else 0) =
      if b ∈ conjugacyClassWithin L a then
        -(Nat.card CL : k)
      else 0 := by
    intro b
    by_cases hb : b ∈ conjugacyClassWithin L a
    · rw [if_pos hb, if_pos hb, hlocal b hb]
    · rw [if_neg hb, if_neg hb]
  simp_rw [hpoint]
  let S := conjugacyClassWithin L a
  have hfilter :
      (Finset.univ : Finset Γ).filter (fun b ↦ b ∈ S) =
        (Set.toFinite S).toFinset := by
    ext b
    simp
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul]
  rw [← Set.ncard_eq_toFinset_card S (Set.toFinite S)]
  rw [show S.ncard = CL.relIndex L by
    exact ncard_conjugacyClassWithin_eq_relIndex L a]
  have hCLcardNat : CL.relIndex L * Nat.card CL = Nat.card L :=
    relIndex_mul_natCard (centralizerWithin_le_left L (Subgroup.zpowers a))
  have hCLcard : (CL.relIndex L : k) * (Nat.card CL : k) =
      (Nat.card L : k) := by
    exact_mod_cast hCLcardNat
  rw [← hCLcard]
  ring

private theorem DadeExpansion_orbit_sum_value
    [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (alpha : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A})
    (g : G) {a : Γ} (ha : a ∈ A)
    (hg : (g : Γ) ∈ Dade_support1 ddA a) :
    ∑ omega : DadeSubsetOrbit ddA,
        ((-1 : k) ^
          (Dade_transversal omega : Set Γ).ncard) *
        Dade_ind_restriction ddA alpha
          (Dade_transversal omega) g =
      -alpha ⟨a, ddA.1.1 ha⟩ := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  let f : DadeSubset A → k := fun B ↦
    ((-1 : k) ^ (B : Set Γ).ncard) *
      Dade_ind_restriction ddA alpha B g
  have hf (x : L) (B : DadeSubset A) : f (x • B) = f B := by
    have hcard : ((x • B : DadeSubset A) : Set Γ).ncard =
        (B : Set Γ).ncard := by
      rw [coe_dadeSubset_smul ddA x B,
        Set.ncard_image_of_injective _
          (MulAut.conj (x : Γ)).injective]
    have hInd := congrArg
      (fun phi : ClassFunction G k ↦ phi g)
      (Dade_Ind_restr_J ddA alpha x B)
    dsimp [f]
    rw [hcard, hInd]
  have havg := Dade_orbit_average ddA f hf
  change (∑ omega : DadeSubsetOrbit ddA,
      ((-1 : k) ^ (Dade_transversal omega : Set Γ).ncard) *
        Dade_ind_restriction ddA alpha
          (Dade_transversal omega) g) =
    ∑ B : DadeSubset A,
      (((-1 : k) ^ (B : Set Γ).ncard) *
        Dade_ind_restriction ddA alpha B g) /
          ((MulAction.stabilizer L B).index : k) at havg
  rw [havg]
  have hterm (B : DadeSubset A) :
      (((-1 : k) ^ (B : Set Γ).ncard) *
          Dade_ind_restriction ddA alpha B g) /
            ((MulAction.stabilizer L B).index : k) =
        (alpha ⟨a, ddA.1.1 ha⟩ / (Nat.card L : k)) *
          (((-1 : k) ^ (B : Set Γ).ncard /
              (Nat.card (DadeSetSignalizer ddA B) : k)) *
            DadeIndExpansionCount ddA B g a) := by
    let H := DadeSetSignalizer ddA B
    let K := DadeSetComplement ddA B
    let M := DadeSetNormalizer ddA B
    let I := (MulAction.stabilizer L B).index
    have hMcardNat : Nat.card M = Nat.card H * Nat.card K :=
      natCard_DadeSetNormalizer_eq_mul ddA B
    have hIcardNat : I * Nat.card K = Nat.card L := by
      have hindex := (MulAction.stabilizer L B).index_mul_card
      rw [natCard_DadeSubset_stabilizer_eq_complement ddA B] at hindex
      exact hindex
    have hMcard : (Nat.card M : k) =
        (Nat.card H : k) * (Nat.card K : k) := by
      exact_mod_cast hMcardNat
    have hIcard : (I : k) * (Nat.card K : k) =
        (Nat.card L : k) := by
      exact_mod_cast hIcardNat
    have hH0 : (Nat.card H : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hK0 : (Nat.card K : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hI0 : (I : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
    rw [Dade_Ind_expansion_value ddA alpha halpha B g ha hg]
    change (((-1 : k) ^ (B : Set Γ).ncard) *
          ((alpha ⟨a, ddA.1.1 ha⟩ / (Nat.card M : k)) *
            DadeIndExpansionCount ddA B g a)) / (I : k) = _
    rw [hMcard, ← hIcard]
    field_simp [hH0, hK0, hI0]
    ring
  calc
    (∑ B : DadeSubset A,
        (((-1 : k) ^ (B : Set Γ).ncard) *
          Dade_ind_restriction ddA alpha B g) /
            ((MulAction.stabilizer L B).index : k)) =
        ∑ B : DadeSubset A,
          (alpha ⟨a, ddA.1.1 ha⟩ / (Nat.card L : k)) *
            (((-1 : k) ^ (B : Set Γ).ncard /
                (Nat.card (DadeSetSignalizer ddA B) : k)) *
              DadeIndExpansionCount ddA B g a) := by
      apply Finset.sum_congr rfl
      intro B _hB
      exact hterm B
    _ = (alpha ⟨a, ddA.1.1 ha⟩ / (Nat.card L : k)) *
        ∑ B : DadeSubset A,
          (((-1 : k) ^ (B : Set Γ).ncard /
              (Nat.card (DadeSetSignalizer ddA B) : k)) *
            DadeIndExpansionCount ddA B g a) := by
      rw [Finset.mul_sum]
    _ = (alpha ⟨a, ddA.1.1 ha⟩ / (Nat.card L : k)) *
        (-(Nat.card L : k)) := by
      rw [DadeExpansionCount_alternating_sum ddA g ha hg]
    _ = -alpha ⟨a, ddA.1.1 ha⟩ := by
      have hL0 : (Nat.card L : k) ≠ 0 :=
        Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      field_simp [hL0]

private theorem ClassFunction_finset_sum_apply
    {I : Type*} {G₀ : Type*} [Group G₀]
    {k : Type*} [Field k]
    (s : Finset I) (f : I → ClassFunction G₀ k) (g : G₀) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

/-- Peterfalvi 2.10, Coq `Dade_expansion`: the Dade isometry is the
alternating sum of the induced restrictions indexed by the nonempty subset
orbits of `A`. -/
theorem Dade_expansion
    [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (alpha : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : Γ) ∈ A}) :
    Dade ddA alpha =
      -∑ omega : DadeSubsetOrbit ddA,
        ((-1 : k) ^
          (Dade_transversal omega : Set Γ).ncard) •
        Dade_ind_restriction ddA alpha
          (Dade_transversal omega) := by
  apply ClassFunction.ext
  intro g
  rw [ClassFunction.neg_apply,
    ClassFunction_finset_sum_apply]
  simp only [ClassFunction.smul_apply, smul_eq_mul]
  by_cases hg : (g : Γ) ∈ Dade_support ddA
  · rcases hg with ⟨a, ha, hga⟩
    rw [DadeE ddA alpha ha g hga,
      DadeExpansion_orbit_sum_value ddA alpha halpha g ha hga]
    simp
  · rw [Dade_eq_zero_of_not_mem ddA alpha g hg]
    have hsum :
        (∑ omega : DadeSubsetOrbit ddA,
          ((-1 : k) ^
            (Dade_transversal omega : Set Γ).ncard) *
          Dade_ind_restriction ddA alpha
            (Dade_transversal omega) g) = 0 := by
      apply Finset.sum_eq_zero
      intro omega _homega
      rw [Dade_Ind_expansion_zero ddA alpha halpha
        (Dade_transversal omega) g hg, mul_zero]
    rw [hsum, neg_zero]

end

end Submission.OddOrder.PF
