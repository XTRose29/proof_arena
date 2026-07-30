import Submission.OddOrder.PF.Section02.DadeInductionRestrictionConjugation
import Submission.OddOrder.PF.Section02.DadeSetCentralizer
import Submission.OddOrder.PF.Section02.DadeGlobalSupport
import Submission.OddOrder.PF.Section02.DadeSupportTI
import Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset

/-!
# Peterfalvi 2.10.3: values of the induced Dade restriction terms

This file ports Coq `PFsection2.v`, the block from `calA` through
`Dade_Ind_expansion`.  The source counts the elements `x ∈ G` for which
`x⁻¹ g x` lies in a specified right coset.  We retain that count explicitly
as `DadeConjugators` and express finite source big operators as sums over the
finite ambient type.

As in `DadeInductionRestrictionConjugation`, subgroup class functions are
genuinely subgroup-typed in Lean.  The term being evaluated is therefore
`Dade_ind_restriction`, which already transports the restriction class
function into the copy of its set normalizer inside `G`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u v

variable {Γ : Type u} [Group Γ]

/-- Coq `calA g X`: the elements of `G` conjugating `g` into `X`. -/
def DadeConjugators
    {G : Subgroup Γ} (g : G) (X : Set Γ) : Set G :=
  {x | (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈ X}

/-- The values of the right-factor projection relevant to the support block
of `a`: elements of the setwise normalizer complement lying in the
`L`-conjugacy class of `a`. -/
def DadeNormalizerConjugacySlice
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A) (a : Γ) : Set Γ :=
  (DadeSetComplement ddA B : Set Γ) ∩ conjugacyClassWithin L a

/-- The counting sum in Coq `Dade_Ind_expansion`. -/
def DadeIndExpansionCount
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A)
    (g : G) (a : Γ) : k :=
  ∑ b : Γ, if b ∈ DadeNormalizerConjugacySlice ddA B a then
    ((DadeConjugators g
      ((DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ))).ncard : k)
  else 0

private theorem DadeConjugators_ncard_cast
    [Fintype Γ]
    {k : Type v} [Field k]
    {G : Subgroup Γ} (g : G) (X : Set Γ) :
    ((DadeConjugators g X).ncard : k) =
      ∑ x : G, if (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈ X then 1 else 0 := by
  rw [Set.ncard_eq_toFinset_card, Finset.card_eq_sum_ones,
    Nat.cast_sum]
  simp only [Nat.cast_one]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext x
    simp [DadeConjugators]
  · intro x hx
    simp

private theorem DadeConjugators_conj_ncard
    [Fintype Γ]
    {G : Subgroup Γ} (g : G) (X : Set Γ) (x : Γ) (hxG : x ∈ G) :
    (DadeConjugators g ((MulAut.conj x) '' X)).ncard =
      (DadeConjugators g X).ncard := by
  let xG : G := ⟨x, hxG⟩
  have hset :
      DadeConjugators g ((MulAut.conj x) '' X) =
        (fun y : G ↦ y * xG⁻¹) '' DadeConjugators g X := by
    ext y
    constructor
    · intro hy
      change (y : Γ)⁻¹ * (g : Γ) * (y : Γ) ∈
        (MulAut.conj x) '' X at hy
      rcases hy with ⟨u, hu, huy⟩
      refine ⟨y * xG, ?_, by simp⟩
      change (((y * xG : G) : Γ))⁻¹ * (g : Γ) *
          ((y * xG : G) : Γ) ∈ X
      convert hu using 1
      dsimp [xG]
      rw [mul_inv_rev]
      calc
        x⁻¹ * (y : Γ)⁻¹ * (g : Γ) * ((y : Γ) * x) =
            x⁻¹ * ((y : Γ)⁻¹ * (g : Γ) * (y : Γ)) * x := by
          group
        _ = x⁻¹ * (MulAut.conj x u) * x := by rw [huy]
        _ = u := by
          dsimp [MulAut.conj_apply]
          group
    · rintro ⟨z, hz, rfl⟩
      change ((((z * xG⁻¹ : G) : Γ))⁻¹ * (g : Γ) *
          ((z * xG⁻¹ : G) : Γ)) ∈ (MulAut.conj x) '' X
      change (z : Γ)⁻¹ * (g : Γ) * (z : Γ) ∈ X at hz
      refine ⟨(z : Γ)⁻¹ * (g : Γ) * (z : Γ), hz, ?_⟩
      dsimp [xG, MulAut.conj_apply]
      group
  rw [hset]
  exact Set.ncard_image_of_injective _
    (Equiv.mulRight xG⁻¹).injective

private theorem conjugacyClassWithin_conj
    {L : Subgroup Γ} (x : L) (a : Γ) :
    conjugacyClassWithin L ((x : Γ) * a * (x : Γ)⁻¹) =
      (MulAut.conj (x : Γ)) '' conjugacyClassWithin L a := by
  ext b
  constructor
  · rintro ⟨y, hyL, rfl⟩
    let z : Γ := (x : Γ)⁻¹ * y * (x : Γ)
    have hzL : z ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem x.property) hyL) x.property
    refine ⟨z⁻¹ * a * z, ⟨z, hzL, rfl⟩, ?_⟩
    dsimp [z, MulAut.conj_apply]
    group
  · rintro ⟨b, ⟨z, hzL, rfl⟩, rfl⟩
    let y : Γ := (x : Γ) * z * (x : Γ)⁻¹
    have hyL : y ∈ L :=
      L.mul_mem (L.mul_mem x.property hzL) (L.inv_mem x.property)
    refine ⟨y, hyL, ?_⟩
    dsimp [y, MulAut.conj_apply]
    group

private theorem DadeNormalizerConjugacySlice_smul
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : L) (B : DadeSubset A) (a : Γ) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    DadeNormalizerConjugacySlice ddA (x • B)
        ((x : Γ) * a * (x : Γ)⁻¹) =
      (MulAut.conj (x : Γ)) ''
        DadeNormalizerConjugacySlice ddA B a := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  unfold DadeNormalizerConjugacySlice
  rw [Dade_set_complement_smul ddA x B,
    conjugacyClassWithin_conj x a]
  ext b
  change (b ∈ (DadeSetComplement ddA B).map
      (MulAut.conj (x : Γ)).toMonoidHom ∧
      b ∈ (MulAut.conj (x : Γ)).toEquiv '' conjugacyClassWithin L a) ↔
    b ∈ (MulAut.conj (x : Γ)).toEquiv ''
      ((DadeSetComplement ddA B : Set Γ) ∩ conjugacyClassWithin L a)
  rw [Subgroup.mem_map_equiv, Set.mem_image_equiv, Set.mem_image_equiv]
  rfl

private theorem Dade_signalizer_rightCoset_smul
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : L) (B : DadeSubset A) (b : Γ) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    (DadeSetSignalizer ddA (x • B) : Set Γ) *
        ({(MulAut.conj (x : Γ)).toEquiv b} : Set Γ) =
      (MulAut.conj (x : Γ)) ''
        ((DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ)) := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  change (Dade_set_signalizer ddA ((x • B : DadeSubset A) : Set Γ) :
      Set Γ) * ({(x : Γ) * b * (x : Γ)⁻¹} : Set Γ) = _
  rw [Dade_set_signalizer_smul ddA x B]
  change (((Dade_set_signalizer ddA (B : Set Γ)).map
      (MulAut.conj (x : Γ)).toMonoidHom : Subgroup Γ) : Set Γ) *
        ({(MulAut.conj (x : Γ)) b} : Set Γ) = _
  rw [Subgroup.coe_map]
  rw [← Set.image_singleton]
  exact (Set.image_mul (MulAut.conj (x : Γ)).toMonoidHom).symm

/-- Simultaneous conjugation of a Dade subset and the support parameter
does not change the counting coefficient in `Dade_Ind_expansion`. -/
theorem DadeIndExpansionCount_smul
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : L) (B : DadeSubset A)
    (g : G) (a : Γ) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    DadeIndExpansionCount (k := k) ddA (x • B) g
        ((x : Γ) * a * (x : Γ)⁻¹) =
      DadeIndExpansionCount ddA B g a := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  unfold DadeIndExpansionCount
  symm
  refine Fintype.sum_equiv (MulAut.conj (x : Γ)).toEquiv
    (fun b : Γ ↦
      if b ∈ DadeNormalizerConjugacySlice ddA B a then
        ((DadeConjugators g
          ((DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ))).ncard : k)
      else 0)
    (fun b : Γ ↦
      if b ∈ DadeNormalizerConjugacySlice ddA (x • B)
          ((x : Γ) * a * (x : Γ)⁻¹) then
        ((DadeConjugators g
          ((DadeSetSignalizer ddA (x • B) : Set Γ) *
            ({b} : Set Γ))).ncard : k)
      else 0) ?_
  intro b
  have hbiff :
      (MulAut.conj (x : Γ)).toEquiv b ∈
          DadeNormalizerConjugacySlice ddA (x • B)
            ((x : Γ) * a * (x : Γ)⁻¹) ↔
        b ∈ DadeNormalizerConjugacySlice ddA B a := by
    rw [DadeNormalizerConjugacySlice_smul ddA x B a]
    exact
      (@Set.mem_image_equiv Γ Γ (DadeNormalizerConjugacySlice ddA B a)
        (MulAut.conj (x : Γ)).toEquiv
        ((MulAut.conj (x : Γ)).toEquiv b)).trans (by
          rw [Equiv.symm_apply_apply])
  by_cases hb : b ∈ DadeNormalizerConjugacySlice ddA B a
  · rw [if_pos hb, if_pos (hbiff.mpr hb),
      Dade_signalizer_rightCoset_smul ddA x B b]
    exact congrArg (fun n : ℕ ↦ (n : k))
      (DadeConjugators_conj_ncard g
        ((DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ))
        (x : Γ) (ddA.2.1 x.property)).symm
  · have hxb : (MulAut.conj (x : Γ)).toEquiv b ∉
        DadeNormalizerConjugacySlice ddA (x • B)
          ((x : Γ) * a * (x : Γ)⁻¹) :=
      fun h ↦ hb (hbiff.mp h)
    rw [if_neg hb, if_neg hxb]

private theorem Dade_set_signalizer_le_G
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A) :
    DadeSetSignalizer ddA B ≤ G := by
  obtain ⟨a, haB⟩ := B.property.2
  have hHa : Dade_set_signalizer ddA (B : Set Γ) ≤
      DadeSignalizer ddA a := iInf_le_of_le ⟨a, haB⟩ le_rfl
  exact hHa.trans (Dade_signalizer_sub ddA a)

/-- The complement normalizes the signalizer factor, extracted from the
internal semidirect-product structure. -/
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

/-- A right coset of a set signalizer by a relevant element of `A` lies in
the corresponding first Dade support.  This is the partition argument used
inside Coq `Dade_Ind_expansion`. -/
private theorem Dade_setSignalizer_rightCoset_subset_support1
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A)
    (b : DadeSetComplement ddA B) (hbA : (b : Γ) ∈ A) :
    (DadeSetSignalizer ddA B : Set Γ) * ({(b : Γ)} : Set Γ) ⊆
      Dade_support1 ddA (b : Γ) := by
  let HB := DadeSetSignalizer ddA B
  let C := centralizerWithin HB (Subgroup.zpowers (b : Γ))
  have hHBG : HB ≤ G := Dade_set_signalizer_le_G ddA B
  have hbNorm : (b : Γ) ∈ Subgroup.normalizer (HB : Set Γ) :=
    Dade_complement_mem_signalizer_normalizer ddA B b
  obtain ⟨a, haB⟩ := B.property.2
  have haA : a ∈ A := B.property.1 haB
  have hHBHa : HB ≤ DadeSignalizer ddA a :=
    iInf_le_of_le ⟨a, haB⟩ le_rfl
  have hbCL : (b : Γ) ∈
      centralizerWithin L (Subgroup.zpowers (b : Γ)) := by
    refine ⟨b.property.1, ?_⟩
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.refl (b : Γ)).zpow_left n).eq
  have hcop : Nat.Coprime (Nat.card HB) (orderOf (b : Γ)) := by
    apply (Dade_coprime ddA haA hbA).coprime_dvd_left
      (Subgroup.card_dvd_of_le hHBHa) |>.coprime_dvd_right
    simpa only [Subgroup.orderOf_mk] using
      (orderOf_dvd_natCard
        (⟨(b : Γ), hbCL⟩ :
          centralizerWithin L (Subgroup.zpowers (b : Γ))))
  have hpart := partition_cent_rcoset HB (b : Γ) hbNorm hcop
  let conjugationAction := subgroupConjugationActionOnAmbient HB
  letI : SMul HB Γ := conjugationAction.toSMul
  letI : MulAction HB Γ := conjugationAction.toMulAction
  letI : MulAction HB (Set Γ) := Set.mulActionSet
  have hCsignal : C ≤ DadeSignalizer ddA (b : Γ) := by
    change centralizerWithin
      (Dade_set_signalizer ddA (B : Set Γ))
        (Subgroup.zpowers (b : Γ)) ≤ DadeSignalizer ddA (b : Γ)
    rw [← Dade_setU1 ddA B.property.1 B.property.2 hbA]
    exact iInf_le_of_le ⟨(b : Γ), Set.mem_insert (b : Γ) (B : Set Γ)⟩ le_rfl
  intro m hm
  have hmUnion : m ∈ ⋃₀ (MulAction.orbit HB
      ((C : Set Γ) * ({(b : Γ)} : Set Γ))) := by
    rw [hpart.1.1]
    exact hm
  rcases Set.mem_sUnion.mp hmUnion with ⟨S, hS, hmS⟩
  rcases hS with ⟨y, rfl⟩
  rcases Set.mem_smul_set.mp hmS with ⟨u, hu, rfl⟩
  refine ⟨u, ?_, (y : Γ)⁻¹, G.inv_mem (hHBG y.property), ?_⟩
  · rcases Set.mem_mul.mp hu with ⟨c, hc, t, ht, rfl⟩
    exact ⟨c, hCsignal hc, t, ht, rfl⟩
  · change ((y : Γ)⁻¹)⁻¹ * u * (y : Γ)⁻¹ =
      (MulAut.conj (y : Γ)) u
    simp only [inv_inv, MulAut.conj_apply]

private theorem Dade_restrm_apply_mul_expansion
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A)
    (n : DadeSetSignalizer ddA B)
    (h : DadeSetComplement ddA B) :
    Dade_restrm ddA B
        (⟨(n : Γ) * (h : Γ),
          (DadeSetNormalizer ddA B).mul_mem
            ((Dade_set_sdprod_subtype ddA B).1 n.property)
            ((Dade_set_sdprod_subtype ddA B).2.1 h.property)⟩ :
          DadeSetNormalizer ddA B) =
      Subgroup.inclusion inf_le_left h := by
  let nM : DadeSetNormalizer ddA B :=
    ⟨(n : Γ), (Dade_set_sdprod_subtype ddA B).1 n.property⟩
  let hM : DadeSetNormalizer ddA B :=
    ⟨(h : Γ), (Dade_set_sdprod_subtype ddA B).2.1 h.property⟩
  change Dade_restrm ddA B (nM * hM) =
    Subgroup.inclusion inf_le_left h
  rw [map_mul, show Dade_restrm ddA B nM = 1 by
      exact Dade_restrm_apply_signalizer ddA B n,
    show Dade_restrm ddA B hM = Subgroup.inclusion inf_le_left h by
      exact Dade_restrm_apply_complement ddA B h,
    one_mul]

/-- The projection has value `b` exactly on the right coset of the
signalizer by `b`; this is the Lean form of the source lemma `remgrMid`. -/
private theorem Dade_restrm_eq_iff_mem_rightCoset
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A)
    (m : DadeSetNormalizer ddA B)
    (b : DadeSetComplement ddA B) :
    Dade_restrm ddA B m = Subgroup.inclusion inf_le_left b ↔
      (m : Γ) ∈
        (DadeSetSignalizer ddA B : Set Γ) * ({(b : Γ)} : Set Γ) := by
  let hsd := Dade_set_sdprod_subtype ddA B
  let N : Subgroup (DadeSetNormalizer ddA B) :=
    (DadeSetSignalizer ddA B).subgroupOf (DadeSetNormalizer ddA B)
  let H : Subgroup (DadeSetNormalizer ddA B) :=
    (DadeSetComplement ddA B).subgroupOf (DadeSetNormalizer ddA B)
  letI : N.Normal := by simpa [N] using hsd.2.2.1
  have hcomp : N.IsComplement' H := by simpa [N, H] using hsd.2.2.2
  constructor
  · intro hmb
    obtain ⟨p, hp, _⟩ := hcomp.existsUnique m
    rcases p with ⟨n, h⟩
    let n₀ : DadeSetSignalizer ddA B :=
      ⟨((n : N) : DadeSetNormalizer ddA B), n.property⟩
    let h₀ : DadeSetComplement ddA B :=
      ⟨((h : H) : DadeSetNormalizer ddA B), h.property⟩
    have hpΓ : (n₀ : Γ) * (h₀ : Γ) = (m : Γ) :=
      congrArg (fun z : DadeSetNormalizer ddA B ↦ (z : Γ)) hp
    have hmFactor : m =
        (⟨(n₀ : Γ) * (h₀ : Γ),
          (DadeSetNormalizer ddA B).mul_mem
            (hsd.1 n₀.property) (hsd.2.1 h₀.property)⟩ :
          DadeSetNormalizer ddA B) := by
      apply Subtype.ext
      exact hpΓ.symm
    have hproj : Dade_restrm ddA B m =
        Subgroup.inclusion inf_le_left h₀ := by
      rw [hmFactor]
      exact Dade_restrm_apply_mul_expansion ddA B n₀ h₀
    have hhL : Subgroup.inclusion inf_le_left h₀ =
        Subgroup.inclusion inf_le_left b := hproj.symm.trans hmb
    have hhΓ : (h₀ : Γ) = (b : Γ) :=
      congrArg (fun z : L ↦ (z : Γ)) hhL
    refine Set.mem_mul.mpr ⟨(n₀ : Γ), n₀.property,
      (b : Γ), Set.mem_singleton (b : Γ), ?_⟩
    rw [← hhΓ]
    exact hpΓ
  · intro hm
    rcases Set.mem_mul.mp hm with ⟨n, hn, t, ht, hnt⟩
    rw [Set.mem_singleton_iff] at ht
    subst t
    let n₀ : DadeSetSignalizer ddA B := ⟨n, hn⟩
    have hmFactor : m =
        (⟨(n₀ : Γ) * (b : Γ),
          (DadeSetNormalizer ddA B).mul_mem
            (hsd.1 n₀.property) (hsd.2.1 b.property)⟩ :
          DadeSetNormalizer ddA B) := by
      apply Subtype.ext
      exact hnt.symm
    rw [hmFactor]
    exact Dade_restrm_apply_mul_expansion ddA B n₀ b

/-- The projection really takes values in the complement, even though its
public codomain is the containing subgroup `L`. -/
private theorem Dade_restrm_mem_complement
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A)
    (m : DadeSetNormalizer ddA B) :
    ((Dade_restrm ddA B m : L) : Γ) ∈ DadeSetComplement ddA B := by
  let hsd := Dade_set_sdprod_subtype ddA B
  let N : Subgroup (DadeSetNormalizer ddA B) :=
    (DadeSetSignalizer ddA B).subgroupOf (DadeSetNormalizer ddA B)
  let H : Subgroup (DadeSetNormalizer ddA B) :=
    (DadeSetComplement ddA B).subgroupOf (DadeSetNormalizer ddA B)
  letI : N.Normal := by simpa [N] using hsd.2.2.1
  have hcomp : N.IsComplement' H := by simpa [N, H] using hsd.2.2.2
  obtain ⟨p, hp, _⟩ := hcomp.existsUnique m
  rcases p with ⟨n, h⟩
  let n₀ : DadeSetSignalizer ddA B :=
    ⟨((n : N) : DadeSetNormalizer ddA B), n.property⟩
  let h₀ : DadeSetComplement ddA B :=
    ⟨((h : H) : DadeSetNormalizer ddA B), h.property⟩
  have hpΓ : (n₀ : Γ) * (h₀ : Γ) = (m : Γ) :=
    congrArg (fun z : DadeSetNormalizer ddA B ↦ (z : Γ)) hp
  have hmFactor : m =
      (⟨(n₀ : Γ) * (h₀ : Γ),
        (DadeSetNormalizer ddA B).mul_mem
          (hsd.1 n₀.property) (hsd.2.1 h₀.property)⟩ :
        DadeSetNormalizer ddA B) := by
    apply Subtype.ext
    exact hpΓ.symm
  have hproj : Dade_restrm ddA B m =
      Subgroup.inclusion inf_le_left h₀ := by
    rw [hmFactor]
    exact Dade_restrm_apply_mul_expansion ddA B n₀ h₀
  change (Dade_restrm ddA B m : Γ) ∈ DadeSetComplement ddA B
  rw [hproj]
  exact h₀.property

private theorem Dade_signalizer_rightCoset_subset_normalizer
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A)
    (b : DadeSetComplement ddA B) :
    (DadeSetSignalizer ddA B : Set Γ) * ({(b : Γ)} : Set Γ) ⊆
      DadeSetNormalizer ddA B := by
  intro m hm
  rcases Set.mem_mul.mp hm with ⟨n, hn, t, ht, rfl⟩
  rw [Set.mem_singleton_iff] at ht
  subst t
  exact (DadeSetNormalizer ddA B).mul_mem
    ((Dade_set_sdprod_subtype ddA B).1 hn)
    ((Dade_set_sdprod_subtype ddA B).2.1 b.property)

private theorem DadeIndExpansionCount_eq_sum
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A)
    (g : G) (a : Γ) :
    DadeIndExpansionCount (k := k) ddA B g a =
      ∑ x : G,
        if hx : (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
            DadeSetNormalizer ddA B then
          if ((Dade_restrm ddA B
              ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hx⟩ : L) : Γ) ∈
              DadeNormalizerConjugacySlice ddA B a then
            1
          else 0
        else 0 := by
  classical
  unfold DadeIndExpansionCount
  simp_rw [DadeConjugators_ncard_cast]
  calc
    _ =
      ∑ b : Γ, ∑ x : G,
        if b ∈ DadeNormalizerConjugacySlice ddA B a then
          if (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
              (DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ) then
            (1 : k)
          else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hb : b ∈ DadeNormalizerConjugacySlice ddA B a <;>
        simp [hb]
    _ = ∑ x : G, ∑ b : Γ,
        if b ∈ DadeNormalizerConjugacySlice ddA B a then
          if (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
              (DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ) then
            (1 : k)
          else 0
        else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxM : (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
          DadeSetNormalizer ddA B
      · rw [dif_pos hxM]
        let m : DadeSetNormalizer ddA B :=
          ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hxM⟩
        let b₀ : Γ := ((Dade_restrm ddA B m : L) : Γ)
        have hb₀C : b₀ ∈ DadeSetComplement ddA B :=
          Dade_restrm_mem_complement ddA B m
        let bC : DadeSetComplement ddA B := ⟨b₀, hb₀C⟩
        have hproj : Dade_restrm ddA B m =
            Subgroup.inclusion inf_le_left bC := by
          apply Subtype.ext
          rfl
        have hxCoset : (m : Γ) ∈
            (DadeSetSignalizer ddA B : Set Γ) * ({b₀} : Set Γ) := by
          exact (Dade_restrm_eq_iff_mem_rightCoset ddA B m bC).mp hproj
        by_cases hb₀ : b₀ ∈ DadeNormalizerConjugacySlice ddA B a
        · rw [if_pos hb₀]
          rw [Finset.sum_eq_single b₀]
          · rw [if_pos hb₀, if_pos hxCoset]
          · intro b _hb hbne
            by_cases hb : b ∈ DadeNormalizerConjugacySlice ddA B a
            · have hbC : b ∈ DadeSetComplement ddA B := hb.1
              let bC' : DadeSetComplement ddA B := ⟨b, hbC⟩
              by_cases hxCoset' : (m : Γ) ∈
                  (DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ)
              · have hproj' :=
                    (Dade_restrm_eq_iff_mem_rightCoset ddA B m bC').mpr hxCoset'
                have heq : b₀ = b := by
                  change ((Dade_restrm ddA B m : L) : Γ) = b
                  exact congrArg (fun z : L ↦ (z : Γ)) hproj'
                exact (hbne heq.symm).elim
              · rw [if_pos hb, if_neg hxCoset']
            · rw [if_neg hb]
          · intro hbnot
            exact (hbnot (Finset.mem_univ b₀)).elim
        · rw [if_neg hb₀]
          apply Finset.sum_eq_zero
          intro b _hb
          by_cases hb : b ∈ DadeNormalizerConjugacySlice ddA B a
          · have hbC : b ∈ DadeSetComplement ddA B := hb.1
            let bC' : DadeSetComplement ddA B := ⟨b, hbC⟩
            by_cases hxCoset' : (m : Γ) ∈
                (DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ)
            · have hproj' :=
                  (Dade_restrm_eq_iff_mem_rightCoset ddA B m bC').mpr hxCoset'
              have heq : b₀ = b := by
                change ((Dade_restrm ddA B m : L) : Γ) = b
                exact congrArg (fun z : L ↦ (z : Γ)) hproj'
              exact (hb₀ (heq ▸ hb)).elim
            · rw [if_pos hb, if_neg hxCoset']
          · rw [if_neg hb]
      · rw [dif_neg hxM]
        apply Finset.sum_eq_zero
        intro b _hb
        by_cases hb : b ∈ DadeNormalizerConjugacySlice ddA B a
        · have hbC : b ∈ DadeSetComplement ddA B := hb.1
          let bC : DadeSetComplement ddA B := ⟨b, hbC⟩
          by_cases hxCoset :
              (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
                (DadeSetSignalizer ddA B : Set Γ) * ({b} : Set Γ)
          · exact (hxM
              (Dade_signalizer_rightCoset_subset_normalizer ddA B bC hxCoset)).elim
          · rw [if_pos hb, if_neg hxCoset]
        · rw [if_neg hb]

private theorem Dade_restriction_value_indicator
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {a : L | (a : Γ) ∈ A})
    (B : DadeSubset A) (g : G) (a : Γ) (ha : a ∈ A)
    (hg : (g : Γ) ∈ Dade_support1 ddA a)
    (x : G)
    (hxM : (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
      DadeSetNormalizer ddA B) :
    alpha (Dade_restrm ddA B
        ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hxM⟩) =
      if ((Dade_restrm ddA B
          ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hxM⟩ : L) : Γ) ∈
          DadeNormalizerConjugacySlice ddA B a then
        alpha ⟨a, ddA.1.1 ha⟩
      else 0 := by
  let m : DadeSetNormalizer ddA B :=
    ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hxM⟩
  let bL : L := Dade_restrm ddA B m
  have hbC : (bL : Γ) ∈ DadeSetComplement ddA B :=
    Dade_restrm_mem_complement ddA B m
  let b : DadeSetComplement ddA B := ⟨(bL : Γ), hbC⟩
  have hproj : Dade_restrm ddA B m =
      Subgroup.inclusion inf_le_left b := by
    apply Subtype.ext
    rfl
  have hmCoset : (m : Γ) ∈
      (DadeSetSignalizer ddA B : Set Γ) * ({(b : Γ)} : Set Γ) :=
    (Dade_restrm_eq_iff_mem_rightCoset ddA B m b).mp hproj
  by_cases hbA : (b : Γ) ∈ A
  · have hmSupport : (m : Γ) ∈ Dade_support1 ddA (b : Γ) :=
      Dade_setSignalizer_rightCoset_subset_support1 ddA B b hbA hmCoset
    have hgSupport : (g : Γ) ∈ Dade_support1 ddA (b : Γ) :=
      (classSupportWithin_rightConj_iff
        (G := G)
        (S := (DadeSignalizer ddA (b : Γ) : Set Γ) *
          ({(b : Γ)} : Set Γ)) x.property).mp hmSupport
    rcases Dade_support1_TI ddA ha hbA ⟨(g : Γ), hg, hgSupport⟩ with
      ⟨y, hyL, hba⟩
    have hbSlice : (b : Γ) ∈ DadeNormalizerConjugacySlice ddA B a :=
      ⟨b.property, ⟨y, hyL, hba.symm⟩⟩
    rw [if_pos hbSlice]
    let yL : L := ⟨y, hyL⟩
    let aL : L := ⟨a, ddA.1.1 ha⟩
    have hbConj : bL = yL⁻¹ * aL * yL := by
      apply Subtype.ext
      exact hba
    calc
      alpha (Dade_restrm ddA B m) = alpha bL := rfl
      _ = alpha (yL⁻¹ * aL * yL) := congrArg alpha hbConj
      _ = alpha aL := by
        simpa using ClassFunction.conj_apply alpha yL⁻¹ aL
      _ = alpha ⟨a, ddA.1.1 ha⟩ := rfl
  · have hbNotSlice : (b : Γ) ∉
        DadeNormalizerConjugacySlice ddA B a := by
      rintro ⟨_hbC, y, hyL, hyb⟩
      apply hbA
      rw [← hyb]
      exact (Subgroup.mem_set_normalizer_iff''.mp (ddA.1.2 hyL) a).mp ha
    rw [if_neg hbNotSlice]
    exact ClassFunction.eq_zero_of_mem_supportedOn halpha hbA

/-- Direct evaluation formula for an induced Dade restriction term, with
the subgroup copy inside `G` converted back to the ambient set normalizer. -/
theorem Dade_ind_restriction_apply_formula
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (B : DadeSubset A) (g : G) :
    Dade_ind_restriction ddA alpha B g =
      (Nat.card (DadeSetNormalizer ddA B) : k)⁻¹ *
        ∑ x : G,
          if hx : (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
              DadeSetNormalizer ddA B then
            alpha (Dade_restrm ddA B
              ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hx⟩)
          else 0 := by
  let M := DadeSetNormalizer ddA B
  let H : Subgroup G := M.subgroupOf G
  have hcard : Nat.card H = Nat.card M :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (Dade_set_normalizer_le ddA B)).toEquiv
  rw [Dade_ind_restriction, ClassFunction.induce_apply_formula, hcard]
  rfl

/-- The first clause of Coq `Dade_Ind_expansion`: every induced restriction
term vanishes away from the global Dade support. -/
theorem Dade_Ind_expansion_zero
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {a : L | (a : Γ) ∈ A})
    (B : DadeSubset A) (g : G)
    (hg : (g : Γ) ∉ Dade_support ddA) :
    Dade_ind_restriction ddA alpha B g = 0 := by
  rw [Dade_ind_restriction_apply_formula]
  suffices (∑ x : G,
      if hx : (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
          DadeSetNormalizer ddA B then
        alpha (Dade_restrm ddA B
          ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hx⟩)
      else 0) = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro x _hx
  by_cases hxM : (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
      DadeSetNormalizer ddA B
  · rw [dif_pos hxM]
    let m : DadeSetNormalizer ddA B :=
      ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hxM⟩
    let bL : L := Dade_restrm ddA B m
    have hbC : (bL : Γ) ∈ DadeSetComplement ddA B :=
      Dade_restrm_mem_complement ddA B m
    have hbNotA : (bL : Γ) ∉ A := by
      intro hbA
      let b : DadeSetComplement ddA B := ⟨(bL : Γ), hbC⟩
      have hproj : Dade_restrm ddA B m =
          Subgroup.inclusion inf_le_left b := by
        apply Subtype.ext
        rfl
      have hmCoset : (m : Γ) ∈
          (DadeSetSignalizer ddA B : Set Γ) *
            ({(b : Γ)} : Set Γ) :=
        (Dade_restrm_eq_iff_mem_rightCoset ddA B m b).mp hproj
      have hmSupport : (m : Γ) ∈ Dade_support1 ddA (b : Γ) :=
        Dade_setSignalizer_rightCoset_subset_support1
          ddA B b hbA hmCoset
      have hgSupport : (g : Γ) ∈ Dade_support1 ddA (b : Γ) := by
        exact (classSupportWithin_rightConj_iff
          (G := G)
          (S := (DadeSignalizer ddA (b : Γ) : Set Γ) *
            ({(b : Γ)} : Set Γ)) x.property).mp hmSupport
      exact hg ⟨(b : Γ), hbA, hgSupport⟩
    exact ClassFunction.eq_zero_of_mem_supportedOn halpha hbNotA
  · rw [dif_neg hxM]

/-- The value clause of Coq `Dade_Ind_expansion`: on the first support
attached to `a`, the induced restriction is the normalized conjugator
count times `alpha a`. -/
theorem Dade_Ind_expansion_value
    [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {a : L | (a : Γ) ∈ A})
    (B : DadeSubset A) (g : G) {a : Γ} (ha : a ∈ A)
    (hg : (g : Γ) ∈ Dade_support1 ddA a) :
    Dade_ind_restriction ddA alpha B g =
      (alpha ⟨a, ddA.1.1 ha⟩ /
        (Nat.card (DadeSetNormalizer ddA B) : k)) *
        DadeIndExpansionCount ddA B g a := by
  rw [Dade_ind_restriction_apply_formula,
    DadeIndExpansionCount_eq_sum]
  have hsum :
      (∑ x : G,
        if hx : (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
            DadeSetNormalizer ddA B then
          alpha (Dade_restrm ddA B
            ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hx⟩)
        else 0) =
      alpha ⟨a, ddA.1.1 ha⟩ *
        ∑ x : G,
          if hx : (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
              DadeSetNormalizer ddA B then
            if ((Dade_restrm ddA B
                ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hx⟩ : L) : Γ) ∈
                DadeNormalizerConjugacySlice ddA B a then
              1
            else 0
          else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hxM : (x : Γ)⁻¹ * (g : Γ) * (x : Γ) ∈
        DadeSetNormalizer ddA B
    · rw [dif_pos hxM, dif_pos hxM,
        Dade_restriction_value_indicator ddA alpha halpha B g a ha hg x hxM]
      by_cases hb : ((Dade_restrm ddA B
          ⟨(x : Γ)⁻¹ * (g : Γ) * (x : Γ), hxM⟩ : L) : Γ) ∈
          DadeNormalizerConjugacySlice ddA B a <;> simp [hb]
    · rw [dif_neg hxM, dif_neg hxM, mul_zero]
  rw [hsum, div_eq_mul_inv]
  ring

/-- Peterfalvi 2.10.3, Coq `Dade_Ind_expansion`. -/
theorem Dade_Ind_expansion
    [Fintype Γ]
    {k : Type v} [Field k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (halpha : alpha ∈
      ClassFunction.supportedOn {a : L | (a : Γ) ∈ A})
    (B : DadeSubset A) (g : G) :
    ((g : Γ) ∉ Dade_support ddA →
      Dade_ind_restriction ddA alpha B g = 0) ∧
    (∀ {a : Γ} (ha : a ∈ A), (g : Γ) ∈ Dade_support1 ddA a →
      Dade_ind_restriction ddA alpha B g =
        (alpha ⟨a, ddA.1.1 ha⟩ /
          (Nat.card (DadeSetNormalizer ddA B) : k)) *
          DadeIndExpansionCount ddA B g a) := by
  constructor
  · exact Dade_Ind_expansion_zero ddA alpha halpha B g
  · intro a ha hg
    exact Dade_Ind_expansion_value ddA alpha halpha B g ha hg

end

end Submission.OddOrder.PF
