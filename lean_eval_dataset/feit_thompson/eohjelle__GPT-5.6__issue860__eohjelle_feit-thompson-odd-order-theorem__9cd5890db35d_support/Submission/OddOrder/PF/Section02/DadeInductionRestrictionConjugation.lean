import Submission.OddOrder.PF.Section01.SubgroupInductionConjugation
import Submission.OddOrder.PF.Section02.DadeExpansionRestriction

/-!
# Peterfalvi 2.10.1: conjugacy invariance of the induced restriction terms

The MathComp notation `B :^ x` means `x⁻¹ B x`, whereas the action on
`DadeSubset A` used by the Lean port is `x • B = x B x⁻¹`.  Thus the theorem
below has the same content as Coq `Dade_Ind_restr_J`, with the conjugating
element inverted relative to the source notation.

Coq class functions on subgroups are ambient functions extended by zero.
Lean instead gives a class function the subgroup type as its domain.  We
therefore transport `Dade_cfun_restriction ddA B alpha` to the copy of the
set normalizer inside `G` before inducing it.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u v

variable {Γ : Type u} [Group Γ]

/-- The set signalizer is transported by the conjugation action on Dade
subsets. -/
theorem Dade_set_signalizer_smul
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : L) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    Dade_set_signalizer ddA (x • B : DadeSubset A) =
      (Dade_set_signalizer ddA B).map
        (MulAut.conj (x : Γ)).toMonoidHom := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map_equiv]
    change (x : Γ)⁻¹ * y * (x : Γ) ∈
      Dade_set_signalizer ddA (B : Set Γ)
    change (x : Γ)⁻¹ * y * (x : Γ) ∈
      ⨅ b : (B : Set Γ), DadeSignalizer ddA b
    rw [Subgroup.mem_iInf]
    intro b
    have hxb : (x : Γ) * (b : Γ) * (x : Γ)⁻¹ ∈
        ((x • B : DadeSubset A) : Set Γ) := by
      rw [coe_dadeSubset_smul ddA]
      exact ⟨b, b.property, rfl⟩
    have hyxb := (Subgroup.mem_iInf.mp hy)
      ⟨(x : Γ) * (b : Γ) * (x : Γ)⁻¹, hxb⟩
    have hJ := DadeJ ddA (b : Γ) (x : Γ)⁻¹ (L.inv_mem x.property)
    simp only [inv_inv] at hJ
    rw [hJ] at hyxb
    exact Subgroup.mem_map_equiv.mp hyxb
  · intro hy
    rw [Subgroup.mem_map_equiv] at hy
    change (x : Γ)⁻¹ * y * (x : Γ) ∈
      Dade_set_signalizer ddA (B : Set Γ) at hy
    change y ∈ ⨅ a : (((x • B : DadeSubset A) : Set Γ)),
      DadeSignalizer ddA a
    rw [Subgroup.mem_iInf]
    rintro ⟨a, ha⟩
    rw [coe_dadeSubset_smul ddA] at ha
    rcases ha with ⟨b, hb, rfl⟩
    have hyb := (Subgroup.mem_iInf.mp hy) ⟨b, hb⟩
    have hJ := DadeJ ddA (b : Γ) (x : Γ)⁻¹ (L.inv_mem x.property)
    simp only [inv_inv] at hJ
    change y ∈ DadeSignalizer ddA
      ((x : Γ) * (b : Γ) * (x : Γ)⁻¹)
    rw [hJ]
    have hymap := Subgroup.mem_map_of_mem
      (MulAut.conj (x : Γ)).toMonoidHom hyb
    convert hymap using 1
    symm
    change (x : Γ) * ((x : Γ)⁻¹ * y * (x : Γ)) * (x : Γ)⁻¹ = y
    group

/-- Setwise normalizers of Dade subsets are transported by conjugation. -/
private theorem Dade_setwiseNormalizer_smul
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : L) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    Subgroup.normalizer ((x • B : DadeSubset A) : Set Γ) =
      (Subgroup.normalizer (B : Set Γ)).map
        (MulAut.conj (x : Γ)).toMonoidHom := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  ext y
  rw [Subgroup.mem_map_equiv]
  change y ∈ Subgroup.normalizer (((x • B : DadeSubset A) : Set Γ)) ↔
    (x : Γ)⁻¹ * y * (x : Γ) ∈ Subgroup.normalizer (B : Set Γ)
  rw [Subgroup.mem_set_normalizer_iff'',
    Subgroup.mem_set_normalizer_iff'']
  rw [coe_dadeSubset_smul ddA]
  constructor
  · intro hy b
    have himage := hy ((x : Γ) * b * (x : Γ)⁻¹)
    constructor
    · intro hb
      have hmem := himage.mp ⟨b, hb, rfl⟩
      rcases hmem with ⟨c, hc, hcy⟩
      change (x : Γ) * c * (x : Γ)⁻¹ =
        y⁻¹ * ((x : Γ) * b * (x : Γ)⁻¹) * y at hcy
      have heq : (x : Γ)⁻¹ * y⁻¹ * (x : Γ) * b *
          (x : Γ)⁻¹ * y * (x : Γ) = c := by
        calc
          _ = (x : Γ)⁻¹ *
              (y⁻¹ * ((x : Γ) * b * (x : Γ)⁻¹) * y) *
              (x : Γ) := by group
          _ = (x : Γ)⁻¹ * ((x : Γ) * c * (x : Γ)⁻¹) *
              (x : Γ) := by rw [← hcy]
          _ = c := by group
      have hexplicit : (x : Γ)⁻¹ * y⁻¹ * (x : Γ) * b *
          (x : Γ)⁻¹ * y * (x : Γ) ∈ (B : Set Γ) := by
        rwa [heq]
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hexplicit
    · intro hb
      have hright : y⁻¹ * ((x : Γ) * b * (x : Γ)⁻¹) * y ∈
          MulAut.conj (x : Γ) '' (B : Set Γ) := by
        have hb' : (x : Γ)⁻¹ * y⁻¹ * (x : Γ) * b *
            (x : Γ)⁻¹ * y * (x : Γ) ∈ (B : Set Γ) := by
          simpa only [mul_inv_rev, inv_inv, mul_assoc] using hb
        refine ⟨(x : Γ)⁻¹ * y⁻¹ * (x : Γ) * b *
            (x : Γ)⁻¹ * y * (x : Γ), hb', ?_⟩
        change (x : Γ) *
          ((x : Γ)⁻¹ * y⁻¹ * (x : Γ) * b *
            (x : Γ)⁻¹ * y * (x : Γ)) * (x : Γ)⁻¹ = _
        group
      rcases himage.mpr hright with ⟨c, hc, hcb⟩
      have : c = b := by
        apply (MulAut.conj (x : Γ)).injective
        simpa only [MulAut.conj_apply] using hcb
      rwa [← this]
  · intro hy h
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' := (hy b).mp hb
      have hb'' : (x : Γ)⁻¹ * y⁻¹ * (x : Γ) * b *
          (x : Γ)⁻¹ * y * (x : Γ) ∈ (B : Set Γ) := by
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using hb'
      refine ⟨(x : Γ)⁻¹ * y⁻¹ * (x : Γ) * b *
          (x : Γ)⁻¹ * y * (x : Γ), hb'', ?_⟩
      change (x : Γ) *
        ((x : Γ)⁻¹ * y⁻¹ * (x : Γ) * b *
          (x : Γ)⁻¹ * y * (x : Γ)) * (x : Γ)⁻¹ = _
      simp only [MulAut.conj_apply]
      group
    · rintro ⟨c, hc, hcy⟩
      change (x : Γ) * c * (x : Γ)⁻¹ = y⁻¹ * h * y at hcy
      let b : Γ := (x : Γ)⁻¹ * y * (x : Γ) * c *
        (x : Γ)⁻¹ * y⁻¹ * (x : Γ)
      have hbExplicit : (x : Γ)⁻¹ * y⁻¹ * (x : Γ) * b *
          (x : Γ)⁻¹ * y * (x : Γ) ∈ (B : Set Γ) := by
        convert hc using 1
        dsimp [b]
        group
      have hb : b ∈ (B : Set Γ) := (hy b).mpr (by
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using hbExplicit)
      refine ⟨b, hb, ?_⟩
      calc
        (MulAut.conj (x : Γ)) b =
            y * ((x : Γ) * c * (x : Γ)⁻¹) * y⁻¹ := by
          dsimp [b, MulAut.conj_apply]
          group
        _ = y * (y⁻¹ * h * y) * y⁻¹ := by rw [hcy]
        _ = h := by group

/-- The complement factor in the set normalizer is transported by
conjugation. -/
theorem Dade_set_complement_smul
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : L) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    DadeSetComplement ddA (x • B) =
      (DadeSetComplement ddA B).map
        (MulAut.conj (x : Γ)).toMonoidHom := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  unfold DadeSetComplement
  calc
    L ⊓ Subgroup.normalizer (((x • B : DadeSubset A) : Set Γ)) =
        L.map (MulAut.conj (x : Γ)).toMonoidHom ⊓
          (Subgroup.normalizer (B : Set Γ)).map
            (MulAut.conj (x : Γ)).toMonoidHom := by
      congr 1
      · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (Subgroup.le_normalizer x.property)).symm
      · exact Dade_setwiseNormalizer_smul ddA x B
    _ = (L ⊓ Subgroup.normalizer (B : Set Γ)).map
          (MulAut.conj (x : Γ)).toMonoidHom :=
      (Subgroup.map_inf _ _ _ (MulAut.conj (x : Γ)).injective).symm

/-- The whole set normalizer is transported by conjugation. -/
private theorem Dade_set_normalizer_smul
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : L) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    DadeSetNormalizer ddA (x • B) =
      (DadeSetNormalizer ddA B).map
        (MulAut.conj (x : Γ)).toMonoidHom := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  unfold DadeSetNormalizer Dade_set_normalizer
  rw [Subgroup.map_sup, Dade_set_signalizer_smul ddA x B]
  congr 1
  exact Dade_set_complement_smul ddA x B

/-- Every set normalizer occurring in the expansion is a subgroup of `G`.
This is Coq's local lemma `sMG`. -/
theorem Dade_set_normalizer_le
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (B : DadeSubset A) :
    DadeSetNormalizer ddA B ≤ G := by
  obtain ⟨a, haB⟩ := B.property.2
  have hHa : Dade_set_signalizer ddA (B : Set Γ) ≤
      DadeSignalizer ddA a :=
    iInf_le_of_le ⟨a, haB⟩ le_rfl
  have hHG : Dade_set_signalizer ddA (B : Set Γ) ≤ G :=
    hHa.trans (Dade_signalizer_sub ddA a)
  have hNG : L ⊓ Subgroup.normalizer (B : Set Γ) ≤ G :=
    inf_le_left.trans ddA.2.1
  exact sup_le hHG hNG

/-- Evaluation of the projection on an explicitly factored element of the
internal semidirect product. -/
private theorem Dade_restrm_apply_mul
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
  rw [map_mul]
  rw [show Dade_restrm ddA B nM = 1 by
      exact Dade_restrm_apply_signalizer ddA B n,
    show Dade_restrm ddA B hM = Subgroup.inclusion inf_le_left h by
      exact Dade_restrm_apply_complement ddA B h,
    one_mul]

/-- The semidirect-product projections for conjugate Dade subsets commute
with conjugation. -/
private theorem Dade_restrm_smul
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : L) (B : DadeSubset A)
    (y : DadeSetNormalizer ddA B) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    let yx : DadeSetNormalizer ddA (x • B) :=
      ⟨(x : Γ) * (y : Γ) * (x : Γ)⁻¹, by
        rw [Dade_set_normalizer_smul ddA x B]
        have hy := Subgroup.mem_map_of_mem
          (MulAut.conj (x : Γ)).toMonoidHom y.property
        convert hy using 1
        exact (MulAut.conj_apply (x : Γ) (y : Γ)).symm⟩
    Dade_restrm ddA (x • B) yx =
      x * Dade_restrm ddA B y * x⁻¹ := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  let hsd := Dade_set_sdprod_subtype ddA B
  let N : Subgroup (DadeSetNormalizer ddA B) :=
    (DadeSetSignalizer ddA B).subgroupOf (DadeSetNormalizer ddA B)
  let H : Subgroup (DadeSetNormalizer ddA B) :=
    (DadeSetComplement ddA B).subgroupOf (DadeSetNormalizer ddA B)
  letI : N.Normal := by simpa [N, hsd] using hsd.2.2.1
  have hcomp : N.IsComplement' H := by
    simpa [N, H, hsd] using hsd.2.2.2
  obtain ⟨p, hp, _hpUnique⟩ := hcomp.existsUnique y
  rcases p with ⟨n, h⟩
  let n₀ : DadeSetSignalizer ddA B :=
    ⟨((n : N) : DadeSetNormalizer ddA B), n.property⟩
  let h₀ : DadeSetComplement ddA B :=
    ⟨((h : H) : DadeSetNormalizer ddA B), h.property⟩
  have hpΓ : (n₀ : Γ) * (h₀ : Γ) = (y : Γ) := by
    exact congrArg (fun z : DadeSetNormalizer ddA B ↦ (z : Γ)) hp
  have hyFactor : y =
      (⟨(n₀ : Γ) * (h₀ : Γ),
        (DadeSetNormalizer ddA B).mul_mem
          (hsd.1 n₀.property) (hsd.2.1 h₀.property)⟩ :
        DadeSetNormalizer ddA B) := by
    apply Subtype.ext
    exact hpΓ.symm
  have hproj : Dade_restrm ddA B y =
      Subgroup.inclusion inf_le_left h₀ := by
    rw [hyFactor]
    exact Dade_restrm_apply_mul ddA B n₀ h₀

  let nₓ : DadeSetSignalizer ddA (x • B) :=
    ⟨(x : Γ) * (n₀ : Γ) * (x : Γ)⁻¹, by
      change (x : Γ) * (n₀ : Γ) * (x : Γ)⁻¹ ∈
        Dade_set_signalizer ddA (((x • B : DadeSubset A) : Set Γ))
      rw [Dade_set_signalizer_smul ddA x B]
      exact Subgroup.mem_map_of_mem
        (MulAut.conj (x : Γ)).toMonoidHom n₀.property⟩
  let hₓ : DadeSetComplement ddA (x • B) :=
    ⟨(x : Γ) * (h₀ : Γ) * (x : Γ)⁻¹, by
      change (x : Γ) * (h₀ : Γ) * (x : Γ)⁻¹ ∈
        L ⊓ Subgroup.normalizer (((x • B : DadeSubset A) : Set Γ))
      rw [show L ⊓ Subgroup.normalizer
          (((x • B : DadeSubset A) : Set Γ)) =
          (L ⊓ Subgroup.normalizer (B : Set Γ)).map
            (MulAut.conj (x : Γ)).toMonoidHom by
        exact Dade_set_complement_smul ddA x B]
      exact Subgroup.mem_map_of_mem
        (MulAut.conj (x : Γ)).toMonoidHom h₀.property⟩
  let yx : DadeSetNormalizer ddA (x • B) :=
    ⟨(x : Γ) * (y : Γ) * (x : Γ)⁻¹, by
      change (x : Γ) * (y : Γ) * (x : Γ)⁻¹ ∈
        Dade_set_normalizer ddA (((x • B : DadeSubset A) : Set Γ))
      rw [show Dade_set_normalizer ddA
          (((x • B : DadeSubset A) : Set Γ)) =
          (Dade_set_normalizer ddA (B : Set Γ)).map
            (MulAut.conj (x : Γ)).toMonoidHom by
        exact Dade_set_normalizer_smul ddA x B]
      exact Subgroup.mem_map_of_mem
        (MulAut.conj (x : Γ)).toMonoidHom y.property⟩
  have hyxFactor : yx =
      (⟨(nₓ : Γ) * (hₓ : Γ),
        (DadeSetNormalizer ddA (x • B)).mul_mem
          ((Dade_set_sdprod_subtype ddA (x • B)).1 nₓ.property)
          ((Dade_set_sdprod_subtype ddA (x • B)).2.1 hₓ.property)⟩ :
        DadeSetNormalizer ddA (x • B)) := by
    apply Subtype.ext
    change (x : Γ) * (y : Γ) * (x : Γ)⁻¹ =
      ((x : Γ) * (n₀ : Γ) * (x : Γ)⁻¹) *
        ((x : Γ) * (h₀ : Γ) * (x : Γ)⁻¹)
    rw [← hpΓ]
    group
  calc
    Dade_restrm ddA (x • B) yx =
        Dade_restrm ddA (x • B)
          (⟨(nₓ : Γ) * (hₓ : Γ),
            (DadeSetNormalizer ddA (x • B)).mul_mem
              ((Dade_set_sdprod_subtype ddA (x • B)).1 nₓ.property)
              ((Dade_set_sdprod_subtype ddA (x • B)).2.1 hₓ.property)⟩ :
            DadeSetNormalizer ddA (x • B)) := congrArg _ hyxFactor
    _ = Subgroup.inclusion inf_le_left hₓ :=
      Dade_restrm_apply_mul ddA (x • B) nₓ hₓ
    _ = x * Subgroup.inclusion inf_le_left h₀ * x⁻¹ := by
      apply Subtype.ext
      rfl
    _ = x * Dade_restrm ddA B y * x⁻¹ := by rw [hproj]

/-- The restriction class functions themselves are compatible with
conjugating the indexing subset. -/
private theorem Dade_cfun_restriction_smul
    [Finite Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (x : L) (B : DadeSubset A) (y : DadeSetNormalizer ddA B) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    let yx : DadeSetNormalizer ddA (x • B) :=
      ⟨(x : Γ) * (y : Γ) * (x : Γ)⁻¹, by
        rw [Dade_set_normalizer_smul ddA x B]
        exact Subgroup.mem_map_of_mem
          (MulAut.conj (x : Γ)).toMonoidHom y.property⟩
    Dade_cfun_restriction ddA (x • B) alpha yx =
      Dade_cfun_restriction ddA B alpha y := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  let yx : DadeSetNormalizer ddA (x • B) :=
    ⟨(x : Γ) * (y : Γ) * (x : Γ)⁻¹, by
      rw [Dade_set_normalizer_smul ddA x B]
      have hy := Subgroup.mem_map_of_mem
        (MulAut.conj (x : Γ)).toMonoidHom y.property
      convert hy using 1
      exact (MulAut.conj_apply (x : Γ) (y : Γ)).symm⟩
  change Dade_cfun_restriction ddA (x • B) alpha yx =
    Dade_cfun_restriction ddA B alpha y
  rw [Dade_restrictionE, Dade_restrictionE,
    show Dade_restrm ddA (x • B) yx =
        x * Dade_restrm ddA B y * x⁻¹ by
      exact Dade_restrm_smul ddA x B y]
  exact ClassFunction.conj_apply alpha x (Dade_restrm ddA B y)

/-- Inside `G`, the set normalizer belonging to `x • B` is the conjugate
of the one belonging to `B`. -/
private theorem Dade_set_normalizer_subgroupOf_smul
    [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (x : L) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    let xG : G := ⟨(x : Γ), ddA.2.1 x.property⟩
    conjugateSubgroup
        ((DadeSetNormalizer ddA B).subgroupOf G) xG =
      (DadeSetNormalizer ddA (x • B)).subgroupOf G := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  let xG : G := ⟨(x : Γ), ddA.2.1 x.property⟩
  ext z
  unfold conjugateSubgroup
  rw [Subgroup.mem_map_equiv]
  change (x : Γ)⁻¹ * (z : Γ) * (x : Γ) ∈
      DadeSetNormalizer ddA B ↔
    (z : Γ) ∈ DadeSetNormalizer ddA (x • B)
  rw [Dade_set_normalizer_smul ddA x B, Subgroup.mem_map_equiv]
  rfl

/-- The subgroup-typed restriction term, transported to the copy of the set
normalizer inside `G`.  This transport replaces MathComp's convention that
class functions on subgroups are ambient functions extended by zero. -/
noncomputable def Dade_inducing_restriction
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (B : DadeSubset A) :
    ClassFunction ((DadeSetNormalizer ddA B).subgroupOf G) k :=
  ClassFunction.comap
    (Subgroup.subgroupOfEquivOfLe
      (Dade_set_normalizer_le ddA B)).toMonoidHom
    (Dade_cfun_restriction ddA B alpha)

/-- The term obtained by inducing the restriction attached to `B` from its
set normalizer to `G`. -/
noncomputable def Dade_ind_restriction
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (B : DadeSubset A) : ClassFunction G k :=
  ClassFunction.induce ((DadeSetNormalizer ddA B).subgroupOf G)
    (Dade_inducing_restriction ddA alpha B)

/-- Peterfalvi (2.10.1), Coq `Dade_Ind_restr_J`: replacing a nonempty Dade
subset by an `L`-conjugate does not change its induced restriction term. -/
theorem Dade_Ind_restr_J
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (x : L) (B : DadeSubset A) :
    letI : MulAction L (DadeSubset A) :=
      dadeSubsetConjugationAction ddA
    Dade_ind_restriction ddA alpha (x • B) =
      Dade_ind_restriction ddA alpha B := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  let H : Subgroup G := (DadeSetNormalizer ddA B).subgroupOf G
  let Hx : Subgroup G :=
    (DadeSetNormalizer ddA (x • B)).subgroupOf G
  let xG : G := ⟨(x : Γ), ddA.2.1 x.property⟩
  have hsub : conjugateSubgroup H xG = Hx := by
    simpa [H, Hx, xG] using
      Dade_set_normalizer_subgroupOf_smul ddA x B
  change ClassFunction.induce Hx
      (Dade_inducing_restriction ddA alpha (x • B)) =
    ClassFunction.induce H
      (Dade_inducing_restriction ddA alpha B)
  apply ClassFunction.ext
  intro g
  rw [ClassFunction.induce_apply_formula,
    ClassFunction.induce_apply_formula]
  let e : H ≃* Hx :=
    (conjugateSubgroupEquiv H xG).trans
      (MulEquiv.subgroupCongr hsub)
  have hcard : Nat.card Hx = Nat.card H :=
    (Nat.card_congr e.toEquiv).symm
  rw [hcard]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight xG)
    (fun z : G ↦ ClassFunction.inductionKernel Hx
      (Dade_inducing_restriction ddA alpha (x • B)) z g)
    (fun z : G ↦ ClassFunction.inductionKernel H
      (Dade_inducing_restriction ddA alpha B) z g) fun z ↦ ?_
  change ClassFunction.inductionKernel Hx
      (Dade_inducing_restriction ddA alpha (x • B)) z g =
    ClassFunction.inductionKernel H
      (Dade_inducing_restriction ddA alpha B) (z * xG) g
  have hmem : z⁻¹ * g * z ∈ Hx ↔
      (z * xG)⁻¹ * g * (z * xG) ∈ H := by
    rw [← hsub]
    rw [show z⁻¹ * g * z ∈ conjugateSubgroup H xG ↔
        (MulAut.conj xG).symm (z⁻¹ * g * z) ∈ H by
      exact Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply, mul_inv_rev, mul_assoc]
  by_cases hz : z⁻¹ * g * z ∈ Hx
  · have hzx : (z * xG)⁻¹ * g * (z * xG) ∈ H := hmem.mp hz
    rw [ClassFunction.inductionKernel_of_mem _ _ z g hz,
      ClassFunction.inductionKernel_of_mem _ _ (z * xG) g hzx]
    have hzM : ((((z⁻¹ * g * z : G) : G) : Γ)) ∈
        DadeSetNormalizer ddA (x • B) := by
      change z⁻¹ * g * z ∈ Hx at hz
      exact hz
    have hzxM : (((((z * xG)⁻¹ * g * (z * xG) : G) : G) : Γ)) ∈
        DadeSetNormalizer ddA B := by
      change (z * xG)⁻¹ * g * (z * xG) ∈ H at hzx
      exact hzx
    let y : DadeSetNormalizer ddA B :=
      ⟨((z * xG)⁻¹ * g * (z * xG) : G), hzxM⟩
    let yx : DadeSetNormalizer ddA (x • B) :=
      ⟨(z⁻¹ * g * z : G), hzM⟩
    change Dade_cfun_restriction ddA (x • B) alpha yx =
      Dade_cfun_restriction ddA B alpha y
    let cy : DadeSetNormalizer ddA (x • B) :=
      ⟨(x : Γ) * (y : Γ) * (x : Γ)⁻¹, by
        rw [Dade_set_normalizer_smul ddA x B]
        have hy := Subgroup.mem_map_of_mem
          (MulAut.conj (x : Γ)).toMonoidHom y.property
        convert hy using 1
        exact (MulAut.conj_apply (x : Γ) (y : Γ)).symm⟩
    have hcy : cy = yx := by
      apply Subtype.ext
      change (x : Γ) *
          (((z * xG)⁻¹ * g * (z * xG) : G) : Γ) *
          (x : Γ)⁻¹ = (((z⁻¹ * g * z : G) : G) : Γ)
      dsimp [xG]
      group
    rw [← hcy]
    exact Dade_cfun_restriction_smul ddA alpha x B y
  · have hzx : (z * xG)⁻¹ * g * (z * xG) ∉ H :=
      fun h ↦ hz (hmem.mpr h)
    rw [ClassFunction.inductionKernel_of_notMem _ _ z g hz,
      ClassFunction.inductionKernel_of_notMem _ _ (z * xG) g hzx]

/-- Orbit-representative form of `Dade_Ind_restr_J`, used when the expansion
sum is reindexed by `Dade_transversal`. -/
theorem Dade_Ind_restr_transversal
    [Fintype Γ]
    {k : Type v} [Field k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k)
    (B : DadeSubset A) :
    Dade_ind_restriction ddA alpha
        (Dade_transversal
          (Quotient.mk'' B : DadeSubsetOrbit ddA)) =
      Dade_ind_restriction ddA alpha B := by
  letI : MulAction L (DadeSubset A) :=
    dadeSubsetConjugationAction ddA
  obtain ⟨x, hx⟩ := exists_smul_eq_Dade_transversal (ddA := ddA) B
  rw [← hx]
  exact Dade_Ind_restr_J ddA alpha x B

end

end Submission.OddOrder.PF
