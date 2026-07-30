import Submission.OddOrder.PF.Section02.ClassSupportPartition
import Submission.OddOrder.PF.Section02.DadeGlobalSupport
import Submission.OddOrder.PF.Section02.DadeSupportTI

/-!
# Partitions of the Dade support

The first Dade supports partition the global support.  Their blocks correspond
to the `L`-conjugacy classes represented in `A`; this correspondence replaces
the representative finset used in the source proof of Dade reciprocity.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped Classical Pointwise

universe u

/-- The family of `L`-conjugacy classes represented in `A`. -/
def conjugacyClassBlocks
    {Γ : Type u} [Group Γ] (L : Subgroup Γ) (A : Set Γ) : Set (Set Γ) :=
  {B | ∃ a ∈ A, B = conjugacyClassWithin L a}

/-- The family of first Dade-support blocks represented in `A`. -/
def Dade_supportBlocks
    {Γ : Type u} [Group Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) : Set (Set Γ) :=
  {B | ∃ a ∈ A, B = Dade_support1 ddA a}

/-- The `L`-conjugacy classes represented in a normalized set partition that
set. -/
theorem conjugacyClassBlocks_partition
    {Γ : Type u} [Group Γ] (L : Subgroup Γ) (A : Set Γ)
    (hnorm : L ≤ Subgroup.normalizer A) :
    IsSetPartition (conjugacyClassBlocks L A) A := by
  constructor
  · ext x
    constructor
    · intro hx
      rcases Set.mem_sUnion.mp hx with ⟨B, ⟨a, ha, rfl⟩, l, hl, rfl⟩
      exact (Subgroup.mem_set_normalizer_iff''.mp (hnorm hl) a).mp ha
    · intro hx
      apply Set.mem_sUnion.mpr
      refine ⟨conjugacyClassWithin L x, ⟨x, hx, rfl⟩, ?_⟩
      exact ⟨1, L.one_mem, by simp⟩
  constructor
  · rw [Set.pairwiseDisjoint_iff]
    rintro B ⟨a, ha, rfl⟩ C ⟨b, hb, rfl⟩ hinter
    rcases hinter with ⟨x, ⟨l, hl, hla⟩, ⟨k, hk, hkb⟩⟩
    change l⁻¹ * a * l = x at hla
    change k⁻¹ * b * k = x at hkb
    ext y
    constructor
    · rintro ⟨d, hd, rfl⟩
      refine ⟨k * l⁻¹ * d,
        L.mul_mem (L.mul_mem hk (L.inv_mem hl)) hd, ?_⟩
      calc
        (k * l⁻¹ * d)⁻¹ * b * (k * l⁻¹ * d) =
            d⁻¹ * l * (k⁻¹ * b * k) * l⁻¹ * d := by group
        _ = d⁻¹ * l * (l⁻¹ * a * l) * l⁻¹ * d := by
          rw [hkb.trans hla.symm]
        _ = d⁻¹ * a * d := by group
    · rintro ⟨d, hd, rfl⟩
      refine ⟨l * k⁻¹ * d,
        L.mul_mem (L.mul_mem hl (L.inv_mem hk)) hd, ?_⟩
      calc
        (l * k⁻¹ * d)⁻¹ * a * (l * k⁻¹ * d) =
            d⁻¹ * k * (l⁻¹ * a * l) * k⁻¹ * d := by group
        _ = d⁻¹ * k * (k⁻¹ * b * k) * k⁻¹ * d := by
          rw [(hkb.trans hla.symm).symm]
        _ = d⁻¹ * b * d := by group
  · rintro ⟨a, ha, hempty⟩
    have : a ∈ (∅ : Set Γ) := by
      rw [hempty]
      exact ⟨1, L.one_mem, by simp⟩
    exact this

/-- The first Dade supports indexed by `A` partition the global Dade
support. -/
theorem Dade_supportBlocks_partition
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    IsSetPartition (Dade_supportBlocks ddA) (Dade_support ddA) := by
  constructor
  · ext x
    constructor
    · intro hx
      rcases Set.mem_sUnion.mp hx with ⟨B, ⟨a, ha, rfl⟩, hxa⟩
      exact ⟨a, ha, hxa⟩
    · rintro ⟨a, ha, hxa⟩
      exact Set.mem_sUnion.mpr
        ⟨Dade_support1 ddA a, ⟨a, ha, rfl⟩, hxa⟩
  constructor
  · rw [Set.pairwiseDisjoint_iff]
    rintro B ⟨a, ha, rfl⟩ C ⟨b, hb, rfl⟩ hinter
    rcases Dade_support1_TI ddA ha hb hinter with ⟨x, hx, rfl⟩
    exact (Dade_support1_id ddA a x hx).symm
  · rintro ⟨a, ha, hempty⟩
    have hmem : a ∈ Dade_support1 ddA a := by
      simpa using
        mem_Dade_support1 ddA ha (DadeSignalizer ddA a).one_mem
    rw [← hempty] at hmem
    exact hmem

private theorem Dade_support1_eq_iff_conjugacyClassWithin_eq
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) {a b : Γ}
    (ha : a ∈ A) (hb : b ∈ A) :
    Dade_support1 ddA a = Dade_support1 ddA b ↔
      conjugacyClassWithin L a = conjugacyClassWithin L b := by
  constructor
  · intro hsupp
    have hmem : a ∈ Dade_support1 ddA a := by
      simpa using
        mem_Dade_support1 ddA ha (DadeSignalizer ddA a).one_mem
    have hinter :
        (Dade_support1 ddA a ∩ Dade_support1 ddA b).Nonempty :=
      ⟨a, hmem, by rw [← hsupp]; exact hmem⟩
    rcases Dade_support1_TI ddA ha hb hinter with ⟨x, hx, rfl⟩
    ext y
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨x⁻¹ * d, L.mul_mem (L.inv_mem hx) hd, by group⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨x * d, L.mul_mem hx hd, by group⟩
  · intro hclass
    have hbclass : b ∈ conjugacyClassWithin L a := by
      rw [hclass]
      exact ⟨1, L.one_mem, by simp⟩
    rcases hbclass with ⟨x, hx, rfl⟩
    exact (Dade_support1_id ddA a x hx).symm

private noncomputable def conjugacyBlockOfSupportBlock
    {Γ : Type u} [Group Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    Dade_supportBlocks ddA → conjugacyClassBlocks L A := fun B => by
  let a : Γ := Classical.choose B.property
  have ha : a ∈ A := (Classical.choose_spec B.property).1
  exact ⟨conjugacyClassWithin L a, ⟨a, ha, rfl⟩⟩

private theorem conjugacyBlockOfSupportBlock_injective
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    Function.Injective (conjugacyBlockOfSupportBlock ddA) := by
  intro B C hBC
  apply Subtype.ext
  let a : Γ := Classical.choose B.property
  have ha : a ∈ A := (Classical.choose_spec B.property).1
  have hBa : (B : Set Γ) = Dade_support1 ddA a :=
    (Classical.choose_spec B.property).2
  let b : Γ := Classical.choose C.property
  have hb : b ∈ A := (Classical.choose_spec C.property).1
  have hCb : (C : Set Γ) = Dade_support1 ddA b :=
    (Classical.choose_spec C.property).2
  have hclass : conjugacyClassWithin L a = conjugacyClassWithin L b :=
    congrArg Subtype.val hBC
  have hbclass : b ∈ conjugacyClassWithin L a := by
    rw [hclass]
    exact ⟨1, L.one_mem, by simp⟩
  rcases hbclass with ⟨x, hx, hxb⟩
  rw [hBa, hCb, ← hxb]
  exact (Dade_support1_id ddA a x hx).symm

private theorem conjugacyBlockOfSupportBlock_surjective
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    Function.Surjective (conjugacyBlockOfSupportBlock ddA) := by
  intro C
  let a : Γ := Classical.choose C.property
  have ha : a ∈ A := (Classical.choose_spec C.property).1
  have hCa : (C : Set Γ) = conjugacyClassWithin L a :=
    (Classical.choose_spec C.property).2
  let B : Dade_supportBlocks ddA :=
    ⟨Dade_support1 ddA a, ⟨a, ha, rfl⟩⟩
  refine ⟨B, ?_⟩
  apply Subtype.ext
  change conjugacyClassWithin L (Classical.choose B.property) = C
  have hBchoose : Dade_support1 ddA (Classical.choose B.property) =
      Dade_support1 ddA a := by
    simpa [B] using
      (Classical.choose_spec B.property).2.symm
  have hchooseA : Classical.choose B.property ∈ A :=
    (Classical.choose_spec B.property).1
  rw [hCa]
  exact (Dade_support1_eq_iff_conjugacyClassWithin_eq ddA hchooseA ha).mp
    hBchoose

/-- First-support blocks correspond to the `L`-conjugacy classes represented
in `A`. -/
noncomputable def Dade_supportBlocksEquiv
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    Dade_supportBlocks ddA ≃ conjugacyClassBlocks L A :=
  Equiv.ofBijective (conjugacyBlockOfSupportBlock ddA)
    ⟨conjugacyBlockOfSupportBlock_injective ddA,
      conjugacyBlockOfSupportBlock_surjective ddA⟩

/-- The block correspondence sends the first support at `a` to the
`L`-conjugacy class of `a`. -/
@[simp]
theorem Dade_supportBlocksEquiv_mk
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) {a : Γ} (ha : a ∈ A) :
    Dade_supportBlocksEquiv ddA
        (⟨Dade_support1 ddA a, ⟨a, ha, rfl⟩⟩ :
          Dade_supportBlocks ddA) =
      (⟨conjugacyClassWithin L a, ⟨a, ha, rfl⟩⟩ :
        conjugacyClassBlocks L A) := by
  unfold Dade_supportBlocksEquiv
  change conjugacyBlockOfSupportBlock ddA
      (⟨Dade_support1 ddA a, ⟨a, ha, rfl⟩⟩ :
        Dade_supportBlocks ddA) = _
  apply Subtype.ext
  unfold conjugacyBlockOfSupportBlock
  change conjugacyClassWithin L
      (Classical.choose
        (show Dade_support1 ddA a ∈ Dade_supportBlocks ddA from
          ⟨a, ha, rfl⟩)) =
    conjugacyClassWithin L a
  apply (Dade_support1_eq_iff_conjugacyClassWithin_eq ddA
    ((Classical.choose_spec
      (show Dade_support1 ddA a ∈ Dade_supportBlocks ddA from
        ⟨a, ha, rfl⟩)).1) ha).mp
  exact (Classical.choose_spec
    (show Dade_support1 ddA a ∈ Dade_supportBlocks ddA from
      ⟨a, ha, rfl⟩)).2.symm

/-- The size of an `L`-conjugacy class is the relative index of the
centralizer of its representative in `L`. -/
theorem ncard_conjugacyClassWithin_eq_relIndex
    {Γ : Type u} [Group Γ] (L : Subgroup Γ) (a : Γ) :
    (conjugacyClassWithin L a).ncard =
      (centralizerWithin L (Subgroup.zpowers a)).relIndex L := by
  let conjugationAction := subgroupConjugationActionOnAmbient L
  letI : SMul L Γ := conjugationAction.toSMul
  letI : MulAction L Γ := conjugationAction.toMulAction
  have horbit : MulAction.orbit L a = conjugacyClassWithin L a := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      refine ⟨(l : Γ)⁻¹, L.inv_mem l.property, ?_⟩
      change (((l : Γ)⁻¹)⁻¹ * a * (l : Γ)⁻¹) =
        (l : Γ) * a * (l : Γ)⁻¹
      simp
    · rintro ⟨l, hl, rfl⟩
      refine ⟨⟨l⁻¹, L.inv_mem hl⟩, ?_⟩
      change l⁻¹ * a * (l⁻¹)⁻¹ = l⁻¹ * a * l
      simp
  rw [← horbit, ← MulAction.index_stabilizer L a]
  congr 1
  ext l
  rw [MulAction.mem_stabilizer_iff]
  change ((l : Γ) * a * (l : Γ)⁻¹ = a) ↔ _
  constructor
  · intro hl
    refine ⟨l.property, ?_⟩
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcomm : Commute (l : Γ) a :=
      mul_inv_eq_iff_eq_mul.mp hl
    exact (hcomm.zpow_right n).symm.eq
  · rintro ⟨_, hl⟩
    have hcomm : Commute (l : Γ) a := by
      exact (hl a (Subgroup.mem_zpowers a)).symm
    exact mul_inv_eq_iff_eq_mul.mpr hcomm.eq

end

end Submission.OddOrder.PF
