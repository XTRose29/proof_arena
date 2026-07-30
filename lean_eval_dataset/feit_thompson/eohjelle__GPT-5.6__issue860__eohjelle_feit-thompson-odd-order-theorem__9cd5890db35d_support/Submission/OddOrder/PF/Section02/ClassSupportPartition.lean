import Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset
import Submission.OddOrder.PF.Section02.DadeSupportConjugation

/-!
# Partitions of conjugacy-saturated supports

A finite set partition decomposes sums blockwise.  For a normalized-TI set,
its conjugates form such a partition of its conjugacy-saturated support, and
orbit-stabilizer counts the blocks by the relative index of its normalizer.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

/-- Finsum form of blockwise summation over a finite set partition. -/
theorem IsSetPartition.finsum_mem
    {α M : Type*} [AddCommMonoid M]
    {P : Set (Set α)} {D : Set α}
    (hpart : IsSetPartition P D)
    (hP : P.Finite) (hblocks : ∀ B ∈ P, B.Finite)
    (f : α → M) :
    ∑ᶠ x ∈ D, f x = ∑ᶠ B ∈ P, ∑ᶠ x ∈ B, f x := by
  rw [← hpart.1]
  exact finsum_mem_sUnion hpart.2.1 hP hblocks

/-- Sum a function blockwise over a finite set partition. -/
theorem IsSetPartition.sum_subtype
    {α M : Type*} [Fintype α] [AddCommMonoid M]
    {P : Set (Set α)} {D : Set α}
    (hpart : IsSetPartition P D) (f : α → M) :
    (∑ x : D, f x) = ∑ B : P, ∑ x : (B : Set α), f x := by
  classical
  have hP : P.Finite := Set.toFinite P
  have hblocks : ∀ B ∈ P, B.Finite := fun B _ ↦ Set.toFinite B
  calc
    (∑ x : D, f x) = ∑ᶠ x : D, f x :=
      (finsum_eq_sum_of_fintype (fun x : D ↦ f x)).symm
    _ = ∑ᶠ x ∈ D, f x := finsum_set_coe_eq_finsum_mem D
    _ = ∑ᶠ B ∈ P, ∑ᶠ x ∈ B, f x :=
      hpart.finsum_mem hP hblocks f
    _ = ∑ᶠ B : P, ∑ᶠ x ∈ (B : Set α), f x :=
      (finsum_set_coe_eq_finsum_mem P).symm
    _ = ∑ᶠ B : P, ∑ᶠ x : (B : Set α), f x := by
      congr 1
      funext B
      exact (finsum_set_coe_eq_finsum_mem (B : Set α)).symm
    _ = ∑ B : P, ∑ x : (B : Set α), f x := by
      rw [finsum_eq_sum_of_fintype]
      congr 1
      funext B
      rw [finsum_eq_sum_of_fintype]

/-- The conjugates of a normalized-TI set partition its conjugacy-saturated
support, and their number is the relative index of its normalizer. -/
theorem normalizedTI_classSupport_partition
    {Γ : Type*} [Group Γ]
    {S : Set Γ} {D N : Subgroup Γ}
    (hTI : IsNormalizedTI S D N) :
    let conjugationAction := subgroupConjugationActionOnAmbient D
    letI : SMul D Γ := conjugationAction.toSMul
    letI : MulAction D Γ := conjugationAction.toMulAction
    letI : MulAction D (Set Γ) := Set.mulActionSet
    IsSetPartition (MulAction.orbit D S) (classSupportWithin D S) ∧
      (MulAction.orbit D S).ncard = N.relIndex D := by
  let conjugationAction := subgroupConjugationActionOnAmbient D
  letI : SMul D Γ := conjugationAction.toSMul
  letI : MulAction D Γ := conjugationAction.toMulAction
  letI : MulAction D (Set Γ) := Set.mulActionSet
  change IsSetPartition (MulAction.orbit D S) (classSupportWithin D S) ∧
    (MulAction.orbit D S).ncard = N.relIndex D

  have act_set_eq_of_mem_normalizer (d : D)
      (hd : (d : Γ) ∈ Subgroup.normalizer S) : d • S = S := by
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_set_normalizer_iff.mp hd y).mp hy
    · intro hx
      refine ⟨(d : Γ)⁻¹ * x * (d : Γ),
        (Subgroup.mem_set_normalizer_iff''.mp hd x).mp hx, ?_⟩
      change (d : Γ) * ((d : Γ)⁻¹ * x * (d : Γ)) * (d : Γ)⁻¹ = x
      group

  have hunion : ⋃₀ (MulAction.orbit D S) = classSupportWithin D S := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_sUnion.mp hx with ⟨B, ⟨d, rfl⟩, hxB⟩
      rcases Set.mem_smul_set.mp hxB with ⟨y, hy, rfl⟩
      refine ⟨y, hy, (d : Γ)⁻¹, D.inv_mem d.property, ?_⟩
      change (((d : Γ)⁻¹)⁻¹ * y * (d : Γ)⁻¹) =
        (d : Γ) * y * (d : Γ)⁻¹
      simp only [inv_inv]
    · rintro ⟨y, hy, g, hg, rfl⟩
      let d : D := ⟨g⁻¹, D.inv_mem hg⟩
      apply Set.mem_sUnion.mpr
      refine ⟨d • S, ⟨d, rfl⟩, ?_⟩
      have := Set.smul_mem_smul_set (a := d) hy
      have heq : d • y = g⁻¹ * y * g := by
        change g⁻¹ * y * (g⁻¹)⁻¹ = g⁻¹ * y * g
        simp only [inv_inv]
      change g⁻¹ * y * g ∈ d • S
      rw [← heq]
      exact this

  have hpair : (MulAction.orbit D S).PairwiseDisjoint id := by
    rw [Set.pairwiseDisjoint_iff]
    intro B hB C hC hinter
    rcases hB with ⟨d, rfl⟩
    rcases hC with ⟨e, rfl⟩
    rcases hinter with ⟨x, hxd, hxe⟩
    rcases Set.mem_smul_set.mp hxd with ⟨s, hs, hds⟩
    rcases Set.mem_smul_set.mp hxe with ⟨t, ht, het⟩
    change (d : Γ) * s * (d : Γ)⁻¹ = x at hds
    change (e : Γ) * t * (e : Γ)⁻¹ = x at het
    let g : D := e⁻¹ * d
    have hoverlap :
        (S ∩ (fun a ↦ (g : Γ)⁻¹ * a * (g : Γ)) '' S).Nonempty := by
      refine ⟨s, hs, t, ht, ?_⟩
      calc
        (g : Γ)⁻¹ * t * (g : Γ) =
            (d : Γ)⁻¹ * ((e : Γ) * t * (e : Γ)⁻¹) * (d : Γ) := by
          simp only [g, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        _ = (d : Γ)⁻¹ * x * (d : Γ) := by rw [het]
        _ = s := by
          rw [← hds]
          group
    have hgN : (g : Γ) ∈ N := hTI.2.2 g.property hoverlap
    have hgNorm : (g : Γ) ∈ Subgroup.normalizer S := (hTI.2.1 hgN).2
    have hgS : g • S = S := act_set_eq_of_mem_normalizer g hgNorm
    calc
      d • S = (e * g) • S := by simp [g]
      _ = e • (g • S) := mul_smul e g S
      _ = e • S := by rw [hgS]

  have hnonempty : (∅ : Set Γ) ∉ MulAction.orbit D S := by
    rintro ⟨d, hd⟩
    change d • S = (∅ : Set Γ) at hd
    obtain ⟨s, hs⟩ := hTI.1
    have hds : d • s ∈ d • S := Set.smul_mem_smul_set hs
    rw [hd] at hds
    exact (Set.mem_empty_iff_false (d • s)).mp hds

  have hstab : MulAction.stabilizer D S = N.subgroupOf D := by
    ext d
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hdS
      obtain ⟨s, hs⟩ := hTI.1
      have hds : d • s ∈ S := by
        rw [← hdS]
        exact Set.smul_mem_smul_set hs
      have hoverlap :
          (S ∩ (fun a ↦ ((d : Γ)⁻¹)⁻¹ * a * (d : Γ)⁻¹) '' S).Nonempty := by
        refine ⟨d • s, hds, s, hs, ?_⟩
        change ((d : Γ)⁻¹)⁻¹ * s * (d : Γ)⁻¹ =
          (d : Γ) * s * (d : Γ)⁻¹
        simp only [inv_inv]
      have hdinvN : (d : Γ)⁻¹ ∈ N :=
        hTI.2.2 (D.inv_mem d.property) hoverlap
      change (d : Γ) ∈ N
      simpa only [inv_inv] using N.inv_mem hdinvN
    · intro hdN
      change (d : Γ) ∈ N at hdN
      exact act_set_eq_of_mem_normalizer d (hTI.2.1 hdN).2

  have horbitcard : (MulAction.orbit D S).ncard = N.relIndex D := by
    rw [← MulAction.index_stabilizer D S, hstab]
    rfl

  exact ⟨⟨hunion, hpair, hnonempty⟩, horbitcard⟩

end

end Submission.OddOrder.PF
