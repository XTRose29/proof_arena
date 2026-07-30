import Submission.OddOrder.PF.Section02.DadeCosetPower
import Submission.OddOrder.MathlibSupport.NormalizedTI

/-!
# Peterfalvi 2.4(c): the normalized-TI Dade cover

The right coset of the canonical signalizer over `a` is normalized TI in
`G`, with relative normalizer the centralizer of `a` in `G`.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.MathlibSupport
open scoped Pointwise

universe u

/-- The strengthening of Peterfalvi 2.4(c): the Dade right coset over `a`
is normalized TI, with its relative normalizer equal to the centralizer of
`a` in `G`. -/
theorem Dade_cover_TI
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    {a : Γ} (ha : a ∈ A) :
    IsNormalizedTI
      ((DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ))
      G (centralizerWithin G (Subgroup.zpowers a)) := by
  let H : Subgroup Γ := DadeSignalizer ddA a
  let C : Subgroup Γ := centralizerWithin G (Subgroup.zpowers a)
  let S : Set Γ := (H : Set Γ) * ({a} : Set Γ)
  change IsNormalizedTI S G C

  have hsd : IsInternalSemidirectProductIn H
      (centralizerWithin L (Subgroup.zpowers a)) C := by
    simpa [H, C] using Dade_sdprod ddA ha
  have hCnormH : C ≤ Subgroup.normalizer (H : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsd.1).mp
      hsd.2.2.1

  have hrightConj_mem {c z : Γ} (hc : c ∈ C) (hz : z ∈ S) :
      c⁻¹ * z * c ∈ S := by
    rcases Set.mem_mul.mp hz with ⟨h, hh, t, ht, rfl⟩
    rw [Set.mem_singleton_iff] at ht
    subst t
    have hhc : c⁻¹ * h * c ∈ H :=
      ((Subgroup.mem_set_normalizer_iff''.mp
        (hCnormH hc)) h).mp hh
    have hcomm : Commute a c :=
      hc.2 a (Subgroup.mem_zpowers a)
    apply Set.mem_mul.mpr
    refine ⟨c⁻¹ * h * c, hhc, a, Set.mem_singleton a, ?_⟩
    calc
      (c⁻¹ * h * c) * a = c⁻¹ * h * (c * a) := by group
      _ = c⁻¹ * h * (a * c) := by rw [← hcomm.eq]
      _ = c⁻¹ * (h * a) * c := by group

  refine ⟨?_, ?_, ?_⟩
  · refine ⟨a, Set.mem_mul.mpr ?_⟩
    exact ⟨1, H.one_mem, a, Set.mem_singleton a, one_mul a⟩
  · intro c hc
    refine ⟨hc.1, ?_⟩
    apply Subgroup.mem_set_normalizer_iff''.mpr
    intro z
    constructor
    · exact hrightConj_mem hc
    · intro hz
      have hback := hrightConj_mem (C.inv_mem hc) hz
      simpa [mul_assoc] using hback
  · intro g hg hinter
    rcases hinter with ⟨v, hv, u, hu, rfl⟩
    have hga : g⁻¹ * a * g = a :=
      dade_coset_conj_right_factor ddA ha ha hu hv rfl
    refine ⟨hg, ?_⟩
    have hcomm : Commute a g := by
      rw [commute_iff_eq]
      calc
        a * g = g * (g⁻¹ * a * g) := by group
        _ = g * a := by rw [hga]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (hcomm.zpow_left k).eq

/-- Peterfalvi 2.4(c): the relative normalizer in `G` of the Dade cover
over `a` is its centralizer in `G`. -/
theorem norm_Dade_cover
    {Γ : Type u} [Group Γ] [Finite Γ]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    {a : Γ} (ha : a ∈ A) :
    G ⊓ Subgroup.normalizer
        ((DadeSignalizer ddA a : Set Γ) * ({a} : Set Γ)) =
      centralizerWithin G (Subgroup.zpowers a) :=
  (Dade_cover_TI ddA ha).inf_normalizer_eq

end Submission.OddOrder.PF
