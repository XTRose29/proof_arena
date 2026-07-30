import Submission.OddOrder.PF.Section02.DadeSupportConjugation

/-!
# Conjugacy-saturated support properties

Generic containment and normalization facts for `classSupportWithin`.  The
support uses explicit right conjugates `g⁻¹ * x * g`; the final theorem
bridges this convention to Mathlib's left-conjugation definition of a set
normalizer by replacing `g` with `g⁻¹`.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.MathlibSupport

universe u

variable {Γ : Type u} [Group Γ]

/-- Saturating a subset of `G` under `G`-conjugacy remains inside `G`. -/
theorem classSupportWithin_subset
    {G : Subgroup Γ} {S : Set Γ} (hS : S ⊆ (G : Set Γ)) :
    classSupportWithin G S ⊆ (G : Set Γ) := by
  rintro y ⟨x, hxS, g, hgG, rfl⟩
  exact G.mul_mem (G.mul_mem (G.inv_mem hgG) (hS hxS)) hgG

private theorem classSupportWithin_rightConj
    {G : Subgroup Γ} {S : Set Γ} {x g : Γ} (hg : g ∈ G)
    (hx : x ∈ classSupportWithin G S) :
    g⁻¹ * x * g ∈ classSupportWithin G S := by
  rcases hx with ⟨y, hyS, k, hkG, rfl⟩
  refine ⟨y, hyS, k * g, G.mul_mem hkG hg, ?_⟩
  group

/-- Membership in a conjugacy-saturated support is invariant under explicit
right conjugation by an element of the ambient subgroup. -/
theorem classSupportWithin_rightConj_iff
    {G : Subgroup Γ} {S : Set Γ} {x g : Γ} (hg : g ∈ G) :
    g⁻¹ * x * g ∈ classSupportWithin G S ↔
      x ∈ classSupportWithin G S := by
  constructor
  · intro hx
    have hx' := classSupportWithin_rightConj
      (G := G) (S := S) (g := g⁻¹) (G.inv_mem hg) hx
    simpa [mul_assoc] using hx'
  · exact classSupportWithin_rightConj hg

/-- The ambient subgroup normalizes every support saturated under its
conjugacy classes. -/
theorem le_normalizer_classSupportWithin
    (G : Subgroup Γ) (S : Set Γ) :
    G ≤ Subgroup.normalizer (classSupportWithin G S) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  simpa using
    (classSupportWithin_rightConj_iff
      (G := G) (S := S) (x := x) (g := g⁻¹) (G.inv_mem hg)).symm

end Submission.OddOrder.PF
