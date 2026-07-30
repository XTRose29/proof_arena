import Submission.OddOrder.MathlibSupport.Centralizer

/-!
# Normalized trivial-intersection sets

This is the propositional content of MathComp's `normedTI A D L`.  MathComp's
right conjugate `a ^ g` is written explicitly as `g⁻¹ * a * g` below.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- A nonempty set `A` whose conjugates by `D` have trivial intersection,
with normalizer `L` inside `D`.

The last clause is the overlap formulation of the trivial-intersection
condition. -/
def IsNormalizedTI (A : Set G) (D L : Subgroup G) : Prop :=
  A.Nonempty ∧ L ≤ D ⊓ Subgroup.normalizer A ∧
    ∀ ⦃g⦄, g ∈ D →
      (A ∩ (fun a ↦ g⁻¹ * a * g) '' A).Nonempty → g ∈ L

/-- Membership form of the normalized trivial-intersection condition.

For `a ∈ A` and `g ∈ D`, the right conjugate `g⁻¹ * a * g` lies in
`A` exactly when `g` belongs to the relative normalizer `L`. -/
theorem isNormalizedTI_iff_mem_conj {A : Set G} {D L : Subgroup G} :
    IsNormalizedTI A D L ↔
      A.Nonempty ∧ L ≤ D ∧
        ∀ ⦃a⦄, a ∈ A → ∀ ⦃g⦄, g ∈ D →
          (g⁻¹ * a * g ∈ A ↔ g ∈ L) := by
  constructor
  · rintro ⟨hA, hL, hoverlap⟩
    refine ⟨hA, fun g hg ↦ (hL hg).1, ?_⟩
    intro a ha g hg
    constructor
    · intro hag
      apply hoverlap hg
      exact ⟨g⁻¹ * a * g, hag, a, ha, rfl⟩
    · intro hgL
      exact ((Subgroup.mem_set_normalizer_iff''.mp (hL hgL).2) a).mp ha
  · rintro ⟨hA, hLD, hmem⟩
    refine ⟨hA, ?_, ?_⟩
    · intro g hgL
      refine ⟨hLD hgL, ?_⟩
      apply Subgroup.mem_set_normalizer_iff''.mpr
      intro a
      constructor
      · intro ha
        exact (hmem ha (hLD hgL)).mpr hgL
      · intro hag
        have hginvL : g⁻¹ ∈ L := L.inv_mem hgL
        have hback : g * (g⁻¹ * a * g) * g⁻¹ ∈ A := by
          simpa only [inv_inv] using (hmem hag (hLD hginvL)).mpr hginvL
        simpa [mul_assoc] using hback
    · intro g hg hoverlap
      rcases hoverlap with ⟨x, hxA, a, ha, rfl⟩
      exact (hmem ha hg).mp hxA

/-- The relative normalizer in a normalized trivial-intersection set is
exactly the specified subgroup `L`. -/
theorem IsNormalizedTI.inf_normalizer_eq
    {A : Set G} {D L : Subgroup G} (h : IsNormalizedTI A D L) :
    D ⊓ Subgroup.normalizer A = L := by
  have hmem := isNormalizedTI_iff_mem_conj.mp h
  apply le_antisymm
  · rintro g ⟨hgD, hgN⟩
    obtain ⟨a, ha⟩ := hmem.1
    have hconj : g * a * g⁻¹ ∈ A :=
      ((Subgroup.mem_set_normalizer_iff.mp hgN) a).mp ha
    have hginvL : g⁻¹ ∈ L :=
      (hmem.2.2 ha (D.inv_mem hgD)).mp (by
        simpa only [inv_inv] using hconj)
    simpa only [inv_inv] using L.inv_mem hginvL
  · exact h.2.1

/-- In a normalized trivial-intersection set, the centralizer in `D` of an
element of `A` lies in the relative normalizer `L`. -/
theorem IsNormalizedTI.centralizerWithin_zpowers_le
    {A : Set G} {D L : Subgroup G} (h : IsNormalizedTI A D L)
    {a : G} (ha : a ∈ A) :
    centralizerWithin D (Subgroup.zpowers a) ≤ L := by
  intro x hx
  apply ((isNormalizedTI_iff_mem_conj.mp h).2.2 ha hx.1).mp
  have hcomm : Commute a x := hx.2 a (Subgroup.mem_zpowers a)
  have hconj : x⁻¹ * a * x = a := by
    calc
      x⁻¹ * a * x = x⁻¹ * (a * x) := by rw [mul_assoc]
      _ = x⁻¹ * (x * a) := by rw [hcomm.eq]
      _ = a := by simp
  rw [hconj]
  exact ha

end Submission.OddOrder.MathlibSupport
