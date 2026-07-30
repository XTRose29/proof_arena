import Submission.Inside

open LeanEval.Geometry.PicksTheorem

namespace Submission.HalfspaceEscape

/-- The forward affine ray from `x` in direction `d`. -/
def forwardRay (x d : ℝ × ℝ) : Set (ℝ × ℝ) :=
  (fun t : ℝ => x + t • d) '' Set.Ici 0

/-- The initial point belongs to its forward ray. -/
theorem self_mem_forwardRay (x d : ℝ × ℝ) :
    x ∈ forwardRay x d := by
  refine ⟨0, Set.mem_Ici.mpr le_rfl, ?_⟩
  simp

/-- A forward affine ray is preconnected. -/
theorem isPreconnected_forwardRay (x d : ℝ × ℝ) :
    IsPreconnected (forwardRay x d) := by
  exact
    isPreconnected_Ici.image
      (fun t : ℝ => x + t • d)
      ((continuous_const.add
        (continuous_id.smul continuous_const)).continuousOn)

/-- A forward ray in a nonzero direction is unbounded. -/
theorem not_isBounded_forwardRay
    (x : ℝ × ℝ) {d : ℝ × ℝ} (hd : d ≠ 0) :
    ¬ Bornology.IsBounded (forwardRay x d) := by
  intro hbounded
  rw [forwardRay] at hbounded
  obtain ⟨C, hC⟩ :=
    Metric.isBounded_image_iff.mp hbounded
  have hnorm : 0 < ‖d‖ :=
    norm_pos_iff.mpr hd
  let t : ℝ := (|C| + 1) / ‖d‖
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hbound :=
    hC 0 (Set.mem_Ici.mpr le_rfl)
      t (Set.mem_Ici.mpr ht)
  have hdist :
      dist (x + (0 : ℝ) • d) (x + t • d) =
        t * ‖d‖ := by
    calc
      _ = ‖(-t) • d‖ := by
        rw [dist_eq_norm]
        congr 1
        module
      _ = t * ‖d‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg,
          abs_of_nonneg ht]
  rw [hdist] at hbound
  have ht_eval : t * ‖d‖ = |C| + 1 := by
    dsimp [t]
    exact div_mul_cancel₀ _ hnorm.ne'
  rw [ht_eval] at hbound
  linarith [le_abs_self C]

/-- A linear functional that is strictly positive along the ray direction
keeps the whole ray beyond the corresponding supporting level. -/
theorem forwardRay_subset_compl_of_strictHalfspace
    (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ)
    {x d : ℝ × ℝ}
    (hx : c < f x)
    (hd : 0 < f d)
    {B : Set (ℝ × ℝ)}
    (hB : ∀ y ∈ B, f y ≤ c) :
    forwardRay x d ⊆ Bᶜ := by
  rintro y ⟨t, ht, rfl⟩ hyB
  have hle := hB _ hyB
  simp only [map_add, map_smul, smul_eq_mul] at hle
  have htd : 0 ≤ t * f d :=
    mul_nonneg ht hd.le
  linarith

/-- A strict supporting half-space supplies the complete escape witness used
by the bounded-component definition of `inside`. -/
theorem exists_unbounded_escape_of_strictHalfspace
    (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ)
    {x d : ℝ × ℝ}
    (hx : c < f x)
    (hd : 0 < f d)
    {B : Set (ℝ × ℝ)}
    (hB : ∀ y ∈ B, f y ≤ c) :
    ∃ W : Set (ℝ × ℝ),
      x ∈ W ∧
        IsPreconnected W ∧
        W ⊆ Bᶜ ∧
        ¬ Bornology.IsBounded W := by
  refine
    ⟨forwardRay x d, self_mem_forwardRay x d,
      isPreconnected_forwardRay x d,
      forwardRay_subset_compl_of_strictHalfspace
        f c hx hd hB, ?_⟩
  apply not_isBounded_forwardRay x
  intro hdZero
  rw [hdZero, map_zero] at hd
  exact lt_irrefl 0 hd

/-- If one candidate interior lies strictly beyond a supporting line and the
other boundary lies weakly on the opposite side, the two bounded-component
interiors are disjoint. -/
theorem disjoint_inside_of_strictHalfspace
    {A B : Set (ℝ × ℝ)}
    (f : (ℝ × ℝ) →L[ℝ] ℝ) (c : ℝ)
    (d : ℝ × ℝ)
    (hd : 0 < f d)
    (hA : ∀ x ∈ inside A, c < f x)
    (hB : ∀ y ∈ B, f y ≤ c) :
    Disjoint (inside A) (inside B) := by
  apply Inside.disjoint_inside_of_unbounded_witness
  intro x hxA
  exact
    exists_unbounded_escape_of_strictHalfspace
      f c (hA x hxA) hd hB

end Submission.HalfspaceEscape
