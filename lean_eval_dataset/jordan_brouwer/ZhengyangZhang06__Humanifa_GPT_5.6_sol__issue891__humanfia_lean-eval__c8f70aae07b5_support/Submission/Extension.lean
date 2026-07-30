import Submission.Helpers

namespace Submission.Helpers

open Set

/-- The inverse of a sphere embedding extends continuously to the ambient
space, taking values in the closed unit ball and taking values in the open
unit ball precisely away from the embedded sphere.  This is the extension
used to attach a cohomotopy/degree invariant to complementary components. -/
theorem exists_strict_unitBall_extension (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d)),
      (∀ z, f (r z) = z) ∧
      (∀ x, ‖f x‖ ≤ 1) ∧
      (∀ x, x ∉ Set.range r → ‖f x‖ < 1) := by
  let inclusion :
      C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        EuclideanSpace ℝ (Fin d)) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hclosedEmbedding := sphere_isClosedEmbedding d r hcont hinj
  obtain ⟨F, hFball, hF⟩ :=
    inclusion.exists_extension_forall_mem hclosedEmbedding
      (t := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
      fun z ↦ Metric.sphere_subset_closedBall z.2
  have hrange : (Set.range r).Nonempty :=
    (sphere_range_connected d hd r hcont).nonempty
  have hrangeClosed : IsClosed (Set.range r) :=
    hclosedEmbedding.isClosed_range
  let scale : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun x ↦ (1 + Metric.infDist x (Set.range r))⁻¹
  have hdenom (x : EuclideanSpace ℝ (Fin d)) :
      0 < 1 + Metric.infDist x (Set.range r) :=
    add_pos_of_pos_of_nonneg zero_lt_one Metric.infDist_nonneg
  have hscale : Continuous scale := by
    exact (continuous_const.add
      (Metric.continuous_infDist_pt (Set.range r))).inv₀ fun x ↦
        (hdenom x).ne'
  let f : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d)) :=
    ⟨fun x ↦ scale x • F x, hscale.smul F.continuous⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro z
    have hdist : Metric.infDist (r z) (Set.range r) = 0 :=
      Metric.infDist_zero_of_mem ⟨z, rfl⟩
    have hFz : F (r z) = z := DFunLike.congr_fun hF z
    simp [f, scale, hdist, hFz]
  · intro x
    have hFnorm : ‖F x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hFball x
    have hscale_nonneg : 0 ≤ scale x :=
      inv_nonneg.mpr (hdenom x).le
    have hscale_le_one : scale x ≤ 1 := by
      change (1 + Metric.infDist x (Set.range r))⁻¹ ≤ 1
      rw [inv_le_one₀ (hdenom x)]
      linarith [Metric.infDist_nonneg (x := x) (s := Set.range r)]
    calc
      ‖f x‖ = scale x * ‖F x‖ := by
        simp [f, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hscale_nonneg]
      _ ≤ scale x * 1 :=
        mul_le_mul_of_nonneg_left hFnorm hscale_nonneg
      _ ≤ 1 := by simpa using hscale_le_one
  · intro x hx
    have hFnorm : ‖F x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hFball x
    have hdist : 0 < Metric.infDist x (Set.range r) :=
      (hrangeClosed.notMem_iff_infDist_pos hrange).mp hx
    have hscale_pos : 0 < scale x := inv_pos.mpr (hdenom x)
    have hscale_lt_one : scale x < 1 := by
      change (1 + Metric.infDist x (Set.range r))⁻¹ < 1
      rw [inv_lt_one₀ (hdenom x)]
      linarith
    calc
      ‖f x‖ = scale x * ‖F x‖ := by
        simp [f, norm_smul, Real.norm_eq_abs, abs_of_pos hscale_pos]
      _ ≤ scale x * 1 :=
        mul_le_mul_of_nonneg_left hFnorm hscale_pos.le
      _ < 1 := by simpa using hscale_lt_one

end Submission.Helpers
