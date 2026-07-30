import Mathlib

open Set

namespace Submission

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nearest point projection onto a nonempty complete convex set. -/
noncomputable def metricProjection (K : Set E) (hK_nonempty : K.Nonempty)
    (hK_complete : IsComplete K) (hK_convex : Convex ℝ K) (u : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hK_nonempty hK_complete hK_convex u)

theorem metricProjection_mem (K : Set E) (hK_nonempty : K.Nonempty)
    (hK_complete : IsComplete K) (hK_convex : Convex ℝ K) (u : E) :
    metricProjection K hK_nonempty hK_complete hK_convex u ∈ K :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hK_nonempty hK_complete hK_convex u)).1

theorem metricProjection_norm_eq_iInf (K : Set E) (hK_nonempty : K.Nonempty)
    (hK_complete : IsComplete K) (hK_convex : Convex ℝ K) (u : E) :
    ‖u - metricProjection K hK_nonempty hK_complete hK_convex u‖ =
      ⨅ w : K, ‖u - (w : E)‖ :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hK_nonempty hK_complete hK_convex u)).2

theorem metricProjection_inner_nonpos (K : Set E) (hK_nonempty : K.Nonempty)
    (hK_complete : IsComplete K) (hK_convex : Convex ℝ K) (u w : E) (hw : w ∈ K) :
    inner ℝ
        (u - metricProjection K hK_nonempty hK_complete hK_convex u)
        (w - metricProjection K hK_nonempty hK_complete hK_convex u) ≤ 0 := by
  exact (norm_eq_iInf_iff_real_inner_le_zero hK_convex
    (metricProjection_mem K hK_nonempty hK_complete hK_convex u)).1
    (metricProjection_norm_eq_iInf K hK_nonempty hK_complete hK_convex u) w hw

theorem metricProjection_eq_self_of_mem (K : Set E) (hK_nonempty : K.Nonempty)
    (hK_complete : IsComplete K) (hK_convex : Convex ℝ K) {u : E} (hu : u ∈ K) :
    metricProjection K hK_nonempty hK_complete hK_convex u = u := by
  let p := metricProjection K hK_nonempty hK_complete hK_convex u
  have hp_le : inner ℝ (u - p) (u - p) ≤ 0 := by
    simpa [p] using metricProjection_inner_nonpos K hK_nonempty hK_complete hK_convex u u hu
  have hp_ge : 0 ≤ inner ℝ (u - p) (u - p) := real_inner_self_nonneg
  have hp_zero : inner ℝ (u - p) (u - p) = 0 := le_antisymm hp_le hp_ge
  have h_sub : u - p = 0 := inner_self_eq_zero.mp hp_zero
  exact (sub_eq_zero.mp h_sub).symm

theorem metricProjection_nonexpansive (K : Set E) (hK_nonempty : K.Nonempty)
    (hK_complete : IsComplete K) (hK_convex : Convex ℝ K) (u v : E) :
    ‖metricProjection K hK_nonempty hK_complete hK_convex u -
        metricProjection K hK_nonempty hK_complete hK_convex v‖ ≤ ‖u - v‖ := by
  let P := metricProjection K hK_nonempty hK_complete hK_convex
  let p := P u
  let q := P v
  have hp : p ∈ K := by
    simpa [p, P] using metricProjection_mem K hK_nonempty hK_complete hK_convex u
  have hq : q ∈ K := by
    simpa [q, P] using metricProjection_mem K hK_nonempty hK_complete hK_convex v
  have hu_var : inner ℝ (u - p) (q - p) ≤ 0 := by
    simpa [p, q, P] using
      metricProjection_inner_nonpos K hK_nonempty hK_complete hK_convex u q hq
  have hv_var : inner ℝ (v - q) (p - q) ≤ 0 := by
    simpa [p, q, P] using
      metricProjection_inner_nonpos K hK_nonempty hK_complete hK_convex v p hp
  have hu_nonneg : 0 ≤ inner ℝ (u - p) (p - q) := by
    have hqp : q - p = -(p - q) := by abel
    have : -inner ℝ (u - p) (p - q) ≤ 0 := by
      simpa only [hqp, inner_neg_right] using hu_var
    linarith
  have hmain : inner ℝ (p - q) (p - q) ≤ inner ℝ (u - v) (p - q) := by
    have hvec : u - v = (u - p) + (p - q) - (v - q) := by abel
    have hdecomp : inner ℝ (u - v) (p - q) =
        inner ℝ (u - p) (p - q) + inner ℝ (p - q) (p - q) -
          inner ℝ (v - q) (p - q) := by
      rw [hvec]
      simp only [inner_sub_left, inner_add_left]
    nlinarith
  have hcs : inner ℝ (u - v) (p - q) ≤ ‖u - v‖ * ‖p - q‖ :=
    real_inner_le_norm (u - v) (p - q)
  have hsquare : ‖p - q‖ ^ 2 ≤ ‖u - v‖ * ‖p - q‖ := by
    have hself : inner ℝ (p - q) (p - q) = ‖p - q‖ ^ 2 := by
      exact inner_self_eq_norm_sq (𝕜 := ℝ) (p - q)
    nlinarith
  by_cases hzero : ‖p - q‖ = 0
  · rw [hzero]
    exact norm_nonneg _
  · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have hmul : ‖p - q‖ * ‖p - q‖ ≤ ‖u - v‖ * ‖p - q‖ := by
      simpa [pow_two] using hsquare
    exact le_of_mul_le_mul_right hmul hpos

theorem metricProjection_lipschitzWith (K : Set E) (hK_nonempty : K.Nonempty)
    (hK_complete : IsComplete K) (hK_convex : Convex ℝ K) :
    LipschitzWith 1 (fun u => metricProjection K hK_nonempty hK_complete hK_convex u) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  simpa [dist_eq_norm] using
    metricProjection_nonexpansive K hK_nonempty hK_complete hK_convex u v

theorem metricProjection_continuous (K : Set E) (hK_nonempty : K.Nonempty)
    (hK_complete : IsComplete K) (hK_convex : Convex ℝ K) :
    Continuous fun u => metricProjection K hK_nonempty hK_complete hK_convex u :=
  (metricProjection_lipschitzWith K hK_nonempty hK_complete hK_convex).continuous

end Projection

end Submission
