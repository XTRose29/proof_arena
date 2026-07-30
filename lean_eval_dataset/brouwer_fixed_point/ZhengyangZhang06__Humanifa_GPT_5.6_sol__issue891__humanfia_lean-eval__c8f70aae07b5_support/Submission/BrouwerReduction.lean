import Submission.CubeFixedPoint
import Submission.Projection

open Set

namespace Submission

noncomputable def constantVector {d : ℕ} (c : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun _ => c

@[simp]
theorem constantVector_apply {d : ℕ} (c : ℝ) (i : Fin d) :
    constantVector c i = c :=
  rfl

noncomputable def fromUnitCube {d : ℕ} (R : ℝ)
    (u : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (2 * R) • u - constantVector R

noncomputable def toUnitCube {d : ℕ} (R : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (2 * R)⁻¹ • (x + constantVector R)

@[simp]
theorem fromUnitCube_apply {d : ℕ} (R : ℝ) (u : EuclideanSpace ℝ (Fin d))
    (i : Fin d) :
    fromUnitCube R u i = 2 * R * u i - R := by
  simp [fromUnitCube]

@[simp]
theorem toUnitCube_apply {d : ℕ} (R : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (i : Fin d) :
    toUnitCube R x i = (2 * R)⁻¹ * (x i + R) := by
  simp [toUnitCube]
  ring

theorem continuous_fromUnitCube {d : ℕ} (R : ℝ) :
    Continuous (fromUnitCube (d := d) R) := by
  exact (continuous_const.smul continuous_id).sub continuous_const

theorem continuous_toUnitCube {d : ℕ} (R : ℝ) :
    Continuous (toUnitCube (d := d) R) := by
  exact continuous_const.smul (continuous_id.add continuous_const)

theorem toUnitCube_fromUnitCube {d : ℕ} {R : ℝ} (hR : R ≠ 0)
    (u : EuclideanSpace ℝ (Fin d)) :
    toUnitCube R (fromUnitCube R u) = u := by
  ext i
  simp [toUnitCube_apply, fromUnitCube_apply]
  field_simp

theorem fromUnitCube_toUnitCube {d : ℕ} {R : ℝ} (hR : R ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) :
    fromUnitCube R (toUnitCube R x) = x := by
  ext i
  simp [toUnitCube_apply, fromUnitCube_apply]
  field_simp
  ring

def symmetricCube (d : ℕ) (R : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ∈ Icc (-R) R}

theorem fromUnitCube_mem_symmetricCube {d : ℕ} {R : ℝ} (hR : 0 < R)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ unitCube d) :
    fromUnitCube R u ∈ symmetricCube d R := by
  intro i
  have hui := hu i
  simp only [mem_Icc] at hui ⊢
  rw [fromUnitCube_apply]
  constructor <;> nlinarith

theorem toUnitCube_mem_unitCube {d : ℕ} {R : ℝ} (hR : 0 < R)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ symmetricCube d R) :
    toUnitCube R x ∈ unitCube d := by
  intro i
  have hxi := hx i
  simp only [mem_Icc] at hxi ⊢
  rw [toUnitCube_apply, inv_mul_eq_div]
  have htwoR : 0 < 2 * R := mul_pos (by norm_num) hR
  constructor
  · exact div_nonneg (by linarith) htwoR.le
  · rw [div_le_one htwoR]
    linarith

theorem subset_symmetricCube_of_subset_closedBall {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    {R : ℝ} (hKR : K ⊆ Metric.closedBall 0 R) :
    K ⊆ symmetricCube d R := by
  intro x hx i
  have hnorm : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp (hKR hx)
  exact abs_le.mp ((abs_apply_le_norm x i).trans hnorm)

theorem brouwer_fixed_point_aux {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
    (hK_nonempty : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf_cont : ContinuousOn f K) (hf_maps : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  obtain ⟨R, hR, hKR⟩ := hK_compact.isBounded.subset_closedBall_lt 0 0
  have hKcube : K ⊆ symmetricCube d R := subset_symmetricCube_of_subset_closedBall hKR
  let P := metricProjection K hK_nonempty hK_compact.isComplete hK_convex
  have hP_cont : Continuous P :=
    metricProjection_continuous K hK_nonempty hK_compact.isComplete hK_convex
  have hP_mem (x : EuclideanSpace ℝ (Fin d)) : P x ∈ K :=
    metricProjection_mem K hK_nonempty hK_compact.isComplete hK_convex x
  let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun u => toUnitCube R (f (P (fromUnitCube R u)))
  have hPfrom_cont : Continuous (fun u => P (fromUnitCube R u)) :=
    hP_cont.comp (continuous_fromUnitCube R)
  have hfP_cont : ContinuousOn (fun u => f (P (fromUnitCube R u))) (unitCube d) := by
    simpa [Function.comp_def] using
      hf_cont.comp hPfrom_cont.continuousOn (fun u _ => hP_mem (fromUnitCube R u))
  have hg_cont : ContinuousOn g (unitCube d) := by
    simpa [g, Function.comp_def] using
      (continuous_toUnitCube R).comp_continuousOn hfP_cont
  have hg_maps : MapsTo g (unitCube d) (unitCube d) := by
    intro u hu
    apply toUnitCube_mem_unitCube hR
    apply hKcube
    exact hf_maps (hP_mem (fromUnitCube R u))
  obtain ⟨u, hu, hgu⟩ := unitCube_fixed_point g hg_cont hg_maps
  let x := fromUnitCube R u
  have hfx : f (P x) = x := by
    have h := congrArg (fromUnitCube R) hgu
    simpa [g, x, fromUnitCube_toUnitCube hR.ne'] using h
  have hx : x ∈ K := by
    rw [← hfx]
    exact hf_maps (hP_mem x)
  have hPx : P x = x :=
    metricProjection_eq_self_of_mem K hK_nonempty hK_compact.isComplete hK_convex hx
  refine ⟨x, hx, ?_⟩
  simpa [hPx] using hfx

end Submission
