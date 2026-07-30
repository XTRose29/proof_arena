import Submission.Helpers

namespace Submission.Helpers

open Function Metric ODE Set Topology
open scoped NNReal Topology

section LipschitzFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : E → E} {K L : ℝ≥0}

/-- The chosen global integral curve of a bounded globally Lipschitz vector field. -/
noncomputable def globalIntegralCurve
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (x : E) : ℝ → E :=
  Classical.choose (exists_global_integralCurve_of_lipschitz_bounded hv hbound x)

@[simp]
theorem globalIntegralCurve_zero
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (x : E) :
    globalIntegralCurve hv hbound x 0 = x :=
  (Classical.choose_spec
    (exists_global_integralCurve_of_lipschitz_bounded hv hbound x)).1

theorem globalIntegralCurve_hasDerivAt
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (x : E) (t : ℝ) :
    HasDerivAt (globalIntegralCurve hv hbound x)
      (v (globalIntegralCurve hv hbound x t)) t :=
  (Classical.choose_spec
    (exists_global_integralCurve_of_lipschitz_bounded hv hbound x)).2 t

theorem globalIntegralCurve_unique
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L)
    {x : E} {f : ℝ → E} (hf0 : f 0 = x)
    (hf : ∀ t, HasDerivAt f (v (f t)) t) :
    f = globalIntegralCurve hv hbound x := by
  funext t
  let a : ℝ := |t| + 1
  have ha : 0 < a := by positivity
  have h0 : (0 : ℝ) ∈ Ioo (-a) a := ⟨neg_lt_zero.mpr ha, ha⟩
  have ht : t ∈ Ioo (-a) a := by
    rw [mem_Ioo]
    exact ⟨lt_of_lt_of_le (by linarith) (neg_abs_le t),
      lt_of_le_of_lt (le_abs_self t) (lt_add_one _)⟩
  exact integralCurveOn_Ioo_eqOn_of_lipschitz hv h0
    (fun s _ ↦ hf s)
    (fun s _ ↦ globalIntegralCurve_hasDerivAt hv hbound x s)
    (by simpa using hf0) ht

theorem globalIntegralCurve_add
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L)
    (x : E) (t s : ℝ) :
    globalIntegralCurve hv hbound x (t + s) =
      globalIntegralCurve hv hbound (globalIntegralCurve hv hbound x s) t := by
  let f : ℝ → E := fun u ↦ globalIntegralCurve hv hbound x (u + s)
  have hf0 : f 0 = globalIntegralCurve hv hbound x s := by simp [f]
  have hf (u : ℝ) : HasDerivAt f (v (f u)) u := by
    simpa [f] using
      (globalIntegralCurve_hasDerivAt hv hbound x (u + s)).comp_add_const u s
  exact congrFun (globalIntegralCurve_unique hv hbound hf0 hf) t

/-- The integral curve through an equilibrium is constant. -/
theorem globalIntegralCurve_eq_of_eq_zero
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L)
    {x : E} (hx : v x = 0) (t : ℝ) :
    globalIntegralCurve hv hbound x t = x := by
  let f : ℝ → E := fun _ ↦ x
  have hf0 : f 0 = x := rfl
  have hf (s : ℝ) : HasDerivAt f (v (f s)) s := by
    simpa [f, hx] using (hasDerivAt_const (x := s) (c := x))
  exact congrFun (globalIntegralCurve_unique hv hbound hf0 hf).symm t

/-- If an integral curve reaches an equilibrium, it is constant. -/
theorem globalIntegralCurve_eq_of_apply_eq_zero
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L)
    (x : E) {t : ℝ} (ht : v (globalIntegralCurve hv hbound x t) = 0)
    (s : ℝ) :
    globalIntegralCurve hv hbound x s = globalIntegralCurve hv hbound x t := by
  rw [show s = (s - t) + t by ring, globalIntegralCurve_add]
  exact globalIntegralCurve_eq_of_eq_zero hv hbound ht (s - t)

theorem globalIntegralCurve_lipschitzWith_time
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (x : E) :
    LipschitzWith L (globalIntegralCurve hv hbound x) := by
  apply lipschitzWith_of_nnnorm_deriv_le (𝕜 := ℝ)
  · intro t
    exact (globalIntegralCurve_hasDerivAt hv hbound x t).differentiableAt
  · intro t
    rw [(globalIntegralCurve_hasDerivAt hv hbound x t).deriv]
    exact_mod_cast hbound (globalIntegralCurve hv hbound x t)

theorem dist_globalIntegralCurve_le_of_nonneg
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L)
    (x y : E) {t : ℝ} (ht : 0 ≤ t) :
    dist (globalIntegralCurve hv hbound x t)
        (globalIntegralCurve hv hbound y t) ≤
      dist x y * Real.exp ((K : ℝ) * t) := by
  have h := dist_le_of_trajectories_ODE
    (v := fun _ : ℝ ↦ v) (K := K) (a := 0) (b := t)
      (δ := dist x y)
      (f := globalIntegralCurve hv hbound x)
      (g := globalIntegralCurve hv hbound y)
      (fun _ ↦ hv)
      (globalIntegralCurve_lipschitzWith_time hv hbound x).continuous.continuousOn
      (fun s _ ↦ (globalIntegralCurve_hasDerivAt hv hbound x s).hasDerivWithinAt)
      (globalIntegralCurve_lipschitzWith_time hv hbound y).continuous.continuousOn
      (fun s _ ↦ (globalIntegralCurve_hasDerivAt hv hbound y s).hasDerivWithinAt)
      (by simp) t ⟨ht, le_rfl⟩
  simpa using h

theorem dist_globalIntegralCurve_le
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L)
    (x y : E) (t : ℝ) :
    dist (globalIntegralCurve hv hbound x t)
        (globalIntegralCurve hv hbound y t) ≤
      dist x y * Real.exp ((K : ℝ) * |t|) := by
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht] using
      dist_globalIntegralCurve_le_of_nonneg hv hbound x y ht
  · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    let w : E → E := fun z ↦ -v z
    have hw : LipschitzWith K w := hv.neg
    have hwbound : ∀ z, ‖w z‖ ≤ L := fun z ↦ by simpa [w] using hbound z
    have hrev (z : E) :
        globalIntegralCurve hw hwbound z (-t) = globalIntegralCurve hv hbound z t := by
      let f : ℝ → E := fun u ↦ globalIntegralCurve hv hbound z (-u)
      have hf0 : f 0 = z := by simp [f]
      have hf (u : ℝ) : HasDerivAt f (w (f u)) u := by
        simpa [f, w] using
          (globalIntegralCurve_hasDerivAt hv hbound z (0 - u)).comp_const_sub 0 u
      have hfun := globalIntegralCurve_unique hw hwbound hf0 hf
      simpa [f] using (congrFun hfun (-t)).symm
    rw [← hrev x, ← hrev y]
    simpa [abs_of_neg (lt_of_not_ge ht)] using
      dist_globalIntegralCurve_le_of_nonneg hw hwbound x y ht'

theorem globalIntegralCurve_lipschitzWith_initial
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (t : ℝ) :
    LipschitzWith
      ⟨Real.exp ((K : ℝ) * |t|), Real.exp_pos _ |>.le⟩
      (fun x ↦ globalIntegralCurve hv hbound x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (globalIntegralCurve hv hbound x t)
      (globalIntegralCurve hv hbound y t) ≤
    Real.exp ((K : ℝ) * |t|) * dist x y
  rw [mul_comm]
  exact dist_globalIntegralCurve_le hv hbound x y t

theorem continuous_uncurry_globalIntegralCurve
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) :
    Continuous (Function.uncurry fun t x ↦ globalIntegralCurve hv hbound x t) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, x⟩
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  let g : ℝ × E → ℝ := fun p ↦
    (L : ℝ) * dist p.1 t + Real.exp ((K : ℝ) * |t|) * dist p.2 x
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ dist_nonneg)
  · filter_upwards [] with p
    calc
      dist (globalIntegralCurve hv hbound p.2 p.1)
          (globalIntegralCurve hv hbound x t) ≤
        dist (globalIntegralCurve hv hbound p.2 p.1)
            (globalIntegralCurve hv hbound p.2 t) +
          dist (globalIntegralCurve hv hbound p.2 t)
            (globalIntegralCurve hv hbound x t) := dist_triangle _ _ _
      _ ≤ (L : ℝ) * dist p.1 t +
          Real.exp ((K : ℝ) * |t|) * dist p.2 x := by
        gcongr
        · exact (globalIntegralCurve_lipschitzWith_time hv hbound p.2).dist_le_mul _ _
        · exact (globalIntegralCurve_lipschitzWith_initial hv hbound t).dist_le_mul _ _
      _ = g p := rfl
  · have hg : ContinuousAt g (t, x) := by fun_prop
    have hzero : g (t, x) = 0 := by simp [g]
    rw [← hzero]
    exact hg

/-- A bounded globally Lipschitz autonomous vector field integrates to a continuous real flow. -/
noncomputable def flowOfLipschitzBounded
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) : Flow ℝ E where
  toFun t x := globalIntegralCurve hv hbound x t
  cont' := continuous_uncurry_globalIntegralCurve hv hbound
  map_add' := fun t s x ↦ globalIntegralCurve_add hv hbound x t s
  map_zero' := globalIntegralCurve_zero hv hbound

@[simp]
theorem flowOfLipschitzBounded_apply
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (t : ℝ) (x : E) :
    flowOfLipschitzBounded hv hbound t x = globalIntegralCurve hv hbound x t := rfl

theorem flowOfLipschitzBounded_hasDerivAt
    (hv : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (x : E) (t : ℝ) :
    HasDerivAt (fun s ↦ flowOfLipschitzBounded hv hbound s x)
      (v (flowOfLipschitzBounded hv hbound t x)) t :=
  globalIntegralCurve_hasDerivAt hv hbound x t

end LipschitzFlow

end Submission.Helpers
