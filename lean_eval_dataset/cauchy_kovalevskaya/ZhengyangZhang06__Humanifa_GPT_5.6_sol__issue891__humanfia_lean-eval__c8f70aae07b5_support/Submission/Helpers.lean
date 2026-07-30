import Mathlib

open Set
open scoped Topology ContDiff

noncomputable section

namespace Submission.Helpers

variable {X E F : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Lift a continuous multilinear map pointwise to continuous functions on a compact space. -/
def pointwiseContinuousMultilinearMap {n : ℕ} (p : E [×n]→L[ℝ] F) :
    C(X, E) [×n]→L[ℝ] C(X, F) :=
  MultilinearMap.mkContinuous
    { toFun := fun m =>
        ⟨fun x => p (fun i => m i x), by fun_prop⟩
      map_update_add' := by
        intro _ m i x y
        ext z
        have hupdate (a : C(X, E)) :
            (fun j => (Function.update m i a j) z) =
              Function.update (fun j => m j z) i (a z) := by
          funext j
          by_cases h : j = i <;> simp [Function.update, h]
        change p (fun j => (Function.update m i (x + y) j) z) =
          p (fun j => (Function.update m i x j) z) +
            p (fun j => (Function.update m i y j) z)
        rw [hupdate, hupdate, hupdate]
        exact p.map_update_add (fun j => m j z) i (x z) (y z)
      map_update_smul' := by
        intro _ m i c x
        ext z
        have hupdate (a : C(X, E)) :
            (fun j => (Function.update m i a j) z) =
              Function.update (fun j => m j z) i (a z) := by
          funext j
          by_cases h : j = i <;> simp [Function.update, h]
        change p (fun j => (Function.update m i (c • x) j) z) =
          c • p (fun j => (Function.update m i x j) z)
        rw [hupdate, hupdate]
        exact p.map_update_smul (fun j => m j z) i c (x z) }
    ‖p‖
    (by
      intro m
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg p) (Finset.prod_nonneg fun _ _ =>
        norm_nonneg _))).2
      intro x
      calc
        ‖p (fun i => m i x)‖ ≤ ‖p‖ * ∏ i, ‖m i x‖ := p.le_opNorm _
        _ ≤ ‖p‖ * ∏ i, ‖m i‖ := by
          gcongr with i
          exact ContinuousMap.norm_coe_le_norm (m i) x)

@[simp]
theorem pointwiseContinuousMultilinearMap_apply {n : ℕ} (p : E [×n]→L[ℝ] F)
    (m : Fin n → C(X, E)) (x : X) :
    pointwiseContinuousMultilinearMap p m x = p (fun i => m i x) :=
  rfl

theorem norm_pointwiseContinuousMultilinearMap_le {n : ℕ} (p : E [×n]→L[ℝ] F) :
    ‖pointwiseContinuousMultilinearMap (X := X) p‖ ≤ ‖p‖ := by
  unfold pointwiseContinuousMultilinearMap
  apply MultilinearMap.mkContinuous_norm_le
  exact norm_nonneg p

/-- Lift a formal multilinear series pointwise to continuous functions on a compact space. -/
def pointwiseFormalMultilinearSeries (p : FormalMultilinearSeries ℝ E F) :
    FormalMultilinearSeries ℝ C(X, E) C(X, F) :=
  fun n => pointwiseContinuousMultilinearMap (p n)

@[simp]
theorem pointwiseFormalMultilinearSeries_apply (p : FormalMultilinearSeries ℝ E F)
    (n : ℕ) (m : Fin n → C(X, E)) (x : X) :
    pointwiseFormalMultilinearSeries p n m x = p n (fun i => m i x) :=
  rfl

theorem radius_le_radius_pointwiseFormalMultilinearSeries
    (p : FormalMultilinearSeries ℝ E F) :
    p.radius ≤ (pointwiseFormalMultilinearSeries (X := X) p).radius := by
  apply FormalMultilinearSeries.radius_le_of_le
  intro n
  exact norm_pointwiseContinuousMultilinearMap_le (X := X) (p n)

/-- Postcompose a continuous map by a globally continuous function. -/
def postcompContinuousMap (f : E → F) (hf : Continuous f) : C(X, E) → C(X, F) :=
  fun g => ⟨f ∘ g, hf.comp g.continuous⟩

omit [CompactSpace X] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp]
theorem postcompContinuousMap_apply (f : E → F) (hf : Continuous f) (g : C(X, E)) (x : X) :
    postcompContinuousMap f hf g x = f (g x) :=
  rfl

theorem HasFPowerSeriesOnBall.postcompContinuousMap [CompleteSpace F]
    {f : E → F} {p : FormalMultilinearSeries ℝ E F} {x : E} {r : ENNReal}
    (h : HasFPowerSeriesOnBall f p x r) (hf : Continuous f) :
    HasFPowerSeriesOnBall (Submission.Helpers.postcompContinuousMap (X := X) f hf)
      (pointwiseFormalMultilinearSeries p) (ContinuousMap.const X x) r := by
  refine
    { r_le := h.r_le.trans (radius_le_radius_pointwiseFormalMultilinearSeries (X := X) p)
      r_pos := h.r_pos
      hasSum := ?_ }
  intro y hy
  let q := pointwiseFormalMultilinearSeries (X := X) p
  have hyq : y ∈ Metric.eball (0 : C(X, E)) q.radius :=
    Metric.mem_eball.mpr <| (Metric.mem_eball.mp hy).trans_le
      (h.r_le.trans (radius_le_radius_pointwiseFormalMultilinearSeries (X := X) p))
  have hsum : Summable (fun n : ℕ => q n fun _ => y) := q.summable hyq
  have heq : (∑' n : ℕ, q n fun _ => y) =
      Submission.Helpers.postcompContinuousMap f hf (ContinuousMap.const X x + y) := by
    ext z
    have hyz : y z ∈ Metric.eball (0 : E) r := by
      rw [mem_eball_zero_iff, enorm_eq_nnnorm] at hy ⊢
      exact lt_of_le_of_lt (by exact_mod_cast ContinuousMap.norm_coe_le_norm y z) hy
    have hz := (ContinuousMap.evalCLM ℝ z).hasSum hsum.hasSum
    have hz' := h.hasSum hyz
    exact hz.unique (by simpa [q] using hz')
  rw [← heq]
  exact hsum.hasSum

theorem AnalyticAt.postcompContinuousMap [CompleteSpace F]
    {f : E → F} {x : E} (h : AnalyticAt ℝ f x) (hf : Continuous f) :
    AnalyticAt ℝ (Submission.Helpers.postcompContinuousMap (X := X) f hf)
      (ContinuousMap.const X x) := by
  rcases h with ⟨p, r, hp⟩
  exact ⟨pointwiseFormalMultilinearSeries p, r,
    Submission.Helpers.HasFPowerSeriesOnBall.postcompContinuousMap hp hf⟩

/-- Pointwise pairing is a continuous linear map on compact-domain continuous functions. -/
def prodContinuousMapCLM : C(X, E) × C(X, F) →L[ℝ] C(X, E × F) :=
  LinearMap.mkContinuous
    { toFun := fun p => p.1.prodMk p.2
      map_add' := by
        intro p q
        ext x <;> simp
      map_smul' := by
        intro c p
        ext x <;> simp }
    1
    (by
      intro p
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg p)).2
      intro x
      change max ‖p.1 x‖ ‖p.2 x‖ ≤ max ‖p.1‖ ‖p.2‖
      exact max_le_max (ContinuousMap.norm_coe_le_norm p.1 x)
        (ContinuousMap.norm_coe_le_norm p.2 x))

abbrev PathInterval := Set.Icc (0 : ℝ) 1

/-- The identity coordinate on the unit interval, as a continuous map. -/
def pathTime : C(PathInterval, ℝ) :=
  ⟨fun s => s, continuous_subtype_val⟩

/-- Scale the unit-interval coordinate by a duration. -/
def pathTimeCLM : ℝ →L[ℝ] C(PathInterval, ℝ) :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) pathTime

@[simp]
theorem pathTimeCLM_apply (t : ℝ) (s : PathInterval) : pathTimeCLM t s = t * s := rfl

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Convert parameters `(initial state, duration, path)` to the time-state path fed to a vector
field. -/
def pathInputCLM : ((Y × ℝ) × C(PathInterval, Y)) →L[ℝ] C(PathInterval, ℝ × Y) :=
  prodContinuousMapCLM.comp <| ContinuousLinearMap.prod
    (pathTimeCLM.comp <|
      (ContinuousLinearMap.snd ℝ Y ℝ).comp
        (ContinuousLinearMap.fst ℝ (Y × ℝ) C(PathInterval, Y)))
    (ContinuousLinearMap.snd ℝ (Y × ℝ) C(PathInterval, Y))

@[simp]
theorem pathInputCLM_apply (q : (Y × ℝ) × C(PathInterval, Y)) (s : PathInterval) :
    pathInputCLM q s = (q.1.2 * s, q.2 s) := rfl

/-- Extend a unit-interval path to the real line by clamping its input. -/
def extendPath (g : C(PathInterval, Y)) : ℝ → Y :=
  fun s => g (Set.projIcc 0 1 zero_le_one s)

omit [NormedSpace ℝ Y] in
theorem continuous_extendPath (g : C(PathInterval, Y)) : Continuous (extendPath g) :=
  g.continuous.comp continuous_projIcc

variable [CompleteSpace Y]

/-- The primitive `s ↦ ∫₀ˢ g`, as a bounded continuous linear operator on paths. -/
def pathIntegralCLM : C(PathInterval, Y) →L[ℝ] C(PathInterval, Y) :=
  LinearMap.mkContinuous
    { toFun := fun g =>
        ⟨fun s => ∫ r in (0 : ℝ)..(s : ℝ), extendPath g r,
          (intervalIntegral.continuous_primitive
            (fun a b => (continuous_extendPath g).intervalIntegrable a b) 0).comp
              continuous_subtype_val⟩
      map_add' := by
        intro g h
        ext s
        apply intervalIntegral.integral_add
        · exact (continuous_extendPath g).intervalIntegrable 0 s
        · exact (continuous_extendPath h).intervalIntegrable 0 s
      map_smul' := by
        intro c g
        ext s
        exact intervalIntegral.integral_smul c (extendPath g) }
    1
    (by
      intro g
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg g)).2
      intro s
      calc
        ‖∫ r in (0 : ℝ)..(s : ℝ), extendPath g r‖ ≤ ‖g‖ * |(s : ℝ) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun r _ =>
            ContinuousMap.norm_coe_le_norm g (Set.projIcc 0 1 zero_le_one r)
        _ ≤ ‖g‖ := by
          rw [sub_zero, abs_of_nonneg s.2.1]
          exact mul_le_of_le_one_right (norm_nonneg g) s.2.2)

omit [CompleteSpace Y] in
@[simp]
theorem pathIntegralCLM_apply (g : C(PathInterval, Y)) (s : PathInterval) :
    pathIntegralCLM g s = ∫ r in (0 : ℝ)..(s : ℝ), extendPath g r := rfl

/-- Apply a time-dependent vector field pointwise to the rescaled time-state path. -/
def pathVectorField (V : ℝ × Y → Y) (hV : Continuous V) :
    ((Y × ℝ) × C(PathInterval, Y)) → C(PathInterval, Y) :=
  fun q => postcompContinuousMap V hV (pathInputCLM q)

omit [CompleteSpace Y] in
@[simp]
theorem pathVectorField_apply (V : ℝ × Y → Y) (hV : Continuous V)
    (q : (Y × ℝ) × C(PathInterval, Y)) (s : PathInterval) :
    pathVectorField V hV q s = V (q.1.2 * s, q.2 s) := rfl

omit [CompleteSpace Y] in
@[simp]
theorem pathInputCLM_base (y : Y) :
    pathInputCLM (((y, (0 : ℝ)), ContinuousMap.const PathInterval y)) =
      ContinuousMap.const PathInterval ((0 : ℝ), y) := by
  apply ContinuousMap.ext
  intro s
  rw [pathInputCLM_apply]
  simp

theorem analyticAt_pathVectorField {V : ℝ × Y → Y} {y : Y}
    (hV : AnalyticAt ℝ V (0, y)) (hVc : Continuous V) :
    AnalyticAt ℝ (pathVectorField V hVc)
      ((y, (0 : ℝ)), ContinuousMap.const PathInterval y) := by
  have hp := Submission.Helpers.AnalyticAt.postcompContinuousMap
    (X := PathInterval) hV hVc
  have hL := (pathInputCLM (Y := Y)).analyticAt
    ((y, (0 : ℝ)), ContinuousMap.const PathInterval y)
  rw [← pathInputCLM_base y] at hp
  change AnalyticAt ℝ
    (fun q => postcompContinuousMap V hVc (pathInputCLM q))
      ((y, (0 : ℝ)), ContinuousMap.const PathInterval y)
  exact hp.comp hL

/-- The rescaled integral equation for an ODE path. -/
def pathEquation (V : ℝ × Y → Y) (hV : Continuous V) :
    ((Y × ℝ) × C(PathInterval, Y)) → C(PathInterval, Y) :=
  fun q => q.2 - ContinuousMap.const PathInterval q.1.1 -
    q.1.2 • pathIntegralCLM (pathVectorField V hV q)

omit [CompleteSpace Y] in
@[simp]
theorem pathEquation_zero_duration (V : ℝ × Y → Y) (hV : Continuous V)
    (y : Y) (g : C(PathInterval, Y)) :
    pathEquation V hV ((y, (0 : ℝ)), g) = g - ContinuousMap.const PathInterval y := by
  simp [pathEquation]

omit [CompleteSpace Y] in
@[simp]
theorem pathEquation_base (V : ℝ × Y → Y) (hV : Continuous V) (y : Y) :
    pathEquation V hV ((y, (0 : ℝ)), ContinuousMap.const PathInterval y) = 0 := by
  simp

theorem analyticAt_pathEquation {V : ℝ × Y → Y} {y : Y}
    (hV : AnalyticAt ℝ V (0, y)) (hVc : Continuous V) :
    AnalyticAt ℝ (pathEquation V hVc)
      ((y, (0 : ℝ)), ContinuousMap.const PathInterval y) := by
  let q₀ : (Y × ℝ) × C(PathInterval, Y) :=
    ((y, (0 : ℝ)), ContinuousMap.const PathInterval y)
  have hγ : AnalyticAt ℝ (fun q : (Y × ℝ) × C(PathInterval, Y) => q.2) q₀ := by
    simpa using
      (ContinuousLinearMap.snd ℝ (Y × ℝ) C(PathInterval, Y)).analyticAt q₀
  have hy : AnalyticAt ℝ
      (fun q : (Y × ℝ) × C(PathInterval, Y) => ContinuousMap.const PathInterval q.1.1) q₀ := by
    change AnalyticAt ℝ ⇑((ContinuousLinearMap.const ℝ PathInterval).comp
      ((ContinuousLinearMap.fst ℝ Y ℝ).comp
        (ContinuousLinearMap.fst ℝ (Y × ℝ) C(PathInterval, Y)))) q₀
    exact ((ContinuousLinearMap.const ℝ PathInterval).comp
      ((ContinuousLinearMap.fst ℝ Y ℝ).comp
        (ContinuousLinearMap.fst ℝ (Y × ℝ) C(PathInterval, Y)))).analyticAt q₀
  have ht : AnalyticAt ℝ (fun q : (Y × ℝ) × C(PathInterval, Y) => q.1.2) q₀ := by
    change AnalyticAt ℝ ⇑((ContinuousLinearMap.snd ℝ Y ℝ).comp
      (ContinuousLinearMap.fst ℝ (Y × ℝ) C(PathInterval, Y))) q₀
    exact ((ContinuousLinearMap.snd ℝ Y ℝ).comp
      (ContinuousLinearMap.fst ℝ (Y × ℝ) C(PathInterval, Y))).analyticAt q₀
  have hW : AnalyticAt ℝ (pathVectorField V hVc) q₀ :=
    analyticAt_pathVectorField hV hVc
  have hJW : AnalyticAt ℝ (fun q => pathIntegralCLM (pathVectorField V hVc q)) q₀ :=
    ((pathIntegralCLM (Y := Y)).analyticAt _).comp hW
  exact (hγ.sub hy).sub (ht.smul hJW)

theorem pathEquation_right_fderiv {V : ℝ × Y → Y} {y : Y}
    (hV : AnalyticAt ℝ V (0, y)) (hVc : Continuous V) :
    fderiv ℝ (pathEquation V hVc)
        ((y, (0 : ℝ)), ContinuousMap.const PathInterval y) ∘L
      ContinuousLinearMap.inr ℝ (Y × ℝ) C(PathInterval, Y) =
        ContinuousLinearMap.id ℝ C(PathInterval, Y) := by
  let g₀ := ContinuousMap.const PathInterval y
  let q₀ : (Y × ℝ) × C(PathInterval, Y) := ((y, (0 : ℝ)), g₀)
  have hEq : AnalyticAt ℝ (pathEquation V hVc) q₀ := analyticAt_pathEquation hV hVc
  have hInr : HasFDerivAt (fun g : C(PathInterval, Y) => ((y, (0 : ℝ)), g))
      (ContinuousLinearMap.inr ℝ (Y × ℝ) C(PathInterval, Y)) g₀ := by
    fun_prop
  have hRight : HasFDerivAt
      (fun g : C(PathInterval, Y) => pathEquation V hVc ((y, (0 : ℝ)), g))
      (fderiv ℝ (pathEquation V hVc) q₀ ∘L
        ContinuousLinearMap.inr ℝ (Y × ℝ) C(PathInterval, Y)) g₀ := by
    simpa [q₀, Function.comp_def] using hEq.hasStrictFDerivAt.hasFDerivAt.comp g₀ hInr
  have hId : HasFDerivAt
      (fun g : C(PathInterval, Y) => g - ContinuousMap.const PathInterval y)
      (ContinuousLinearMap.id ℝ C(PathInterval, Y)) g₀ := by
    fun_prop
  apply (show HasFDerivAt
      (fun g : C(PathInterval, Y) => g - ContinuousMap.const PathInterval y)
      (fderiv ℝ (pathEquation V hVc) q₀ ∘L
        ContinuousLinearMap.inr ℝ (Y × ℝ) C(PathInterval, Y)) g₀ by
    simpa using hRight).unique hId

/-- Analytic implicit-function construction of a local family of ODE paths. The final conjunct is
the local uniqueness statement supplied by the implicit-function theorem. -/
theorem exists_analytic_implicitPath (V : ℝ × Y → Y)
    (hV : AnalyticOnNhd ℝ V univ) (y : Y) :
    ∃ ψ : Y × ℝ → C(PathInterval, Y),
      AnalyticAt ℝ ψ (y, 0) ∧
      ψ (y, 0) = ContinuousMap.const PathInterval y ∧
      (∀ᶠ a in 𝓝 (y, 0), pathEquation V hV.continuous (a, ψ a) = 0) ∧
      (∀ᶠ q in 𝓝 ((y, 0), ContinuousMap.const PathInterval y),
        pathEquation V hV.continuous q = 0 ↔ ψ q.1 = q.2) := by
  let q₀ : (Y × ℝ) × C(PathInterval, Y) :=
    ((y, (0 : ℝ)), ContinuousMap.const PathInterval y)
  have hEqA : AnalyticAt ℝ (pathEquation V hV.continuous) q₀ :=
    analyticAt_pathEquation (hV (0, y) (mem_univ _)) hV.continuous
  have hEq : ContDiffAt ℝ ω (pathEquation V hV.continuous) q₀ := hEqA.contDiffAt
  have hInv :
      (fderiv ℝ (pathEquation V hV.continuous) q₀ ∘L
        ContinuousLinearMap.inr ℝ (Y × ℝ) C(PathInterval, Y)).IsInvertible := by
    rw [pathEquation_right_fderiv (hV (0, y) (mem_univ _)) hV.continuous]
    exact ⟨ContinuousLinearEquiv.refl ℝ C(PathInterval, Y), rfl⟩
  have hω : (ω : ℕ∞ω) ≠ 0 := by simp
  let ψ : Y × ℝ → C(PathInterval, Y) := hEq.implicitFunction hω hInv
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · exact (hEq.contDiffAt_implicitFunction hω hInv).analyticAt
  · exact hEq.implicitFunction_apply_self hω hInv
  · filter_upwards [hEq.eventually_apply_implicitFunction hω hInv] with a ha
    simpa [q₀, pathEquation_base] using ha
  · filter_upwards [hEq.eventually_apply_eq_iff_implicitFunction hω hInv] with q hq
    simpa [q₀, pathEquation_base] using hq

/-- Picard-Lindelöf flow with the trajectory-ball membership retained from the fixed-point
construction. -/
theorem IsPicardLindelof.exists_flow_with_mem
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {v : ℝ → Z → Z} {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    {z₀ : Z} {a r L K : NNReal}
    (hv : IsPicardLindelof v t₀ z₀ a r L K) :
    ∃ α : Z → ℝ → Z, ∀ z ∈ Metric.closedBall z₀ r,
      α z t₀ = z ∧
      (∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt (α z) (v t (α z t)) (Set.Icc tmin tmax) t) ∧
      ∀ t, α z t ∈ Metric.closedBall z₀ a := by
  classical
  have hfixed (z : Z) (hz : z ∈ Metric.closedBall z₀ r) :=
    ODE.FunSpace.exists_isFixedPt_next hv hz
  choose γ hγ using hfixed
  let α : Z → ℝ → Z := fun z =>
    if hz : z ∈ Metric.closedBall z₀ r then (γ z hz).compProj else 0
  refine ⟨α, fun z hz => ⟨?_, ?_, ?_⟩⟩
  · simp only [α, dif_pos hz, ODE.FunSpace.compProj_val]
    rw [← hγ z hz, ODE.FunSpace.next_apply₀]
  · intro t ht
    simp only [α, dif_pos hz]
    rw [ODE.FunSpace.compProj_apply]
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hv.continuousOn_uncurry
      (γ z hz).continuous_compProj.continuousOn
      (fun _ _ => (γ z hz).compProj_mem_closedBall hv.mul_max_le) z ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hγ z hz]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro t
    simp only [α, dif_pos hz]
    exact (γ z hz).compProj_mem_closedBall hv.mul_max_le

omit [NormedSpace ℝ Y] [CompleteSpace Y] in
theorem extendPath_of_mem (g : C(PathInterval, Y)) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    extendPath g s = g ⟨s, hs⟩ := by
  simp [extendPath, Set.projIcc_of_mem zero_le_one hs]

omit [CompleteSpace Y] in
theorem pathEquation_value {V : ℝ × Y → Y} (hVc : Continuous V)
    {y : Y} {t : ℝ} {g : C(PathInterval, Y)}
    (hEq : pathEquation V hVc ((y, t), g) = 0) (s : PathInterval) :
    g s = y + t • ∫ r in (0 : ℝ)..(s : ℝ), extendPath (pathVectorField V hVc ((y, t), g)) r := by
  have hs := congrArg (fun k : C(PathInterval, Y) => k s) hEq
  simp only [pathEquation, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    ContinuousMap.smul_apply, pathIntegralCLM_apply, ContinuousMap.zero_apply] at hs
  have hsub : g s - y =
      t • ∫ r in (0 : ℝ)..(s : ℝ), extendPath (pathVectorField V hVc ((y, t), g)) r :=
    sub_eq_zero.mp hs
  calc
    g s = (g s - y) + y := (sub_add_cancel _ _).symm
    _ = (t • ∫ r in (0 : ℝ)..(s : ℝ),
        extendPath (pathVectorField V hVc ((y, t), g)) r) + y := by rw [hsub]
    _ = y + t • ∫ r in (0 : ℝ)..(s : ℝ),
        extendPath (pathVectorField V hVc ((y, t), g)) r := add_comm _ _

theorem hasDerivWithinAt_extendPath_of_pathEquation {V : ℝ × Y → Y}
    (hVc : Continuous V) {y : Y} {t : ℝ} {g : C(PathInterval, Y)}
    (hEq : pathEquation V hVc ((y, t), g) = 0) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (extendPath g) (t • V (t * s, extendPath g s))
      (Set.Icc (0 : ℝ) 1) s := by
  let w := pathVectorField V hVc ((y, t), g)
  have hw : Continuous (extendPath w) := continuous_extendPath w
  have hI : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, extendPath w r) (extendPath w s) s :=
    intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 s)
      hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt
  have hR : HasDerivWithinAt
      (fun u => y + t • ∫ r in (0 : ℝ)..u, extendPath w r)
      (t • extendPath w s) (Set.Icc (0 : ℝ) 1) s :=
    ((hI.const_smul t).const_add y).hasDerivWithinAt
  have hR' : HasDerivWithinAt (extendPath g) (t • extendPath w s)
      (Set.Icc (0 : ℝ) 1) s := hR.congr
    (fun u hu => by
      rw [extendPath_of_mem g hu]
      exact pathEquation_value hVc hEq ⟨u, hu⟩)
    (by
      rw [extendPath_of_mem g hs]
      exact pathEquation_value hVc hEq ⟨s, hs⟩)
  convert hR' using 1
  rw [extendPath_of_mem w hs, extendPath_of_mem g hs]
  rfl

/-- Adjoin the time coordinate to make a time-dependent vector field autonomous. -/
def augmentedField (V : ℝ × Y → Y) : ℝ × Y → ℝ × Y :=
  fun z => (1, V z)

omit [CompleteSpace Y] in
theorem analyticOnNhd_augmentedField {V : ℝ × Y → Y}
    (hV : AnalyticOnNhd ℝ V univ) :
    AnalyticOnNhd ℝ (augmentedField V) univ := by
  intro z _
  exact analyticAt_const.prod (hV z (mem_univ z))

/-- The time-state curve represented by a rescaled implicit path. -/
def normalizedPath (t : ℝ) (g : C(PathInterval, Y)) : ℝ → ℝ × Y :=
  fun s => (t * s, extendPath g s)

theorem hasDerivWithinAt_normalizedPath_of_pathEquation {V : ℝ × Y → Y}
    (hVc : Continuous V) {y : Y} {t : ℝ} {g : C(PathInterval, Y)}
    (hEq : pathEquation V hVc ((y, t), g) = 0) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (normalizedPath t g)
      (t • augmentedField V (normalizedPath t g s)) (Set.Icc (0 : ℝ) 1) s := by
  have ht : HasDerivWithinAt (fun u : ℝ => t * u) t (Set.Icc (0 : ℝ) 1) s := by
    exact (hasDerivAt_const_mul t).hasDerivWithinAt
  have hg := hasDerivWithinAt_extendPath_of_pathEquation hVc hEq hs
  have hfun : normalizedPath t g = fun u => (t * u, extendPath g u) := rfl
  have hder : t • augmentedField V (normalizedPath t g s) =
      (t, t • V (t * s, extendPath g s)) := by
    simp [normalizedPath, augmentedField]
  rw [hder, hfun]
  exact ht.prodMk hg

omit [CompleteSpace Y] in
theorem hasDerivWithinAt_rescaled_picard {V : ℝ × Y → Y}
    {α : ℝ → ℝ × Y} {tmin tmax t s : ℝ}
    (hzero : (0 : ℝ) ∈ Set.Icc tmin tmax)
    (hα : ∀ τ ∈ Set.Icc tmin tmax,
      HasDerivWithinAt α (augmentedField V (α τ)) (Set.Icc tmin tmax) τ)
    (ht : t ∈ Set.Icc tmin tmax) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun u => α (t * u))
      (t • augmentedField V (α (t * s))) (Set.Icc (0 : ℝ) 1) s := by
  have hmul : HasDerivWithinAt (fun u : ℝ => t * u) t (Set.Icc (0 : ℝ) 1) s := by
    exact (hasDerivAt_const_mul t).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun u : ℝ => t * u) (Set.Icc (0 : ℝ) 1)
      (Set.Icc tmin tmax) := by
    intro u hu
    constructor <;> nlinarith [hzero.1, hzero.2, ht.1, ht.2, hu.1, hu.2]
  have hcomp := (hα (t * s) (hmaps hs)).hasFDerivWithinAt.comp_hasDerivWithinAt s hmul hmaps
  simpa [Function.comp_def] using hcomp

theorem implicitPath_endpoint_eq_picard {V : ℝ × Y → Y} (hVc : Continuous V)
    {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    (hzero : (0 : ℝ) ∈ Set.Icc tmin tmax) (ht₀ : (t₀ : ℝ) = 0)
    {z₀ : ℝ × Y} {a r L K : NNReal}
    (hpl : IsPicardLindelof (fun _ => augmentedField V)
      (tmin := tmin) (tmax := tmax) t₀ z₀ a r L K)
    {α : (ℝ × Y) → ℝ → ℝ × Y}
    (hα : ∀ z ∈ Metric.closedBall z₀ r,
      α z t₀ = z ∧
      (∀ τ ∈ Set.Icc tmin tmax,
        HasDerivWithinAt (α z) (augmentedField V (α z τ)) (Set.Icc tmin tmax) τ) ∧
      ∀ τ, α z τ ∈ Metric.closedBall z₀ a)
    {y : Y} {t : ℝ} {g : C(PathInterval, Y)}
    (hy : ((0 : ℝ), y) ∈ Metric.closedBall z₀ r)
    (ht : t ∈ Set.Icc tmin tmax)
    (hEq : pathEquation V hVc ((y, t), g) = 0)
    (hgmem : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      normalizedPath t g s ∈ Metric.closedBall z₀ a) :
    (t, g ⟨1, by simp⟩) = α (0, y) t := by
  let γ : ℝ → ℝ × Y := normalizedPath t g
  let β : ℝ → ℝ × Y := fun s => α (0, y) (t * s)
  have hγder : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt γ (t • augmentedField V (γ s)) (Set.Icc (0 : ℝ) 1) s := by
    intro s hs
    exact hasDerivWithinAt_normalizedPath_of_pathEquation hVc hEq hs
  have hβder : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt β (t • augmentedField V (β s)) (Set.Icc (0 : ℝ) 1) s := by
    intro s hs
    exact hasDerivWithinAt_rescaled_picard hzero (hα (0, y) hy).2.1 ht hs
  have hLip : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      LipschitzOnWith (‖t‖₊ * K) (fun z => t • augmentedField V z)
        (Metric.closedBall z₀ a) := by
    intro _ _
    simpa [Function.comp_def] using
      (lipschitzWith_smul t).comp_lipschitzOnWith (hpl.lipschitzOnWith 0 hzero)
  have hright_mem (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
      Set.Icc (0 : ℝ) 1 ∈ 𝓝[Set.Ici s] s := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio 1, Iio_mem_nhds hs.2, ?_⟩
    rintro u ⟨hu1, hu2⟩
    exact ⟨hs.1.trans hu2, hu1.le⟩
  have hγ0 : γ 0 = ((0 : ℝ), y) := by
    have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hg0 : g ⟨0, hzero⟩ = y := by
      simpa using pathEquation_value hVc hEq (⟨0, hzero⟩ : PathInterval)
    rw [show γ 0 = (0, extendPath g 0) by simp [γ, normalizedPath]]
    rw [extendPath_of_mem g hzero, hg0]
  have hβ0 : β 0 = ((0 : ℝ), y) := by
    change α (0, y) (t * 0) = (0, y)
    rw [mul_zero]
    simpa [ht₀] using (hα (0, y) hy).1
  have hcurves : Set.EqOn γ β (Set.Icc (0 : ℝ) 1) :=
    ODE_solution_unique_of_mem_Icc_right
      (a := 0) (b := 1)
      (v := fun _ z => t • augmentedField V z)
      (s := fun _ => Metric.closedBall z₀ a) hLip
      (HasDerivWithinAt.continuousOn hγder)
      (fun s hs => (hγder s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (hright_mem s hs))
      (fun s hs => hgmem s (Set.Ico_subset_Icc_self hs))
      (HasDerivWithinAt.continuousOn hβder)
      (fun s hs => (hβder s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (hright_mem s hs))
      (fun s _ => (hα (0, y) hy).2.2 (t * s))
      (hγ0.trans hβ0.symm)
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  change (t, g ⟨1, hone⟩) = α (0, y) t
  have h1 := hcurves (x := 1) hone
  have hext1 : extendPath g 1 = g ⟨1, hone⟩ := extendPath_of_mem g hone
  simpa [γ, β, normalizedPath, hext1] using h1

/-- An analytic autonomous nonautonomous ODE has a local analytic flow, on a metric ball in the
initial-state/time variables. -/
theorem exists_analytic_localFlow (V : ℝ × Y → Y)
    (hV : AnalyticOnNhd ℝ V univ) (y₀ : Y) :
    ∃ δ > (0 : ℝ), ∃ φ : Y × ℝ → Y,
      AnalyticOnNhd ℝ φ (Metric.ball (y₀, (0 : ℝ)) δ) ∧
      (∀ y, (y, (0 : ℝ)) ∈ Metric.ball (y₀, (0 : ℝ)) δ → φ (y, 0) = y) ∧
      ∀ p ∈ Metric.ball (y₀, (0 : ℝ)) δ,
        HasDerivAt (fun t => φ (p.1, t)) (V (p.2, φ p)) p.2 := by
  have hAug : AnalyticOnNhd ℝ (augmentedField V) univ :=
    analyticOnNhd_augmentedField hV
  have hAugOne : ContDiffAt ℝ 1 (augmentedField V) ((0 : ℝ), y₀) :=
    (hAug (0, y₀) (mem_univ _)).contDiffAt
  obtain ⟨ε, hε, a, r, L, K, hr, hplAll⟩ :=
    IsPicardLindelof.of_contDiffAt_one hAugOne
  have hzero : (0 : ℝ) ∈ Set.Icc (0 - ε) (0 + ε) := by constructor <;> linarith
  have hpl := hplAll 0
  have hLpos : (0 : ℝ) < L := by
    have hnorm := hpl.norm_le 0 hzero ((0 : ℝ), y₀)
      (Metric.mem_closedBall_self (show (0 : ℝ) ≤ a by positivity))
    have hone : (1 : ℝ) ≤ ‖augmentedField V ((0 : ℝ), y₀)‖ := by
      simp [augmentedField, Prod.norm_def]
    linarith
  have hmaxpos : 0 < max ((0 + ε) - (0 : ℝ)) ((0 : ℝ) - (0 - ε)) := by
    simpa using hε
  have har : r < a := by
    have hbound : (L : ℝ) * max ((0 + ε) - (0 : ℝ)) ((0 : ℝ) - (0 - ε)) ≤
        (a : ℝ) - (r : ℝ) := by
      simpa using hpl.mul_max_le
    have hsub : (0 : ℝ) < (a : ℝ) - (r : ℝ) :=
      (mul_pos hLpos hmaxpos).trans_le hbound
    exact_mod_cast sub_pos.mp hsub
  have ha : (0 : ℝ) < a := by exact_mod_cast hr.trans har
  obtain ⟨α, hα⟩ :=
    Submission.Helpers.IsPicardLindelof.exists_flow_with_mem hpl
  obtain ⟨ψ, hψAnalytic, hψZero, hψEquation, _⟩ :=
    exists_analytic_implicitPath V hV y₀
  let g₀ : C(PathInterval, Y) := ContinuousMap.const PathInterval y₀
  have hψClose : ∀ᶠ p in 𝓝 (y₀, (0 : ℝ)), ψ p ∈ Metric.ball g₀ (a : ℝ) :=
    hψAnalytic.continuousAt (by simpa [g₀, hψZero] using Metric.ball_mem_nhds g₀ ha)
  have hgood : {p : Y × ℝ |
      AnalyticAt ℝ ψ p ∧ pathEquation V hV.continuous (p, ψ p) = 0 ∧
        ψ p ∈ Metric.ball g₀ (a : ℝ)} ∈ 𝓝 (y₀, (0 : ℝ)) := by
    filter_upwards [hψAnalytic.eventually_analyticAt, hψEquation, hψClose] with p hpA hpEq hpClose
    exact ⟨hpA, hpEq, hpClose⟩
  obtain ⟨δ₀, hδ₀, hδ₀good⟩ := Metric.mem_nhds_iff.mp hgood
  let m : ℝ := min δ₀ (min (r : ℝ) (min ε (a : ℝ)))
  have hm : 0 < m := by simp [m, hδ₀, hr, hε, ha]
  let δ := m / 2
  have hδ : 0 < δ := by simp [δ, hm]
  have hδδ₀ : δ < δ₀ := by
    calc
      δ < m := by simp [δ, hm]
      _ ≤ δ₀ := min_le_left _ _
  have hδr : δ < (r : ℝ) := by
    calc
      δ < m := by simp [δ, hm]
      _ ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ < ε := by
    calc
      δ < m := by simp [δ, hm]
      _ ≤ ε := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδa : δ < (a : ℝ) := by
    calc
      δ < m := by simp [δ, hm]
      _ ≤ a := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let one : PathInterval := ⟨1, by norm_num⟩
  let φ : Y × ℝ → Y := fun p => ψ p one
  have hdata (p : Y × ℝ) (hp : p ∈ Metric.ball (y₀, (0 : ℝ)) δ) :
      AnalyticAt ℝ ψ p ∧ pathEquation V hV.continuous (p, ψ p) = 0 ∧
        ψ p ∈ Metric.ball g₀ (a : ℝ) := by
    apply hδ₀good
    exact Metric.mem_ball.mpr ((Metric.mem_ball.mp hp).trans hδδ₀)
  have hyMem (p : Y × ℝ) (hp : p ∈ Metric.ball (y₀, (0 : ℝ)) δ) :
      ((0 : ℝ), p.1) ∈ Metric.closedBall ((0 : ℝ), y₀) (r : ℝ) := by
    rw [Metric.mem_closedBall, Prod.dist_eq]
    have hp' := Metric.mem_ball.mp hp
    have hy : dist p.1 y₀ ≤ dist p (y₀, (0 : ℝ)) := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    exact max_le (by simp) ((hy.trans_lt hp').trans hδr |>.le)
  have htMem (p : Y × ℝ) (hp : p ∈ Metric.ball (y₀, (0 : ℝ)) δ) :
      p.2 ∈ Set.Icc (0 - ε) (0 + ε) := by
    have hp' := Metric.mem_ball.mp hp
    have ht : dist p.2 (0 : ℝ) ≤ dist p (y₀, (0 : ℝ)) := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    have habs : |p.2| < ε := by
      have habsLe : |p.2| ≤ dist p (y₀, (0 : ℝ)) := by
        simpa [Real.dist_eq] using ht
      exact (habsLe.trans_lt hp').trans hδε
    exact ⟨by linarith [abs_lt.mp habs |>.1], by linarith [abs_lt.mp habs |>.2]⟩
  have hpathMem (p : Y × ℝ) (hp : p ∈ Metric.ball (y₀, (0 : ℝ)) δ)
      (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      normalizedPath p.2 (ψ p) s ∈ Metric.closedBall ((0 : ℝ), y₀) (a : ℝ) := by
    rw [Metric.mem_closedBall, Prod.dist_eq]
    have hp' := Metric.mem_ball.mp hp
    have ht : dist p.2 (0 : ℝ) ≤ dist p (y₀, (0 : ℝ)) := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    have htime : dist (p.2 * s) (0 : ℝ) ≤ (a : ℝ) := by
      rw [Real.dist_eq, sub_zero, abs_mul]
      have hsAbs : |s| ≤ (1 : ℝ) := by
        rw [abs_of_nonneg hs.1]
        exact hs.2
      have htimeLt : |p.2| * |s| < (a : ℝ) := by
        calc
        |p.2| * |s| ≤ |p.2| * 1 :=
          mul_le_mul_of_nonneg_left hsAbs (abs_nonneg p.2)
        _ = |p.2| := mul_one _
        _ = dist p.2 0 := by rw [Real.dist_eq, sub_zero]
        _ ≤ dist p (y₀, (0 : ℝ)) := ht
        _ < δ := hp'
        _ < a := hδa
      exact htimeLt.le
    have hstate : dist (extendPath (ψ p) s) y₀ ≤ (a : ℝ) := by
      rw [extendPath_of_mem (ψ p) hs]
      let s' : PathInterval := ⟨s, hs⟩
      change dist (ψ p s') y₀ ≤ (a : ℝ)
      have hstateLt : dist (ψ p s') y₀ < (a : ℝ) := by
        calc
        dist (ψ p s') y₀ = dist (ψ p s') (g₀ s') := rfl
        _ ≤ dist (ψ p) g₀ := ContinuousMap.dist_apply_le_dist s'
        _ < a := Metric.mem_ball.mp (hdata p hp).2.2
      exact hstateLt.le
    simpa [normalizedPath] using max_le htime hstate
  have hstateEndpoint (p : Y × ℝ) (hp : p ∈ Metric.ball (y₀, (0 : ℝ)) δ) :
      (p.2, φ p) = α (0, p.1) p.2 := by
    exact implicitPath_endpoint_eq_picard hV.continuous hzero (by rfl) hpl hα
      (hyMem p hp) (htMem p hp) (hdata p hp).2.1 (hpathMem p hp)
  have hendpoint (p : Y × ℝ) (hp : p ∈ Metric.ball (y₀, (0 : ℝ)) δ) :
      φ p = (α (0, p.1) p.2).2 := congrArg Prod.snd (hstateEndpoint p hp)
  refine ⟨δ, hδ, φ, ?_, ?_, ?_⟩
  · intro p hp
    exact ((ContinuousMap.evalCLM ℝ one).analyticAt _).comp (hdata p hp).1
  · intro y hy
    rw [hendpoint (y, 0) hy, (hα (0, y) (hyMem (y, 0) hy)).1]
  · intro p hp
    have hαDerivWithin := (hα (0, p.1) (hyMem p hp)).2.1 p.2 (htMem p hp)
    have htInterior : p.2 ∈ Set.Ioo (0 - ε) (0 + ε) := by
      have hp' := Metric.mem_ball.mp hp
      have ht : dist p.2 (0 : ℝ) ≤ dist p (y₀, (0 : ℝ)) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      have habs : |p.2| < ε := by
        have habsLe : |p.2| ≤ dist p (y₀, (0 : ℝ)) := by
          simpa [Real.dist_eq] using ht
        exact (habsLe.trans_lt hp').trans hδε
      exact ⟨by linarith [abs_lt.mp habs |>.1], by linarith [abs_lt.mp habs |>.2]⟩
    have hαDeriv : HasDerivAt (α (0, p.1))
        (augmentedField V (α (0, p.1) p.2)) p.2 :=
      hαDerivWithin.hasDerivAt (Icc_mem_nhds htInterior.1 htInterior.2)
    have hsecond : HasDerivAt (fun t => (α (0, p.1) t).2)
        (V (p.2, φ p)) p.2 := by
      have h := (ContinuousLinearMap.snd ℝ ℝ Y).hasFDerivAt.comp_hasDerivAt p.2 hαDeriv
      rw [← hstateEndpoint p hp] at h
      simpa [augmentedField, Function.comp_def] using h
    have hnear : ∀ᶠ t in 𝓝 p.2, (p.1, t) ∈ Metric.ball (y₀, (0 : ℝ)) δ := by
      exact (continuousAt_const.prodMk continuousAt_id) ((Metric.isOpen_ball.mem_nhds hp))
    have heq : (fun t => φ (p.1, t)) =ᶠ[𝓝 p.2] fun t => (α (0, p.1) t).2 := by
      filter_upwards [hnear] with t ht
      exact hendpoint (p.1, t) ht
    exact hsecond.congr_of_eventuallyEq heq

omit [CompleteSpace Y] in
/-- The differential of a local flow at time zero is the identity in the initial-state direction
and the vector field in the time direction. -/
theorem localFlow_fderiv_zero_apply {V : ℝ × Y → Y} {δ : ℝ} {φ : Y × ℝ → Y}
    {y₀ : Y}
    (hφ : AnalyticOnNhd ℝ φ (Metric.ball (y₀, (0 : ℝ)) δ))
    (hinit : ∀ y, (y, (0 : ℝ)) ∈ Metric.ball (y₀, (0 : ℝ)) δ → φ (y, 0) = y)
    (hderiv : ∀ p ∈ Metric.ball (y₀, (0 : ℝ)) δ,
      HasDerivAt (fun t => φ (p.1, t)) (V (p.2, φ p)) p.2)
    {y : Y} (hy : (y, (0 : ℝ)) ∈ Metric.ball (y₀, (0 : ℝ)) δ)
    (v : Y) (s : ℝ) :
    fderiv ℝ φ (y, 0) (v, s) = v + s • V (0, y) := by
  have hφAt := (hφ (y, 0) hy).hasStrictFDerivAt.hasFDerivAt
  have hinl : HasFDerivAt (fun x : Y => (x, (0 : ℝ)))
      (ContinuousLinearMap.inl ℝ Y ℝ) y := by fun_prop
  have hhorizontal := hφAt.comp y hinl
  have hnear : ∀ᶠ x in 𝓝 y, (x, (0 : ℝ)) ∈ Metric.ball (y₀, (0 : ℝ)) δ := by
    exact (continuousAt_id.prodMk continuousAt_const) (Metric.isOpen_ball.mem_nhds hy)
  have heq : (fun x => φ (x, (0 : ℝ))) =ᶠ[𝓝 y] id := by
    filter_upwards [hnear] with x hx
    exact hinit x hx
  have hid : HasFDerivAt (fun x : Y => x) (ContinuousLinearMap.id ℝ Y) y :=
    hasFDerivAt_id y
  have hhorizontal' : HasFDerivAt (fun x => φ (x, (0 : ℝ)))
      (ContinuousLinearMap.id ℝ Y) y := hid.congr_of_eventuallyEq heq
  have hhorEq := hhorizontal.unique hhorizontal'
  have hhor : fderiv ℝ φ (y, 0) (v, 0) = v := by
    have := congrArg (fun A : Y →L[ℝ] Y => A v) hhorEq
    simpa using this
  have hinr : HasDerivAt (fun t : ℝ => (y, t)) ((0 : Y), (1 : ℝ)) 0 := by
    exact (hasDerivAt_const (x := (0 : ℝ)) (c := y)).prodMk (hasDerivAt_id (𝕜 := ℝ) 0)
  have hvertical := hφAt.comp_hasDerivAt 0 hinr
  have hflow := hderiv (y, 0) hy
  rw [hinit y hy] at hflow
  have hvert : fderiv ℝ φ (y, 0) ((0 : Y), (1 : ℝ)) = V (0, y) :=
    hvertical.unique hflow
  have hdecomp : (v, s) = (v, (0 : ℝ)) + s • ((0 : Y), (1 : ℝ)) := by
    ext <;> simp
  rw [hdecomp, map_add, map_smul, hhor, hvert]

/-- The elementary time shear used to make the characteristic-coordinate differential equal to
the identity. -/
def timeShearHomeomorph (c : Y) : Y × ℝ ≃ₜ Y × ℝ where
  toFun p := (p.1 + p.2 • c, p.2)
  invFun p := (p.1 - p.2 • c, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [CompleteSpace Y] in
@[simp]
theorem timeShearHomeomorph_apply (c : Y) (p : Y × ℝ) :
    timeShearHomeomorph c p = (p.1 + p.2 • c, p.2) := rfl

omit [CompleteSpace Y] in
@[simp]
theorem timeShearHomeomorph_symm_apply (c : Y) (p : Y × ℝ) :
    (timeShearHomeomorph c).symm p = (p.1 - p.2 • c, p.2) := rfl

end Submission.Helpers
