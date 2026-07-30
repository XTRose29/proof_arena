import Submission.Components

namespace Submission.Existence

open Function Set
open Winding
open MeasureTheory
open scoped ContDiff

noncomputable section

/-- A nonvanishing continuous function on the plane has a continuous logarithm after
restriction to any loop. -/
theorem hasLog_comp_of_global
    (F : C(ℂ, ℂ)) (hF : ∀ x, F x ≠ 0) (u : C(Circle, ℂ)) :
    HasLog (F.comp u) := by
  obtain ⟨L, hL, _hLuniq⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts F
      (a₀ := (0 : ℂ)) (e₀ := Complex.log (F 0))
      (Complex.exp_log (hF 0)) (fun x ↦ hF x)
  refine ⟨L.comp u, fun z ↦ ?_⟩
  exact congrFun hL.2 (u z)

/-- Applying an invertible real-linear map to a loop with a logarithm again gives a
loop with a logarithm. -/
theorem HasLog.comp_continuousLinearEquiv
    {u : C(Circle, ℂ)} (hu : HasLog u) (A : ℂ ≃L[ℝ] ℂ) :
    HasLog ⟨fun z ↦ A (u z), A.continuous.comp u.continuous⟩ := by
  obtain ⟨l, hl⟩ := hu
  let F : C(ℂ, ℂ) :=
    ⟨fun w ↦ A (Complex.exp w), A.continuous.comp Complex.continuous_exp⟩
  have hF (w : ℂ) : F w ≠ 0 := by
    simpa only [F, ContinuousMap.coe_mk, map_zero] using
      A.injective.ne (Complex.exp_ne_zero w)
  obtain ⟨L, hL⟩ := hasLog_comp_of_global F hF l
  refine ⟨L, fun z ↦ ?_⟩
  rw [hL]
  change A (Complex.exp (l z)) = A (u z)
  rw [hl]

/-- A loop viewed from a point whose norm is larger than every point of the loop has
winding number zero. -/
theorem windingAround_eq_zero_of_forall_norm_lt
    (r : C(Circle, ℂ)) {x : ℂ} (hx : x ∉ Set.range r)
    (hfar : ∀ z, ‖r z‖ < ‖x‖) :
    windingAround r x hx = 0 := by
  have hx0 : x ≠ 0 := by
    intro hxzero
    subst x
    exact (not_lt_of_ge (norm_nonneg (r (1 : Circle)))) (by
      simpa using hfar (1 : Circle))
  let q : C(Circle, ℂ) :=
    ⟨fun z ↦ 1 - r z / x,
      continuous_const.sub (r.continuous.div_const x)⟩
  have hqsmall (z : Circle) : ‖-(r z / x)‖ < 1 := by
    simpa [norm_div, div_lt_one (norm_pos_iff.mpr hx0)] using hfar z
  have hqslit (z : Circle) : q z ∈ Complex.slitPlane := by
    change 1 + -(r z / x) ∈ Complex.slitPlane
    exact Complex.mem_slitPlane_of_norm_lt_one (hqsmall z)
  have hq0 (z : Circle) : q z ≠ 0 :=
    Complex.slitPlane_ne_zero (hqslit z)
  let lq : C(Circle, ℂ) :=
    ⟨fun z ↦ Complex.log (q z), q.continuous.clog hqslit⟩
  let lc : C(Circle, ℂ) :=
    ContinuousMap.const Circle (Complex.log (-x))
  refine (hasLog_iff_winding_eq_zero (aroundMap r x)
    (aroundMap_ne_zero r hx)).mp ?_
  refine ⟨lc + lq, fun z ↦ ?_⟩
  change Complex.exp (Complex.log (-x) + Complex.log (q z)) = r z - x
  rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hx0),
    Complex.exp_log (hq0 z)]
  change -x * (1 - r z / x) = r z - x
  field_simp [hx0]
  ring

/-- The winding number vanishes on every unbounded complementary component. -/
theorem windingAround_eq_zero_of_not_isBounded_component
    (r : C(Circle, ℂ)) {x : ℂ} (hx : x ∈ (Set.range r)ᶜ)
    (hxb : ¬ Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ x)) :
    windingAround r x hx = 0 := by
  obtain ⟨R, hR⟩ := (isCompact_range r.continuous).isBounded.subset_ball (0 : ℂ)
  have hy : ∃ y ∈ connectedComponentIn (Set.range r)ᶜ x, R < ‖y‖ := by
    by_contra h
    push Not at h
    apply hxb
    exact (isBounded_iff_forall_norm_le
      (s := connectedComponentIn (Set.range r)ᶜ x)).2 ⟨R, h⟩
  obtain ⟨y, hycomp, hyR⟩ := hy
  have hycompl : y ∈ (Set.range r)ᶜ :=
    connectedComponentIn_subset (Set.range r)ᶜ x hycomp
  have hfar (z : Circle) : ‖r z‖ < ‖y‖ := by
    have := hR (⟨z, rfl⟩ : r z ∈ Set.range r)
    rw [Metric.mem_ball, dist_zero_right] at this
    exact this.trans hyR
  calc
    windingAround r x hx = windingAround r y hycompl :=
      (windingAround_eq_of_mem_connectedComponentIn r hx hycompl hycomp).symm
    _ = 0 := windingAround_eq_zero_of_forall_norm_lt r hycompl hfar

/-- A smooth, compactly supported approximation of the inverse parametrization, shifted by a
small regular value. -/
structure RegularApproximation (r : C(Circle, ℂ)) where
  g : ℂ → ℂ
  a : ℂ
  smooth' : ContDiff ℝ ∞ g
  a_ne_zero : a ≠ 0
  close_on_curve : ∀ z, ‖(g (r z) - a) - z‖ < 1
  roots_finite : {x | g x = a}.Finite
  regular : ∀ x, g x = a → (fderiv ℝ g x).det ≠ 0

theorem exists_regularApproximation
    (r : C(Circle, ℂ)) (hinj : Function.Injective r) :
    Nonempty (RegularApproximation r) := by
  classical
  have hrclosed : Topology.IsClosedEmbedding r :=
    r.continuous.isClosedEmbedding hinj
  obtain ⟨F, hF⟩ := circleCoe.exists_extension hrclosed
  obtain ⟨R, hR⟩ := (isCompact_range r.continuous).isBounded.subset_ball (0 : ℂ)
  let cutoff : ℂ → ℝ := fun x ↦ max 0 (min 1 (R + 1 - ‖x‖))
  have hcutoff_cont : Continuous cutoff := by
    exact (continuous_const.max
      (continuous_const.min (continuous_const.sub continuous_norm)))
  have hcutoff_range (z : Circle) : cutoff (r z) = 1 := by
    have hz := hR (⟨z, rfl⟩ : r z ∈ Set.range r)
    rw [Metric.mem_ball, dist_zero_right] at hz
    have : 1 < R + 1 - ‖r z‖ := by linarith
    simp [cutoff, min_eq_left this.le]
  have hcutoff_far {x : ℂ} (hx : R + 1 ≤ ‖x‖) : cutoff x = 0 := by
    have : R + 1 - ‖x‖ ≤ 0 := sub_nonpos.mpr hx
    dsimp [cutoff]
    rw [show min 1 (R + 1 - ‖x‖) = R + 1 - ‖x‖ by
      exact min_eq_right (this.trans zero_le_one)]
    exact max_eq_left this
  let f : ℂ → ℂ := fun x ↦ cutoff x • F x
  have hfcont : Continuous f := hcutoff_cont.smul F.continuous
  have hfrange (z : Circle) : f (r z) = z := by
    change cutoff (r z) • F (r z) = z
    rw [hcutoff_range]
    have hFr : F (r z) = z := DFunLike.congr_fun hF z
    simp [hFr]
  have hfsupport : Function.support f ⊆ Metric.closedBall (0 : ℂ) (R + 1) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hnorm
    have hnorm' : R + 1 ≤ ‖x‖ := le_of_not_ge hnorm
    exact hx (by simp [f, hcutoff_far hnorm'])
  obtain ⟨g, hg, hgclose, hgsupport⟩ :=
    hfcont.exists_contDiff_approx ⊤ (continuous_const : Continuous fun _ : ℂ ↦ (1 / 16 : ℝ))
      (fun _ ↦ by norm_num)
  let critical : Set ℂ := {x | (fderiv ℝ g x).det = 0}
  have hgdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hcritical : volume (g '' critical) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (μ := volume) (s := critical) (f' := fun x ↦ fderiv ℝ g x)
    · intro x _hx
      exact (hgdiff x).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      exact hx
  let bad : Set ℂ := g '' critical ∪ {0}
  have hbad : volume bad = 0 := by
    exact measure_union_null hcritical (by simp)
  have hdense : Dense badᶜ := by
    rw [dense_iff_closure_eq, closure_compl,
      MeasureTheory.Measure.interior_eq_empty_of_null hbad]
    simp
  obtain ⟨a, habad, haball⟩ := hdense.exists_mem_open
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) (1 / 16)))
    (Metric.nonempty_ball.mpr (by norm_num))
  have ha0 : a ≠ 0 := by
    intro ha
    apply habad
    exact Or.inr (by simp [ha])
  have hanorm : ‖a‖ < 1 / 16 := by
    simpa [Metric.mem_ball, dist_zero_right] using haball
  have haregular (x : ℂ) (hx : g x = a) : (fderiv ℝ g x).det ≠ 0 := by
    intro hdet
    apply habad
    exact Or.inl ⟨x, hdet, hx⟩
  let roots : Set ℂ := {x | g x = a}
  have hroots_closed : IsClosed roots := by
    exact isClosed_singleton.preimage hg.continuous
  have hroots_subset : roots ⊆ Metric.closedBall (0 : ℂ) (R + 1) := by
    intro x hx
    apply hfsupport (hgsupport ?_)
    change g x ≠ 0
    rw [hx]
    exact ha0
  have hroots_compact : IsCompact roots :=
    (isCompact_closedBall (0 : ℂ) (R + 1)).of_isClosed_subset
      hroots_closed hroots_subset
  have hroots_discrete : IsDiscrete roots := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro x hx
    let A : ℂ ≃L[ℝ] ℂ :=
      (fderiv ℝ g x).toContinuousLinearEquivOfDetNeZero (haregular x hx)
    have hfd : HasFDerivAt g (fderiv ℝ g x) x :=
      (hgdiff x).hasFDerivAt
    have hstrict : HasStrictFDerivAt g (A : ℂ →L[ℝ] ℂ) x := by
      simpa only [A, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
        hg.contDiffAt.hasStrictFDerivAt' hfd (by simp)
    let e : OpenPartialHomeomorph ℂ ℂ := hstrict.toOpenPartialHomeomorph g
    refine ⟨e.source, e.open_source, ?_⟩
    ext y
    constructor
    · rintro ⟨hyU, hyroot⟩
      have hxy : y = x := by
        apply e.injOn hyU hstrict.mem_toOpenPartialHomeomorph_source
        exact hyroot.trans hx.symm
      simp [hxy]
    · intro hy
      have hyx : y = x := by simpa using hy
      subst y
      exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hx⟩
  have hroots_finite : roots.Finite := hroots_compact.finite hroots_discrete
  refine ⟨{
    g := g
    a := a
    smooth' := hg
    a_ne_zero := ha0
    close_on_curve := fun z ↦ ?_
    roots_finite := hroots_finite
    regular := haregular }⟩
  calc
    ‖(g (r z) - a) - z‖ ≤ ‖g (r z) - z‖ + ‖a‖ := by
      calc
        ‖(g (r z) - a) - z‖ = ‖(g (r z) - z) - a‖ := by
          congr 1
          ring
        _ ≤ ‖g (r z) - z‖ + ‖a‖ := norm_sub_le _ _
    _ < 1 / 16 + 1 / 16 := by
      gcongr
      simpa [dist_eq_norm, hfrange] using hgclose (r z)
    _ < 1 := by norm_num

end

end Submission.Existence
