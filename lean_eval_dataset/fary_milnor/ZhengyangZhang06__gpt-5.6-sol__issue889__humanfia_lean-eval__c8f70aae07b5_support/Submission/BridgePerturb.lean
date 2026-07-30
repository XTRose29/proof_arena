import Submission.SignArc

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def heightProfilePerturb (r : ℝ → Space) (u : Space)
    (a b c t : ℝ) : Space :=
  r t + (c * bridgeCircleY a b t) • u

theorem contDiff_heightProfilePerturb {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      heightProfilePerturb r u a b p.2 p.1) := by
  have hY : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => bridgeCircleY a b p.1) :=
    (contDiff_bridgeCircleY ha hab hb).comp contDiff_fst
  simpa [heightProfilePerturb] using
    (hknot.smooth.comp contDiff_fst).add
      ((contDiff_snd.mul hY).smul
        (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => u)))

theorem periodic_heightProfilePerturb {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (a b c : ℝ) :
    Function.Periodic (heightProfilePerturb r u a b c) period := by
  intro t
  simp [heightProfilePerturb, hknot.periodic t, periodic_bridgeCircleY a b t]

theorem velocity_heightProfilePerturb {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b c t : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    velocity (heightProfilePerturb r u a b c) t =
      velocity r t +
        (c * (bridgeCircleSpeed a b t * bridgeCircleX a b t)) • u := by
  have hr := hasDerivAt_curve hknot t
  have hY := (hasDerivAt_bridgeCircleY (t := t) ha hab hb).const_mul c
  have hYu := hY.smul_const u
  have hsum := hr.add hYu
  have hsum' : HasDerivAt (heightProfilePerturb r u a b c)
      (velocity r t +
        (c * (bridgeCircleSpeed a b t * bridgeCircleX a b t)) • u) t :=
    hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  exact hsum'.deriv

theorem height_heightProfilePerturb {r : ℝ → Space} (u : Space)
    (hu : ‖u‖ = 1) (a b c t : ℝ) :
    height (heightProfilePerturb r u a b c) u t =
      height r u t + c * bridgeCircleY a b t := by
  change inner ℝ u (r t + (c * bridgeCircleY a b t) • u) =
    inner ℝ u (r t) + c * bridgeCircleY a b t
  rw [inner_add_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hu]
  norm_num

theorem deriv_height_heightProfilePerturb {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (hu : ‖u‖ = 1)
    {a b c t : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    deriv (height (heightProfilePerturb r u a b c) u) t =
      ‖velocity r t‖ * directionalUnitTangent r u t +
        c * (bridgeCircleSpeed a b t * bridgeCircleX a b t) := by
  have heq : height (heightProfilePerturb r u a b c) u =
      fun x => height r u x + c * bridgeCircleY a b x := by
    funext x
    exact height_heightProfilePerturb u hu a b c x
  rw [heq]
  have hsum := (hasDerivAt_height hknot u t).add
    ((hasDerivAt_bridgeCircleY (t := t) ha hab hb).const_mul c)
  have hsum' : HasDerivAt (fun x => height r u x + c * bridgeCircleY a b x)
      (inner ℝ u (velocity r t) +
        c * (bridgeCircleSpeed a b t * bridgeCircleX a b t)) t :=
    hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  rw [hsum'.deriv]
  rw [← (hasDerivAt_height hknot u t).deriv,
    deriv_height_eq_speed_mul_directionalUnitTangent hknot]

theorem deriv_nonneg_of_right_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableAt ℝ f a) (hab : a < b) (hfa : f a = 0)
    (hnonneg : ∀ x ∈ Ioo a b, 0 ≤ f x) : 0 ≤ deriv f a := by
  have htend := (hasDerivAt_iff_tendsto_slope_left_right.mp hf.hasDerivAt).2
  apply ge_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hab).filter_mono inf_le_left] with x hax hxb
  rw [slope_nonneg_iff_of_le hax.le, hfa]
  exact hnonneg x ⟨hax, hxb⟩

theorem deriv_nonpos_of_right_nonpos {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableAt ℝ f a) (hab : a < b) (hfa : f a = 0)
    (hnonpos : ∀ x ∈ Ioo a b, f x ≤ 0) : deriv f a ≤ 0 := by
  have htend := (hasDerivAt_iff_tendsto_slope_left_right.mp hf.hasDerivAt).2
  apply le_of_tendsto htend
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hab).filter_mono inf_le_left] with x hax hxb
  rw [slope_nonpos_iff_of_le hax.le, hfa]
  exact hnonpos x ⟨hax, hxb⟩

theorem contDiff_bridgeCircleSpeed {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) : ContDiff ℝ ⊤ (bridgeCircleSpeed a b) := by
  unfold bridgeCircleSpeed
  exact contDiff_const.div (contDiff_bridgeDenominator a b)
    fun t => (bridgeDenominator_pos (t := t) ha hab hb).ne'

theorem deriv_bridgeCircleVelocity_left_pos {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    0 < deriv (bridgeCircleSpeed a b * bridgeCircleX a b) a := by
  have hs : HasDerivAt (bridgeCircleSpeed a b)
      (deriv (bridgeCircleSpeed a b) a) a :=
    ((contDiff_bridgeCircleSpeed ha hab hb).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hx := hasDerivAt_bridgeCircleX (t := a) ha hab hb
  have hprod := hs.mul hx
  have heq := hprod.deriv
  rw [bridgeCircleX_left, bridgeCircleY_left ha hab hb] at heq
  simp only [mul_zero, zero_add, mul_neg, neg_neg] at heq
  rw [heq]
  exact mul_pos (bridgeCircleSpeed_pos ha hab hb)
    (mul_pos (bridgeCircleSpeed_pos ha hab hb) zero_lt_one)

theorem deriv_bridgeCircleVelocity_right_neg {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    deriv (bridgeCircleSpeed a b * bridgeCircleX a b) b < 0 := by
  have hs : HasDerivAt (bridgeCircleSpeed a b)
      (deriv (bridgeCircleSpeed a b) b) b :=
    ((contDiff_bridgeCircleSpeed ha hab hb).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hx := hasDerivAt_bridgeCircleX (t := b) ha hab hb
  have hprod := hs.mul hx
  have heq := hprod.deriv
  rw [bridgeCircleX_right, bridgeCircleY_right ha hab hb] at heq
  simp only [mul_zero, zero_add, mul_one] at heq
  rw [heq]
  exact mul_neg_of_pos_of_neg (bridgeCircleSpeed_pos ha hab hb)
    (neg_neg_of_pos (bridgeCircleSpeed_pos ha hab hb))

theorem deriv_deriv_height_heightProfilePerturb_of_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (hu : ‖u‖ = 1)
    {a b c t : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < period)
    (hz : directionalUnitTangent r u t = 0) :
    deriv (deriv (height (heightProfilePerturb r u a b c) u)) t =
      ‖velocity r t‖ * deriv (directionalUnitTangent r u) t +
        c * deriv (bridgeCircleSpeed a b * bridgeCircleX a b) t := by
  have heq : deriv (height (heightProfilePerturb r u a b c) u) =
      fun x => ‖velocity r x‖ * directionalUnitTangent r u x +
        c * (bridgeCircleSpeed a b x * bridgeCircleX a b x) := by
    funext x
    exact deriv_height_heightProfilePerturb hknot u hu ha hab hb
  rw [heq]
  have hspeed := hasDerivAt_speed hknot t
  have hdir : HasDerivAt (directionalUnitTangent r u)
      (deriv (directionalUnitTangent r u) t) t :=
    ((contDiff_directionalUnitTangent hknot u).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hbridge : HasDerivAt
      (bridgeCircleSpeed a b * bridgeCircleX a b)
      (deriv (bridgeCircleSpeed a b * bridgeCircleX a b) t) t :=
    (((contDiff_bridgeCircleSpeed ha hab hb).mul
      (contDiff_bridgeCircleX ha hab hb)).differentiable
        (by simp)).differentiableAt.hasDerivAt
  have hsum := (hspeed.mul hdir).add (hbridge.const_mul c)
  have hsum' : HasDerivAt
      (fun x => ‖velocity r x‖ * directionalUnitTangent r u x +
        c * (bridgeCircleSpeed a b x * bridgeCircleX a b x))
      (inner ℝ (velocity r t) (acceleration r t) / ‖velocity r t‖ *
          directionalUnitTangent r u t +
        ‖velocity r t‖ * deriv (directionalUnitTangent r u) t +
        c * deriv (bridgeCircleSpeed a b * bridgeCircleX a b) t) t :=
    hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  rw [hsum'.deriv, hz]
  ring

theorem deriv_deriv_height_eq_speed_mul_deriv_directional_of_zero
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) (t : ℝ)
    (hz : directionalUnitTangent r u t = 0) :
    deriv (deriv (height r u)) t =
      ‖velocity r t‖ * deriv (directionalUnitTangent r u) t := by
  rw [(hasDerivAt_deriv_height_of_directionalUnitTangent_eq_zero
    hknot u t hz).deriv]
  rw [(hasDerivAt_directionalUnitTangent hknot u t).deriv]

theorem MinMaxBridgeData.of_weak_heightProfilePerturb
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1)
    {a b c : ℝ} (hdata : WeakMinMaxSignData period
      (directionalUnitTangent r u) a b) (hc : 0 < c)
    (hqknot : IsSmoothKnot (heightProfilePerturb r u a b c)) :
    MinMaxBridgeData (heightProfilePerturb r u a b c) u a b := by
  let q := heightProfilePerturb r u a b c
  have hderivPos : ∀ t ∈ Ioo a b, 0 < deriv (height q u) t := by
    intro t ht
    rw [deriv_height_heightProfilePerturb hknot u hu
      hdata.left_mem.1 hdata.left_lt_right hdata.right_mem.2]
    have hbase : 0 ≤ ‖velocity r t‖ * directionalUnitTangent r u t :=
      mul_nonneg (norm_nonneg _) (hdata.nonneg t ⟨ht.1.le, ht.2.le⟩)
    have hprofile : 0 < c *
        (bridgeCircleSpeed a b t * bridgeCircleX a b t) :=
      mul_pos hc (mul_pos
        (bridgeCircleSpeed_pos hdata.left_mem.1 hdata.left_lt_right
          hdata.right_mem.2)
        (bridgeCircleX_pos_of_mem_Ioo hdata.left_mem.1
          hdata.left_lt_right hdata.right_mem.2 ht))
    linarith
  have hderivNeg : ∀ t ∈ Ioo b (a + period),
      deriv (height q u) t < 0 := by
    intro t ht
    rw [deriv_height_heightProfilePerturb hknot u hu
      hdata.left_mem.1 hdata.left_lt_right hdata.right_mem.2]
    have hbase : ‖velocity r t‖ * directionalUnitTangent r u t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
        (hdata.nonpos_wrap t ⟨ht.1.le, ht.2.le⟩)
    have hprofile : c *
        (bridgeCircleSpeed a b t * bridgeCircleX a b t) < 0 :=
      mul_neg_of_pos_of_neg hc (mul_neg_of_pos_of_neg
        (bridgeCircleSpeed_pos hdata.left_mem.1 hdata.left_lt_right
          hdata.right_mem.2)
        (bridgeCircleX_neg_of_mem_wrap hdata.left_mem.1
          hdata.left_lt_right hdata.right_mem.2 ht))
    linarith
  have hleftZero : directionalUnitTangent q u a = 0 := by
    have hheight : deriv (height q u) a = 0 := by
      rw [deriv_height_heightProfilePerturb hknot u hu
        hdata.left_mem.1 hdata.left_lt_right hdata.right_mem.2,
        hdata.left_zero, bridgeCircleX_left]
      ring
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hqknot u] at hheight
    exact (mul_eq_zero.mp hheight).resolve_left
      (norm_ne_zero_iff.mpr (hqknot.regular a))
  have hrightZero : directionalUnitTangent q u b = 0 := by
    have hheight : deriv (height q u) b = 0 := by
      rw [deriv_height_heightProfilePerturb hknot u hu
        hdata.left_mem.1 hdata.left_lt_right hdata.right_mem.2,
        hdata.right_zero, bridgeCircleX_right]
      ring
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hqknot u] at hheight
    exact (mul_eq_zero.mp hheight).resolve_left
      (norm_ne_zero_iff.mpr (hqknot.regular b))
  refine ⟨hdata.left_mem, hdata.right_mem, hdata.left_lt_right, ?_, ?_,
    ?_, ?_, hleftZero, hrightZero, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Icc a b)
      (continuous_height hqknot u).continuousOn
    intro t ht
    rw [interior_Icc] at ht
    exact hderivPos t ht
  · apply strictAntiOn_of_deriv_neg (convex_Icc b (a + period))
      (continuous_height hqknot u).continuousOn
    intro t ht
    rw [interior_Icc] at ht
    exact hderivNeg t ht
  · intro t ht
    have h := hderivPos t ht
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hqknot u] at h
    exact pos_of_mul_pos_right h (norm_nonneg _)
  · intro t ht
    have h := hderivNeg t ht
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hqknot u] at h
    exact neg_of_mul_neg_right h (norm_nonneg _)
  · have hfderiv : 0 ≤ deriv (directionalUnitTangent r u) a :=
      deriv_nonneg_of_right_nonneg
        ((contDiff_directionalUnitTangent hknot u).differentiable
          (by simp)).differentiableAt hdata.left_lt_right hdata.left_zero
        (fun t ht => hdata.nonneg t ⟨ht.1.le, ht.2.le⟩)
    have hsecond : 0 < deriv (deriv (height q u)) a := by
      rw [deriv_deriv_height_heightProfilePerturb_of_zero hknot u hu
        hdata.left_mem.1 hdata.left_lt_right hdata.right_mem.2
        hdata.left_zero]
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (norm_nonneg _) hfderiv)
        (mul_pos hc (deriv_bridgeCircleVelocity_left_pos
          hdata.left_mem.1 hdata.left_lt_right hdata.right_mem.2))
    rw [deriv_deriv_height_eq_speed_mul_deriv_directional_of_zero
      hqknot u a hleftZero] at hsecond
    exact pos_of_mul_pos_right hsecond (norm_nonneg _)
  · have hfderiv : deriv (directionalUnitTangent r u) b ≤ 0 :=
      deriv_nonpos_of_right_nonpos
        ((contDiff_directionalUnitTangent hknot u).differentiable
          (by simp)).differentiableAt
        (show b < a + period by linarith [hdata.left_mem.1,
          hdata.right_mem.2, period_pos]) hdata.right_zero
        (fun t ht => hdata.nonpos_wrap t ⟨ht.1.le, ht.2.le⟩)
    have hsecond : deriv (deriv (height q u)) b < 0 := by
      rw [deriv_deriv_height_heightProfilePerturb_of_zero hknot u hu
        hdata.left_mem.1 hdata.left_lt_right hdata.right_mem.2
        hdata.right_zero]
      exact add_neg_of_nonpos_of_neg
        (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hfderiv)
        (mul_neg_of_pos_of_neg hc (deriv_bridgeCircleVelocity_right_neg
          hdata.left_mem.1 hdata.left_lt_right hdata.right_mem.2))
    rw [deriv_deriv_height_eq_speed_mul_deriv_directional_of_zero
      hqknot u b hrightZero] at hsecond
    exact neg_of_mul_neg_right hsecond (norm_nonneg _)

theorem MinMaxBridgeData.toMaxMin_neg {r : ℝ → Space} {u : Space} {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) : MaxMinBridgeData r (-u) a b where
  left_mem := hdata.left_mem
  right_mem := hdata.right_mem
  left_lt_right := hdata.left_lt_right
  height_anti := by
    intro x hx y hy hxy
    rw [height_neg, height_neg]
    exact neg_lt_neg (hdata.height_mono hx hy hxy)
  height_mono_wrap := by
    intro x hx y hy hxy
    rw [height_neg, height_neg]
    exact neg_lt_neg (hdata.height_anti_wrap hx hy hxy)
  tangent_neg := by
    intro z hz
    rw [directionalUnitTangent_neg]
    exact neg_lt_zero.mpr (hdata.tangent_pos z hz)
  tangent_pos_wrap := by
    intro z hz
    rw [directionalUnitTangent_neg]
    exact neg_pos.mpr (hdata.tangent_neg_wrap z hz)
  tangent_left := by
    rw [directionalUnitTangent_neg, hdata.tangent_left, neg_zero]
  tangent_right := by
    rw [directionalUnitTangent_neg, hdata.tangent_right, neg_zero]
  tangent_deriv_left := by
    rw [deriv_directionalUnitTangent_neg]
    exact neg_lt_zero.mpr hdata.tangent_deriv_left
  tangent_deriv_right := by
    rw [deriv_directionalUnitTangent_neg]
    exact neg_pos.mpr hdata.tangent_deriv_right

theorem MaxMinBridgeData.of_weak_heightProfilePerturb
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1)
    {a b c : ℝ} (hdata : WeakMaxMinSignData period
      (directionalUnitTangent r u) a b) (hc : c < 0)
    (hqknot : IsSmoothKnot (heightProfilePerturb r u a b c)) :
    MaxMinBridgeData (heightProfilePerturb r u a b c) u a b := by
  have hweakNeg : WeakMinMaxSignData period
      (directionalUnitTangent r (-u)) a b := by
    refine ⟨hdata.left_mem, hdata.right_mem, hdata.left_lt_right,
      ?_, ?_, ?_, ?_⟩
    · intro z hz
      rw [directionalUnitTangent_neg]
      exact neg_nonneg.mpr (hdata.nonpos z hz)
    · intro z hz
      rw [directionalUnitTangent_neg]
      exact neg_nonpos.mpr (hdata.nonneg_wrap z hz)
    · rw [directionalUnitTangent_neg, hdata.left_zero, neg_zero]
    · rw [directionalUnitTangent_neg, hdata.right_zero, neg_zero]
  have hcurve : heightProfilePerturb r (-u) a b (-c) =
      heightProfilePerturb r u a b c := by
    funext t
    simp only [heightProfilePerturb]
    module
  have hqknotNeg : IsSmoothKnot (heightProfilePerturb r (-u) a b (-c)) := by
    rw [hcurve]
    exact hqknot
  have hmin := MinMaxBridgeData.of_weak_heightProfilePerturb hknot
    (u := -u) (by simpa using hu) hweakNeg (neg_pos.mpr hc) hqknotNeg
  have hmax := hmin.toMaxMin_neg
  rw [hcurve] at hmax
  simpa using hmax

theorem uniform_c1_close_all_of_periodic_family {A : ℝ → ℝ → Space}
    (hA : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => A p.1 p.2))
    {q : ℝ → Space} (hqperiod : Function.Periodic q period)
    (hAperiod : ∀ s, Function.Periodic (fun t => A t s) period)
    {a epsilon : ℝ}
    (hclose : ∀ t ∈ Icc (0 : ℝ) period,
      ‖A t a - q t‖ < epsilon ∧
      ‖familyVelocity A (t, a) - velocity q t‖ < epsilon) :
    ∀ t, ‖A t a - q t‖ < epsilon ∧
      ‖velocity (fun x => A x a) t - velocity q t‖ < epsilon := by
  intro t
  let fp : ℝ → Space := fun x => A x a - q x
  have hfpperiod : Function.Periodic fp period :=
    (hAperiod a).sub hqperiod
  obtain ⟨tp, htp, htpeq⟩ := hfpperiod.exists_mem_Ico period_pos t 0
  have htpIcc : tp ∈ Icc (0 : ℝ) period :=
    ⟨htp.1, by simpa using htp.2.le⟩
  have hp := (hclose tp htpIcc).1
  have hpos : ‖A t a - q t‖ < epsilon := by
    change ‖fp t‖ < epsilon
    rw [htpeq]
    exact hp
  let fv : ℝ → Space := fun x =>
    velocity (fun y => A y a) x - velocity q x
  have hfvperiod : Function.Periodic fv period := by
    exact (periodic_deriv (hAperiod a)).sub (periodic_deriv hqperiod)
  obtain ⟨tv, htv, htveq⟩ := hfvperiod.exists_mem_Ico period_pos t 0
  have htvIcc : tv ∈ Icc (0 : ℝ) period :=
    ⟨htv.1, by simpa using htv.2.le⟩
  have hv := (hclose tv htvIcc).2
  rw [familyVelocity_eq_velocity hA] at hv
  have hvel : ‖velocity (fun x => A x a) t - velocity q t‖ < epsilon := by
    change ‖fv t‖ < epsilon
    rw [htveq]
    exact hv
  exact ⟨hpos, hvel⟩

set_option maxHeartbeats 2000000 in
theorem exists_heightProfilePerturb_isotopy_radius {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ c, |c| < eta →
      IsKnotIsotopic r (heightProfilePerturb r u a b c) := by
  let A : ℝ → ℝ → Space := fun t c => heightProfilePerturb r u a b c t
  have hA : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => A p.1 p.2) := by
    simpa [A] using contDiff_heightProfilePerturb hknot u ha hab hb
  have hAperiod : ∀ c, Function.Periodic (fun t => A t c) period := by
    intro c
    exact periodic_heightProfilePerturb hknot u a b c
  obtain ⟨epsilon, hepsilon, hstable⟩ := exists_c1_knot_neighborhood hknot
  obtain ⟨eta, heta, hclose⟩ :=
    exists_uniform_c1_close_endpoint_radius hA hepsilon (c := 0) (q := r) (by
      intro t
      simp [A, heightProfilePerturb])
  have hsmallKnot : ∀ c, |c| < eta → IsSmoothKnot (fun t => A t c) := by
    intro c hc
    have hperiodClose := hclose c (by simpa using hc)
    have hcloseAll := uniform_c1_close_all_of_periodic_family hA hknot.periodic
      hAperiod hperiodClose
    apply hstable (fun t => A t c)
    · exact hA.comp (contDiff_id.prodMk contDiff_const)
    · exact hAperiod c
    · exact fun t => (hcloseAll t).1
    · exact fun t => (hcloseAll t).2
  refine ⟨eta, heta, ?_⟩
  intro c hc
  let R : ℝ → ℝ → Space := fun t s => A t (s * c)
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · exact hA.comp (contDiff_fst.prodMk (contDiff_snd.mul contDiff_const))
  · intro t
    simp [R, A, heightProfilePerturb]
  · intro t
    simp [R, A]
  · intro s hs
    apply hsmallKnot (s * c)
    rw [abs_mul, abs_of_nonneg hs.1]
    have hle : s * |c| ≤ |c| :=
      mul_le_of_le_one_left (abs_nonneg c) hs.2
    exact hle.trans_lt hc

theorem constant_of_monotone_of_periodic {g : ℝ → ℝ} {P : ℝ}
    (hP : 0 < P) (hperiod : Function.Periodic g P) (hmono : Monotone g) :
    ∀ x y, g x = g y := by
  have hordered : ∀ x y, x ≤ y → g x = g y := by
    intro x y hxy
    obtain ⟨n, hn⟩ := exists_nat_gt ((y - x) / P)
    have hmul : y - x < (n : ℝ) * P := (div_lt_iff₀ hP).mp hn
    have hybound : y ≤ x + n • P := by
      simp only [nsmul_eq_mul]
      linarith
    have hleft := hmono hxy
    have hright := hmono hybound
    have hper := (hperiod.nsmul n) x
    rw [hper] at hright
    exact le_antisymm hleft hright
  intro x y
  rcases le_total x y with hxy | hyx
  · exact hordered x y hxy
  · exact (hordered y x hyx).symm

theorem constant_of_antitone_of_periodic {g : ℝ → ℝ} {P : ℝ}
    (hP : 0 < P) (hperiod : Function.Periodic g P) (hanti : Antitone g) :
    ∀ x y, g x = g y := by
  have hmono : Monotone (fun x => -g x) := by
    intro x y hxy
    exact neg_le_neg (hanti hxy)
  have hperiodNeg : Function.Periodic (fun x => -g x) P := by
    intro x
    change -g (x + P) = -g x
    rw [hperiod x]
  have hconst := constant_of_monotone_of_periodic hP hperiodNeg hmono
  intro x y
  exact neg_inj.mp (hconst x y)

theorem directionalUnitTangent_eq_zero_of_nonnegative {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space)
    (hnonneg : ∀ t, 0 ≤ directionalUnitTangent r u t) :
    directionalUnitTangent r u = 0 := by
  have hmono : Monotone (height r u) := by
    apply monotone_of_deriv_nonneg
    · exact (contDiff_height hknot u).differentiable (by simp)
    · intro t
      rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot]
      exact mul_nonneg (norm_nonneg _) (hnonneg t)
  have hconst := constant_of_monotone_of_periodic period_pos
    (periodic_height hknot u) hmono
  have hheight : height r u = fun _ => height r u 0 := by
    funext t
    exact hconst t 0
  funext t
  simpa [directionalUnitTangent] using
    inner_unitTangent_eq_zero_of_height_constant hknot u (height r u 0) hheight t

theorem directionalUnitTangent_eq_zero_of_nonpositive {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space)
    (hnonpos : ∀ t, directionalUnitTangent r u t ≤ 0) :
    directionalUnitTangent r u = 0 := by
  have hanti : Antitone (height r u) := by
    apply antitone_of_deriv_nonpos
    · exact (contDiff_height hknot u).differentiable (by simp)
    · intro t
      rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot]
      exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (hnonpos t)
  have hconst := constant_of_antitone_of_periodic period_pos
    (periodic_height hknot u) hanti
  have hheight : height r u = fun _ => height r u 0 := by
    funext t
    exact hconst t 0
  funext t
  simpa [directionalUnitTangent] using
    inner_unitTangent_eq_zero_of_height_constant hknot u (height r u 0) hheight t

theorem exists_pos_neg_directionalUnitTangent_of_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space)
    (hne : directionalUnitTangent r u ≠ 0) :
    (∃ t ∈ Ioo (0 : ℝ) period, 0 < directionalUnitTangent r u t) ∧
      ∃ t ∈ Ioo (0 : ℝ) period, directionalUnitTangent r u t < 0 := by
  let f := directionalUnitTangent r u
  have hfperiod : Function.Periodic f period := periodic_directionalUnitTangent hknot u
  have hposAny : ∃ t, 0 < f t := by
    by_contra hnot
    have hnonpos : ∀ t, f t ≤ 0 := fun t => le_of_not_gt fun ht => hnot ⟨t, ht⟩
    exact hne (directionalUnitTangent_eq_zero_of_nonpositive hknot u hnonpos)
  have hnegAny : ∃ t, f t < 0 := by
    by_contra hnot
    have hnonneg : ∀ t, 0 ≤ f t := fun t => le_of_not_gt fun ht => hnot ⟨t, ht⟩
    exact hne (directionalUnitTangent_eq_zero_of_nonnegative hknot u hnonneg)
  constructor
  · rcases hposAny with ⟨t, ht⟩
    obtain ⟨s, hs, hts⟩ := hfperiod.exists_mem_Ico period_pos t 0
    have hsp : 0 < f s := by rw [← hts]; exact ht
    by_cases hs0 : s = 0
    · subst s
      exact exists_right_pos (continuous_directionalUnitTangent hknot u).continuousAt
        hsp period_pos
    · exact ⟨s, ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), by simpa using hs.2⟩, hsp⟩
  · rcases hnegAny with ⟨t, ht⟩
    obtain ⟨s, hs, hts⟩ := hfperiod.exists_mem_Ico period_pos t 0
    have hsn : f s < 0 := by rw [← hts]; exact ht
    by_cases hs0 : s = 0
    · subst s
      exact exists_right_lt_zero
        (continuous_directionalUnitTangent hknot u).continuousAt hsn period_pos
    · exact ⟨s, ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), by simpa using hs.2⟩, hsn⟩

theorem IsKnotIsotopic.right_isSmoothKnot {p q : ℝ → Space}
    (hpq : IsKnotIsotopic p q) : IsSmoothKnot q := by
  rcases hpq with ⟨R, _hR, _hR0, hR1, hRknot⟩
  simpa only [hR1] using hRknot 1 ⟨zero_le_one, le_rfl⟩

theorem isUnknotted_of_weak_bridge_sign_data {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1)
    (hdata : (∃ a b, WeakMinMaxSignData period
        (directionalUnitTangent r u) a b) ∨
      ∃ a b, WeakMaxMinSignData period
        (directionalUnitTangent r u) a b) : IsUnknotted r := by
  rcases hdata with ⟨a, b, hab⟩ | ⟨a, b, hab⟩
  · obtain ⟨eta, heta, hisoRadius⟩ :=
      exists_heightProfilePerturb_isotopy_radius hknot u
        hab.left_mem.1 hab.left_lt_right hab.right_mem.2
    let c := eta / 2
    have hc : 0 < c := div_pos heta (by norm_num)
    have hcsmall : |c| < eta := by
      rw [abs_of_pos hc]
      dsimp [c]
      linarith
    have hiso := hisoRadius c hcsmall
    have hqknot := hiso.right_isSmoothKnot
    have hbridge := MinMaxBridgeData.of_weak_heightProfilePerturb
      hknot hu hab hc hqknot
    apply hiso.isUnknotted
    exact isUnknotted_of_minMaxBridgeData hqknot hu hbridge
  · obtain ⟨eta, heta, hisoRadius⟩ :=
      exists_heightProfilePerturb_isotopy_radius hknot u
        hab.left_mem.1 hab.left_lt_right hab.right_mem.2
    let c := -(eta / 2)
    have hc : c < 0 := by dsimp [c]; linarith
    have hcsmall : |c| < eta := by
      rw [abs_of_neg hc]
      dsimp [c]
      linarith
    have hiso := hisoRadius c hcsmall
    have hqknot := hiso.right_isSmoothKnot
    have hbridge := MaxMinBridgeData.of_weak_heightProfilePerturb
      hknot hu hab hc hqknot
    apply hiso.isUnknotted
    exact isUnknotted_of_maxMinBridgeData hqknot hu hbridge

end Submission.Helpers
