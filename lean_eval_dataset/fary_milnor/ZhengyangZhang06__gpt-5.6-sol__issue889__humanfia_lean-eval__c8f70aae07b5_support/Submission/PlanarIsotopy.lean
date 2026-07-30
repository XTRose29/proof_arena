import Submission.PlanarReparam

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

theorem injOn_periodic_shifted_Ico {q : ℝ → Space}
    (hperiodic : Function.Periodic q period)
    (hinj : Set.InjOn q (Ico (0 : ℝ) period)) (a : ℝ) :
    Set.InjOn q (Ico a (a + period)) := by
  intro x hx y hy hxy
  have hp : 0 < period := by simp [period, Real.pi_pos]
  obtain ⟨nx, hnx, _⟩ := existsUnique_zsmul_near_of_pos' hp x
  obtain ⟨ny, hny, _⟩ := existsUnique_zsmul_near_of_pos' hp y
  have hqx : q (x - nx • period) = q x := hperiodic.sub_zsmul_eq nx
  have hqy : q (y - ny • period) = q y := hperiodic.sub_zsmul_eq ny
  have hred : x - nx • period = y - ny • period :=
    hinj hnx hny (hqx.trans (hxy.trans hqy.symm))
  have hcongr : x + (ny - nx) • period = y := by
    rw [sub_zsmul]
    linarith
  obtain ⟨m, _hm, huniq⟩ := existsUnique_add_zsmul_mem_Ico hp x a
  have hzero : x + (0 : ℤ) • period ∈ Ico a (a + period) := by
    simpa using hx
  have hdelta : x + (ny - nx) • period ∈ Ico a (a + period) := by
    rw [hcongr]
    exact hy
  have hdeltaZero : ny - nx = 0 :=
    (huniq (ny - nx) hdelta).trans (huniq 0 hzero).symm
  have hnyx : ny = nx := sub_eq_zero.mp hdeltaZero
  rw [hnyx] at hred
  linarith

theorem isSmoothKnot_comp_degreeOne {q : ℝ → Space} (hq : IsSmoothKnot q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ⊤ φ)
    (hφperiod : ∀ t, φ (t + period) = φ t + period)
    (hφmono : StrictMono φ) (hφderiv : ∀ t, deriv φ t ≠ 0) :
    IsSmoothKnot (fun t => q (φ t)) where
  smooth := hq.smooth.comp hφ
  periodic := by
    intro t
    change q (φ (t + period)) = q (φ t)
    rw [hφperiod, hq.periodic]
  injective_on_period := by
    intro x hx y hy hxy
    have hφperiodZero : φ period = φ 0 + period := by
      simpa using hφperiod 0
    have hφx : φ x ∈ Ico (φ 0) (φ 0 + period) := by
      constructor
      · exact hφmono.monotone hx.1
      · rw [← hφperiodZero]
        exact hφmono hx.2
    have hφy : φ y ∈ Ico (φ 0) (φ 0 + period) := by
      constructor
      · exact hφmono.monotone hy.1
      · rw [← hφperiodZero]
        exact hφmono hy.2
    have hφxy := injOn_periodic_shifted_Ico hq.periodic hq.injective_on_period
      (φ 0) hφx hφy hxy
    exact hφmono.injective hφxy
  regular := by
    intro t
    have hφat : HasDerivAt φ (deriv φ t) t :=
      ((hφ.differentiable (by simp)).differentiableAt).hasDerivAt
    have hcomp := (hasDerivAt_curve hq (φ t)).scomp t hφat
    rw [velocity]
    change deriv (q ∘ φ) t ≠ 0
    rw [hcomp.deriv]
    exact smul_ne_zero (hφderiv t) (hq.regular (φ t))

def ofLpContinuousLinearMap : Space →L[ℝ] (Fin 3 → ℝ) where
  toFun := ofLp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def spaceCoordinateCLM (i : Fin 3) : Space →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
    ofLpContinuousLinearMap

noncomputable def minOrientationCLM (w : ℝ) : Space →L[ℝ] Space where
  toFun v := toLp 2 ![(1 - w) * v 0 + w * v 1,
    w * v 0 + (1 - w) * v 1, w * (1 - w) * (v 1 - v 0)]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [smul_eq_mul]
    all_goals ring
  cont := by fun_prop

noncomputable def maxOrientationCLM (w : ℝ) : Space →L[ℝ] Space where
  toFun v := toLp 2 ![(1 - w) * v 0 - w * v 1,
    -w * v 0 + (1 - w) * v 1, w * (1 - w) * (v 0 + v 1)]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [smul_eq_mul]
    all_goals ring
  cont := by fun_prop

theorem minOrientationCLM_eq_zero_of_coord_two_eq_zero {w : ℝ} {v : Space}
    (hv2 : v 2 = 0) (hzero : minOrientationCLM w v = 0) : v = 0 := by
  have h0 := congrArg (fun z : Space => z 0) hzero
  have h1 := congrArg (fun z : Space => z 1) hzero
  have h2 := congrArg (fun z : Space => z 2) hzero
  simp [minOrientationCLM] at h0 h1 h2
  have h2' : w * (1 - w) * (v 1 - v 0) = 0 := by
    rcases h2 with (hw | hw) | hv
    · simp [hw]
    · simp [hw]
    · simp [hv]
  obtain ⟨hv0, hv1⟩ := minOrientation_kernel (w := w) (x := v 0) (y := v 1)
    h0 h1 h2'
  ext i
  fin_cases i
  · simpa using hv0
  · simpa using hv1
  · simpa using hv2

theorem maxOrientationCLM_eq_zero_of_coord_two_eq_zero {w : ℝ} {v : Space}
    (hv2 : v 2 = 0) (hzero : maxOrientationCLM w v = 0) : v = 0 := by
  have h0 := congrArg (fun z : Space => z 0) hzero
  have h1 := congrArg (fun z : Space => z 1) hzero
  have h2 := congrArg (fun z : Space => z 2) hzero
  simp [maxOrientationCLM] at h0 h1 h2
  have h1' : -w * v 0 + (1 - w) * v 1 = 0 := by
    linarith
  have h2' : w * (1 - w) * (v 0 + v 1) = 0 := by
    rcases h2 with (hw | hw) | hv
    · simp [hw]
    · simp [hw]
    · simp [hv]
  obtain ⟨hv0, hv1⟩ := maxOrientation_kernel (w := w) (x := v 0) (y := v 1)
    h0 h1' h2'
  ext i
  fin_cases i
  · simpa using hv0
  · simpa using hv1
  · simpa using hv2

theorem velocity_coord_two_eq_zero {q : ℝ → Space} (hq : IsSmoothKnot q)
    (hplanar : ∀ t, q t 2 = 0) (t : ℝ) :
    velocity q t 2 = 0 := by
  have hcomp := (spaceCoordinateCLM 2).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_curve hq t)
  have hcoord : HasDerivAt (spaceCoordinateCLM 2 ∘ q) (velocity q t 2) t := by
    simpa [spaceCoordinateCLM, ofLpContinuousLinearMap] using hcomp
  have hfun : (spaceCoordinateCLM 2 ∘ q) = fun _ : ℝ => 0 := by
    funext z
    simpa [spaceCoordinateCLM, ofLpContinuousLinearMap] using hplanar z
  rw [hfun] at hcoord
  simpa using hcoord.deriv.symm

theorem isSmoothKnot_minOrientationCLM {q : ℝ → Space} (hq : IsSmoothKnot q)
    (hplanar : ∀ t, q t 2 = 0) (w : ℝ) :
    IsSmoothKnot (fun t => minOrientationCLM w (q t)) where
  smooth := (minOrientationCLM w).contDiff.comp hq.smooth
  periodic := by
    intro t
    change minOrientationCLM w (q (t + period)) = minOrientationCLM w (q t)
    rw [hq.periodic]
  injective_on_period := by
    intro x hx y hy hxy
    apply hq.injective_on_period hx hy
    change minOrientationCLM w (q x) = minOrientationCLM w (q y) at hxy
    have hdiff : minOrientationCLM w (q x - q y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hdiff2 : (q x - q y) 2 = 0 := by
      simp [hplanar]
    exact sub_eq_zero.mp
      (minOrientationCLM_eq_zero_of_coord_two_eq_zero hdiff2 hdiff)
  regular := by
    intro t
    have hcomp := (minOrientationCLM w).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_curve hq t)
    rw [velocity]
    change deriv (minOrientationCLM w ∘ q) t ≠ 0
    rw [hcomp.deriv]
    intro hzero
    have hvel := minOrientationCLM_eq_zero_of_coord_two_eq_zero
      (velocity_coord_two_eq_zero hq hplanar t) hzero
    exact hq.regular t hvel

theorem isSmoothKnot_maxOrientationCLM {q : ℝ → Space} (hq : IsSmoothKnot q)
    (hplanar : ∀ t, q t 2 = 0) (w : ℝ) :
    IsSmoothKnot (fun t => maxOrientationCLM w (q t)) where
  smooth := (maxOrientationCLM w).contDiff.comp hq.smooth
  periodic := by
    intro t
    change maxOrientationCLM w (q (t + period)) = maxOrientationCLM w (q t)
    rw [hq.periodic]
  injective_on_period := by
    intro x hx y hy hxy
    apply hq.injective_on_period hx hy
    change maxOrientationCLM w (q x) = maxOrientationCLM w (q y) at hxy
    have hdiff : maxOrientationCLM w (q x - q y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hdiff2 : (q x - q y) 2 = 0 := by
      simp [hplanar]
    exact sub_eq_zero.mp
      (maxOrientationCLM_eq_zero_of_coord_two_eq_zero hdiff2 hdiff)
  regular := by
    intro t
    have hcomp := (maxOrientationCLM w).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_curve hq t)
    rw [velocity]
    change deriv (maxOrientationCLM w ∘ q) t ≠ 0
    rw [hcomp.deriv]
    intro hzero
    have hvel := maxOrientationCLM_eq_zero_of_coord_two_eq_zero
      (velocity_coord_two_eq_zero hq hplanar t) hzero
    exact hq.regular t hvel

noncomputable def bridgeStageWeight (s : ℝ) : ℝ :=
  1 - isotopyWeight s

theorem bridgeStageWeight_nonneg (s : ℝ) : 0 ≤ bridgeStageWeight s := by
  exact sub_nonneg.mpr (isotopyWeight_le_one s)

theorem bridgeStageWeight_le_one (s : ℝ) : bridgeStageWeight s ≤ 1 := by
  dsimp [bridgeStageWeight]
  linarith [isotopyWeight_nonneg s]

theorem bridgeStageWeight_mem_Icc (s : ℝ) : bridgeStageWeight s ∈ Icc (0 : ℝ) 1 :=
  ⟨bridgeStageWeight_nonneg s, bridgeStageWeight_le_one s⟩

@[simp] theorem bridgeStageWeight_zero : bridgeStageWeight 0 = 0 := by
  simp [bridgeStageWeight]

@[simp] theorem bridgeStageWeight_one : bridgeStageWeight 1 = 1 := by
  simp [bridgeStageWeight]

theorem contDiff_bridgeStageWeight : ContDiff ℝ ⊤ bridgeStageWeight := by
  exact contDiff_const.sub contDiff_isotopyWeight

noncomputable def planarUnknotMinMax (r : ℝ → Space) (u : Space)
    (a b t s : ℝ) : Space :=
  let w := bridgeStageWeight s
  minOrientationCLM w
    (planarBridgeCircleHomotopyMinMax r u a b (bridgeReparam a b t s) w)

noncomputable def planarUnknotMaxMin (r : ℝ → Space) (u : Space)
    (a b t s : ℝ) : Space :=
  let w := bridgeStageWeight s
  maxOrientationCLM w
    (planarBridgeCircleHomotopyMaxMin r u a b (bridgeReparam a b t s) w)

@[simp] theorem planarUnknotMinMax_zero {r : ℝ → Space}
    (u : Space) (a b t : ℝ) :
    planarUnknotMinMax r u a b t 0 = planarBridgeCurve r u t := by
  ext i
  fin_cases i <;>
    simp [planarUnknotMinMax, minOrientationCLM,
      planarBridgeCircleHomotopyMinMax, planarBridgeCurve]

@[simp] theorem planarUnknotMaxMin_zero {r : ℝ → Space}
    (u : Space) (a b t : ℝ) :
    planarUnknotMaxMin r u a b t 0 = planarBridgeCurve r u t := by
  ext i
  fin_cases i <;>
    simp [planarUnknotMaxMin, maxOrientationCLM,
      planarBridgeCircleHomotopyMaxMin, planarBridgeCurve]

@[simp] theorem planarUnknotMinMax_one {r : ℝ → Space} {u : Space}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < period) (t : ℝ) :
    planarUnknotMinMax r u a b t 1 = standardCircle t := by
  ext i
  fin_cases i <;>
    simp [planarUnknotMinMax, minOrientationCLM,
      planarBridgeCircleHomotopyMinMax, standardCircle,
      bridgeCircleX_bridgeInverseParameter ha hab hb,
      bridgeCircleY_bridgeInverseParameter ha hab hb]

@[simp] theorem planarUnknotMaxMin_one {r : ℝ → Space} {u : Space}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < period) (t : ℝ) :
    planarUnknotMaxMin r u a b t 1 = standardCircle t := by
  ext i
  fin_cases i <;>
    simp [planarUnknotMaxMin, maxOrientationCLM,
      planarBridgeCircleHomotopyMaxMin, standardCircle,
      bridgeCircleX_bridgeInverseParameter ha hab hb,
      bridgeCircleY_bridgeInverseParameter ha hab hb]

theorem contDiff_planarUnknotMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => planarUnknotMinMax r u a b p.1 p.2) := by
  have hw : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => bridgeStageWeight p.2) :=
    contDiff_bridgeStageWeight.comp contDiff_snd
  have hq : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      planarBridgeCircleHomotopyMinMax r u a b
        (bridgeReparam a b p.1 p.2) (bridgeStageWeight p.2)) :=
    (contDiff_planarBridgeCircleHomotopyMinMax hknot u ha hab hb).comp
      ((contDiff_bridgeReparam ha hab hb).prodMk hw)
  rw [contDiff_euclidean] at hq ⊢
  intro i
  fin_cases i
  · simpa [planarUnknotMinMax, minOrientationCLM] using
      ((contDiff_const.sub hw).mul (hq 0)).add (hw.mul (hq 1))
  · simpa [planarUnknotMinMax, minOrientationCLM] using
      (hw.mul (hq 0)).add ((contDiff_const.sub hw).mul (hq 1))
  · simpa [planarUnknotMinMax, minOrientationCLM] using
      ((hw.mul (contDiff_const.sub hw)).mul ((hq 1).sub (hq 0)))

theorem contDiff_planarUnknotMaxMin {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => planarUnknotMaxMin r u a b p.1 p.2) := by
  have hw : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => bridgeStageWeight p.2) :=
    contDiff_bridgeStageWeight.comp contDiff_snd
  have hq : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      planarBridgeCircleHomotopyMaxMin r u a b
        (bridgeReparam a b p.1 p.2) (bridgeStageWeight p.2)) :=
    (contDiff_planarBridgeCircleHomotopyMaxMin hknot u ha hab hb).comp
      ((contDiff_bridgeReparam ha hab hb).prodMk hw)
  rw [contDiff_euclidean] at hq ⊢
  intro i
  fin_cases i
  · simpa [planarUnknotMaxMin, maxOrientationCLM] using
      ((contDiff_const.sub hw).mul (hq 0)).sub (hw.mul (hq 1))
  · simpa [planarUnknotMaxMin, maxOrientationCLM] using
      (hw.mul (hq 0)).neg.add ((contDiff_const.sub hw).mul (hq 1))
  · simpa [planarUnknotMaxMin, maxOrientationCLM] using
      ((hw.mul (contDiff_const.sub hw)).mul ((hq 0).add (hq 1)))

theorem isSmoothKnot_planarUnknotMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (s : ℝ) :
    IsSmoothKnot (fun t => planarUnknotMinMax r u a b t s) := by
  let w := bridgeStageWeight s
  let q := fun t => planarBridgeCircleHomotopyMinMax r u a b t w
  let φ := fun t => bridgeReparam a b t s
  have hq : IsSmoothKnot q := by
    dsimp [q]
    exact isSmoothKnot_planarBridgeCircleHomotopyMinMax hknot u
      hdata.left_mem hdata.right_mem hdata.left_lt_right
      (bridgeStageWeight_mem_Icc s) hdata.height_mono hdata.height_anti_wrap
      hdata.tangent_pos hdata.tangent_neg_wrap hdata.tangent_left
      hdata.tangent_right hdata.tangent_deriv_left hdata.tangent_deriv_right
  have hφsmooth : ContDiff ℝ ⊤ φ := by
    dsimp [φ]
    exact (contDiff_bridgeReparam hdata.left_mem.1 hdata.left_lt_right
      hdata.right_mem.2).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => s)))
  have hφperiod : ∀ t, φ (t + period) = φ t + period := by
    intro t
    exact bridgeReparam_add_period a b t s
  have hφmono : StrictMono φ := by
    exact strictMono_bridgeReparam hdata.left_mem.1 hdata.left_lt_right
      hdata.right_mem.2
  have hφderiv : ∀ t, deriv φ t ≠ 0 := by
    intro t
    exact ne_of_gt (deriv_bridgeReparam_pos hdata.left_mem.1
      hdata.left_lt_right hdata.right_mem.2)
  have hcomp : IsSmoothKnot (fun t => q (φ t)) :=
    isSmoothKnot_comp_degreeOne hq hφsmooth hφperiod hφmono hφderiv
  have hplanar : ∀ t, (q (φ t)) 2 = 0 := by
    intro t
    simp [q, planarBridgeCircleHomotopyMinMax]
  have horient := isSmoothKnot_minOrientationCLM hcomp hplanar w
  simpa [planarUnknotMinMax, w, q, φ] using horient

theorem isSmoothKnot_planarUnknotMaxMin {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MaxMinBridgeData r u a b) (s : ℝ) :
    IsSmoothKnot (fun t => planarUnknotMaxMin r u a b t s) := by
  let w := bridgeStageWeight s
  let q := fun t => planarBridgeCircleHomotopyMaxMin r u a b t w
  let φ := fun t => bridgeReparam a b t s
  have hq : IsSmoothKnot q := by
    dsimp [q]
    exact isSmoothKnot_planarBridgeCircleHomotopyMaxMin hknot u
      hdata.left_mem hdata.right_mem hdata.left_lt_right
      (bridgeStageWeight_mem_Icc s) hdata.height_anti hdata.height_mono_wrap
      hdata.tangent_neg hdata.tangent_pos_wrap hdata.tangent_left
      hdata.tangent_right hdata.tangent_deriv_left hdata.tangent_deriv_right
  have hφsmooth : ContDiff ℝ ⊤ φ := by
    dsimp [φ]
    exact (contDiff_bridgeReparam hdata.left_mem.1 hdata.left_lt_right
      hdata.right_mem.2).comp
        (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => s)))
  have hφperiod : ∀ t, φ (t + period) = φ t + period := by
    intro t
    exact bridgeReparam_add_period a b t s
  have hφmono : StrictMono φ := by
    exact strictMono_bridgeReparam hdata.left_mem.1 hdata.left_lt_right
      hdata.right_mem.2
  have hφderiv : ∀ t, deriv φ t ≠ 0 := by
    intro t
    exact ne_of_gt (deriv_bridgeReparam_pos hdata.left_mem.1
      hdata.left_lt_right hdata.right_mem.2)
  have hcomp : IsSmoothKnot (fun t => q (φ t)) :=
    isSmoothKnot_comp_degreeOne hq hφsmooth hφperiod hφmono hφderiv
  have hplanar : ∀ t, (q (φ t)) 2 = 0 := by
    intro t
    simp [q, planarBridgeCircleHomotopyMaxMin]
  have horient := isSmoothKnot_maxOrientationCLM hcomp hplanar w
  simpa [planarUnknotMaxMin, w, q, φ] using horient

theorem isUnknotted_planarBridgeCurve_of_nondegenerate_of_ncard_eq_two
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u)
    (hcard : (tangentGreatCircleIntersections r u).ncard = 2) :
    IsUnknotted (planarBridgeCurve r u) := by
  rcases exists_bridgeOrientationData_of_ncard_intersections_eq_two
      hknot u hgeneric hcard with ⟨a, b, hdata⟩ | ⟨a, b, hdata⟩
  · refine ⟨planarUnknotMinMax r u a b, ?_, ?_, ?_, ?_⟩
    · exact contDiff_planarUnknotMinMax hknot u hdata.left_mem.1
        hdata.left_lt_right hdata.right_mem.2
    · intro t
      exact planarUnknotMinMax_zero u a b t
    · intro t
      exact planarUnknotMinMax_one hdata.left_mem.1 hdata.left_lt_right
        hdata.right_mem.2 t
    · intro s _hs
      exact isSmoothKnot_planarUnknotMinMax hknot u hdata s
  · refine ⟨planarUnknotMaxMin r u a b, ?_, ?_, ?_, ?_⟩
    · exact contDiff_planarUnknotMaxMin hknot u hdata.left_mem.1
        hdata.left_lt_right hdata.right_mem.2
    · intro t
      exact planarUnknotMaxMin_zero u a b t
    · intro t
      exact planarUnknotMaxMin_one hdata.left_mem.1 hdata.left_lt_right
        hdata.right_mem.2 t
    · intro s _hs
      exact isSmoothKnot_planarUnknotMaxMin hknot u hdata s

end Submission.Helpers
