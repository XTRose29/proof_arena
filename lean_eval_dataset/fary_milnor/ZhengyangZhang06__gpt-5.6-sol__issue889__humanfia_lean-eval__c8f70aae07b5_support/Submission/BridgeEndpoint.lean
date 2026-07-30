import Submission.BridgeTarget

open LeanEval.Geometry.FaryMilnorProblem
open MeasureTheory
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def minMaxWrapHeightOrderIso {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    (Icc b (a + period))ᵒᵈ ≃o Icc (height r u a) (height r u b) := by
  let f : (Icc b (a + period))ᵒᵈ →
      Icc (height r u a) (height r u b) := fun t =>
    let t' : Icc b (a + period) := OrderDual.ofDual t
    ⟨height r u t', by
      have hbmem : b ∈ Icc b (a + period) := by
        constructor
        · exact le_rfl
        · linarith [hdata.left_mem.1, hdata.right_mem.2]
      have haPmem : a + period ∈ Icc b (a + period) := by
        constructor
        · linarith [hdata.left_mem.1, hdata.right_mem.2]
        · exact le_rfl
      have hlower := strictAntiOn_le_of_le hdata.height_anti_wrap t'.property
        haPmem t'.property.2
      have hupper := strictAntiOn_le_of_le hdata.height_anti_wrap hbmem
        t'.property t'.property.1
      rw [periodic_height hknot u a] at hlower
      exact ⟨hlower, hupper⟩⟩
  have hf : StrictMono f := by
    intro x y hxy
    dsimp [f]
    exact hdata.height_anti_wrap (OrderDual.ofDual y).property
      (OrderDual.ofDual x).property hxy
  have hsurj : Function.Surjective f := by
    intro x
    have hbaP : b ≤ a + period := by
      linarith [hdata.left_mem.1, hdata.right_mem.2]
    have himage : (x : ℝ) ∈ height r u '' Icc b (a + period) := by
      apply intermediate_value_Icc' hbaP
        (continuous_height hknot u).continuousOn
      rw [periodic_height hknot u a]
      exact x.property
    obtain ⟨t, ht, htx⟩ := himage
    refine ⟨OrderDual.toDual ⟨t, ht⟩, ?_⟩
    exact Subtype.ext htx
  exact StrictMono.orderIsoOfSurjective f hf hsurj

@[simp] theorem minMaxWrapHeightOrderIso_apply {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (t : (Icc b (a + period))ᵒᵈ) :
    ((minMaxWrapHeightOrderIso hknot u hdata t :
      Icc (height r u a) (height r u b)) : ℝ) =
      height r u ((OrderDual.ofDual t : Icc b (a + period)) : ℝ) := rfl

noncomputable def minMaxWrapHeightParameter {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (x : ℝ) : ℝ :=
  ((OrderDual.ofDual ((minMaxWrapHeightOrderIso hknot u hdata).symm
    (projIcc (height r u a) (height r u b)
      hdata.height_endpoints_lt.le x)) : Icc b (a + period)) : ℝ)

theorem continuous_minMaxWrapHeightParameter {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    Continuous (minMaxWrapHeightParameter hknot u hdata) := by
  have hval : Continuous (fun t : (Icc b (a + period))ᵒᵈ =>
      ((OrderDual.ofDual t : Icc b (a + period)) : ℝ)) := by
    change Continuous (fun t : Icc b (a + period) => (t : ℝ))
    exact continuous_subtype_val
  exact hval.comp
    ((minMaxWrapHeightOrderIso hknot u hdata).symm.continuous.comp
      continuous_projIcc)

theorem minMaxWrapHeightParameter_mem {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    minMaxWrapHeightParameter hknot u hdata x ∈ Icc b (a + period) :=
  (OrderDual.ofDual ((minMaxWrapHeightOrderIso hknot u hdata).symm
    (projIcc (height r u a) (height r u b)
      hdata.height_endpoints_lt.le x)) : Icc b (a + period)) |>.property

theorem height_minMaxWrapHeightParameter {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Icc (height r u a) (height r u b)) :
    height r u (minMaxWrapHeightParameter hknot u hdata x) = x := by
  let z : Icc (height r u a) (height r u b) := ⟨x, hx⟩
  have happly := (minMaxWrapHeightOrderIso hknot u hdata).apply_symm_apply z
  have hval := congrArg Subtype.val happly
  change height r u
      ((OrderDual.ofDual ((minMaxWrapHeightOrderIso hknot u hdata).symm z) :
        Icc b (a + period)) : ℝ) = x at hval
  simpa only [minMaxWrapHeightParameter, z,
    projIcc_of_mem hdata.height_endpoints_lt.le hx] using hval

theorem minMaxWrapHeightParameter_left {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    minMaxWrapHeightParameter hknot u hdata (height r u a) = a + period := by
  apply hdata.height_anti_wrap.injOn
    (minMaxWrapHeightParameter_mem hknot u hdata)
    (by
      constructor
      · linarith [hdata.left_mem.1, hdata.right_mem.2]
      · exact le_rfl)
  rw [height_minMaxWrapHeightParameter hknot u hdata
    ⟨le_rfl, hdata.height_endpoints_lt.le⟩]
  exact (periodic_height hknot u a).symm

theorem minMaxWrapHeightParameter_right {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    minMaxWrapHeightParameter hknot u hdata (height r u b) = b := by
  apply hdata.height_anti_wrap.injOn
    (minMaxWrapHeightParameter_mem hknot u hdata)
    (by
      constructor
      · exact le_rfl
      · linarith [hdata.left_mem.1, hdata.right_mem.2])
  rw [height_minMaxWrapHeightParameter hknot u hdata
    ⟨hdata.height_endpoints_lt.le, le_rfl⟩]

noncomputable def averagedDerivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (x y : ℝ) : E :=
  ∫ z in (0 : ℝ)..1, deriv f (x + z * (y - x))

theorem continuous_averagedDerivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E}
    (hf : ContDiff ℝ ⊤ f) :
    Continuous (fun p : ℝ × ℝ => averagedDerivative f p.1 p.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hderiv : Continuous (deriv f) :=
    hf.continuous_deriv (by simp)
  exact hderiv.comp (by fun_prop)

@[simp] theorem averagedDerivative_same {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (x : ℝ) :
    averagedDerivative f x x = deriv f x := by
  simp [averagedDerivative]

theorem averagedDerivative_eq_slope {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E}
    (hf : ContDiff ℝ ⊤ f) {x y : ℝ} (hxy : y ≠ x) :
    averagedDerivative f x y = slope f x y := by
  let φ : ℝ → E := fun z => f (x + z * (y - x))
  have harg : ContDiff ℝ ⊤ (fun z : ℝ => x + z * (y - x)) := by
    fun_prop
  have hφ : ContDiff ℝ ⊤ φ := hf.comp harg
  have hderiv : ∀ z : ℝ, deriv φ z =
      (y - x) • deriv f (x + z * (y - x)) := by
    intro z
    have hfAt : HasDerivAt f (deriv f (x + z * (y - x)))
        (x + z * (y - x)) :=
      ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
    have hargAt : HasDerivAt (fun w : ℝ => x + w * (y - x)) (y - x) z := by
      simpa using ((hasDerivAt_id z).mul_const (y - x)).const_add x
    exact (hfAt.scomp z hargAt).deriv
  have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    (hφ.of_le (by simp)).contDiffOn (by norm_num : (0 : ℝ) ≤ 1)
  simp_rw [hderiv] at hFTC
  rw [intervalIntegral.integral_smul] at hFTC
  have hsmul : (y - x) • averagedDerivative f x y = f y - f x := by
    simpa [averagedDerivative, φ] using hFTC
  rw [slope_def_module]
  calc
    averagedDerivative f x y =
        (y - x)⁻¹ • ((y - x) • averagedDerivative f x y) := by
      simp [sub_ne_zero.mpr hxy]
    _ = (y - x)⁻¹ • (f y - f x) := by rw [hsmul]

theorem deriv_curve_coordinate_of_contDiff {f : ℝ → Space}
    (hf : ContDiff ℝ ⊤ f) (i : Fin 3) (t : ℝ) :
    deriv (fun z => f z i) t = deriv f t i := by
  have hfAt : HasDerivAt f (deriv f t) t :=
    ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
  have hcomp := (spaceCoordinateCLM i).hasFDerivAt.comp_hasDerivAt t hfAt
  have hcoord : HasDerivAt (spaceCoordinateCLM i ∘ f) (deriv f t i) t := by
    simpa [spaceCoordinateCLM, ofLpContinuousLinearMap] using hcomp
  have hfun : (spaceCoordinateCLM i ∘ f) = fun z => f z i := by
    funext z
    simp [spaceCoordinateCLM, ofLpContinuousLinearMap]
  rw [hfun] at hcoord
  exact hcoord.deriv

theorem averagedDerivative_apply {f : ℝ → Space} (hf : ContDiff ℝ ⊤ f)
    (x y : ℝ) (i : Fin 3) :
    averagedDerivative f x y i =
      averagedDerivative (fun t => f t i) x y := by
  have hint : IntervalIntegrable
      (fun z => deriv f (x + z * (y - x))) volume (0 : ℝ) 1 :=
    ((hf.continuous_deriv (by simp)).comp (by fun_prop)).intervalIntegrable 0 1
  have hcomm := (spaceCoordinateCLM i).intervalIntegral_comp_comm hint
  rw [averagedDerivative, averagedDerivative]
  change spaceCoordinateCLM i
      (∫ z in (0 : ℝ)..1, deriv f (x + z * (y - x))) = _
  rw [← hcomm]
  apply intervalIntegral.integral_congr
  intro z _hz
  change deriv f (x + z * (y - x)) i =
    deriv (fun t => f t i) (x + z * (y - x))
  exact (deriv_curve_coordinate_of_contDiff hf i _).symm

theorem continuous_averagedDerivative_space {f : ℝ → Space}
    (hf : ContDiff ℝ ⊤ f) :
    Continuous (fun p : ℝ × ℝ => averagedDerivative f p.1 p.2) := by
  have hcoord (i : Fin 3) : ContDiff ℝ ⊤ (fun t => f t i) := by
    have h := (spaceCoordinateCLM i).contDiff.comp hf
    have hfun : (spaceCoordinateCLM i ∘ f) = fun t => f t i := by
      funext t
      simp [spaceCoordinateCLM, ofLpContinuousLinearMap]
    rwa [hfun] at h
  have hraw : Continuous (fun p : ℝ × ℝ =>
      fun i : Fin 3 => averagedDerivative (fun t => f t i) p.1 p.2) :=
    continuous_pi fun i => continuous_averagedDerivative (hcoord i)
  have hto : Continuous (fun p : ℝ × ℝ => toLp 2
      (fun i : Fin 3 => averagedDerivative (fun t => f t i) p.1 p.2)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp hraw
  convert hto using 1
  funext p
  ext i
  simpa using averagedDerivative_apply hf p.1 p.2 i

theorem minMaxHeightParameter_mem_Ioo {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Ioo (height r u a) (height r u b)) :
    minMaxHeightParameter hknot u hdata x ∈ Ioo a b := by
  have htmem := minMaxHeightParameter_mem hknot u hdata (x := x)
  have hh := height_minMaxHeightParameter hknot u hdata
    ⟨hx.1.le, hx.2.le⟩
  constructor
  · by_contra h
    have heq := le_antisymm (le_of_not_gt h) htmem.1
    rw [heq] at hh
    exact (ne_of_lt hx.1) hh
  · by_contra h
    have heq := le_antisymm htmem.2 (le_of_not_gt h)
    rw [heq] at hh
    exact (ne_of_lt hx.2) hh.symm

theorem minMaxWrapHeightParameter_mem_Ioo {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Ioo (height r u a) (height r u b)) :
    minMaxWrapHeightParameter hknot u hdata x ∈ Ioo b (a + period) := by
  have htmem := minMaxWrapHeightParameter_mem hknot u hdata (x := x)
  have hh := height_minMaxWrapHeightParameter hknot u hdata
    ⟨hx.1.le, hx.2.le⟩
  constructor
  · by_contra h
    have heq := le_antisymm (le_of_not_gt h) htmem.1
    rw [heq] at hh
    exact (ne_of_lt hx.2) hh.symm
  · by_contra h
    have heq := le_antisymm htmem.2 (le_of_not_gt h)
    rw [heq, periodic_height hknot u a] at hh
    exact (ne_of_lt hx.1) hh

theorem minMaxWrapHeightParameter_isForwardMate {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Ioo (height r u a) (height r u b)) :
    IsForwardHeightMate r u (minMaxHeightParameter hknot u hdata x)
      (minMaxWrapHeightParameter hknot u hdata x) := by
  let t := minMaxHeightParameter hknot u hdata x
  let y := minMaxWrapHeightParameter hknot u hdata x
  have ht : t ∈ Ioo a b := minMaxHeightParameter_mem_Ioo hknot u hdata hx
  have hy : y ∈ Ioo b (a + period) :=
    minMaxWrapHeightParameter_mem_Ioo hknot u hdata hx
  have hty : t < y := lt_trans ht.2 hy.1
  have hytP : y < t + period := by linarith [hy.2, ht.1]
  have hheight : height r u y = height r u t := by
    rw [height_minMaxWrapHeightParameter hknot u hdata
        ⟨hx.1.le, hx.2.le⟩,
      height_minMaxHeightParameter hknot u hdata
        ⟨hx.1.le, hx.2.le⟩]
  have htpos : 0 < directionalUnitTangent r u t := hdata.tangent_pos t ht
  have hyneg : directionalUnitTangent r u y < 0 := hdata.tangent_neg_wrap y hy
  exact ⟨⟨hty, hytP⟩, hheight, mul_neg_of_pos_of_neg htpos hyneg⟩

theorem forwardHeightMateMinMax_heightParameter {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Ioo (height r u a) (height r u b)) :
    forwardHeightMateMinMax hknot u hdata
        (minMaxHeightParameter hknot u hdata x) =
      minMaxWrapHeightParameter hknot u hdata x := by
  symm
  apply forwardHeightMateMinMax_unique hknot u hdata
  · exact ne_of_gt (hdata.tangent_pos _
      (minMaxHeightParameter_mem_Ioo hknot u hdata hx))
  · exact minMaxWrapHeightParameter_isForwardMate hknot u hdata hx

theorem averagedDerivative_ratio_eq_diffRatio {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f)
    (hg : ContDiff ℝ ⊤ g) {x y : ℝ} (hxy : y ≠ x)
    (hgxy : g y ≠ g x) :
    (averagedDerivative g x y)⁻¹ • averagedDerivative f x y =
      (g x - g y)⁻¹ • (f x - f y) := by
  rw [averagedDerivative_eq_slope hg hxy,
    averagedDerivative_eq_slope hf hxy]
  rw [slope_def_field, slope_def_module, smul_smul]
  have hxy' : y - x ≠ 0 := sub_ne_zero.mpr hxy
  have hgxy' : g y - g x ≠ 0 := sub_ne_zero.mpr hgxy
  have hgxy'' : g x - g y ≠ 0 := sub_ne_zero.mpr hgxy.symm
  have hcoef : ((g y - g x) / (y - x))⁻¹ * (y - x)⁻¹ =
      -(g x - g y)⁻¹ := by
    field_simp [hxy', hgxy', hgxy'']
    ring
  rw [hcoef, neg_smul]
  module

noncomputable def minMaxLowerChordDirection {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (x : ℝ) : Space :=
  let t := minMaxHeightParameter hknot u hdata x
  let y := minMaxWrapHeightParameter hknot u hdata x - period
  (averagedDerivative (directionalUnitTangent r u) t y)⁻¹ •
    averagedDerivative r t y

noncomputable def minMaxUpperChordDirection {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (x : ℝ) : Space :=
  let t := minMaxHeightParameter hknot u hdata x
  let y := minMaxWrapHeightParameter hknot u hdata x
  (averagedDerivative (directionalUnitTangent r u) t y)⁻¹ •
    averagedDerivative r t y

theorem minMaxLowerChordDirection_left {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    minMaxLowerChordDirection hknot u hdata (height r u a) =
      minMaxLeftDirection u hdata := by
  rw [minMaxLowerChordDirection,
    minMaxHeightParameter_height hknot u hdata
      ⟨le_rfl, hdata.left_lt_right.le⟩,
    minMaxWrapHeightParameter_left hknot u hdata]
  simp [minMaxLeftDirection, velocity]

theorem minMaxUpperChordDirection_right {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    minMaxUpperChordDirection hknot u hdata (height r u b) =
      minMaxRightDirection u hdata := by
  rw [minMaxUpperChordDirection,
    minMaxHeightParameter_height hknot u hdata
      ⟨hdata.left_lt_right.le, le_rfl⟩,
    minMaxWrapHeightParameter_right hknot u hdata]
  simp [minMaxRightDirection, velocity]

theorem minMaxUpperChordDirection_eq_central {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Ioo (height r u a) (height r u b)) :
    minMaxUpperChordDirection hknot u hdata x =
      centralMateDirectionMinMax hknot u hdata x := by
  let t := minMaxHeightParameter hknot u hdata x
  let y := minMaxWrapHeightParameter hknot u hdata x
  have ht : t ∈ Ioo a b := minMaxHeightParameter_mem_Ioo hknot u hdata hx
  have hy : y ∈ Ioo b (a + period) :=
    minMaxWrapHeightParameter_mem_Ioo hknot u hdata hx
  have hgyt : directionalUnitTangent r u y ≠
      directionalUnitTangent r u t := by
    have htpos := hdata.tangent_pos t ht
    have hyneg := hdata.tangent_neg_wrap y hy
    linarith
  have hyt : y ≠ t := by
    intro h
    exact hgyt (congrArg (directionalUnitTangent r u) h)
  rw [minMaxUpperChordDirection]
  change (averagedDerivative (directionalUnitTangent r u) t y)⁻¹ •
      averagedDerivative r t y = _
  rw [averagedDerivative_ratio_eq_diffRatio hknot.smooth
    (contDiff_directionalUnitTangent hknot u) hyt hgyt]
  rw [centralMateDirectionMinMax, mateDirectionMinMax,
    forwardHeightMateMinMax_heightParameter hknot u hdata hx]

theorem minMaxLowerChordDirection_eq_central {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Ioo (height r u a) (height r u b)) :
    minMaxLowerChordDirection hknot u hdata x =
      centralMateDirectionMinMax hknot u hdata x := by
  let t := minMaxHeightParameter hknot u hdata x
  let y := minMaxWrapHeightParameter hknot u hdata x
  let y' := y - period
  have ht : t ∈ Ioo a b := minMaxHeightParameter_mem_Ioo hknot u hdata hx
  have hy : y ∈ Ioo b (a + period) :=
    minMaxWrapHeightParameter_mem_Ioo hknot u hdata hx
  have hgy : directionalUnitTangent r u y' =
      directionalUnitTangent r u y := by
    have hper := (periodic_directionalUnitTangent hknot u) y'
    simpa [y', sub_add_cancel] using hper.symm
  have hry : r y' = r y := by
    have hper := hknot.periodic y'
    simpa [y', sub_add_cancel] using hper.symm
  have hgyt : directionalUnitTangent r u y' ≠
      directionalUnitTangent r u t := by
    rw [hgy]
    have htpos := hdata.tangent_pos t ht
    have hyneg := hdata.tangent_neg_wrap y hy
    linarith
  have hy't : y' ≠ t := by
    intro h
    exact hgyt (congrArg (directionalUnitTangent r u) h)
  rw [minMaxLowerChordDirection]
  change (averagedDerivative (directionalUnitTangent r u) t y')⁻¹ •
      averagedDerivative r t y' = _
  rw [averagedDerivative_ratio_eq_diffRatio hknot.smooth
    (contDiff_directionalUnitTangent hknot u) hy't hgyt]
  rw [hgy, hry, centralMateDirectionMinMax, mateDirectionMinMax,
    forwardHeightMateMinMax_heightParameter hknot u hdata hx]

theorem left_lt_bridgeHeightMidpoint {low high : ℝ} (hlh : low < high) :
    low < bridgeHeightMidpoint low high := by
  unfold bridgeHeightMidpoint
  linarith

theorem bridgeHeightMidpoint_lt_right {low high : ℝ} (hlh : low < high) :
    bridgeHeightMidpoint low high < high := by
  unfold bridgeHeightMidpoint
  linarith

theorem averagedDerivative_lower_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Icc (height r u a) (height r u b) ∩
      Iic (bridgeHeightMidpoint (height r u a) (height r u b))) :
    averagedDerivative (directionalUnitTangent r u)
        (minMaxHeightParameter hknot u hdata x)
        (minMaxWrapHeightParameter hknot u hdata x - period) ≠ 0 := by
  by_cases hxl : x = height r u a
  · subst x
    rw [minMaxHeightParameter_height hknot u hdata
        ⟨le_rfl, hdata.left_lt_right.le⟩,
      minMaxWrapHeightParameter_left hknot u hdata]
    simpa using hdata.tangent_deriv_left.ne'
  · have hxgt : height r u a < x := lt_of_le_of_ne hx.1.1 (Ne.symm hxl)
    have hxlt : x < height r u b := lt_of_le_of_lt hx.2
      (bridgeHeightMidpoint_lt_right hdata.height_endpoints_lt)
    have hxIoo : x ∈ Ioo (height r u a) (height r u b) := ⟨hxgt, hxlt⟩
    let t := minMaxHeightParameter hknot u hdata x
    let y := minMaxWrapHeightParameter hknot u hdata x
    let y' := y - period
    have ht : t ∈ Ioo a b := minMaxHeightParameter_mem_Ioo hknot u hdata hxIoo
    have hy : y ∈ Ioo b (a + period) :=
      minMaxWrapHeightParameter_mem_Ioo hknot u hdata hxIoo
    have hgy : directionalUnitTangent r u y' =
        directionalUnitTangent r u y := by
      have hper := (periodic_directionalUnitTangent hknot u) y'
      simpa [y', sub_add_cancel] using hper.symm
    have hgyt : directionalUnitTangent r u y' ≠
        directionalUnitTangent r u t := by
      rw [hgy]
      have htpos := hdata.tangent_pos t ht
      have hyneg := hdata.tangent_neg_wrap y hy
      linarith
    have hy't : y' ≠ t := by
      intro h
      exact hgyt (congrArg (directionalUnitTangent r u) h)
    rw [averagedDerivative_eq_slope
      (contDiff_directionalUnitTangent hknot u) hy't, slope_def_field]
    exact div_ne_zero (sub_ne_zero.mpr hgyt) (sub_ne_zero.mpr hy't)

theorem averagedDerivative_upper_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Icc (height r u a) (height r u b) ∩
      Ici (bridgeHeightMidpoint (height r u a) (height r u b))) :
    averagedDerivative (directionalUnitTangent r u)
        (minMaxHeightParameter hknot u hdata x)
        (minMaxWrapHeightParameter hknot u hdata x) ≠ 0 := by
  by_cases hxr : x = height r u b
  · subst x
    rw [minMaxHeightParameter_height hknot u hdata
        ⟨hdata.left_lt_right.le, le_rfl⟩,
      minMaxWrapHeightParameter_right hknot u hdata]
    simpa using hdata.tangent_deriv_right.ne
  · have hxlt : x < height r u b := lt_of_le_of_ne hx.1.2 hxr
    have hxgt : height r u a < x :=
      (left_lt_bridgeHeightMidpoint hdata.height_endpoints_lt).trans_le hx.2
    have hxIoo : x ∈ Ioo (height r u a) (height r u b) := ⟨hxgt, hxlt⟩
    let t := minMaxHeightParameter hknot u hdata x
    let y := minMaxWrapHeightParameter hknot u hdata x
    have ht : t ∈ Ioo a b := minMaxHeightParameter_mem_Ioo hknot u hdata hxIoo
    have hy : y ∈ Ioo b (a + period) :=
      minMaxWrapHeightParameter_mem_Ioo hknot u hdata hxIoo
    have hgyt : directionalUnitTangent r u y ≠
        directionalUnitTangent r u t := by
      have htpos := hdata.tangent_pos t ht
      have hyneg := hdata.tangent_neg_wrap y hy
      linarith
    have hyt : y ≠ t := by
      intro h
      exact hgyt (congrArg (directionalUnitTangent r u) h)
    rw [averagedDerivative_eq_slope
      (contDiff_directionalUnitTangent hknot u) hyt, slope_def_field]
    exact div_ne_zero (sub_ne_zero.mpr hgyt) (sub_ne_zero.mpr hyt)

theorem continuousOn_minMaxLowerChordDirection {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    ContinuousOn (minMaxLowerChordDirection hknot u hdata)
      (Icc (height r u a) (height r u b) ∩
        Iic (bridgeHeightMidpoint (height r u a) (height r u b))) := by
  let t := minMaxHeightParameter hknot u hdata
  let y := fun x => minMaxWrapHeightParameter hknot u hdata x - period
  have ht : Continuous t := continuous_minMaxHeightParameter hknot u hdata
  have hy : Continuous y :=
    (continuous_minMaxWrapHeightParameter hknot u hdata).sub continuous_const
  have hg := (continuous_averagedDerivative
      (contDiff_directionalUnitTangent hknot u)).comp (ht.prodMk hy)
  have hr := (continuous_averagedDerivative_space hknot.smooth).comp (ht.prodMk hy)
  change ContinuousOn (fun x =>
      (averagedDerivative (directionalUnitTangent r u)
        (minMaxHeightParameter hknot u hdata x)
        (minMaxWrapHeightParameter hknot u hdata x - period))⁻¹ •
      averagedDerivative r (minMaxHeightParameter hknot u hdata x)
        (minMaxWrapHeightParameter hknot u hdata x - period)) _
  exact (hg.continuousOn.inv₀ (fun x hx =>
    averagedDerivative_lower_ne_zero hknot u hdata hx)).smul hr.continuousOn

theorem continuousOn_minMaxUpperChordDirection {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    ContinuousOn (minMaxUpperChordDirection hknot u hdata)
      (Icc (height r u a) (height r u b) ∩
        Ici (bridgeHeightMidpoint (height r u a) (height r u b))) := by
  let t := minMaxHeightParameter hknot u hdata
  let y := minMaxWrapHeightParameter hknot u hdata
  have ht : Continuous t := continuous_minMaxHeightParameter hknot u hdata
  have hy : Continuous y := continuous_minMaxWrapHeightParameter hknot u hdata
  have hg := (continuous_averagedDerivative
      (contDiff_directionalUnitTangent hknot u)).comp (ht.prodMk hy)
  have hr := (continuous_averagedDerivative_space hknot.smooth).comp (ht.prodMk hy)
  change ContinuousOn (fun x =>
      (averagedDerivative (directionalUnitTangent r u)
        (minMaxHeightParameter hknot u hdata x)
        (minMaxWrapHeightParameter hknot u hdata x))⁻¹ •
      averagedDerivative r (minMaxHeightParameter hknot u hdata x)
        (minMaxWrapHeightParameter hknot u hdata x)) _
  exact (hg.continuousOn.inv₀ (fun x hx =>
    averagedDerivative_upper_ne_zero hknot u hdata hx)).smul hr.continuousOn

noncomputable def extendedMateDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (x : ℝ) : Space :=
  if x ≤ bridgeHeightMidpoint (height r u a) (height r u b) then
    minMaxLowerChordDirection hknot u hdata x
  else
    minMaxUpperChordDirection hknot u hdata x

theorem extendedMateDirectionMinMax_eq_central {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Ioo (height r u a) (height r u b)) :
    extendedMateDirectionMinMax hknot u hdata x =
      centralMateDirectionMinMax hknot u hdata x := by
  rw [extendedMateDirectionMinMax]
  split
  · exact minMaxLowerChordDirection_eq_central hknot u hdata hx
  · exact minMaxUpperChordDirection_eq_central hknot u hdata hx

theorem continuousOn_extendedMateDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    ContinuousOn (extendedMateDirectionMinMax hknot u hdata)
      (Icc (height r u a) (height r u b)) := by
  let m := bridgeHeightMidpoint (height r u a) (height r u b)
  apply ContinuousOn.if
  · intro x hx
    have hxmid : x = m := by
      have hfront := hx.2
      change x ∈ frontier (Iic m) at hfront
      exact mem_singleton_iff.mp (frontier_Iic_subset m hfront)
    subst x
    have hm : m ∈ Ioo (height r u a) (height r u b) :=
      ⟨left_lt_bridgeHeightMidpoint hdata.height_endpoints_lt,
        bridgeHeightMidpoint_lt_right hdata.height_endpoints_lt⟩
    rw [minMaxLowerChordDirection_eq_central hknot u hdata hm,
      minMaxUpperChordDirection_eq_central hknot u hdata hm]
  · change ContinuousOn (minMaxLowerChordDirection hknot u hdata)
      (Icc (height r u a) (height r u b) ∩ closure (Iic m))
    rw [closure_Iic]
    simpa [m] using continuousOn_minMaxLowerChordDirection hknot u hdata
  · have hclosure : closure {x : ℝ | ¬x ≤ m} = Ici m := by
      rw [show {x : ℝ | ¬x ≤ m} = Ioi m by ext; simp]
      exact closure_Ioi m
    rw [hclosure]
    simpa [m] using continuousOn_minMaxUpperChordDirection hknot u hdata

theorem extendedMateDirectionMinMax_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Icc (height r u a) (height r u b)) :
    extendedMateDirectionMinMax hknot u hdata x ≠ 0 := by
  rcases eq_or_ne x (height r u a) with hxl | hxl
  · subst x
    rw [extendedMateDirectionMinMax, if_pos
      (left_lt_bridgeHeightMidpoint hdata.height_endpoints_lt).le,
      minMaxLowerChordDirection_left]
    exact minMaxLeftDirection_ne_zero hknot u hdata
  rcases eq_or_ne x (height r u b) with hxr | hxr
  · subst x
    rw [extendedMateDirectionMinMax, if_neg
      (not_le.mpr (bridgeHeightMidpoint_lt_right hdata.height_endpoints_lt)),
      minMaxUpperChordDirection_right]
    exact minMaxRightDirection_ne_zero hknot u hdata
  · have hxIoo : x ∈ Ioo (height r u a) (height r u b) :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxl), lt_of_le_of_ne hx.2 hxr⟩
    rw [extendedMateDirectionMinMax_eq_central hknot u hdata hxIoo]
    exact centralMateDirectionMinMax_ne_zero hknot u hdata hxIoo

theorem inner_extendedMateDirectionMinMax_eq_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Icc (height r u a) (height r u b)) :
    inner ℝ u (extendedMateDirectionMinMax hknot u hdata x) = 0 := by
  rcases eq_or_ne x (height r u a) with hxl | hxl
  · subst x
    rw [extendedMateDirectionMinMax, if_pos
      (left_lt_bridgeHeightMidpoint hdata.height_endpoints_lt).le,
      minMaxLowerChordDirection_left]
    exact inner_unit_minMaxLeftDirection_eq_zero hknot hdata
  rcases eq_or_ne x (height r u b) with hxr | hxr
  · subst x
    rw [extendedMateDirectionMinMax, if_neg
      (not_le.mpr (bridgeHeightMidpoint_lt_right hdata.height_endpoints_lt)),
      minMaxUpperChordDirection_right]
    exact inner_unit_minMaxRightDirection_eq_zero hknot hdata
  · have hxIoo : x ∈ Ioo (height r u a) (height r u b) :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxl), lt_of_le_of_ne hx.2 hxr⟩
    rw [extendedMateDirectionMinMax_eq_central hknot u hdata hxIoo]
    exact inner_centralMateDirectionMinMax_eq_zero hknot u hdata hxIoo

noncomputable def projectedExtendedMateDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (x : ℝ) : Space :=
  extendedMateDirectionMinMax hknot u hdata
    (projIcc (height r u a) (height r u b)
      hdata.height_endpoints_lt.le x)

theorem continuous_projectedExtendedMateDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    Continuous (projectedExtendedMateDirectionMinMax hknot u hdata) := by
  let p : ℝ → Icc (height r u a) (height r u b) :=
    projIcc (height r u a) (height r u b) hdata.height_endpoints_lt.le
  have hp : Continuous (fun x => (p x : ℝ)) :=
    continuous_subtype_val.comp continuous_projIcc
  have hcomp := (continuousOn_extendedMateDirectionMinMax hknot u hdata).comp_continuous
    hp fun x => (p x).property
  convert hcomp using 1
  funext x
  rfl

theorem projectedExtendedMateDirectionMinMax_eq {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b x : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hx : x ∈ Icc (height r u a) (height r u b)) :
    projectedExtendedMateDirectionMinMax hknot u hdata x =
      extendedMateDirectionMinMax hknot u hdata x := by
  simp [projectedExtendedMateDirectionMinMax,
    projIcc_of_mem hdata.height_endpoints_lt.le hx]

@[simp] theorem bridgeHeightContraction_one (low high x : ℝ) :
    bridgeHeightContraction low high 1 x = x := by
  unfold bridgeHeightContraction bridgeHeightMidpoint
  ring

theorem exists_uniform_positive_contractedMateDirectionMinMax
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      ∀ x ∈ Icc (height r u a) (height r u b),
        0 < inner ℝ (extendedMateDirectionMinMax hknot u hdata x)
          (contractedMateDirectionMinMax hknot u hdata k x) := by
  let low := height r u a
  let high := height r u b
  let D := projectedExtendedMateDirectionMinMax hknot u hdata
  let F : ℝ × ℝ → ℝ := fun p =>
    inner ℝ (D p.2) (D (bridgeHeightContraction low high p.1 p.2))
  have hD : Continuous D :=
    continuous_projectedExtendedMateDirectionMinMax hknot u hdata
  have hC : Continuous (fun p : ℝ × ℝ =>
      bridgeHeightContraction low high p.1 p.2) := by
    unfold bridgeHeightContraction bridgeHeightMidpoint
    fun_prop
  have hF : Continuous F := by
    exact (hD.comp continuous_snd).inner (hD.comp hC)
  have hev : ∀ᶠ k in 𝓝 (1 : ℝ),
      ∀ x ∈ Icc low high, 0 < F (k, x) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro x hx
    have hDne : D x ≠ 0 := by
      rw [show D x = extendedMateDirectionMinMax hknot u hdata x by
        exact projectedExtendedMateDirectionMinMax_eq hknot u hdata hx]
      exact extendedMateDirectionMinMax_ne_zero hknot u hdata hx
    have hpos : 0 < F (1, x) := by
      simpa [F, bridgeHeightContraction_one] using real_inner_self_pos.mpr hDne
    exact hF.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
  have hcl : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact right_mem_Icc.mpr zero_le_one
  have hinter := (mem_closure_iff_nhds.mp hcl)
    {k : ℝ | ∀ x ∈ Icc low high, 0 < F (k, x)} hev
  obtain ⟨k, hkpos, hkIoo⟩ := hinter
  refine ⟨k, hkIoo.1.le, hkIoo.2, ?_⟩
  intro x hx
  have hx' : x ∈ Icc low high := by simpa [low, high] using hx
  have hpos := hkpos x hx'
  have hcontract : bridgeHeightContraction low high k x ∈ Ioo low high :=
    bridgeHeightContraction_mem_Ioo hdata.height_endpoints_lt hkIoo.1.le
      hkIoo.2 hx
  change 0 < inner ℝ (D x)
    (D (bridgeHeightContraction low high k x)) at hpos
  rw [show D x = extendedMateDirectionMinMax hknot u hdata x by
      exact projectedExtendedMateDirectionMinMax_eq hknot u hdata hx] at hpos
  rw [show D (bridgeHeightContraction low high k x) =
      extendedMateDirectionMinMax hknot u hdata
        (bridgeHeightContraction low high k x) by
      exact projectedExtendedMateDirectionMinMax_eq hknot u hdata
        ⟨hcontract.1.le, hcontract.2.le⟩] at hpos
  rw [extendedMateDirectionMinMax_eq_central hknot u hdata hcontract] at hpos
  simpa [F, D, low, high, contractedMateDirectionMinMax] using hpos

end Submission.Helpers
