import Submission.BridgeCenter

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

theorem strictAntiOn_le_of_le {f : ℝ → ℝ} {s : Set ℝ} {x y : ℝ}
    (hf : StrictAntiOn f s) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≤ y) :
    f y ≤ f x := by
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (hf hx hy hlt).le

theorem height_mem_Icc_minMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    height r u t ∈ Icc (height r u a) (height r u b) := by
  have hp : 0 < period := by simp [period, Real.pi_pos]
  obtain ⟨m, hm, _hmuniq⟩ := existsUnique_add_zsmul_mem_Ico hp t a
  let z : ℝ := t + m • period
  have hz : z ∈ Ico a (a + period) := by simpa [z] using hm
  have hshift : height r u z = height r u t := by
    have hper := (periodic_height hknot u).sub_zsmul_eq (x := t) (-m)
    simpa [z, sub_neg_eq_add] using hper
  rw [← hshift]
  by_cases hzb : z ≤ b
  · have hzab : z ∈ Icc a b := ⟨hz.1, hzb⟩
    exact ⟨strictMonoOn_le_of_le hdata.height_mono
        ⟨le_rfl, hdata.left_lt_right.le⟩ hzab hzab.1,
      strictMonoOn_le_of_le hdata.height_mono hzab
        ⟨hdata.left_lt_right.le, le_rfl⟩ hzab.2⟩
  · have hbz : b ≤ z := (lt_of_not_ge hzb).le
    have hzwrap : z ∈ Icc b (a + period) := ⟨hbz, hz.2.le⟩
    have haP : a + period ∈ Icc b (a + period) := by
      constructor
      · linarith [hdata.right_mem.2, hdata.left_mem.1]
      · exact le_rfl
    have hbmem : b ∈ Icc b (a + period) := by
      constructor
      · exact le_rfl
      · linarith [hdata.right_mem.2, hdata.left_mem.1]
    have hlower := strictAntiOn_le_of_le hdata.height_anti_wrap hzwrap haP hz.2.le
    have hupper := strictAntiOn_le_of_le hdata.height_anti_wrap hbmem hzwrap hbz
    rw [periodic_height hknot u a] at hlower
    exact ⟨hlower, hupper⟩

theorem deriv_directionalUnitTangent_ne_zero_of_minMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hzero : directionalUnitTangent r u t = 0) :
    deriv (directionalUnitTangent r u) t ≠ 0 := by
  have hp : 0 < period := by simp [period, Real.pi_pos]
  obtain ⟨m, hm, _hmuniq⟩ := existsUnique_add_zsmul_mem_Ico hp t a
  let z : ℝ := t + m • period
  have hz : z ∈ Ico a (a + period) := by simpa [z] using hm
  have hgshift : directionalUnitTangent r u z =
      directionalUnitTangent r u t := by
    have hper := (periodic_directionalUnitTangent hknot u).sub_zsmul_eq
      (x := t) (-m)
    simpa [z, sub_neg_eq_add] using hper
  have hdshift : deriv (directionalUnitTangent r u) z =
      deriv (directionalUnitTangent r u) t := by
    have hper := (periodic_deriv_directionalUnitTangent hknot u).sub_zsmul_eq
      (x := t) (-m)
    simpa [z, sub_neg_eq_add] using hper
  have hgz : directionalUnitTangent r u z = 0 := hgshift.trans hzero
  have hz_cases : z = a ∨ z = b := by
    by_cases hzb : z ≤ b
    · by_cases hza : z = a
      · exact Or.inl hza
      · by_cases hzbeq : z = b
        · exact Or.inr hzbeq
        · have hza_lt : a < z := lt_of_le_of_ne hz.1 (Ne.symm hza)
          have hzb_lt : z < b := lt_of_le_of_ne hzb hzbeq
          have hpos := hdata.tangent_pos z ⟨hza_lt, hzb_lt⟩
          rw [hgz] at hpos
          linarith
    · have hbz : b < z := lt_of_not_ge hzb
      have hneg := hdata.tangent_neg_wrap z ⟨hbz, hz.2⟩
      rw [hgz] at hneg
      linarith
  rcases hz_cases with rfl | rfl
  · rw [← hdshift]
    exact hdata.tangent_deriv_left.ne'
  · rw [← hdshift]
    exact hdata.tangent_deriv_right.ne

theorem injOn_planarBridgeCurve_of_minMaxData {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    Set.InjOn (planarBridgeCurve r u) (Ico (0 : ℝ) period) := by
  intro x hx y hy hxy
  let x' := periodLift a x
  let y' := periodLift a y
  have hx' : x' ∈ Ico a (a + period) :=
    periodLift_mem_Ico hdata.left_mem hx
  have hy' : y' ∈ Ico a (a + period) :=
    periodLift_mem_Ico hdata.left_mem hy
  have hxy' : planarBridgeCurve r u x' = planarBridgeCurve r u y' := by
    calc
      planarBridgeCurve r u x' = planarBridgeCurve r u x :=
        planarBridgeCurve_periodLift hknot u
      _ = planarBridgeCurve r u y := hxy
      _ = planarBridgeCurve r u y' :=
        (planarBridgeCurve_periodLift hknot u).symm
  have hheight : height r u x' = height r u y' := by
    have h := congrArg (fun v : Space => v 0) hxy'
    simpa [planarBridgeCurve] using h
  have hdir : directionalUnitTangent r u x' =
      directionalUnitTangent r u y' := by
    have h := congrArg (fun v : Space => v 1) hxy'
    simpa [planarBridgeCurve] using h
  by_cases hxsplit : x' ≤ b
  · by_cases hysplit : y' ≤ b
    · have hxeq : x' = y' := hdata.height_mono.injOn
        ⟨hx'.1, hxsplit⟩ ⟨hy'.1, hysplit⟩ hheight
      exact periodLift_injective_on_Ico hdata.left_mem hx hy hxeq
    · have hygt : b < y' := lt_of_not_ge hysplit
      have hygNeg : directionalUnitTangent r u y' < 0 :=
        hdata.tangent_neg_wrap y' ⟨hygt, hy'.2⟩
      have hxgNonneg : 0 ≤ directionalUnitTangent r u x' := by
        rcases eq_or_lt_of_le hx'.1 with hxa | hxa
        · rw [← hxa, hdata.tangent_left]
        · rcases eq_or_lt_of_le hxsplit with hxb | hxb
          · rw [hxb, hdata.tangent_right]
          · exact (hdata.tangent_pos x' ⟨hxa, hxb⟩).le
      linarith
  · have hxgt : b < x' := lt_of_not_ge hxsplit
    by_cases hysplit : y' ≤ b
    · have hxgNeg : directionalUnitTangent r u x' < 0 :=
        hdata.tangent_neg_wrap x' ⟨hxgt, hx'.2⟩
      have hygNonneg : 0 ≤ directionalUnitTangent r u y' := by
        rcases eq_or_lt_of_le hy'.1 with hya | hya
        · rw [← hya, hdata.tangent_left]
        · rcases eq_or_lt_of_le hysplit with hyb | hyb
          · rw [hyb, hdata.tangent_right]
          · exact (hdata.tangent_pos y' ⟨hya, hyb⟩).le
      linarith
    · have hxeq : x' = y' := hdata.height_anti_wrap.injOn
        ⟨hxgt.le, hx'.2.le⟩ ⟨(lt_of_not_ge hysplit).le, hy'.2.le⟩ hheight
      exact periodLift_injective_on_Ico hdata.left_mem hx hy hxeq

noncomputable def minMaxLeftDirection {r : ℝ → Space}
    (u : Space) {a b : ℝ} (_hdata : MinMaxBridgeData r u a b) : Space :=
  (deriv (directionalUnitTangent r u) a)⁻¹ • velocity r a

noncomputable def minMaxRightDirection {r : ℝ → Space}
    (u : Space) {a b : ℝ} (_hdata : MinMaxBridgeData r u a b) : Space :=
  (deriv (directionalUnitTangent r u) b)⁻¹ • velocity r b

theorem minMaxLeftDirection_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    minMaxLeftDirection u hdata ≠ 0 := by
  exact smul_ne_zero (inv_ne_zero hdata.tangent_deriv_left.ne')
    (hknot.regular a)

theorem minMaxRightDirection_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    minMaxRightDirection u hdata ≠ 0 := by
  exact smul_ne_zero (inv_ne_zero hdata.tangent_deriv_right.ne)
    (hknot.regular b)

theorem inner_minMaxLeftDirection_self_pos {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    0 < inner ℝ (minMaxLeftDirection u hdata)
      (minMaxLeftDirection u hdata) := by
  exact real_inner_self_pos.mpr (minMaxLeftDirection_ne_zero hknot u hdata)

theorem inner_minMaxRightDirection_self_pos {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    0 < inner ℝ (minMaxRightDirection u hdata)
      (minMaxRightDirection u hdata) := by
  exact real_inner_self_pos.mpr (minMaxRightDirection_ne_zero hknot u hdata)

theorem inner_unit_minMaxLeftDirection_eq_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    inner ℝ u (minMaxLeftDirection u hdata) = 0 := by
  rw [minMaxLeftDirection, real_inner_smul_right,
    ← (hasDerivAt_height hknot u a).deriv,
    deriv_height_eq_speed_mul_directionalUnitTangent hknot u a,
    hdata.tangent_left]
  simp

theorem inner_unit_minMaxRightDirection_eq_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    inner ℝ u (minMaxRightDirection u hdata) = 0 := by
  rw [minMaxRightDirection, real_inner_smul_right,
    ← (hasDerivAt_height hknot u b).deriv,
    deriv_height_eq_speed_mul_directionalUnitTangent hknot u b,
    hdata.tangent_right]
  simp

noncomputable def bridgeHeightMidpoint (low high : ℝ) : ℝ :=
  (low + high) / 2

noncomputable def bridgeHeightContraction
    (low high k x : ℝ) : ℝ :=
  bridgeHeightMidpoint low high +
    k * (x - bridgeHeightMidpoint low high)

theorem bridgeHeightContraction_mem_Ioo {low high k x : ℝ}
    (hlh : low < high) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hx : x ∈ Icc low high) :
    bridgeHeightContraction low high k x ∈ Ioo low high := by
  have hspan : 0 < high - low := sub_pos.mpr hlh
  have hkspan : 0 < (1 - k) * (high - low) :=
    mul_pos (sub_pos.mpr hk1) hspan
  have hleft : low - bridgeHeightMidpoint low high ≤
      x - bridgeHeightMidpoint low high := sub_le_sub_right hx.1 _
  have hright : x - bridgeHeightMidpoint low high ≤
      high - bridgeHeightMidpoint low high := sub_le_sub_right hx.2 _
  constructor <;>
    dsimp [bridgeHeightContraction, bridgeHeightMidpoint] at * <;>
    nlinarith [mul_le_mul_of_nonneg_left hleft hk0,
      mul_le_mul_of_nonneg_left hright hk0]

theorem contDiff_bridgeHeightContraction (low high k : ℝ) :
    ContDiff ℝ ⊤ (bridgeHeightContraction low high k) := by
  unfold bridgeHeightContraction
  fun_prop

noncomputable def contractedMateDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (k x : ℝ) : Space :=
  centralMateDirectionMinMax hknot u hdata
    (bridgeHeightContraction (height r u a) (height r u b) k x)

theorem contDiffAt_contractedMateDirectionMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k x : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hx : x ∈ Icc (height r u a) (height r u b)) :
    ContDiffAt ℝ ⊤ (contractedMateDirectionMinMax hknot u hdata k) x := by
  have hinner := bridgeHeightContraction_mem_Ioo hdata.height_endpoints_lt
    hk0 hk1 hx
  exact (contDiffAt_centralMateDirectionMinMax hknot u hdata hinner).comp x
    (contDiff_bridgeHeightContraction _ _ k).contDiffAt

theorem contractedMateDirectionMinMax_ne_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k x : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hx : x ∈ Icc (height r u a) (height r u b)) :
    contractedMateDirectionMinMax hknot u hdata k x ≠ 0 := by
  exact centralMateDirectionMinMax_ne_zero hknot u hdata
    (bridgeHeightContraction_mem_Ioo hdata.height_endpoints_lt hk0 hk1 hx)

theorem inner_contractedMateDirectionMinMax_eq_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k x : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hx : x ∈ Icc (height r u a) (height r u b)) :
    inner ℝ u (contractedMateDirectionMinMax hknot u hdata k x) = 0 := by
  exact inner_centralMateDirectionMinMax_eq_zero hknot u hdata
    (bridgeHeightContraction_mem_Ioo hdata.height_endpoints_lt hk0 hk1 hx)

noncomputable def contractedBridgeCurveMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (k t : ℝ) : Space :=
  height r u t • u + directionalUnitTangent r u t •
    contractedMateDirectionMinMax hknot u hdata k (height r u t)

theorem inner_contractedBridgeCurveMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b k t : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    inner ℝ u (contractedBridgeCurveMinMax hknot u hdata k t) =
      height r u t := by
  rw [contractedBridgeCurveMinMax, inner_add_right,
    real_inner_smul_right, real_inner_smul_right,
    inner_contractedMateDirectionMinMax_eq_zero hknot u hdata hk0 hk1
      (height_mem_Icc_minMax hknot u hdata)]
  rw [real_inner_self_eq_norm_sq, hu]
  norm_num

theorem contDiff_contractedBridgeCurveMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ContDiff ℝ ⊤ (contractedBridgeCurveMinMax hknot u hdata k) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hx := height_mem_Icc_minMax hknot u hdata (t := t)
  have hdir : ContDiffAt ℝ ⊤ (fun z =>
      contractedMateDirectionMinMax hknot u hdata k (height r u z)) t :=
    (contDiffAt_contractedMateDirectionMinMax hknot u hdata hk0 hk1 hx).comp t
      (contDiff_height hknot u).contDiffAt
  exact ((contDiff_height hknot u).contDiffAt.smul
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => u)).contDiffAt).add
    ((contDiff_directionalUnitTangent hknot u).contDiffAt.smul hdir)

theorem periodic_contractedBridgeCurveMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    Function.Periodic (contractedBridgeCurveMinMax hknot u hdata k) period := by
  intro t
  simp only [contractedBridgeCurveMinMax]
  rw [periodic_height hknot u t, periodic_directionalUnitTangent hknot u t]

theorem injOn_contractedBridgeCurveMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b k : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    Set.InjOn (contractedBridgeCurveMinMax hknot u hdata k)
      (Ico (0 : ℝ) period) := by
  intro x hx y hy hxy
  have hheight : height r u x = height r u y := by
    have h := congrArg (fun v : Space => inner ℝ u v) hxy
    simpa only [inner_contractedBridgeCurveMinMax hknot hu hdata hk0 hk1] using h
  let d := contractedMateDirectionMinMax hknot u hdata k (height r u x)
  have hd : d ≠ 0 := by
    exact contractedMateDirectionMinMax_ne_zero hknot u hdata hk0 hk1
      (height_mem_Icc_minMax hknot u hdata)
  have hscaled : directionalUnitTangent r u x • d =
      directionalUnitTangent r u y • d := by
    have hxy' := hxy
    rw [contractedBridgeCurveMinMax, contractedBridgeCurveMinMax,
      hheight] at hxy'
    have hdEq : contractedMateDirectionMinMax hknot u hdata k (height r u y) = d := by
      simp [d, hheight]
    rw [hdEq] at hxy'
    change height r u y • u + directionalUnitTangent r u x • d =
      height r u y • u + directionalUnitTangent r u y • d at hxy'
    exact add_left_cancel hxy'
  have hdir : directionalUnitTangent r u x =
      directionalUnitTangent r u y := by
    have hzero : (directionalUnitTangent r u x -
        directionalUnitTangent r u y) • d = 0 := by
      rw [sub_smul, hscaled, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact (hd h).elim
  apply injOn_planarBridgeCurve_of_minMaxData hknot u hdata hx hy
  ext i
  fin_cases i
  · simp [planarBridgeCurve, hheight]
  · simp [planarBridgeCurve, hdir]
  · simp [planarBridgeCurve]

theorem regular_contractedBridgeCurveMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b k : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ∀ t, velocity (contractedBridgeCurveMinMax hknot u hdata k) t ≠ 0 := by
  intro t hvel
  let q := contractedBridgeCurveMinMax hknot u hdata k
  have hqcont : ContDiff ℝ ⊤ q :=
    contDiff_contractedBridgeCurveMinMax hknot u hdata hk0 hk1
  have hqder : HasDerivAt q (velocity q t) t := by
    change HasDerivAt q (deriv q t) t
    exact ((hqcont.differentiable (by simp)).differentiableAt).hasDerivAt
  have hinnerDer := (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt t hqder
  have hinnerFun : (innerSL ℝ u ∘ q) = height r u := by
    funext z
    exact inner_contractedBridgeCurveMinMax hknot hu hdata hk0 hk1
  rw [hinnerFun] at hinnerDer
  have hheightDeriv : deriv (height r u) t = 0 := by
    rw [hinnerDer.deriv]
    change inner ℝ u (velocity q t) = 0
    rw [hvel, inner_zero_right]
  have hgzero : directionalUnitTangent r u t = 0 := by
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u t] at hheightDeriv
    exact (mul_eq_zero.mp hheightDeriv).resolve_left
      (norm_ne_zero_iff.mpr (hknot.regular t))
  let d : ℝ → Space := fun z =>
    contractedMateDirectionMinMax hknot u hdata k (height r u z)
  have hx := height_mem_Icc_minMax hknot u hdata (t := t)
  have hdcont : ContDiffAt ℝ ⊤ d t :=
    (contDiffAt_contractedMateDirectionMinMax hknot u hdata hk0 hk1 hx).comp t
      (contDiff_height hknot u).contDiffAt
  have hdder : HasDerivAt d (deriv d t) t :=
    (hdcont.differentiableAt (by simp)).hasDerivAt
  have hhder : HasDerivAt (height r u) 0 t := by
    have h : HasDerivAt (height r u) (deriv (height r u) t) t :=
      ((contDiff_height hknot u).differentiable
        (by simp)).differentiableAt.hasDerivAt
    rw [hheightDeriv] at h
    exact h
  have hgder : HasDerivAt (directionalUnitTangent r u)
      (deriv (directionalUnitTangent r u) t) t :=
    ((contDiff_directionalUnitTangent hknot u).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hformula := (hhder.smul_const u).add (hgder.smul hdder)
  have hqeq : (fun z => height r u z • u +
      directionalUnitTangent r u z • d z) = q := by
    funext z
    rfl
  change HasDerivAt (fun z => height r u z • u +
    directionalUnitTangent r u z • d z)
      (0 • u + (directionalUnitTangent r u t • deriv d t +
        deriv (directionalUnitTangent r u) t • d t)) t at hformula
  rw [hqeq] at hformula
  have hvelocity : velocity q t =
      deriv (directionalUnitTangent r u) t • d t := by
    rw [velocity, hformula.deriv]
    simp [hgzero]
  have hdne : d t ≠ 0 :=
    contractedMateDirectionMinMax_ne_zero hknot u hdata hk0 hk1 hx
  have hgderne := deriv_directionalUnitTangent_ne_zero_of_minMax
    hknot u hdata hgzero
  rw [hvelocity] at hvel
  exact smul_ne_zero hgderne hdne hvel

theorem isSmoothKnot_contractedBridgeCurveMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b k : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    IsSmoothKnot (contractedBridgeCurveMinMax hknot u hdata k) where
  smooth := contDiff_contractedBridgeCurveMinMax hknot u hdata hk0 hk1
  periodic := periodic_contractedBridgeCurveMinMax hknot u hdata
  injective_on_period := injOn_contractedBridgeCurveMinMax hknot hu hdata hk0 hk1
  regular := regular_contractedBridgeCurveMinMax hknot hu hdata hk0 hk1

noncomputable def liftPlanarCurveAlong (u : Space) (q d : ℝ → Space)
    (t : ℝ) : Space :=
  q t 0 • u + q t 1 • d t

theorem hasDerivAt_curve_coordinate {q : ℝ → Space}
    (hq : IsSmoothKnot q) (i : Fin 3) (t : ℝ) :
    HasDerivAt (fun z => q z i) (velocity q t i) t := by
  have h := (spaceCoordinateCLM i).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_curve hq t)
  have hcoord : HasDerivAt (spaceCoordinateCLM i ∘ q) (velocity q t i) t := by
    simpa [spaceCoordinateCLM, ofLpContinuousLinearMap] using h
  have hfun : (spaceCoordinateCLM i ∘ q) = fun z => q z i := by
    funext z
    simp [spaceCoordinateCLM, ofLpContinuousLinearMap]
  rwa [hfun] at hcoord

theorem inner_liftPlanarCurveAlong {u : Space} (hu : ‖u‖ = 1)
    {q d : ℝ → Space} (hdorth : ∀ t, inner ℝ u (d t) = 0) (t : ℝ) :
    inner ℝ u (liftPlanarCurveAlong u q d t) = q t 0 := by
  rw [liftPlanarCurveAlong, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, hdorth]
  rw [real_inner_self_eq_norm_sq, hu]
  norm_num

theorem isSmoothKnot_liftPlanarCurveAlong {u : Space} (hu : ‖u‖ = 1)
    {q d : ℝ → Space} (hq : IsSmoothKnot q)
    (hplanar : ∀ t, q t 2 = 0) (hd : ContDiff ℝ ⊤ d)
    (hdper : Function.Periodic d period) (hdne : ∀ t, d t ≠ 0)
    (hdorth : ∀ t, inner ℝ u (d t) = 0)
    (hdfiber : ∀ x y, q x 0 = q y 0 → d x = d y)
    (hdvelocity : ∀ t, velocity q t 0 = 0 → velocity d t = 0) :
    IsSmoothKnot (liftPlanarCurveAlong u q d) where
  smooth := by
    have hq0 : ContDiff ℝ ⊤ (fun t => q t 0) :=
      (spaceCoordinateCLM 0).contDiff.comp hq.smooth
    have hq1 : ContDiff ℝ ⊤ (fun t => q t 1) :=
      (spaceCoordinateCLM 1).contDiff.comp hq.smooth
    exact (hq0.smul
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => u))).add (hq1.smul hd)
  periodic := by
    intro t
    simp only [liftPlanarCurveAlong]
    rw [hq.periodic t, hdper t]
  injective_on_period := by
    intro x hx y hy hxy
    have hq0 : q x 0 = q y 0 := by
      have h := congrArg (fun v : Space => inner ℝ u v) hxy
      simpa only [inner_liftPlanarCurveAlong hu hdorth] using h
    have hdxy : d x = d y := hdfiber x y hq0
    have hscaled : q x 1 • d y = q y 1 • d y := by
      have hxy' := hxy
      rw [liftPlanarCurveAlong, liftPlanarCurveAlong, hq0, hdxy] at hxy'
      exact add_left_cancel hxy'
    have hq1 : q x 1 = q y 1 := by
      have hzero : (q x 1 - q y 1) • d y = 0 := by
        rw [sub_smul, hscaled, sub_self]
      rcases smul_eq_zero.mp hzero with h | h
      · exact sub_eq_zero.mp h
      · exact (hdne y h).elim
    apply hq.injective_on_period hx hy
    ext i
    fin_cases i
    · exact hq0
    · exact hq1
    · simp [hplanar]
  regular := by
    intro t hzero
    let c := liftPlanarCurveAlong u q d
    have hccont : ContDiff ℝ ⊤ c := by
      have hq0 : ContDiff ℝ ⊤ (fun z => q z 0) :=
        (spaceCoordinateCLM 0).contDiff.comp hq.smooth
      have hq1 : ContDiff ℝ ⊤ (fun z => q z 1) :=
        (spaceCoordinateCLM 1).contDiff.comp hq.smooth
      exact (hq0.smul
        (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => u))).add (hq1.smul hd)
    have hcder : HasDerivAt c (velocity c t) t := by
      change HasDerivAt c (deriv c t) t
      exact ((hccont.differentiable (by simp)).differentiableAt).hasDerivAt
    have hinnerDer := (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt t hcder
    have hinnerFun : (innerSL ℝ u ∘ c) = fun z => q z 0 := by
      funext z
      exact inner_liftPlanarCurveAlong hu hdorth z
    rw [hinnerFun] at hinnerDer
    have hq0vel : velocity q t 0 = 0 := by
      have hcoord := hasDerivAt_curve_coordinate hq 0 t
      rw [← hcoord.deriv, hinnerDer.deriv]
      change inner ℝ u (velocity c t) = 0
      rw [hzero, inner_zero_right]
    have hdvel : velocity d t = 0 := hdvelocity t hq0vel
    have hq1vel : velocity q t 1 ≠ 0 := by
      intro hq1zero
      apply hq.regular t
      ext i
      fin_cases i
      · exact hq0vel
      · exact hq1zero
      · exact velocity_coord_two_eq_zero hq hplanar t
    have hq0der := hasDerivAt_curve_coordinate hq 0 t
    have hq1der := hasDerivAt_curve_coordinate hq 1 t
    have hdder : HasDerivAt d (velocity d t) t := by
      change HasDerivAt d (deriv d t) t
      exact ((hd.differentiable (by simp)).differentiableAt).hasDerivAt
    have hformula := (hq0der.smul_const u).add (hq1der.smul hdder)
    change HasDerivAt c
      (velocity q t 0 • u +
        (q t 1 • velocity d t + velocity q t 1 • d t)) t at hformula
    have hvelFormula := hformula.deriv
    have hcvel : velocity c t = velocity q t 1 • d t := by
      rw [velocity, hvelFormula, hq0vel, hdvel]
      simp
    rw [hcvel] at hzero
    exact smul_ne_zero hq1vel (hdne t) hzero

theorem convexCombination_ne_zero_of_inner_pos {v w : Space} {s : ℝ}
    (hv : v ≠ 0) (hvw : 0 < inner ℝ v w) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) • v + s • w ≠ 0 := by
  intro hzero
  have hinner := congrArg (fun z : Space => inner ℝ v z) hzero
  simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at hinner
  have hvv : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
  have : 0 < (1 - s) * inner ℝ v v + s * inner ℝ v w := by
    rcases eq_or_lt_of_le hs0 with rfl | hs
    · simpa using hvv
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr hs1) hvv.le) (mul_pos hs hvw)
  linarith

end Submission.Helpers
