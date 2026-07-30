import Submission.BridgeEndpoint

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def straightContractedBridgeMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (k t s : ℝ) : Space :=
  (1 - s) • r t + s • contractedBridgeCurveMinMax hknot u hdata k t

@[simp] theorem straightContractedBridgeMinMax_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (k t : ℝ) :
    straightContractedBridgeMinMax hknot u hdata k t 0 = r t := by
  simp [straightContractedBridgeMinMax]

@[simp] theorem straightContractedBridgeMinMax_one {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (k t : ℝ) :
    straightContractedBridgeMinMax hknot u hdata k t 1 =
      contractedBridgeCurveMinMax hknot u hdata k t := by
  simp [straightContractedBridgeMinMax]

theorem contDiff_straightContractedBridgeMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      straightContractedBridgeMinMax hknot u hdata k p.1 p.2) := by
  have hr : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => r p.1) :=
    hknot.smooth.comp contDiff_fst
  have hq : ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      contractedBridgeCurveMinMax hknot u hdata k p.1) :=
    (contDiff_contractedBridgeCurveMinMax hknot u hdata hk0 hk1).comp
      contDiff_fst
  have hs : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.2) := contDiff_snd
  simpa [straightContractedBridgeMinMax] using
    ((contDiff_const.sub hs).smul hr).add (hs.smul hq)

theorem periodic_straightContractedBridgeMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k s : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    Function.Periodic
      (fun t => straightContractedBridgeMinMax hknot u hdata k t s) period := by
  intro t
  simp only [straightContractedBridgeMinMax]
  rw [hknot.periodic t, periodic_contractedBridgeCurveMinMax hknot u hdata t]

theorem inner_straightContractedBridgeMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b k s t : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    inner ℝ u (straightContractedBridgeMinMax hknot u hdata k t s) =
      height r u t := by
  rw [straightContractedBridgeMinMax, inner_add_right,
    real_inner_smul_right, real_inner_smul_right,
    inner_contractedBridgeCurveMinMax hknot hu hdata hk0 hk1]
  change (1 - s) * height r u t + s * height r u t = height r u t
  ring

theorem straightContractedBridgeMinMax_periodLift {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k s t : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    straightContractedBridgeMinMax hknot u hdata k (periodLift a t) s =
      straightContractedBridgeMinMax hknot u hdata k t s := by
  rw [periodLift]
  split_ifs
  · exact periodic_straightContractedBridgeMinMax hknot u hdata t
  · rfl

theorem curve_sub_mate_eq_smul_extendedDirection {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t y : ℝ}
    (hdata : MinMaxBridgeData r u a b) (ht : t ∈ Ioo a b)
    (hy : y ∈ Ioo b (a + period))
    (hheight : height r u y = height r u t) :
    r t - r y =
      (directionalUnitTangent r u t - directionalUnitTangent r u y) •
        extendedMateDirectionMinMax hknot u hdata (height r u t) := by
  have hxheight : height r u t ∈
      Ioo (height r u a) (height r u b) := by
    exact ⟨hdata.height_mono ⟨le_rfl, hdata.left_lt_right.le⟩
        ⟨ht.1.le, ht.2.le⟩ ht.1,
      hdata.height_mono ⟨ht.1.le, ht.2.le⟩
        ⟨hdata.left_lt_right.le, le_rfl⟩ ht.2⟩
  have hmate : forwardHeightMateMinMax hknot u hdata t = y := by
    symm
    apply forwardHeightMateMinMax_unique hknot u hdata
    · exact ne_of_gt (hdata.tangent_pos t ht)
    · refine ⟨⟨lt_trans ht.2 hy.1, ?_⟩, hheight, ?_⟩
      · linarith [hy.2, ht.1]
      · exact mul_neg_of_pos_of_neg (hdata.tangent_pos t ht)
          (hdata.tangent_neg_wrap y hy)
  have hgdiff : directionalUnitTangent r u t -
      directionalUnitTangent r u y ≠ 0 := by
    have htpos := hdata.tangent_pos t ht
    have hyneg := hdata.tangent_neg_wrap y hy
    linarith
  rw [extendedMateDirectionMinMax_eq_central hknot u hdata hxheight,
    centralMateDirectionMinMax,
    minMaxHeightParameter_height hknot u hdata ⟨ht.1.le, ht.2.le⟩,
    mateDirectionMinMax, hmate]
  rw [smul_smul]
  simp [hgdiff]

theorem contractedBridge_sub_eq_smul_direction {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k t y : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hheight : height r u y = height r u t) :
    contractedBridgeCurveMinMax hknot u hdata k t -
        contractedBridgeCurveMinMax hknot u hdata k y =
      (directionalUnitTangent r u t - directionalUnitTangent r u y) •
        contractedMateDirectionMinMax hknot u hdata k (height r u t) := by
  unfold contractedBridgeCurveMinMax
  rw [hheight]
  module

theorem straightContractedBridgeMinMax_ne_of_opposite_arcs
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space) {a b k s t y : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hs : s ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ x ∈ Icc (height r u a) (height r u b),
      0 < inner ℝ (extendedMateDirectionMinMax hknot u hdata x)
        (contractedMateDirectionMinMax hknot u hdata k x))
    (ht : t ∈ Ioo a b) (hy : y ∈ Ioo b (a + period))
    (hheight : height r u y = height r u t) :
    straightContractedBridgeMinMax hknot u hdata k t s ≠
      straightContractedBridgeMinMax hknot u hdata k y s := by
  let D := extendedMateDirectionMinMax hknot u hdata (height r u t)
  let d := contractedMateDirectionMinMax hknot u hdata k (height r u t)
  have hxheight := height_mem_Icc_minMax hknot u hdata (t := t)
  have hDne : D ≠ 0 := extendedMateDirectionMinMax_ne_zero hknot u hdata hxheight
  have hinner : 0 < inner ℝ D d := hpos _ hxheight
  have hcombo : (1 - s) • D + s • d ≠ 0 :=
    convexCombination_ne_zero_of_inner_pos hDne hinner hs.1 hs.2
  have hgdiff : directionalUnitTangent r u t -
      directionalUnitTangent r u y ≠ 0 := by
    have htpos := hdata.tangent_pos t ht
    have hyneg := hdata.tangent_neg_wrap y hy
    linarith
  have hrsub := curve_sub_mate_eq_smul_extendedDirection
    hknot u hdata ht hy hheight
  have hqsub := contractedBridge_sub_eq_smul_direction
    hknot u hdata (k := k) hheight
  intro heq
  have hzero : (directionalUnitTangent r u t - directionalUnitTangent r u y) •
      ((1 - s) • D + s • d) = 0 := by
    calc
      _ = (1 - s) • (r t - r y) +
          s • (contractedBridgeCurveMinMax hknot u hdata k t -
            contractedBridgeCurveMinMax hknot u hdata k y) := by
        rw [hrsub, hqsub]
        module
      _ = straightContractedBridgeMinMax hknot u hdata k t s -
          straightContractedBridgeMinMax hknot u hdata k y s := by
        unfold straightContractedBridgeMinMax
        module
      _ = 0 := sub_eq_zero.mpr heq
  exact smul_ne_zero hgdiff hcombo hzero

theorem injOn_straightContractedBridgeMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b k s : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ x ∈ Icc (height r u a) (height r u b),
      0 < inner ℝ (extendedMateDirectionMinMax hknot u hdata x)
        (contractedMateDirectionMinMax hknot u hdata k x)) :
    Set.InjOn (fun t => straightContractedBridgeMinMax hknot u hdata k t s)
      (Ico (0 : ℝ) period) := by
  intro x hx y hy hxy
  have hheight : height r u x = height r u y := by
    have h := congrArg (fun v : Space => inner ℝ u v) hxy
    simpa only [inner_straightContractedBridgeMinMax hknot hu hdata hk0 hk1]
      using h
  let x' := periodLift a x
  let y' := periodLift a y
  have hx' : x' ∈ Ico a (a + period) := periodLift_mem_Ico hdata.left_mem hx
  have hy' : y' ∈ Ico a (a + period) := periodLift_mem_Ico hdata.left_mem hy
  have hxy' : straightContractedBridgeMinMax hknot u hdata k x' s =
      straightContractedBridgeMinMax hknot u hdata k y' s := by
    calc
      _ = straightContractedBridgeMinMax hknot u hdata k x s :=
        straightContractedBridgeMinMax_periodLift hknot u hdata
      _ = straightContractedBridgeMinMax hknot u hdata k y s := hxy
      _ = _ := (straightContractedBridgeMinMax_periodLift hknot u hdata).symm
  have hheight' : height r u x' = height r u y' := by
    have h := congrArg (fun v : Space => inner ℝ u v) hxy'
    simpa only [inner_straightContractedBridgeMinMax hknot hu hdata hk0 hk1]
      using h
  by_cases hxb : x' ≤ b
  · by_cases hyb : y' ≤ b
    · have hxeq := hdata.height_mono.injOn ⟨hx'.1, hxb⟩ ⟨hy'.1, hyb⟩ hheight'
      exact periodLift_injective_on_Ico hdata.left_mem hx hy hxeq
    · have hygt : b < y' := lt_of_not_ge hyb
      have hxa : a < x' := by
        rcases hx'.1.eq_or_lt with hxa | hxa
        · have hlt := hdata.height_anti_wrap
            ⟨hygt.le, hy'.2.le⟩
            ⟨by linarith [hdata.left_mem.1, hdata.right_mem.2], le_rfl⟩ hy'.2
          rw [periodic_height hknot u a] at hlt
          have heq : height r u a = height r u y' := by
            rw [hxa, hheight']
          exact ((ne_of_lt hlt) heq).elim
        · exact hxa
      have hxb' : x' < b := by
        rcases hxb.eq_or_lt with hxb | hxb
        · have hlt := hdata.height_anti_wrap
            ⟨le_rfl, by linarith [hdata.left_mem.1, hdata.right_mem.2]⟩
            ⟨hygt.le, hy'.2.le⟩ hygt
          have heq : height r u y' = height r u b := by
            rw [← hheight', hxb]
          exact ((ne_of_lt hlt) heq).elim
        · exact hxb
      exact (straightContractedBridgeMinMax_ne_of_opposite_arcs
        hknot u hdata hs hpos ⟨hxa, hxb'⟩ ⟨hygt, hy'.2⟩
          hheight'.symm hxy').elim
  · have hxgt : b < x' := lt_of_not_ge hxb
    by_cases hyb : y' ≤ b
    · have hya : a < y' := by
        rcases hy'.1.eq_or_lt with hya | hya
        · have hlt := hdata.height_anti_wrap
            ⟨hxgt.le, hx'.2.le⟩
            ⟨by linarith [hdata.left_mem.1, hdata.right_mem.2], le_rfl⟩ hx'.2
          rw [periodic_height hknot u a] at hlt
          have heq : height r u a = height r u x' := by
            rw [hya, ← hheight']
          exact ((ne_of_lt hlt) heq).elim
        · exact hya
      have hyb' : y' < b := by
        rcases hyb.eq_or_lt with hyb | hyb
        · have hlt := hdata.height_anti_wrap
            ⟨le_rfl, by linarith [hdata.left_mem.1, hdata.right_mem.2]⟩
            ⟨hxgt.le, hx'.2.le⟩ hxgt
          have heq : height r u x' = height r u b := by
            rw [hheight', hyb]
          exact ((ne_of_lt hlt) heq).elim
        · exact hyb
      exact (straightContractedBridgeMinMax_ne_of_opposite_arcs
        hknot u hdata hs hpos ⟨hya, hyb'⟩ ⟨hxgt, hx'.2⟩
          hheight' hxy'.symm).elim
    · have hxeq := hdata.height_anti_wrap.injOn
        ⟨hxgt.le, hx'.2.le⟩ ⟨(lt_of_not_ge hyb).le, hy'.2.le⟩ hheight'
      exact periodLift_injective_on_Ico hdata.left_mem hx hy hxeq

theorem velocity_left_eq_deriv_smul_extendedDirection {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    velocity r a = deriv (directionalUnitTangent r u) a •
      extendedMateDirectionMinMax hknot u hdata (height r u a) := by
  rw [extendedMateDirectionMinMax, if_pos
    (left_lt_bridgeHeightMidpoint hdata.height_endpoints_lt).le,
    minMaxLowerChordDirection_left, minMaxLeftDirection, smul_smul]
  simp [hdata.tangent_deriv_left.ne']

theorem velocity_right_eq_deriv_smul_extendedDirection {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    velocity r b = deriv (directionalUnitTangent r u) b •
      extendedMateDirectionMinMax hknot u hdata (height r u b) := by
  rw [extendedMateDirectionMinMax, if_neg
    (not_le.mpr (bridgeHeightMidpoint_lt_right hdata.height_endpoints_lt)),
    minMaxUpperChordDirection_right, minMaxRightDirection, smul_smul]
  simp [hdata.tangent_deriv_right.ne]

theorem velocity_eq_deriv_smul_extendedDirection_of_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t : ℝ}
    (hdata : MinMaxBridgeData r u a b)
    (hzero : directionalUnitTangent r u t = 0) :
    velocity r t = deriv (directionalUnitTangent r u) t •
      extendedMateDirectionMinMax hknot u hdata (height r u t) := by
  have hp : 0 < period := by simp [period, Real.pi_pos]
  obtain ⟨m, hm, _hmuniq⟩ := existsUnique_add_zsmul_mem_Ico hp t a
  let z : ℝ := t + m • period
  have hz : z ∈ Ico a (a + period) := by simpa [z] using hm
  have hgshift : directionalUnitTangent r u z =
      directionalUnitTangent r u t := by
    have hper := (periodic_directionalUnitTangent hknot u).sub_zsmul_eq
      (x := t) (-m)
    simpa [z, sub_neg_eq_add] using hper
  have hvshift : velocity r z = velocity r t := by
    have hper := (periodic_velocity hknot).sub_zsmul_eq (x := t) (-m)
    simpa [z, sub_neg_eq_add] using hper
  have hdshift : deriv (directionalUnitTangent r u) z =
      deriv (directionalUnitTangent r u) t := by
    have hper := (periodic_deriv_directionalUnitTangent hknot u).sub_zsmul_eq
      (x := t) (-m)
    simpa [z, sub_neg_eq_add] using hper
  have hhshift : height r u z = height r u t := by
    have hper := (periodic_height hknot u).sub_zsmul_eq (x := t) (-m)
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
  rcases hz_cases with hza | hzb
  · calc
      velocity r t = velocity r z := hvshift.symm
      _ = deriv (directionalUnitTangent r u) z •
          extendedMateDirectionMinMax hknot u hdata (height r u z) := by
        rw [hza]
        exact velocity_left_eq_deriv_smul_extendedDirection hknot u hdata
      _ = _ := by rw [hdshift, hhshift]
  · calc
      velocity r t = velocity r z := hvshift.symm
      _ = deriv (directionalUnitTangent r u) z •
          extendedMateDirectionMinMax hknot u hdata (height r u z) := by
        rw [hzb]
        exact velocity_right_eq_deriv_smul_extendedDirection hknot u hdata
      _ = _ := by rw [hdshift, hhshift]

theorem velocity_contractedBridgeCurveMinMax_of_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k t : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hzero : directionalUnitTangent r u t = 0) :
    velocity (contractedBridgeCurveMinMax hknot u hdata k) t =
      deriv (directionalUnitTangent r u) t •
        contractedMateDirectionMinMax hknot u hdata k (height r u t) := by
  let q := contractedBridgeCurveMinMax hknot u hdata k
  let d : ℝ → Space := fun z =>
    contractedMateDirectionMinMax hknot u hdata k (height r u z)
  have hx := height_mem_Icc_minMax hknot u hdata (t := t)
  have hdcont : ContDiffAt ℝ ⊤ d t :=
    (contDiffAt_contractedMateDirectionMinMax hknot u hdata hk0 hk1 hx).comp t
      (contDiff_height hknot u).contDiffAt
  have hdder : HasDerivAt d (deriv d t) t :=
    (hdcont.differentiableAt (by simp)).hasDerivAt
  have hheightDeriv : deriv (height r u) t = 0 := by
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u t, hzero]
    simp
  have hhder : HasDerivAt (height r u) 0 t := by
    have h : HasDerivAt (height r u) (deriv (height r u) t) t :=
      ((contDiff_height hknot u).differentiable
        (by simp)).differentiableAt.hasDerivAt
    rwa [hheightDeriv] at h
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
  rw [velocity, hformula.deriv]
  simp [hzero, d]

theorem regular_straightContractedBridgeMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b k s : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ x ∈ Icc (height r u a) (height r u b),
      0 < inner ℝ (extendedMateDirectionMinMax hknot u hdata x)
        (contractedMateDirectionMinMax hknot u hdata k x)) :
    ∀ t, velocity
      (fun z => straightContractedBridgeMinMax hknot u hdata k z s) t ≠ 0 := by
  intro t hvel
  let q := fun z => straightContractedBridgeMinMax hknot u hdata k z s
  let c := contractedBridgeCurveMinMax hknot u hdata k
  have hqcont : ContDiff ℝ ⊤ q :=
    (contDiff_straightContractedBridgeMinMax hknot u hdata hk0 hk1).comp
      (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => s)))
  have hqder : HasDerivAt q (velocity q t) t := by
    change HasDerivAt q (deriv q t) t
    exact ((hqcont.differentiable (by simp)).differentiableAt).hasDerivAt
  have hinnerDer := (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt t hqder
  have hinnerFun : (innerSL ℝ u ∘ q) = height r u := by
    funext z
    exact inner_straightContractedBridgeMinMax hknot hu hdata hk0 hk1
  rw [hinnerFun] at hinnerDer
  have hheightDeriv : deriv (height r u) t = 0 := by
    rw [hinnerDer.deriv]
    change inner ℝ u (velocity q t) = 0
    rw [hvel, inner_zero_right]
  have hgzero : directionalUnitTangent r u t = 0 := by
    rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u t] at hheightDeriv
    exact (mul_eq_zero.mp hheightDeriv).resolve_left
      (norm_ne_zero_iff.mpr (hknot.regular t))
  have hccont : ContDiff ℝ ⊤ c :=
    contDiff_contractedBridgeCurveMinMax hknot u hdata hk0 hk1
  have hcder : HasDerivAt c (velocity c t) t := by
    change HasDerivAt c (deriv c t) t
    exact ((hccont.differentiable (by simp)).differentiableAt).hasDerivAt
  have hformula := ((hasDerivAt_curve hknot t).const_smul (1 - s)).add
    (hcder.const_smul s)
  change HasDerivAt q ((1 - s) • velocity r t + s • velocity c t) t at hformula
  have hvelocity : velocity q t =
      (1 - s) • velocity r t + s • velocity c t := by
    rw [velocity, hformula.deriv]
  have hrvel := velocity_eq_deriv_smul_extendedDirection_of_zero
    hknot u hdata hgzero
  have hcvel := velocity_contractedBridgeCurveMinMax_of_zero
    hknot u hdata hk0 hk1 hgzero
  let D := extendedMateDirectionMinMax hknot u hdata (height r u t)
  let d := contractedMateDirectionMinMax hknot u hdata k (height r u t)
  have hx := height_mem_Icc_minMax hknot u hdata (t := t)
  have hDne : D ≠ 0 := extendedMateDirectionMinMax_ne_zero hknot u hdata hx
  have hinner : 0 < inner ℝ D d := hpos _ hx
  have hcombo : (1 - s) • D + s • d ≠ 0 :=
    convexCombination_ne_zero_of_inner_pos hDne hinner hs.1 hs.2
  have hgderne := deriv_directionalUnitTangent_ne_zero_of_minMax
    hknot u hdata hgzero
  have hvelocity' : velocity q t =
      deriv (directionalUnitTangent r u) t • ((1 - s) • D + s • d) := by
    rw [hvelocity, hrvel, hcvel]
    module
  rw [hvelocity'] at hvel
  exact smul_ne_zero hgderne hcombo hvel

theorem isSmoothKnot_straightContractedBridgeMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b k s : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ x ∈ Icc (height r u a) (height r u b),
      0 < inner ℝ (extendedMateDirectionMinMax hknot u hdata x)
        (contractedMateDirectionMinMax hknot u hdata k x)) :
    IsSmoothKnot
      (fun t => straightContractedBridgeMinMax hknot u hdata k t s) where
  smooth := (contDiff_straightContractedBridgeMinMax hknot u hdata hk0 hk1).comp
    (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => s)))
  periodic := periodic_straightContractedBridgeMinMax hknot u hdata
  injective_on_period := injOn_straightContractedBridgeMinMax
    hknot hu hdata hk0 hk1 hs hpos
  regular := regular_straightContractedBridgeMinMax
    hknot hu hdata hk0 hk1 hs hpos

theorem exists_straightContractedBridgeMinMax_isotopy {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) :
    ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
        straightContractedBridgeMinMax hknot u hdata k p.1 p.2) ∧
      (∀ t, straightContractedBridgeMinMax hknot u hdata k t 0 = r t) ∧
      (∀ t, straightContractedBridgeMinMax hknot u hdata k t 1 =
        contractedBridgeCurveMinMax hknot u hdata k t) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        IsSmoothKnot
          (fun t => straightContractedBridgeMinMax hknot u hdata k t s) := by
  obtain ⟨k, hk0, hk1, hpos⟩ :=
    exists_uniform_positive_contractedMateDirectionMinMax hknot u hdata
  refine ⟨k, hk0, hk1,
    contDiff_straightContractedBridgeMinMax hknot u hdata hk0 hk1,
    ?_, ?_, ?_⟩
  · intro t
    exact straightContractedBridgeMinMax_zero hknot u hdata k t
  · intro t
    exact straightContractedBridgeMinMax_one hknot u hdata k t
  · intro s hs
    exact isSmoothKnot_straightContractedBridgeMinMax
      hknot hu hdata hk0 hk1 hs hpos

end Submission.Helpers
