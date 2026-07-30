import Submission.PlanarUnknot

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def angleDenominator (k t : ℝ) : ℝ :=
  (1 + k) + (1 - k) * Real.cos t

noncomputable def angleCorrection (k t : ℝ) : ℝ :=
  (k - 1) * Real.sin t / angleDenominator k t

noncomputable def angleMap (k t : ℝ) : ℝ :=
  t + 2 * Real.arctan (angleCorrection k t)

theorem angleDenominator_pos {k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 < angleDenominator k t := by
  by_cases hk1 : k ≤ 1
  · have hcoef : 0 ≤ 1 - k := sub_nonneg.mpr hk1
    have hcos := Real.neg_one_le_cos t
    have hmul : -(1 - k) ≤ (1 - k) * Real.cos t := by
      nlinarith
    unfold angleDenominator
    linarith
  · have hcoef : 1 - k < 0 := sub_neg.mpr (lt_of_not_ge hk1)
    have hcos := Real.cos_le_one t
    have hmul : 1 - k ≤ (1 - k) * Real.cos t := by
      nlinarith
    unfold angleDenominator
    linarith

theorem angleSecondDenominator_pos {k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 < (1 + k ^ 2) + (1 - k ^ 2) * Real.cos t := by
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk
  by_cases hk1 : k ^ 2 ≤ 1
  · have hcoef : 0 ≤ 1 - k ^ 2 := sub_nonneg.mpr hk1
    have hcos := Real.neg_one_le_cos t
    have hmul : -(1 - k ^ 2) ≤ (1 - k ^ 2) * Real.cos t := by
      nlinarith
    linarith
  · have hcoef : 1 - k ^ 2 < 0 := sub_neg.mpr (lt_of_not_ge hk1)
    have hcos := Real.cos_le_one t
    have hmul : 1 - k ^ 2 ≤ (1 - k ^ 2) * Real.cos t := by
      nlinarith
    linarith

theorem hasDerivAt_angleDenominator (k t : ℝ) :
    HasDerivAt (angleDenominator k) ((k - 1) * Real.sin t) t := by
  have hcos := Real.hasDerivAt_cos t
  have hmul := hcos.const_mul (1 - k)
  convert (hasDerivAt_const (x := t) (c := (1 + k : ℝ))).add hmul using 1 <;>
    try rfl
  ring

theorem hasDerivAt_angleCorrection {k t : ℝ} (hk : 0 < k) :
    HasDerivAt (angleCorrection k)
      (((k - 1) * Real.cos t * angleDenominator k t -
          ((k - 1) * Real.sin t) ^ 2) /
        angleDenominator k t ^ 2) t := by
  have hnum := Real.hasDerivAt_sin t |>.const_mul (k - 1)
  have hden := hasDerivAt_angleDenominator k t
  have hden_ne := (angleDenominator_pos hk t).ne'
  convert hnum.div hden hden_ne using 1 <;> try rfl
  ring

theorem hasDerivAt_angleMap {k t : ℝ} (hk : 0 < k) :
    HasDerivAt (angleMap k)
      (2 * k / ((1 + k ^ 2) + (1 - k ^ 2) * Real.cos t)) t := by
  have hcorr := hasDerivAt_angleCorrection (t := t) hk
  have hmap := (hasDerivAt_id t).add (hcorr.arctan.const_mul 2)
  have hD : angleDenominator k t ≠ 0 := (angleDenominator_pos hk t).ne'
  have hE := angleSecondDenominator_pos hk t
  have hfun : angleMap k = id + fun y => 2 * Real.arctan (angleCorrection k y) := by
    funext z
    change z + 2 * Real.arctan (angleCorrection k z) =
      z + 2 * Real.arctan (angleCorrection k z)
    rfl
  rw [hfun]
  have hcoef :
      1 + 2 *
          (1 / (1 + angleCorrection k t ^ 2) *
            (((k - 1) * Real.cos t * angleDenominator k t -
                ((k - 1) * Real.sin t) ^ 2) /
              angleDenominator k t ^ 2)) =
        2 * k / ((1 + k ^ 2) + (1 - k ^ 2) * Real.cos t) := by
    unfold angleCorrection
    unfold angleDenominator at hD ⊢
    have htrig : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    have hE' :
        1 + k ^ 2 - k ^ 2 * Real.cos t + Real.cos t ≠ 0 := by
      have heq :
          1 + k ^ 2 - k ^ 2 * Real.cos t + Real.cos t =
            (1 + k ^ 2) + (1 - k ^ 2) * Real.cos t := by
        ring
      rw [heq]
      exact hE.ne'
    field_simp [hD, hE.ne', hE']
    rw [htrig]
    ring_nf
    field_simp [hE']
    ring
  rw [← hcoef]
  exact hmap

theorem deriv_angleMap {k t : ℝ} (hk : 0 < k) :
    deriv (angleMap k) t =
      2 * k / ((1 + k ^ 2) + (1 - k ^ 2) * Real.cos t) :=
  (hasDerivAt_angleMap (t := t) hk).deriv

theorem deriv_angleMap_pos {k t : ℝ} (hk : 0 < k) :
    0 < deriv (angleMap k) t := by
  rw [deriv_angleMap hk]
  exact div_pos (mul_pos two_pos hk) (angleSecondDenominator_pos hk t)

theorem strictMono_angleMap {k : ℝ} (hk : 0 < k) : StrictMono (angleMap k) := by
  apply strictMono_of_deriv_pos
  intro t
  exact deriv_angleMap_pos hk

theorem periodic_angleCorrection (k : ℝ) :
    Function.Periodic (angleCorrection k) period := by
  intro t
  unfold angleCorrection angleDenominator
  have harg : t + period = t + 2 * Real.pi := by simp [period]
  rw [harg]
  simp

theorem angleMap_add_period (k t : ℝ) :
    angleMap k (t + period) = angleMap k t + period := by
  unfold angleMap
  rw [periodic_angleCorrection k t]
  ring

@[simp] theorem angleMap_one (t : ℝ) : angleMap 1 t = t := by
  simp [angleMap, angleCorrection]

theorem cos_two_mul_arctan_formula (q : ℝ) :
    Real.cos (2 * Real.arctan q) = (1 - q ^ 2) / (1 + q ^ 2) := by
  have hpos : 0 < 1 + q ^ 2 := by positivity
  have hsqrt : Real.sqrt (1 + q ^ 2) ^ 2 = 1 + q ^ 2 :=
    Real.sq_sqrt hpos.le
  have hsqrt_ne : Real.sqrt (1 + q ^ 2) ≠ 0 := by positivity
  rw [Real.cos_two_mul', Real.cos_arctan, Real.sin_arctan]
  field_simp [hsqrt_ne, hpos.ne']
  rw [hsqrt]

theorem sin_two_mul_arctan_formula (q : ℝ) :
    Real.sin (2 * Real.arctan q) = 2 * q / (1 + q ^ 2) := by
  have hpos : 0 < 1 + q ^ 2 := by positivity
  have hsqrt : Real.sqrt (1 + q ^ 2) ^ 2 = 1 + q ^ 2 :=
    Real.sq_sqrt hpos.le
  have hsqrt_ne : Real.sqrt (1 + q ^ 2) ≠ 0 := by positivity
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp [hsqrt_ne, hpos.ne']
  rw [hsqrt]

theorem one_sub_div_sq_div_one_add_div_sq {D N : ℝ} (hD : D ≠ 0) :
    (1 - (N / D) ^ 2) / (1 + (N / D) ^ 2) =
      (D ^ 2 - N ^ 2) / (D ^ 2 + N ^ 2) := by
  have hsum : D ^ 2 + N ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hD, sq_nonneg N]
  field_simp [hD, hsum]

theorem two_mul_div_div_one_add_div_sq {D N : ℝ} (hD : D ≠ 0) :
    (2 * (N / D)) / (1 + (N / D) ^ 2) =
      2 * N * D / (D ^ 2 + N ^ 2) := by
  have hsum : D ^ 2 + N ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero hD, sq_nonneg N]
  field_simp [hD, hsum]

theorem angleCorrection_cosFraction {k : ℝ} (hk : 0 < k) (t : ℝ) :
    (1 - angleCorrection k t ^ 2) / (1 + angleCorrection k t ^ 2) =
      (angleDenominator k t ^ 2 - ((k - 1) * Real.sin t) ^ 2) /
        (angleDenominator k t ^ 2 + ((k - 1) * Real.sin t) ^ 2) := by
  let D := angleDenominator k t
  let N := (k - 1) * Real.sin t
  have hD : D ≠ 0 := by
    dsimp [D]
    exact (angleDenominator_pos hk t).ne'
  change (1 - (N / D) ^ 2) / (1 + (N / D) ^ 2) =
    (D ^ 2 - N ^ 2) / (D ^ 2 + N ^ 2)
  exact one_sub_div_sq_div_one_add_div_sq hD

theorem angleCorrection_sinFraction {k : ℝ} (hk : 0 < k) (t : ℝ) :
    2 * angleCorrection k t / (1 + angleCorrection k t ^ 2) =
      2 * ((k - 1) * Real.sin t) * angleDenominator k t /
        (angleDenominator k t ^ 2 + ((k - 1) * Real.sin t) ^ 2) := by
  let D := angleDenominator k t
  let N := (k - 1) * Real.sin t
  have hD : D ≠ 0 := by
    dsimp [D]
    exact (angleDenominator_pos hk t).ne'
  change 2 * (N / D) / (1 + (N / D) ^ 2) =
    2 * N * D / (D ^ 2 + N ^ 2)
  exact two_mul_div_div_one_add_div_sq hD

theorem cos_angleMap {k : ℝ} (hk : 0 < k) (t : ℝ) :
    Real.cos (angleMap k t) =
      ((1 - k ^ 2) + (1 + k ^ 2) * Real.cos t) /
        ((1 + k ^ 2) + (1 - k ^ 2) * Real.cos t) := by
  let D := angleDenominator k t
  let N := (k - 1) * Real.sin t
  let E := (1 + k ^ 2) + (1 - k ^ 2) * Real.cos t
  have hE : E ≠ 0 := by
    dsimp [E]
    exact (angleSecondDenominator_pos hk t).ne'
  have hsum : D ^ 2 + N ^ 2 = 2 * E := by
    dsimp [D, N, E]
    unfold angleDenominator
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [angleMap, Real.cos_add, cos_two_mul_arctan_formula,
    sin_two_mul_arctan_formula, angleCorrection_cosFraction hk,
    angleCorrection_sinFraction hk]
  change Real.cos t * ((D ^ 2 - N ^ 2) / (D ^ 2 + N ^ 2)) -
      Real.sin t * (2 * N * D / (D ^ 2 + N ^ 2)) =
    ((1 - k ^ 2) + (1 + k ^ 2) * Real.cos t) / E
  rw [hsum]
  field_simp [hE]
  dsimp [D, N, E]
  unfold angleDenominator
  ring_nf
  have htrig : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [htrig]
  ring

theorem sin_angleMap {k : ℝ} (hk : 0 < k) (t : ℝ) :
    Real.sin (angleMap k t) =
      2 * k * Real.sin t /
        ((1 + k ^ 2) + (1 - k ^ 2) * Real.cos t) := by
  let D := angleDenominator k t
  let N := (k - 1) * Real.sin t
  let E := (1 + k ^ 2) + (1 - k ^ 2) * Real.cos t
  have hE : E ≠ 0 := by
    dsimp [E]
    exact (angleSecondDenominator_pos hk t).ne'
  have hsum : D ^ 2 + N ^ 2 = 2 * E := by
    dsimp [D, N, E]
    unfold angleDenominator
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [angleMap, Real.sin_add, cos_two_mul_arctan_formula,
    sin_two_mul_arctan_formula, angleCorrection_cosFraction hk,
    angleCorrection_sinFraction hk]
  change Real.sin t * ((D ^ 2 - N ^ 2) / (D ^ 2 + N ^ 2)) +
      Real.cos t * (2 * N * D / (D ^ 2 + N ^ 2)) =
    2 * k * Real.sin t / E
  rw [hsum]
  field_simp [hE]
  dsimp [D, N, E]
  unfold angleDenominator
  ring_nf
  have htrig : Real.sin t ^ 2 = 1 - Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have htrig3 : Real.sin t ^ 3 = Real.sin t * (1 - Real.cos t ^ 2) := by
    calc
      Real.sin t ^ 3 = Real.sin t * Real.sin t ^ 2 := by ring
      _ = Real.sin t * (1 - Real.cos t ^ 2) := by rw [htrig]
  rw [htrig3]
  ring

noncomputable def bridgeInverseScale (a b : ℝ) : ℝ :=
  (1 - Real.cos (bridgeHalfSpan a b)) / Real.sin (bridgeHalfSpan a b)

theorem bridgeInverseScale_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    0 < bridgeInverseScale a b := by
  have hcos := abs_cos_bridgeHalfSpan_lt_one ha hab hb
  have hnum : 0 < 1 - Real.cos (bridgeHalfSpan a b) :=
    sub_pos.mpr (abs_lt.mp hcos).2
  exact div_pos hnum (sin_bridgeHalfSpan_pos ha hab hb)

theorem bridgeInverseDenominator_pos {a b t : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    0 < 1 + Real.cos (bridgeHalfSpan a b) * Real.cos t := by
  have hc := abs_cos_bridgeHalfSpan_lt_one ha hab hb
  have ht : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
  have hmul :
      |Real.cos (bridgeHalfSpan a b) * Real.cos t| < 1 := by
    rw [abs_mul]
    calc
      |Real.cos (bridgeHalfSpan a b)| * |Real.cos t|
          ≤ |Real.cos (bridgeHalfSpan a b)| * 1 := by gcongr
      _ < 1 := by simpa using hc
  linarith [(abs_lt.mp hmul).1]

theorem cos_angleMap_bridgeInverseScale {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) (t : ℝ) :
    Real.cos (angleMap (bridgeInverseScale a b) t) =
      (Real.cos t + Real.cos (bridgeHalfSpan a b)) /
        (1 + Real.cos (bridgeHalfSpan a b) * Real.cos t) := by
  let c := Real.cos (bridgeHalfSpan a b)
  let s := Real.sin (bridgeHalfSpan a b)
  let k := bridgeInverseScale a b
  have hs : s ≠ 0 := by
    dsimp [s]
    exact (sin_bridgeHalfSpan_pos ha hab hb).ne'
  have hk : 0 < k := by
    dsimp [k]
    exact bridgeInverseScale_pos ha hab hb
  have htarget : 1 + c * Real.cos t ≠ 0 := by
    dsimp [c]
    exact (bridgeInverseDenominator_pos (t := t) ha hab hb).ne'
  have hangle := (angleSecondDenominator_pos hk t).ne'
  rw [cos_angleMap hk]
  change
    ((1 - k ^ 2) + (1 + k ^ 2) * Real.cos t) /
        ((1 + k ^ 2) + (1 - k ^ 2) * Real.cos t) =
      (Real.cos t + c) / (1 + c * Real.cos t)
  dsimp [k, bridgeInverseScale]
  change
    ((1 - ((1 - c) / s) ^ 2) +
        (1 + ((1 - c) / s) ^ 2) * Real.cos t) /
        ((1 + ((1 - c) / s) ^ 2) +
          (1 - ((1 - c) / s) ^ 2) * Real.cos t) = _
  have htrig : s ^ 2 = 1 - c ^ 2 := by
    dsimp [s, c]
    nlinarith [Real.sin_sq_add_cos_sq (bridgeHalfSpan a b)]
  have hcne : 1 - c ≠ 0 := by
    apply ne_of_gt
    dsimp [c]
    exact sub_pos.mpr (abs_lt.mp (abs_cos_bridgeHalfSpan_lt_one ha hab hb)).2
  have hfactor :
      1 - c + c * Real.cos t - c ^ 2 * Real.cos t ≠ 0 := by
    have heq :
        1 - c + c * Real.cos t - c ^ 2 * Real.cos t =
          (1 - c) * (1 + c * Real.cos t) := by
      ring
    rw [heq]
    exact mul_ne_zero hcne htarget
  field_simp [hs, htarget, hangle]
  rw [htrig]
  ring_nf
  field_simp [hfactor]
  ring

theorem sin_angleMap_bridgeInverseScale {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) (t : ℝ) :
    Real.sin (angleMap (bridgeInverseScale a b) t) =
      Real.sin (bridgeHalfSpan a b) * Real.sin t /
        (1 + Real.cos (bridgeHalfSpan a b) * Real.cos t) := by
  let c := Real.cos (bridgeHalfSpan a b)
  let s := Real.sin (bridgeHalfSpan a b)
  let k := bridgeInverseScale a b
  have hs : s ≠ 0 := by
    dsimp [s]
    exact (sin_bridgeHalfSpan_pos ha hab hb).ne'
  have hk : 0 < k := by
    dsimp [k]
    exact bridgeInverseScale_pos ha hab hb
  have htarget : 1 + c * Real.cos t ≠ 0 := by
    dsimp [c]
    exact (bridgeInverseDenominator_pos (t := t) ha hab hb).ne'
  have hangle := (angleSecondDenominator_pos hk t).ne'
  rw [sin_angleMap hk]
  change
    2 * k * Real.sin t /
        ((1 + k ^ 2) + (1 - k ^ 2) * Real.cos t) =
      s * Real.sin t / (1 + c * Real.cos t)
  dsimp [k, bridgeInverseScale]
  change
    2 * ((1 - c) / s) * Real.sin t /
        ((1 + ((1 - c) / s) ^ 2) +
          (1 - ((1 - c) / s) ^ 2) * Real.cos t) = _
  have htrig : s ^ 2 = 1 - c ^ 2 := by
    dsimp [s, c]
    nlinarith [Real.sin_sq_add_cos_sq (bridgeHalfSpan a b)]
  have hcne : 1 - c ≠ 0 := by
    apply ne_of_gt
    dsimp [c]
    exact sub_pos.mpr (abs_lt.mp (abs_cos_bridgeHalfSpan_lt_one ha hab hb)).2
  have hfactor :
      1 - c + c * Real.cos t - c ^ 2 * Real.cos t ≠ 0 := by
    have heq :
        1 - c + c * Real.cos t - c ^ 2 * Real.cos t =
          (1 - c) * (1 + c * Real.cos t) := by
      ring
    rw [heq]
    exact mul_ne_zero hcne htarget
  field_simp [hs, htarget, hangle]
  rw [htrig]
  ring_nf
  field_simp [hfactor]
  ring

noncomputable def bridgeInverseParameter (a b t : ℝ) : ℝ :=
  bridgeMidpoint a b + angleMap (bridgeInverseScale a b) t

theorem bridgeInverseParameter_sub_midpoint (a b t : ℝ) :
    bridgeInverseParameter a b t - bridgeMidpoint a b =
      angleMap (bridgeInverseScale a b) t := by
  simp [bridgeInverseParameter]

theorem bridgeCircleX_bridgeInverseParameter {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) (t : ℝ) :
    bridgeCircleX a b (bridgeInverseParameter a b t) = Real.cos t := by
  let c := Real.cos (bridgeHalfSpan a b)
  let q := 1 + c * Real.cos t
  have hq : q ≠ 0 := by
    dsimp [q, c]
    exact (bridgeInverseDenominator_pos (t := t) ha hab hb).ne'
  have hbridge :
      1 - c * ((Real.cos t + c) / q) ≠ 0 := by
    have hpos := bridgeDenominator_pos
      (t := bridgeInverseParameter a b t) ha hab hb
    unfold bridgeDenominator at hpos
    rw [bridgeInverseParameter_sub_midpoint,
      cos_angleMap_bridgeInverseScale ha hab hb] at hpos
    simpa [c, q] using hpos.ne'
  have hden : q - c * (Real.cos t + c) ≠ 0 := by
    have hc : c ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one]
      dsimp [c]
      exact abs_cos_bridgeHalfSpan_lt_one ha hab hb
    dsimp [q]
    nlinarith
  rw [bridgeCircleX, bridgeDenominator,
    bridgeInverseParameter_sub_midpoint,
    cos_angleMap_bridgeInverseScale ha hab hb]
  change (((Real.cos t + c) / q) - c) /
      (1 - c * ((Real.cos t + c) / q)) = Real.cos t
  field_simp [hq, hbridge]
  ring_nf
  field_simp [hden]
  ring

theorem bridgeCircleY_bridgeInverseParameter {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) (t : ℝ) :
    bridgeCircleY a b (bridgeInverseParameter a b t) = Real.sin t := by
  let c := Real.cos (bridgeHalfSpan a b)
  let s := Real.sin (bridgeHalfSpan a b)
  let q := 1 + c * Real.cos t
  have hq : q ≠ 0 := by
    dsimp [q, c]
    exact (bridgeInverseDenominator_pos (t := t) ha hab hb).ne'
  have hbridge :
      1 - c * ((Real.cos t + c) / q) ≠ 0 := by
    have hpos := bridgeDenominator_pos
      (t := bridgeInverseParameter a b t) ha hab hb
    unfold bridgeDenominator at hpos
    rw [bridgeInverseParameter_sub_midpoint,
      cos_angleMap_bridgeInverseScale ha hab hb] at hpos
    simpa [c, q] using hpos.ne'
  have hden : q - c * (Real.cos t + c) ≠ 0 := by
    have hc : c ^ 2 < 1 := by
      rw [sq_lt_one_iff_abs_lt_one]
      dsimp [c]
      exact abs_cos_bridgeHalfSpan_lt_one ha hab hb
    dsimp [q]
    nlinarith
  rw [bridgeCircleY, bridgeDenominator,
    bridgeInverseParameter_sub_midpoint,
    cos_angleMap_bridgeInverseScale ha hab hb,
    sin_angleMap_bridgeInverseScale ha hab hb]
  change (s * (s * Real.sin t / q)) /
      (1 - c * ((Real.cos t + c) / q)) = Real.sin t
  have htrig : s ^ 2 = 1 - c ^ 2 := by
    dsimp [s, c]
    nlinarith [Real.sin_sq_add_cos_sq (bridgeHalfSpan a b)]
  field_simp [hq, hbridge]
  rw [htrig]
  field_simp [hden]
  dsimp [q]
  ring

noncomputable def bridgeReparamScale (a b s : ℝ) : ℝ :=
  isotopyWeight s + (1 - isotopyWeight s) * bridgeInverseScale a b

noncomputable def bridgeReparamCenter (a b s : ℝ) : ℝ :=
  (1 - isotopyWeight s) * bridgeMidpoint a b

noncomputable def bridgeReparam (a b t s : ℝ) : ℝ :=
  bridgeReparamCenter a b s + angleMap (bridgeReparamScale a b s) t

theorem bridgeReparamScale_pos {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    0 < bridgeReparamScale a b s := by
  have hw0 := isotopyWeight_nonneg s
  have hw1 := isotopyWeight_le_one s
  have hk := bridgeInverseScale_pos ha hab hb
  by_cases hw : isotopyWeight s = 0
  · simp [bridgeReparamScale, hw, hk]
  · have hwpos : 0 < isotopyWeight s := lt_of_le_of_ne hw0 (Ne.symm hw)
    have hnonneg :
        0 ≤ (1 - isotopyWeight s) * bridgeInverseScale a b :=
      mul_nonneg (sub_nonneg.mpr hw1) hk.le
    unfold bridgeReparamScale
    linarith

theorem contDiff_bridgeReparamScale (a b : ℝ) :
    ContDiff ℝ ⊤ (bridgeReparamScale a b) := by
  unfold bridgeReparamScale
  exact contDiff_isotopyWeight.add
    ((contDiff_const.sub contDiff_isotopyWeight).mul contDiff_const)

theorem contDiff_bridgeReparamCenter (a b : ℝ) :
    ContDiff ℝ ⊤ (bridgeReparamCenter a b) := by
  unfold bridgeReparamCenter
  exact (contDiff_const.sub contDiff_isotopyWeight).mul contDiff_const

theorem contDiff_angleMap_varyingScale {k : ℝ → ℝ}
    (hk : ContDiff ℝ ⊤ k) (hkpos : ∀ s, 0 < k s) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => angleMap (k p.2) p.1) := by
  let K : ℝ × ℝ → ℝ := fun p => k p.2
  let D : ℝ × ℝ → ℝ := fun p =>
    (1 + K p) + (1 - K p) * Real.cos p.1
  have hK : ContDiff ℝ ⊤ K := hk.comp contDiff_snd
  have hD : ContDiff ℝ ⊤ D := by
    dsimp [D]
    fun_prop
  have hDne : ∀ p, D p ≠ 0 := by
    intro p
    dsimp [D, K]
    exact (angleDenominator_pos (hkpos p.2) p.1).ne'
  have hcorr : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => (K p - 1) * Real.sin p.1 / D p) := by
    exact ((hK.sub contDiff_const).mul (Real.contDiff_sin.comp contDiff_fst)).div hD hDne
  have hatan : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => Real.arctan ((K p - 1) * Real.sin p.1 / D p)) :=
    Real.contDiff_arctan.comp hcorr
  change ContDiff ℝ ⊤
    (fun p : ℝ × ℝ => p.1 +
      2 * Real.arctan (((k p.2 - 1) * Real.sin p.1) /
        ((1 + k p.2) + (1 - k p.2) * Real.cos p.1)))
  simpa [K, D] using contDiff_fst.add (contDiff_const.mul hatan)

theorem contDiff_bridgeReparam {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => bridgeReparam a b p.1 p.2) := by
  unfold bridgeReparam
  exact (contDiff_bridgeReparamCenter a b).comp contDiff_snd |>.add
    (contDiff_angleMap_varyingScale (contDiff_bridgeReparamScale a b)
      fun s => bridgeReparamScale_pos ha hab hb)

@[simp] theorem bridgeReparam_zero (a b t : ℝ) :
    bridgeReparam a b t 0 = t := by
  simp [bridgeReparam, bridgeReparamCenter, bridgeReparamScale]

@[simp] theorem bridgeReparam_one (a b t : ℝ) :
    bridgeReparam a b t 1 = bridgeInverseParameter a b t := by
  simp [bridgeReparam, bridgeReparamCenter, bridgeReparamScale,
    bridgeInverseParameter]

theorem bridgeReparam_add_period (a b t s : ℝ) :
    bridgeReparam a b (t + period) s = bridgeReparam a b t s + period := by
  unfold bridgeReparam
  rw [angleMap_add_period]
  ring

theorem strictMono_bridgeReparam {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    StrictMono (fun t => bridgeReparam a b t s) := by
  intro x y hxy
  unfold bridgeReparam
  exact add_lt_add_right
    (strictMono_angleMap (bridgeReparamScale_pos ha hab hb) hxy) _

theorem hasDerivAt_bridgeReparam {a b t s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    HasDerivAt (fun z => bridgeReparam a b z s)
      (2 * bridgeReparamScale a b s /
        ((1 + bridgeReparamScale a b s ^ 2) +
          (1 - bridgeReparamScale a b s ^ 2) * Real.cos t)) t := by
  unfold bridgeReparam
  exact (hasDerivAt_angleMap (k := bridgeReparamScale a b s) (t := t)
    (bridgeReparamScale_pos ha hab hb)).const_add (bridgeReparamCenter a b s)

theorem deriv_bridgeReparam_pos {a b t s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    0 < deriv (fun z => bridgeReparam a b z s) t := by
  rw [(hasDerivAt_bridgeReparam (t := t) (s := s) ha hab hb).deriv]
  exact div_pos (mul_pos two_pos (bridgeReparamScale_pos ha hab hb))
    (angleSecondDenominator_pos (bridgeReparamScale_pos ha hab hb) t)

end Submission.Helpers
