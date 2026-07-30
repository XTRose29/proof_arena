import Submission.PlanarBridge

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def bridgeMidpoint (a b : ℝ) : ℝ :=
  (a + b) / 2

noncomputable def bridgeHalfSpan (a b : ℝ) : ℝ :=
  (b - a) / 2

noncomputable def bridgeDenominator (a b t : ℝ) : ℝ :=
  1 - Real.cos (bridgeHalfSpan a b) * Real.cos (t - bridgeMidpoint a b)

noncomputable def bridgeCircleX (a b t : ℝ) : ℝ :=
  (Real.cos (t - bridgeMidpoint a b) - Real.cos (bridgeHalfSpan a b)) /
    bridgeDenominator a b t

noncomputable def bridgeCircleY (a b t : ℝ) : ℝ :=
  Real.sin (bridgeHalfSpan a b) * Real.sin (t - bridgeMidpoint a b) /
    bridgeDenominator a b t

noncomputable def bridgeCircleSpeed (a b t : ℝ) : ℝ :=
  Real.sin (bridgeHalfSpan a b) / bridgeDenominator a b t

theorem bridgeHalfSpan_pos {a b : ℝ} (hab : a < b) :
    0 < bridgeHalfSpan a b := by
  simp [bridgeHalfSpan, hab]

theorem bridgeHalfSpan_lt_pi {a b : ℝ} (ha : 0 ≤ a) (hb : b < period) :
    bridgeHalfSpan a b < Real.pi := by
  simp only [bridgeHalfSpan, period] at *
  linarith

theorem sin_bridgeHalfSpan_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    0 < Real.sin (bridgeHalfSpan a b) := by
  exact Real.sin_pos_of_pos_of_lt_pi (bridgeHalfSpan_pos hab)
    (bridgeHalfSpan_lt_pi ha hb)

theorem abs_cos_bridgeHalfSpan_lt_one {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    |Real.cos (bridgeHalfSpan a b)| < 1 := by
  rw [← sq_lt_one_iff_abs_lt_one]
  nlinarith [Real.sin_sq_add_cos_sq (bridgeHalfSpan a b),
    sq_pos_of_pos (sin_bridgeHalfSpan_pos ha hab hb)]

theorem bridgeDenominator_pos {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    0 < bridgeDenominator a b t := by
  have hc := abs_cos_bridgeHalfSpan_lt_one ha hab hb
  have ht : |Real.cos (t - bridgeMidpoint a b)| ≤ 1 := Real.abs_cos_le_one _
  have hmul : Real.cos (bridgeHalfSpan a b) * Real.cos (t - bridgeMidpoint a b) < 1 := by
    calc
      Real.cos (bridgeHalfSpan a b) * Real.cos (t - bridgeMidpoint a b)
          ≤ |Real.cos (bridgeHalfSpan a b)| * |Real.cos (t - bridgeMidpoint a b)| := by
            rw [← abs_mul]
            exact le_abs_self _
      _ ≤ |Real.cos (bridgeHalfSpan a b)| * 1 := by
            gcongr
      _ < 1 := by simpa using hc
  simpa [bridgeDenominator] using sub_pos.mpr hmul

theorem bridgeCircleSpeed_pos {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    0 < bridgeCircleSpeed a b t := by
  exact div_pos (sin_bridgeHalfSpan_pos ha hab hb)
    (bridgeDenominator_pos (t := t) ha hab hb)

theorem bridgeCircle_sq_add_sq {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    bridgeCircleX a b t ^ 2 + bridgeCircleY a b t ^ 2 = 1 := by
  have hden := (bridgeDenominator_pos (t := t) ha hab hb).ne'
  rw [bridgeCircleX, bridgeCircleY]
  field_simp [hden]
  rw [bridgeDenominator]
  nlinarith [Real.sin_sq_add_cos_sq (bridgeHalfSpan a b),
    Real.sin_sq_add_cos_sq (t - bridgeMidpoint a b)]

theorem contDiff_bridgeDenominator (a b : ℝ) :
    ContDiff ℝ ⊤ (bridgeDenominator a b) := by
  unfold bridgeDenominator
  fun_prop

theorem contDiff_bridgeCircleX {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    ContDiff ℝ ⊤ (bridgeCircleX a b) := by
  unfold bridgeCircleX
  have hnum : ContDiff ℝ ⊤
      (fun t => Real.cos (t - bridgeMidpoint a b) - Real.cos (bridgeHalfSpan a b)) := by
    fun_prop
  exact hnum.div (contDiff_bridgeDenominator a b)
    fun t => (bridgeDenominator_pos (t := t) ha hab hb).ne'

theorem contDiff_bridgeCircleY {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    ContDiff ℝ ⊤ (bridgeCircleY a b) := by
  unfold bridgeCircleY
  have hnum : ContDiff ℝ ⊤
      (fun t => Real.sin (bridgeHalfSpan a b) *
        Real.sin (t - bridgeMidpoint a b)) := by
    fun_prop
  exact hnum.div (contDiff_bridgeDenominator a b)
    fun t => (bridgeDenominator_pos (t := t) ha hab hb).ne'

theorem hasDerivAt_bridgeDenominator (a b t : ℝ) :
    HasDerivAt (bridgeDenominator a b)
      (Real.cos (bridgeHalfSpan a b) *
        Real.sin (t - bridgeMidpoint a b)) t := by
  have harg : HasDerivAt (fun z : ℝ => z - bridgeMidpoint a b) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (bridgeMidpoint a b)
  have hcos := harg.cos
  have hmul := hcos.const_mul (Real.cos (bridgeHalfSpan a b))
  convert (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub hmul using 1 <;>
    try rfl
  ring

theorem hasDerivAt_bridgeCircleX {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    HasDerivAt (bridgeCircleX a b)
      (-(bridgeCircleSpeed a b t * bridgeCircleY a b t)) t := by
  have harg : HasDerivAt (fun z : ℝ => z - bridgeMidpoint a b) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (bridgeMidpoint a b)
  have hnum : HasDerivAt
      (fun z => Real.cos (z - bridgeMidpoint a b) - Real.cos (bridgeHalfSpan a b))
      (-Real.sin (t - bridgeMidpoint a b)) t := by
    simpa using harg.cos.sub_const (Real.cos (bridgeHalfSpan a b))
  have hden := hasDerivAt_bridgeDenominator a b t
  have hden_ne := (bridgeDenominator_pos (t := t) ha hab hb).ne'
  have hden_expr :
      1 - Real.cos (bridgeHalfSpan a b) *
        Real.cos (t - bridgeMidpoint a b) ≠ 0 := by
    simpa [bridgeDenominator] using hden_ne
  convert hnum.div hden hden_ne using 1 <;> try rfl
  unfold bridgeCircleSpeed bridgeCircleY bridgeDenominator
  field_simp [hden_expr]
  have htrig : Real.sin (bridgeHalfSpan a b) ^ 2 =
      1 - Real.cos (bridgeHalfSpan a b) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (bridgeHalfSpan a b)]
  rw [htrig]
  ring

theorem hasDerivAt_bridgeCircleY {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    HasDerivAt (bridgeCircleY a b)
      (bridgeCircleSpeed a b t * bridgeCircleX a b t) t := by
  have harg : HasDerivAt (fun z : ℝ => z - bridgeMidpoint a b) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (bridgeMidpoint a b)
  have hnum : HasDerivAt
      (fun z => Real.sin (bridgeHalfSpan a b) *
        Real.sin (z - bridgeMidpoint a b))
      (Real.sin (bridgeHalfSpan a b) *
        Real.cos (t - bridgeMidpoint a b)) t := by
    simpa using harg.sin.const_mul (Real.sin (bridgeHalfSpan a b))
  have hden := hasDerivAt_bridgeDenominator a b t
  have hden_ne := (bridgeDenominator_pos (t := t) ha hab hb).ne'
  have hden_expr :
      1 - Real.cos (bridgeHalfSpan a b) *
        Real.cos (t - bridgeMidpoint a b) ≠ 0 := by
    simpa [bridgeDenominator] using hden_ne
  convert hnum.div hden hden_ne using 1 <;> try rfl
  unfold bridgeCircleSpeed bridgeCircleX bridgeDenominator
  field_simp [hden_expr]
  have htrig : Real.sin (t - bridgeMidpoint a b) ^ 2 =
      1 - Real.cos (t - bridgeMidpoint a b) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (t - bridgeMidpoint a b)]
  rw [htrig]
  ring

theorem deriv_bridgeCircleX {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    deriv (bridgeCircleX a b) t =
      -(bridgeCircleSpeed a b t * bridgeCircleY a b t) :=
  (hasDerivAt_bridgeCircleX (t := t) ha hab hb).deriv

theorem deriv_bridgeCircleY {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    deriv (bridgeCircleY a b) t =
      bridgeCircleSpeed a b t * bridgeCircleX a b t :=
  (hasDerivAt_bridgeCircleY (t := t) ha hab hb).deriv

theorem periodic_bridgeCircleX (a b : ℝ) :
    Function.Periodic (bridgeCircleX a b) period := by
  intro t
  rw [bridgeCircleX, bridgeCircleX, bridgeDenominator, bridgeDenominator]
  have harg : t + period - bridgeMidpoint a b =
      (t - bridgeMidpoint a b) + 2 * Real.pi := by
    simp [period]
    ring
  rw [harg]
  simp

theorem periodic_bridgeCircleY (a b : ℝ) :
    Function.Periodic (bridgeCircleY a b) period := by
  intro t
  rw [bridgeCircleY, bridgeCircleY, bridgeDenominator, bridgeDenominator]
  have harg : t + period - bridgeMidpoint a b =
      (t - bridgeMidpoint a b) + 2 * Real.pi := by
    simp [period]
    ring
  rw [harg]
  simp

theorem injOn_bridgeCircleXY {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    Set.InjOn (fun t => (bridgeCircleX a b t, bridgeCircleY a b t))
      (Ico (0 : ℝ) period) := by
  intro x hx y hy hxy
  have hX := congrArg Prod.fst hxy
  have hY := congrArg Prod.snd hxy
  dsimp at hX hY
  have hdx := (bridgeDenominator_pos (t := x) ha hab hb).ne'
  have hdy := (bridgeDenominator_pos (t := y) ha hab hb).ne'
  have hdx' : 1 - Real.cos (bridgeHalfSpan a b) *
      Real.cos (x - bridgeMidpoint a b) ≠ 0 := by
    simpa [bridgeDenominator] using hdx
  have hdy' : 1 - Real.cos (bridgeHalfSpan a b) *
      Real.cos (y - bridgeMidpoint a b) ≠ 0 := by
    simpa [bridgeDenominator] using hdy
  have hdx'' : 1 - Real.cos (x - bridgeMidpoint a b) *
      Real.cos (bridgeHalfSpan a b) ≠ 0 := by
    simpa [mul_comm] using hdx'
  have hdy'' : 1 - Real.cos (y - bridgeMidpoint a b) *
      Real.cos (bridgeHalfSpan a b) ≠ 0 := by
    simpa [mul_comm] using hdy'
  have hcosShift : Real.cos (x - bridgeMidpoint a b) =
      Real.cos (y - bridgeMidpoint a b) := by
    unfold bridgeCircleX bridgeDenominator at hX
    field_simp [hdx', hdy', hdx'', hdy''] at hX
    have hsin := sin_bridgeHalfSpan_pos ha hab hb
    have htrig := Real.sin_sq_add_cos_sq (bridgeHalfSpan a b)
    nlinarith [sq_pos_of_pos hsin]
  have hsinShift : Real.sin (x - bridgeMidpoint a b) =
      Real.sin (y - bridgeMidpoint a b) := by
    unfold bridgeCircleY bridgeDenominator at hY
    field_simp [hdx', hdy', hdx'', hdy''] at hY
    rw [hcosShift] at hY
    have hcoef : Real.sin (bridgeHalfSpan a b) *
        (1 - Real.cos (bridgeHalfSpan a b) *
          Real.cos (y - bridgeMidpoint a b)) ≠ 0 :=
      mul_ne_zero (sin_bridgeHalfSpan_pos ha hab hb).ne' hdy'
    apply mul_left_cancel₀ hcoef
    nlinarith
  have hxShift : x - bridgeMidpoint a b ∈
      Ico (-bridgeMidpoint a b) (period - bridgeMidpoint a b) := by
    constructor <;> linarith [hx.1, hx.2]
  have hyShift : y - bridgeMidpoint a b ∈
      Ico (-bridgeMidpoint a b) (period - bridgeMidpoint a b) := by
    constructor <;> linarith [hy.1, hy.2]
  have hcircle : circleMap 0 1 (x - bridgeMidpoint a b) =
      circleMap 0 1 (y - bridgeMidpoint a b) := by
    apply Complex.ext
    · simpa [circleMap_zero_re] using hcosShift
    · simpa [circleMap_zero_im] using hsinShift
  have hinj : Set.InjOn (circleMap 0 1)
      (Ico (-bridgeMidpoint a b) (period - bridgeMidpoint a b)) :=
    injOn_circleMap_of_abs_sub_le' (c := 0) (R := 1) one_ne_zero (by simp [period])
  have hshift := hinj hxShift hyShift hcircle
  linarith

noncomputable def bridgeCircleMinMax (a b t : ℝ) : Space :=
  toLp 2 ![bridgeCircleY a b t, bridgeCircleX a b t, 0]

noncomputable def bridgeCircleMaxMin (a b t : ℝ) : Space :=
  toLp 2 ![-bridgeCircleY a b t, -bridgeCircleX a b t, 0]

theorem contDiff_bridgeCircleMinMax {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    ContDiff ℝ ⊤ (bridgeCircleMinMax a b) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [bridgeCircleMinMax] using contDiff_bridgeCircleY ha hab hb
  · simpa [bridgeCircleMinMax] using contDiff_bridgeCircleX ha hab hb
  · simpa [bridgeCircleMinMax] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℝ)))

theorem contDiff_bridgeCircleMaxMin {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    ContDiff ℝ ⊤ (bridgeCircleMaxMin a b) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [bridgeCircleMaxMin] using (contDiff_bridgeCircleY ha hab hb).neg
  · simpa [bridgeCircleMaxMin] using (contDiff_bridgeCircleX ha hab hb).neg
  · simpa [bridgeCircleMaxMin] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℝ)))

theorem periodic_bridgeCircleMinMax (a b : ℝ) :
    Function.Periodic (bridgeCircleMinMax a b) period := by
  intro t
  ext i
  fin_cases i
  · simp [bridgeCircleMinMax, periodic_bridgeCircleY a b t]
  · simp [bridgeCircleMinMax, periodic_bridgeCircleX a b t]
  · simp [bridgeCircleMinMax]

theorem periodic_bridgeCircleMaxMin (a b : ℝ) :
    Function.Periodic (bridgeCircleMaxMin a b) period := by
  intro t
  ext i
  fin_cases i
  · simp [bridgeCircleMaxMin, periodic_bridgeCircleY a b t]
  · simp [bridgeCircleMaxMin, periodic_bridgeCircleX a b t]
  · simp [bridgeCircleMaxMin]

theorem velocity_bridgeCircleMinMax {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    velocity (bridgeCircleMinMax a b) t =
      toLp 2 ![bridgeCircleSpeed a b t * bridgeCircleX a b t,
        -(bridgeCircleSpeed a b t * bridgeCircleY a b t), 0] := by
  have hraw : HasDerivAt
      (fun z : ℝ => ![bridgeCircleY a b z, bridgeCircleX a b z, 0])
      ![bridgeCircleSpeed a b t * bridgeCircleX a b t,
        -(bridgeCircleSpeed a b t * bridgeCircleY a b t), 0] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hasDerivAt_bridgeCircleY ha hab hb
    · exact hasDerivAt_bridgeCircleX ha hab hb
    · simpa using hasDerivAt_const (x := t) (c := (0 : ℝ))
  exact (toLpContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw).deriv

theorem velocity_bridgeCircleMaxMin {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    velocity (bridgeCircleMaxMin a b) t =
      toLp 2 ![-(bridgeCircleSpeed a b t * bridgeCircleX a b t),
        bridgeCircleSpeed a b t * bridgeCircleY a b t, 0] := by
  have hraw : HasDerivAt
      (fun z : ℝ => ![-bridgeCircleY a b z, -bridgeCircleX a b z, 0])
      ![-(bridgeCircleSpeed a b t * bridgeCircleX a b t),
        bridgeCircleSpeed a b t * bridgeCircleY a b t, 0] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact (hasDerivAt_bridgeCircleY ha hab hb).neg
    · have hneg := (hasDerivAt_bridgeCircleX (t := t) ha hab hb).neg
      have hneg' : HasDerivAt (fun z => -bridgeCircleX a b z)
          (bridgeCircleSpeed a b t * bridgeCircleY a b t) t := by
        convert hneg using 1 <;> try rfl
        ring
      exact hneg'
    · simpa using hasDerivAt_const (x := t) (c := (0 : ℝ))
  exact (toLpContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw).deriv

theorem isSmoothKnot_bridgeCircleMinMax {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    IsSmoothKnot (bridgeCircleMinMax a b) where
  smooth := contDiff_bridgeCircleMinMax ha hab hb
  periodic := periodic_bridgeCircleMinMax a b
  injective_on_period := by
    intro x hx y hy hxy
    apply injOn_bridgeCircleXY ha hab hb hx hy
    apply Prod.ext
    · simpa [bridgeCircleMinMax] using congrArg (fun v : Space => v 1) hxy
    · simpa [bridgeCircleMinMax] using congrArg (fun v : Space => v 0) hxy
  regular := by
    intro t hzero
    have h0 : bridgeCircleSpeed a b t * bridgeCircleX a b t = 0 := by
      simpa [velocity_bridgeCircleMinMax ha hab hb] using
        congrArg (fun v : Space => v 0) hzero
    have h1 : bridgeCircleSpeed a b t * bridgeCircleY a b t = 0 := by
      simpa [velocity_bridgeCircleMinMax ha hab hb] using
        congrArg (fun v : Space => v 1) hzero
    have hspeed := (bridgeCircleSpeed_pos (t := t) ha hab hb).ne'
    have hX : bridgeCircleX a b t = 0 := (mul_eq_zero.mp h0).resolve_left hspeed
    have hY : bridgeCircleY a b t = 0 := (mul_eq_zero.mp h1).resolve_left hspeed
    nlinarith [bridgeCircle_sq_add_sq (t := t) ha hab hb]

theorem isSmoothKnot_bridgeCircleMaxMin {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    IsSmoothKnot (bridgeCircleMaxMin a b) where
  smooth := contDiff_bridgeCircleMaxMin ha hab hb
  periodic := periodic_bridgeCircleMaxMin a b
  injective_on_period := by
    intro x hx y hy hxy
    apply injOn_bridgeCircleXY ha hab hb hx hy
    apply Prod.ext
    · have h1 := congrArg (fun v : Space => v 1) hxy
      exact neg_inj.mp (by simpa [bridgeCircleMaxMin] using h1)
    · have h0 := congrArg (fun v : Space => v 0) hxy
      simpa [bridgeCircleMaxMin] using neg_inj.mp h0
  regular := by
    intro t hzero
    have h0 : bridgeCircleSpeed a b t * bridgeCircleX a b t = 0 := by
      simpa [velocity_bridgeCircleMaxMin ha hab hb] using
        congrArg (fun v : Space => v 0) hzero
    have h1 : bridgeCircleSpeed a b t * bridgeCircleY a b t = 0 := by
      simpa [velocity_bridgeCircleMaxMin ha hab hb] using
        congrArg (fun v : Space => v 1) hzero
    have hspeed := (bridgeCircleSpeed_pos (t := t) ha hab hb).ne'
    have hX : bridgeCircleX a b t = 0 := (mul_eq_zero.mp h0).resolve_left hspeed
    have hY : bridgeCircleY a b t = 0 := (mul_eq_zero.mp h1).resolve_left hspeed
    nlinarith [bridgeCircle_sq_add_sq (t := t) ha hab hb]

theorem bridgeCircleX_pos_of_mem_Ioo {a b z : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) (hz : z ∈ Ioo a b) :
    0 < bridgeCircleX a b z := by
  have hd0 := bridgeHalfSpan_pos hab
  have hdpi := bridgeHalfSpan_lt_pi ha hb
  have hw : |z - bridgeMidpoint a b| < bridgeHalfSpan a b := by
    rw [abs_lt]
    constructor <;> simp only [bridgeMidpoint, bridgeHalfSpan] <;> linarith [hz.1, hz.2]
  have hcos : Real.cos (bridgeHalfSpan a b) <
      Real.cos (z - bridgeMidpoint a b) := by
    have hcosAbs := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := |z - bridgeMidpoint a b|) (y := bridgeHalfSpan a b)
      (abs_nonneg _) hdpi.le hw
    simpa only [Real.cos_abs] using hcosAbs
  exact div_pos (sub_pos.mpr hcos) (bridgeDenominator_pos ha hab hb)

theorem bridgeCircleX_neg_of_mem_wrap {a b z : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) (hz : z ∈ Ioo b (a + period)) :
    bridgeCircleX a b z < 0 := by
  have hd0 := bridgeHalfSpan_pos hab
  have hdpi := bridgeHalfSpan_lt_pi ha hb
  let w := z - bridgeMidpoint a b
  have hdw : bridgeHalfSpan a b < w := by
    dsimp [w, bridgeMidpoint, bridgeHalfSpan]
    linarith [hz.1]
  have hwtop : w < 2 * Real.pi - bridgeHalfSpan a b := by
    dsimp [w, bridgeMidpoint, bridgeHalfSpan, period] at *
    linarith [hz.2]
  have hcos : Real.cos w < Real.cos (bridgeHalfSpan a b) := by
    by_cases hwpi : w ≤ Real.pi
    · exact Real.cos_lt_cos_of_nonneg_of_le_pi hd0.le hwpi hdw
    · have hpiw : Real.pi < w := lt_of_not_ge hwpi
      have hmirror0 : 0 ≤ 2 * Real.pi - w := by linarith [hwtop, hd0]
      have hmirrorpi : 2 * Real.pi - w ≤ Real.pi := by linarith
      have hdmirror : bridgeHalfSpan a b < 2 * Real.pi - w := by linarith
      rw [← Real.cos_two_pi_sub w]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi hd0.le hmirrorpi hdmirror
  exact div_neg_of_neg_of_pos (sub_neg.mpr hcos)
    (bridgeDenominator_pos ha hab hb)

theorem strictMonoOn_bridgeCircleY_Icc {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    StrictMonoOn (bridgeCircleY a b) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    (contDiff_bridgeCircleY ha hab hb).continuous.continuousOn
  intro z hz
  rw [interior_Icc] at hz
  rw [deriv_bridgeCircleY ha hab hb]
  exact mul_pos (bridgeCircleSpeed_pos ha hab hb)
    (bridgeCircleX_pos_of_mem_Ioo ha hab hb hz)

theorem strictAntiOn_bridgeCircleY_wrap {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    StrictAntiOn (bridgeCircleY a b) (Icc b (a + period)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc b (a + period))
    (contDiff_bridgeCircleY ha hab hb).continuous.continuousOn
  intro z hz
  rw [interior_Icc] at hz
  rw [deriv_bridgeCircleY ha hab hb]
  exact mul_neg_of_pos_of_neg (bridgeCircleSpeed_pos ha hab hb)
    (bridgeCircleX_neg_of_mem_wrap ha hab hb hz)

theorem strictMonoOn_convexCombination {f g : ℝ → ℝ} {s : ℝ} {S : Set ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hf : StrictMonoOn f S)
    (hg : StrictMonoOn g S) :
    StrictMonoOn (fun x => (1 - s) * f x + s * g x) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hs.1 with rfl | hspos
  · simpa using hf hx hy hxy
  rcases eq_or_lt_of_le hs.2 with hsone | hslt
  · subst s
    simpa using hg hx hy hxy
  have hF := mul_lt_mul_of_pos_left (hf hx hy hxy) (sub_pos.mpr hslt)
  have hG := mul_lt_mul_of_pos_left (hg hx hy hxy) hspos
  linarith

theorem strictAntiOn_convexCombination {f g : ℝ → ℝ} {s : ℝ} {S : Set ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hf : StrictAntiOn f S)
    (hg : StrictAntiOn g S) :
    StrictAntiOn (fun x => (1 - s) * f x + s * g x) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hs.1 with rfl | hspos
  · simpa using hf hx hy hxy
  rcases eq_or_lt_of_le hs.2 with hsone | hslt
  · subst s
    simpa using hg hx hy hxy
  have hF := mul_lt_mul_of_pos_left (hf hx hy hxy) (sub_pos.mpr hslt)
  have hG := mul_lt_mul_of_pos_left (hg hx hy hxy) hspos
  linarith

theorem convexCombination_pos {x y s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hx : 0 < x) (hy : 0 < y) :
    0 < (1 - s) * x + s * y := by
  rcases eq_or_lt_of_le hs.1 with rfl | hspos
  · simpa using hx
  rcases eq_or_lt_of_le hs.2 with hsone | hslt
  · subst s
    simpa using hy
  exact add_pos (mul_pos (sub_pos.mpr hslt) hx) (mul_pos hspos hy)

theorem convexCombination_neg {x y s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hx : x < 0) (hy : y < 0) :
    (1 - s) * x + s * y < 0 := by
  rcases eq_or_lt_of_le hs.1 with rfl | hspos
  · simpa using hx
  rcases eq_or_lt_of_le hs.2 with hsone | hslt
  · subst s
    simpa using hy
  exact add_neg (mul_neg_of_pos_of_neg (sub_pos.mpr hslt) hx)
    (mul_neg_of_pos_of_neg hspos hy)

theorem convexCombination_nonneg {x y s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (1 - s) * x + s * y :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr hs.2) hx) (mul_nonneg hs.1 hy)

theorem convexCombination_nonpos {x y s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hx : x ≤ 0) (hy : y ≤ 0) :
    (1 - s) * x + s * y ≤ 0 :=
  add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs.2) hx)
    (mul_nonpos_of_nonneg_of_nonpos hs.1 hy)

noncomputable def planarBridgeCircleHomotopyMinMax (r : ℝ → Space)
    (u : Space) (a b t s : ℝ) : Space :=
  toLp 2 ![(1 - s) * height r u t + s * bridgeCircleY a b t,
    (1 - s) * directionalUnitTangent r u t + s * bridgeCircleX a b t, 0]

noncomputable def planarBridgeCircleHomotopyMaxMin (r : ℝ → Space)
    (u : Space) (a b t s : ℝ) : Space :=
  toLp 2 ![(1 - s) * height r u t - s * bridgeCircleY a b t,
    (1 - s) * directionalUnitTangent r u t - s * bridgeCircleX a b t, 0]

theorem contDiff_planarBridgeCircleHomotopyMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      planarBridgeCircleHomotopyMinMax r u a b p.1 p.2) := by
  have hh : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => height r u p.1) :=
    (contDiff_height hknot u).comp contDiff_fst
  have hg : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => directionalUnitTangent r u p.1) :=
    (contDiff_directionalUnitTangent hknot u).comp contDiff_fst
  have hX : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => bridgeCircleX a b p.1) :=
    (contDiff_bridgeCircleX ha hab hb).comp contDiff_fst
  have hY : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => bridgeCircleY a b p.1) :=
    (contDiff_bridgeCircleY ha hab hb).comp contDiff_fst
  have honeSub : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => 1 - p.2) := by fun_prop
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [planarBridgeCircleHomotopyMinMax] using
      (honeSub.mul hh).add (contDiff_snd.mul hY)
  · simpa [planarBridgeCircleHomotopyMinMax] using
      (honeSub.mul hg).add (contDiff_snd.mul hX)
  · simpa [planarBridgeCircleHomotopyMinMax] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (0 : ℝ)))

theorem contDiff_planarBridgeCircleHomotopyMaxMin {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      planarBridgeCircleHomotopyMaxMin r u a b p.1 p.2) := by
  have hh : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => height r u p.1) :=
    (contDiff_height hknot u).comp contDiff_fst
  have hg : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => directionalUnitTangent r u p.1) :=
    (contDiff_directionalUnitTangent hknot u).comp contDiff_fst
  have hX : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => bridgeCircleX a b p.1) :=
    (contDiff_bridgeCircleX ha hab hb).comp contDiff_fst
  have hY : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => bridgeCircleY a b p.1) :=
    (contDiff_bridgeCircleY ha hab hb).comp contDiff_fst
  have honeSub : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => 1 - p.2) := by fun_prop
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [planarBridgeCircleHomotopyMaxMin] using
      (honeSub.mul hh).sub (contDiff_snd.mul hY)
  · simpa [planarBridgeCircleHomotopyMaxMin] using
      (honeSub.mul hg).sub (contDiff_snd.mul hX)
  · simpa [planarBridgeCircleHomotopyMaxMin] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (0 : ℝ)))

theorem planarBridgeCircleHomotopyMinMax_zero {r : ℝ → Space}
    (u : Space) (a b t : ℝ) :
    planarBridgeCircleHomotopyMinMax r u a b t 0 = planarBridgeCurve r u t := by
  ext i
  fin_cases i <;> simp [planarBridgeCircleHomotopyMinMax, planarBridgeCurve]

theorem planarBridgeCircleHomotopyMinMax_one {r : ℝ → Space}
    (u : Space) (a b t : ℝ) :
    planarBridgeCircleHomotopyMinMax r u a b t 1 = bridgeCircleMinMax a b t := by
  ext i
  fin_cases i <;> simp [planarBridgeCircleHomotopyMinMax, bridgeCircleMinMax]

theorem planarBridgeCircleHomotopyMaxMin_zero {r : ℝ → Space}
    (u : Space) (a b t : ℝ) :
    planarBridgeCircleHomotopyMaxMin r u a b t 0 = planarBridgeCurve r u t := by
  ext i
  fin_cases i <;> simp [planarBridgeCircleHomotopyMaxMin, planarBridgeCurve]

theorem planarBridgeCircleHomotopyMaxMin_one {r : ℝ → Space}
    (u : Space) (a b t : ℝ) :
    planarBridgeCircleHomotopyMaxMin r u a b t 1 = bridgeCircleMaxMin a b t := by
  ext i
  fin_cases i <;> simp [planarBridgeCircleHomotopyMaxMin, bridgeCircleMaxMin]

theorem periodic_planarBridgeCircleHomotopyMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (a b s : ℝ) :
    Function.Periodic (fun t =>
      planarBridgeCircleHomotopyMinMax r u a b t s) period := by
  intro t
  ext i
  fin_cases i
  · simp [planarBridgeCircleHomotopyMinMax, periodic_height hknot u t,
      periodic_bridgeCircleY a b t]
  · simp [planarBridgeCircleHomotopyMinMax,
      periodic_directionalUnitTangent hknot u t, periodic_bridgeCircleX a b t]
  · simp [planarBridgeCircleHomotopyMinMax]

theorem periodic_planarBridgeCircleHomotopyMaxMin {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) (a b s : ℝ) :
    Function.Periodic (fun t =>
      planarBridgeCircleHomotopyMaxMin r u a b t s) period := by
  intro t
  ext i
  fin_cases i
  · simp [planarBridgeCircleHomotopyMaxMin, periodic_height hknot u t,
      periodic_bridgeCircleY a b t]
  · simp [planarBridgeCircleHomotopyMaxMin,
      periodic_directionalUnitTangent hknot u t, periodic_bridgeCircleX a b t]
  · simp [planarBridgeCircleHomotopyMaxMin]

theorem bridgeCircleX_left {a b : ℝ} : bridgeCircleX a b a = 0 := by
  have harg : a - bridgeMidpoint a b = -bridgeHalfSpan a b := by
    simp [bridgeMidpoint, bridgeHalfSpan]
    ring
  rw [bridgeCircleX, harg, Real.cos_neg]
  simp

theorem bridgeCircleX_right {a b : ℝ} : bridgeCircleX a b b = 0 := by
  have harg : b - bridgeMidpoint a b = bridgeHalfSpan a b := by
    simp [bridgeMidpoint, bridgeHalfSpan]
    ring
  rw [bridgeCircleX, harg]
  simp

theorem bridgeCircleY_left {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) : bridgeCircleY a b a = -1 := by
  have harg : a - bridgeMidpoint a b = -bridgeHalfSpan a b := by
    simp [bridgeMidpoint, bridgeHalfSpan]
    ring
  have hneg : bridgeCircleY a b a < 0 := by
    rw [bridgeCircleY, harg, Real.sin_neg]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (sin_bridgeHalfSpan_pos ha hab hb)
        (neg_neg_of_pos (sin_bridgeHalfSpan_pos ha hab hb)))
      (bridgeDenominator_pos ha hab hb)
  have hsq := bridgeCircle_sq_add_sq (t := a) ha hab hb
  rw [bridgeCircleX_left] at hsq
  norm_num at hsq
  rcases hsq with hsq | hsq
  · linarith
  · exact hsq

theorem bridgeCircleY_right {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) : bridgeCircleY a b b = 1 := by
  have harg : b - bridgeMidpoint a b = bridgeHalfSpan a b := by
    simp [bridgeMidpoint, bridgeHalfSpan]
    ring
  have hpos : 0 < bridgeCircleY a b b := by
    rw [bridgeCircleY, harg]
    exact div_pos (mul_pos (sin_bridgeHalfSpan_pos ha hab hb)
      (sin_bridgeHalfSpan_pos ha hab hb)) (bridgeDenominator_pos ha hab hb)
  have hsq := bridgeCircle_sq_add_sq (t := b) ha hab hb
  rw [bridgeCircleX_right] at hsq
  norm_num at hsq
  rcases hsq with hsq | hsq
  · exact hsq
  · linarith

theorem velocity_planarBridgeCircleHomotopyMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t s : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    velocity (fun z => planarBridgeCircleHomotopyMinMax r u a b z s) t =
      toLp 2 ![(1 - s) * deriv (height r u) t +
          s * (bridgeCircleSpeed a b t * bridgeCircleX a b t),
        (1 - s) * deriv (directionalUnitTangent r u) t -
          s * (bridgeCircleSpeed a b t * bridgeCircleY a b t), 0] := by
  have hheight0 : HasDerivAt (height r u) (deriv (height r u) t) t :=
    (((contDiff_height hknot u).differentiable (by simp)).differentiableAt).hasDerivAt
  have hg0 : HasDerivAt (directionalUnitTangent r u)
      (deriv (directionalUnitTangent r u) t) t :=
    (((contDiff_directionalUnitTangent hknot u).differentiable
      (by simp)).differentiableAt).hasDerivAt
  have hheight := hheight0.const_mul (1 - s)
  have hY := (hasDerivAt_bridgeCircleY (t := t) ha hab hb).const_mul s
  have hg := hg0.const_mul (1 - s)
  have hX := (hasDerivAt_bridgeCircleX (t := t) ha hab hb).const_mul s
  have hcoord0 : HasDerivAt
      (fun z => (1 - s) * height r u z + s * bridgeCircleY a b z)
      ((1 - s) * deriv (height r u) t +
        s * (bridgeCircleSpeed a b t * bridgeCircleX a b t)) t := by
    exact (hheight.add hY).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hcoord1 : HasDerivAt
      (fun z => (1 - s) * directionalUnitTangent r u z +
        s * bridgeCircleX a b z)
      ((1 - s) * deriv (directionalUnitTangent r u) t -
        s * (bridgeCircleSpeed a b t * bridgeCircleY a b t)) t := by
    have h := (hg.add hX).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
    convert h using 1 <;> try rfl
    ring
  have hraw : HasDerivAt
      (fun z : ℝ => ![(1 - s) * height r u z + s * bridgeCircleY a b z,
        (1 - s) * directionalUnitTangent r u z + s * bridgeCircleX a b z, 0])
      ![(1 - s) * deriv (height r u) t +
          s * (bridgeCircleSpeed a b t * bridgeCircleX a b t),
        (1 - s) * deriv (directionalUnitTangent r u) t -
          s * (bridgeCircleSpeed a b t * bridgeCircleY a b t), 0] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hcoord0
    · exact hcoord1
    · simpa using hasDerivAt_const (x := t) (c := (0 : ℝ))
  exact (toLpContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw).deriv

theorem velocity_planarBridgeCircleHomotopyMaxMin {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b t s : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    velocity (fun z => planarBridgeCircleHomotopyMaxMin r u a b z s) t =
      toLp 2 ![(1 - s) * deriv (height r u) t -
          s * (bridgeCircleSpeed a b t * bridgeCircleX a b t),
        (1 - s) * deriv (directionalUnitTangent r u) t +
          s * (bridgeCircleSpeed a b t * bridgeCircleY a b t), 0] := by
  have hheight0 : HasDerivAt (height r u) (deriv (height r u) t) t :=
    (((contDiff_height hknot u).differentiable (by simp)).differentiableAt).hasDerivAt
  have hg0 : HasDerivAt (directionalUnitTangent r u)
      (deriv (directionalUnitTangent r u) t) t :=
    (((contDiff_directionalUnitTangent hknot u).differentiable
      (by simp)).differentiableAt).hasDerivAt
  have hheight := hheight0.const_mul (1 - s)
  have hY := (hasDerivAt_bridgeCircleY (t := t) ha hab hb).const_mul s
  have hg := hg0.const_mul (1 - s)
  have hX := (hasDerivAt_bridgeCircleX (t := t) ha hab hb).const_mul s
  have hcoord0 : HasDerivAt
      (fun z => (1 - s) * height r u z - s * bridgeCircleY a b z)
      ((1 - s) * deriv (height r u) t -
        s * (bridgeCircleSpeed a b t * bridgeCircleX a b t)) t := by
    exact (hheight.sub hY).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hcoord1 : HasDerivAt
      (fun z => (1 - s) * directionalUnitTangent r u z -
        s * bridgeCircleX a b z)
      ((1 - s) * deriv (directionalUnitTangent r u) t +
        s * (bridgeCircleSpeed a b t * bridgeCircleY a b t)) t := by
    have h := (hg.sub hX).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
    convert h using 1 <;> try rfl
    ring
  have hraw : HasDerivAt
      (fun z : ℝ => ![(1 - s) * height r u z - s * bridgeCircleY a b z,
        (1 - s) * directionalUnitTangent r u z - s * bridgeCircleX a b z, 0])
      ![(1 - s) * deriv (height r u) t -
          s * (bridgeCircleSpeed a b t * bridgeCircleX a b t),
        (1 - s) * deriv (directionalUnitTangent r u) t +
          s * (bridgeCircleSpeed a b t * bridgeCircleY a b t), 0] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hcoord0
    · exact hcoord1
    · simpa using hasDerivAt_const (x := t) (c := (0 : ℝ))
  exact (toLpContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw).deriv

theorem injOn_phasePair_of_two_monotone_arcs {f g : ℝ → ℝ} {a b : ℝ}
    (ha : a ∈ Ico (0 : ℝ) period) (hfper : Function.Periodic f period)
    (hgper : Function.Periodic g period)
    (hmono : StrictMonoOn f (Icc a b))
    (hanti : StrictAntiOn f (Icc b (a + period)))
    (hpos : ∀ z ∈ Ioo a b, 0 < g z)
    (hneg : ∀ z ∈ Ioo b (a + period), g z < 0)
    (hga : g a = 0) (hgb : g b = 0) :
    Set.InjOn (fun t => (f t, g t)) (Ico (0 : ℝ) period) := by
  intro x hx y hy hxy
  let x' := periodLift a x
  let y' := periodLift a y
  have hx' : x' ∈ Ico a (a + period) := periodLift_mem_Ico ha hx
  have hy' : y' ∈ Ico a (a + period) := periodLift_mem_Ico ha hy
  have hfx : f x' = f x := by
    dsimp [x']
    rw [periodLift]
    split_ifs
    · exact hfper x
    · rfl
  have hfy : f y' = f y := by
    dsimp [y']
    rw [periodLift]
    split_ifs
    · exact hfper y
    · rfl
  have hgx : g x' = g x := by
    dsimp [x']
    rw [periodLift]
    split_ifs
    · exact hgper x
    · rfl
  have hgy : g y' = g y := by
    dsimp [y']
    rw [periodLift]
    split_ifs
    · exact hgper y
    · rfl
  have hfxy : f x' = f y' := by
    rw [hfx, hfy]
    exact congrArg Prod.fst hxy
  have hgxy : g x' = g y' := by
    rw [hgx, hgy]
    exact congrArg Prod.snd hxy
  have hrecover (h : x' = y') : x = y :=
    periodLift_injective_on_Ico ha hx hy h
  by_cases hxb : x' ≤ b
  · by_cases hyb : y' ≤ b
    · apply hrecover
      exact hmono.injOn ⟨hx'.1, hxb⟩ ⟨hy'.1, hyb⟩ hfxy
    · have hygt : b < y' := lt_of_not_ge hyb
      have hgyneg : g y' < 0 := hneg y' ⟨hygt, hy'.2⟩
      have hgxnonneg : 0 ≤ g x' := by
        rcases eq_or_lt_of_le hx'.1 with hxa | hxa
        · rw [← hxa, hga]
        rcases eq_or_lt_of_le hxb with hxb' | hxb'
        · rw [hxb', hgb]
        · exact (hpos x' ⟨hxa, hxb'⟩).le
      linarith
  · have hxgt : b < x' := lt_of_not_ge hxb
    by_cases hyb : y' ≤ b
    · have hgxneg : g x' < 0 := hneg x' ⟨hxgt, hx'.2⟩
      have hgynonneg : 0 ≤ g y' := by
        rcases eq_or_lt_of_le hy'.1 with hya | hya
        · rw [← hya, hga]
        rcases eq_or_lt_of_le hyb with hyb' | hyb'
        · rw [hyb', hgb]
        · exact (hpos y' ⟨hya, hyb'⟩).le
      linarith
    · apply hrecover
      exact hanti.injOn ⟨hxgt.le, hx'.2.le⟩
        ⟨(lt_of_not_ge hyb).le, hy'.2.le⟩ hfxy

theorem injOn_planarBridgeCircleHomotopyMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b s : ℝ}
    (ha : a ∈ Ico (0 : ℝ) period) (hb : b ∈ Ico (0 : ℝ) period)
    (hab : a < b) (hs : s ∈ Icc (0 : ℝ) 1)
    (hmono : StrictMonoOn (height r u) (Icc a b))
    (hanti : StrictAntiOn (height r u) (Icc b (a + period)))
    (hpos : ∀ z ∈ Ioo a b, 0 < directionalUnitTangent r u z)
    (hneg : ∀ z ∈ Ioo b (a + period), directionalUnitTangent r u z < 0)
    (hga : directionalUnitTangent r u a = 0)
    (hgb : directionalUnitTangent r u b = 0) :
    Set.InjOn (fun t => planarBridgeCircleHomotopyMinMax r u a b t s)
      (Ico (0 : ℝ) period) := by
  let f := fun t => (1 - s) * height r u t + s * bridgeCircleY a b t
  let g := fun t => (1 - s) * directionalUnitTangent r u t +
    s * bridgeCircleX a b t
  have hfper : Function.Periodic f period := by
    intro t
    simp [f, periodic_height hknot u t, periodic_bridgeCircleY a b t]
  have hgper : Function.Periodic g period := by
    intro t
    simp [g, periodic_directionalUnitTangent hknot u t,
      periodic_bridgeCircleX a b t]
  have hfmono : StrictMonoOn f (Icc a b) := by
    exact strictMonoOn_convexCombination hs hmono
      (strictMonoOn_bridgeCircleY_Icc ha.1 hab hb.2)
  have hfanti : StrictAntiOn f (Icc b (a + period)) := by
    exact strictAntiOn_convexCombination hs hanti
      (strictAntiOn_bridgeCircleY_wrap ha.1 hab hb.2)
  have hgpos : ∀ z ∈ Ioo a b, 0 < g z := by
    intro z hz
    exact convexCombination_pos hs (hpos z hz)
      (bridgeCircleX_pos_of_mem_Ioo ha.1 hab hb.2 hz)
  have hgneg : ∀ z ∈ Ioo b (a + period), g z < 0 := by
    intro z hz
    exact convexCombination_neg hs (hneg z hz)
      (bridgeCircleX_neg_of_mem_wrap ha.1 hab hb.2 hz)
  have hga' : g a = 0 := by simp [g, hga, bridgeCircleX_left]
  have hgb' : g b = 0 := by simp [g, hgb, bridgeCircleX_right]
  have hpair := injOn_phasePair_of_two_monotone_arcs ha hfper hgper
    hfmono hfanti hgpos hgneg hga' hgb'
  intro x hx y hy hxy
  apply hpair hx hy
  apply Prod.ext
  · simpa [f, planarBridgeCircleHomotopyMinMax] using
      congrArg (fun v : Space => v 0) hxy
  · simpa [g, planarBridgeCircleHomotopyMinMax] using
      congrArg (fun v : Space => v 1) hxy

theorem injOn_planarBridgeCircleHomotopyMaxMin {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b s : ℝ}
    (ha : a ∈ Ico (0 : ℝ) period) (hb : b ∈ Ico (0 : ℝ) period)
    (hab : a < b) (hs : s ∈ Icc (0 : ℝ) 1)
    (hanti : StrictAntiOn (height r u) (Icc a b))
    (hmono : StrictMonoOn (height r u) (Icc b (a + period)))
    (hneg : ∀ z ∈ Ioo a b, directionalUnitTangent r u z < 0)
    (hpos : ∀ z ∈ Ioo b (a + period), 0 < directionalUnitTangent r u z)
    (hga : directionalUnitTangent r u a = 0)
    (hgb : directionalUnitTangent r u b = 0) :
    Set.InjOn (fun t => planarBridgeCircleHomotopyMaxMin r u a b t s)
      (Ico (0 : ℝ) period) := by
  let f := fun t => -((1 - s) * height r u t - s * bridgeCircleY a b t)
  let g := fun t => -((1 - s) * directionalUnitTangent r u t -
    s * bridgeCircleX a b t)
  have hfper : Function.Periodic f period := by
    intro t
    simp [f, periodic_height hknot u t, periodic_bridgeCircleY a b t]
  have hgper : Function.Periodic g period := by
    intro t
    simp [g, periodic_directionalUnitTangent hknot u t,
      periodic_bridgeCircleX a b t]
  have hnegHeight : StrictMonoOn (fun t => -height r u t) (Icc a b) := by
    intro x hx y hy hxy
    exact neg_lt_neg (hanti hx hy hxy)
  have hnegHeightWrap : StrictAntiOn (fun t => -height r u t)
      (Icc b (a + period)) := by
    intro x hx y hy hxy
    exact neg_lt_neg (hmono hx hy hxy)
  have hfmono : StrictMonoOn f (Icc a b) := by
    intro x hx y hy hxy
    have h := strictMonoOn_convexCombination hs hnegHeight
      (strictMonoOn_bridgeCircleY_Icc ha.1 hab hb.2) hx hy hxy
    dsimp [f] at *
    linarith
  have hfanti : StrictAntiOn f (Icc b (a + period)) := by
    intro x hx y hy hxy
    have h := strictAntiOn_convexCombination hs hnegHeightWrap
      (strictAntiOn_bridgeCircleY_wrap ha.1 hab hb.2) hx hy hxy
    dsimp [f] at *
    linarith
  have hgpos : ∀ z ∈ Ioo a b, 0 < g z := by
    intro z hz
    have := convexCombination_pos hs (neg_pos.mpr (hneg z hz))
      (bridgeCircleX_pos_of_mem_Ioo ha.1 hab hb.2 hz)
    simpa [g, mul_neg, neg_sub] using this
  have hgneg : ∀ z ∈ Ioo b (a + period), g z < 0 := by
    intro z hz
    have := convexCombination_neg hs (neg_neg_of_pos (hpos z hz))
      (bridgeCircleX_neg_of_mem_wrap ha.1 hab hb.2 hz)
    simpa [g, mul_neg, neg_sub] using this
  have hga' : g a = 0 := by simp [g, hga, bridgeCircleX_left]
  have hgb' : g b = 0 := by simp [g, hgb, bridgeCircleX_right]
  have hpair := injOn_phasePair_of_two_monotone_arcs ha hfper hgper
    hfmono hfanti hgpos hgneg hga' hgb'
  intro x hx y hy hxy
  apply hpair hx hy
  apply Prod.ext
  · have h0 := congrArg (fun v : Space => v 0) hxy
    have h0' : (1 - s) * height r u x - s * bridgeCircleY a b x =
        (1 - s) * height r u y - s * bridgeCircleY a b y := by
      simpa [planarBridgeCircleHomotopyMaxMin] using h0
    dsimp [f]
    rw [h0']
  · have h1 := congrArg (fun v : Space => v 1) hxy
    have h1' : (1 - s) * directionalUnitTangent r u x -
        s * bridgeCircleX a b x =
        (1 - s) * directionalUnitTangent r u y -
          s * bridgeCircleX a b y := by
      simpa [planarBridgeCircleHomotopyMaxMin] using h1
    dsimp [g]
    rw [h1']

theorem regular_planarBridgeCircleHomotopyMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b s : ℝ}
    (ha : a ∈ Ico (0 : ℝ) period) (hb : b ∈ Ico (0 : ℝ) period)
    (hab : a < b) (hs : s ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ z ∈ Ioo a b, 0 < directionalUnitTangent r u z)
    (hneg : ∀ z ∈ Ioo b (a + period), directionalUnitTangent r u z < 0)
    (hda : 0 < deriv (directionalUnitTangent r u) a)
    (hdb : deriv (directionalUnitTangent r u) b < 0) :
    ∀ t, velocity (fun z =>
      planarBridgeCircleHomotopyMinMax r u a b z s) t ≠ 0 := by
  let c := fun z => planarBridgeCircleHomotopyMinMax r u a b z s
  have hcper : Function.Periodic c period :=
    periodic_planarBridgeCircleHomotopyMinMax hknot u a b s
  have hvper : Function.Periodic (velocity c) period := by
    simpa [velocity] using periodic_deriv hcper
  have hp : 0 < period := by simp [period, Real.pi_pos]
  intro t hzero
  obtain ⟨z, hz, htz⟩ := hvper.exists_mem_Ico hp t a
  have hzeroz : velocity c z = 0 := by rw [← htz]; exact hzero
  have hcoord0 : (1 - s) * deriv (height r u) z +
      s * (bridgeCircleSpeed a b z * bridgeCircleX a b z) = 0 := by
    simpa [c, velocity_planarBridgeCircleHomotopyMinMax hknot u ha.1 hab hb.2] using
      congrArg (fun v : Space => v 0) hzeroz
  have hcoord1 : (1 - s) * deriv (directionalUnitTangent r u) z -
      s * (bridgeCircleSpeed a b z * bridgeCircleY a b z) = 0 := by
    simpa [c, velocity_planarBridgeCircleHomotopyMinMax hknot u ha.1 hab hb.2] using
      congrArg (fun v : Space => v 1) hzeroz
  by_cases hzb : z ≤ b
  · rcases eq_or_lt_of_le hz.1 with hza | hza
    · subst z
      have hmodel : 0 < bridgeCircleSpeed a b a :=
        bridgeCircleSpeed_pos ha.1 hab hb.2
      have hcomb := convexCombination_pos hs hda hmodel
      rw [bridgeCircleY_left ha.1 hab hb.2] at hcoord1
      linarith
    rcases eq_or_lt_of_le hzb with hzb | hzb
    · subst z
      have hmodel : -bridgeCircleSpeed a b b < 0 :=
        neg_neg_of_pos (bridgeCircleSpeed_pos ha.1 hab hb.2)
      have hcomb := convexCombination_neg hs hdb hmodel
      rw [bridgeCircleY_right ha.1 hab hb.2] at hcoord1
      linarith
    · have hgpos := hpos z ⟨hza, hzb⟩
      have hheightPos : 0 < deriv (height r u) z := by
        rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u z]
        exact mul_pos (speed_pos hknot z) hgpos
      have hmodelPos : 0 < bridgeCircleSpeed a b z * bridgeCircleX a b z :=
        mul_pos (bridgeCircleSpeed_pos ha.1 hab hb.2)
          (bridgeCircleX_pos_of_mem_Ioo ha.1 hab hb.2 ⟨hza, hzb⟩)
      have hcomb := convexCombination_pos hs hheightPos hmodelPos
      linarith
  · have hzb' : b < z := lt_of_not_ge hzb
    have hztop : z < a + period := hz.2
    have hgneg := hneg z ⟨hzb', hztop⟩
    have hheightNeg : deriv (height r u) z < 0 := by
      rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u z]
      exact mul_neg_of_pos_of_neg (speed_pos hknot z) hgneg
    have hmodelNeg : bridgeCircleSpeed a b z * bridgeCircleX a b z < 0 :=
      mul_neg_of_pos_of_neg (bridgeCircleSpeed_pos ha.1 hab hb.2)
        (bridgeCircleX_neg_of_mem_wrap ha.1 hab hb.2 ⟨hzb', hztop⟩)
    have hcomb := convexCombination_neg hs hheightNeg hmodelNeg
    linarith

theorem regular_planarBridgeCircleHomotopyMaxMin {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b s : ℝ}
    (ha : a ∈ Ico (0 : ℝ) period) (hb : b ∈ Ico (0 : ℝ) period)
    (hab : a < b) (hs : s ∈ Icc (0 : ℝ) 1)
    (hneg : ∀ z ∈ Ioo a b, directionalUnitTangent r u z < 0)
    (hpos : ∀ z ∈ Ioo b (a + period), 0 < directionalUnitTangent r u z)
    (hda : deriv (directionalUnitTangent r u) a < 0)
    (hdb : 0 < deriv (directionalUnitTangent r u) b) :
    ∀ t, velocity (fun z =>
      planarBridgeCircleHomotopyMaxMin r u a b z s) t ≠ 0 := by
  let c := fun z => planarBridgeCircleHomotopyMaxMin r u a b z s
  have hcper : Function.Periodic c period :=
    periodic_planarBridgeCircleHomotopyMaxMin hknot u a b s
  have hvper : Function.Periodic (velocity c) period := by
    simpa [velocity] using periodic_deriv hcper
  have hp : 0 < period := by simp [period, Real.pi_pos]
  intro t hzero
  obtain ⟨z, hz, htz⟩ := hvper.exists_mem_Ico hp t a
  have hzeroz : velocity c z = 0 := by rw [← htz]; exact hzero
  have hcoord0 : (1 - s) * deriv (height r u) z -
      s * (bridgeCircleSpeed a b z * bridgeCircleX a b z) = 0 := by
    simpa [c, velocity_planarBridgeCircleHomotopyMaxMin hknot u ha.1 hab hb.2] using
      congrArg (fun v : Space => v 0) hzeroz
  have hcoord1 : (1 - s) * deriv (directionalUnitTangent r u) z +
      s * (bridgeCircleSpeed a b z * bridgeCircleY a b z) = 0 := by
    simpa [c, velocity_planarBridgeCircleHomotopyMaxMin hknot u ha.1 hab hb.2] using
      congrArg (fun v : Space => v 1) hzeroz
  by_cases hzb : z ≤ b
  · rcases eq_or_lt_of_le hz.1 with hza | hza
    · subst z
      have hmodel : -bridgeCircleSpeed a b a < 0 :=
        neg_neg_of_pos (bridgeCircleSpeed_pos ha.1 hab hb.2)
      have hcomb := convexCombination_neg hs hda hmodel
      rw [bridgeCircleY_left ha.1 hab hb.2] at hcoord1
      linarith
    rcases eq_or_lt_of_le hzb with hzb | hzb
    · subst z
      have hmodel : 0 < bridgeCircleSpeed a b b :=
        bridgeCircleSpeed_pos ha.1 hab hb.2
      have hcomb := convexCombination_pos hs hdb hmodel
      rw [bridgeCircleY_right ha.1 hab hb.2] at hcoord1
      linarith
    · have hgneg := hneg z ⟨hza, hzb⟩
      have hheightNeg : deriv (height r u) z < 0 := by
        rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u z]
        exact mul_neg_of_pos_of_neg (speed_pos hknot z) hgneg
      have hmodelNeg : -(bridgeCircleSpeed a b z * bridgeCircleX a b z) < 0 :=
        neg_neg_of_pos (mul_pos (bridgeCircleSpeed_pos ha.1 hab hb.2)
          (bridgeCircleX_pos_of_mem_Ioo ha.1 hab hb.2 ⟨hza, hzb⟩))
      have hcomb := convexCombination_neg hs hheightNeg hmodelNeg
      linarith
  · have hzb' : b < z := lt_of_not_ge hzb
    have hztop : z < a + period := hz.2
    have hgpos := hpos z ⟨hzb', hztop⟩
    have hheightPos : 0 < deriv (height r u) z := by
      rw [deriv_height_eq_speed_mul_directionalUnitTangent hknot u z]
      exact mul_pos (speed_pos hknot z) hgpos
    have hmodelPos : 0 < -(bridgeCircleSpeed a b z * bridgeCircleX a b z) :=
      neg_pos.mpr (mul_neg_of_pos_of_neg (bridgeCircleSpeed_pos ha.1 hab hb.2)
        (bridgeCircleX_neg_of_mem_wrap ha.1 hab hb.2 ⟨hzb', hztop⟩))
    have hcomb := convexCombination_pos hs hheightPos hmodelPos
    linarith

theorem isSmoothKnot_planarBridgeCircleHomotopyMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b s : ℝ}
    (ha : a ∈ Ico (0 : ℝ) period) (hb : b ∈ Ico (0 : ℝ) period)
    (hab : a < b) (hs : s ∈ Icc (0 : ℝ) 1)
    (hmono : StrictMonoOn (height r u) (Icc a b))
    (hanti : StrictAntiOn (height r u) (Icc b (a + period)))
    (hpos : ∀ z ∈ Ioo a b, 0 < directionalUnitTangent r u z)
    (hneg : ∀ z ∈ Ioo b (a + period), directionalUnitTangent r u z < 0)
    (hga : directionalUnitTangent r u a = 0)
    (hgb : directionalUnitTangent r u b = 0)
    (hda : 0 < deriv (directionalUnitTangent r u) a)
    (hdb : deriv (directionalUnitTangent r u) b < 0) :
    IsSmoothKnot (fun t =>
      planarBridgeCircleHomotopyMinMax r u a b t s) where
  smooth := (contDiff_planarBridgeCircleHomotopyMinMax hknot u ha.1 hab hb.2).comp
    (contDiff_id.prodMk
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => s)))
  periodic := periodic_planarBridgeCircleHomotopyMinMax hknot u a b s
  injective_on_period := injOn_planarBridgeCircleHomotopyMinMax hknot u
    ha hb hab hs hmono hanti hpos hneg hga hgb
  regular := regular_planarBridgeCircleHomotopyMinMax hknot u
    ha hb hab hs hpos hneg hda hdb

theorem isSmoothKnot_planarBridgeCircleHomotopyMaxMin {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b s : ℝ}
    (ha : a ∈ Ico (0 : ℝ) period) (hb : b ∈ Ico (0 : ℝ) period)
    (hab : a < b) (hs : s ∈ Icc (0 : ℝ) 1)
    (hanti : StrictAntiOn (height r u) (Icc a b))
    (hmono : StrictMonoOn (height r u) (Icc b (a + period)))
    (hneg : ∀ z ∈ Ioo a b, directionalUnitTangent r u z < 0)
    (hpos : ∀ z ∈ Ioo b (a + period), 0 < directionalUnitTangent r u z)
    (hga : directionalUnitTangent r u a = 0)
    (hgb : directionalUnitTangent r u b = 0)
    (hda : deriv (directionalUnitTangent r u) a < 0)
    (hdb : 0 < deriv (directionalUnitTangent r u) b) :
    IsSmoothKnot (fun t =>
      planarBridgeCircleHomotopyMaxMin r u a b t s) where
  smooth := (contDiff_planarBridgeCircleHomotopyMaxMin hknot u ha.1 hab hb.2).comp
    (contDiff_id.prodMk
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => s)))
  periodic := periodic_planarBridgeCircleHomotopyMaxMin hknot u a b s
  injective_on_period := injOn_planarBridgeCircleHomotopyMaxMin hknot u
    ha hb hab hs hanti hmono hneg hpos hga hgb
  regular := regular_planarBridgeCircleHomotopyMaxMin hknot u
    ha hb hab hs hneg hpos hda hdb

theorem directionalUnitTangent_ne_zero_between_of_intersections_eq_pair
    {r : ℝ → Space} {u : Space} {a b : ℝ}
    (haS : a ∈ tangentGreatCircleIntersections r u)
    (hbS : b ∈ tangentGreatCircleIntersections r u) (hab : a < b)
    (hpair : tangentGreatCircleIntersections r u = {a, b}) :
    ∀ z ∈ Ioo a b, directionalUnitTangent r u z ≠ 0 := by
  intro z hz hz0
  have hzIco : z ∈ Ico (0 : ℝ) period :=
    ⟨haS.1.1.trans hz.1.le, hz.2.trans hbS.1.2⟩
  have hzS : z ∈ tangentGreatCircleIntersections r u := ⟨hzIco, hz0⟩
  rw [hpair] at hzS
  rcases hzS with rfl | hzS
  · exact (lt_irrefl _ hz.1)
  · have : z = b := by simpa using hzS
    subst z
    exact (lt_irrefl _ hz.2)

theorem directionalUnitTangent_ne_zero_wrap_of_intersections_eq_pair
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {u : Space} {a b : ℝ}
    (haS : a ∈ tangentGreatCircleIntersections r u)
    (hbS : b ∈ tangentGreatCircleIntersections r u) (hab : a < b)
    (hpair : tangentGreatCircleIntersections r u = {a, b}) :
    ∀ z ∈ Ioo b (a + period), directionalUnitTangent r u z ≠ 0 := by
  intro z hz hz0
  by_cases hzp : z < period
  · have hzIco : z ∈ Ico (0 : ℝ) period :=
      ⟨hbS.1.1.trans hz.1.le, hzp⟩
    have hzS : z ∈ tangentGreatCircleIntersections r u := ⟨hzIco, hz0⟩
    rw [hpair] at hzS
    rcases hzS with hzS | hzS
    · have : z = a := by simpa using hzS
      exact (not_lt_of_ge hab.le) (this ▸ hz.1)
    · have : z = b := by simpa using hzS
      exact (lt_irrefl _ (this ▸ hz.1))
  · have hpz : period ≤ z := le_of_not_gt hzp
    let z' := z - period
    have hz'zero : directionalUnitTangent r u z' = 0 := by
      have hper := periodic_directionalUnitTangent hknot u z'
      have hz'eq : z' + period = z := by dsimp [z']; ring
      rw [hz'eq] at hper
      rw [← hper]
      exact hz0
    have hz'Ico : z' ∈ Ico (0 : ℝ) period := by
      constructor
      · dsimp [z']
        linarith
      · dsimp [z']
        linarith [hz.2, haS.1.2]
    have hz'S : z' ∈ tangentGreatCircleIntersections r u := ⟨hz'Ico, hz'zero⟩
    rw [hpair] at hz'S
    have hz'lt : z' < a := by
      dsimp [z']
      linarith [hz.2]
    rcases hz'S with hz'S | hz'S
    · have : z' = a := by simpa using hz'S
      exact (lt_irrefl _ (this ▸ hz'lt))
    · have : z' = b := by simpa using hz'S
      exact (not_lt_of_ge hab.le) (this ▸ hz'lt)

structure MinMaxBridgeData (r : ℝ → Space) (u : Space) (a b : ℝ) : Prop where
  left_mem : a ∈ Ico (0 : ℝ) period
  right_mem : b ∈ Ico (0 : ℝ) period
  left_lt_right : a < b
  height_mono : StrictMonoOn (height r u) (Icc a b)
  height_anti_wrap : StrictAntiOn (height r u) (Icc b (a + period))
  tangent_pos : ∀ z ∈ Ioo a b, 0 < directionalUnitTangent r u z
  tangent_neg_wrap : ∀ z ∈ Ioo b (a + period), directionalUnitTangent r u z < 0
  tangent_left : directionalUnitTangent r u a = 0
  tangent_right : directionalUnitTangent r u b = 0
  tangent_deriv_left : 0 < deriv (directionalUnitTangent r u) a
  tangent_deriv_right : deriv (directionalUnitTangent r u) b < 0

structure MaxMinBridgeData (r : ℝ → Space) (u : Space) (a b : ℝ) : Prop where
  left_mem : a ∈ Ico (0 : ℝ) period
  right_mem : b ∈ Ico (0 : ℝ) period
  left_lt_right : a < b
  height_anti : StrictAntiOn (height r u) (Icc a b)
  height_mono_wrap : StrictMonoOn (height r u) (Icc b (a + period))
  tangent_neg : ∀ z ∈ Ioo a b, directionalUnitTangent r u z < 0
  tangent_pos_wrap : ∀ z ∈ Ioo b (a + period), 0 < directionalUnitTangent r u z
  tangent_left : directionalUnitTangent r u a = 0
  tangent_right : directionalUnitTangent r u b = 0
  tangent_deriv_left : deriv (directionalUnitTangent r u) a < 0
  tangent_deriv_right : 0 < deriv (directionalUnitTangent r u) b

theorem exists_bridgeOrientationData_of_ncard_intersections_eq_two
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    (hgeneric : IsNondegenerateDirection r u)
    (hcard : (tangentGreatCircleIntersections r u).ncard = 2) :
    (∃ a b, MinMaxBridgeData r u a b) ∨
      (∃ a b, MaxMinBridgeData r u a b) := by
  obtain ⟨tmax, tmin, hne, htmax, htmin, hset, hmax, hmin, harcs⟩ :=
    exists_two_monotone_height_arcs_of_ncard_intersections_eq_two
      hknot u hgeneric hcard
  let S := tangentGreatCircleIntersections r u
  have hsetS : S = {tmax, tmin} := by simpa [S] using hset
  have htmaxS : tmax ∈ S := by rw [hsetS]; simp
  have htminS : tmin ∈ S := by rw [hsetS]; simp
  have htmaxIcc : tmax ∈ tangentGreatCircleIntersectionsIcc r u :=
    ⟨⟨htmax.1, htmax.2.le⟩, htmaxS.2⟩
  have htminIcc : tmin ∈ tangentGreatCircleIntersectionsIcc r u :=
    ⟨⟨htmin.1, htmin.2.le⟩, htminS.2⟩
  have hmaxDeriv : deriv (directionalUnitTangent r u) tmax < 0 := by
    rw [(hasDerivAt_directionalUnitTangent hknot u tmax).deriv]
    exact inner_deriv_unitTangent_neg_of_isLocalMax_height
      hknot u hgeneric htmaxIcc hmax
  have hminDeriv : 0 < deriv (directionalUnitTangent r u) tmin := by
    rw [(hasDerivAt_directionalUnitTangent hknot u tmin).deriv]
    exact inner_deriv_unitTangent_pos_of_isLocalMin_height
      hknot u hgeneric htminIcc hmin
  rcases harcs with hminmax | hmaxmin
  · rcases hminmax with ⟨hminmax, hmono, hanti⟩
    have hsetSwap : tangentGreatCircleIntersections r u = {tmin, tmax} := by
      simpa [Set.pair_comm] using hset
    have hnoOrd := directionalUnitTangent_ne_zero_between_of_intersections_eq_pair
      (r := r) (u := u) htminS htmaxS hminmax hsetSwap
    have hnoWrap := directionalUnitTangent_ne_zero_wrap_of_intersections_eq_pair
      hknot htminS htmaxS hminmax hsetSwap
    have hpos : ∀ z ∈ Ioo tmin tmax, 0 < directionalUnitTangent r u z :=
      pos_on_Ioo_of_deriv_pos_of_no_zeros
        (continuous_directionalUnitTangent hknot u) hminmax htminS.2 hminDeriv hnoOrd
    have hneg : ∀ z ∈ Ioo tmax (tmin + period),
        directionalUnitTangent r u z < 0 :=
      neg_on_Ioo_of_deriv_neg_of_no_zeros
        (continuous_directionalUnitTangent hknot u)
        (by linarith [htmax.2, htmin.1]) htmaxS.2 hmaxDeriv hnoWrap
    exact Or.inl ⟨tmin, tmax, {
      left_mem := htmin
      right_mem := htmax
      left_lt_right := hminmax
      height_mono := hmono
      height_anti_wrap := hanti
      tangent_pos := hpos
      tangent_neg_wrap := hneg
      tangent_left := htminS.2
      tangent_right := htmaxS.2
      tangent_deriv_left := hminDeriv
      tangent_deriv_right := hmaxDeriv }⟩
  · rcases hmaxmin with ⟨hmaxmin, hanti, hmono⟩
    have hnoOrd := directionalUnitTangent_ne_zero_between_of_intersections_eq_pair
      (r := r) (u := u) htmaxS htminS hmaxmin hset
    have hnoWrap := directionalUnitTangent_ne_zero_wrap_of_intersections_eq_pair
      hknot htmaxS htminS hmaxmin hset
    have hneg : ∀ z ∈ Ioo tmax tmin, directionalUnitTangent r u z < 0 :=
      neg_on_Ioo_of_deriv_neg_of_no_zeros
        (continuous_directionalUnitTangent hknot u) hmaxmin htmaxS.2 hmaxDeriv hnoOrd
    have hpos : ∀ z ∈ Ioo tmin (tmax + period),
        0 < directionalUnitTangent r u z :=
      pos_on_Ioo_of_deriv_pos_of_no_zeros
        (continuous_directionalUnitTangent hknot u)
        (by linarith [htmin.2, htmax.1]) htminS.2 hminDeriv hnoWrap
    exact Or.inr ⟨tmax, tmin, {
      left_mem := htmax
      right_mem := htmin
      left_lt_right := hmaxmin
      height_anti := hanti
      height_mono_wrap := hmono
      tangent_neg := hneg
      tangent_pos_wrap := hpos
      tangent_left := htmaxS.2
      tangent_right := htminS.2
      tangent_deriv_left := hmaxDeriv
      tangent_deriv_right := hminDeriv }⟩

noncomputable def isotopyWeight (s : ℝ) : ℝ :=
  (1 - s) ^ 2 / ((1 - s) ^ 2 + s ^ 2)

theorem isotopyWeight_den_pos (s : ℝ) : 0 < (1 - s) ^ 2 + s ^ 2 := by
  by_cases hs : s = 0
  · subst s
    norm_num
  · have hs2 : 0 < s ^ 2 := by positivity
    nlinarith [sq_nonneg (1 - s)]

theorem isotopyWeight_nonneg (s : ℝ) : 0 ≤ isotopyWeight s := by
  exact div_nonneg (sq_nonneg _) (isotopyWeight_den_pos s).le

theorem isotopyWeight_le_one (s : ℝ) : isotopyWeight s ≤ 1 := by
  rw [isotopyWeight, div_le_one (isotopyWeight_den_pos s)]
  exact le_add_of_nonneg_right (sq_nonneg s)

@[simp] theorem isotopyWeight_zero : isotopyWeight 0 = 1 := by
  norm_num [isotopyWeight]

@[simp] theorem isotopyWeight_one : isotopyWeight 1 = 0 := by
  norm_num [isotopyWeight]

theorem contDiff_isotopyWeight : ContDiff ℝ ⊤ isotopyWeight := by
  unfold isotopyWeight
  have hnum : ContDiff ℝ ⊤ (fun s : ℝ => (1 - s) ^ 2) := by fun_prop
  have hden : ContDiff ℝ ⊤ (fun s : ℝ => (1 - s) ^ 2 + s ^ 2) := by fun_prop
  exact hnum.div hden fun s => (isotopyWeight_den_pos s).ne'

noncomputable def movingCircleParameter (a b s : ℝ) : ℝ :=
  isotopyWeight s * Real.cos (bridgeHalfSpan a b)

noncomputable def movingCircleCenter (a b s : ℝ) : ℝ :=
  isotopyWeight s * bridgeMidpoint a b

noncomputable def movingCircleRoot (a b s : ℝ) : ℝ :=
  Real.sqrt (1 - movingCircleParameter a b s ^ 2)

noncomputable def movingCircleDenominator (a b t s : ℝ) : ℝ :=
  1 - movingCircleParameter a b s * Real.cos (t - movingCircleCenter a b s)

noncomputable def movingCircleX (a b t s : ℝ) : ℝ :=
  (Real.cos (t - movingCircleCenter a b s) - movingCircleParameter a b s) /
    movingCircleDenominator a b t s

noncomputable def movingCircleY (a b t s : ℝ) : ℝ :=
  movingCircleRoot a b s * Real.sin (t - movingCircleCenter a b s) /
    movingCircleDenominator a b t s

noncomputable def movingCircleSpeed (a b t s : ℝ) : ℝ :=
  movingCircleRoot a b s / movingCircleDenominator a b t s

theorem abs_movingCircleParameter_lt_one {a b s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    |movingCircleParameter a b s| < 1 := by
  rw [movingCircleParameter, abs_mul, abs_of_nonneg (isotopyWeight_nonneg s)]
  calc
    isotopyWeight s * |Real.cos (bridgeHalfSpan a b)|
        ≤ 1 * |Real.cos (bridgeHalfSpan a b)| := by
          gcongr
          exact isotopyWeight_le_one s
    _ < 1 := by simpa using abs_cos_bridgeHalfSpan_lt_one ha hab hb

theorem movingCircleRadicand_pos {a b s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    0 < 1 - movingCircleParameter a b s ^ 2 := by
  rw [sub_pos, sq_lt_one_iff_abs_lt_one]
  exact abs_movingCircleParameter_lt_one ha hab hb

theorem movingCircleRoot_pos {a b s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    0 < movingCircleRoot a b s := by
  exact Real.sqrt_pos.2 (movingCircleRadicand_pos ha hab hb)

theorem movingCircleDenominator_pos {a b t s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    0 < movingCircleDenominator a b t s := by
  have hc := abs_movingCircleParameter_lt_one (s := s) ha hab hb
  have ht : |Real.cos (t - movingCircleCenter a b s)| ≤ 1 := Real.abs_cos_le_one _
  have hmul : movingCircleParameter a b s *
      Real.cos (t - movingCircleCenter a b s) < 1 := by
    calc
      movingCircleParameter a b s * Real.cos (t - movingCircleCenter a b s)
          ≤ |movingCircleParameter a b s| *
              |Real.cos (t - movingCircleCenter a b s)| := by
            rw [← abs_mul]
            exact le_abs_self _
      _ ≤ |movingCircleParameter a b s| * 1 := by gcongr
      _ < 1 := by simpa using hc
  simpa [movingCircleDenominator] using sub_pos.mpr hmul

theorem movingCircleSpeed_pos {a b t s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    0 < movingCircleSpeed a b t s :=
  div_pos (movingCircleRoot_pos ha hab hb)
    (movingCircleDenominator_pos ha hab hb)

theorem movingCircle_sq_add_sq {a b t s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    movingCircleX a b t s ^ 2 + movingCircleY a b t s ^ 2 = 1 := by
  have hden := (movingCircleDenominator_pos (t := t) (s := s) ha hab hb).ne'
  have hroot : movingCircleRoot a b s ^ 2 =
      1 - movingCircleParameter a b s ^ 2 := by
    rw [movingCircleRoot]
    exact Real.sq_sqrt (movingCircleRadicand_pos (s := s) ha hab hb).le
  rw [movingCircleX, movingCircleY]
  field_simp [hden]
  rw [movingCircleDenominator, movingCircleRoot] at *
  nlinarith [Real.sin_sq_add_cos_sq (t - movingCircleCenter a b s)]

theorem contDiff_movingCircleX {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => movingCircleX a b p.1 p.2) := by
  have hw : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => isotopyWeight p.2) :=
    contDiff_isotopyWeight.comp contDiff_snd
  have hc : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => movingCircleParameter a b p.2) := by
    simpa [movingCircleParameter] using hw.mul
      (contDiff_const : ContDiff ℝ ⊤
        (fun _ : ℝ × ℝ => Real.cos (bridgeHalfSpan a b)))
  have hm : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => movingCircleCenter a b p.2) := by
    simpa [movingCircleCenter] using hw.mul
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => bridgeMidpoint a b))
  have harg : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.1 - movingCircleCenter a b p.2) :=
    contDiff_fst.sub hm
  have hden : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => movingCircleDenominator a b p.1 p.2) := by
    simpa [movingCircleDenominator] using
      (contDiff_const.sub (hc.mul harg.cos))
  have hnum : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => Real.cos (p.1 - movingCircleCenter a b p.2) -
        movingCircleParameter a b p.2) := harg.cos.sub hc
  exact hnum.div hden fun p => (movingCircleDenominator_pos ha hab hb).ne'

theorem contDiff_movingCircleY {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => movingCircleY a b p.1 p.2) := by
  have hw : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => isotopyWeight p.2) :=
    contDiff_isotopyWeight.comp contDiff_snd
  have hc : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => movingCircleParameter a b p.2) := by
    simpa [movingCircleParameter] using hw.mul
      (contDiff_const : ContDiff ℝ ⊤
        (fun _ : ℝ × ℝ => Real.cos (bridgeHalfSpan a b)))
  have hm : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => movingCircleCenter a b p.2) := by
    simpa [movingCircleCenter] using hw.mul
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => bridgeMidpoint a b))
  have harg : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => p.1 - movingCircleCenter a b p.2) :=
    contDiff_fst.sub hm
  have hrad : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => 1 - movingCircleParameter a b p.2 ^ 2) := by
    fun_prop
  have hroot : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => movingCircleRoot a b p.2) := by
    simpa [movingCircleRoot] using hrad.sqrt
      (fun p => (movingCircleRadicand_pos (s := p.2) ha hab hb).ne')
  have hden : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => movingCircleDenominator a b p.1 p.2) := by
    simpa [movingCircleDenominator] using
      (contDiff_const.sub (hc.mul harg.cos))
  have hnum : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => movingCircleRoot a b p.2 *
        Real.sin (p.1 - movingCircleCenter a b p.2)) := hroot.mul harg.sin
  exact hnum.div hden fun p => (movingCircleDenominator_pos ha hab hb).ne'

theorem movingCircleRoot_zero {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) : movingCircleRoot a b 0 = Real.sin (bridgeHalfSpan a b) := by
  have htrig : 1 - Real.cos (bridgeHalfSpan a b) ^ 2 =
      Real.sin (bridgeHalfSpan a b) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (bridgeHalfSpan a b)]
  rw [movingCircleRoot, movingCircleParameter, isotopyWeight_zero, one_mul, htrig,
    Real.sqrt_sq_eq_abs, abs_of_pos (sin_bridgeHalfSpan_pos ha hab hb)]

@[simp] theorem movingCircleX_zero (a b t : ℝ) :
    movingCircleX a b t 0 = bridgeCircleX a b t := by
  simp [movingCircleX, movingCircleDenominator, movingCircleParameter,
    movingCircleCenter, bridgeCircleX, bridgeDenominator]

@[simp] theorem movingCircleY_zero {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) : movingCircleY a b t 0 = bridgeCircleY a b t := by
  simp [movingCircleY, movingCircleDenominator, movingCircleParameter,
    movingCircleCenter, bridgeCircleY, bridgeDenominator, movingCircleRoot_zero ha hab hb]

@[simp] theorem movingCircleX_one (a b t : ℝ) : movingCircleX a b t 1 = Real.cos t := by
  simp [movingCircleX, movingCircleDenominator, movingCircleParameter,
    movingCircleCenter]

@[simp] theorem movingCircleY_one (a b t : ℝ) : movingCircleY a b t 1 = Real.sin t := by
  simp [movingCircleY, movingCircleDenominator, movingCircleParameter,
    movingCircleCenter, movingCircleRoot]

theorem hasDerivAt_movingCircleDenominator {a b t s : ℝ} :
    HasDerivAt (fun z => movingCircleDenominator a b z s)
      (movingCircleParameter a b s * Real.sin (t - movingCircleCenter a b s)) t := by
  have harg : HasDerivAt (fun z : ℝ => z - movingCircleCenter a b s) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (movingCircleCenter a b s)
  have hmul := harg.cos.const_mul (movingCircleParameter a b s)
  convert (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub hmul using 1 <;>
    try rfl
  ring

theorem hasDerivAt_movingCircleX {a b t s : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    HasDerivAt (fun z => movingCircleX a b z s)
      (-(movingCircleSpeed a b t s * movingCircleY a b t s)) t := by
  have harg : HasDerivAt (fun z : ℝ => z - movingCircleCenter a b s) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (movingCircleCenter a b s)
  have hnum : HasDerivAt
      (fun z => Real.cos (z - movingCircleCenter a b s) -
        movingCircleParameter a b s)
      (-Real.sin (t - movingCircleCenter a b s)) t := by
    simpa using harg.cos.sub_const (movingCircleParameter a b s)
  have hden := hasDerivAt_movingCircleDenominator (a := a) (b := b) (s := s) (t := t)
  have hden_ne := (movingCircleDenominator_pos (t := t) (s := s) ha hab hb).ne'
  have hden_expr : 1 - movingCircleParameter a b s *
      Real.cos (t - movingCircleCenter a b s) ≠ 0 := by
    simpa [movingCircleDenominator] using hden_ne
  have hroot := Real.sq_sqrt (movingCircleRadicand_pos (s := s) ha hab hb).le
  convert hnum.div hden hden_ne using 1 <;> try rfl
  unfold movingCircleSpeed movingCircleY movingCircleDenominator
  field_simp [hden_expr]
  unfold movingCircleRoot
  rw [hroot]
  ring

theorem hasDerivAt_movingCircleY {a b t s : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    HasDerivAt (fun z => movingCircleY a b z s)
      (movingCircleSpeed a b t s * movingCircleX a b t s) t := by
  have harg : HasDerivAt (fun z : ℝ => z - movingCircleCenter a b s) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (movingCircleCenter a b s)
  have hnum : HasDerivAt
      (fun z => movingCircleRoot a b s *
        Real.sin (z - movingCircleCenter a b s))
      (movingCircleRoot a b s * Real.cos (t - movingCircleCenter a b s)) t := by
    simpa using harg.sin.const_mul (movingCircleRoot a b s)
  have hden := hasDerivAt_movingCircleDenominator (a := a) (b := b) (s := s) (t := t)
  have hden_ne := (movingCircleDenominator_pos (t := t) (s := s) ha hab hb).ne'
  have hden_expr : 1 - movingCircleParameter a b s *
      Real.cos (t - movingCircleCenter a b s) ≠ 0 := by
    simpa [movingCircleDenominator] using hden_ne
  convert hnum.div hden hden_ne using 1 <;> try rfl
  unfold movingCircleSpeed movingCircleX movingCircleDenominator
  field_simp [hden_expr]
  have hinner : Real.cos (t - movingCircleCenter a b s) -
      movingCircleParameter a b s =
      Real.cos (t - movingCircleCenter a b s) *
          (1 - movingCircleParameter a b s *
            Real.cos (t - movingCircleCenter a b s)) -
        movingCircleParameter a b s *
          Real.sin (t - movingCircleCenter a b s) ^ 2 := by
    have htrig : Real.sin (t - movingCircleCenter a b s) ^ 2 =
        1 - Real.cos (t - movingCircleCenter a b s) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (t - movingCircleCenter a b s)]
    rw [htrig]
    ring
  rw [hinner]

theorem periodic_movingCircleX (a b s : ℝ) :
    Function.Periodic (fun t => movingCircleX a b t s) period := by
  intro t
  change movingCircleX a b (t + period) s = movingCircleX a b t s
  unfold movingCircleX movingCircleDenominator
  have harg : t + period - movingCircleCenter a b s =
      (t - movingCircleCenter a b s) + 2 * Real.pi := by
    simp [period]
    ring
  rw [harg]
  simp

theorem periodic_movingCircleY (a b s : ℝ) :
    Function.Periodic (fun t => movingCircleY a b t s) period := by
  intro t
  change movingCircleY a b (t + period) s = movingCircleY a b t s
  unfold movingCircleY movingCircleDenominator
  have harg : t + period - movingCircleCenter a b s =
      (t - movingCircleCenter a b s) + 2 * Real.pi := by
    simp [period]
    ring
  rw [harg]
  simp

theorem injOn_movingCircleXY {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    Set.InjOn (fun t => (movingCircleX a b t s, movingCircleY a b t s))
      (Ico (0 : ℝ) period) := by
  intro x hx y hy hxy
  have hX := congrArg Prod.fst hxy
  have hY := congrArg Prod.snd hxy
  dsimp at hX hY
  have hdx := (movingCircleDenominator_pos (t := x) (s := s) ha hab hb).ne'
  have hdy := (movingCircleDenominator_pos (t := y) (s := s) ha hab hb).ne'
  have hdx' : 1 - movingCircleParameter a b s *
      Real.cos (x - movingCircleCenter a b s) ≠ 0 := by
    simpa [movingCircleDenominator] using hdx
  have hdy' : 1 - movingCircleParameter a b s *
      Real.cos (y - movingCircleCenter a b s) ≠ 0 := by
    simpa [movingCircleDenominator] using hdy
  have hdx'' : 1 - Real.cos (x - movingCircleCenter a b s) *
      movingCircleParameter a b s ≠ 0 := by simpa [mul_comm] using hdx'
  have hdy'' : 1 - Real.cos (y - movingCircleCenter a b s) *
      movingCircleParameter a b s ≠ 0 := by simpa [mul_comm] using hdy'
  have hcosShift : Real.cos (x - movingCircleCenter a b s) =
      Real.cos (y - movingCircleCenter a b s) := by
    unfold movingCircleX movingCircleDenominator at hX
    field_simp [hdx', hdy', hdx'', hdy''] at hX
    have hc := abs_movingCircleParameter_lt_one (s := s) ha hab hb
    have hc2 : movingCircleParameter a b s ^ 2 < 1 :=
      (sq_lt_one_iff_abs_lt_one (movingCircleParameter a b s)).2 hc
    nlinarith
  have hsinShift : Real.sin (x - movingCircleCenter a b s) =
      Real.sin (y - movingCircleCenter a b s) := by
    unfold movingCircleY movingCircleDenominator at hY
    field_simp [hdx', hdy', hdx'', hdy''] at hY
    rw [hcosShift] at hY
    have hcoef : movingCircleRoot a b s *
        (1 - movingCircleParameter a b s *
          Real.cos (y - movingCircleCenter a b s)) ≠ 0 :=
      mul_ne_zero (movingCircleRoot_pos (s := s) ha hab hb).ne' hdy'
    apply mul_left_cancel₀ hcoef
    nlinarith
  have hxShift : x - movingCircleCenter a b s ∈
      Ico (-movingCircleCenter a b s) (period - movingCircleCenter a b s) := by
    constructor <;> linarith [hx.1, hx.2]
  have hyShift : y - movingCircleCenter a b s ∈
      Ico (-movingCircleCenter a b s) (period - movingCircleCenter a b s) := by
    constructor <;> linarith [hy.1, hy.2]
  have hcircle : circleMap 0 1 (x - movingCircleCenter a b s) =
      circleMap 0 1 (y - movingCircleCenter a b s) := by
    apply Complex.ext
    · simpa [circleMap_zero_re] using hcosShift
    · simpa [circleMap_zero_im] using hsinShift
  have hinj : Set.InjOn (circleMap 0 1)
      (Ico (-movingCircleCenter a b s) (period - movingCircleCenter a b s)) :=
    injOn_circleMap_of_abs_sub_le' (c := 0) (R := 1) one_ne_zero (by simp [period])
  have hshift := hinj hxShift hyShift hcircle
  linarith

noncomputable def movingCircleCurve (a b t s : ℝ) : Space :=
  toLp 2 ![movingCircleX a b t s, movingCircleY a b t s, 0]

theorem contDiff_movingCircleCurve {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => movingCircleCurve a b p.1 p.2) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [movingCircleCurve] using contDiff_movingCircleX ha hab hb
  · simpa [movingCircleCurve] using contDiff_movingCircleY ha hab hb
  · simpa [movingCircleCurve] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (0 : ℝ)))

theorem velocity_movingCircleCurve {a b t s : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b < period) :
    velocity (fun z => movingCircleCurve a b z s) t =
      toLp 2 ![-(movingCircleSpeed a b t s * movingCircleY a b t s),
        movingCircleSpeed a b t s * movingCircleX a b t s, 0] := by
  have hraw : HasDerivAt
      (fun z : ℝ => ![movingCircleX a b z s, movingCircleY a b z s, 0])
      ![-(movingCircleSpeed a b t s * movingCircleY a b t s),
        movingCircleSpeed a b t s * movingCircleX a b t s, 0] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hasDerivAt_movingCircleX ha hab hb
    · exact hasDerivAt_movingCircleY ha hab hb
    · simpa using hasDerivAt_const (x := t) (c := (0 : ℝ))
  exact (toLpContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw).deriv

theorem minOrientation_kernel {w x y : ℝ}
    (h0 : (1 - w) * x + w * y = 0)
    (h1 : w * x + (1 - w) * y = 0)
    (h2 : w * (1 - w) * (y - x) = 0) : x = 0 ∧ y = 0 := by
  have hsum : x + y = 0 := by linarith
  have hdiff : (1 - 2 * w) * (x - y) = 0 := by nlinarith
  by_cases hmid : 1 - 2 * w = 0
  · have hw : w = 1 / 2 := by linarith
    rw [hw] at h2
    norm_num at h2
    constructor <;> linarith
  · have hxy : x - y = 0 := (mul_eq_zero.mp hdiff).resolve_left hmid
    constructor <;> linarith

theorem maxOrientation_kernel {w x y : ℝ}
    (h0 : (1 - w) * x - w * y = 0)
    (h1 : -w * x + (1 - w) * y = 0)
    (h2 : w * (1 - w) * (x + y) = 0) : x = 0 ∧ y = 0 := by
  have hdiff : x - y = 0 := by linarith
  have hsum : (1 - 2 * w) * (x + y) = 0 := by nlinarith
  by_cases hmid : 1 - 2 * w = 0
  · have hw : w = 1 / 2 := by linarith
    rw [hw] at h2
    norm_num at h2
    constructor <;> linarith
  · have hxy : x + y = 0 := (mul_eq_zero.mp hsum).resolve_left hmid
    constructor <;> linarith

noncomputable def orientedMovingCircleMinMax (a b t s : ℝ) : Space :=
  let w := isotopyWeight s
  let x := movingCircleX a b t s
  let y := movingCircleY a b t s
  toLp 2 ![(1 - w) * x + w * y,
    w * x + (1 - w) * y, w * (1 - w) * (y - x)]

noncomputable def orientedMovingCircleMaxMin (a b t s : ℝ) : Space :=
  let w := isotopyWeight s
  let x := movingCircleX a b t s
  let y := movingCircleY a b t s
  toLp 2 ![(1 - w) * x - w * y,
    -w * x + (1 - w) * y, w * (1 - w) * (x + y)]

theorem contDiff_orientedMovingCircleMinMax {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => orientedMovingCircleMinMax a b p.1 p.2) := by
  have hw : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => isotopyWeight p.2) :=
    contDiff_isotopyWeight.comp contDiff_snd
  have hX := contDiff_movingCircleX ha hab hb
  have hY := contDiff_movingCircleY ha hab hb
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [orientedMovingCircleMinMax] using
      ((contDiff_const.sub hw).mul hX).add (hw.mul hY)
  · simpa [orientedMovingCircleMinMax] using
      (hw.mul hX).add ((contDiff_const.sub hw).mul hY)
  · simpa [orientedMovingCircleMinMax] using
      ((hw.mul (contDiff_const.sub hw)).mul (hY.sub hX))

theorem contDiff_orientedMovingCircleMaxMin {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => orientedMovingCircleMaxMin a b p.1 p.2) := by
  have hw : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => isotopyWeight p.2) :=
    contDiff_isotopyWeight.comp contDiff_snd
  have hX := contDiff_movingCircleX ha hab hb
  have hY := contDiff_movingCircleY ha hab hb
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · simpa [orientedMovingCircleMaxMin] using
      ((contDiff_const.sub hw).mul hX).sub (hw.mul hY)
  · simpa [orientedMovingCircleMaxMin] using
      (hw.mul hX).neg.add ((contDiff_const.sub hw).mul hY)
  · simpa [orientedMovingCircleMaxMin] using
      ((hw.mul (contDiff_const.sub hw)).mul (hX.add hY))

@[simp] theorem orientedMovingCircleMinMax_zero {a b t : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    orientedMovingCircleMinMax a b t 0 = bridgeCircleMinMax a b t := by
  ext i
  fin_cases i <;> simp [orientedMovingCircleMinMax, bridgeCircleMinMax,
    movingCircleX_zero, movingCircleY_zero ha hab hb]

@[simp] theorem orientedMovingCircleMaxMin_zero {a b t : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b < period) :
    orientedMovingCircleMaxMin a b t 0 = bridgeCircleMaxMin a b t := by
  ext i
  fin_cases i <;> simp [orientedMovingCircleMaxMin, bridgeCircleMaxMin,
    movingCircleX_zero, movingCircleY_zero ha hab hb]

@[simp] theorem orientedMovingCircleMinMax_one (a b t : ℝ) :
    orientedMovingCircleMinMax a b t 1 = standardCircle t := by
  ext i
  fin_cases i <;> simp [orientedMovingCircleMinMax, standardCircle]

@[simp] theorem orientedMovingCircleMaxMin_one (a b t : ℝ) :
    orientedMovingCircleMaxMin a b t 1 = standardCircle t := by
  ext i
  fin_cases i <;> simp [orientedMovingCircleMaxMin, standardCircle]

theorem periodic_orientedMovingCircleMinMax (a b s : ℝ) :
    Function.Periodic (fun t => orientedMovingCircleMinMax a b t s) period := by
  intro t
  ext i
  fin_cases i <;> simp [orientedMovingCircleMinMax,
    periodic_movingCircleX a b s t, periodic_movingCircleY a b s t]

theorem periodic_orientedMovingCircleMaxMin (a b s : ℝ) :
    Function.Periodic (fun t => orientedMovingCircleMaxMin a b t s) period := by
  intro t
  ext i
  fin_cases i <;> simp [orientedMovingCircleMaxMin,
    periodic_movingCircleX a b s t, periodic_movingCircleY a b s t]

theorem injOn_orientedMovingCircleMinMax {a b s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    Set.InjOn (fun t => orientedMovingCircleMinMax a b t s)
      (Ico (0 : ℝ) period) := by
  intro t ht z hz htz
  let w := isotopyWeight s
  let dx := movingCircleX a b t s - movingCircleX a b z s
  let dy := movingCircleY a b t s - movingCircleY a b z s
  have h0raw := congrArg (fun v : Space => v 0) htz
  have h1raw := congrArg (fun v : Space => v 1) htz
  have h2raw := congrArg (fun v : Space => v 2) htz
  have h0 : (1 - w) * dx + w * dy = 0 := by
    dsimp [w, dx, dy]
    have h := sub_eq_zero.mpr h0raw
    simp [orientedMovingCircleMinMax] at h
    nlinarith
  have h1 : w * dx + (1 - w) * dy = 0 := by
    dsimp [w, dx, dy]
    have h := sub_eq_zero.mpr h1raw
    simp [orientedMovingCircleMinMax] at h
    nlinarith
  have h2 : w * (1 - w) * (dy - dx) = 0 := by
    dsimp [w, dx, dy]
    have h := sub_eq_zero.mpr h2raw
    simp [orientedMovingCircleMinMax] at h
    nlinarith
  obtain ⟨hdx, hdy⟩ := minOrientation_kernel h0 h1 h2
  apply injOn_movingCircleXY ha hab hb ht hz
  apply Prod.ext <;> dsimp [dx, dy] at * <;> linarith

theorem injOn_orientedMovingCircleMaxMin {a b s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    Set.InjOn (fun t => orientedMovingCircleMaxMin a b t s)
      (Ico (0 : ℝ) period) := by
  intro t ht z hz htz
  let w := isotopyWeight s
  let dx := movingCircleX a b t s - movingCircleX a b z s
  let dy := movingCircleY a b t s - movingCircleY a b z s
  have h0raw := congrArg (fun v : Space => v 0) htz
  have h1raw := congrArg (fun v : Space => v 1) htz
  have h2raw := congrArg (fun v : Space => v 2) htz
  have h0 : (1 - w) * dx - w * dy = 0 := by
    dsimp [w, dx, dy]
    have h := sub_eq_zero.mpr h0raw
    simp [orientedMovingCircleMaxMin] at h
    nlinarith
  have h1 : -w * dx + (1 - w) * dy = 0 := by
    dsimp [w, dx, dy]
    have h := sub_eq_zero.mpr h1raw
    simp [orientedMovingCircleMaxMin] at h
    nlinarith
  have h2 : w * (1 - w) * (dx + dy) = 0 := by
    dsimp [w, dx, dy]
    have h := sub_eq_zero.mpr h2raw
    simp [orientedMovingCircleMaxMin] at h
    nlinarith
  obtain ⟨hdx, hdy⟩ := maxOrientation_kernel h0 h1 h2
  apply injOn_movingCircleXY ha hab hb ht hz
  apply Prod.ext <;> dsimp [dx, dy] at * <;> linarith

theorem velocity_orientedMovingCircleMinMax {a b t s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    velocity (fun z => orientedMovingCircleMinMax a b z s) t =
      let w := isotopyWeight s
      let dx := -(movingCircleSpeed a b t s * movingCircleY a b t s)
      let dy := movingCircleSpeed a b t s * movingCircleX a b t s
      toLp 2 ![(1 - w) * dx + w * dy,
        w * dx + (1 - w) * dy, w * (1 - w) * (dy - dx)] := by
  let w := isotopyWeight s
  let dx := -(movingCircleSpeed a b t s * movingCircleY a b t s)
  let dy := movingCircleSpeed a b t s * movingCircleX a b t s
  have hX := hasDerivAt_movingCircleX (t := t) (s := s) ha hab hb
  have hY := hasDerivAt_movingCircleY (t := t) (s := s) ha hab hb
  have hraw : HasDerivAt
      (fun z : ℝ => ![(1 - w) * movingCircleX a b z s + w * movingCircleY a b z s,
        w * movingCircleX a b z s + (1 - w) * movingCircleY a b z s,
        w * (1 - w) * (movingCircleY a b z s - movingCircleX a b z s)])
      ![(1 - w) * dx + w * dy, w * dx + (1 - w) * dy,
        w * (1 - w) * (dy - dx)] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact (hX.const_mul (1 - w)).add (hY.const_mul w)
    · exact (hX.const_mul w).add (hY.const_mul (1 - w))
    · exact ((hY.sub hX).const_mul (w * (1 - w)))
  exact (toLpContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw).deriv

theorem velocity_orientedMovingCircleMaxMin {a b t s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    velocity (fun z => orientedMovingCircleMaxMin a b z s) t =
      let w := isotopyWeight s
      let dx := -(movingCircleSpeed a b t s * movingCircleY a b t s)
      let dy := movingCircleSpeed a b t s * movingCircleX a b t s
      toLp 2 ![(1 - w) * dx - w * dy,
        -w * dx + (1 - w) * dy, w * (1 - w) * (dx + dy)] := by
  let w := isotopyWeight s
  let dx := -(movingCircleSpeed a b t s * movingCircleY a b t s)
  let dy := movingCircleSpeed a b t s * movingCircleX a b t s
  have hX := hasDerivAt_movingCircleX (t := t) (s := s) ha hab hb
  have hY := hasDerivAt_movingCircleY (t := t) (s := s) ha hab hb
  have hcoord1 : HasDerivAt
      (fun z => -w * movingCircleX a b z s +
        (1 - w) * movingCircleY a b z s)
      (-w * dx + (1 - w) * dy) t := by
    exact ((hX.const_mul (-w)).add (hY.const_mul (1 - w))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hraw : HasDerivAt
      (fun z : ℝ => ![(1 - w) * movingCircleX a b z s - w * movingCircleY a b z s,
        -w * movingCircleX a b z s + (1 - w) * movingCircleY a b z s,
        w * (1 - w) * (movingCircleX a b z s + movingCircleY a b z s)])
      ![(1 - w) * dx - w * dy, -w * dx + (1 - w) * dy,
        w * (1 - w) * (dx + dy)] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact (hX.const_mul (1 - w)).sub (hY.const_mul w)
    · exact hcoord1
    · exact ((hX.add hY).const_mul (w * (1 - w)))
  exact (toLpContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw).deriv

set_option maxHeartbeats 2000000 in
theorem isSmoothKnot_orientedMovingCircleMinMax {a b s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    IsSmoothKnot (fun t => orientedMovingCircleMinMax a b t s) where
  smooth := (contDiff_orientedMovingCircleMinMax ha hab hb).comp
    (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => s)))
  periodic := periodic_orientedMovingCircleMinMax a b s
  injective_on_period := injOn_orientedMovingCircleMinMax ha hab hb
  regular := by
    intro t hzero
    let w := isotopyWeight s
    let dx := -(movingCircleSpeed a b t s * movingCircleY a b t s)
    let dy := movingCircleSpeed a b t s * movingCircleX a b t s
    have h0 : (1 - w) * dx + w * dy = 0 := by
      simpa [w, dx, dy, velocity_orientedMovingCircleMinMax ha hab hb] using
        congrArg (fun v : Space => v 0) hzero
    have h1 : w * dx + (1 - w) * dy = 0 := by
      simpa [w, dx, dy, velocity_orientedMovingCircleMinMax ha hab hb] using
        congrArg (fun v : Space => v 1) hzero
    have h2 : w * (1 - w) * (dy - dx) = 0 := by
      simpa [w, dx, dy, velocity_orientedMovingCircleMinMax ha hab hb] using
        congrArg (fun v : Space => v 2) hzero
    obtain ⟨hdx, hdy⟩ := minOrientation_kernel h0 h1 h2
    dsimp [dx, dy] at hdx hdy
    have hspeed := (movingCircleSpeed_pos (t := t) (s := s) ha hab hb).ne'
    have hX : movingCircleX a b t s = 0 := (mul_eq_zero.mp hdy).resolve_left hspeed
    have hY : movingCircleY a b t s = 0 :=
      (mul_eq_zero.mp (neg_eq_zero.mp hdx)).resolve_left hspeed
    nlinarith [movingCircle_sq_add_sq (t := t) (s := s) ha hab hb]

set_option maxHeartbeats 2000000 in
theorem isSmoothKnot_orientedMovingCircleMaxMin {a b s : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    IsSmoothKnot (fun t => orientedMovingCircleMaxMin a b t s) where
  smooth := (contDiff_orientedMovingCircleMaxMin ha hab hb).comp
    (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => s)))
  periodic := periodic_orientedMovingCircleMaxMin a b s
  injective_on_period := injOn_orientedMovingCircleMaxMin ha hab hb
  regular := by
    intro t hzero
    let w := isotopyWeight s
    let dx := -(movingCircleSpeed a b t s * movingCircleY a b t s)
    let dy := movingCircleSpeed a b t s * movingCircleX a b t s
    have h0 : (1 - w) * dx - w * dy = 0 := by
      simpa [w, dx, dy, velocity_orientedMovingCircleMaxMin ha hab hb] using
        congrArg (fun v : Space => v 0) hzero
    have h1 : -w * dx + (1 - w) * dy = 0 := by
      simpa [w, dx, dy, velocity_orientedMovingCircleMaxMin ha hab hb] using
        congrArg (fun v : Space => v 1) hzero
    have h2 : w * (1 - w) * (dx + dy) = 0 := by
      simpa [w, dx, dy, velocity_orientedMovingCircleMaxMin ha hab hb] using
        congrArg (fun v : Space => v 2) hzero
    obtain ⟨hdx, hdy⟩ := maxOrientation_kernel h0 h1 h2
    dsimp [dx, dy] at hdx hdy
    have hspeed := (movingCircleSpeed_pos (t := t) (s := s) ha hab hb).ne'
    have hX : movingCircleX a b t s = 0 := (mul_eq_zero.mp hdy).resolve_left hspeed
    have hY : movingCircleY a b t s = 0 :=
      (mul_eq_zero.mp (neg_eq_zero.mp hdx)).resolve_left hspeed
    nlinarith [movingCircle_sq_add_sq (t := t) (s := s) ha hab hb]

theorem isUnknotted_bridgeCircleMinMax {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    IsUnknotted (bridgeCircleMinMax a b) := by
  refine ⟨orientedMovingCircleMinMax a b, ?_, ?_, ?_, ?_⟩
  · exact contDiff_orientedMovingCircleMinMax ha hab hb
  · intro t
    exact orientedMovingCircleMinMax_zero ha hab hb
  · intro t
    exact orientedMovingCircleMinMax_one a b t
  · intro s _hs
    exact isSmoothKnot_orientedMovingCircleMinMax ha hab hb

theorem isUnknotted_bridgeCircleMaxMin {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b < period) :
    IsUnknotted (bridgeCircleMaxMin a b) := by
  refine ⟨orientedMovingCircleMaxMin a b, ?_, ?_, ?_, ?_⟩
  · exact contDiff_orientedMovingCircleMaxMin ha hab hb
  · intro t
    exact orientedMovingCircleMaxMin_zero ha hab hb
  · intro t
    exact orientedMovingCircleMaxMin_one a b t
  · intro s _hs
    exact isSmoothKnot_orientedMovingCircleMaxMin ha hab hb

end Submission.Helpers
