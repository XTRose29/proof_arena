import Submission.BridgeContract

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

theorem period_pos : 0 < period := by
  simp [period, Real.pi_pos]

theorem eq_of_curve_eq_of_mem_Icc_of_abs_sub_lt_period
    {p : ℝ → Space} (hp : IsSmoothKnot p) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) period) (hy : y ∈ Icc (0 : ℝ) period)
    (hxy : p x = p y) (hclose : |x - y| < period) :
    x = y := by
  by_cases hxP : x = period
  · subst x
    by_cases hyP : y = period
    · exact hyP.symm
    · have hyIco : y ∈ Ico (0 : ℝ) period := ⟨hy.1, lt_of_le_of_ne hy.2 hyP⟩
      have h0y : p 0 = p y := by
        rw [← hxy]
        simpa using (hp.periodic 0).symm
      have hy0 := hp.injective_on_period (left_mem_Ico.mpr period_pos)
        hyIco h0y
      subst y
      rw [sub_zero, abs_of_pos period_pos] at hclose
      exact (lt_irrefl _ hclose).elim
  · have hxIco : x ∈ Ico (0 : ℝ) period :=
      ⟨hx.1, lt_of_le_of_ne hx.2 hxP⟩
    by_cases hyP : y = period
    · subst y
      have hx0 : p x = p 0 := by
        calc
          p x = p period := hxy
          _ = p 0 := by simpa using hp.periodic 0
      have hxzero := hp.injective_on_period hxIco
        (left_mem_Ico.mpr period_pos) hx0
      subst x
      rw [abs_sub_comm, sub_zero, abs_of_pos period_pos] at hclose
      exact (lt_irrefl _ hclose).elim
    · exact hp.injective_on_period hxIco ⟨hy.1, lt_of_le_of_ne hy.2 hyP⟩ hxy

def farParameterPairs (d : ℝ) : Set (ℝ × ℝ) :=
  (Icc (0 : ℝ) period ×ˢ Icc (0 : ℝ) period) ∩
    {z | d ≤ |z.2 - z.1|} ∩ {z | |z.2 - z.1| ≤ period - d}

theorem isCompact_farParameterPairs (d : ℝ) :
    IsCompact (farParameterPairs d) := by
  have hdiff : Continuous (fun z : ℝ × ℝ => |z.2 - z.1|) :=
    (continuous_snd.sub continuous_fst).abs
  exact ((isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const hdiff)).inter_right
    (isClosed_le hdiff continuous_const)

theorem nonempty_farParameterPairs {d : ℝ}
    (hd0 : 0 ≤ d) (hdhalf : d ≤ period / 2) :
    (farParameterPairs d).Nonempty := by
  refine ⟨(0, period / 2), ?_⟩
  change (((0 : ℝ) ∈ Icc 0 period ∧ period / 2 ∈ Icc 0 period) ∧
      d ≤ |period / 2 - 0|) ∧ |period / 2 - 0| ≤ period - d
  refine ⟨⟨⟨⟨le_rfl, period_pos.le⟩,
    ⟨by linarith [period_pos], by linarith [period_pos]⟩⟩, ?_⟩, ?_⟩
  · have hhalf0 : 0 ≤ period / 2 := by linarith [period_pos]
    simpa [abs_of_nonneg hhalf0] using hdhalf
  · have hhalf0 : 0 ≤ period / 2 := by linarith [period_pos]
    simp only [sub_zero, abs_of_nonneg hhalf0]
    linarith

set_option maxHeartbeats 1000000 in
theorem exists_c1_knot_neighborhood {p : ℝ → Space}
    (hp : IsSmoothKnot p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℝ → Space,
      ContDiff ℝ ⊤ q → Function.Periodic q period →
      (∀ t, ‖q t - p t‖ < ε) →
      (∀ t, ‖velocity q t - velocity p t‖ < ε) →
      IsSmoothKnot q := by
  let J : Set ℝ := Icc (0 : ℝ) (2 * period)
  have hJcompact : IsCompact J := isCompact_Icc
  have hJnonempty : J.Nonempty :=
    nonempty_Icc.mpr (by linarith [period_pos] : (0 : ℝ) ≤ 2 * period)
  have hvcont : Continuous (velocity p) := (contDiff_velocity hp).continuous
  obtain ⟨t₀, ht₀, hmin⟩ := hJcompact.exists_isMinOn hJnonempty
    hvcont.norm.continuousOn
  let m : ℝ := ‖velocity p t₀‖
  have hmpos : 0 < m := norm_pos_iff.mpr (hp.regular t₀)
  have hmle : ∀ t ∈ J, m ≤ ‖velocity p t‖ := by
    intro t ht
    exact hmin ht
  have hvuc : UniformContinuousOn (velocity p) J :=
    hJcompact.uniformContinuousOn_of_continuous hvcont.continuousOn
  obtain ⟨d₀, hd₀0, hd₀⟩ := (Metric.uniformContinuousOn_iff.mp hvuc)
    (m / 4) (div_pos hmpos (by norm_num))
  let d : ℝ := min d₀ (period / 4)
  have hdpos : 0 < d := lt_min hd₀0 (div_pos period_pos (by norm_num))
  have hdle : d ≤ d₀ := min_le_left _ _
  have hdquarter : d ≤ period / 4 := min_le_right _ _
  have hdhalf : d ≤ period / 2 := by linarith [period_pos]
  have hvelNear : ∀ x ∈ J, ∀ y ∈ J, |x - y| < d →
      ‖velocity p x - velocity p y‖ < m / 4 := by
    intro x hx y hy hxy
    apply hd₀ x hx y hy
    rw [Real.dist_eq]
    exact hxy.trans_le hdle
  let K := farParameterPairs d
  have hKcompact : IsCompact K := isCompact_farParameterPairs d
  have hKnonempty : K.Nonempty := nonempty_farParameterPairs hdpos.le hdhalf
  let sep : ℝ × ℝ → ℝ := fun z => ‖p z.2 - p z.1‖
  have hsepcont : Continuous sep :=
    ((hp.smooth.continuous.comp continuous_snd).sub
      (hp.smooth.continuous.comp continuous_fst)).norm
  obtain ⟨z₀, hz₀, hsepmin⟩ := hKcompact.exists_isMinOn hKnonempty
    hsepcont.continuousOn
  let η : ℝ := sep z₀
  have hηpos : 0 < η := by
    apply norm_pos_iff.mpr
    intro hzero
    have heq : p z₀.2 = p z₀.1 := sub_eq_zero.mp hzero
    have hzbox := hz₀.1.1
    have hzfar := hz₀.2
    change |z₀.2 - z₀.1| ≤ period - d at hzfar
    have heqParam := eq_of_curve_eq_of_mem_Icc_of_abs_sub_lt_period hp
      hzbox.2 hzbox.1 heq (by
        exact hzfar.trans_lt (sub_lt_self _ hdpos))
    have hdlower := hz₀.1.2
    change d ≤ |z₀.2 - z₀.1| at hdlower
    rw [heqParam, sub_self, abs_zero] at hdlower
    exact (not_le_of_gt hdpos) hdlower
  let ε : ℝ := min (m / 4) (η / 4)
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨ε, hεpos, ?_⟩
  intro q hqsmooth hqperiod hpos hvel
  have hεm : ε ≤ m / 4 := min_le_left _ _
  have hεη : ε ≤ η / 4 := min_le_right _ _
  have hqregular : ∀ t, velocity q t ≠ 0 := by
    intro t hzero
    have hpv : ‖velocity p t‖ < ε := by
      simpa [hzero, norm_neg] using hvel t
    have hpvpos : 0 < ‖velocity p t‖ := norm_pos_iff.mpr (hp.regular t)
    have hperiodicVelocity : Function.Periodic (velocity p) period :=
      periodic_deriv hp.periodic
    obtain ⟨z, hz, hzt⟩ := hperiodicVelocity.exists_mem_Ico period_pos t 0
    have hzJ : z ∈ J := ⟨hz.1, by linarith [hz.2, period_pos]⟩
    have hm := hmle z hzJ
    rw [← hzt] at hm
    linarith
  have hqinj : Set.InjOn q (Ico (0 : ℝ) period) := by
    intro x hx y hy hxy
    wlog hle : x ≤ y generalizing x y
    · exact (this (x := y) (y := x) hy hx hxy.symm
        (le_of_not_ge hle)).symm
    rcases hle.eq_or_lt with heq | hlt
    · exact heq
    · let gap := y - x
      have hgap0 : 0 < gap := sub_pos.mpr hlt
      have hgapP : gap < period := by dsimp [gap]; linarith [hx.1, hy.2]
      by_cases hnear : gap < d
      · let v := velocity p x
        let φ : ℝ → ℝ := (innerSL ℝ v) ∘ q
        have hφcont : Continuous φ :=
          (innerSL ℝ v).continuous.comp hqsmooth.continuous
        have hφderiv : ∀ z ∈ Ioo x y, 0 < deriv φ z := by
          intro z hz
          have hxJ : x ∈ J := ⟨hx.1, by linarith [hx.2, period_pos]⟩
          have hzJ : z ∈ J :=
            ⟨hx.1.trans hz.1.le, by linarith [hz.2, hy.2, period_pos]⟩
          have hpnear : ‖velocity p z - velocity p x‖ < m / 4 := by
            rw [norm_sub_rev]
            apply hvelNear x hxJ z hzJ
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hz.1.le)]
            exact (sub_lt_sub_right hz.2 x).trans hnear
          have hqnear : ‖velocity q z - velocity p z‖ < m / 4 :=
            (hvel z).trans_le hεm
          have hdiff : ‖velocity q z - v‖ < m / 2 := by
            calc
              ‖velocity q z - v‖ ≤
                  ‖velocity q z - velocity p z‖ +
                    ‖velocity p z - velocity p x‖ := by
                dsimp [v]
                rw [show velocity q z - velocity p x =
                    (velocity q z - velocity p z) +
                      (velocity p z - velocity p x) by abel]
                exact norm_add_le _ _
              _ < m / 4 + m / 4 := add_lt_add hqnear hpnear
              _ = m / 2 := by ring
          have hvnorm : m ≤ ‖v‖ := hmle x hxJ
          have hvpos : 0 < ‖v‖ := hvnorm.trans_lt' hmpos
          have hinnerLower := neg_le_of_abs_le
            (abs_real_inner_le_norm v (velocity q z - v))
          have hmul : ‖v‖ * ‖velocity q z - v‖ < ‖v‖ * (m / 2) :=
            mul_lt_mul_of_pos_left hdiff hvpos
          have hpositive : 0 < inner ℝ v (velocity q z) := by
            rw [show velocity q z = v + (velocity q z - v) by abel,
              inner_add_right, real_inner_self_eq_norm_sq]
            nlinarith [norm_nonneg v]
          have hcomp := (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt z
            ((hqsmooth.differentiable (by simp)).differentiableAt.hasDerivAt)
          have hderivEq : deriv φ z = inner ℝ v (velocity q z) := by
            dsimp [φ]
            simpa [velocity] using hcomp.deriv
          rwa [hderivEq]
        have hmono : StrictMonoOn φ (Icc x y) :=
          strictMonoOn_of_deriv_pos (convex_Icc x y) hφcont.continuousOn (by
            simpa [interior_Icc, hlt.ne] using hφderiv)
        have hstrict := hmono (left_mem_Icc.mpr hlt.le)
          (right_mem_Icc.mpr hlt.le) hlt
        dsimp [φ] at hstrict
        rw [hxy] at hstrict
        exact (lt_irrefl _ hstrict).elim
      · by_cases hwrap : period - gap < d
        · let v := velocity p y
          let φ : ℝ → ℝ := (innerSL ℝ v) ∘ q
          have hyxP : y < x + period := by dsimp [gap] at hgapP ⊢; linarith
          have hφcont : Continuous φ :=
            (innerSL ℝ v).continuous.comp hqsmooth.continuous
          have hφderiv : ∀ z ∈ Ioo y (x + period), 0 < deriv φ z := by
            intro z hz
            have hyJ : y ∈ J := ⟨hy.1, by linarith [hy.2, period_pos]⟩
            have hzJ : z ∈ J := by
              constructor
              · exact hy.1.trans hz.1.le
              · linarith [hz.2, hx.2, period_pos]
            have hpnear : ‖velocity p z - velocity p y‖ < m / 4 := by
              rw [norm_sub_rev]
              apply hvelNear y hyJ z hzJ
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hz.1.le)]
              have : z - y < period - gap := by dsimp [gap]; linarith [hz.2]
              exact this.trans hwrap
            have hqnear : ‖velocity q z - velocity p z‖ < m / 4 :=
              (hvel z).trans_le hεm
            have hdiff : ‖velocity q z - v‖ < m / 2 := by
              calc
                ‖velocity q z - v‖ ≤
                    ‖velocity q z - velocity p z‖ +
                      ‖velocity p z - velocity p y‖ := by
                  dsimp [v]
                  rw [show velocity q z - velocity p y =
                      (velocity q z - velocity p z) +
                        (velocity p z - velocity p y) by abel]
                  exact norm_add_le _ _
                _ < m / 4 + m / 4 := add_lt_add hqnear hpnear
                _ = m / 2 := by ring
            have hvnorm : m ≤ ‖v‖ := hmle y hyJ
            have hvpos : 0 < ‖v‖ := hvnorm.trans_lt' hmpos
            have hinnerLower := neg_le_of_abs_le
              (abs_real_inner_le_norm v (velocity q z - v))
            have hmul : ‖v‖ * ‖velocity q z - v‖ < ‖v‖ * (m / 2) :=
              mul_lt_mul_of_pos_left hdiff hvpos
            have hpositive : 0 < inner ℝ v (velocity q z) := by
              rw [show velocity q z = v + (velocity q z - v) by abel,
                inner_add_right, real_inner_self_eq_norm_sq]
              nlinarith [norm_nonneg v]
            have hcomp := (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt z
              ((hqsmooth.differentiable (by simp)).differentiableAt.hasDerivAt)
            have hderivEq : deriv φ z = inner ℝ v (velocity q z) := by
              dsimp [φ]
              simpa [velocity] using hcomp.deriv
            rwa [hderivEq]
          have hmono : StrictMonoOn φ (Icc y (x + period)) :=
            strictMonoOn_of_deriv_pos (convex_Icc y (x + period)) hφcont.continuousOn (by
              simpa [interior_Icc, hyxP.ne] using hφderiv)
          have hstrict := hmono (left_mem_Icc.mpr hyxP.le)
            (right_mem_Icc.mpr hyxP.le) hyxP
          have hqxP : q (x + period) = q x := hqperiod x
          dsimp [φ] at hstrict
          rw [hqxP, hxy] at hstrict
          exact (lt_irrefl _ hstrict).elim
        · have hfar : (x, y) ∈ K := by
            refine ⟨⟨⟨⟨hx.1, hx.2.le⟩, ⟨hy.1, hy.2.le⟩⟩, ?_⟩, ?_⟩
            · change d ≤ |y - x|
              rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]
              exact le_of_not_gt hnear
            · change |y - x| ≤ period - d
              rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]
              linarith [le_of_not_gt hwrap]
          have hsepLower : η ≤ ‖p y - p x‖ := by
            simpa [η, sep] using hsepmin hfar
          have hbound : ‖p y - p x‖ < 2 * ε := by
            calc
              ‖p y - p x‖ = ‖(p y - q y) + (q x - p x)‖ := by
                rw [hxy]
                congr 1
                abel
              _ ≤ ‖p y - q y‖ + ‖q x - p x‖ := norm_add_le _ _
              _ < ε + ε := add_lt_add (by simpa [norm_sub_rev] using hpos y) (hpos x)
              _ = 2 * ε := by ring
          nlinarith
  exact ⟨hqsmooth, hqperiod, hqinj, hqregular⟩

end Submission.Helpers
