import Submission.BridgeUnknot

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def familyVelocity (P : ℝ → ℝ → Space) (z : ℝ × ℝ) : Space :=
  (fderiv ℝ (fun p : ℝ × ℝ => P p.1 p.2) z) (1, 0)

theorem hasDerivAt_familySlice {P : ℝ → ℝ → Space}
    (hP : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => P p.1 p.2)) (t s : ℝ) :
    HasDerivAt (fun x => P x s) (familyVelocity P (t, s)) t := by
  have hpath : HasDerivAt (fun x : ℝ => (x, s)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const (x := t) (c := s))
  have hfull := ((hP.differentiable (by simp)).differentiableAt.hasFDerivAt)
    |>.comp_hasDerivAt t hpath
  exact hfull.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

theorem familyVelocity_eq_velocity {P : ℝ → ℝ → Space}
    (hP : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => P p.1 p.2)) (t s : ℝ) :
    familyVelocity P (t, s) = velocity (fun x => P x s) t := by
  exact (hasDerivAt_familySlice hP t s).deriv.symm

theorem continuous_familyVelocity {P : ℝ → ℝ → Space}
    (hP : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => P p.1 p.2)) :
    Continuous (familyVelocity P) := by
  exact (hP.continuous_fderiv (by simp)).clm_apply continuous_const

def familyFarParameterPairs (d : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) period ×ˢ Icc (0 : ℝ) period)) ∩
    {z | d ≤ |z.2.2 - z.2.1|} ∩ {z | |z.2.2 - z.2.1| ≤ period - d}

theorem isCompact_familyFarParameterPairs (d : ℝ) :
    IsCompact (familyFarParameterPairs d) := by
  have hdiff : Continuous (fun z : ℝ × (ℝ × ℝ) => |z.2.2 - z.2.1|) :=
    ((continuous_snd.comp continuous_snd).sub
      (continuous_fst.comp continuous_snd)).abs
  exact ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
      (isClosed_le continuous_const hdiff)).inter_right
    (isClosed_le hdiff continuous_const)

theorem nonempty_familyFarParameterPairs {d : ℝ}
    (hd0 : 0 ≤ d) (hdhalf : d ≤ period / 2) :
    (familyFarParameterPairs d).Nonempty := by
  refine ⟨(0, (0, period / 2)), ?_⟩
  change (((0 : ℝ) ∈ Icc 0 1 ∧
      ((0 : ℝ) ∈ Icc 0 period ∧ period / 2 ∈ Icc 0 period)) ∧
        d ≤ |period / 2 - 0|) ∧ |period / 2 - 0| ≤ period - d
  refine ⟨⟨⟨⟨le_rfl, zero_le_one⟩,
    ⟨⟨le_rfl, period_pos.le⟩,
      ⟨by linarith [period_pos], by linarith [period_pos]⟩⟩⟩, ?_⟩, ?_⟩
  · have hhalf0 : 0 ≤ period / 2 := by linarith [period_pos]
    simpa [abs_of_nonneg hhalf0] using hdhalf
  · have hhalf0 : 0 ≤ period / 2 := by linarith [period_pos]
    simp only [sub_zero, abs_of_nonneg hhalf0]
    linarith

set_option maxHeartbeats 2000000 in
theorem exists_uniform_c1_knot_family_neighborhood
    {P : ℝ → ℝ → Space}
    (hP : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => P p.1 p.2))
    (hPknot : ∀ s ∈ Icc (0 : ℝ) 1, IsSmoothKnot (fun t => P t s)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ q : ℝ → Space,
      ContDiff ℝ ⊤ q → Function.Periodic q period →
      (∀ t, ‖q t - P t s‖ < ε) →
      (∀ t, ‖velocity q t - velocity (fun x => P x s) t‖ < ε) →
      IsSmoothKnot q := by
  let J : Set ℝ := Icc (0 : ℝ) (2 * period)
  let B : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ J
  have hBcompact : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hBnonempty : B.Nonempty := by
    exact ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩,
      ⟨le_rfl, by linarith [period_pos]⟩⟩⟩
  let v : ℝ × ℝ → Space := fun z => familyVelocity P (z.2, z.1)
  have hvcont : Continuous v :=
    (continuous_familyVelocity hP).comp (continuous_snd.prodMk continuous_fst)
  obtain ⟨z₀, hz₀, hmin⟩ := hBcompact.exists_isMinOn hBnonempty
    hvcont.norm.continuousOn
  let m : ℝ := ‖v z₀‖
  have hmpos : 0 < m := by
    apply norm_pos_iff.mpr
    dsimp [m, v]
    rw [familyVelocity_eq_velocity hP]
    exact (hPknot z₀.1 hz₀.1).regular z₀.2
  have hmle : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ J,
      m ≤ ‖velocity (fun x => P x s) t‖ := by
    intro s hs t ht
    have h := hmin (show (s, t) ∈ B from ⟨hs, ht⟩)
    simpa [m, v, familyVelocity_eq_velocity hP] using h
  have hvuc : UniformContinuousOn v B :=
    hBcompact.uniformContinuousOn_of_continuous hvcont.continuousOn
  obtain ⟨d₀, hd₀0, hd₀⟩ := (Metric.uniformContinuousOn_iff.mp hvuc)
    (m / 4) (div_pos hmpos (by norm_num))
  let d : ℝ := min d₀ (period / 4)
  have hdpos : 0 < d := lt_min hd₀0 (div_pos period_pos (by norm_num))
  have hdle : d ≤ d₀ := min_le_left _ _
  have hdquarter : d ≤ period / 4 := min_le_right _ _
  have hdhalf : d ≤ period / 2 := by linarith [period_pos]
  have hvelNear : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ J, ∀ y ∈ J,
      |x - y| < d →
      ‖velocity (fun z => P z s) x - velocity (fun z => P z s) y‖ < m / 4 := by
    intro s hs x hx y hy hxy
    have h := hd₀ (s, x) (show (s, x) ∈ B from ⟨hs, hx⟩)
      (s, y) (show (s, y) ∈ B from ⟨hs, hy⟩)
    have hdist : dist (s, x) (s, y) < d₀ := by
      rw [dist_prod_same_left, Real.dist_eq]
      exact hxy.trans_le hdle
    have hv := h hdist
    simpa [v, familyVelocity_eq_velocity hP, dist_eq_norm] using hv
  let K := familyFarParameterPairs d
  have hKcompact : IsCompact K := isCompact_familyFarParameterPairs d
  have hKnonempty : K.Nonempty := nonempty_familyFarParameterPairs hdpos.le hdhalf
  let sep : ℝ × (ℝ × ℝ) → ℝ := fun z => ‖P z.2.2 z.1 - P z.2.1 z.1‖
  have hsepcont : Continuous sep :=
    ((hP.continuous.comp
      ((continuous_snd.comp continuous_snd).prodMk continuous_fst)).sub
      (hP.continuous.comp
        ((continuous_fst.comp continuous_snd).prodMk continuous_fst))).norm
  obtain ⟨w₀, hw₀, hsepmin⟩ := hKcompact.exists_isMinOn hKnonempty
    hsepcont.continuousOn
  let eta : ℝ := sep w₀
  have hetapos : 0 < eta := by
    apply norm_pos_iff.mpr
    intro hzero
    have heq : P w₀.2.2 w₀.1 = P w₀.2.1 w₀.1 := sub_eq_zero.mp hzero
    have hs := hw₀.1.1.1
    have hwbox := hw₀.1.1.2
    have hwfar := hw₀.2
    change |w₀.2.2 - w₀.2.1| ≤ period - d at hwfar
    have heqParam := eq_of_curve_eq_of_mem_Icc_of_abs_sub_lt_period
      (hPknot w₀.1 hs) hwbox.2 hwbox.1 heq (by
        exact hwfar.trans_lt (sub_lt_self _ hdpos))
    have hdlower := hw₀.1.2
    change d ≤ |w₀.2.2 - w₀.2.1| at hdlower
    rw [heqParam, sub_self, abs_zero] at hdlower
    exact (not_le_of_gt hdpos) hdlower
  let ε : ℝ := min (m / 4) (eta / 4)
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨ε, hεpos, ?_⟩
  intro s hs q hqsmooth hqperiod hpos hvel
  let p : ℝ → Space := fun t => P t s
  have hp : IsSmoothKnot p := hPknot s hs
  have hεm : ε ≤ m / 4 := min_le_left _ _
  have hεeta : ε ≤ eta / 4 := min_le_right _ _
  have hqregular : ∀ t, velocity q t ≠ 0 := by
    intro t hzero
    have hpv : ‖velocity p t‖ < ε := by
      simpa [p, hzero, norm_neg] using hvel t
    have hpvpos : 0 < ‖velocity p t‖ := norm_pos_iff.mpr (hp.regular t)
    have hperiodicVelocity : Function.Periodic (velocity p) period :=
      periodic_deriv hp.periodic
    obtain ⟨z, hz, hzt⟩ := hperiodicVelocity.exists_mem_Ico period_pos t 0
    have hzJ : z ∈ J := ⟨hz.1, by linarith [hz.2, period_pos]⟩
    have hm := hmle s hs z hzJ
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
      · let a := velocity p x
        let phi : ℝ → ℝ := (innerSL ℝ a) ∘ q
        have hphicont : Continuous phi :=
          (innerSL ℝ a).continuous.comp hqsmooth.continuous
        have hphideriv : ∀ z ∈ Ioo x y, 0 < deriv phi z := by
          intro z hz
          have hxJ : x ∈ J := ⟨hx.1, by linarith [hx.2, period_pos]⟩
          have hzJ : z ∈ J :=
            ⟨hx.1.trans hz.1.le, by linarith [hz.2, hy.2, period_pos]⟩
          have hpnear : ‖velocity p z - velocity p x‖ < m / 4 := by
            rw [norm_sub_rev]
            apply hvelNear s hs x hxJ z hzJ
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hz.1.le)]
            exact (sub_lt_sub_right hz.2 x).trans hnear
          have hqnear : ‖velocity q z - velocity p z‖ < m / 4 :=
            (hvel z).trans_le hεm
          have hdiff : ‖velocity q z - a‖ < m / 2 := by
            calc
              ‖velocity q z - a‖ ≤
                  ‖velocity q z - velocity p z‖ +
                    ‖velocity p z - velocity p x‖ := by
                dsimp [a]
                rw [show velocity q z - velocity p x =
                    (velocity q z - velocity p z) +
                      (velocity p z - velocity p x) by abel]
                exact norm_add_le _ _
              _ < m / 4 + m / 4 := add_lt_add hqnear hpnear
              _ = m / 2 := by ring
          have hanorm : m ≤ ‖a‖ := hmle s hs x hxJ
          have hapos : 0 < ‖a‖ := hanorm.trans_lt' hmpos
          have hinnerLower := neg_le_of_abs_le
            (abs_real_inner_le_norm a (velocity q z - a))
          have hmul : ‖a‖ * ‖velocity q z - a‖ < ‖a‖ * (m / 2) :=
            mul_lt_mul_of_pos_left hdiff hapos
          have hpositive : 0 < inner ℝ a (velocity q z) := by
            rw [show velocity q z = a + (velocity q z - a) by abel,
              inner_add_right, real_inner_self_eq_norm_sq]
            nlinarith [norm_nonneg a]
          have hcomp := (innerSL ℝ a).hasFDerivAt.comp_hasDerivAt z
            ((hqsmooth.differentiable (by simp)).differentiableAt.hasDerivAt)
          have hderivEq : deriv phi z = inner ℝ a (velocity q z) := by
            dsimp [phi]
            simpa [velocity] using hcomp.deriv
          rwa [hderivEq]
        have hmono : StrictMonoOn phi (Icc x y) :=
          strictMonoOn_of_deriv_pos (convex_Icc x y) hphicont.continuousOn (by
            simpa [interior_Icc, hlt.ne] using hphideriv)
        have hstrict := hmono (left_mem_Icc.mpr hlt.le)
          (right_mem_Icc.mpr hlt.le) hlt
        dsimp [phi] at hstrict
        rw [hxy] at hstrict
        exact (lt_irrefl _ hstrict).elim
      · by_cases hwrap : period - gap < d
        · let a := velocity p y
          let phi : ℝ → ℝ := (innerSL ℝ a) ∘ q
          have hyxP : y < x + period := by dsimp [gap] at hgapP ⊢; linarith
          have hphicont : Continuous phi :=
            (innerSL ℝ a).continuous.comp hqsmooth.continuous
          have hphideriv : ∀ z ∈ Ioo y (x + period), 0 < deriv phi z := by
            intro z hz
            have hyJ : y ∈ J := ⟨hy.1, by linarith [hy.2, period_pos]⟩
            have hzJ : z ∈ J := by
              constructor
              · exact hy.1.trans hz.1.le
              · linarith [hz.2, hx.2, period_pos]
            have hpnear : ‖velocity p z - velocity p y‖ < m / 4 := by
              rw [norm_sub_rev]
              apply hvelNear s hs y hyJ z hzJ
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hz.1.le)]
              have : z - y < period - gap := by dsimp [gap]; linarith [hz.2]
              exact this.trans hwrap
            have hqnear : ‖velocity q z - velocity p z‖ < m / 4 :=
              (hvel z).trans_le hεm
            have hdiff : ‖velocity q z - a‖ < m / 2 := by
              calc
                ‖velocity q z - a‖ ≤
                    ‖velocity q z - velocity p z‖ +
                      ‖velocity p z - velocity p y‖ := by
                  dsimp [a]
                  rw [show velocity q z - velocity p y =
                      (velocity q z - velocity p z) +
                        (velocity p z - velocity p y) by abel]
                  exact norm_add_le _ _
                _ < m / 4 + m / 4 := add_lt_add hqnear hpnear
                _ = m / 2 := by ring
            have hanorm : m ≤ ‖a‖ := hmle s hs y hyJ
            have hapos : 0 < ‖a‖ := hanorm.trans_lt' hmpos
            have hinnerLower := neg_le_of_abs_le
              (abs_real_inner_le_norm a (velocity q z - a))
            have hmul : ‖a‖ * ‖velocity q z - a‖ < ‖a‖ * (m / 2) :=
              mul_lt_mul_of_pos_left hdiff hapos
            have hpositive : 0 < inner ℝ a (velocity q z) := by
              rw [show velocity q z = a + (velocity q z - a) by abel,
                inner_add_right, real_inner_self_eq_norm_sq]
              nlinarith [norm_nonneg a]
            have hcomp := (innerSL ℝ a).hasFDerivAt.comp_hasDerivAt z
              ((hqsmooth.differentiable (by simp)).differentiableAt.hasDerivAt)
            have hderivEq : deriv phi z = inner ℝ a (velocity q z) := by
              dsimp [phi]
              simpa [velocity] using hcomp.deriv
            rwa [hderivEq]
          have hmono : StrictMonoOn phi (Icc y (x + period)) :=
            strictMonoOn_of_deriv_pos (convex_Icc y (x + period))
              hphicont.continuousOn (by
                simpa [interior_Icc, hyxP.ne] using hphideriv)
          have hstrict := hmono (left_mem_Icc.mpr hyxP.le)
            (right_mem_Icc.mpr hyxP.le) hyxP
          have hqxP : q (x + period) = q x := hqperiod x
          dsimp [phi] at hstrict
          rw [hqxP, hxy] at hstrict
          exact (lt_irrefl _ hstrict).elim
        · have hfar : (s, (x, y)) ∈ K := by
            refine ⟨⟨⟨hs, ⟨⟨hx.1, hx.2.le⟩, ⟨hy.1, hy.2.le⟩⟩⟩, ?_⟩, ?_⟩
            · change d ≤ |y - x|
              rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]
              exact le_of_not_gt hnear
            · change |y - x| ≤ period - d
              rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]
              linarith [le_of_not_gt hwrap]
          have hsepLower : eta ≤ ‖p y - p x‖ := by
            simpa [eta, sep, p] using hsepmin hfar
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
