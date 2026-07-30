import Submission.RiemannReachable
import Submission.ConformalInjective

open Filter Function Metric Set
open scoped Topology

namespace Submission

lemma NormalizedDiskEmbedding.deriv_ne_zero_at
    {U : Set ℂ} {x : ℂ} (E : NormalizedDiskEmbedding U x)
    (hUo : IsOpen U) {z : ℂ} (hz : z ∈ U) : deriv E.toFun z ≠ 0 :=
  deriv_ne_zero_of_injOn_of_differentiableOn hUo E.differentiableOn E.injOn hz

lemma exists_scaledNormalizedDiskEmbedding
    {f : ℂ → ℂ} {R : ℝ} (hR1 : 1 < R)
    (hf : NormalizedUnivalentOn f R) :
    ∃ C : ℝ, 1 < C ∧
      ∃ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0,
        E.toFun = fun z => f z / (C : ℂ) := by
  have hball : ball (0 : ℂ) 1 ⊆ ball 0 R := ball_subset_ball hR1.le
  have hclosed : closedBall (0 : ℂ) 1 ⊆ ball 0 R := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    rw [mem_ball_zero_iff]
    exact hz.trans_lt hR1
  have hcont : ContinuousOn (fun z => ‖f z‖) (closedBall (0 : ℂ) 1) :=
    (hf.1.continuousOn.mono hclosed).norm
  rcases (isCompact_closedBall (0 : ℂ) 1).bddAbove_image hcont with ⟨M, hM⟩
  let C : ℝ := max M 1 + 1
  have hMC : M < C := by dsimp only [C]; linarith [le_max_left M 1]
  have hC1 : 1 < C := by dsimp only [C]; linarith [le_max_right M 1]
  have hC0 : 0 < C := zero_lt_one.trans hC1
  let e : ℂ → ℂ := fun z => f z / (C : ℂ)
  have hediff : DifferentiableOn ℂ e (ball (0 : ℂ) 1) := by
    intro z hz
    have hzR := hball hz
    exact ((hf.1 z hzR).differentiableAt (isOpen_ball.mem_nhds hzR)).div_const (C : ℂ)
      |>.differentiableWithinAt
  have hemap : MapsTo e (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    have hzclosed : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz
    have hfC : ‖f z‖ < C := (hM ⟨z, hzclosed, rfl⟩).trans_lt hMC
    rw [mem_ball_zero_iff]
    change ‖f z / (C : ℂ)‖ < 1
    rw [norm_div, Complex.norm_real,
      Real.norm_of_nonneg hC0.le, div_lt_iff₀ hC0]
    simpa using hfC
  have heinj : (ball (0 : ℂ) 1).InjOn e := by
    intro z hz w hw heq
    apply hf.2.1 (hball hz) (hball hw)
    have hC : (C : ℂ) ≠ 0 := by exact_mod_cast hC0.ne'
    dsimp only [e] at heq
    field_simp [hC] at heq
    exact heq
  have hezero : e 0 = 0 := by simp [e, hf.2.2.1]
  have hederiv : deriv e 0 ≠ 0 := by
    have hzeroR : (0 : ℂ) ∈ ball 0 R := mem_ball_self (zero_lt_one.trans hR1)
    have hfAt : DifferentiableAt ℂ f 0 :=
      (hf.1 0 hzeroR).differentiableAt (isOpen_ball.mem_nhds hzeroR)
    have heAt : HasDerivAt e (1 / (C : ℂ)) 0 := by
      simpa only [e, hf.2.2.2] using hfAt.hasDerivAt.div_const (C : ℂ)
    rw [heAt.deriv]
    exact div_ne_zero one_ne_zero (by exact_mod_cast hC0.ne')
  exact ⟨C, hC1, ⟨⟨e, hediff, hemap, heinj, hezero, hederiv⟩, rfl⟩⟩

lemma normalizedDiskEmbedding_derivNorm_le_one_unitBall
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    ‖deriv E.toFun 0‖ ≤ 1 := by
  apply Complex.norm_deriv_le_one_of_mapsTo_ball E.differentiableOn _ zero_lt_one
  intro z hz
  rw [E.map_base]
  exact ball_subset_closedBall (E.mapsTo hz)

noncomputable def reachableNormalizedDiskEmbeddingDerivSup
    {U : Set ℂ} {x : ℂ} (E₀ : NormalizedDiskEmbedding U x) : ℝ :=
  sSup (Set.range fun E : ReachableNormalizedDiskEmbedding E₀ =>
    ‖deriv E.1.toFun x‖)

noncomputable def normalizedDiskEmbeddingDerivSup (U : Set ℂ) (x : ℂ) : ℝ :=
  sSup (Set.range fun E : NormalizedDiskEmbedding U x => ‖deriv E.toFun x‖)

lemma normalizedDiskEmbedding_derivNorm_bddAbove
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hx : x ∈ U) :
    BddAbove (Set.range fun E : NormalizedDiskEmbedding U x =>
      ‖deriv E.toFun x‖) := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hx)
  refine ⟨1 / R, ?_⟩
  rintro y ⟨E, rfl⟩
  apply Complex.norm_deriv_le_div_of_mapsTo_ball
    (E.differentiableOn.mono hRU) _ hR
  intro z hz
  have hzBall := E.mapsTo (hRU hz)
  have hzNormLt : ‖E z‖ < 1 := by
    simpa [mem_ball_zero_iff] using hzBall
  have hzNorm : ‖E z‖ ≤ 1 := by
    exact hzNormLt.le
  simpa [E.map_base, mem_closedBall, dist_zero_right] using hzNorm

lemma normalizedDiskEmbedding_derivNorm_range_nonempty
    {U : Set ℂ} {x : ℂ} (hE : Nonempty (NormalizedDiskEmbedding U x)) :
    (Set.range fun E : NormalizedDiskEmbedding U x =>
      ‖deriv E.toFun x‖).Nonempty := by
  rcases hE with ⟨E⟩
  exact ⟨‖deriv E.toFun x‖, ⟨E, rfl⟩⟩

lemma normalizedDiskEmbeddingDerivSup_pos
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hx : x ∈ U)
    (hE : Nonempty (NormalizedDiskEmbedding U x)) :
    0 < normalizedDiskEmbeddingDerivSup U x := by
  rcases hE with ⟨E⟩
  have hb := normalizedDiskEmbedding_derivNorm_bddAbove hUo hx
  have hle : ‖deriv E.toFun x‖ ≤ normalizedDiskEmbeddingDerivSup U x := by
    exact le_csSup hb ⟨E, rfl⟩
  exact (norm_pos_iff.mpr E.deriv_ne_zero).trans_le hle

lemma normalizedDiskEmbedding_derivNorm_le_sup
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hx : x ∈ U)
    (E : NormalizedDiskEmbedding U x) :
    ‖deriv E.toFun x‖ ≤ normalizedDiskEmbeddingDerivSup U x := by
  exact le_csSup (normalizedDiskEmbedding_derivNorm_bddAbove hUo hx) ⟨E, rfl⟩

lemma exists_normalizedDiskEmbedding_derivNorm_tendsto_sup
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hx : x ∈ U)
    (hE : Nonempty (NormalizedDiskEmbedding U x)) :
    ∃ E : ℕ → NormalizedDiskEmbedding U x,
      Tendsto (fun j => ‖deriv (E j).toFun x‖) atTop
        (𝓝 (normalizedDiskEmbeddingDerivSup U x)) := by
  let S : Set ℝ := Set.range fun E : NormalizedDiskEmbedding U x =>
    ‖deriv E.toFun x‖
  have hSne : S.Nonempty :=
    normalizedDiskEmbedding_derivNorm_range_nonempty hE
  have hSbdd : BddAbove S :=
    normalizedDiskEmbedding_derivNorm_bddAbove hUo hx
  rcases exists_seq_tendsto_sSup hSne hSbdd with ⟨d, hdmono, hdtend, hdmem⟩
  have hwitness : ∀ j, ∃ E : NormalizedDiskEmbedding U x,
      ‖deriv E.toFun x‖ = d j := by
    intro j
    simpa only [S, Set.mem_range] using hdmem j
  choose E hEderiv using hwitness
  refine ⟨E, ?_⟩
  simpa only [normalizedDiskEmbeddingDerivSup, S, hEderiv] using hdtend

lemma reachableNormalizedDiskEmbedding_derivNorm_bddAbove
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hx : x ∈ U)
    (E₀ : NormalizedDiskEmbedding U x) :
    BddAbove (Set.range fun E : ReachableNormalizedDiskEmbedding E₀ =>
      ‖deriv E.1.toFun x‖) := by
  apply (normalizedDiskEmbedding_derivNorm_bddAbove hUo hx).mono
  rintro y ⟨E, rfl⟩
  exact ⟨E.1, rfl⟩

lemma reachableNormalizedDiskEmbeddingDerivSup_pos
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hx : x ∈ U)
    (E₀ : NormalizedDiskEmbedding U x) :
    0 < reachableNormalizedDiskEmbeddingDerivSup E₀ := by
  let E : ReachableNormalizedDiskEmbedding E₀ :=
    ⟨E₀, ⟨NormalizedDiskEmbedding.ReachableFrom.refl⟩⟩
  have hle : ‖deriv E.1.toFun x‖ ≤
      reachableNormalizedDiskEmbeddingDerivSup E₀ := by
    exact le_csSup (reachableNormalizedDiskEmbedding_derivNorm_bddAbove hUo hx E₀)
      ⟨E, rfl⟩
  exact (norm_pos_iff.mpr E₀.deriv_ne_zero).trans_le hle

lemma reachableNormalizedDiskEmbedding_derivNorm_le_sup
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hx : x ∈ U)
    {E₀ : NormalizedDiskEmbedding U x}
    (E : ReachableNormalizedDiskEmbedding E₀) :
    ‖deriv E.1.toFun x‖ ≤ reachableNormalizedDiskEmbeddingDerivSup E₀ := by
  exact le_csSup (reachableNormalizedDiskEmbedding_derivNorm_bddAbove hUo hx E₀)
    ⟨E, rfl⟩

lemma exists_reachableNormalizedDiskEmbedding_derivNorm_tendsto_sup
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hx : x ∈ U)
    (E₀ : NormalizedDiskEmbedding U x) :
    ∃ E : ℕ → ReachableNormalizedDiskEmbedding E₀,
      Tendsto (fun j => ‖deriv (E j).1.toFun x‖) atTop
        (nhds (reachableNormalizedDiskEmbeddingDerivSup E₀)) := by
  let S : Set ℝ := Set.range fun E : ReachableNormalizedDiskEmbedding E₀ =>
    ‖deriv E.1.toFun x‖
  have hSne : S.Nonempty := Set.range_nonempty _
  have hSbdd : BddAbove S :=
    reachableNormalizedDiskEmbedding_derivNorm_bddAbove hUo hx E₀
  rcases exists_seq_tendsto_sSup hSne hSbdd with ⟨d, hdmono, hdtend, hdmem⟩
  have hwitness : ∀ j, ∃ E : ReachableNormalizedDiskEmbedding E₀,
      ‖deriv E.1.toFun x‖ = d j := by
    intro j
    simpa only [S, Set.mem_range] using hdmem j
  choose E hEderiv using hwitness
  refine ⟨E, ?_⟩
  simpa only [reachableNormalizedDiskEmbeddingDerivSup, S, hEderiv] using hdtend

lemma omittedPoint_derivative_norm_eq_gain
    {a b d : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    (hb : b ∈ ball (0 : ℂ) 1) (hbpow : b ^ 2 = -a) :
    ‖(1 - starRingEnd ℂ b * b)⁻¹ *
        (((1 - starRingEnd ℂ a * a) * d) / (2 * b))‖ =
      (1 - ‖a‖)⁻¹ * ((1 - ‖a‖ ^ 2) / (2 * ‖b‖)) * ‖d‖ := by
  have haNorm : ‖a‖ < 1 := by simpa [mem_ball_zero_iff] using ha
  have hbNorm : ‖b‖ < 1 := by simpa [mem_ball_zero_iff] using hb
  have hnormRel : ‖b‖ ^ 2 = ‖a‖ := by
    have h := congrArg norm hbpow
    simpa [norm_pow] using h
  have hnormTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_mul, norm_inv, norm_one_sub_conj_mul_self hbNorm.le,
    norm_div, norm_mul, norm_one_sub_conj_mul_self haNorm.le,
    norm_mul, hnormTwo, hnormRel]
  ring

lemma omittedPoint_gain_uniform {r s rho : ℝ}
    (hs : 0 < s) (hrel : s ^ 2 = r) (hr : r ≤ rho)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    1 + (1 - rho) ^ 2 / 8 ≤
      (1 - r)⁻¹ * ((1 - r ^ 2) / (2 * s)) := by
  have hr1 : r < 1 := hr.trans_lt hrho1
  have hs1 : s < 1 := by
    by_contra hnot
    have : 1 ≤ s := le_of_not_gt hnot
    nlinarith [sq_nonneg (s - 1)]
  have hsk : s ≤ (1 + rho) / 2 := by
    by_contra hnot
    have hlt : (1 + rho) / 2 < s := lt_of_not_ge hnot
    have hsq : rho < ((1 + rho) / 2) ^ 2 := by
      nlinarith [sq_pos_of_pos (sub_pos.mpr hrho1)]
    nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos_of_nonneg_of_pos
      (by positivity : 0 ≤ (1 + rho) / 2) hs)]
  have hdiff0 : 0 ≤ (1 - rho) / 2 := by linarith
  have hdiff : (1 - rho) / 2 ≤ 1 - s := by linarith
  have hsqDiff : ((1 - rho) / 2) ^ 2 ≤ (1 - s) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hdiff)
      (add_nonneg hdiff0 (by linarith : 0 ≤ 1 - s))
    nlinarith
  have hgainEq :
      (1 - r)⁻¹ * ((1 - r ^ 2) / (2 * s)) = (1 + r) / (2 * s) := by
    have h1r : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
    field_simp [h1r, ne_of_gt hs]
    ring
  rw [hgainEq]
  rw [le_div_iff₀ (by positivity)]
  have hsle : s ≤ 1 := hs1.le
  nlinarith

lemma eventually_ball_subset_normalizedDiskEmbedding_image
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hx : x ∈ U) {E : ℕ → NormalizedDiskEmbedding U x}
    (hE : Tendsto (fun j => ‖deriv (E j).toFun x‖) atTop
      (𝓝 (normalizedDiskEmbeddingDerivSup U x)))
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    ∀ᶠ j in atTop, ball (0 : ℂ) rho ⊆ (E j).toFun '' U := by
  let M := normalizedDiskEmbeddingDerivSup U x
  let delta := (1 - rho) ^ 2 / 8
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hM : 0 < M :=
    normalizedDiskEmbeddingDerivSup_pos hUo hx ⟨E 0⟩
  have hscaled : Tendsto
      (fun j => (1 + delta) * ‖deriv (E j).toFun x‖) atTop
      (𝓝 ((1 + delta) * M)) := by
    simpa only [M] using hE.const_mul (1 + delta)
  have hMlt : M < (1 + delta) * M := by nlinarith
  filter_upwards [hscaled.eventually_const_lt hMlt] with j hj
  intro a ha
  by_contra haImage
  have ha1 : a ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at ha ⊢
    exact ha.trans hrho1
  have haRho : ‖a‖ ≤ rho := by
    have haNormRho : ‖a‖ < rho := by
      simpa [mem_ball_zero_iff] using ha
    exact haNormRho.le
  have ha0 : a ≠ 0 := by
    intro hzero
    apply haImage
    exact ⟨x, hx, by simpa [hzero] using (E j).map_base⟩
  rcases (E j).exists_omittedPointImprovementData
      hUo hUc hx ha1 haImage with ⟨F, b, hbpow, hb, hderiv⟩
  have hb0 : 0 < ‖b‖ := by
    rw [norm_pos_iff]
    intro hzero
    have h := hbpow
    rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at h
    exact ha0 (neg_eq_zero.mp h.symm)
  have hnormRel : ‖b‖ ^ 2 = ‖a‖ := by
    have h := congrArg norm hbpow
    simpa [norm_pow] using h
  have hgain :
      1 + delta ≤
        (1 - ‖a‖)⁻¹ * ((1 - ‖a‖ ^ 2) / (2 * ‖b‖)) := by
    exact omittedPoint_gain_uniform hb0 hnormRel haRho hrho0 hrho1
  have hFnorm :
      ‖deriv F.toFun x‖ =
        (1 - ‖a‖)⁻¹ * ((1 - ‖a‖ ^ 2) / (2 * ‖b‖)) *
          ‖deriv (E j).toFun x‖ := by
    rw [hderiv]
    exact omittedPoint_derivative_norm_eq_gain ha1 hb hbpow
  have hprod :
      (1 + delta) * ‖deriv (E j).toFun x‖ ≤ ‖deriv F.toFun x‖ := by
    rw [hFnorm]
    exact mul_le_mul_of_nonneg_right hgain (norm_nonneg _)
  have hFle : ‖deriv F.toFun x‖ ≤ M := by
    exact normalizedDiskEmbedding_derivNorm_le_sup hUo hx F
  exact (not_lt_of_ge hFle) (hj.trans_le hprod)

lemma eventually_ball_subset_reachableNormalizedDiskEmbedding_image
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hx : x ∈ U) {E₀ : NormalizedDiskEmbedding U x}
    {E : ℕ → ReachableNormalizedDiskEmbedding E₀}
    (hE : Tendsto (fun j => ‖deriv (E j).1.toFun x‖) atTop
      (nhds (reachableNormalizedDiskEmbeddingDerivSup E₀)))
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    ∀ᶠ j in atTop, ball (0 : ℂ) rho ⊆ (E j).1.toFun '' U := by
  classical
  let M := reachableNormalizedDiskEmbeddingDerivSup E₀
  let delta := (1 - rho) ^ 2 / 8
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hM : 0 < M :=
    reachableNormalizedDiskEmbeddingDerivSup_pos hUo hx E₀
  have hscaled : Tendsto
      (fun j => (1 + delta) * ‖deriv (E j).1.toFun x‖) atTop
      (nhds ((1 + delta) * M)) := by
    simpa only [M] using hE.const_mul (1 + delta)
  have hMlt : M < (1 + delta) * M := by nlinarith
  filter_upwards [hscaled.eventually_const_lt hMlt] with j hj
  intro a ha
  by_contra haImage
  have ha1 : a ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at ha ⊢
    exact ha.trans hrho1
  have haRho : ‖a‖ ≤ rho := by
    have haNormRho : ‖a‖ < rho := by
      simpa [mem_ball_zero_iff] using ha
    exact haNormRho.le
  have ha0 : a ≠ 0 := by
    intro hzero
    apply haImage
    exact ⟨x, hx, by simpa [hzero] using (E j).1.map_base⟩
  rcases (E j).1.exists_omittedPointImprovementData_full
      hUo hUc hx ha1 haImage with
    ⟨F, b, q, hbpow, hb, hqpow, hbq, hF, hderiv⟩
  let step : (E j).1.OmittedPointStep F :=
    ⟨a, b, q, ha1, haImage, hbpow, hb, hqpow, hbq, hF, hderiv⟩
  let F_reachable : ReachableNormalizedDiskEmbedding E₀ :=
    ⟨F, ⟨NormalizedDiskEmbedding.ReachableFrom.step (E j).2.some step⟩⟩
  have hb0 : 0 < ‖b‖ := by
    rw [norm_pos_iff]
    intro hzero
    have h := hbpow
    rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at h
    exact ha0 (neg_eq_zero.mp h.symm)
  have hnormRel : ‖b‖ ^ 2 = ‖a‖ := by
    have h := congrArg norm hbpow
    simpa [norm_pow] using h
  have hgain :
      1 + delta ≤
        (1 - ‖a‖)⁻¹ * ((1 - ‖a‖ ^ 2) / (2 * ‖b‖)) := by
    exact omittedPoint_gain_uniform hb0 hnormRel haRho hrho0 hrho1
  have hFnorm :
      ‖deriv F.toFun x‖ =
        (1 - ‖a‖)⁻¹ * ((1 - ‖a‖ ^ 2) / (2 * ‖b‖)) *
          ‖deriv (E j).1.toFun x‖ := by
    rw [hderiv]
    exact omittedPoint_derivative_norm_eq_gain ha1 hb hbpow
  have hprod :
      (1 + delta) * ‖deriv (E j).1.toFun x‖ ≤ ‖deriv F.toFun x‖ := by
    rw [hFnorm]
    exact mul_le_mul_of_nonneg_right hgain (norm_nonneg _)
  have hFle : ‖deriv F.toFun x‖ ≤ M := by
    exact reachableNormalizedDiskEmbedding_derivNorm_le_sup hUo hx F_reachable
  exact (not_lt_of_ge hFle) (hj.trans_le hprod)

lemma exists_reachableNormalizedDiskEmbeddings_exhausting_unitBall
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hx : x ∈ U) (E₀ : NormalizedDiskEmbedding U x) :
    ∃ E : ℕ → ReachableNormalizedDiskEmbedding E₀,
      Tendsto (fun j => ‖deriv (E j).1.toFun x‖) atTop
          (nhds (reachableNormalizedDiskEmbeddingDerivSup E₀)) ∧
        ∀ rho : ℝ, 0 ≤ rho → rho < 1 →
          ∀ᶠ j in atTop, ball (0 : ℂ) rho ⊆ (E j).1.toFun '' U := by
  rcases exists_reachableNormalizedDiskEmbedding_derivNorm_tendsto_sup
      hUo hx E₀ with ⟨E, hE⟩
  refine ⟨E, hE, ?_⟩
  intro rho hrho0 hrho1
  exact eventually_ball_subset_reachableNormalizedDiskEmbedding_image
    hUo hUc hx hE hrho0 hrho1

lemma exists_normalizedDiskEmbeddings_exhausting_unitBall
    {U : Set ℂ} {x : ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    (hU : U ≠ Set.univ) (hx : x ∈ U) :
    ∃ E : ℕ → NormalizedDiskEmbedding U x,
      Tendsto (fun j => ‖deriv (E j).toFun x‖) atTop
          (𝓝 (normalizedDiskEmbeddingDerivSup U x)) ∧
        ∀ rho : ℝ, 0 ≤ rho → rho < 1 →
          ∀ᶠ j in atTop, ball (0 : ℂ) rho ⊆ (E j).toFun '' U := by
  have hnonempty := exists_normalizedDiskEmbedding hUo hUc hU hx
  rcases exists_normalizedDiskEmbedding_derivNorm_tendsto_sup
      hUo hx hnonempty with ⟨E, hE⟩
  refine ⟨E, hE, ?_⟩
  intro rho hrho0 hrho1
  exact eventually_ball_subset_normalizedDiskEmbedding_image
    hUo hUc hx hE hrho0 hrho1

noncomputable def NormalizedDiskEmbedding.imageInverse
    {U : Set ℂ} {x : ℂ} (E : NormalizedDiskEmbedding U x) (w : ℂ) : ℂ := by
  classical
  exact if hw : w ∈ E.toFun '' U then Classical.choose hw else x

lemma NormalizedDiskEmbedding.imageInverse_mem
    {U : Set ℂ} {x : ℂ} (E : NormalizedDiskEmbedding U x)
    {w : ℂ} (hw : w ∈ E.toFun '' U) : E.imageInverse w ∈ U := by
  simpa only [imageInverse, dif_pos hw] using (Classical.choose_spec hw).1

lemma NormalizedDiskEmbedding.apply_imageInverse
    {U : Set ℂ} {x : ℂ} (E : NormalizedDiskEmbedding U x)
    {w : ℂ} (hw : w ∈ E.toFun '' U) : E (E.imageInverse w) = w := by
  simpa only [imageInverse, dif_pos hw] using (Classical.choose_spec hw).2

lemma NormalizedDiskEmbedding.imageInverse_apply
    {U : Set ℂ} {x z : ℂ} (E : NormalizedDiskEmbedding U x)
    (hz : z ∈ U) : E.imageInverse (E z) = z := by
  have hw : E z ∈ E.toFun '' U := ⟨z, hz, rfl⟩
  exact E.injOn (E.imageInverse_mem hw) hz (E.apply_imageInverse hw)

@[simp]
lemma NormalizedDiskEmbedding.imageInverse_zero
    {U : Set ℂ} {x : ℂ} (E : NormalizedDiskEmbedding U x)
    (hx : x ∈ U) : E.imageInverse 0 = x := by
  rw [← E.map_base]
  exact E.imageInverse_apply hx

lemma NormalizedDiskEmbedding.imageInverse_hasStrictDerivAt
    {U : Set ℂ} {x : ℂ} (E : NormalizedDiskEmbedding U x)
    (hUo : IsOpen U) {w : ℂ} (hw : w ∈ E.toFun '' U) :
    HasStrictDerivAt E.imageInverse
      (deriv E.toFun (E.imageInverse w))⁻¹ w := by
  let z := E.imageInverse w
  have hz : z ∈ U := E.imageInverse_mem hw
  have hEw : E z = w := E.apply_imageInverse hw
  have hEa : AnalyticAt ℂ E.toFun z :=
    (E.differentiableOn.analyticOnNhd hUo) z hz
  have hleft : ∀ᶠ y in nhds z, E.imageInverse (E y) = y := by
    filter_upwards [hUo.mem_nhds hz] with y hy
    exact E.imageInverse_apply hy
  have hinv := hEa.hasStrictDerivAt.to_local_left_inverse
    (E.deriv_ne_zero_at hUo hz) hleft
  rw [hEw] at hinv
  exact hinv

lemma NormalizedDiskEmbedding.imageInverse_differentiableOn
    {U : Set ℂ} {x : ℂ} (E : NormalizedDiskEmbedding U x)
    (hUo : IsOpen U) : DifferentiableOn ℂ E.imageInverse (E.toFun '' U) := by
  intro w hw
  exact (E.imageInverse_hasStrictDerivAt hUo hw).hasDerivAt.differentiableAt
    |>.differentiableWithinAt

lemma NormalizedDiskEmbedding.imageInverse_hasStrictDerivAt_zero
    {U : Set ℂ} {x : ℂ} (E : NormalizedDiskEmbedding U x)
    (hUo : IsOpen U) (hx : x ∈ U) :
    HasStrictDerivAt E.imageInverse (deriv E.toFun x)⁻¹ 0 := by
  have hzero : 0 ∈ E.toFun '' U := ⟨x, hx, E.map_base⟩
  simpa [E.imageInverse_zero hx] using
    E.imageInverse_hasStrictDerivAt hUo hzero

lemma NormalizedDiskEmbedding.imageInverse_injOn
    {U : Set ℂ} {x : ℂ} (E : NormalizedDiskEmbedding U x) :
    (E.toFun '' U).InjOn E.imageInverse := by
  intro w hw v hv heq
  calc
    w = E (E.imageInverse w) := (E.apply_imageInverse hw).symm
    _ = E (E.imageInverse v) := congrArg E.toFun heq
    _ = v := E.apply_imageInverse hv

lemma NormalizedDiskEmbedding.radius_le_derivNorm_of_ball_subset_image
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    {rho : ℝ} (hrho : 0 < rho)
    (hsub : ball (0 : ℂ) rho ⊆ E.toFun '' ball (0 : ℂ) 1) :
    rho ≤ ‖deriv E.toFun 0‖ := by
  let G := E.imageInverse
  have hGdiff : DifferentiableOn ℂ G (ball (0 : ℂ) rho) :=
    (E.imageInverse_differentiableOn isOpen_ball).mono hsub
  have hGzero : G 0 = 0 := E.imageInverse_zero (mem_ball_self zero_lt_one)
  have hGmap : MapsTo G (ball (0 : ℂ) rho) (closedBall (G 0) 1) := by
    intro w hw
    have hmem := E.imageInverse_mem (hsub hw)
    rw [hGzero]
    exact ball_subset_closedBall hmem
  have hSchwarz :=
    Complex.norm_deriv_le_div_of_mapsTo_ball hGdiff hGmap hrho
  have hGderiv : deriv G 0 = (deriv E.toFun 0)⁻¹ :=
    (E.imageInverse_hasStrictDerivAt_zero isOpen_ball
      (mem_ball_self zero_lt_one)).hasDerivAt.deriv
  rw [hGderiv, norm_inv] at hSchwarz
  have hd : 0 < ‖deriv E.toFun 0‖ := norm_pos_iff.mpr E.deriv_ne_zero
  have hmul := mul_le_mul_of_nonneg_left hSchwarz
    (mul_nonneg hrho.le (norm_nonneg (deriv E.toFun 0)))
  calc
    rho = (rho * ‖deriv E.toFun 0‖) * ‖deriv E.toFun 0‖⁻¹ := by
      field_simp [ne_of_gt hd]
    _ ≤ (rho * ‖deriv E.toFun 0‖) * (1 / rho) := hmul
    _ = ‖deriv E.toFun 0‖ := by field_simp [ne_of_gt hrho]

lemma reachableNormalizedDiskEmbeddingDerivSup_unitBall_eq_one
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    reachableNormalizedDiskEmbeddingDerivSup E₀ = 1 := by
  let M := reachableNormalizedDiskEmbeddingDerivSup E₀
  have hMpos : 0 < M :=
    reachableNormalizedDiskEmbeddingDerivSup_pos isOpen_ball
      (mem_ball_self zero_lt_one) E₀
  have hMle : M ≤ 1 := by
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨E, rfl⟩
    exact normalizedDiskEmbedding_derivNorm_le_one_unitBall E.1
  apply le_antisymm hMle
  by_contra hnot
  have hMlt : M < 1 := lt_of_not_ge hnot
  let rho := (M + 1) / 2
  have hrho0 : 0 ≤ rho := by dsimp only [rho]; linarith
  have hrho : 0 < rho := by dsimp only [rho]; linarith
  have hrho1 : rho < 1 := by dsimp only [rho]; linarith
  have hMrho : M < rho := by dsimp only [rho]; linarith
  rcases exists_reachableNormalizedDiskEmbeddings_exhausting_unitBall
      isOpen_ball (isSimplyConnected_ball 0 zero_lt_one)
      (mem_ball_self zero_lt_one) E₀ with ⟨E, hE, hexhaust⟩
  obtain ⟨j, hj⟩ := (hexhaust rho hrho0 hrho1).exists
  have hrhoDeriv := (E j).1.radius_le_derivNorm_of_ball_subset_image hrho hj
  have hDerivM := reachableNormalizedDiskEmbedding_derivNorm_le_sup
    isOpen_ball (mem_ball_self zero_lt_one) (E j)
  exact (not_lt_of_ge hDerivM) (hMrho.trans_le hrhoDeriv)

lemma exists_reachableNormalizedDiskEmbeddings_exhausting_unitBall_tendsto_one
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    ∃ E : ℕ → ReachableNormalizedDiskEmbedding E₀,
      Tendsto (fun j => ‖deriv (E j).1.toFun 0‖) atTop (nhds 1) ∧
        ∀ rho : ℝ, 0 ≤ rho → rho < 1 →
          ∀ᶠ j in atTop,
            ball (0 : ℂ) rho ⊆ (E j).1.toFun '' ball (0 : ℂ) 1 := by
  rcases exists_reachableNormalizedDiskEmbeddings_exhausting_unitBall
      isOpen_ball (isSimplyConnected_ball 0 zero_lt_one)
      (mem_ball_self zero_lt_one) E₀ with ⟨E, hE, hexhaust⟩
  refine ⟨E, ?_, hexhaust⟩
  simpa only [reachableNormalizedDiskEmbeddingDerivSup_unitBall_eq_one E₀] using hE

end Submission
