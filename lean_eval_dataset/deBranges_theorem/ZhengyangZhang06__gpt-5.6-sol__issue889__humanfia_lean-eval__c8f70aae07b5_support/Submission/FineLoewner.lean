import Submission.FormalLogarithmic

open Function Metric Set

namespace Submission

lemma hasDerivAt_of_continuousAt_exp_comp_eq
    {l u : ℂ → ℂ} {z u' : ℂ}
    (hl : ContinuousAt l z) (hu : HasDerivAt u u' z)
    (heq : Complex.exp ∘ l =ᶠ[nhds z] u) :
    HasDerivAt l (u' / u z) z := by
  have hexp : HasDerivAt Complex.exp (Complex.exp (l z)) (l z) :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id (l z)).cexp
  have h := hexp.of_comp_left hl hu (Complex.exp_ne_zero _) heq
  have hz : Complex.exp (l z) = u z := heq.eq_of_nhds
  rwa [hz] at h

/-- The image of a normalized disk embedding cannot contain a circle while
omitting a point enclosed by that circle.  This is the elementary winding
argument needed to choose every omitted-point step on one prescribed circle. -/
lemma NormalizedDiskEmbedding.ball_subset_image_of_sphere_subset_image
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    {rho : ℝ} (hrho : 0 < rho)
    (hsphere : sphere (0 : ℂ) rho ⊆ E.toFun '' ball (0 : ℂ) 1) :
    ball (0 : ℂ) rho ⊆ E.toFun '' ball (0 : ℂ) 1 := by
  intro a ha
  by_contra haImage
  let u : ℂ → ℂ := fun z ↦ E z - a
  have hucont : ContinuousOn u (ball (0 : ℂ) 1) :=
    E.differentiableOn.continuousOn.sub continuousOn_const
  have hu0 : 0 ∉ u '' ball (0 : ℂ) 1 := by
    rintro ⟨z, hz, hzero⟩
    apply haImage
    refine ⟨z, hz, ?_⟩
    dsimp only [u] at hzero
    exact sub_eq_zero.mp hzero
  rcases Complex.exists_continuousOn_eqOn_exp_comp
      (isSimplyConnected_ball (0 : ℂ) zero_lt_one) isOpen_ball hucont hu0 with
    ⟨l, hlcont, hlexp⟩
  have hprimitive : ∀ w ∈ sphere (0 : ℂ) rho,
      HasDerivWithinAt (l ∘ E.imageInverse) ((w - a)⁻¹)
        (sphere (0 : ℂ) rho) w := by
    intro w hw
    have hwImage : w ∈ E.toFun '' ball (0 : ℂ) 1 := hsphere hw
    have hz : E.imageInverse w ∈ ball (0 : ℂ) 1 :=
      E.imageInverse_mem hwImage
    have hEw : E (E.imageInverse w) = w := E.apply_imageInverse hwImage
    have hEAt : DifferentiableAt ℂ E.toFun (E.imageInverse w) :=
      E.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz)
    have huAt : HasDerivAt u (deriv E.toFun (E.imageInverse w))
        (E.imageInverse w) := by
      simpa only [u] using hEAt.hasDerivAt.sub_const a
    have hlexp' : Complex.exp ∘ l =ᶠ[nhds (E.imageInverse w)] u := by
      filter_upwards [isOpen_ball.mem_nhds hz] with z hz'
      exact hlexp hz'
    have hlAt : HasDerivAt l
        (deriv E.toFun (E.imageInverse w) / u (E.imageInverse w))
        (E.imageInverse w) :=
      hasDerivAt_of_continuousAt_exp_comp_eq
        (hlcont.continuousAt (isOpen_ball.mem_nhds hz)) huAt hlexp'
    have hGAt := (E.imageInverse_hasStrictDerivAt isOpen_ball hwImage).hasDerivAt
    have hcomp := hlAt.comp w hGAt
    apply hcomp.hasDerivWithinAt.congr_deriv
    dsimp only [u] at hcomp ⊢
    rw [hEw]
    have hderiv : deriv E.toFun (E.imageInverse w) ≠ 0 :=
      E.deriv_ne_zero_at isOpen_ball hz
    field_simp [hderiv]
  have hzero : (∮ z in C((0 : ℂ), rho), (z - a)⁻¹) = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt hrho.le hprimitive
  have hnonzero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  apply hnonzero
  rw [← circleIntegral.integral_sub_inv_of_mem_ball ha, hzero]

lemma NormalizedDiskEmbedding.exists_omitted_on_sphere_of_deriv_norm_lt
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    {rho : ℝ} (hrho : 0 < rho) (_hrho1 : rho < 1)
    (hderiv : ‖deriv E.toFun 0‖ < rho) :
    ∃ a ∈ sphere (0 : ℂ) rho,
      a ∉ E.toFun '' ball (0 : ℂ) 1 := by
  by_contra hnot
  have hsphere : sphere (0 : ℂ) rho ⊆ E.toFun '' ball (0 : ℂ) 1 := by
    intro a haSphere
    by_contra haImage
    exact hnot ⟨a, haSphere, haImage⟩
  have hball := E.ball_subset_image_of_sphere_subset_image hrho hsphere
  have hle := E.radius_le_derivNorm_of_ball_subset_image hrho hball
  exact (not_le_of_gt hderiv) hle

structure FineNextEmbeddingData
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) (rho : ℝ) where
  next : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0
  progress :
    (rho ≤ ‖deriv E.toFun 0‖ ∧ next = E) ∨
      (‖deriv E.toFun 0‖ < rho ∧
        ∃ step : E.OmittedPointStep next, ‖step.a‖ = rho)

lemma nonempty_fineNextEmbeddingData
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    Nonempty (FineNextEmbeddingData E rho) := by
  by_cases hstop : rho ≤ ‖deriv E.toFun 0‖
  · exact ⟨⟨E, Or.inl ⟨hstop, rfl⟩⟩⟩
  · have hderiv : ‖deriv E.toFun 0‖ < rho := lt_of_not_ge hstop
    rcases E.exists_omitted_on_sphere_of_deriv_norm_lt hrho hrho1 hderiv with
      ⟨a, haSphere, haOmitted⟩
    have haNorm : ‖a‖ = rho := by
      simpa [mem_sphere, dist_zero_right] using haSphere
    have haBall : a ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, haNorm]
      exact hrho1
    rcases E.exists_omittedPointImprovementData_full isOpen_ball
        (isSimplyConnected_ball (0 : ℂ) zero_lt_one)
        (mem_ball_self zero_lt_one) haBall haOmitted with
      ⟨F, b, q, hbpow, hb, hqpow, hbq, hF, hderivF⟩
    let step : E.OmittedPointStep F :=
      ⟨a, b, q, haBall, haOmitted, hbpow, hb, hqpow, hbq, hF, hderivF⟩
    exact ⟨⟨F, Or.inr ⟨hderiv, step, by simpa only [step] using haNorm⟩⟩⟩

noncomputable def fineNextEmbeddingData
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) :
    FineNextEmbeddingData E rho :=
  Classical.choice (nonempty_fineNextEmbeddingData E hrho hrho1)

noncomputable def fineEmbeddingChain
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) :
    ℕ → NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0
  | 0 => E₀
  | j + 1 =>
      (fineNextEmbeddingData (fineEmbeddingChain E₀ rho hrho hrho1 j)
        rho hrho hrho1).next

lemma fineEmbeddingChain_succ_progress
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) (j : ℕ) :
    (rho ≤ ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ ∧
        fineEmbeddingChain E₀ rho hrho hrho1 (j + 1) =
          fineEmbeddingChain E₀ rho hrho hrho1 j) ∨
      (‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ < rho ∧
        ∃ step : (fineEmbeddingChain E₀ rho hrho hrho1 j).OmittedPointStep
            (fineEmbeddingChain E₀ rho hrho hrho1 (j + 1)),
          ‖step.a‖ = rho) := by
  exact (fineNextEmbeddingData
    (fineEmbeddingChain E₀ rho hrho hrho1 j) rho hrho hrho1).progress

noncomputable def fineLoewnerGain (rho : ℝ) : ℝ :=
  (1 + rho) / (2 * Real.sqrt rho)

lemma omittedPointStep_deriv_norm_eq_fineLoewnerGain
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    {rho : ℝ} (hrho : 0 < rho)
    (step : E.OmittedPointStep F) (ha : ‖step.a‖ = rho) :
    ‖deriv F.toFun 0‖ =
      fineLoewnerGain rho * ‖deriv E.toFun 0‖ := by
  have hbNormSq : ‖step.b‖ ^ 2 = rho := by
    have h := congrArg norm step.b_sq
    rw [norm_pow, norm_neg, ha] at h
    exact h
  have hsqrt : ‖step.b‖ = Real.sqrt rho := by
    have hsqrtSq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho.le
    nlinarith [norm_nonneg step.b, Real.sqrt_nonneg rho]
  rw [step.deriv_eq,
    omittedPoint_derivative_norm_eq_gain step.a_mem step.b_mem step.b_sq,
    ha, hsqrt]
  unfold fineLoewnerGain
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
  have hrho1 : rho < 1 := by
    simpa [mem_ball_zero_iff, ha] using step.a_mem
  have hne : 1 - rho ≠ 0 := sub_ne_zero.mpr hrho1.ne'
  field_simp [hne, ne_of_gt hroot]
  ring

lemma one_lt_fineLoewnerGain {rho : ℝ} (hrho : 0 < rho)
    (hrho1 : rho < 1) : 1 < fineLoewnerGain rho := by
  have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
  have hsqrtSq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho.le
  unfold fineLoewnerGain
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [sq_pos_of_pos (sub_pos.mpr (by
    nlinarith [Real.sqrt_nonneg rho] : Real.sqrt rho < 1))]

lemma fineEmbeddingChain_eventually_reaches
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) :
    ∃ j, rho ≤ ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ := by
  by_contra hnever
  have hlt (j : ℕ) :
      ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ < rho := by
    exact lt_of_not_ge fun h ↦ hnever ⟨j, h⟩
  have hrec (j : ℕ) :
      ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 (j + 1)).toFun 0‖ =
        fineLoewnerGain rho *
          ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ := by
    rcases fineEmbeddingChain_succ_progress E₀ rho hrho hrho1 j with hstop | hgrow
    · exact False.elim ((not_le_of_gt (hlt j)) hstop.1)
    · rcases hgrow.2 with ⟨step, ha⟩
      exact omittedPointStep_deriv_norm_eq_fineLoewnerGain hrho step ha
  have hformula (j : ℕ) :
      ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ =
        fineLoewnerGain rho ^ j * ‖deriv E₀.toFun 0‖ := by
    induction j with
    | zero => simp [fineEmbeddingChain]
    | succ j ih =>
        rw [hrec j, ih, pow_succ']
        ring
  have hd0 : 0 < ‖deriv E₀.toFun 0‖ := norm_pos_iff.mpr E₀.deriv_ne_zero
  obtain ⟨j, hj⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt
      (one_lt_fineLoewnerGain hrho hrho1)).atTop_mul_const hd0).eventually_gt_atTop 1
      |>.exists
  have hleOne := normalizedDiskEmbedding_derivNorm_le_one_unitBall
    (fineEmbeddingChain E₀ rho hrho hrho1 j)
  rw [hformula] at hleOne
  exact (not_lt_of_ge hleOne) hj

lemma fineEmbeddingChain_grow
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) (j : ℕ)
    (hj : ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ < rho) :
    ∃ step : (fineEmbeddingChain E₀ rho hrho hrho1 j).OmittedPointStep
        (fineEmbeddingChain E₀ rho hrho hrho1 (j + 1)),
      ‖step.a‖ = rho := by
  rcases fineEmbeddingChain_succ_progress E₀ rho hrho hrho1 j with hstop | hgrow
  · exact False.elim ((not_le_of_gt hj) hstop.1)
  · exact hgrow.2

noncomputable def fineEmbeddingChainStep
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) (j : ℕ)
    (hj : ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ < rho) :
    (fineEmbeddingChain E₀ rho hrho hrho1 j).OmittedPointStep
      (fineEmbeddingChain E₀ rho hrho hrho1 (j + 1)) :=
  Classical.choose (fineEmbeddingChain_grow E₀ rho hrho hrho1 j hj)

lemma fineEmbeddingChainStep_a_norm
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) (j : ℕ)
    (hj : ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ < rho) :
    ‖(fineEmbeddingChainStep E₀ rho hrho hrho1 j hj).a‖ = rho :=
  Classical.choose_spec (fineEmbeddingChain_grow E₀ rho hrho hrho1 j hj)

noncomputable def fineEmbeddingReach
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) :
    ∀ j : ℕ, E₀.ReachableFrom (fineEmbeddingChain E₀ rho hrho hrho1 j)
  | 0 => NormalizedDiskEmbedding.ReachableFrom.refl
  | j + 1 => by
      by_cases hj :
          ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ < rho
      · exact NormalizedDiskEmbedding.ReachableFrom.step
          (fineEmbeddingReach E₀ rho hrho hrho1 j)
          (fineEmbeddingChainStep E₀ rho hrho hrho1 j hj)
      · have hstop :=
          (fineEmbeddingChain_succ_progress E₀ rho hrho hrho1 j).resolve_right
            (fun hgrow ↦ hj hgrow.1)
        rw [hstop.2]
        exact fineEmbeddingReach E₀ rho hrho hrho1 j

lemma fineEmbeddingReach_succ_of_lt
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1) (j : ℕ)
    (hj : ‖deriv (fineEmbeddingChain E₀ rho hrho hrho1 j).toFun 0‖ < rho) :
    fineEmbeddingReach E₀ rho hrho hrho1 (j + 1) =
      NormalizedDiskEmbedding.ReachableFrom.step
        (fineEmbeddingReach E₀ rho hrho hrho1 j)
        (fineEmbeddingChainStep E₀ rho hrho hrho1 j hj) := by
  rw [fineEmbeddingReach]
  simp only [hj, dif_pos]

lemma NormalizedDiskEmbedding.ReachableFrom.inverseMap_deriv_mul
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) :
    deriv reach.inverseMap 0 * deriv E.toFun 0 = deriv E₀.toFun 0 := by
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have heq : EqOn (reach.inverseMap ∘ E.toFun) E₀.toFun (ball (0 : ℂ) 1) :=
    fun z hz ↦ reach.inverseMap_apply hz
  have hderivEq := heq.deriv isOpen_ball hzero
  have hInvAt : DifferentiableAt ℂ reach.inverseMap 0 :=
    reach.inverseMap_differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds hzero)
  have hEAt : DifferentiableAt ℂ E.toFun 0 :=
    E.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hzero)
  have hInvAt' : DifferentiableAt ℂ reach.inverseMap (E.toFun 0) := by
    simpa only [E.map_base] using hInvAt
  have hcomp : deriv (reach.inverseMap ∘ E.toFun) 0 =
      deriv reach.inverseMap 0 * deriv E.toFun 0 := by
    simpa only [E.map_base] using
      (hInvAt'.hasDerivAt.comp 0 hEAt.hasDerivAt).deriv
  rwa [hcomp] at hderivEq

lemma NormalizedDiskEmbedding.ReachableFrom.inverseMap_deriv_ne_zero
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) : deriv reach.inverseMap 0 ≠ 0 := by
  intro hzero
  have h := reach.inverseMap_deriv_mul
  rw [hzero, zero_mul] at h
  exact E₀.deriv_ne_zero h.symm

noncomputable def NormalizedDiskEmbedding.ReachableFrom.normalizedInverse
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (z : ℂ) : ℂ :=
  reach.inverseMap z / deriv reach.inverseMap 0

lemma NormalizedDiskEmbedding.ReachableFrom.normalizedInverse_differentiableOn
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) :
    DifferentiableOn ℂ reach.normalizedInverse (ball (0 : ℂ) 1) :=
  reach.inverseMap_differentiableOn.div_const _

@[simp]
lemma NormalizedDiskEmbedding.ReachableFrom.normalizedInverse_zero
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) : reach.normalizedInverse 0 = 0 := by
  simp [NormalizedDiskEmbedding.ReachableFrom.normalizedInverse,
    reach.inverseMap_zero]

lemma NormalizedDiskEmbedding.ReachableFrom.deriv_normalizedInverse
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) : deriv reach.normalizedInverse 0 = 1 := by
  have hAt : DifferentiableAt ℂ reach.inverseMap 0 :=
    reach.inverseMap_differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))
  rw [show reach.normalizedInverse =
      fun z ↦ reach.inverseMap z / deriv reach.inverseMap 0 by rfl,
    (hAt.hasDerivAt.div_const _).deriv,
    div_self reach.inverseMap_deriv_ne_zero]

lemma NormalizedDiskEmbedding.ReachableFrom.norm_deriv_inverseMap
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) :
    ‖deriv reach.inverseMap 0‖ =
      ‖deriv E₀.toFun 0‖ / ‖deriv E.toFun 0‖ := by
  have h := congrArg norm reach.inverseMap_deriv_mul
  rw [norm_mul] at h
  have hE : 0 < ‖deriv E.toFun 0‖ := norm_pos_iff.mpr E.deriv_ne_zero
  rw [eq_div_iff (ne_of_gt hE)]
  exact h

noncomputable def NormalizedDiskEmbedding.OmittedPointStep.contraction
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) : ℂ :=
  2 * step.b / (1 + ‖step.b‖ ^ 2)

lemma NormalizedDiskEmbedding.OmittedPointStep.norm_contraction
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
  (step : E.OmittedPointStep F) :
    ‖step.contraction‖ = 2 * ‖step.b‖ / (1 + ‖step.b‖ ^ 2) := by
  rw [NormalizedDiskEmbedding.OmittedPointStep.contraction, norm_div, norm_mul]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hden : ‖(1 + (‖step.b‖ ^ 2 : ℂ))‖ = 1 + ‖step.b‖ ^ 2 := by
    rw [show (1 + (‖step.b‖ ^ 2 : ℂ)) =
      ((1 + ‖step.b‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [htwo, hden]

lemma NormalizedDiskEmbedding.OmittedPointStep.norm_contraction_lt_one
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) : ‖step.contraction‖ < 1 := by
  rw [step.norm_contraction, div_lt_one (by positivity : 0 < 1 + ‖step.b‖ ^ 2)]
  have hb : ‖step.b‖ < 1 := by
    simpa [mem_ball_zero_iff] using step.b_mem
  nlinarith [sq_pos_of_pos (sub_pos.mpr hb)]

lemma NormalizedDiskEmbedding.OmittedPointStep.inverseMap_eq_contraction
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    step.inverseMap z =
      z * (z + step.contraction) /
        (1 + starRingEnd ℂ step.contraction * z) := by
  have hbInner := diskMobiusInv_mapsTo_unitBall step.b_mem hz
  have hsq : diskMobiusInv step.b z ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]
    have hlt : ‖diskMobiusInv step.b z‖ < 1 := by
      simpa [mem_ball_zero_iff] using hbInner
    nlinarith [norm_nonneg (diskMobiusInv step.b z)]
  have hdb := diskMobiusInv_denominator_ne_zero step.b_mem hz
  have hda := diskMobiusInv_denominator_ne_zero step.a_mem hsq
  have hlambda : step.contraction ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff] using step.norm_contraction_lt_one
  have hright : 1 + starRingEnd ℂ step.contraction * z ≠ 0 :=
    diskMobiusInv_denominator_ne_zero hlambda hz
  have ha : step.a = -step.b ^ 2 := by
    simpa using congrArg Neg.neg step.b_sq.symm
  have hbReal : (starRingEnd ℂ step.b * step.b) =
      (‖step.b‖ : ℂ) ^ 2 := Complex.conj_mul' step.b
  have hS : 1 + starRingEnd ℂ step.b * step.b ≠ 0 := by
    rw [hbReal]
    exact_mod_cast (by positivity : (0 : ℝ) < 1 + ‖step.b‖ ^ 2).ne'
  have hlambdaEq : step.contraction =
      2 * step.b / (1 + starRingEnd ℂ step.b * step.b) := by
    unfold NormalizedDiskEmbedding.OmittedPointStep.contraction
    rw [hbReal]
  have hstarLambda : starRingEnd ℂ step.contraction =
      2 * starRingEnd ℂ step.b /
        (1 + starRingEnd ℂ step.b * step.b) := by
    rw [hlambdaEq]
    simp
    have htwo : starRingEnd ℂ (2 : ℂ) = 2 := Complex.conj_ofNat 2
    rw [htwo]
    ring
  have houter :
      1 - (starRingEnd ℂ step.b) ^ 2 *
          ((z + step.b) / (1 + starRingEnd ℂ step.b * z)) ^ 2 ≠ 0 := by
    simpa only [ha, diskMobiusInv, map_neg, map_pow, neg_mul, sub_eq_add_neg,
      add_comm] using hda
  have hright' :
      1 + (2 * starRingEnd ℂ step.b /
        (1 + starRingEnd ℂ step.b * step.b)) * z ≠ 0 := by
    simpa only [hstarLambda] using hright
  rw [NormalizedDiskEmbedding.OmittedPointStep.inverseMap, ha, hstarLambda,
    hlambdaEq]
  simp only [diskMobiusInv, map_neg, map_pow]
  rw [neg_mul]
  simp only [← sub_eq_add_neg]
  change
    (((z + step.b) / (1 + starRingEnd ℂ step.b * z)) ^ 2 - step.b ^ 2) /
        (1 - (starRingEnd ℂ step.b) ^ 2 *
          ((z + step.b) / (1 + starRingEnd ℂ step.b * z)) ^ 2) =
      z * (z + 2 * step.b /
          (1 + starRingEnd ℂ step.b * step.b)) /
        (1 + (2 * starRingEnd ℂ step.b /
          (1 + starRingEnd ℂ step.b * step.b)) * z)
  have hnum :
      ((z + step.b) / (1 + starRingEnd ℂ step.b * z)) ^ 2 - step.b ^ 2 =
        z * (1 - starRingEnd ℂ step.b * step.b) *
          (2 * step.b + (1 + starRingEnd ℂ step.b * step.b) * z) /
            (1 + starRingEnd ℂ step.b * z) ^ 2 := by
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hdb)).2
    calc
      (((z + step.b) ^ 2 / (1 + starRingEnd ℂ step.b * z) ^ 2 -
            step.b ^ 2) * (1 + starRingEnd ℂ step.b * z) ^ 2) =
          (z + step.b) ^ 2 -
            step.b ^ 2 * (1 + starRingEnd ℂ step.b * z) ^ 2 := by
        rw [sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hdb)]
      _ = _ := by ring
  have hden :
      1 - (starRingEnd ℂ step.b) ^ 2 *
          ((z + step.b) / (1 + starRingEnd ℂ step.b * z)) ^ 2 =
        (1 - starRingEnd ℂ step.b * step.b) *
          (1 + starRingEnd ℂ step.b * step.b +
            2 * starRingEnd ℂ step.b * z) /
              (1 + starRingEnd ℂ step.b * z) ^ 2 := by
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hdb)).2
    calc
      ((1 - (starRingEnd ℂ step.b) ^ 2 *
          ((z + step.b) ^ 2 /
            (1 + starRingEnd ℂ step.b * z) ^ 2)) *
          (1 + starRingEnd ℂ step.b * z) ^ 2) =
        (1 + starRingEnd ℂ step.b * z) ^ 2 -
          (starRingEnd ℂ step.b) ^ 2 * (z + step.b) ^ 2 := by
        rw [sub_mul, one_mul, mul_assoc,
          div_mul_cancel₀ _ (pow_ne_zero 2 hdb)]
      _ = _ := by ring
  have hproduct :
      (1 - starRingEnd ℂ step.b * step.b) *
          (1 + starRingEnd ℂ step.b * step.b +
            2 * starRingEnd ℂ step.b * z) ≠ 0 := by
    intro hzero
    apply houter
    rw [hden, hzero]
    simp
  have hminus : 1 - starRingEnd ℂ step.b * step.b ≠ 0 :=
    (mul_ne_zero_iff.mp hproduct).1
  have hplus : 1 + starRingEnd ℂ step.b * step.b +
      2 * starRingEnd ℂ step.b * z ≠ 0 :=
    (mul_ne_zero_iff.mp hproduct).2
  rw [hnum, hden]
  rw [div_div_div_cancel_right₀ (pow_ne_zero 2 hdb)]
  rw [show z * (1 - starRingEnd ℂ step.b * step.b) *
        (2 * step.b + (1 + starRingEnd ℂ step.b * step.b) * z) =
      (1 - starRingEnd ℂ step.b * step.b) *
        (z * (2 * step.b +
          (1 + starRingEnd ℂ step.b * step.b) * z)) by ring,
    mul_div_mul_left _ _ hminus]
  have hnumRight :
      z + 2 * step.b / (1 + starRingEnd ℂ step.b * step.b) =
        ((1 + starRingEnd ℂ step.b * step.b) * z + 2 * step.b) /
          (1 + starRingEnd ℂ step.b * step.b) := by
    apply (eq_div_iff hS).2
    rw [add_mul, div_mul_cancel₀ _ hS]
    ring
  have hdenRight :
      1 + (2 * starRingEnd ℂ step.b /
          (1 + starRingEnd ℂ step.b * step.b)) * z =
        (1 + starRingEnd ℂ step.b * step.b +
          2 * starRingEnd ℂ step.b * z) /
            (1 + starRingEnd ℂ step.b * step.b) := by
    apply (eq_div_iff hS).2
    rw [add_mul, one_mul]
    rw [show
      (2 * starRingEnd ℂ step.b /
          (1 + starRingEnd ℂ step.b * step.b) * z) *
          (1 + starRingEnd ℂ step.b * step.b) =
        ((2 * starRingEnd ℂ step.b /
          (1 + starRingEnd ℂ step.b * step.b)) *
            (1 + starRingEnd ℂ step.b * step.b)) * z by ring,
      div_mul_cancel₀ _ hS]
  rw [hnumRight, hdenRight, ← mul_div_assoc,
    div_div_div_cancel_right₀ hS]
  ring

lemma NormalizedDiskEmbedding.OmittedPointStep.deriv_inverseMap_zero
    {E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (step : E.OmittedPointStep F) :
    deriv step.inverseMap 0 = step.contraction := by
  have heq : EqOn step.inverseMap
      (fun z ↦ z * (z + step.contraction) /
        (1 + starRingEnd ℂ step.contraction * z)) (ball (0 : ℂ) 1) :=
    fun z hz ↦ step.inverseMap_eq_contraction hz
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  rw [heq.deriv isOpen_ball hzero]
  have hden : 1 + starRingEnd ℂ step.contraction * (0 : ℂ) ≠ 0 := by simp
  have hfun :
      (fun z : ℂ ↦ z * (z + step.contraction) /
        (1 + starRingEnd ℂ step.contraction * z)) =
      (id * (fun z : ℂ ↦ z + step.contraction)) /
        ((fun _ : ℂ ↦ 1) + fun z ↦ starRingEnd ℂ step.contraction * z) := by
    funext z
    rfl
  rw [hfun]
  simpa using (((hasDerivAt_id 0).mul
      ((hasDerivAt_id 0).add_const step.contraction)).div
        ((hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).add
          ((hasDerivAt_id 0).const_mul (starRingEnd ℂ step.contraction))) hden).deriv

lemma NormalizedDiskEmbedding.OmittedPointStep.normalizedInverse_step
    {E₀ E F : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (step : E.OmittedPointStep F) (z : ℂ) :
    (NormalizedDiskEmbedding.ReachableFrom.step reach step).normalizedInverse z =
      reach.normalizedInverse (step.inverseMap z) / step.contraction := by
  have hInvAt : DifferentiableAt ℂ reach.inverseMap 0 :=
    reach.inverseMap_differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))
  have hStepAt : DifferentiableAt ℂ step.inverseMap 0 :=
    step.inverseMap_differentiableOn.differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))
  have hInvAt' : DifferentiableAt ℂ reach.inverseMap (step.inverseMap 0) := by
    simpa only [step.inverseMap_zero] using hInvAt
  have hderiv : deriv (reach.inverseMap ∘ step.inverseMap) 0 =
      deriv reach.inverseMap 0 * step.contraction := by
    rw [(hInvAt'.hasDerivAt.comp 0 hStepAt.hasDerivAt).deriv,
      step.inverseMap_zero, step.deriv_inverseMap_zero]
  change reach.inverseMap (step.inverseMap z) /
      deriv (reach.inverseMap ∘ step.inverseMap) 0 =
    (reach.inverseMap (step.inverseMap z) / deriv reach.inverseMap 0) /
      step.contraction
  rw [hderiv]
  have hb : step.b ≠ 0 := by
    intro hb
    have ha : step.a = 0 := by
      have h := step.b_sq
      rw [hb] at h
      simpa using h.symm
    apply step.a_omitted
    exact ⟨0, mem_ball_self zero_lt_one, by simpa [ha] using E.map_base⟩
  have hcontraction : step.contraction ≠ 0 := by
    unfold NormalizedDiskEmbedding.OmittedPointStep.contraction
    apply div_ne_zero (mul_ne_zero (by norm_num) hb)
    exact_mod_cast (by positivity : (0 : ℝ) < 1 + ‖step.b‖ ^ 2).ne'
  field_simp [reach.inverseMap_deriv_ne_zero, hcontraction]

end Submission
