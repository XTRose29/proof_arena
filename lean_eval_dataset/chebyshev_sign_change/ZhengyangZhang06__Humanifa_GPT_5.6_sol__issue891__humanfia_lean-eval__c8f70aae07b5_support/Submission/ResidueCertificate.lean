import Submission.ZeroDensity

open Filter InnerProductSpace Metric Real Set Topology

namespace Submission.ResidueCertificate

open Submission.ZeroMass Submission.ZeroDensity


lemma shiftedChiFourXi_eq_zero_of_divisor_ne_zero {R : ℝ} {u : ℂ}
    (hu : shiftedZeroDivisor R u ≠ 0) :
    shiftedChiFourXi u = 0 := by
  have huSupport : u ∈ (shiftedZeroDivisor R).support := hu
  have hnormal : MeromorphicNFOn shiftedChiFourXi (ball (0 : ℂ) R) := by
    intro z _hz
    exact differentiable_shiftedChiFourXi.analyticAt z |>.meromorphicNFAt
  have hzeroSet : u ∈ (ball (0 : ℂ) R ∩ {z | shiftedChiFourXi z = 0}) := by
    change u ∈ ball (0 : ℂ) R ∩ shiftedChiFourXi ⁻¹' {0}
    rw [hnormal.zero_set_eq_divisor_support]
    · exact huSupport
    · intro z
      exact meromorphicOrderAt_shiftedChiFourXi_ne_top z
  exact hzeroSet.2

lemma shiftedZero_original_mem_nontrivial {R : ℝ} {u : ℂ}
    (hu : shiftedZeroDivisor R u ≠ 0) :
    1 / 2 + u ∈ Submission.Analytic.chiFourNontrivialZeroSet := by
  apply Submission.ZeroExistence.chiFourXi_zero_mem_nontrivial
  simpa [shiftedChiFourXi] using shiftedChiFourXi_eq_zero_of_divisor_ne_zero hu

lemma meromorphicOrderAt_shiftedChiFourXi_add_half (u : ℂ) :
    meromorphicOrderAt shiftedChiFourXi u =
      meromorphicOrderAt Submission.ZeroExistence.chiFourXi (1 / 2 + u) := by
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := Submission.ZeroExistence.chiFourXi)
    (g := fun z : ℂ => 1 / 2 + z) (x := u) (by fun_prop) (by simp)
  change meromorphicOrderAt
      (fun z => Submission.ZeroExistence.chiFourXi (1 / 2 + z)) u = _
  simpa [Function.comp_def] using hcomp

lemma meromorphicOrderAt_chiFourXi_eq_completed (s : ℂ) :
    meromorphicOrderAt Submission.ZeroExistence.chiFourXi s =
      meromorphicOrderAt
        (DirichletCharacter.completedLFunction Submission.Helpers.chiFour) s := by
  let factor : ℂ → ℂ := fun z => (4 : ℂ) ^ (z / 2)
  letI : NeZero (4 : ℂ) := ⟨by norm_num⟩
  have hfactor : AnalyticAt ℂ factor s := by
    have hdiff : Differentiable ℂ factor := by
      dsimp [factor]
      exact (differentiable_const_cpow_of_neZero (4 : ℂ)).comp (by fun_prop)
    exact hdiff.analyticAt s
  have hfactorNe : factor s ≠ 0 := by
    dsimp [factor]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hfactorOrder : meromorphicOrderAt factor s = 0 :=
    hfactor.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfactorNe
  have hcompleted : AnalyticAt ℂ
    (DirichletCharacter.completedLFunction Submission.Helpers.chiFour) s :=
    (DirichletCharacter.differentiable_completedLFunction
      Submission.Helpers.chiFour_ne_one).analyticAt s
  have hxi : Submission.ZeroExistence.chiFourXi =
      factor *
        (DirichletCharacter.completedLFunction Submission.Helpers.chiFour : ℂ → ℂ) := by
    rfl
  rw [hxi]
  rw [meromorphicOrderAt_mul hfactor.meromorphicAt hcompleted.meromorphicAt,
    hfactorOrder, zero_add]

lemma shiftedZeroDivisor_eq_zeroMultiplicity {R : ℝ} {u : ℂ}
    (hu : shiftedZeroDivisor R u ≠ 0) :
    shiftedZeroDivisor R u =
      (Submission.Analytic.chiFourZeroMultiplicity (1 / 2 + u) : ℤ) := by
  have huBall : u ∈ ball (0 : ℂ) R :=
    (shiftedZeroDivisor R).supportWithinDomain hu
  have hs := shiftedZero_original_mem_nontrivial hu
  have hcompleted := Submission.Analytic.chiFour_completed_divisor_eq_zeroMultiplicity
    (U := Set.univ) hs (Set.mem_univ (1 / 2 + u))
  unfold shiftedZeroDivisor
  rw [MeromorphicOn.divisor_apply
      (fun z _hz => meromorphic_shiftedChiFourXi z) huBall,
    meromorphicOrderAt_shiftedChiFourXi_add_half,
    meromorphicOrderAt_chiFourXi_eq_completed]
  rw [MeromorphicOn.divisor_apply
      (fun z _hz =>
        (DirichletCharacter.differentiable_completedLFunction
          Submission.Helpers.chiFour_ne_one).analyticAt z |>.meromorphicAt)
      (Set.mem_univ (1 / 2 + u))] at hcompleted
  exact hcompleted

lemma shiftedZeroCount_le_jensen {r : ℝ} (hr : 0 < r) :
    shiftedZeroCount r ≤
      Real.log (shiftedGrowthMajorant (4 * r) / ‖shiftedChiFourXi 0‖) /
        Real.log 2 := by
  let D := MeromorphicOn.divisor shiftedChiFourXi
    (closedBall (0 : ℂ) (2 * r))
  have hDfinite : Function.HasFiniteSupport D :=
    (MeromorphicOn.divisor shiftedChiFourXi
      (closedBall (0 : ℂ) (2 * r))).finiteSupport
      (isCompact_closedBall (0 : ℂ) (2 * r))
  have hZfinite : Function.HasFiniteSupport (shiftedZeroDivisor r) :=
    shiftedZeroDivisor_support_finite r
  have hpoint : (fun u => shiftedZeroDivisor r u) ≤ fun u => D u := by
    intro u
    change shiftedZeroDivisor r u ≤ D u
    by_cases hu : u ∈ ball (0 : ℂ) r
    · have huClosed : u ∈ closedBall (0 : ℂ) (2 * r) := by
        rw [mem_closedBall_iff_norm, sub_zero]
        have hunorm : ‖u‖ < r := by simpa [mem_ball_iff_norm] using hu
        linarith
      unfold shiftedZeroDivisor D
      rw [MeromorphicOn.divisor_apply
          (fun z _hz => meromorphic_shiftedChiFourXi z) hu,
        MeromorphicOn.divisor_apply
          (fun z _hz => meromorphic_shiftedChiFourXi z) huClosed]
    · rw [(shiftedZeroDivisor r).apply_eq_zero_of_notMem hu]
      exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (U := closedBall (0 : ℂ) (2 * r))
        (fun z _hz => differentiable_shiftedChiFourXi.analyticAt z)) u
  have hsumInt : ∑ᶠ u, shiftedZeroDivisor r u ≤ ∑ᶠ u, D u :=
    finsum_le_finsum' hZfinite hDfinite hpoint
  have hcastZ : shiftedZeroCount r = ((∑ᶠ u, shiftedZeroDivisor r u : ℤ) : ℝ) := by
    unfold shiftedZeroCount
    exact (map_finsum (Int.castRingHom ℝ) hZfinite).symm
  have hcastD :
      ((∑ᶠ u, D u : ℤ) : ℝ) = ∑ᶠ u, (D u : ℝ) :=
    map_finsum (Int.castRingHom ℝ) hDfinite
  have hsumReal : shiftedZeroCount r ≤ ∑ᶠ u, (D u : ℝ) := by
    rw [hcastZ, ← hcastD]
    exact_mod_cast hsumInt
  have hjensen := AnalyticOnNhd.sum_divisor_le
    (f := shiftedChiFourXi) (c := (0 : ℂ)) (r := 2 * r) (R := 4 * r)
    (M := shiftedGrowthMajorant (4 * r))
    (by simp [abs_of_pos hr]; positivity)
    (by simp [abs_of_pos hr]; linarith)
    (one_le_shiftedGrowthMajorant (by positivity))
    (fun z _hz => differentiable_shiftedChiFourXi.analyticAt z)
    shiftedChiFourXi_zero_ne
    (fun z hz => norm_shiftedChiFourXi_le_growthMajorant_of_mem_sphere (by positivity) <| by
      simpa [abs_of_pos hr] using hz)
  have hratio : (4 * r) / (2 * r) = 2 := by
    field_simp [hr.ne']
    ring
  have hDabs : closedBall (0 : ℂ) |2 * r| = closedBall (0 : ℂ) (2 * r) := by
    rw [abs_of_pos (by positivity : 0 < 2 * r)]
  rw [hratio, hDabs] at hjensen
  have hjensen' : ∑ᶠ u, (D u : ℝ) ≤
      Real.log (shiftedGrowthMajorant (4 * r) / ‖shiftedChiFourXi 0‖) /
        Real.log 2 := by
    rw [← hcastD]
    simpa [D] using hjensen
  exact hsumReal.trans hjensen'

noncomputable def shiftedZeroJensenConstant : ℝ :=
  (16 * Submission.ZeroExistence.chiFourXiGrowthConstant +
      |Real.log ‖shiftedChiFourXi 0‖|) / Real.log 2

private lemma chiFourXiGrowthConstant_nonneg' :
    0 ≤ Submission.ZeroExistence.chiFourXiGrowthConstant := by
  unfold Submission.ZeroExistence.chiFourXiGrowthConstant
  unfold Submission.ZeroExistence.chiFourXiRightGrowthConstant
  have hstrip := Submission.Growth.chiFourCompletedStripBound_nonneg (1 / 2) 3
  have hL : 0 ≤ Submission.ZeroExistence.chiFourLNormBound := by
    unfold Submission.ZeroExistence.chiFourLNormBound
    exact tsum_nonneg fun _ => norm_nonneg _
  nlinarith

lemma shiftedZeroJensenConstant_nonneg : 0 ≤ shiftedZeroJensenConstant := by
  unfold shiftedZeroJensenConstant
  exact div_nonneg
    (add_nonneg
      (mul_nonneg (by norm_num)
        chiFourXiGrowthConstant_nonneg')
      (abs_nonneg _))
    (Real.log_nonneg (by norm_num))

lemma shiftedZeroCount_le_cubicRootBound {r : ℝ} (hr : 1 ≤ r) :
    shiftedZeroCount r ≤ shiftedZeroJensenConstant * r * Real.sqrt r := by
  have hrPos : 0 < r := zero_lt_one.trans_le hr
  have hbase : 0 ≤ 4 * r + 1 := by positivity
  have hsqrtBound : Real.sqrt (4 * r + 1) ≤ 3 * Real.sqrt r := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hrPos.le]
      nlinarith
  have hsqrtOne : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
  have hshape :
      1 + (4 * r + 1) * Real.sqrt (4 * r + 1) ≤
        16 * r * Real.sqrt r := by
    have hlin : 4 * r + 1 ≤ 5 * r := by linarith
    have hprod := mul_le_mul hlin hsqrtBound (Real.sqrt_nonneg _) (by positivity)
    have hrSqrt : 1 ≤ r * Real.sqrt r := by nlinarith
    nlinarith
  have hj := shiftedZeroCount_le_jensen hrPos
  have hnormPos : 0 < ‖shiftedChiFourXi 0‖ :=
    norm_pos_iff.mpr shiftedChiFourXi_zero_ne
  have hmajorPos : 0 < shiftedGrowthMajorant (4 * r) :=
    shiftedGrowthMajorant_pos _
  have hlogMajor :
      Real.log (shiftedGrowthMajorant (4 * r)) =
        Submission.ZeroExistence.chiFourXiGrowthConstant *
          (1 + (4 * r + 1) * Real.sqrt (4 * r + 1)) := by
    rw [shiftedGrowthMajorant, Real.log_exp]
  have hlogDiv :
      Real.log (shiftedGrowthMajorant (4 * r) / ‖shiftedChiFourXi 0‖) =
        Real.log (shiftedGrowthMajorant (4 * r)) -
          Real.log ‖shiftedChiFourXi 0‖ := by
    exact Real.log_div hmajorPos.ne' hnormPos.ne'
  rw [hlogDiv, hlogMajor] at hj
  have hgrowth := mul_le_mul_of_nonneg_left hshape
    chiFourXiGrowthConstant_nonneg'
  have hlogNorm : -Real.log ‖shiftedChiFourXi 0‖ ≤
      |Real.log ‖shiftedChiFourXi 0‖| * (r * Real.sqrt r) := by
    have habs := neg_le_abs (Real.log ‖shiftedChiFourXi 0‖)
    have hscale : 1 ≤ r * Real.sqrt r := by nlinarith
    exact habs.trans (by
      simpa using mul_le_mul_of_nonneg_left hscale (abs_nonneg (Real.log ‖shiftedChiFourXi 0‖)))
  have hnum :
      Submission.ZeroExistence.chiFourXiGrowthConstant *
            (1 + (4 * r + 1) * Real.sqrt (4 * r + 1)) -
          Real.log ‖shiftedChiFourXi 0‖ ≤
        (16 * Submission.ZeroExistence.chiFourXiGrowthConstant +
          |Real.log ‖shiftedChiFourXi 0‖|) * (r * Real.sqrt r) := by
    calc
      _ ≤ 16 * Submission.ZeroExistence.chiFourXiGrowthConstant *
            (r * Real.sqrt r) +
          |Real.log ‖shiftedChiFourXi 0‖| * (r * Real.sqrt r) := by
        linarith
      _ = _ := by ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply hj.trans
  rw [shiftedZeroJensenConstant]
  calc
    (Submission.ZeroExistence.chiFourXiGrowthConstant *
            (1 + (4 * r + 1) * Real.sqrt (4 * r + 1)) -
          Real.log ‖shiftedChiFourXi 0‖) /
        Real.log 2 ≤
        ((16 * Submission.ZeroExistence.chiFourXiGrowthConstant +
          |Real.log ‖shiftedChiFourXi 0‖|) * (r * Real.sqrt r)) /
          Real.log 2 := div_le_div_of_nonneg_right hnum hlog2.le
    _ = ((16 * Submission.ZeroExistence.chiFourXiGrowthConstant +
          |Real.log ‖shiftedChiFourXi 0‖|) / Real.log 2) * r * Real.sqrt r := by
      ring

lemma shiftedZeroCount_two_sqrt_le_quarter
    {B R : ℝ} (hR : 1 ≤ R)
    (hroot : 16 * shiftedZeroJensenConstant ≤
      B * Real.sqrt (Real.sqrt R)) :
    shiftedZeroCount (2 * Real.sqrt R) ≤ B * R / 4 := by
  have hsqrtR : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
  have hsqrtRPos : 0 < Real.sqrt R := zero_lt_one.trans_le hsqrtR
  have hr : 1 ≤ 2 * Real.sqrt R := by linarith
  have hcount := shiftedZeroCount_le_cubicRootBound hr
  have hinner : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
  have hsqrtTwo : Real.sqrt (2 * Real.sqrt R) ≤
      2 * Real.sqrt (Real.sqrt R) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hinner]
      nlinarith
  have hJ : 0 ≤ shiftedZeroJensenConstant := shiftedZeroJensenConstant_nonneg
  have hprod :
      shiftedZeroJensenConstant * (2 * Real.sqrt R) *
          Real.sqrt (2 * Real.sqrt R) ≤
        4 * shiftedZeroJensenConstant * Real.sqrt R *
          Real.sqrt (Real.sqrt R) := by
    calc
      shiftedZeroJensenConstant * (2 * Real.sqrt R) *
          Real.sqrt (2 * Real.sqrt R) ≤
          shiftedZeroJensenConstant * (2 * Real.sqrt R) *
            (2 * Real.sqrt (Real.sqrt R)) := by
        gcongr
      _ = 4 * shiftedZeroJensenConstant * Real.sqrt R *
          Real.sqrt (Real.sqrt R) := by ring
  have hRpow : Real.sqrt R * Real.sqrt R = R := by
    nlinarith [Real.sq_sqrt (show 0 ≤ R by positivity)]
  have htarget :
      4 * shiftedZeroJensenConstant * Real.sqrt R *
          Real.sqrt (Real.sqrt R) ≤ B * R / 4 := by
    calc
      4 * shiftedZeroJensenConstant * Real.sqrt R *
          Real.sqrt (Real.sqrt R) =
          (16 * shiftedZeroJensenConstant) *
            (Real.sqrt R / 4) * Real.sqrt (Real.sqrt R) := by ring
      _ ≤ (B * Real.sqrt (Real.sqrt R)) *
            (Real.sqrt R / 4) * Real.sqrt (Real.sqrt R) := by
        gcongr
      _ = B * (Real.sqrt (Real.sqrt R) * Real.sqrt (Real.sqrt R)) *
          Real.sqrt R / 4 := by ring
      _ = B * R / 4 := by
        rw [show Real.sqrt (Real.sqrt R) * Real.sqrt (Real.sqrt R) =
          Real.sqrt R by nlinarith [Real.sq_sqrt hinner]]
        calc
          B * Real.sqrt R * Real.sqrt R / 4 =
              B * (Real.sqrt R * Real.sqrt R) / 4 := by ring
          _ = B * R / 4 := by rw [hRpow]
  exact hcount.trans (hprod.trans htarget)

lemma shiftedZeroCount_mono {r R : ℝ} (_hr : 0 ≤ r) (hrR : r ≤ R) :
    shiftedZeroCount r ≤ shiftedZeroCount R := by
  rcases hrR.eq_or_lt with rfl | hrRlt
  · exact le_rfl
  let S := (shiftedZeroDivisor_support_finite R).toFinset
  let T := S.filter fun u => ‖u‖ < r
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  calc
    shiftedZeroCount r = ∑ u ∈ T, (shiftedZeroDivisor R u : ℝ) := by
      dsimp [T, S]
      exact (sum_shiftedZeroDivisor_filter_norm_lt hrRlt).symm
    _ ≤ ∑ u ∈ S, (shiftedZeroDivisor R u : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hTsub
      intro u _huS _huT
      exact_mod_cast shiftedZeroDivisor_nonneg R u
    _ = shiftedZeroCount R := by
      dsimp [S]
      exact sum_shiftedZeroDivisor_eq_count R

lemma exists_shiftedZero_free_radius :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ u ∈ ball (0 : ℂ) delta, shiftedChiFourXi u ≠ 0 := by
  have hevent : ∀ᶠ u : ℂ in 𝓝 0, shiftedChiFourXi u ≠ 0 :=
    differentiable_shiftedChiFourXi.continuous.continuousAt.preimage_mem_nhds
      (compl_singleton_mem_nhds_iff.mpr shiftedChiFourXi_zero_ne)
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hevent
  exact ⟨delta, hdelta, fun u hu => hball hu⟩

lemma shiftedZeroCount_eq_zero_of_le_free_radius
    {delta R : ℝ} (_hR : 0 < R) (hRdelta : R ≤ delta)
    (hfree : ∀ u ∈ ball (0 : ℂ) delta, shiftedChiFourXi u ≠ 0) :
    shiftedZeroCount R = 0 := by
  unfold shiftedZeroCount
  have hzero (u : ℂ) : (shiftedZeroDivisor R u : ℝ) = 0 := by
    by_contra hdivReal
    have hdiv : shiftedZeroDivisor R u ≠ 0 := by
      intro h
      apply hdivReal
      rw [h]
      norm_num
    have huBall : u ∈ ball (0 : ℂ) R :=
      (shiftedZeroDivisor R).supportWithinDomain hdiv
    have huDelta : u ∈ ball (0 : ℂ) delta := ball_subset_ball hRdelta huBall
    have huClosed : u ∈ closedBall (0 : ℂ) R := ball_subset_closedBall huBall
    exact hdiv (shiftedZeroDivisor_eq_zero_of_ne_zero huClosed (hfree u huDelta))
  simpa only [hzero] using (finsum_zero : ∑ᶠ _u : ℂ, (0 : ℝ) = 0)

end Submission.ResidueCertificate
