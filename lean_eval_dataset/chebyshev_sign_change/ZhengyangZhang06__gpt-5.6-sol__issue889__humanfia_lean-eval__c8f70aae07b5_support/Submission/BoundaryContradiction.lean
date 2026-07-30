import Submission.FiniteSupportReduction

open Complex Filter MeasureTheory Metric Real Set Topology
open LeanEval.NumberTheory.ChebyshevSignChangeProblem

namespace Submission.BoundaryContradiction

open Submission.Analytic Submission.BoundaryFinal Submission.BoundaryOscillation
open Submission.Endpoint
open Submission.BoundaryTauberian Submission.FiniteSupportPD Submission.Helpers
open Submission.ResidueCertificate Submission.SignChange Submission.ZeroMass

noncomputable def mellinDyadicWeight (r a : ℝ) : ℝ :=
  Real.exp ((5 / 2 - r) * Real.log a) -
    Real.exp ((5 / 2 - 2 * r) * Real.log a)

noncomputable def mellinDyadicDifference (C r t : ℝ) : ℂ :=
  adjustedPrimeMellin (-1) C (boundaryPoint t + (r : ℂ)) -
    adjustedPrimeMellin (-1) C (boundaryPoint t + ((2 * r : ℝ) : ℂ))

private lemma mellinDyadicWeight_nonneg_ae (C : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ a ∂mellinMeasure (-1) C, 0 ≤ mellinDyadicWeight r a := by
  filter_upwards [ae_log_nonneg_mellinMeasure (-1) C] with a ha
  unfold mellinDyadicWeight
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (by linarith) ha

private lemma integrable_mellin_boundaryPath
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    (t : ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun a => Complex.exp
      ((3 - (boundaryPoint t + (r : ℂ))) * (Real.log a : ℂ)))
      (mellinMeasure (-1) C) := by
  have hbeta : mellinAbscissa (-1) C = (1 / 2 : ℝ) :=
    mellinAbscissa_eq_half hone (by norm_num)
  apply ProbabilityTheory.integrable_cexp_mul_of_re_mem_interior_integrableExpSet
  apply three_sub_re_mem_interior_integrableExpSet hone
  rw [hbeta, Complex.add_re, boundaryPoint_re]
  simp
  exact hr

private lemma mellinDyadicWeight_fourierAtom (r t a : ℝ) :
    (mellinDyadicWeight r a : ℂ) *
        Complex.exp (-((((t * Real.log a : ℝ) : ℂ) * I))) =
      Complex.exp
          ((3 - (boundaryPoint t + (r : ℂ))) * (Real.log a : ℂ)) -
        Complex.exp
          ((3 - (boundaryPoint t + ((2 * r : ℝ) : ℂ))) *
            (Real.log a : ℂ)) := by
  have hfirst :
      (Real.exp ((5 / 2 - r) * Real.log a) : ℂ) *
          Complex.exp (-((((t * Real.log a : ℝ) : ℂ) * I))) =
        Complex.exp
          ((3 - (boundaryPoint t + (r : ℂ))) * (Real.log a : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    unfold boundaryPoint
    push_cast
    ring
  have hsecond :
      (Real.exp ((5 / 2 - 2 * r) * Real.log a) : ℂ) *
          Complex.exp (-((((t * Real.log a : ℝ) : ℂ) * I))) =
        Complex.exp
          ((3 - (boundaryPoint t + ((2 * r : ℝ) : ℂ))) *
            (Real.log a : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    unfold boundaryPoint
    push_cast
    ring
  unfold mellinDyadicWeight
  rw [Complex.ofReal_sub, sub_mul, hfirst, hsecond]

private lemma integrable_mellinDyadicWeight_fourierAtom
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    Integrable (fun a => (mellinDyadicWeight r a : ℂ) *
      Complex.exp (-((((t * Real.log a : ℝ) : ℂ) * I))))
      (mellinMeasure (-1) C) := by
  have hfirst := integrable_mellin_boundaryPath hone t hr
  have hsecond := integrable_mellin_boundaryPath hone t (show 0 < 2 * r by positivity)
  apply (hfirst.sub hsecond).congr
  filter_upwards with a
  exact (mellinDyadicWeight_fourierAtom r t a).symm

private lemma mellinDyadicDifference_eq_fourierKernel
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    mellinDyadicDifference C r t =
      fourierKernel (mellinDyadicWeight r) Real.log (mellinMeasure (-1) C) t := by
  have hfirst := integrable_mellin_boundaryPath hone t hr
  have hsecond := integrable_mellin_boundaryPath hone t (show 0 < 2 * r by positivity)
  unfold mellinDyadicDifference adjustedPrimeMellin ProbabilityTheory.complexMGF
  unfold fourierKernel
  rw [← integral_sub hfirst hsecond]
  apply integral_congr_ae
  filter_upwards with a
  exact (mellinDyadicWeight_fourierAtom r t a).symm

lemma mellinDyadicDifference_quadraticallyNonnegative
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    {r : ℝ} (hr : 0 < r) :
    IsQuadraticallyNonnegative (mellinDyadicDifference C r) := by
  have hpd : IsQuadraticallyNonnegative
      (fourierKernel (mellinDyadicWeight r) Real.log
        (mellinMeasure (-1) C)) :=
    fourierKernel_quadraticallyNonnegative
      (q := mellinDyadicWeight r) (X := Real.log)
      (mu := mellinMeasure (-1) C)
      (mellinDyadicWeight_nonneg_ae C hr)
      (integrable_mellinDyadicWeight_fourierAtom hone hr)
  intro n _inst t c
  simpa only [mellinDyadicDifference_eq_fourierKernel hone hr] using hpd t c

noncomputable def boundaryKernel (t : ℝ) : ℂ :=
  ((Real.log 2 : ℝ) : ℂ) * boundaryResidueMass t / boundaryPoint t

lemma boundaryKernel_quadraticallyNonnegative
    {C : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n) :
    IsQuadraticallyNonnegative boundaryKernel := by
  intro n _inst t c
  let Q : ℝ → ℂ := fun r =>
    ∑ i, ∑ j, star (c i) * mellinDyadicDifference C r (t i - t j) * c j
  let qlim : ℂ :=
    ∑ i, ∑ j, star (c i) * boundaryKernel (t i - t j) * c j
  have hnon : ∀ᶠ r in nhdsWithin 0 (Ioi 0), 0 ≤ (Q r).re := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mellinDyadicDifference_quadraticallyNonnegative hone hr t c
  have hlim : Filter.Tendsto Q (nhdsWithin 0 (Ioi 0)) (nhds qlim) := by
    dsimp [Q, qlim]
    apply tendsto_finsetSum
    intro i _hi
    apply tendsto_finsetSum
    intro j _hj
    have hcore := tendsto_adjustedPrimeMellin_dyadicDifference hone (t i - t j)
    have hleft : Filter.Tendsto (fun _ : ℝ => star (c i))
        (nhdsWithin 0 (Ioi 0)) (nhds (star (c i))) := tendsto_const_nhds
    have hmul := (hleft.mul hcore).mul_const (c j)
    simpa only [mellinDyadicDifference, boundaryKernel, starRingEnd_apply] using hmul
  have hre := continuous_re.continuousAt.tendsto.comp hlim
  exact ge_of_tendsto hre hnon

private lemma volumeReal_centeredIntervals {R a b : ℝ} (hR : 0 < R) :
    volume.real
        (Icc (a - R) (a + R) ∩ Icc (b - R) (b + R)) =
      2 * R * boundaryWeight R (a - b) := by
  have hends :
      min (a + R) (b + R) - max (a - R) (b - R) =
        2 * R - |a - b| := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left (by linarith),
        max_eq_right (by linarith),
        abs_of_nonpos (sub_nonpos.mpr hab)]
      ring
    · rw [min_eq_right (by linarith),
        max_eq_left (by linarith),
        abs_of_nonneg (sub_nonneg.mpr hba)]
      ring
  rw [Icc_inter_Icc, volume_real_Icc, hends]
  unfold boundaryWeight
  by_cases h : |a - b| ≤ 2 * R
  · have hleft : 0 ≤ 2 * R - |a - b| := sub_nonneg.mpr h
    have hright : 0 ≤ 1 - |a - b| / (2 * R) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      exact h
    rw [max_eq_left hleft, max_eq_right hright]
    field_simp [hR.ne']
  · have hleft : 2 * R - |a - b| ≤ 0 :=
      sub_nonpos.mpr (le_of_not_ge h)
    have hright : 1 - |a - b| / (2 * R) ≤ 0 := by
      rw [sub_nonpos, one_le_div (by positivity)]
      exact le_of_not_ge h
    rw [max_eq_right hleft, max_eq_left hright]
    ring

lemma boundaryWeight_mul_quadraticallyNonnegative
    {R : ℝ} (hR : 0 < R) {k : ℝ → ℂ}
    (hpd : IsQuadraticallyNonnegative k) :
    IsQuadraticallyNonnegative
      (fun t => (boundaryWeight R t : ℂ) * k t) := by
  intro n _inst t c
  classical
  let J : n → Set ℝ := fun i => Icc (t i - R) (t i + R)
  let d : ℝ → n → ℂ := fun x i => if x ∈ J i then c i else 0
  let A : n → n → ℝ := fun i j =>
    (star (c i) * k (t i - t j) * c j).re
  let H : ℝ → ℝ := fun x =>
    (∑ i, ∑ j, star (d x i) * k (t i - t j) * d x j).re
  let S : ℝ → ℝ := fun x =>
    ∑ i, ∑ j, (J i ∩ J j).indicator (fun _ => A i j) x
  have hHS (x : ℝ) : H x = S x := by
    dsimp [H, S]
    change
      (∑ i, ∑ j, star (d x i) * k (t i - t j) * d x j).re = _
    change Complex.reCLM
        (∑ i, ∑ j, star (d x i) * k (t i - t j) * d x j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hi : x ∈ J i <;> by_cases hj : x ∈ J j <;>
      simp [d, A, Set.indicator, hi, hj]
  have htermInt (i j : n) : Integrable
      (fun x => (J i ∩ J j).indicator (fun _ => A i j) x) volume := by
    exact (integrableOn_const (C := A i j)
      (ne_of_lt ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top))).integrable_indicator
      (measurableSet_Icc.inter measurableSet_Icc)
  have hSint : Integrable S volume := by
    dsimp [S]
    apply integrable_finsetSum Finset.univ
    intro i _hi
    apply integrable_finsetSum Finset.univ
    intro j _hj
    exact htermInt i j
  have hHnon (x : ℝ) : 0 ≤ H x := by
    exact hpd t (d x)
  have hIntNonneg : 0 ≤ ∫ x, H x := integral_nonneg hHnon
  have hIntEval :
      (∫ x, H x) = ∑ i, ∑ j, volume.real (J i ∩ J j) * A i j := by
    calc
      (∫ x, H x) = ∫ x, S x :=
        integral_congr_ae (ae_of_all volume hHS)
      _ = ∑ i, ∫ x, ∑ j, (J i ∩ J j).indicator
          (fun _ => A i j) x := by
        dsimp [S]
        rw [integral_finsetSum Finset.univ]
        intro i _hi
        exact integrable_finsetSum Finset.univ fun j _hj => htermInt i j
      _ = ∑ i, ∑ j, ∫ x, (J i ∩ J j).indicator
          (fun _ => A i j) x := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [integral_finsetSum Finset.univ]
        intro j _hj
        exact htermInt i j
      _ = ∑ i, ∑ j, volume.real (J i ∩ J j) * A i j := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        rw [integral_indicator_const (A i j) ((measurableSet_Icc.inter measurableSet_Icc))]
        simp only [smul_eq_mul]
        rfl
  rw [hIntEval] at hIntNonneg
  have hreSum :
      (∑ i, ∑ j, star (c i) *
          ((boundaryWeight R (t i - t j) : ℂ) * k (t i - t j)) * c j).re =
        ∑ i, ∑ j, (star (c i) *
          ((boundaryWeight R (t i - t j) : ℂ) * k (t i - t j)) * c j).re := by
    change Complex.reCLM (∑ i, ∑ j, _) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rfl
  have hscaled :
      (∑ i, ∑ j, volume.real (J i ∩ J j) * A i j) =
        2 * R *
          (∑ i, ∑ j, star (c i) *
            ((boundaryWeight R (t i - t j) : ℂ) * k (t i - t j)) * c j).re := by
    rw [hreSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [show volume.real (J i ∩ J j) =
        2 * R * boundaryWeight R (t i - t j) by
      exact volumeReal_centeredIntervals hR]
    dsimp [A]
    have hcplxStar :
        star (c i) *
            ((boundaryWeight R (t i - t j) : ℂ) * k (t i - t j)) * c j =
          (boundaryWeight R (t i - t j) : ℂ) *
            (star (c i) * k (t i - t j) * c j) := by ring
    have hcplx :
        (starRingEnd ℂ) (c i) *
            ((boundaryWeight R (t i - t j) : ℂ) * k (t i - t j)) * c j =
          (boundaryWeight R (t i - t j) : ℂ) *
            ((starRingEnd ℂ) (c i) * k (t i - t j) * c j) := by
      simpa only [starRingEnd_apply] using hcplxStar
    rw [hcplx, Complex.mul_re]
    simp
    ring
  rw [hscaled] at hIntNonneg
  nlinarith

private lemma shiftedZeroDivisor_ne_zero_of_eq_zero
    {Q : ℝ} {u : ℂ} (hu : u ∈ ball (0 : ℂ) Q)
    (hzero : shiftedChiFourXi u = 0) :
    shiftedZeroDivisor Q u ≠ 0 := by
  have hnormal : MeromorphicNFOn shiftedChiFourXi (ball (0 : ℂ) Q) := by
    intro z _hz
    exact differentiable_shiftedChiFourXi.analyticAt z |>.meromorphicNFAt
  have hzeroSet : u ∈ ball (0 : ℂ) Q ∩ shiftedChiFourXi ⁻¹' {0} :=
    ⟨hu, hzero⟩
  rw [hnormal.zero_set_eq_divisor_support] at hzeroSet
  · change u ∈ (shiftedZeroDivisor Q).support
    exact hzeroSet
  · intro z
    exact meromorphicOrderAt_shiftedChiFourXi_ne_top z

lemma shiftedZeroDivisor_mul_I_eq_zeroMultiplicity
    {Q t : ℝ} (htQ : |t| < Q) :
    shiftedZeroDivisor Q ((t : ℂ) * I) =
      (chiFourZeroMultiplicity (boundaryPoint t) : ℤ) := by
  by_cases hdiv : shiftedZeroDivisor Q ((t : ℂ) * I) = 0
  · rw [hdiv]
    have hmult : chiFourZeroMultiplicity (boundaryPoint t) = 0 := by
      by_contra hmult
      have hL : DirichletCharacter.LFunction chiFour (boundaryPoint t) = 0 := by
        by_contra hL
        apply hmult
        unfold chiFourZeroMultiplicity analyticOrderNatAt
        rw [(differentiable_chiFour_LFunction.analyticAt _).analyticOrderAt_eq_zero.mpr hL]
        rfl
      have hcompleted :
          DirichletCharacter.completedLFunction chiFour (boundaryPoint t) = 0 :=
        (chiFour_LFunction_zero_iff_completed (by
          rw [boundaryPoint_re]
          norm_num)).mp hL
      have hshifted : shiftedChiFourXi ((t : ℂ) * I) = 0 := by
        unfold shiftedChiFourXi Submission.ZeroExistence.chiFourXi
        rw [show (1 / 2 : ℂ) + (t : ℂ) * I = boundaryPoint t by
          rfl, hcompleted, mul_zero]
      have huBall : ((t : ℂ) * I) ∈ ball (0 : ℂ) Q := by
        rw [mem_ball, dist_zero_right, norm_mul]
        simpa [Complex.norm_real, Real.norm_eq_abs] using htQ
      exact (shiftedZeroDivisor_ne_zero_of_eq_zero huBall hshifted) hdiv
    simp [hmult]
  · simpa [boundaryPoint] using
      (shiftedZeroDivisor_eq_zeroMultiplicity hdiv)

noncomputable def weightedBoundaryKernel (R t : ℝ) : ℂ :=
  (boundaryWeight R t : ℂ) * boundaryKernel t

noncomputable def boundaryFrequencySet (Q : ℝ) : Finset ℝ :=
  {0} ∪ (shiftedZeroDivisor_support_finite Q).toFinset.image Complex.im

private lemma weightedBoundaryKernel_support
    {Q R : ℝ} (hR : 0 < R) (hRQ : 2 * R < Q) :
    ∀ t, t ∉ boundaryFrequencySet Q → weightedBoundaryKernel R t = 0 := by
  intro t ht
  by_cases hw : boundaryWeight R t = 0
  · simp [weightedBoundaryKernel, hw]
  have htRange : |t| < 2 * R := by
    by_contra h
    exact hw (boundaryWeight_eq_zero hR (le_of_not_gt h))
  have htQ : |t| < Q := htRange.trans hRQ
  by_cases ht0 : t = 0
  · subst t
    exact (ht (by simp [boundaryFrequencySet])).elim
  have hdiv : shiftedZeroDivisor Q ((t : ℂ) * I) = 0 := by
    by_contra hdiv
    apply ht
    simp only [boundaryFrequencySet, Finset.mem_union, Finset.mem_singleton]
    right
    apply Finset.mem_image.mpr
    refine ⟨(t : ℂ) * I, ?_, by simp⟩
    exact (shiftedZeroDivisor_support_finite Q).mem_toFinset.mpr hdiv
  have hmultZ := shiftedZeroDivisor_mul_I_eq_zeroMultiplicity htQ
  have hmult : chiFourZeroMultiplicity (boundaryPoint t) = 0 := by
    have hz : (chiFourZeroMultiplicity (boundaryPoint t) : ℤ) = 0 := by
      rw [← hmultZ, hdiv]
    exact_mod_cast hz
  simp [weightedBoundaryKernel, boundaryKernel, boundaryResidueMass, ht0, hmult]

private lemma weightedBoundaryKernel_zero {R : ℝ} :
    weightedBoundaryKernel R 0 = (Real.log 2 : ℝ) := by
  unfold weightedBoundaryKernel boundaryKernel boundaryResidueMass boundaryPoint
  rw [if_pos rfl]
  simp [boundaryWeight]

private lemma weightedBoundaryKernel_term_eq
    {C Q R x : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    {u : ℂ} (hdiv : shiftedZeroDivisor Q u ≠ 0) :
    weightedBoundaryKernel R u.im *
        Complex.exp ((((u.im * x : ℝ) : ℂ) * I)) =
      ((Real.log 2 : ℝ) : ℂ) * boundaryZeroTerm Q R x u := by
  have huBall : u ∈ ball (0 : ℂ) Q :=
    (shiftedZeroDivisor Q).supportWithinDomain hdiv
  have hQ : 0 < Q := (norm_nonneg u).trans_lt (by
    simpa [mem_ball, dist_zero_right] using huBall)
  have hure := shifted_zero_re_eq_zero_of_global_positive_neg_one hone hdiv
  have hueq : u = (u.im : ℂ) * I := by
    apply Complex.ext
    · simp [hure]
    · simp
  have himQ : |u.im| < Q := by
    rw [← norm_eq_abs_im hure]
    simpa [mem_ball, dist_zero_right] using huBall
  have him0 : u.im ≠ 0 := by
    intro him
    have hu0 : u = 0 := by
      apply Complex.ext
      · simp [hure]
      · simp [him]
    subst u
    exact hdiv (shiftedZeroDivisor_zero hQ)
  have hmultZ := shiftedZeroDivisor_mul_I_eq_zeroMultiplicity himQ
  rw [← hueq] at hmultZ
  have hmass : boundaryResidueMass u.im = (shiftedZeroDivisor Q u : ℂ) := by
    unfold boundaryResidueMass
    rw [if_neg him0]
    exact_mod_cast hmultZ.symm
  have hpoint : boundaryPoint u.im = 1 / 2 + u := by
    apply Complex.ext <;> simp [boundaryPoint, hure]
  have hexp : Complex.exp ((((u.im * x : ℝ) : ℂ) * I)) =
      Complex.exp (u * (x : ℂ)) := by
    congr 1
    calc
      ((u.im * x : ℝ) : ℂ) * I =
          ((u.im : ℂ) * I) * (x : ℂ) := by
        push_cast
        ring
      _ = u * (x : ℂ) := by rw [← hueq]
  unfold weightedBoundaryKernel boundaryKernel boundaryZeroTerm
  rw [hmass, hpoint, hexp]
  ring

lemma weightedBoundaryKernel_fourierSum_eq
    {C Q R x : ℝ} (hone : ∀ n, 1 ≤ adjustedPrimeSum (-1) C n)
    (hQ : 0 < Q) :
    (∑ t ∈ boundaryFrequencySet Q,
        weightedBoundaryKernel R t *
          Complex.exp ((((t * x : ℝ) : ℂ) * I))) =
      ((Real.log 2 : ℝ) : ℂ) * boundaryPolynomial Q R x := by
  let U := (shiftedZeroDivisor_support_finite Q).toFinset
  have himageInj : Set.InjOn Complex.im (U : Set ℂ) := by
    intro u hu v hv huv
    have hdivu : shiftedZeroDivisor Q u ≠ 0 :=
      (shiftedZeroDivisor_support_finite Q).mem_toFinset.mp hu
    have hdivv : shiftedZeroDivisor Q v ≠ 0 :=
      (shiftedZeroDivisor_support_finite Q).mem_toFinset.mp hv
    have hure := shifted_zero_re_eq_zero_of_global_positive_neg_one hone hdivu
    have hvre := shifted_zero_re_eq_zero_of_global_positive_neg_one hone hdivv
    apply Complex.ext
    · simp [hure, hvre]
    · exact huv
  have hdisjoint : Disjoint ({0} : Finset ℝ) (U.image Complex.im) := by
    rw [Finset.disjoint_left]
    intro t ht0 htU
    simp only [Finset.mem_singleton] at ht0
    subst t
    obtain ⟨u, hu, huim⟩ := Finset.mem_image.mp htU
    have hdiv : shiftedZeroDivisor Q u ≠ 0 :=
      (shiftedZeroDivisor_support_finite Q).mem_toFinset.mp hu
    have hure := shifted_zero_re_eq_zero_of_global_positive_neg_one hone hdiv
    have hu0 : u = 0 := by
      apply Complex.ext
      · simp [hure]
      · simpa using huim
    subst u
    exact hdiv (shiftedZeroDivisor_zero hQ)
  unfold boundaryFrequencySet
  change (∑ t ∈ ({0} ∪ U.image Complex.im),
      weightedBoundaryKernel R t *
        Complex.exp ((((t * x : ℝ) : ℂ) * I))) = _
  rw [Finset.sum_union hdisjoint]
  simp only [Finset.sum_singleton, zero_mul, ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one, weightedBoundaryKernel_zero]
  rw [Finset.sum_image]
  · have hterms :
        (∑ u ∈ U, weightedBoundaryKernel R u.im *
            Complex.exp ((((u.im * x : ℝ) : ℂ) * I))) =
          ∑ u ∈ U, ((Real.log 2 : ℝ) : ℂ) *
            boundaryZeroTerm Q R x u := by
        apply Finset.sum_congr rfl
        intro u hu
        exact weightedBoundaryKernel_term_eq hone
          ((shiftedZeroDivisor_support_finite Q).mem_toFinset.mp hu)
    rw [hterms]
    unfold boundaryPolynomial
    change ((Real.log 2 : ℝ) : ℂ) +
        ∑ u ∈ U, ((Real.log 2 : ℝ) : ℂ) * boundaryZeroTerm Q R x u =
      ((Real.log 2 : ℝ) : ℂ) *
        (1 + ∑ u ∈ U, boundaryZeroTerm Q R x u)
    rw [← Finset.mul_sum, mul_add, mul_one]
  · intro u hu v hv huv
    exact himageInj hu hv huv

theorem not_global_positive_adjustedPrimeSum_neg_one (C : ℝ) :
    ¬ ∀ n, 1 ≤ adjustedPrimeSum (-1) C n := by
  intro hone
  obtain ⟨Q, R, hRfour, hRQ, _hfree, hpolyNeg⟩ :=
    exists_boundaryPolynomial_re_neg hone
  have hR : 0 < R := by linarith
  have hQ : 0 < Q := by linarith
  have hpd : IsQuadraticallyNonnegative (weightedBoundaryKernel R) := by
    exact boundaryWeight_mul_quadraticallyNonnegative hR
      (boundaryKernel_quadraticallyNonnegative hone)
  have hsupp : ∀ t, t ∉ boundaryFrequencySet Q →
      weightedBoundaryKernel R t = 0 :=
    weightedBoundaryKernel_support hR hRQ
  have hnon := fourierSum_nonneg_of_finite_support
    (weightedBoundaryKernel R) hpd (boundaryFrequencySet Q) hsupp (-1 / R)
  rw [weightedBoundaryKernel_fourierSum_eq hone hQ] at hnon
  rw [Complex.mul_re] at hnon
  simp only [ofReal_re, ofReal_im, zero_mul] at hnon
  rw [boundaryPolynomial_re_eq hone] at hnon
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

lemma realCharacterPrimeSum_arbitrarily_negative :
    ∀ N : ℕ, ∃ n > N, realCharacterPrimeSum n < 0 := by
  have hnot : ¬ ∀ᶠ n : ℕ in atTop, 0 ≤ realCharacterPrimeSum n := by
    intro h
    obtain ⟨C, hC⟩ := exists_global_positive_shift_of_eventually_nonneg h
    exact not_global_positive_adjustedPrimeSum_one C (by
      simpa [adjustedPrimeSum] using hC)
  intro N
  by_contra h
  push Not at h
  apply hnot
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  exact h n (lt_of_lt_of_le (Nat.lt_succ_self N) hn)

lemma realCharacterPrimeSum_arbitrarily_positive :
    ∀ N : ℕ, ∃ n > N, 0 < realCharacterPrimeSum n := by
  have hnot : ¬ ∀ᶠ n : ℕ in atTop, realCharacterPrimeSum n ≤ 0 := by
    intro h
    obtain ⟨C, hC⟩ := exists_global_positive_shift_of_eventually_nonpos h
    exact not_global_positive_adjustedPrimeSum_neg_one C (by
      simpa [adjustedPrimeSum] using hC)
  intro N
  by_contra h
  push Not at h
  apply hnot
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  exact h n (lt_of_lt_of_le (Nat.lt_succ_self N) hn)

theorem chebyshev_sign_change :
    chebyshevLead.Infinite ∧
      {n : ℕ | primeCountingMod 3 n < primeCountingMod 1 n}.Infinite := by
  apply chebyshev_sign_change_of_characterPrimeSum_oscillation
  constructor
  · intro N
    obtain ⟨n, hn, hneg⟩ := realCharacterPrimeSum_arbitrarily_negative N
    refine ⟨n, hn, ?_⟩
    unfold realCharacterPrimeSum at hneg
    exact_mod_cast hneg
  · intro N
    obtain ⟨n, hn, hpos⟩ := realCharacterPrimeSum_arbitrarily_positive N
    refine ⟨n, hn, ?_⟩
    unfold realCharacterPrimeSum at hpos
    exact_mod_cast hpos

end Submission.BoundaryContradiction
