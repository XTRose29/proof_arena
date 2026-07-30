import Submission.Central
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Real.Cardinality

open Filter InnerProductSpace Metric Real Set

namespace Submission.ZeroMass

open Submission.ZeroExistence

noncomputable def shiftedChiFourXi (z : ℂ) : ℂ :=
  chiFourXi (1 / 2 + z)

lemma differentiable_shiftedChiFourXi : Differentiable ℂ shiftedChiFourXi := by
  intro z
  exact (differentiable_chiFourXi (1 / 2 + z)).comp z (by fun_prop)

lemma shiftedChiFourXi_neg (z : ℂ) :
    shiftedChiFourXi (-z) = shiftedChiFourXi z := by
  unfold shiftedChiFourXi
  convert chiFourXi_one_sub (1 / 2 + z) using 1
  ring_nf

lemma shiftedChiFourXi_zero_ne : shiftedChiFourXi 0 ≠ 0 := by
  have hcompleted :
      DirichletCharacter.completedLFunction Submission.Helpers.chiFour (1 / 2 : ℂ) ≠ 0 := by
    intro hzero
    apply Submission.Central.chiFour_LFunction_central_ne_zero
    rw [Submission.Analytic.chiFour_LFunction_eq_completed_mul_invGammaFactor]
    change DirichletCharacter.completedLFunction Submission.Helpers.chiFour (1 / 2 : ℂ) *
      (Submission.Helpers.chiFour.gammaFactor (1 / 2 : ℂ))⁻¹ = 0
    rw [hzero]
    simp
  rw [shiftedChiFourXi, add_zero, chiFourXi]
  exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) hcompleted

lemma norm_shiftedChiFourXi_growth (z : ℂ) :
    ‖shiftedChiFourXi z‖ ≤ Real.exp
      (chiFourXiGrowthConstant *
        (1 + ‖1 / 2 + z‖ * Real.sqrt ‖1 / 2 + z‖)) := by
  exact norm_chiFourXi_growth (1 / 2 + z)

noncomputable def shiftedOddPoint (n : ℕ) : ℝ :=
  (2 * n + 1 : ℝ) - 1 / 2

lemma shiftedOddPoint_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < shiftedOddPoint n := by
  unfold shiftedOddPoint
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith

lemma norm_shiftedChiFourXi_odd_lower (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) / 4 ≤ ‖shiftedChiFourXi (shiftedOddPoint n)‖ := by
  have harg : (1 / 2 : ℂ) + (shiftedOddPoint n : ℂ) = ((2 * n + 1 : ℕ) : ℂ) := by
    unfold shiftedOddPoint
    push_cast
    ring
  rw [shiftedChiFourXi, harg]
  exact norm_chiFourXi_odd_nat_lower n hn

lemma meromorphic_shiftedChiFourXi : Meromorphic shiftedChiFourXi := by
  intro z
  exact (differentiable_shiftedChiFourXi.analyticAt z).meromorphicAt

lemma meromorphicOrderAt_shiftedChiFourXi_ne_top (z : ℂ) :
    meromorphicOrderAt shiftedChiFourXi z ≠ ⊤ := by
  apply meromorphic_shiftedChiFourXi.exists_meromorphicOrderAt_ne_top_iff_forall.1
  use 0
  rw [(differentiable_shiftedChiFourXi.analyticAt 0).meromorphicNFAt
    |>.meromorphicOrderAt_eq_zero_iff.mpr shiftedChiFourXi_zero_ne]
  exact WithTop.zero_ne_top

noncomputable def shiftedZeroDivisor (R : ℝ) :=
  MeromorphicOn.divisor shiftedChiFourXi (ball (0 : ℂ) R)

lemma shiftedZeroDivisor_support_finite (R : ℝ) :
    (shiftedZeroDivisor R).support.Finite := by
  apply MeromorphicOn.divisor_ball_support_finite
  intro z hz
  exact meromorphic_shiftedChiFourXi z

lemma shiftedZeroDivisor_nonneg (R : ℝ) : 0 ≤ shiftedZeroDivisor R := by
  have hanalytic : AnalyticOnNhd ℂ shiftedChiFourXi (ball (0 : ℂ) R) := by
    intro z hz
    exact differentiable_shiftedChiFourXi.analyticAt z
  exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic

lemma shiftedZeroDivisor_zero {R : ℝ} (hR : 0 < R) :
    shiftedZeroDivisor R 0 = 0 := by
  unfold shiftedZeroDivisor
  rw [MeromorphicOn.divisor_apply (fun z hz ↦ meromorphic_shiftedChiFourXi z)
    (mem_ball_self hR)]
  rw [(differentiable_shiftedChiFourXi.analyticAt 0).meromorphicNFAt
    |>.meromorphicOrderAt_eq_zero_iff.mpr shiftedChiFourXi_zero_ne]
  simp

noncomputable def shiftedZeroMass (R : ℝ) : ℝ :=
  ∑ᶠ u, (shiftedZeroDivisor R u : ℝ) / ‖u‖

lemma shiftedZeroMass_nonneg (R : ℝ) : 0 ≤ shiftedZeroMass R := by
  unfold shiftedZeroMass
  apply finsum_nonneg
  intro u
  exact div_nonneg (by exact_mod_cast shiftedZeroDivisor_nonneg R u) (norm_nonneg u)

lemma exists_shiftedChiFourXi_zero_free_radius (L : ℝ) :
    ∃ R ∈ Ioo L (L + 1), ∀ z ∈ sphere (0 : ℂ) R, shiftedChiFourXi z ≠ 0 := by
  let badRadii : Set ℝ :=
    norm '' (shiftedZeroDivisor (L + 1)).support
  have hbadFinite : badRadii.Finite := by
    exact (shiftedZeroDivisor_support_finite (L + 1)).image norm
  obtain ⟨R, hR, hRbad⟩ :=
    (Ioo_infinite (show L < L + 1 by linarith)).exists_notMem_finite hbadFinite
  refine ⟨R, hR, ?_⟩
  intro z hz hzZero
  have hzNorm : ‖z‖ = R := by
    simpa [mem_sphere_iff_norm] using hz
  have hzBall : z ∈ ball (0 : ℂ) (L + 1) := by
    rw [mem_ball_iff_norm, sub_zero, hzNorm]
    exact hR.2
  have hnormal :
      MeromorphicNFOn shiftedChiFourXi (ball (0 : ℂ) (L + 1)) := by
    intro w hw
    exact (differentiable_shiftedChiFourXi.analyticAt w).meromorphicNFAt
  have hzSupport : z ∈ (shiftedZeroDivisor (L + 1)).support := by
    change z ∈ Function.support
      (MeromorphicOn.divisor shiftedChiFourXi (ball (0 : ℂ) (L + 1)))
    rw [← hnormal.zero_set_eq_divisor_support]
    · exact ⟨hzBall, by simpa using hzZero⟩
    · intro w
      exact meromorphicOrderAt_shiftedChiFourXi_ne_top w
  apply hRbad
  exact ⟨z, hzSupport, hzNorm⟩

noncomputable def shiftedCanonicalProduct (R : ℝ) : ℂ → ℂ :=
  ∏ᶠ u, (Complex.canonicalFactor R u) ^ (-shiftedZeroDivisor R u)

private lemma shiftedCanonicalProduct_mulSupport_finite (R : ℝ) :
    Function.HasFiniteMulSupport
      (fun u ↦ (Complex.canonicalFactor R u) ^ (-shiftedZeroDivisor R u)) := by
  apply (shiftedZeroDivisor_support_finite R).subset
  intro u hu
  rw [Function.mem_support]
  intro hdiv
  simp [hdiv] at hu

lemma analyticAt_shiftedCanonicalProduct_of_mem_sphere
    {R : ℝ} {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    AnalyticAt ℂ (shiftedCanonicalProduct R) z := by
  unfold shiftedCanonicalProduct
  apply analyticAt_finprod
  intro u
  by_cases hu : shiftedZeroDivisor R u = 0
  · have hfun : (Complex.canonicalFactor R u) ^ (-shiftedZeroDivisor R u) =
        fun _ ↦ (1 : ℂ) := by
      ext w
      simp [hu]
    rw [hfun]
    exact analyticAt_const
  have huBall : u ∈ ball (0 : ℂ) R :=
    (shiftedZeroDivisor R).supportWithinDomain hu
  have hzu : z ≠ u := by
    intro h
    subst z
    have huNorm : ‖u‖ < R := by simpa [mem_ball_iff_norm] using huBall
    have huNormEq : ‖u‖ = R := by simpa [mem_sphere_iff_norm] using hz
    linarith
  exact (Complex.analyticOnNhd_canonicalFactor R u z hzu).zpow
    (Complex.canonicalFactor_ne_zero huBall (sphere_subset_closedBall hz) hzu)

lemma shiftedCanonicalProduct_ne_zero_of_mem_sphere
    {R : ℝ} {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    shiftedCanonicalProduct R z ≠ 0 := by
  unfold shiftedCanonicalProduct
  rw [finprod_apply (shiftedCanonicalProduct_mulSupport_finite R) z]
  apply finprod_ne_zero
  intro u
  by_cases hu : shiftedZeroDivisor R u = 0
  · simp [hu]
  have huBall : u ∈ ball (0 : ℂ) R :=
    (shiftedZeroDivisor R).supportWithinDomain hu
  have hzu : z ≠ u := by
    intro h
    subst z
    have huNorm : ‖u‖ < R := by simpa [mem_ball_iff_norm] using huBall
    have huNormEq : ‖u‖ = R := by simpa [mem_sphere_iff_norm] using hz
    linarith
  exact zpow_ne_zero _
    (Complex.canonicalFactor_ne_zero huBall (sphere_subset_closedBall hz) hzu)

lemma norm_shiftedCanonicalProduct_of_mem_sphere
    {R : ℝ} {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖shiftedCanonicalProduct R z‖ = 1 := by
  unfold shiftedCanonicalProduct
  rw [finprod_apply (shiftedCanonicalProduct_mulSupport_finite R) z]
  simp only [Pi.pow_apply]
  have hfinite : Function.HasFiniteMulSupport
      (fun u ↦ Complex.canonicalFactor R u z ^ (-shiftedZeroDivisor R u)) := by
    apply (shiftedZeroDivisor_support_finite R).subset
    intro u hu
    rw [Function.mem_support]
    intro hdiv
    simp [hdiv] at hu
  rw [finprod_eq_prod _ hfinite]
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro u hu
  by_cases hdiv : shiftedZeroDivisor R u = 0
  · simp [hdiv]
  have huBall : u ∈ ball (0 : ℂ) R :=
    (shiftedZeroDivisor R).supportWithinDomain hdiv
  rw [norm_zpow, Complex.norm_canonicalFactor_eval_circle_eq_one huBall hz,
    one_zpow]

lemma analyticAt_shiftedCanonicalProduct_zero {R : ℝ} (hR : 0 < R) :
    AnalyticAt ℂ (shiftedCanonicalProduct R) 0 := by
  unfold shiftedCanonicalProduct
  apply analyticAt_finprod
  intro u
  by_cases hdiv : shiftedZeroDivisor R u = 0
  · have hfun : (Complex.canonicalFactor R u) ^ (-shiftedZeroDivisor R u) =
        fun _ ↦ (1 : ℂ) := by
      ext w
      simp [hdiv]
    rw [hfun]
    exact analyticAt_const
  have huBall : u ∈ ball (0 : ℂ) R :=
    (shiftedZeroDivisor R).supportWithinDomain hdiv
  have hu0 : (0 : ℂ) ≠ u := by
    intro h
    subst u
    exact hdiv (shiftedZeroDivisor_zero hR)
  exact (Complex.analyticOnNhd_canonicalFactor R u 0 hu0).zpow
    (Complex.canonicalFactor_ne_zero huBall (mem_closedBall_self hR.le) hu0)

lemma shiftedCanonicalProduct_zero_ne {R : ℝ} (hR : 0 < R) :
    shiftedCanonicalProduct R 0 ≠ 0 := by
  unfold shiftedCanonicalProduct
  rw [finprod_apply (shiftedCanonicalProduct_mulSupport_finite R) 0]
  apply finprod_ne_zero
  intro u
  by_cases hdiv : shiftedZeroDivisor R u = 0
  · simp [hdiv]
  have huBall : u ∈ ball (0 : ℂ) R :=
    (shiftedZeroDivisor R).supportWithinDomain hdiv
  have hu0 : (0 : ℂ) ≠ u := by
    intro h
    subst u
    exact hdiv (shiftedZeroDivisor_zero hR)
  exact zpow_ne_zero _
    (Complex.canonicalFactor_ne_zero huBall (mem_closedBall_self hR.le) hu0)

lemma shiftedZeroDivisor_eq_zero_of_ne_zero
    {R : ℝ} {z : ℂ} (_hz : z ∈ closedBall (0 : ℂ) R)
    (hfz : shiftedChiFourXi z ≠ 0) :
    shiftedZeroDivisor R z = 0 := by
  by_cases hzBall : z ∈ ball (0 : ℂ) R
  · unfold shiftedZeroDivisor
    rw [MeromorphicOn.divisor_apply (fun w hw ↦ meromorphic_shiftedChiFourXi w) hzBall]
    rw [(differentiable_shiftedChiFourXi.analyticAt z).meromorphicNFAt
      |>.meromorphicOrderAt_eq_zero_iff.mpr hfz]
    simp
  · exact (shiftedZeroDivisor R).apply_eq_zero_of_notMem hzBall

lemma analyticAt_shiftedCanonicalProduct_of_ne_zero
    {R : ℝ} {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R)
    (hfz : shiftedChiFourXi z ≠ 0) :
    AnalyticAt ℂ (shiftedCanonicalProduct R) z := by
  have hzDiv := shiftedZeroDivisor_eq_zero_of_ne_zero hz hfz
  unfold shiftedCanonicalProduct
  apply analyticAt_finprod
  intro u
  by_cases hdiv : shiftedZeroDivisor R u = 0
  · have hfun : (Complex.canonicalFactor R u) ^ (-shiftedZeroDivisor R u) =
        fun _ ↦ (1 : ℂ) := by
      ext w
      simp [hdiv]
    rw [hfun]
    exact analyticAt_const
  have huBall : u ∈ ball (0 : ℂ) R :=
    (shiftedZeroDivisor R).supportWithinDomain hdiv
  have hzu : z ≠ u := by
    intro h
    subst u
    exact hdiv hzDiv
  exact (Complex.analyticOnNhd_canonicalFactor R u z hzu).zpow
    (Complex.canonicalFactor_ne_zero huBall hz hzu)

lemma shiftedCanonicalProduct_ne_zero_of_ne_zero
    {R : ℝ} {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R)
    (hfz : shiftedChiFourXi z ≠ 0) :
    shiftedCanonicalProduct R z ≠ 0 := by
  have hzDiv := shiftedZeroDivisor_eq_zero_of_ne_zero hz hfz
  unfold shiftedCanonicalProduct
  rw [finprod_apply (shiftedCanonicalProduct_mulSupport_finite R) z]
  apply finprod_ne_zero
  intro u
  by_cases hdiv : shiftedZeroDivisor R u = 0
  · simp [hdiv]
  have huBall : u ∈ ball (0 : ℂ) R :=
    (shiftedZeroDivisor R).supportWithinDomain hdiv
  have hzu : z ≠ u := by
    intro h
    subst u
    exact hdiv hzDiv
  exact zpow_ne_zero _ (Complex.canonicalFactor_ne_zero huBall hz hzu)

private lemma norm_canonicalFactor_zero {R : ℝ} (hR : 0 < R) {u : ℂ}
    (hu : u ≠ 0) :
    ‖Complex.canonicalFactor R u 0‖ = R / ‖u‖ := by
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  field_simp [hR.ne', norm_ne_zero_iff.mpr hu]

lemma norm_shiftedCanonicalProduct_zero_le_one {R : ℝ} (hR : 0 < R) :
    ‖shiftedCanonicalProduct R 0‖ ≤ 1 := by
  unfold shiftedCanonicalProduct
  rw [finprod_apply (shiftedCanonicalProduct_mulSupport_finite R) 0]
  simp only [Pi.pow_apply]
  have hfinite : Function.HasFiniteMulSupport
      (fun u ↦ Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)) := by
    apply (shiftedZeroDivisor_support_finite R).subset
    intro u hu
    rw [Function.mem_support]
    intro hdiv
    simp [hdiv] at hu
  rw [finprod_eq_prod _ hfinite, norm_prod]
  apply Finset.prod_le_one
  · intro u hu
    positivity
  · intro u hu
    by_cases hdiv : shiftedZeroDivisor R u = 0
    · simp [hdiv]
    have huBall : u ∈ ball (0 : ℂ) R :=
      (shiftedZeroDivisor R).supportWithinDomain hdiv
    have hu0 : u ≠ 0 := by
      intro h
      subst u
      exact hdiv (shiftedZeroDivisor_zero hR)
    rw [norm_zpow, norm_canonicalFactor_zero hR hu0]
    apply zpow_le_one_of_nonpos₀
    · apply (one_le_div (norm_pos_iff.mpr hu0)).2
      have huNorm : ‖u‖ < R := by simpa [mem_ball_iff_norm] using huBall
      exact huNorm.le
    · exact neg_nonpos.mpr (shiftedZeroDivisor_nonneg R u)

lemma exists_shiftedCanonicalDecomp (R : ℝ) :
    ∃ g : ℂ → ℂ, Complex.CanonicalDecomp shiftedChiFourXi g R := by
  apply MeromorphicOn.exists_canonicalDecomp
  · intro z hz
    exact meromorphic_shiftedChiFourXi z
  · intro z
    exact meromorphicOrderAt_shiftedChiFourXi_ne_top z

lemma shiftedCanonicalDecomp_eq_of_mem_sphere
    {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    shiftedChiFourXi z = shiftedCanonicalProduct R z * g z := by
  have hzClosed : z ∈ closedBall (0 : ℂ) R := sphere_subset_closedBall hz
  have hPAnalytic : AnalyticAt ℂ (shiftedCanonicalProduct R) z :=
    analyticAt_shiftedCanonicalProduct_of_mem_sphere hz
  have hPNe : shiftedCanonicalProduct R z ≠ 0 :=
    shiftedCanonicalProduct_ne_zero_of_mem_sphere hz
  have hleftNF : MeromorphicNFAt shiftedChiFourXi z :=
    (differentiable_shiftedChiFourXi.analyticAt z).meromorphicNFAt
  have hrightNF : MeromorphicNFAt (shiftedCanonicalProduct R • g) z :=
    (hg.meromorphicNFOn hzClosed).smul_analytic hPAnalytic hPNe
  have hperfect : Perfect (closedBall (0 : ℂ) R) := by
    rw [← closure_ball (0 : ℂ) hR.ne']
    exact isOpen_ball.perfect_closure
  have hcodiscrete : shiftedChiFourXi =ᶠ[codiscreteWithin (closedBall (0 : ℂ) R)]
      shiftedCanonicalProduct R • g := by
    simpa only [shiftedCanonicalProduct, shiftedZeroDivisor] using hg.eventuallyEq
  have hpunctured : shiftedChiFourXi =ᶠ[nhdsWithin z {z}ᶜ]
      shiftedCanonicalProduct R • g :=
    hleftNF.meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      hrightNF.meromorphicAt hzClosed (hperfect.acc z hzClosed) hcodiscrete
  have hlocal : shiftedChiFourXi =ᶠ[nhds z] shiftedCanonicalProduct R • g :=
    (hleftNF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hrightNF).1 hpunctured
  simpa [Pi.smul_apply', smul_eq_mul] using hlocal.eq_of_nhds

lemma shiftedCanonicalDecomp_eq_zero
    {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R) :
    shiftedChiFourXi 0 = shiftedCanonicalProduct R 0 * g 0 := by
  have hzClosed : (0 : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  have hPAnalytic := analyticAt_shiftedCanonicalProduct_zero hR
  have hPNe := shiftedCanonicalProduct_zero_ne hR
  have hleftNF : MeromorphicNFAt shiftedChiFourXi 0 :=
    (differentiable_shiftedChiFourXi.analyticAt 0).meromorphicNFAt
  have hrightNF : MeromorphicNFAt (shiftedCanonicalProduct R • g) 0 :=
    (hg.meromorphicNFOn hzClosed).smul_analytic hPAnalytic hPNe
  have hperfect : Perfect (closedBall (0 : ℂ) R) := by
    rw [← closure_ball (0 : ℂ) hR.ne']
    exact isOpen_ball.perfect_closure
  have hcodiscrete : shiftedChiFourXi =ᶠ[codiscreteWithin (closedBall (0 : ℂ) R)]
      shiftedCanonicalProduct R • g := by
    simpa only [shiftedCanonicalProduct, shiftedZeroDivisor] using hg.eventuallyEq
  have hpunctured : shiftedChiFourXi =ᶠ[nhdsWithin 0 ({0} : Set ℂ)ᶜ]
      shiftedCanonicalProduct R • g :=
    hleftNF.meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      hrightNF.meromorphicAt hzClosed (hperfect.acc 0 hzClosed) hcodiscrete
  have hlocal : shiftedChiFourXi =ᶠ[nhds 0] shiftedCanonicalProduct R • g :=
    (hleftNF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hrightNF).1 hpunctured
  simpa [Pi.smul_apply', smul_eq_mul] using hlocal.eq_of_nhds

lemma shiftedCanonicalDecomp_eq_of_ne_zero
    {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) (hfz : shiftedChiFourXi z ≠ 0) :
    shiftedChiFourXi z = shiftedCanonicalProduct R z * g z := by
  have hPAnalytic := analyticAt_shiftedCanonicalProduct_of_ne_zero hz hfz
  have hPNe := shiftedCanonicalProduct_ne_zero_of_ne_zero hz hfz
  have hleftNF : MeromorphicNFAt shiftedChiFourXi z :=
    (differentiable_shiftedChiFourXi.analyticAt z).meromorphicNFAt
  have hrightNF : MeromorphicNFAt (shiftedCanonicalProduct R • g) z :=
    (hg.meromorphicNFOn hz).smul_analytic hPAnalytic hPNe
  have hperfect : Perfect (closedBall (0 : ℂ) R) := by
    rw [← closure_ball (0 : ℂ) hR.ne']
    exact isOpen_ball.perfect_closure
  have hcodiscrete : shiftedChiFourXi =ᶠ[codiscreteWithin (closedBall (0 : ℂ) R)]
      shiftedCanonicalProduct R • g := by
    simpa only [shiftedCanonicalProduct, shiftedZeroDivisor] using hg.eventuallyEq
  have hpunctured : shiftedChiFourXi =ᶠ[nhdsWithin z {z}ᶜ]
      shiftedCanonicalProduct R • g :=
    hleftNF.meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      hrightNF.meromorphicAt hz (hperfect.acc z hz) hcodiscrete
  have hlocal : shiftedChiFourXi =ᶠ[nhds z] shiftedCanonicalProduct R • g :=
    (hleftNF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hrightNF).1 hpunctured
  simpa [Pi.smul_apply', smul_eq_mul] using hlocal.eq_of_nhds

lemma norm_shiftedChiFourXi_zero_le_canonicalDecomp
    {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R) :
    ‖shiftedChiFourXi 0‖ ≤ ‖g 0‖ := by
  calc
    ‖shiftedChiFourXi 0‖ = ‖shiftedCanonicalProduct R 0‖ * ‖g 0‖ := by
      rw [shiftedCanonicalDecomp_eq_zero hR hg, norm_mul]
    _ ≤ 1 * ‖g 0‖ :=
      mul_le_mul_of_nonneg_right (norm_shiftedCanonicalProduct_zero_le_one hR)
        (norm_nonneg _)
    _ = ‖g 0‖ := one_mul _

lemma shiftedCanonicalDecomp_ne_zero_closedBall
    {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R)
    (hfree : ∀ z ∈ sphere (0 : ℂ) R, shiftedChiFourXi z ≠ 0) :
    ∀ z ∈ closedBall (0 : ℂ) R, g z ≠ 0 := by
  intro z hzClosed
  by_cases hzBall : z ∈ ball (0 : ℂ) R
  · exact hg.ne_zero z hzBall
  have hzSphere : z ∈ sphere (0 : ℂ) R := by
    rw [mem_sphere]
    rw [mem_closedBall] at hzClosed
    rw [mem_ball] at hzBall
    exact le_antisymm hzClosed (le_of_not_gt hzBall)
  intro hgz
  apply hfree z hzSphere
  rw [shiftedCanonicalDecomp_eq_of_mem_sphere hR hg hzSphere, hgz, mul_zero]

lemma shiftedCanonicalDecomp_analyticOnNhd
    {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R)
    (hfree : ∀ z ∈ sphere (0 : ℂ) R, shiftedChiFourXi z ≠ 0) :
    AnalyticOnNhd ℂ g (closedBall (0 : ℂ) R) := by
  intro z hz
  have hgne := shiftedCanonicalDecomp_ne_zero_closedBall hR hg hfree z hz
  have hgnf := hg.meromorphicNFOn hz
  apply hgnf.meromorphicOrderAt_nonneg_iff_analyticAt.1
  rw [hgnf.meromorphicOrderAt_eq_zero_iff.mpr hgne]

lemma norm_shiftedCanonicalDecomp_eq_of_mem_sphere
    {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖g z‖ = ‖shiftedChiFourXi z‖ := by
  have heq := shiftedCanonicalDecomp_eq_of_mem_sphere hR hg hz
  calc
    ‖g z‖ = ‖shiftedCanonicalProduct R z * g z‖ := by
      rw [norm_mul, norm_shiftedCanonicalProduct_of_mem_sphere hz, one_mul]
    _ = ‖shiftedChiFourXi z‖ := congrArg norm heq |>.symm

lemma chiFourXiGrowthConstant_nonneg : 0 ≤ chiFourXiGrowthConstant := by
  unfold chiFourXiGrowthConstant chiFourXiRightGrowthConstant chiFourLNormBound
  have hstrip := Submission.Growth.chiFourCompletedStripBound_nonneg (1 / 2) 3
  have hsum : 0 ≤ ∑' n : ℕ,
      ‖LSeries.term (Submission.Helpers.chiFour ·) (2 : ℂ) n‖ :=
    tsum_nonneg fun _ ↦ norm_nonneg _
  nlinarith

noncomputable def shiftedGrowthMajorant (R : ℝ) : ℝ :=
  Real.exp (chiFourXiGrowthConstant *
    (1 + (R + 1) * Real.sqrt (R + 1)))

lemma shiftedGrowthMajorant_pos (R : ℝ) : 0 < shiftedGrowthMajorant R := by
  exact Real.exp_pos _

lemma one_le_shiftedGrowthMajorant {R : ℝ} (hR : 0 ≤ R) :
    1 ≤ shiftedGrowthMajorant R := by
  exact Real.one_le_exp
    (mul_nonneg chiFourXiGrowthConstant_nonneg (by positivity))

lemma norm_shiftedChiFourXi_le_growthMajorant_of_mem_sphere
    {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖shiftedChiFourXi z‖ ≤ shiftedGrowthMajorant R := by
  have hzNorm : ‖z‖ = R := by simpa [mem_sphere_iff_norm] using hz
  have hnorm : ‖1 / 2 + z‖ ≤ R + 1 := by
    calc
      ‖1 / 2 + z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖z‖ := norm_add_le _ _
      _ = 1 / 2 + R := by rw [hzNorm]; norm_num
      _ ≤ R + 1 := by linarith
  have hsqrt : Real.sqrt ‖1 / 2 + z‖ ≤ Real.sqrt (R + 1) :=
    Real.sqrt_le_sqrt hnorm
  have hprod : ‖1 / 2 + z‖ * Real.sqrt ‖1 / 2 + z‖ ≤
      (R + 1) * Real.sqrt (R + 1) :=
    mul_le_mul hnorm hsqrt (Real.sqrt_nonneg _) (by linarith)
  apply (norm_shiftedChiFourXi_growth z).trans
  unfold shiftedGrowthMajorant
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by linarith) chiFourXiGrowthConstant_nonneg

noncomputable def canonicalRemainderGap (R : ℝ) (g : ℂ → ℂ) (z : ℂ) : ℝ :=
  Real.log (shiftedGrowthMajorant R) - Real.log ‖g z‖

lemma harmonicOnNhd_canonicalRemainderGap
    {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R)
    (hfree : ∀ z ∈ sphere (0 : ℂ) R, shiftedChiFourXi z ≠ 0) :
    HarmonicOnNhd (canonicalRemainderGap R g) (closedBall (0 : ℂ) R) := by
  have hganalytic := shiftedCanonicalDecomp_analyticOnNhd hR hg hfree
  have hgne := shiftedCanonicalDecomp_ne_zero_closedBall hR hg hfree
  intro z hz
  unfold canonicalRemainderGap
  exact (harmonicAt_const _).sub
    ((hganalytic z hz).harmonicAt_log_norm (hgne z hz))

lemma canonicalRemainderGap_nonneg_of_mem_sphere
    {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R)
    (hfree : ∀ z ∈ sphere (0 : ℂ) R, shiftedChiFourXi z ≠ 0)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    0 ≤ canonicalRemainderGap R g z := by
  unfold canonicalRemainderGap
  have hgNorm : ‖g z‖ ≤ shiftedGrowthMajorant R := by
    rw [norm_shiftedCanonicalDecomp_eq_of_mem_sphere hR hg hz]
    exact norm_shiftedChiFourXi_le_growthMajorant_of_mem_sphere hR.le hz
  have hgPos : 0 < ‖g z‖ := norm_pos_iff.mpr <| by
    intro hgz
    apply hfree z hz
    have heq := shiftedCanonicalDecomp_eq_of_mem_sphere hR hg hz
    rw [hgz, mul_zero] at heq
    simpa using heq
  exact sub_nonneg.mpr (Real.log_le_log hgPos hgNorm)

lemma canonicalRemainderGap_zero_le
    {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R) :
    canonicalRemainderGap R g 0 ≤
      Real.log (shiftedGrowthMajorant R) - Real.log ‖shiftedChiFourXi 0‖ := by
  unfold canonicalRemainderGap
  have hcentralPos : 0 < ‖shiftedChiFourXi 0‖ :=
    norm_pos_iff.mpr shiftedChiFourXi_zero_ne
  have hlog := Real.log_le_log hcentralPos
    (norm_shiftedChiFourXi_zero_le_canonicalDecomp hR hg)
  linarith

private lemma abs_poisson_pair_sub_two_le
    {a c : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hc : |c| ≤ 1) :
    |(1 - a ^ 2) / (1 - 2 * a * c + a ^ 2) +
        (1 - a ^ 2) / (1 + 2 * a * c + a ^ 2) - 2| ≤
      16 * a ^ 2 := by
  have hcBounds := abs_le.mp hc
  have hcSq : c ^ 2 ≤ 1 := by
    have hprod : 0 ≤ (1 - c) * (1 + c) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have haSq : a ^ 2 ≤ 1 / 4 := by
    have hprod : 0 ≤ (1 / 2 - a) * (1 / 2 + a) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hd1 : 0 < 1 - 2 * a * c + a ^ 2 := by
    have hnonneg : 0 ≤ 2 * a * (1 - c) :=
      mul_nonneg (mul_nonneg (by norm_num) ha0) (by linarith)
    have hhalf : (1 / 2 : ℝ) ≤ 1 - a := by linarith
    nlinarith [sq_nonneg (1 - a)]
  have hd2 : 0 < 1 + 2 * a * c + a ^ 2 := by
    have hnonneg : 0 ≤ 2 * a * (1 + c) :=
      mul_nonneg (mul_nonneg (by norm_num) ha0) (by linarith)
    have hhalf : (1 / 2 : ℝ) ≤ 1 - a := by linarith
    nlinarith [sq_nonneg (1 - a)]
  let D := (1 + a ^ 2) ^ 2 - 4 * a ^ 2 * c ^ 2
  have hD : 1 / 2 ≤ D := by
    have hDbase : (1 - a ^ 2) ^ 2 ≤ D := by
      have hterm : 0 ≤ 4 * a ^ 2 * (1 - c ^ 2) :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg a))
          (sub_nonneg.mpr hcSq)
      dsimp [D]
      nlinarith
    have hbase : 1 / 2 ≤ (1 - a ^ 2) ^ 2 := by
      have hlin : 3 / 4 ≤ 1 - a ^ 2 := by linarith
      nlinarith [sq_nonneg ((1 - a ^ 2) - 3 / 4)]
    exact hbase.trans hDbase
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hDfactor :
      D = (1 - 2 * a * c + a ^ 2) * (1 + 2 * a * c + a ^ 2) := by
    dsimp [D]
    ring
  have heq :
      (1 - a ^ 2) / (1 - 2 * a * c + a ^ 2) +
          (1 - a ^ 2) / (1 + 2 * a * c + a ^ 2) - 2 =
        4 * a ^ 2 * (2 * c ^ 2 - 1 - a ^ 2) / D := by
    rw [hDfactor]
    let d1 := 1 - 2 * a * c + a ^ 2
    let d2 := 1 + 2 * a * c + a ^ 2
    change (1 - a ^ 2) / d1 + (1 - a ^ 2) / d2 - 2 =
      4 * a ^ 2 * (2 * c ^ 2 - 1 - a ^ 2) / (d1 * d2)
    have hd1' : d1 ≠ 0 := hd1.ne'
    have hd2' : d2 ≠ 0 := hd2.ne'
    field_simp [hd1', hd2']
    ring
  rw [heq, abs_div, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg a),
    abs_of_pos hDpos]
  have hfour : |(4 : ℝ)| = 4 := abs_of_nonneg (by norm_num)
  rw [hfour]
  apply (div_le_iff₀ hDpos).2
  have hfactor : |2 * c ^ 2 - 1 - a ^ 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg c, sq_nonneg a]
  calc
    4 * a ^ 2 * |2 * c ^ 2 - 1 - a ^ 2| ≤ 8 * a ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg a)
        (sub_nonneg.mpr hfactor)]
    _ ≤ 16 * a ^ 2 * D := by
      nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hD)]

private lemma abs_poissonKernel_pair_sub_two_le
    {R r : ℝ} {z : ℂ} (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / 2)
    (hz : z ∈ sphere (0 : ℂ) R) :
    |poissonKernel 0 (r : ℂ) z + poissonKernel 0 (-r : ℂ) z - 2| ≤
      16 * (r / R) ^ 2 := by
  have hzNorm : ‖z‖ = R := by
    simpa [mem_sphere_iff_norm] using hz
  have hrLt : r < R := by linarith
  let a := r / R
  let c := z.re / R
  have ha0 : 0 ≤ a := div_nonneg hr0 hR.le
  have ha : a ≤ 1 / 2 := by
    dsimp [a]
    exact (div_le_iff₀ hR).2 (by linarith)
  have hzRe : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans_eq hzNorm
  have hc : |c| ≤ 1 := by
    dsimp [c]
    rw [abs_div, abs_of_pos hR]
    exact (div_le_one hR).2 hzRe
  have hzNePos : z ≠ (r : ℂ) := by
    intro h
    have hnorm := congrArg norm h
    rw [hzNorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at hnorm
    linarith
  have hzNeNeg : z ≠ (-r : ℂ) := by
    intro h
    have hnorm := congrArg norm h
    have hRr : R = r := by
      simpa [hzNorm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr0] using hnorm
    linarith
  have hminus :
      ‖z - (r : ℂ)‖ ^ 2 = R ^ 2 - 2 * r * z.re + r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, hzNorm]
    ring
  have hplus :
      ‖z - (-r : ℂ)‖ ^ 2 = R ^ 2 + 2 * r * z.re + r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, hzNorm]
    ring
  have hplus' :
      ‖z + (r : ℂ)‖ ^ 2 = R ^ 2 + 2 * r * z.re + r ^ 2 := by
    simpa only [sub_neg_eq_add] using hplus
  have hminusPos : 0 < R ^ 2 - 2 * r * z.re + r ^ 2 := by
    rw [← hminus]
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzNePos))
  have hplusPos : 0 < R ^ 2 + 2 * r * z.re + r ^ 2 := by
    rw [← hplus]
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzNeNeg))
  have hpPos :
      poissonKernel 0 (r : ℂ) z =
        (1 - a ^ 2) / (1 - 2 * a * c + a ^ 2) := by
    rw [poissonKernel_def]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hminus, hzNorm]
    dsimp [a, c]
    field_simp [hR.ne', hminusPos.ne']
  have hpNeg :
      poissonKernel 0 (-r : ℂ) z =
        (1 - a ^ 2) / (1 + 2 * a * c + a ^ 2) := by
    rw [poissonKernel_def]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hplus', hzNorm]
    dsimp [a, c]
    field_simp [hR.ne', hplusPos.ne']
  rw [hpPos, hpNeg]
  exact abs_poisson_pair_sub_two_le ha0 ha hc

private lemma continuousOn_poissonKernel_sphere
    {R : ℝ} {w : ℂ} (_hR : 0 < R) (hw : ‖w‖ < R) :
    ContinuousOn (poissonKernel 0 w) (sphere (0 : ℂ) R) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  unfold poissonKernel
  have hzw : z - w ≠ 0 := by
    intro h
    have hEq : z = w := sub_eq_zero.mp h
    subst z
    have hwNorm : ‖w‖ = R := by simpa [mem_sphere_iff_norm] using hz
    linarith
  have hden : z - 0 - (w - 0) ≠ 0 := by simpa using hzw
  fun_prop (disch := exact pow_ne_zero _ (norm_ne_zero_iff.mpr hden))

private lemma harmonic_pair_lower
    {R r : ℝ} {q : ℂ → ℝ} (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / 2)
    (hq : HarmonicOnNhd q (closedBall (0 : ℂ) R))
    (hqBoundary : ∀ z ∈ sphere (0 : ℂ) R, 0 ≤ q z) :
    (2 - 16 * (r / R) ^ 2) * q 0 ≤ q (r : ℂ) + q (-r : ℂ) := by
  have hrLt : r < R := by linarith
  have hrNorm : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hnegNorm : ‖(-r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hrBall : (r : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_iff_norm, sub_zero, hrNorm]
    exact hrLt
  have hnegBall : (-r : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_iff_norm, sub_zero, hnegNorm]
    exact hrLt
  have hqCont : ContinuousOn q (sphere (0 : ℂ) R) :=
    hq.continuousOn.mono sphere_subset_closedBall
  have hkPosCont := continuousOn_poissonKernel_sphere (R := R) (w := (r : ℂ)) hR (by
    rw [hrNorm]
    exact hrLt)
  have hkNegCont := continuousOn_poissonKernel_sphere (R := R) (w := (-r : ℂ)) hR (by
    rw [hnegNorm]
    exact hrLt)
  have hleftCont : ContinuousOn
      (fun z ↦ (2 - 16 * (r / R) ^ 2) * q z) (sphere (0 : ℂ) R) :=
    continuousOn_const.mul hqCont
  have hleftInt : CircleIntegrable
      (fun z ↦ (2 - 16 * (r / R) ^ 2) * q z) 0 R := by
    have hleftContAbs : ContinuousOn
        (fun z ↦ (2 - 16 * (r / R) ^ 2) * q z) (sphere (0 : ℂ) |R|) := by
      simpa [abs_of_pos hR] using hleftCont
    exact hleftContAbs.circleIntegrable'
  have hposInt : CircleIntegrable (poissonKernel 0 (r : ℂ) • q) 0 R := by
    have hcont : ContinuousOn (poissonKernel 0 (r : ℂ) * q)
        (sphere (0 : ℂ) |R|) := by
      simpa [abs_of_pos hR] using hkPosCont.mul hqCont
    simpa [Pi.smul_apply', smul_eq_mul] using hcont.circleIntegrable'
  have hnegInt : CircleIntegrable (poissonKernel 0 (-r : ℂ) • q) 0 R := by
    have hcont : ContinuousOn (poissonKernel 0 (-r : ℂ) * q)
        (sphere (0 : ℂ) |R|) := by
      simpa [abs_of_pos hR] using hkNegCont.mul hqCont
    simpa [Pi.smul_apply', smul_eq_mul] using hcont.circleIntegrable'
  have hrightInt : CircleIntegrable
      ((poissonKernel 0 (r : ℂ) + poissonKernel 0 (-r : ℂ)) * q) 0 R := by
    have hcont : ContinuousOn
        ((poissonKernel 0 (r : ℂ) + poissonKernel 0 (-r : ℂ)) * q)
        (sphere (0 : ℂ) |R|) := by
      simpa only [abs_of_pos hR] using (hkPosCont.add hkNegCont).mul hqCont
    exact hcont.circleIntegrable'
  have havg := circleAverage_mono hleftInt hrightInt (fun z hz ↦ ?_)
  · have hmean : circleAverage q 0 R = q 0 := by
      have hqAbs : HarmonicOnNhd q (closedBall (0 : ℂ) |R|) := by
        simpa [abs_of_pos hR] using hq
      exact HarmonicOnNhd.circleAverage_eq hqAbs
    have hpos := hq.circleAverage_poissonKernel_smul hrBall
    have hneg := hq.circleAverage_poissonKernel_smul hnegBall
    have hleftEq :
        circleAverage (fun z ↦ (2 - 16 * (r / R) ^ 2) * q z) 0 R =
          (2 - 16 * (r / R) ^ 2) * q 0 := by
      change circleAverage (fun z ↦ (2 - 16 * (r / R) ^ 2) • q z) 0 R = _
      rw [circleAverage_fun_smul, hmean]
      rfl
    rw [hleftEq] at havg
    have hrightEq :
        circleAverage
            ((poissonKernel 0 (r : ℂ) + poissonKernel 0 (-r : ℂ)) * q) 0 R =
          q (r : ℂ) + q (-r : ℂ) := by
      rw [show ((poissonKernel 0 (r : ℂ) + poissonKernel 0 (-r : ℂ)) * q) =
          (poissonKernel 0 (r : ℂ) • q) +
            (poissonKernel 0 (-r : ℂ) • q) by
        funext z
        simp [Pi.add_apply, Pi.mul_apply, smul_eq_mul, add_mul]]
      rw [circleAverage_add hposInt hnegInt, hpos, hneg]
    rw [hrightEq] at havg
    simpa [smul_eq_mul] using havg
  · have hkernel := abs_poissonKernel_pair_sub_two_le hR hr0 hr (by
        simpa [abs_of_pos hR] using hz)
    have hlower := (abs_le.mp hkernel).1
    have hqz := hqBoundary z (by simpa [abs_of_pos hR] using hz)
    change (2 - 16 * (r / R) ^ 2) * q z ≤
      (poissonKernel 0 (r : ℂ) z + poissonKernel 0 (-r : ℂ) z) * q z
    exact mul_le_mul_of_nonneg_right (by linarith) hqz

lemma canonicalRemainder_log_pair_le
    {R r : ℝ} {g : ℂ → ℂ} (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / 2)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R)
    (hfree : ∀ z ∈ sphere (0 : ℂ) R, shiftedChiFourXi z ≠ 0) :
    Real.log ‖g (r : ℂ)‖ + Real.log ‖g (-r : ℂ)‖ - 2 * Real.log ‖g 0‖ ≤
      16 * (r / R) ^ 2 *
        (Real.log (shiftedGrowthMajorant R) - Real.log ‖shiftedChiFourXi 0‖) := by
  have hpair := harmonic_pair_lower hR hr0 hr
    (harmonicOnNhd_canonicalRemainderGap hR hg hfree)
    (fun z hz ↦ canonicalRemainderGap_nonneg_of_mem_sphere hR hg hfree hz)
  have hraw :
      Real.log ‖g (r : ℂ)‖ + Real.log ‖g (-r : ℂ)‖ -
          2 * Real.log ‖g 0‖ ≤
        16 * (r / R) ^ 2 * canonicalRemainderGap R g 0 := by
    unfold canonicalRemainderGap at hpair ⊢
    ring_nf at hpair ⊢
    nlinarith
  apply hraw.trans
  exact mul_le_mul_of_nonneg_left (canonicalRemainderGap_zero_le hR hg)
    (mul_nonneg (by norm_num) (sq_nonneg _))

private lemma log_one_add_sub_log_one_sub_le
    {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    Real.log (1 + x) - Real.log (1 - y) ≤ x + 2 * y := by
  have hlogAdd : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
    linarith
  have hden : 0 < 1 - y := by linarith
  have hinv : (1 - y)⁻¹ - 1 ≤ 2 * y := by
    have heq : (1 - y)⁻¹ - 1 = y / (1 - y) := by
      field_simp [hden.ne']
      ring
    rw [heq]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
  rw [Real.log_inv] at hlogInv
  linarith

private lemma canonical_ratio_le
    {R a r d N : ℝ} (hR : 0 < R) (ha : 0 < a) (hr : 0 ≤ r)
    (hd : d ≤ a + r) (hd0 : 0 < d)
    (hgap : 0 < R ^ 2 - a * r) (hN : R ^ 2 - a * r ≤ N) :
    (R / a) / (N / (R * d)) ≤
      (1 + r / a) / (1 - a * r / R ^ 2) := by
  have hNpos : 0 < N := lt_of_lt_of_le hgap hN
  have hRd : 0 < R * d := mul_pos hR hd0
  have hden : 0 < 1 - a * r / R ^ 2 := by
    rw [sub_pos, div_lt_one (sq_pos_of_pos hR)]
    linarith
  rw [div_le_div_iff₀ (div_pos hNpos hRd) hden]
  field_simp [hR.ne', ha.ne', hNpos.ne', hd0.ne']
  have h₁ := mul_le_mul_of_nonneg_right hd hgap.le
  have h₂ := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ a + r)
  nlinarith

private lemma canonicalFactor_log_zero_sub_le
    {R r : ℝ} {u z : ℂ} (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / 2)
    (huBall : u ∈ ball (0 : ℂ) R) (hu0 : u ≠ 0)
    (hzNorm : ‖z‖ = r) (hzu : z ≠ u) :
    Real.log ‖Complex.canonicalFactor R u 0‖ -
        Real.log ‖Complex.canonicalFactor R u z‖ ≤
      3 * r / ‖u‖ := by
  have huNorm : ‖u‖ < R := by simpa [mem_ball_iff_norm] using huBall
  have huPos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hzClosed : z ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, hzNorm]
    linarith
  have hcanonZ : Complex.canonicalFactor R u z ≠ 0 :=
    Complex.canonicalFactor_ne_zero huBall hzClosed hzu
  have hcanonZero : Complex.canonicalFactor R u 0 ≠ 0 :=
    Complex.canonicalFactor_ne_zero huBall (mem_closedBall_self hR.le) (Ne.symm hu0)
  let d := ‖z - u‖
  let N := ‖((R : ℂ) ^ 2) - (starRingEnd ℂ) u * z‖
  have hd0 : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hzu)
  have hd : d ≤ ‖u‖ + r := by
    dsimp [d]
    calc
      ‖z - u‖ ≤ ‖z‖ + ‖u‖ := norm_sub_le _ _
      _ = ‖u‖ + r := by rw [hzNorm]; ring
  have hgap : 0 < R ^ 2 - ‖u‖ * r := by
    have har : ‖u‖ * r ≤ R * (R / 2) :=
      mul_le_mul huNorm.le hr hr0 hR.le
    nlinarith [sq_pos_of_pos hR]
  have hN : R ^ 2 - ‖u‖ * r ≤ N := by
    have hrev := norm_sub_norm_le ((R : ℂ) ^ 2) ((starRingEnd ℂ) u * z)
    dsimp [N]
    simpa [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      norm_mul, hzNorm] using hrev
  have hcanonZNorm :
      ‖Complex.canonicalFactor R u z‖ = N / (R * d) := by
    rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rfl
  have hratio :
      ‖Complex.canonicalFactor R u 0‖ / ‖Complex.canonicalFactor R u z‖ ≤
        (1 + r / ‖u‖) / (1 - ‖u‖ * r / R ^ 2) := by
    rw [norm_canonicalFactor_zero hR hu0, hcanonZNorm]
    exact canonical_ratio_le hR huPos hr0 hd hd0 hgap hN
  have hx : 0 ≤ r / ‖u‖ := div_nonneg hr0 huPos.le
  have hy0 : 0 ≤ ‖u‖ * r / R ^ 2 := by positivity
  have hy : ‖u‖ * r / R ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).2
    nlinarith [mul_le_mul huNorm.le hr hr0 hR.le]
  have hratioPos :
      0 < ‖Complex.canonicalFactor R u 0‖ /
        ‖Complex.canonicalFactor R u z‖ :=
    div_pos (norm_pos_iff.mpr hcanonZero) (norm_pos_iff.mpr hcanonZ)
  have htargetDenPos : 0 < 1 - ‖u‖ * r / R ^ 2 := by linarith
  have hlogRatio := Real.log_le_log hratioPos hratio
  rw [Real.log_div (norm_ne_zero_iff.mpr hcanonZero)
    (norm_ne_zero_iff.mpr hcanonZ)] at hlogRatio
  rw [Real.log_div (by positivity : 1 + r / ‖u‖ ≠ 0)
    htargetDenPos.ne'] at hlogRatio
  have hlogBound := log_one_add_sub_log_one_sub_le hx hy0 hy
  have hyx : ‖u‖ * r / R ^ 2 ≤ r / ‖u‖ := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hR) huPos).2
    have huSq : ‖u‖ ^ 2 ≤ R ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left huSq hr0]
  calc
    Real.log ‖Complex.canonicalFactor R u 0‖ -
        Real.log ‖Complex.canonicalFactor R u z‖ ≤
      Real.log (1 + r / ‖u‖) - Real.log (1 - ‖u‖ * r / R ^ 2) := hlogRatio
    _ ≤ r / ‖u‖ + 2 * (‖u‖ * r / R ^ 2) := hlogBound
    _ ≤ 3 * r / ‖u‖ := by
      rw [show 3 * r / ‖u‖ = 3 * (r / ‖u‖) by ring]
      linarith

private lemma log_norm_shiftedCanonicalProduct_eq_sum
    {R : ℝ} {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R)
    (hfz : shiftedChiFourXi z ≠ 0) :
    Real.log ‖shiftedCanonicalProduct R z‖ =
      ∑ u ∈ (shiftedZeroDivisor_support_finite R).toFinset,
        Real.log ‖Complex.canonicalFactor R u z ^ (-shiftedZeroDivisor R u)‖ := by
  unfold shiftedCanonicalProduct
  rw [finprod_apply (shiftedCanonicalProduct_mulSupport_finite R) z]
  simp only [Pi.pow_apply]
  have hmulSubset : Function.mulSupport
      (fun u ↦ Complex.canonicalFactor R u z ^ (-shiftedZeroDivisor R u)) ⊆
      (shiftedZeroDivisor R).support := by
    intro u hu
    rw [Function.mem_support]
    intro hdiv
    simp [hdiv] at hu
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hmulSubset
    (shiftedZeroDivisor_support_finite R)]
  rw [norm_prod]
  apply Real.log_prod
  intro u hu
  apply norm_ne_zero_iff.mpr
  apply zpow_ne_zero
  have hdiv : shiftedZeroDivisor R u ≠ 0 := by
    exact (shiftedZeroDivisor_support_finite R).mem_toFinset.mp hu
  have huBall : u ∈ ball (0 : ℂ) R :=
    (shiftedZeroDivisor R).supportWithinDomain hdiv
  have hzDiv := shiftedZeroDivisor_eq_zero_of_ne_zero hz hfz
  have hzu : z ≠ u := by
    intro h
    subst u
    exact hdiv hzDiv
  exact Complex.canonicalFactor_ne_zero huBall hz hzu

lemma log_norm_shiftedCanonicalProduct_pair_le_mass
    {R r : ℝ} (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / 2)
    (hf : shiftedChiFourXi (r : ℂ) ≠ 0) :
    Real.log ‖shiftedCanonicalProduct R (r : ℂ)‖ +
        Real.log ‖shiftedCanonicalProduct R (-r : ℂ)‖ -
        2 * Real.log ‖shiftedCanonicalProduct R 0‖ ≤
      6 * r * shiftedZeroMass R := by
  have hrLe : r ≤ R := by linarith
  have hrNorm : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hnegNorm : ‖(-r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hrClosed : (r : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, hrNorm]
    exact hrLe
  have hnegClosed : (-r : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, hnegNorm]
    exact hrLe
  have hzeroClosed : (0 : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  have hfneg : shiftedChiFourXi (-r : ℂ) ≠ 0 := by
    simpa using shiftedChiFourXi_neg (r : ℂ) ▸ hf
  rw [log_norm_shiftedCanonicalProduct_eq_sum hrClosed hf,
    log_norm_shiftedCanonicalProduct_eq_sum hnegClosed hfneg,
    log_norm_shiftedCanonicalProduct_eq_sum hzeroClosed shiftedChiFourXi_zero_ne]
  let S := (shiftedZeroDivisor_support_finite R).toFinset
  have hsum :
      (∑ u ∈ S,
          Real.log ‖Complex.canonicalFactor R u (r : ℂ) ^ (-shiftedZeroDivisor R u)‖) +
          (∑ u ∈ S,
            Real.log ‖Complex.canonicalFactor R u (-r : ℂ) ^ (-shiftedZeroDivisor R u)‖) -
          2 * (∑ u ∈ S,
            Real.log ‖Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)‖) =
        ∑ u ∈ S,
          (Real.log ‖Complex.canonicalFactor R u (r : ℂ) ^ (-shiftedZeroDivisor R u)‖ +
            Real.log ‖Complex.canonicalFactor R u (-r : ℂ) ^ (-shiftedZeroDivisor R u)‖ -
            2 * Real.log ‖Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)‖) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  change
    (∑ u ∈ S,
        Real.log ‖Complex.canonicalFactor R u (r : ℂ) ^ (-shiftedZeroDivisor R u)‖) +
        (∑ u ∈ S,
          Real.log ‖Complex.canonicalFactor R u (-r : ℂ) ^ (-shiftedZeroDivisor R u)‖) -
        2 * (∑ u ∈ S,
          Real.log ‖Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)‖) ≤
      6 * r * shiftedZeroMass R
  rw [hsum]
  have hterm :
      ∀ u ∈ S,
        Real.log ‖Complex.canonicalFactor R u (r : ℂ) ^ (-shiftedZeroDivisor R u)‖ +
            Real.log ‖Complex.canonicalFactor R u (-r : ℂ) ^ (-shiftedZeroDivisor R u)‖ -
            2 * Real.log ‖Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)‖ ≤
          6 * r * ((shiftedZeroDivisor R u : ℝ) / ‖u‖) := by
    intro u hu
    have hdiv : shiftedZeroDivisor R u ≠ 0 := by
      exact (shiftedZeroDivisor_support_finite R).mem_toFinset.mp hu
    have huBall : u ∈ ball (0 : ℂ) R :=
      (shiftedZeroDivisor R).supportWithinDomain hdiv
    have hu0 : u ≠ 0 := by
      intro hu0
      subst u
      exact hdiv (shiftedZeroDivisor_zero hR)
    have hrDiv := shiftedZeroDivisor_eq_zero_of_ne_zero hrClosed hf
    have hnegDiv := shiftedZeroDivisor_eq_zero_of_ne_zero hnegClosed hfneg
    have hru : (r : ℂ) ≠ u := by
      intro h
      subst u
      exact hdiv hrDiv
    have hnegu : (-r : ℂ) ≠ u := by
      intro h
      subst u
      exact hdiv hnegDiv
    have hplus := canonicalFactor_log_zero_sub_le hR hr0 hr huBall hu0 hrNorm hru
    have hminus := canonicalFactor_log_zero_sub_le hR hr0 hr huBall hu0 hnegNorm hnegu
    have hlogs :
        (Real.log ‖Complex.canonicalFactor R u 0‖ -
            Real.log ‖Complex.canonicalFactor R u (r : ℂ)‖) +
          (Real.log ‖Complex.canonicalFactor R u 0‖ -
            Real.log ‖Complex.canonicalFactor R u (-r : ℂ)‖) ≤
          6 * r / ‖u‖ := by
      rw [show 6 * r / ‖u‖ = 3 * r / ‖u‖ + 3 * r / ‖u‖ by ring]
      exact add_le_add hplus hminus
    have hm : 0 ≤ (shiftedZeroDivisor R u : ℝ) := by
      exact_mod_cast shiftedZeroDivisor_nonneg R u
    have hmul := mul_le_mul_of_nonneg_left hlogs hm
    simp only [norm_zpow, Real.log_zpow, Int.cast_neg] at ⊢
    ring_nf at hmul ⊢
    exact hmul
  calc
    ∑ u ∈ S,
        (Real.log ‖Complex.canonicalFactor R u (r : ℂ) ^ (-shiftedZeroDivisor R u)‖ +
          Real.log ‖Complex.canonicalFactor R u (-r : ℂ) ^ (-shiftedZeroDivisor R u)‖ -
          2 * Real.log ‖Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)‖)
        ≤ ∑ u ∈ S, 6 * r * ((shiftedZeroDivisor R u : ℝ) / ‖u‖) := by
          exact Finset.sum_le_sum fun u hu ↦ hterm u hu
    _ = 6 * r * shiftedZeroMass R := by
      rw [← Finset.mul_sum]
      congr 1
      unfold shiftedZeroMass
      apply (finsum_eq_finsetSum_of_support_subset _ ?_).symm
      intro u hu
      have hdiv : shiftedZeroDivisor R u ≠ 0 := by
        intro hdiv
        simp [hdiv] at hu
      exact (shiftedZeroDivisor_support_finite R).mem_toFinset.mpr hdiv

lemma log_norm_shiftedChiFourXi_pair_le
    {R r : ℝ} {g : ℂ → ℂ} (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / 2)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R)
    (hfree : ∀ z ∈ sphere (0 : ℂ) R, shiftedChiFourXi z ≠ 0)
    (hf : shiftedChiFourXi (r : ℂ) ≠ 0) :
    Real.log ‖shiftedChiFourXi (r : ℂ)‖ +
        Real.log ‖shiftedChiFourXi (-r : ℂ)‖ -
        2 * Real.log ‖shiftedChiFourXi 0‖ ≤
      6 * r * shiftedZeroMass R +
        16 * (r / R) ^ 2 *
          (Real.log (shiftedGrowthMajorant R) - Real.log ‖shiftedChiFourXi 0‖) := by
  have hrLe : r ≤ R := by linarith
  have hrNorm : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hnegNorm : ‖(-r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hrClosed : (r : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, hrNorm]
    exact hrLe
  have hnegClosed : (-r : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, hnegNorm]
    exact hrLe
  have hzeroClosed : (0 : ℂ) ∈ closedBall (0 : ℂ) R := mem_closedBall_self hR.le
  have hfneg : shiftedChiFourXi (-r : ℂ) ≠ 0 := by
    intro hneg
    apply hf
    rw [← shiftedChiFourXi_neg (r : ℂ)]
    simpa using hneg
  have hgNe := shiftedCanonicalDecomp_ne_zero_closedBall hR hg hfree
  have hEqPlus := shiftedCanonicalDecomp_eq_of_ne_zero hR hg hrClosed hf
  have hEqNeg := shiftedCanonicalDecomp_eq_of_ne_zero hR hg hnegClosed hfneg
  have hEqZero := shiftedCanonicalDecomp_eq_of_ne_zero hR hg hzeroClosed shiftedChiFourXi_zero_ne
  have hPPlus := shiftedCanonicalProduct_ne_zero_of_ne_zero hrClosed hf
  have hPNeg := shiftedCanonicalProduct_ne_zero_of_ne_zero hnegClosed hfneg
  have hPZero := shiftedCanonicalProduct_ne_zero_of_ne_zero hzeroClosed shiftedChiFourXi_zero_ne
  have hsplitPlus :
      Real.log ‖shiftedChiFourXi (r : ℂ)‖ =
        Real.log ‖shiftedCanonicalProduct R (r : ℂ)‖ + Real.log ‖g (r : ℂ)‖ := by
    rw [hEqPlus, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hPPlus)
        (norm_ne_zero_iff.mpr (hgNe (r : ℂ) hrClosed))]
  have hsplitNeg :
      Real.log ‖shiftedChiFourXi (-r : ℂ)‖ =
        Real.log ‖shiftedCanonicalProduct R (-r : ℂ)‖ + Real.log ‖g (-r : ℂ)‖ := by
    rw [hEqNeg, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hPNeg)
        (norm_ne_zero_iff.mpr (hgNe (-r : ℂ) hnegClosed))]
  have hsplitZero :
      Real.log ‖shiftedChiFourXi 0‖ =
        Real.log ‖shiftedCanonicalProduct R 0‖ + Real.log ‖g 0‖ := by
    rw [hEqZero, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hPZero)
        (norm_ne_zero_iff.mpr (hgNe 0 hzeroClosed))]
  have hP := log_norm_shiftedCanonicalProduct_pair_le_mass hR hr0 hr hf
  have hgLog := canonicalRemainder_log_pair_le hR hr0 hr hg hfree
  have hcombine :
      Real.log ‖shiftedChiFourXi (r : ℂ)‖ +
          Real.log ‖shiftedChiFourXi (-r : ℂ)‖ -
          2 * Real.log ‖shiftedChiFourXi 0‖ =
        (Real.log ‖shiftedCanonicalProduct R (r : ℂ)‖ +
            Real.log ‖shiftedCanonicalProduct R (-r : ℂ)‖ -
            2 * Real.log ‖shiftedCanonicalProduct R 0‖) +
          (Real.log ‖g (r : ℂ)‖ + Real.log ‖g (-r : ℂ)‖ -
            2 * Real.log ‖g 0‖) := by
    rw [hsplitPlus, hsplitNeg, hsplitZero]
    ring
  rw [hcombine]
  exact add_le_add hP hgLog

noncomputable def zeroMassErrorConstant : ℝ :=
  112 * chiFourXiGrowthConstant + 16 * |Real.log ‖shiftedChiFourXi 0‖|

lemma poisson_error_le_zeroMassErrorConstant
    {r R : ℝ} (hr : 1 ≤ r)
    (hR : R ∈ Ioo ((r + 1) ^ 8) ((r + 1) ^ 8 + 1)) :
    16 * (r / R) ^ 2 *
        (Real.log (shiftedGrowthMajorant R) - Real.log ‖shiftedChiFourXi 0‖) ≤
      zeroMassErrorConstant := by
  let t := r + 1
  have ht : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have ht8 : 1 ≤ t ^ 8 := one_le_pow₀ ht
  have ht12 : 1 ≤ t ^ 12 := one_le_pow₀ ht
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity : 0 < t ^ 8) hR.1.le
  have hRone : R + 1 ≤ 3 * t ^ 8 := by
    linarith [hR.2, ht8]
  have hRone0 : 0 ≤ R + 1 := by linarith
  have hsqrtSq : (Real.sqrt (R + 1)) ^ 2 = R + 1 := Real.sq_sqrt hRone0
  have hsqrt : Real.sqrt (R + 1) ≤ 2 * t ^ 4 := by
    have hsqBound : R + 1 ≤ (2 * t ^ 4) ^ 2 := by
      calc
        R + 1 ≤ 3 * t ^ 8 := hRone
        _ ≤ 4 * t ^ 8 := by nlinarith [pow_nonneg ht0 8]
        _ = (2 * t ^ 4) ^ 2 := by ring
    nlinarith [Real.sqrt_nonneg (R + 1), sq_nonneg (2 * t ^ 4 - Real.sqrt (R + 1))]
  have hprod : (R + 1) * Real.sqrt (R + 1) ≤ 6 * t ^ 12 := by
    calc
      (R + 1) * Real.sqrt (R + 1) ≤ (3 * t ^ 8) * (2 * t ^ 4) :=
        mul_le_mul hRone hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = 6 * t ^ 12 := by ring
  have hins : 1 + (R + 1) * Real.sqrt (R + 1) ≤ 7 * t ^ 12 := by
    nlinarith
  have hlogMajorant : Real.log (shiftedGrowthMajorant R) ≤
      7 * chiFourXiGrowthConstant * t ^ 12 := by
    rw [shiftedGrowthMajorant, Real.log_exp]
    have := mul_le_mul_of_nonneg_left hins chiFourXiGrowthConstant_nonneg
    nlinarith
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hrLeT : r ≤ t := by dsimp [t]; linarith
  have hrSq : r ^ 2 ≤ t ^ 2 := by nlinarith
  have ht14le16 : t ^ 14 ≤ t ^ 16 := by
    calc
      t ^ 14 ≤ t ^ 14 * t ^ 2 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht)
      _ = t ^ 16 := by ring
  have hR8 : t ^ 8 ≤ R := hR.1.le
  have hR16 : t ^ 16 ≤ R ^ 2 := by nlinarith
  have hnum : r ^ 2 * t ^ 12 ≤ R ^ 2 := by
    calc
      r ^ 2 * t ^ 12 ≤ t ^ 2 * t ^ 12 :=
        mul_le_mul_of_nonneg_right hrSq (by positivity)
      _ = t ^ 14 := by ring
      _ ≤ t ^ 16 := ht14le16
      _ ≤ R ^ 2 := hR16
  have hfrac : (r / R) ^ 2 * t ^ 12 ≤ 1 := by
    calc
      (r / R) ^ 2 * t ^ 12 = (r ^ 2 * t ^ 12) / R ^ 2 := by
        field_simp [hRpos.ne']
      _ ≤ 1 := (div_le_one (sq_pos_of_pos hRpos)).2 hnum
  have hratio : (r / R) ^ 2 ≤ 1 := by
    have hdiv0 : 0 ≤ r / R := div_nonneg hr0 hRpos.le
    have htLe8 : t ≤ t ^ 8 := by
      simpa using (pow_le_pow_right₀ ht (by norm_num : 1 ≤ 8))
    have hdiv1 : r / R ≤ 1 :=
      (div_le_one hRpos).2 (hrLeT.trans (htLe8.trans hR8))
    nlinarith [sq_nonneg (r / R)]
  have hcentralGap :
      Real.log (shiftedGrowthMajorant R) - Real.log ‖shiftedChiFourXi 0‖ ≤
        7 * chiFourXiGrowthConstant * t ^ 12 +
          |Real.log ‖shiftedChiFourXi 0‖| := by
    linarith [neg_le_abs (Real.log ‖shiftedChiFourXi 0‖)]
  have heps : 0 ≤ 16 * (r / R) ^ 2 := by positivity
  apply (mul_le_mul_of_nonneg_left hcentralGap heps).trans
  unfold zeroMassErrorConstant
  calc
    16 * (r / R) ^ 2 *
          (7 * chiFourXiGrowthConstant * t ^ 12 +
            |Real.log ‖shiftedChiFourXi 0‖|) =
        112 * chiFourXiGrowthConstant * ((r / R) ^ 2 * t ^ 12) +
          16 * (r / R) ^ 2 * |Real.log ‖shiftedChiFourXi 0‖| := by ring
    _ ≤ 112 * chiFourXiGrowthConstant * 1 +
          16 * 1 * |Real.log ‖shiftedChiFourXi 0‖| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hfrac
          (mul_nonneg (by norm_num) chiFourXiGrowthConstant_nonneg))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio (by norm_num)) (abs_nonneg _))
    _ = 112 * chiFourXiGrowthConstant + 16 * |Real.log ‖shiftedChiFourXi 0‖| := by ring

lemma norm_shiftedChiFourXi_le_exp_of_zeroMass_bound
    {B r : ℝ} (hr : 1 ≤ r) (hmass : ∀ R, shiftedZeroMass R ≤ B)
    (hf : shiftedChiFourXi (r : ℂ) ≠ 0) :
    ‖shiftedChiFourXi (r : ℂ)‖ ≤
      Real.exp (3 * r * B + zeroMassErrorConstant / 2 +
        Real.log ‖shiftedChiFourXi 0‖) := by
  obtain ⟨R, hRint, hfree⟩ :=
    exists_shiftedChiFourXi_zero_free_radius ((r + 1) ^ 8)
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity : 0 < (r + 1) ^ 8) hRint.1.le
  have ht : 1 ≤ r + 1 := by linarith
  have ht2le8 : (r + 1) ^ 2 ≤ (r + 1) ^ 8 :=
    pow_le_pow_right₀ ht (by norm_num)
  have h2r : 2 * r ≤ (r + 1) ^ 2 := by nlinarith
  have hrHalf : r ≤ R / 2 := by
    have : 2 * r ≤ R := (h2r.trans ht2le8).trans hRint.1.le
    linarith
  obtain ⟨g, hg⟩ := exists_shiftedCanonicalDecomp R
  have hpair := log_norm_shiftedChiFourXi_pair_le hRpos (by linarith) hrHalf hg hfree hf
  have heven : shiftedChiFourXi (-r : ℂ) = shiftedChiFourXi (r : ℂ) := by
    simpa using shiftedChiFourXi_neg (r : ℂ)
  rw [heven] at hpair
  have hmassTerm : 6 * r * shiftedZeroMass R ≤ 6 * r * B :=
    mul_le_mul_of_nonneg_left (hmass R) (by positivity)
  have herror := poisson_error_le_zeroMassErrorConstant hr hRint
  have hlog : Real.log ‖shiftedChiFourXi (r : ℂ)‖ ≤
      3 * r * B + zeroMassErrorConstant / 2 +
        Real.log ‖shiftedChiFourXi 0‖ := by
    linarith
  have hnormPos : 0 < ‖shiftedChiFourXi (r : ℂ)‖ := norm_pos_iff.mpr hf
  rw [← Real.exp_log hnormPos]
  exact Real.exp_le_exp.mpr hlog

theorem shiftedZeroMass_unbounded (B : ℝ) :
    ∃ R : ℝ, B < shiftedZeroMass R := by
  by_contra hbounded
  push Not at hbounded
  let rate : ℝ := 6 * B
  let offset : ℝ := 3 / 2 * B + zeroMassErrorConstant / 2 +
    Real.log ‖shiftedChiFourXi 0‖
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp offset)
  obtain ⟨C, hC⟩ := exists_nat_gt (Real.exp rate)
  have hevent := Nat.eventually_mul_pow_lt_factorial_sub (4 * A) C 0
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let n := max N 1
  have hnN : N ≤ n := le_max_left N 1
  have hnOne : 1 ≤ n := le_max_right N 1
  have hfacNat : 4 * A * C ^ n < (n - 0).factorial := hN n hnN
  have hfac : (4 : ℝ) * A * C ^ n < (n.factorial : ℝ) := by
    exact_mod_cast (by simpa using hfacNat)
  have hlower := norm_shiftedChiFourXi_odd_lower n hnOne
  have hfacPos : 0 < (n.factorial : ℝ) / 4 := by positivity
  have hnormPos : 0 < ‖shiftedChiFourXi (shiftedOddPoint n)‖ :=
    hfacPos.trans_le hlower
  have hf : shiftedChiFourXi (shiftedOddPoint n) ≠ 0 :=
    norm_pos_iff.mp hnormPos
  have hrOne : 1 ≤ shiftedOddPoint n := by
    unfold shiftedOddPoint
    have hnCast : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have huRaw := norm_shiftedChiFourXi_le_exp_of_zeroMass_bound hrOne hbounded hf
  have hu : ‖shiftedChiFourXi (shiftedOddPoint n)‖ ≤
      Real.exp (rate * n + offset) := by
    convert huRaw using 1
    congr 1
    dsimp [rate, offset, shiftedOddPoint]
    ring
  have hexpOffset : Real.exp offset ≤ (A : ℝ) := hA.le
  have hexpRate : Real.exp rate ≤ (C : ℝ) := hC.le
  have hexpUpper : Real.exp (rate * n + offset) ≤ (A : ℝ) * C ^ n := by
    rw [Real.exp_add, mul_comm rate (n : ℝ), Real.exp_nat_mul]
    rw [mul_comm (Real.exp rate ^ n) (Real.exp offset)]
    exact mul_le_mul hexpOffset (pow_le_pow_left₀ (Real.exp_nonneg _) hexpRate n)
      (by positivity) (by positivity)
  have hACstrict : (A : ℝ) * C ^ n < (n.factorial : ℝ) / 4 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfac
  have hstrict : ‖shiftedChiFourXi (shiftedOddPoint n)‖ <
      (n.factorial : ℝ) / 4 :=
    hu.trans_lt (hexpUpper.trans_lt hACstrict)
  exact (not_lt_of_ge hlower) hstrict

end Submission.ZeroMass
