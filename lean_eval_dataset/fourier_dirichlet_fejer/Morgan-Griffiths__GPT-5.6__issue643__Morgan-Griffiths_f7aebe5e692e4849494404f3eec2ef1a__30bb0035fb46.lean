import Mathlib

namespace Submission

namespace LeanEval
namespace Analysis

/-!
# Pointwise and Cesàro convergence of Fourier series

§46 of Oliver Knill's *Some Fundamental Theorems in Mathematics*.

* **Dirichlet's pointwise convergence theorem** (main): for a `C¹` 2π-periodic
  complex function `f`, the symmetric Fourier partial sums
  `S_N(f)(x) = ∑_{n = -N}^{N} f̂_n e^{inx}` converge to `f(x)` at every `x ∈ ℝ`.
* **Fejér's theorem** (additional): for a merely *continuous* 2π-periodic `f`,
  the Cesàro means `σ_N(f) = (S_0 + ⋯ + S_N)/(N+1)` of the partial sums converge
  to `f` uniformly on `ℝ`.

mathlib has the circle, the Fourier characters, `fourierCoeffOn`, the `L²`
Fourier series, and uniform convergence under `ℓ¹`-summability
(`hasSum_fourier_series_of_summable`). It has neither the Dirichlet kernel nor
the statement that `C¹` forces pointwise convergence of the symmetric partial
sums — the `C¹` bound `|f̂_n| ≤ C/n` is not `ℓ¹`-summable, so the summable case
does not apply — and it has no Fejér kernel, Cesàro means, or Fejér theorem. The
symmetric partial-sum order `Finset.Icc (-N) N` is essential, since the Fourier
series of a `C¹` function need not converge absolutely.
-/

open Filter Topology

/-- The symmetric Fourier partial sum of `f : ℝ → ℂ` on the period `[0, 2π]`:
`S_N(f)(x) = ∑_{n = -N}^{N} f̂_n · e^{inx}`, with `f̂_n = fourierCoeffOn _ f n`. -/
noncomputable def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    fourierCoeffOn Real.two_pi_pos f n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))

/-- The Cesàro mean of the first `N + 1` Fourier partial sums:
`σ_N(f)(x) = (S_0(f)(x) + S_1(f)(x) + ⋯ + S_N(f)(x)) / (N + 1)`. -/
noncomputable def fourierCesaroMean (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ k ∈ Finset.range (N + 1), fourierPartialSum f k x) / (N + 1 : ℂ)





end Analysis
end LeanEval

namespace LeanEval
namespace Analysis

/-!
# Pointwise and Cesàro convergence of Fourier series

§46 of Oliver Knill's *Some Fundamental Theorems in Mathematics*.

* **Dirichlet's pointwise convergence theorem** (main): for a `C¹` 2π-periodic
  complex function `f`, the symmetric Fourier partial sums
  `S_N(f)(x) = ∑_{n = -N}^{N} f̂_n e^{inx}` converge to `f(x)` at every `x ∈ ℝ`.
* **Fejér's theorem** (additional): for a merely *continuous* 2π-periodic `f`,
  the Cesàro means `σ_N(f) = (S_0 + ⋯ + S_N)/(N+1)` of the partial sums converge
  to `f` uniformly on `ℝ`.

mathlib has the circle, the Fourier characters, `fourierCoeffOn`, the `L²`
Fourier series, and uniform convergence under `ℓ¹`-summability
(`hasSum_fourier_series_of_summable`). It has neither the Dirichlet kernel nor
the statement that `C¹` forces pointwise convergence of the symmetric partial
sums — the `C¹` bound `|f̂_n| ≤ C/n` is not `ℓ¹`-summable, so the summable case
does not apply — and it has no Fejér kernel, Cesàro means, or Fejér theorem. The
symmetric partial-sum order `Finset.Icc (-N) N` is essential, since the Fourier
series of a `C¹` function need not converge absolutely.
-/

open Filter Topology





/-- **Dirichlet's pointwise convergence theorem** (§46). For every `C¹`
2π-periodic complex function `f`, the symmetric Fourier partial sums `S_N(f)(x)`
converge to `f(x)` at every point `x ∈ ℝ`. -/
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/


-- auxiliary ℓ1 estimate
private lemma summable_fourierCoeffOn_C1
    {f : ℝ → ℂ} (hfper : Function.Periodic f (2 * Real.pi)) (hf : ContDiff ℝ 1 f) :
    Summable (fourierCoeffOn Real.two_pi_pos f) := by
  let f' : ℝ → ℂ := fun x => deriv f x
  have hfcont : Continuous f := hf.continuous
  have hdcont : Continuous f' := hf.continuous_deriv (by norm_num)
  have hmem : MeasureTheory.MemLp f' 2
        (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi))) := by
    have hbound0 := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) (2 * Real.pi))).bddAbove_image
      (hdcont.continuousOn.norm)
    rcases (bddAbove_def.mp hbound0) with ⟨C, hC⟩
    refine MeasureTheory.MemLp.of_bound (hdcont.aestronglyMeasurable.restrict) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
      (measurableSet_Ioc)] with y hy
    exact hC _ ⟨y, ⟨le_of_lt hy.1, hy.2⟩, rfl⟩
  have hsquares : Summable (fun n : ℤ => ‖fourierCoeffOn Real.two_pi_pos f' n‖ ^ (2:ℕ)) :=
    (hasSum_sq_fourierCoeffOn Real.two_pi_pos hmem).summable
  have hsquares' : Summable (fun n : ℤ => ‖fourierCoeffOn Real.two_pi_pos f' n‖ ^ (2:ℝ)) := by
    simpa [Real.rpow_two] using hsquares
  have hinv : Summable (fun n : ℤ => (|(n:ℝ)|⁻¹) ^ (2:ℝ)) := by
    have hh := Real.summable_abs_int_rpow (b := (2:ℝ)) (by norm_num)
    refine hh.congr ?_
    intro n
    rw [Real.rpow_neg (abs_nonneg _)]
    simp
  have hprod : Summable (fun n : ℤ => ‖fourierCoeffOn Real.two_pi_pos f' n‖ * |(n:ℝ)|⁻¹) := by
    exact Real.summable_mul_of_Lp_Lq_of_nonneg
      (show (2:ℝ).HolderConjugate 2 by rw [Real.holderConjugate_iff]; norm_num)
      (fun n => norm_nonneg _) (fun n => inv_nonneg.mpr (abs_nonneg _)) hsquares' hinv
  have hcoeff (n : ℤ) (hn : n ≠ 0) :
      fourierCoeffOn Real.two_pi_pos f n =
        (1 / (Complex.I * (n:ℂ))) * fourierCoeffOn Real.two_pi_pos f' n := by
    have he := fourierCoeffOn_of_hasDerivAt (f := f) (f' := f')
      Real.two_pi_pos hn (fun y hy => (hf.differentiable (by norm_num : (1:WithTop ℕ∞) ≠ 0) y).hasDerivAt)
      (hdcont.intervalIntegrable 0 (2 * Real.pi))
    rw [he]
    have hper : f (2 * Real.pi) = f 0 := by
      simpa using (hfper 0)
    -- cancel the common length of the interval
    rw [hper, sub_self]
    simp
    field_simp
  -- replace the zero coefficient by zero; all the others form the Hölder product
  have hnorm0 : Summable (fun n : ℤ => if n = 0 then 0 else ‖fourierCoeffOn Real.two_pi_pos f n‖) := by
    apply hprod.congr
    intro n
    split_ifs with hn
    · subst n; simp
    · rw [hcoeff n hn, norm_mul]
      rw [norm_div, norm_one, norm_mul, Complex.norm_I, one_mul]
      simp
      ac_rfl
  have hnorm : Summable (fun n : ℤ => ‖fourierCoeffOn Real.two_pi_pos f n‖) := by
    have hsingle : Summable (fun n : ℤ => if n = 0 then ‖fourierCoeffOn Real.two_pi_pos f 0‖ else 0) :=
      (hasSum_ite_eq (0:ℤ) ‖fourierCoeffOn Real.two_pi_pos f 0‖).summable
    refine (hsingle.add hnorm0).congr ?_
    intro n
    by_cases hn : n = 0
    · subst n; simp
    · simp [hn]
  exact (summable_norm_iff.mp hnorm)

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/
theorem dirichlet_pointwise
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hC1 : ContDiff ℝ 1 f)
    (x : ℝ) :
    Tendsto (fun N : ℕ => fourierPartialSum f N x) atTop (𝓝 (f x)) :=
/-ResultProofBegin-/by
  classical
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨Real.two_pi_pos⟩
  have hfcont : Continuous f := _hC1.continuous
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨AddCircle.liftIco (2 * Real.pi) 0 f,
      AddCircle.liftIco_zero_continuous
        (by simpa using (_hperiod 0).symm) hfcont.continuousOn⟩
  have hF (y : ℝ) : F (y : AddCircle (2 * Real.pi)) = f y := by
    have heq : (F : AddCircle (2 * Real.pi) → ℂ) = _hperiod.lift := by
      apply AddCircle.Ico_ext (2 * Real.pi) 0
      intro z hz
      change AddCircle.liftIco (2 * Real.pi) 0 f (z : AddCircle (2 * Real.pi)) = _hperiod.lift (z : AddCircle (2 * Real.pi))
      have hz' : z ∈ Set.Ico (0:ℝ) (2 * Real.pi) := by simpa using hz
      rw [AddCircle.liftIco_zero_coe_apply hz']
      rw [Function.Periodic.lift_coe]
    change (F : AddCircle (2 * Real.pi) → ℂ) (y : AddCircle (2 * Real.pi)) = _
    rw [heq, Function.Periodic.lift_coe]
  have hcoef (n : ℤ) : fourierCoeff (F : AddCircle (2 * Real.pi) → ℂ) n =
      fourierCoeffOn Real.two_pi_pos f n := by
    change fourierCoeff (AddCircle.liftIco (2 * Real.pi) 0 f) n = _
    simpa using (fourierCoeff_liftIco_eq (T := 2 * Real.pi) (a := (0:ℝ)) f n)
  have hsumF : Summable (fourierCoeff (F : AddCircle (2 * Real.pi) → ℂ)) := by
    have h := summable_fourierCoeffOn_C1 _hperiod _hC1
    exact h.congr (fun n => (hcoef n).symm)
  have hp := has_pointwise_sum_fourier_series_of_summable (f := F) hsumF (x : AddCircle (2 * Real.pi))
  have hexp (n : ℤ) : (fourier (T := 2 * Real.pi) n) (x : AddCircle (2 * Real.pi)) =
      Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    have hp0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    push_cast
    ring
  have hp' : HasSum
      (fun n : ℤ => fourierCoeffOn Real.two_pi_pos f n *
        Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) (f x) := by
    convert hp using 1
    · ext n
      rw [hcoef n, hexp n]
      simp [smul_eq_mul]
    · exact (hF x).symm
  have hcof : Tendsto (fun N : ℕ => Finset.Icc (-(N:ℤ)) (N:ℤ)) atTop
      (Filter.atTop : Filter (Finset ℤ)) := by
    apply Filter.tendsto_atTop.2
    intro t
    let M : ℕ := ∑ i ∈ t, i.natAbs
    filter_upwards [Filter.eventually_ge_atTop M] with n hn
    intro i hi
    have ha : i.natAbs ≤ M := Finset.single_le_sum (fun j hj => Nat.zero_le _) hi
    have ha' : (i.natAbs : ℤ) ≤ (M:ℤ) := by exact_mod_cast ha
    have hn' : (M:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
    have hab : |i| ≤ (n:ℤ) := by simpa [Int.natCast_natAbs] using ha'.trans hn'
    exact Finset.mem_Icc.mpr (abs_le.mp hab)
  exact hp'.comp hcof
/-ResultProofEnd-/
/-ResultEnd-/


-- Circle versions of the partial sum operators.  Keeping these as continuous maps
-- is useful since the sup norm is the uniform norm.
private noncomputable def circlePartial {T : ℝ} [Fact (0 < T)]
    (F : C(AddCircle T, ℂ)) (N : ℕ) : C(AddCircle T, ℂ) :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff (F : AddCircle T → ℂ) n • fourier n

private noncomputable def circleCesaro {T : ℝ} [Fact (0 < T)]
    (F : C(AddCircle T, ℂ)) (N : ℕ) : C(AddCircle T, ℂ) :=
  ((N + 1 : ℕ) : ℂ)⁻¹ •
    (∑ k ∈ Finset.range (N+1), circlePartial F k)

private lemma continuous_integrable_circle {T : ℝ} [Fact (0 < T)]
    (F : C(AddCircle T, ℂ)) :
    MeasureTheory.Integrable (F : AddCircle T → ℂ) AddCircle.haarAddCircle := by
  have h := ContinuousOn.integrableOn_compact
      (μ := (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle T)))
      (f := (F : AddCircle T → ℂ))
      (isCompact_univ : IsCompact (Set.univ : Set (AddCircle T)))
      (F.continuous.continuousOn)
  exact (MeasureTheory.integrableOn_univ.mp (by simpa using h))

private lemma fourierCoeff_circle_add {T : ℝ} [Fact (0 < T)]
    (F G : C(AddCircle T, ℂ)) (n : ℤ) :
    fourierCoeff (fun x => (F + G) x) n =
      fourierCoeff (F : AddCircle T → ℂ) n + fourierCoeff (G : AddCircle T → ℂ) n := by
  have h := fourierCoeff.add (continuous_integrable_circle F)
      (continuous_integrable_circle G)
  have hn := congrFun h n
  -- `f + g` in the lemma is pointwise addition
  change fourierCoeff ((F : AddCircle T → ℂ) + (G : AddCircle T → ℂ)) n = _
  exact hn

private lemma fourierCoeff_circle_smul {T : ℝ} [Fact (0 < T)]
    (c : ℂ) (F : C(AddCircle T, ℂ)) (n : ℤ) :
    fourierCoeff (fun x => (c • F) x) n = c * fourierCoeff (F : AddCircle T → ℂ) n := by
  change fourierCoeff (c • (F : AddCircle T → ℂ)) n = _
  simpa [smul_eq_mul] using
    (fourierCoeff.const_smul (T:=T) (F : AddCircle T → ℂ) c n)

private lemma circlePartial_add {T : ℝ} [Fact (0 < T)]
    (F G : C(AddCircle T, ℂ)) (N : ℕ) :
    circlePartial (F + G) N = circlePartial F N + circlePartial G N := by
  classical
  simp only [circlePartial]
  -- distribute the sum and scalar coefficients
  simp_rw [fourierCoeff_circle_add (T:=T) F G]
  simp_rw [add_smul]
  -- sums over a `Finset` distribute
  simp only [Finset.sum_add_distrib]


private lemma circlePartial_smul {T : ℝ} [Fact (0 < T)]
    (c : ℂ) (F : C(AddCircle T, ℂ)) (N : ℕ) :
    circlePartial (c • F) N = c • circlePartial F N := by
  classical
  simp only [circlePartial]
  simp_rw [fourierCoeff_circle_smul (T:=T) c F]
  -- pull the common scalar through the finite sum
  simp [mul_smul, Finset.smul_sum]

private lemma circlePartial_zero {T : ℝ} [Fact (0 < T)] (N : ℕ) :
    circlePartial (0 : C(AddCircle T, ℂ)) N = 0 := by
  classical
  -- follows from homogeneity with scalar zero
  simpa using (circlePartial_smul (T:=T) (0:ℂ)
    (0 : C(AddCircle T, ℂ)) N)

-- Evaluation of a Fourier partial sum on one monomial.  Once the cut-off
-- dominates the index only that coefficient remains.
private lemma circlePartial_fourier_eventually {T : ℝ} [Fact (0 < T)]
    (j : ℤ) :
    ∀ᶠ N : ℕ in atTop, circlePartial (fourier (T:=T) j) N = fourier (T:=T) j := by
  classical
  filter_upwards [Filter.eventually_ge_atTop j.natAbs] with N hN
  unfold circlePartial
  have hj : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    have h1 : |j| ≤ (N : ℤ) := by
      have h' : (j.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
      simpa [Int.natCast_natAbs] using h'
    exact Finset.mem_Icc.mpr (abs_le.mp h1)
  -- all other coefficients of `fourier j` vanish
  have hc := fourierCoeff_fourier (T:=T) j
  classical
  -- replace each coefficient by a `Pi.single`
  simp_rw [hc]
  -- the finite sum with a single term
  -- `Finset.sum_eq_single j`
  simp [Pi.single_apply, hj]

-- On the algebraic span of the Fourier monomials the symmetric partial sums
-- are *eventually exactly* the polynomial.
private lemma circlePartial_eventually_eq {T : ℝ} [Fact (0 < T)]
    {F : C(AddCircle T, ℂ)}
    (hF : F ∈ Submodule.span ℂ (Set.range (fourier (T:=T)))) :
    ∀ᶠ N : ℕ in atTop, circlePartial F N = F := by
  classical
  -- span induction, synchronising the two cut-offs with the filter
  refine Submodule.span_induction (s := (Set.range (fourier (T:=T))))
    (p := fun F _ => ∀ᶠ N : ℕ in atTop, circlePartial F N = F) ?_ ?_ ?_ ?_ hF
  · intro u hu
    rcases hu with ⟨j, rfl⟩
    exact circlePartial_fourier_eventually (T:=T) j
  · -- zero
    filter_upwards [] with N
    exact circlePartial_zero (T:=T) N
  · intro u v hu hv eu ev
    filter_upwards [eu, ev] with N hNu hNv
    rw [circlePartial_add]
    simp [hNu, hNv]
  · intro c u hu eu
    filter_upwards [eu] with N hNu
    rw [circlePartial_smul]
    simp [hNu]


-- Consequently the Cesaro means converge in the sup norm on every finite
-- trigonometric polynomial.  This is just the elementary Cesaro lemma in a
-- normed vector space; no estimates on Fourier coefficients are involved.
private lemma circleCesaro_tendsto_of_span {T : ℝ} [Fact (0 < T)]
    {F : C(AddCircle T, ℂ)}
    (hF : F ∈ Submodule.span ℂ (Set.range (fourier (T:=T)))) :
    Tendsto (fun N : ℕ => circleCesaro F N) atTop (𝓝 F) := by
  classical
  have hev : ∀ᶠ n : ℕ in atTop, circlePartial F n = F :=
    circlePartial_eventually_eq (T:=T) hF
  have ht : Tendsto (fun n : ℕ => circlePartial F n) atTop (𝓝 F) := by
    -- an eventually constant sequence converges
    have hconst : Tendsto (fun _n : ℕ => F) atTop (𝓝 F) := tendsto_const_nhds
    exact (tendsto_congr' hev).2 hconst
  have hc := Filter.Tendsto.cesaro_smul ht
  -- Replace the real scalar in the general Cesaro lemma by the equal
  -- complex scalar.  They give the same action on our continuous maps.
  have hsc (n : ℕ) (G : C(AddCircle T, ℂ)) :
      ((n : ℝ)⁻¹) • G = (((n : ℕ) : ℂ)⁻¹) • G := by
    ext x
    change ((n : ℝ)⁻¹) • (G x) = (((n : ℕ) : ℂ)⁻¹) • (G x)
    rw [Complex.real_smul]
    simp only [smul_eq_mul]
    have hn : (((n : ℝ)⁻¹ : ℝ) : ℂ) = ((n : ℕ) : ℂ)⁻¹ := by
      simp
    rw [hn]
  have hc' : Tendsto
      (fun n : ℕ => (((n : ℕ) : ℂ)⁻¹) •
        ∑ i ∈ Finset.range n, circlePartial F i) atTop (𝓝 F) := by
    -- pointwise equality of the two Cesaro sequences
    convert hc using 1
    funext n
    exact (hsc n _).symm
  -- and our definition uses `N+1`, never the empty mean
  have hshift := hc'.comp (Filter.tendsto_add_atTop_nat 1)
  -- just unfold the definition after the harmless shift
  simpa [circleCesaro, Function.comp_def, Nat.cast_add, Nat.cast_one] using hshift


private local instance twoPiFact : Fact (0 < (2 * Real.pi : ℝ)) := ⟨Real.two_pi_pos⟩

-- Relate the circle formula to the original real-periodic definitions.
private noncomputable def liftPeriodic
    (f : ℝ → ℂ) (_hperiod : Function.Periodic f (2 * Real.pi))
    (_hcont : Continuous f) : C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨AddCircle.liftIco (2 * Real.pi) 0 f,
    AddCircle.liftIco_zero_continuous
      (by simpa using (_hperiod 0).symm) _hcont.continuousOn⟩

private lemma liftPeriodic_apply
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi))
    (_hcont : Continuous f) (y : ℝ) :
    (liftPeriodic f _hperiod _hcont) (y : AddCircle (2 * Real.pi)) = f y := by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨Real.two_pi_pos⟩
  let F := liftPeriodic f _hperiod _hcont
  have heq : (F : AddCircle (2 * Real.pi) → ℂ) = _hperiod.lift := by
    apply AddCircle.Ico_ext (2 * Real.pi) 0
    intro z hz
    dsimp [F, liftPeriodic]
    change AddCircle.liftIco (2 * Real.pi) 0 f (z : AddCircle (2 * Real.pi)) =
      _hperiod.lift (z : AddCircle (2 * Real.pi))
    have hz' : z ∈ Set.Ico (0:ℝ) (2 * Real.pi) := by simpa using hz
    rw [AddCircle.liftIco_zero_coe_apply hz']
    rw [Function.Periodic.lift_coe]
  change (F : AddCircle (2 * Real.pi) → ℂ) (y : AddCircle (2 * Real.pi)) = _
  rw [heq, Function.Periodic.lift_coe]

private lemma liftPeriodic_coeff
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi))
    (_hcont : Continuous f) (n : ℤ) :
    fourierCoeff ((liftPeriodic f _hperiod _hcont) :
      AddCircle (2 * Real.pi) → ℂ) n = fourierCoeffOn Real.two_pi_pos f n := by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨Real.two_pi_pos⟩
  change fourierCoeff (AddCircle.liftIco (2 * Real.pi) 0 f) n = _
  simpa using
    (fourierCoeff_liftIco_eq (T := 2 * Real.pi) (a := (0:ℝ)) f n)

private lemma fourier_two_pi_eval (n : ℤ) (x : ℝ) :
    (fourier (T := 2 * Real.pi) n) (x : AddCircle (2 * Real.pi)) =
       Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  have hp0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  push_cast
  ring

private lemma circleCesaro_apply_lift
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi))
    (_hcont : Continuous f) (N : ℕ) (x : ℝ) :
    fourierCesaroMean f N x =
      circleCesaro (liftPeriodic f _hperiod _hcont) N
        (x : AddCircle (2 * Real.pi)) := by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨Real.two_pi_pos⟩
  classical
  -- both sides are the same finite sums
  unfold fourierCesaroMean circleCesaro fourierPartialSum circlePartial
  change _ = (((N + 1 : ℕ) : ℂ)⁻¹ •
        (∑ k ∈ Finset.range (N+1),
          ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ),
            fourierCoeff ((liftPeriodic f _hperiod _hcont) :
              AddCircle (2 * Real.pi) → ℂ) n • fourier (T:=2*Real.pi) n))
          (x : AddCircle (2 * Real.pi))
  simp only [ContinuousMap.smul_apply, Finset.sum_apply]
  simp_rw [ContinuousMap.sum_apply]
  -- At this point all the summands are just complex numbers.
  simp_rw [liftPeriodic_coeff _hperiod _hcont]
  simp_rw [ContinuousMap.smul_apply]
  simp_rw [fourier_two_pi_eval]
  -- the remaining scalar is the reciprocal of `N+1`
  simp [smul_eq_mul, div_eq_inv_mul]

-- The advertised finite-polynomial special case in the original (real)
-- formulation.  All analytic difficulties are absent here: on a polynomial
-- the partial sums stabilize, and the usual Cesaro lemma gives uniform
-- convergence.
private lemma fejer_of_span
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi))
    (_hcont : Continuous f)
    (hspan :
      let _ : Fact (0 < (2 * Real.pi : ℝ)) := ⟨Real.two_pi_pos⟩
      liftPeriodic f _hperiod _hcont ∈
        Submodule.span ℂ (Set.range (fourier (T:=2*Real.pi)))) :
    TendstoUniformly (fun N : ℕ => fourierCesaroMean f N) f atTop := by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨Real.two_pi_pos⟩
  classical
  have hspan' : liftPeriodic f _hperiod _hcont ∈
        Submodule.span ℂ (Set.range (fourier (T:=2*Real.pi))) := hspan
  have ht := circleCesaro_tendsto_of_span (T:=2*Real.pi) hspan'
  -- Sup-norm convergence of continuous maps gives pointwise estimates
  -- independent of the point, hence uniform convergence after projecting
  -- `ℝ` to the circle.
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hev : ∀ᶠ N : ℕ in atTop,
      dist (circleCesaro (liftPeriodic f _hperiod _hcont) N)
        (liftPeriodic f _hperiod _hcont) < ε :=
    (Metric.tendsto_nhds.mp ht) ε hε
  filter_upwards [hev] with N hN
  intro x
  have hpoint := ContinuousMap.dist_apply_le_dist
    (α := AddCircle (2 * Real.pi)) (β := ℂ)
    (f := (liftPeriodic f _hperiod _hcont))
    (g := circleCesaro (liftPeriodic f _hperiod _hcont) N)
    (x : AddCircle (2 * Real.pi))
  -- commute the two distances; `hN` was written in the other orientation
  have hlt : dist
        ((liftPeriodic f _hperiod _hcont) (x : AddCircle (2 * Real.pi)))
        ((circleCesaro (liftPeriodic f _hperiod _hcont) N)
          (x : AddCircle (2 * Real.pi))) < ε :=
    hpoint.trans_lt (by simpa [dist_comm] using hN)
  simpa [liftPeriodic_apply _hperiod _hcont,
    circleCesaro_apply_lift _hperiod _hcont] using hlt


-- The combinatorics behind the positive Fejer kernel. Each frequency `n`
-- occurs `N+1-|n|` times; a convenient precise bijection pairs `(i,j)`
-- with `(max i j, i-j)`.
private lemma cesaro_index_sum (N : ℕ) (a : ℤ → ℂ) :
    (∑ k ∈ Finset.range (N+1), ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), a n) =
    (∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), a ((i:ℤ)-(j:ℤ))) := by
  classical
  let s : Finset (ℕ × ℕ) := (Finset.range (N+1)).product (Finset.range (N+1))
  let t : Finset (Sigma fun _ : ℕ => ℤ) :=
    (Finset.range (N+1)).sigma (fun k => Finset.Icc (-(k:ℤ)) (k:ℤ))
  let φ : ℕ × ℕ → Sigma fun _ : ℕ => ℤ := fun p =>
    ⟨max p.1 p.2, (p.1:ℤ) - (p.2:ℤ)⟩
  let ψ : (Sigma fun _ : ℕ => ℤ) → ℕ × ℕ := fun q =>
    if h : 0 ≤ q.2 then (q.1, q.1 - q.2.toNat)
    else (q.1 - (-q.2).toNat, q.1)
  have hφ (p : ℕ × ℕ) (hp : p ∈ s) : φ p ∈ t := by
    rcases p with ⟨i,j⟩
    simp [s, t, φ, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    constructor
    · omega
    · omega
  have hψ (q : Sigma fun _ : ℕ => ℤ) (hq : q ∈ t) : ψ q ∈ s := by
    rcases q with ⟨k,n⟩
    simp [t, Finset.mem_range, Finset.mem_Icc] at hq
    rcases hq with ⟨hk, hn1, hn2⟩
    by_cases h : 0 ≤ n
    · have hh : n.toNat ≤ k := by have hx := Int.toNat_of_nonneg h; omega
      simp [ψ, h, s, Finset.mem_range]
      constructor <;> omega
    · have hneg : 0 ≤ -n := by omega
      have hh : (-n).toNat ≤ k := by have hx := Int.toNat_of_nonneg hneg; omega
      simp [ψ, h, s, Finset.mem_range]
      constructor <;> omega
  have hleft (p : ℕ × ℕ) (hp : p ∈ s) : ψ (φ p) = p := by
    rcases p with ⟨i,j⟩
    dsimp [φ, ψ]
    split_ifs with h
    · -- i-j >=0 so j≤i
      have hij : j ≤ i := by push_cast at h; omega
      have hm : max i j = i := max_eq_left hij
      simp [hm]
      have hx : ((i:ℤ)-(j:ℤ)).toNat = i-j := by omega
      omega
    · have hji : i < j := by push_cast at h; omega
      have hm : max i j = j := max_eq_right (by omega)
      simp [hm]
      have hx : (-((i:ℤ)-(j:ℤ))).toNat = j-i := by omega
      omega
  have hright (q : Sigma fun _ : ℕ => ℤ) (hq : q ∈ t) : φ (ψ q) = q := by
    rcases q with ⟨k,n⟩
    simp [t, Finset.mem_range, Finset.mem_Icc] at hq
    rcases hq with ⟨hk, hn1, hn2⟩
    dsimp [ψ]
    split_ifs with h
    · have hx := Int.toNat_of_nonneg h
      have hh : n.toNat ≤ k := by omega
      have hm : max k (k - n.toNat) = k := max_eq_left (by omega)
      dsimp [φ]
      apply Sigma.ext hm
      -- subsingleton cast
      subst_vars
      simp
      omega
    · have hneg : 0 ≤ -n := by omega
      have hx := Int.toNat_of_nonneg hneg
      have hh : (-n).toNat ≤ k := by omega
      have hm : max (k - (-n).toNat) k = k := max_eq_right (by omega)
      dsimp [φ]
      apply Sigma.ext hm
      subst_vars
      simp
      omega
  have hsumeq : (∑ p ∈ s, a ((φ p).2)) = ∑ q ∈ t, a q.2 := by
    classical
    refine Finset.sum_bij' (s:=s) (t:=t) (f:= fun p => a ((φ p).2))
      (g:= fun q => a q.2)
      (fun p _ => φ p) (fun q _ => ψ q)
      hφ hψ hleft hright ?_
    intro p hp; rfl
  dsimp [s, t] at hsumeq
  rw [Finset.sum_product] at hsumeq
  rw [Finset.sum_sigma] at hsumeq
  -- unfold maps
  simpa [s, t, φ] using hsumeq.symm

private lemma fejer_kernel_sum {T:ℝ} [Fact (0<T)] (N:ℕ) (z:AddCircle T) :
    (((‖∑ i ∈ Finset.range (N+1), (fourier (T:=T) (i:ℤ)) z‖^2 /
          (N+1:ℝ) : ℝ)) : ℂ) =
      (((N+1:ℕ):ℂ)⁻¹) *
        (∑ k ∈ Finset.range (N+1), ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
           (fourier (T:=T) n) z) := by
  classical
  rw [cesaro_index_sum N (fun n => (fourier (T:=T) n) z)]
  rw [Complex.sq_norm]
  rw [Complex.ofReal_div]
  rw [← Complex.mul_conj]
  simp only [map_sum]
  rw [Finset.sum_mul_sum]
  -- products are Fourier differences
  simp_rw [← fourier_neg]
  simp_rw [← fourier_add]
  rw [div_eq_inv_mul]
  congr 1
  simp


private lemma fourier_char_sub {T:ℝ} [Fact (0<T)] (n:ℤ) (x t:AddCircle T) :
    (fourier (T:=T) n) (x-t) = (fourier n) x * (fourier (-n)) t := by
  induction x using QuotientAddGroup.induction_on
  induction t using QuotientAddGroup.induction_on
  rw [← QuotientAddGroup.mk_sub, fourier_coe_apply, fourier_coe_apply,
    fourier_coe_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma fourier_integral_translate {T:ℝ} [Fact (0<T)]
    (F:C(AddCircle T,ℂ)) (n:ℤ) (x:AddCircle T) :
    (∫ z : AddCircle T, (fourier n) z * F (x-z) ∂AddCircle.haarAddCircle) =
      (fourierCoeff (F:AddCircle T→ℂ) n) * (fourier n) x := by
  have hchar (t:AddCircle T) :
    (fourier (T:=T) n) (x-t) = (fourier n) x * (fourier (-n)) t :=
      fourier_char_sub n x t
  calc
   _ = ∫ t : AddCircle T, (fourier n) (x-t) * F t ∂AddCircle.haarAddCircle := by
     convert MeasureTheory.integral_sub_left_eq_self
       (fun t : AddCircle T => (fourier n) (x-t) * F t)
       AddCircle.haarAddCircle x using 1
     simp
   _ = _ := by
     simp_rw [hchar]
     rw [fourierCoeff]
     simp_rw [smul_eq_mul]
     rw [← MeasureTheory.integral_mul_const]
     congr 1
     funext t
     ring


-- Integrals of the characters on the normalised circle.  This little fact is
-- the only orthogonality needed for the Fejer kernel: every non-constant
-- character has mean zero.
private lemma integral_fourier_character {T : ℝ} [Fact (0 < T)] (n : ℤ) :
    (∫ z : AddCircle T, (fourier (T:=T) n) z ∂AddCircle.haarAddCircle)
      = if n = 0 then (1 : ℂ) else 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [fourier_zero]
  · have h :=
        MeasureTheory.integral_eq_zero_of_add_right_eq_neg
          (μ := (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle T)))
          (fourier_add_half_inv_index hn (Fact.out : 0 < T))
    -- The lemma above is phrased for an arbitrary Haar-invariant measure; the
    -- continuous character here satisfies precisely its translation condition.
    simpa [hn] using h

-- A convenient real-valued Fejer kernel on the circle.  Writing it as a
-- squared norm makes positivity immediate; `fejer_kernel_sum` changes it
-- into the finite Fourier sum when a complex integrand is wanted.
private noncomputable def realFejerKernel {T : ℝ} [Fact (0 < T)]
    (N : ℕ) (z : AddCircle T) : ℝ :=
  ‖∑ i ∈ Finset.range (N+1), (fourier (T:=T) (i:ℤ)) z‖^2 / (N+1:ℝ)

private lemma realFejerKernel_nonneg {T : ℝ} [Fact (0 < T)]
    (N : ℕ) (z : AddCircle T) : 0 ≤ realFejerKernel (T:=T) N z := by
  unfold realFejerKernel
  exact div_nonneg (sq_nonneg _) (by positivity)

private lemma realFejerKernel_continuous {T : ℝ} [Fact (0 < T)]
    (N : ℕ) : Continuous (realFejerKernel (T:=T) N) := by
  unfold realFejerKernel
  fun_prop

private lemma realFejerKernel_integrable {T : ℝ} [Fact (0 < T)]
    (N : ℕ) :
    MeasureTheory.Integrable (realFejerKernel (T:=T) N) AddCircle.haarAddCircle := by
  have h := ContinuousOn.integrableOn_compact
      (μ := (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle T)))
      (f := realFejerKernel (T:=T) N)
      (isCompact_univ : IsCompact (Set.univ : Set (AddCircle T)))
      ((realFejerKernel_continuous (T:=T) N).continuousOn)
  exact MeasureTheory.integrableOn_univ.mp (by simpa using h)

-- The normalisation implicit in `haarAddCircle` is the probability
-- normalisation.  Computing the zero coefficient of the finite Fourier sum
-- therefore shows that the Fejer kernel has mass exactly one.
private lemma realFejerKernel_integral_one {T : ℝ} [Fact (0 < T)] (N : ℕ) :
    (∫ z : AddCircle T, realFejerKernel (T:=T) N z ∂AddCircle.haarAddCircle)
       = (1 : ℝ) := by
  classical
  let c : ℂ := (((N+1:ℕ):ℂ)⁻¹)
  have hpoint (z : AddCircle T) :
      ((realFejerKernel (T:=T) N z : ℝ) : ℂ) =
        c * (∑ k ∈ Finset.range (N+1),
               ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), (fourier (T:=T) n) z) := by
    simpa [realFejerKernel, c] using (fejer_kernel_sum (T:=T) N z)
  have hchar (n : ℤ) :
      MeasureTheory.Integrable (fun z : AddCircle T => (fourier (T:=T) n) z)
        AddCircle.haarAddCircle :=
    continuous_integrable_circle (T:=T) (fourier (T:=T) n)
  have hsumchar (k : ℕ) :
      MeasureTheory.Integrable
        (fun z : AddCircle T => ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
            (fourier (T:=T) n) z) AddCircle.haarAddCircle := by
    have hc : Continuous
        (fun z : AddCircle T => ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
            (fourier (T:=T) n) z) := by fun_prop
    have hh := ContinuousOn.integrableOn_compact
      (μ := (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle T)))
      (f := fun z : AddCircle T => ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
            (fourier (T:=T) n) z)
      (isCompact_univ : IsCompact (Set.univ : Set (AddCircle T))) hc.continuousOn
    exact MeasureTheory.integrableOn_univ.mp (by simpa using hh)
  have hsumint :
      (∫ z : AddCircle T, ((realFejerKernel (T:=T) N z : ℝ) : ℂ)
          ∂AddCircle.haarAddCircle)
        = c *
          (∑ k ∈ Finset.range (N+1),
            ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
              (∫ z : AddCircle T, (fourier (T:=T) n) z
                   ∂AddCircle.haarAddCircle)) := by
    calc
      _ = ∫ z : AddCircle T,
          c * (∑ k ∈ Finset.range (N+1),
               ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), (fourier (T:=T) n) z)
            ∂AddCircle.haarAddCircle := by
                apply MeasureTheory.integral_congr_ae
                exact Filter.Eventually.of_forall hpoint
      _ = c * (∫ z : AddCircle T,
              (∑ k ∈ Finset.range (N+1),
               ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), (fourier (T:=T) n) z)
                ∂AddCircle.haarAddCircle) := by
            rw [MeasureTheory.integral_const_mul]
      _ = _ := by
        congr 1
        rw [MeasureTheory.integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro k hk
          rw [MeasureTheory.integral_finset_sum]
          intro n hn
          exact hchar n
        · intro k hk
          exact hsumchar k
  have hzero (k : ℕ) : (0 : ℤ) ∈ Finset.Icc (-(k:ℤ)) (k:ℤ) := by
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have htot :
      (∑ k ∈ Finset.range (N+1),
            ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
              (∫ z : AddCircle T, (fourier (T:=T) n) z
                   ∂AddCircle.haarAddCircle)) = (N+1 : ℕ) := by
    -- only the zero character survives the integral
    simp_rw [integral_fourier_character (T:=T)]
    classical
    -- each interval contains zero exactly once
    simp [hzero]
  have hcomplex :
      (∫ z : AddCircle T, ((realFejerKernel (T:=T) N z : ℝ) : ℂ)
          ∂AddCircle.haarAddCircle) = (1 : ℂ) := by
    rw [hsumint, htot]
    dsimp [c]
    simp only [Nat.cast_add, Nat.cast_one]
    have hn : ( (N : ℂ) + 1) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero N)
    exact inv_mul_cancel₀ hn
  -- take real parts. `reCLM` commutes with the Bochner integral.
  have hkint : MeasureTheory.Integrable
      (fun z : AddCircle T => ((realFejerKernel (T:=T) N z : ℝ) : ℂ))
      AddCircle.haarAddCircle := by
    -- alternatively this follows by composing with the isometry `ofReal`
    have hc : Continuous
        (fun z : AddCircle T => ((realFejerKernel (T:=T) N z : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (realFejerKernel_continuous (T:=T) N)
    have hh := ContinuousOn.integrableOn_compact
      (μ := (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle T)))
      (f := fun z : AddCircle T => ((realFejerKernel (T:=T) N z : ℝ) : ℂ))
      (isCompact_univ : IsCompact (Set.univ : Set (AddCircle T))) hc.continuousOn
    exact MeasureTheory.integrableOn_univ.mp (by simpa using hh)
  have hre := Complex.reCLM.integral_comp_comm hkint
  -- the left side of `hre` is the desired real integral
  have :
      (∫ z : AddCircle T, realFejerKernel (T:=T) N z
         ∂AddCircle.haarAddCircle)
        =
       (∫ z : AddCircle T, ((realFejerKernel (T:=T) N z : ℝ) : ℂ)
           ∂AddCircle.haarAddCircle).re := by
    simpa using hre
  rw [this, hcomplex]
  norm_num

-- Writing the Cesaro average as convolution with the preceding positive
-- kernel.  Everything here is a finite sum: moving it through the integral
-- only uses continuity on the compact circle.
private lemma circleCesaro_convolution {T : ℝ} [Fact (0 < T)]
    (F : C(AddCircle T, ℂ)) (N : ℕ) (x : AddCircle T) :
    circleCesaro F N x =
      (∫ z : AddCircle T,
         ((realFejerKernel (T:=T) N z : ℝ) : ℂ) * F (x-z)
          ∂AddCircle.haarAddCircle) := by
  classical
  let c : ℂ := (((N+1:ℕ):ℂ)⁻¹)
  have hpoint (z : AddCircle T) :
      ((realFejerKernel (T:=T) N z : ℝ) : ℂ) =
        c * (∑ k ∈ Finset.range (N+1),
               ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), (fourier (T:=T) n) z) := by
    simpa [realFejerKernel, c] using (fejer_kernel_sum (T:=T) N z)
  -- translation invariance of Haar measure is enough here; there is
  -- no limiting operation, just the coefficient of each character.
  have hint (n : ℤ) :
      (∫ z : AddCircle T, (fourier (T:=T) n) z * F (x-z)
          ∂AddCircle.haarAddCircle) =
        (fourierCoeff (F:AddCircle T→ℂ) n) *
          (fourier (T:=T) n) x :=
    fourier_integral_translate (T:=T) F n x
  have hsmall (n : ℤ) : MeasureTheory.Integrable
      (fun z : AddCircle T => (fourier (T:=T) n) z * F (x-z))
        AddCircle.haarAddCircle := by
    have hc : Continuous
        (fun z : AddCircle T => (fourier (T:=T) n) z * F (x-z)) := by
      fun_prop
    have hh := ContinuousOn.integrableOn_compact
      (μ := (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle T)))
      (f := fun z : AddCircle T => (fourier (T:=T) n) z * F (x-z))
      (isCompact_univ : IsCompact (Set.univ : Set (AddCircle T))) hc.continuousOn
    exact MeasureTheory.integrableOn_univ.mp (by simpa using hh)
  have hinner (k : ℕ) : MeasureTheory.Integrable
      (fun z : AddCircle T =>
        ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
          (fourier (T:=T) n) z * F (x-z)) AddCircle.haarAddCircle := by
    have hc : Continuous
      (fun z : AddCircle T =>
        ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
          (fourier (T:=T) n) z * F (x-z)) := by fun_prop
    have hh := ContinuousOn.integrableOn_compact
      (μ := (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle T)))
      (f := fun z : AddCircle T =>
        ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
          (fourier (T:=T) n) z * F (x-z))
      (isCompact_univ : IsCompact (Set.univ : Set (AddCircle T))) hc.continuousOn
    exact MeasureTheory.integrableOn_univ.mp (by simpa using hh)
  -- first expand the convolution; the products distribute over the finite
  -- Fourier sum furnished by `fejer_kernel_sum`.
  calc
    circleCesaro F N x =
       c * (∑ k ∈ Finset.range (N+1),
              ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                (fourierCoeff (F : AddCircle T → ℂ) n) *
                  (fourier (T:=T) n) x) := by
        unfold circleCesaro circlePartial
        simp [c, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
          smul_eq_mul, Finset.mul_sum]
    _ = ∫ z : AddCircle T,
         ((realFejerKernel (T:=T) N z : ℝ) : ℂ) * F (x-z)
          ∂AddCircle.haarAddCircle := by
      symm
      calc
        _ = ∫ z : AddCircle T,
            c * (∑ k ∈ Finset.range (N+1),
              ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                 (fourier (T:=T) n) z * F (x-z))
                ∂AddCircle.haarAddCircle := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with z
            rw [hpoint z]
            -- distribute the common right factor through both sums
            simp only [mul_assoc]
            congr 1
            -- `Finset.sum_mul` twice
            simp [Finset.sum_mul]
        _ = c * (∫ z : AddCircle T,
              (∑ k ∈ Finset.range (N+1),
                ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                   (fourier (T:=T) n) z * F (x-z))
                  ∂AddCircle.haarAddCircle) := by
            rw [MeasureTheory.integral_const_mul]
        _ = _ := by
          congr 1
          rw [MeasureTheory.integral_finset_sum]
          · apply Finset.sum_congr rfl
            intro k hk
            rw [MeasureTheory.integral_finset_sum]
            · apply Finset.sum_congr rfl
              intro n hn
              exact hint n
            · intro n hn
              exact hsmall n
          · intro k hk
            exact hinner k

-- Positivity and unit mass make every Cesaro operator a contraction in the
-- uniform norm.  This uniform (in `N`) bound is what lets us pass from the
-- dense subspace of trigonometric polynomials to all continuous maps.
private lemma circleCesaro_norm_le {T : ℝ} [Fact (0 < T)]
    (F : C(AddCircle T, ℂ)) (N : ℕ) : ‖circleCesaro F N‖ ≤ ‖F‖ := by
  classical
  refine (ContinuousMap.norm_le (circleCesaro F N) (norm_nonneg F)).2 ?_
  intro x
  -- Establish the convolution identity here directly from the finite Fourier
  -- sum.  In particular the norm estimate uses just products of finite
  -- sums of continuous characters commuted with the normalized Haar integral.
  have hconv :
      circleCesaro F N x =
        (∫ z : AddCircle T,
          ((realFejerKernel (T:=T) N z : ℝ) : ℂ) * F (x-z)
            ∂AddCircle.haarAddCircle) := by
    let c : ℂ := (((N+1:ℕ):ℂ)⁻¹)
    have hpoint (z : AddCircle T) :
        ((realFejerKernel (T:=T) N z : ℝ) : ℂ) =
          c * (∑ k ∈ Finset.range (N+1),
               ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), (fourier (T:=T) n) z) := by
      simpa [realFejerKernel, c] using (fejer_kernel_sum (T:=T) N z)
    have hint (n : ℤ) := fourier_integral_translate (T:=T) F n x
    have hsmall (n : ℤ) : MeasureTheory.Integrable
        (fun z : AddCircle T => (fourier (T:=T) n) z * F (x-z))
           AddCircle.haarAddCircle := by
      have hc : Continuous
          (fun z : AddCircle T => (fourier (T:=T) n) z * F (x-z)) := by
        fun_prop
      have hh := ContinuousOn.integrableOn_compact
        (μ := (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle T)))
        (f := fun z : AddCircle T => (fourier (T:=T) n) z * F (x-z))
        (isCompact_univ : IsCompact (Set.univ : Set (AddCircle T)))
          hc.continuousOn
      exact MeasureTheory.integrableOn_univ.mp (by simpa using hh)
    have hinner (k : ℕ) : MeasureTheory.Integrable
        (fun z : AddCircle T =>
          ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
             (fourier (T:=T) n) z * F (x-z))
          AddCircle.haarAddCircle := by
      have hc : Continuous
          (fun z : AddCircle T =>
            ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
               (fourier (T:=T) n) z * F (x-z)) := by fun_prop
      have hh := ContinuousOn.integrableOn_compact
        (μ := (AddCircle.haarAddCircle : MeasureTheory.Measure (AddCircle T)))
        (f := fun z : AddCircle T =>
          ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
             (fourier (T:=T) n) z * F (x-z))
        (isCompact_univ : IsCompact (Set.univ : Set (AddCircle T)))
          hc.continuousOn
      exact MeasureTheory.integrableOn_univ.mp (by simpa using hh)
    calc
      circleCesaro F N x =
         c * (∑ k ∈ Finset.range (N+1),
             ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                (fourierCoeff (F : AddCircle T → ℂ) n) *
                  (fourier (T:=T) n) x) := by
            unfold circleCesaro circlePartial
            simp [c, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
              smul_eq_mul, Finset.mul_sum]
      _ = ∫ z : AddCircle T,
          ((realFejerKernel (T:=T) N z : ℝ) : ℂ) * F (x-z)
             ∂AddCircle.haarAddCircle := by
        symm
        calc
          _ = ∫ z : AddCircle T,
                c * (∑ k ∈ Finset.range (N+1),
                     ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                        (fourier (T:=T) n) z * F (x-z))
                    ∂AddCircle.haarAddCircle := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards [] with z
                rw [hpoint z]
                simp only [mul_assoc]
                congr 1
                simp [Finset.sum_mul]
          _ = c * (∫ z : AddCircle T,
                 (∑ k ∈ Finset.range (N+1),
                    ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                       (fourier (T:=T) n) z * F (x-z))
                    ∂AddCircle.haarAddCircle) := by
                rw [MeasureTheory.integral_const_mul]
          _ = _ := by
                congr 1
                rw [MeasureTheory.integral_finset_sum]
                · apply Finset.sum_congr rfl
                  intro k hk
                  rw [MeasureTheory.integral_finset_sum]
                  · apply Finset.sum_congr rfl
                    intro n hn
                    exact hint n
                  · intro n hn
                    exact hsmall n
                · intro k hk
                  exact hinner k
  rw [hconv]
  have hg : MeasureTheory.Integrable
       (fun z : AddCircle T => realFejerKernel (T:=T) N z * ‖F‖)
       AddCircle.haarAddCircle :=
    (realFejerKernel_integrable (T:=T) N).mul_const _
  calc
    ‖∫ z : AddCircle T,
         ((realFejerKernel (T:=T) N z : ℝ) : ℂ) * F (x-z)
          ∂AddCircle.haarAddCircle‖
       ≤ ∫ z : AddCircle T, realFejerKernel (T:=T) N z * ‖F‖
            ∂AddCircle.haarAddCircle := by
          apply MeasureTheory.norm_integral_le_of_norm_le hg
          filter_upwards [] with z
          calc
            ‖((realFejerKernel (T:=T) N z : ℝ) : ℂ) * F (x-z)‖
                = realFejerKernel (T:=T) N z * ‖F (x-z)‖ := by
                    rw [norm_mul, Complex.norm_real,
                      Real.norm_of_nonneg (realFejerKernel_nonneg (T:=T) N z)]
            _ ≤ realFejerKernel (T:=T) N z * ‖F‖ :=
                  mul_le_mul_of_nonneg_left
                    (ContinuousMap.norm_coe_le_norm F (x-z))
                    (realFejerKernel_nonneg (T:=T) N z)
    _ = ‖F‖ := by
          rw [MeasureTheory.integral_mul_const,
              realFejerKernel_integral_one (T:=T) N, one_mul]

private lemma circleCesaro_add {T : ℝ} [Fact (0 < T)]
    (F G : C(AddCircle T, ℂ)) (N : ℕ) :
    circleCesaro (F+G) N = circleCesaro F N + circleCesaro G N := by
  classical
  unfold circleCesaro
  simp_rw [circlePartial_add]
  simp [Finset.sum_add_distrib, smul_add]

private lemma circleCesaro_smul {T : ℝ} [Fact (0 < T)]
    (c:ℂ) (F : C(AddCircle T, ℂ)) (N : ℕ) :
    circleCesaro (c • F) N = c • circleCesaro F N := by
  classical
  unfold circleCesaro
  simp_rw [circlePartial_smul]
  simp [Finset.smul_sum, smul_smul, mul_comm]

private lemma circleCesaro_sub {T : ℝ} [Fact (0 < T)]
    (F G : C(AddCircle T, ℂ)) (N : ℕ) :
    circleCesaro (F - G) N = circleCesaro F N - circleCesaro G N := by
  -- deriving subtraction from addition and homogeneity avoids a separate
  -- integral computation
  have hneg : circleCesaro (-G) N = - circleCesaro G N := by
    simpa using (circleCesaro_smul (T:=T) (-1:ℂ) G N)
  rw [sub_eq_add_neg, circleCesaro_add, hneg]
  rfl

private lemma circleCesaro_tendsto {T : ℝ} [Fact (0 < T)]
    (F : C(AddCircle T, ℂ)) :
    Tendsto (fun N : ℕ => circleCesaro F N) atTop (𝓝 F) := by
  classical
  apply Metric.tendsto_nhds.2
  intro ε hε
  let S : Submodule ℂ C(AddCircle T, ℂ) :=
    Submodule.span ℂ (Set.range (fourier (T:=T)))
  have htop : F ∈ S.topologicalClosure := by
    change F ∈ (Submodule.span ℂ (Set.range (fourier (T:=T)))).topologicalClosure
    rw [span_fourier_closure_eq_top]
    trivial
  have hmem : F ∈ closure (↑S : Set C(AddCircle T, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact htop
  obtain ⟨P, hPS, hdist⟩ :=
    (Metric.mem_closure_iff.mp hmem) (ε/4) (by linarith)
  have hPspan : P ∈ Submodule.span ℂ (Set.range (fourier (T:=T))) := hPS
  have hp := circleCesaro_tendsto_of_span (T:=T) hPspan
  have hev : ∀ᶠ N : ℕ in atTop, dist (circleCesaro P N) P < ε/2 :=
    (Metric.tendsto_nhds.mp hp) (ε/2) (by linarith)
  filter_upwards [hev] with N hN
  have hfirst : dist (circleCesaro F N) (circleCesaro P N) ≤ dist F P := by
    simpa [dist_eq_norm_sub, ← circleCesaro_sub (T:=T)] using
      (circleCesaro_norm_le (T:=T) (F-P) N)
  have hthird : dist P F < ε/4 := by
    simpa [dist_comm] using hdist
  calc
    dist (circleCesaro F N) F
        ≤ dist (circleCesaro F N) (circleCesaro P N) +
            dist (circleCesaro P N) P + dist P F :=
              dist_triangle4 _ _ _ _
    _ < ε := by
      linarith

/-- **Fejér's theorem** (§46). For every *continuous* 2π-periodic complex
function `f` — without the `C¹` hypothesis of Dirichlet's theorem — the Cesàro
means `σ_N(f)` of the symmetric Fourier partial sums converge to `f` uniformly
on `ℝ`. -/
/-ResultBegin-/
theorem fejer
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hcont : Continuous f) :
    TendstoUniformly (fun N : ℕ => fourierCesaroMean f N) f atTop :=
/-ResultProofBegin-/by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨Real.two_pi_pos⟩
  classical
  -- We record the norm estimate directly; this way the approximation
  -- argument only rests on integrals of *finite* Fourier sums.
  have hnorm (G : C(AddCircle (2*Real.pi), ℂ)) (m : ℕ) :
      ‖circleCesaro G m‖ ≤ ‖G‖ := by
    refine (ContinuousMap.norm_le (circleCesaro G m) (norm_nonneg G)).2 ?_
    intro y
    have hconv :
        circleCesaro G m y =
          (∫ z : AddCircle (2*Real.pi),
             ((realFejerKernel (T:=2*Real.pi) m z : ℝ) : ℂ) *
                G (y - z) ∂AddCircle.haarAddCircle) := by
      let c : ℂ := (((m+1:ℕ):ℂ)⁻¹)
      have hp (z : AddCircle (2*Real.pi)) :
          ((realFejerKernel (T:=2*Real.pi) m z : ℝ) : ℂ) =
            c * (∑ k ∈ Finset.range (m+1),
                  ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                       (fourier (T:=2*Real.pi) n) z) := by
        simpa [realFejerKernel, c] using
          (fejer_kernel_sum (T:=2*Real.pi) m z)
      have hi (n : ℤ) :=
        fourier_integral_translate (T:=2*Real.pi) G n y
      have hterm (n : ℤ) : MeasureTheory.Integrable
          (fun z : AddCircle (2*Real.pi) =>
             (fourier (T:=2*Real.pi) n) z * G (y-z))
            AddCircle.haarAddCircle := by
        have hc : Continuous
            (fun z : AddCircle (2*Real.pi) =>
             (fourier (T:=2*Real.pi) n) z * G (y-z)) := by
          fun_prop
        have hh := ContinuousOn.integrableOn_compact
          (μ := (AddCircle.haarAddCircle :
              MeasureTheory.Measure (AddCircle (2*Real.pi))))
          (f := fun z : AddCircle (2*Real.pi) =>
             (fourier (T:=2*Real.pi) n) z * G (y-z))
          (isCompact_univ :
              IsCompact (Set.univ : Set (AddCircle (2*Real.pi))))
          hc.continuousOn
        exact MeasureTheory.integrableOn_univ.mp (by simpa using hh)
      have hrow (k : ℕ) : MeasureTheory.Integrable
          (fun z : AddCircle (2*Real.pi) =>
             ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
               (fourier (T:=2*Real.pi) n) z * G (y-z))
            AddCircle.haarAddCircle := by
        have hc : Continuous
            (fun z : AddCircle (2*Real.pi) =>
             ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                (fourier (T:=2*Real.pi) n) z * G (y-z)) := by
          fun_prop
        have hh := ContinuousOn.integrableOn_compact
          (μ := (AddCircle.haarAddCircle :
                 MeasureTheory.Measure (AddCircle (2*Real.pi))))
          (f := fun z : AddCircle (2*Real.pi) =>
             ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                (fourier (T:=2*Real.pi) n) z * G (y-z))
          (isCompact_univ :
              IsCompact (Set.univ : Set (AddCircle (2*Real.pi))))
          hc.continuousOn
        exact MeasureTheory.integrableOn_univ.mp (by simpa using hh)
      calc
        circleCesaro G m y =
             c * (∑ k ∈ Finset.range (m+1),
                   ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                       (fourierCoeff (G :
                          AddCircle (2*Real.pi) → ℂ) n) *
                            (fourier (T:=2*Real.pi) n) y) := by
              unfold circleCesaro circlePartial
              simp [c, ContinuousMap.smul_apply,
                ContinuousMap.sum_apply, smul_eq_mul, Finset.mul_sum]
        _ = (∫ z : AddCircle (2*Real.pi),
             ((realFejerKernel (T:=2*Real.pi) m z : ℝ) : ℂ) *
                  G (y-z) ∂AddCircle.haarAddCircle) := by
          symm
          calc
            _ = ∫ z : AddCircle (2*Real.pi),
                  c * (∑ k ∈ Finset.range (m+1),
                      ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                         (fourier (T:=2*Real.pi) n) z * G (y-z))
                      ∂AddCircle.haarAddCircle := by
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards [] with z
                    rw [hp z]
                    simp only [mul_assoc]
                    congr 1
                    simp [Finset.sum_mul]
            _ = c * (∫ z : AddCircle (2*Real.pi),
                    (∑ k ∈ Finset.range (m+1),
                       ∑ n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ),
                           (fourier (T:=2*Real.pi) n) z * G (y-z))
                        ∂AddCircle.haarAddCircle) := by
                    rw [MeasureTheory.integral_const_mul]
            _ = _ := by
                    congr 1
                    rw [MeasureTheory.integral_finset_sum]
                    · apply Finset.sum_congr rfl
                      intro k hk
                      rw [MeasureTheory.integral_finset_sum]
                      · apply Finset.sum_congr rfl
                        intro n hn
                        exact hi n
                      · intro n hn
                        exact hterm n
                    · intro k hk
                      exact hrow k
    rw [hconv]
    have hg : MeasureTheory.Integrable
        (fun z : AddCircle (2*Real.pi) =>
           realFejerKernel (T:=2*Real.pi) m z * ‖G‖)
           AddCircle.haarAddCircle :=
      (realFejerKernel_integrable (T:=2*Real.pi) m).mul_const _
    calc
      ‖∫ z : AddCircle (2*Real.pi),
          ((realFejerKernel (T:=2*Real.pi) m z : ℝ) : ℂ) *
               G (y-z) ∂AddCircle.haarAddCircle‖
        ≤ ∫ z : AddCircle (2*Real.pi),
             realFejerKernel (T:=2*Real.pi) m z * ‖G‖
                ∂AddCircle.haarAddCircle := by
          apply MeasureTheory.norm_integral_le_of_norm_le hg
          filter_upwards [] with z
          calc
            ‖((realFejerKernel (T:=2*Real.pi) m z : ℝ) : ℂ) *
                 G (y-z)‖ =
                 realFejerKernel (T:=2*Real.pi) m z * ‖G (y-z)‖ := by
                   rw [norm_mul, Complex.norm_real,
                     Real.norm_of_nonneg
                       (realFejerKernel_nonneg (T:=2*Real.pi) m z)]
            _ ≤ realFejerKernel (T:=2*Real.pi) m z * ‖G‖ :=
                 mul_le_mul_of_nonneg_left
                   (ContinuousMap.norm_coe_le_norm G (y-z))
                     (realFejerKernel_nonneg (T:=2*Real.pi) m z)
      _ = ‖G‖ := by
            rw [MeasureTheory.integral_mul_const,
                realFejerKernel_integral_one (T:=2*Real.pi) m,
                one_mul]
  have ht :
      Tendsto
        (fun m : ℕ => circleCesaro (liftPeriodic f _hperiod _hcont) m)
           atTop (𝓝 (liftPeriodic f _hperiod _hcont)) := by
    let S : Submodule ℂ C(AddCircle (2*Real.pi), ℂ) :=
      Submodule.span ℂ (Set.range (fourier (T:=2*Real.pi)))
    apply Metric.tendsto_nhds.2
    intro δ hδ
    have htop : (liftPeriodic f _hperiod _hcont) ∈
          S.topologicalClosure := by
      change (liftPeriodic f _hperiod _hcont) ∈
        (Submodule.span ℂ (Set.range (fourier (T:=2*Real.pi)))).topologicalClosure
      rw [span_fourier_closure_eq_top]
      trivial
    have hmem : (liftPeriodic f _hperiod _hcont) ∈
          closure (↑S : Set C(AddCircle (2*Real.pi), ℂ)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact htop
    obtain ⟨P, hPS, hd⟩ :=
      (Metric.mem_closure_iff.mp hmem) (δ/4) (by linarith)
    have hPspan : P ∈
        Submodule.span ℂ (Set.range (fourier (T:=2*Real.pi))) := hPS
    have hp' := circleCesaro_tendsto_of_span
          (T:=2*Real.pi) hPspan
    have ev : ∀ᶠ m : ℕ in atTop,
          dist (circleCesaro P m) P < δ/2 :=
       (Metric.tendsto_nhds.mp hp') (δ/2) (by linarith)
    filter_upwards [ev] with m hm
    have hfirst :
          dist (circleCesaro (liftPeriodic f _hperiod _hcont) m)
             (circleCesaro P m) ≤
            dist (liftPeriodic f _hperiod _hcont) P := by
      simpa [dist_eq_norm_sub, ← circleCesaro_sub (T:=2*Real.pi)]
        using (hnorm ((liftPeriodic f _hperiod _hcont)-P) m)
    have hlast : dist P (liftPeriodic f _hperiod _hcont) < δ/4 := by
      simpa [dist_comm] using hd
    calc
      dist (circleCesaro (liftPeriodic f _hperiod _hcont) m)
          (liftPeriodic f _hperiod _hcont) ≤
          dist (circleCesaro (liftPeriodic f _hperiod _hcont) m)
              (circleCesaro P m) +
            dist (circleCesaro P m) P +
            dist P (liftPeriodic f _hperiod _hcont) :=
         dist_triangle4 _ _ _ _
      _ < δ := by linarith
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hev : ∀ᶠ N : ℕ in atTop,
      dist (circleCesaro (liftPeriodic f _hperiod _hcont) N)
        (liftPeriodic f _hperiod _hcont) < ε :=
    (Metric.tendsto_nhds.mp ht) ε hε
  filter_upwards [hev] with N hN
  intro x
  have hpoint := ContinuousMap.dist_apply_le_dist
    (α := AddCircle (2 * Real.pi)) (β := ℂ)
    (f := (liftPeriodic f _hperiod _hcont))
    (g := circleCesaro (liftPeriodic f _hperiod _hcont) N)
    (x : AddCircle (2 * Real.pi))
  have hlt : dist
        ((liftPeriodic f _hperiod _hcont) (x : AddCircle (2 * Real.pi)))
        ((circleCesaro (liftPeriodic f _hperiod _hcont) N)
          (x : AddCircle (2 * Real.pi))) < ε :=
    hpoint.trans_lt (by simpa [dist_comm] using hN)
  simpa [liftPeriodic_apply _hperiod _hcont,
    circleCesaro_apply_lift _hperiod _hcont] using hlt
/-ResultProofEnd-/
/-ResultEnd-/
end Analysis
end LeanEval

end Submission
