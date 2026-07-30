import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis
open MeasureTheory Filter Topology Real Complex

namespace Submission

/-ResultProofDefinitionsBegin-/

open scoped ComplexConjugate BigOperators
lemma sum_int_Icc_nat {M : Type*} [AddCommMonoid M] (f : ℤ → M) (N : ℕ) :
 (∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), f k) = ∑ i ∈ Finset.range N, f (Int.ofNat (i+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : Finset.Icc (1:ℤ) ((N+1:ℕ):ℤ) = insert (((N+1:ℕ):ℤ)) (Finset.Icc (1:ℤ) (N:ℤ)) := by
      rw [Nat.cast_add, Nat.cast_one]
      symm
      exact Finset.insert_Icc_right_eq_Icc_add_one (by
        have h : (0:ℤ) ≤ (N:ℤ) := by exact_mod_cast (Nat.zero_le N)
        omega)
    rw [hset, Finset.sum_insert]
    · rw [ih, Finset.sum_range_succ]
      simpa [add_comm]
    · simp
open Complex MeasureTheory Filter Topology Real
open scoped ComplexConjugate
local notation "𝕋" => AddCircle (2*Real.pi)
lemma myfnorm (k:ℤ) (x:𝕋) : ‖fourier k x‖ = (1:ℝ) := by
  rw [fourier_apply]
  exact Circle.norm_coe _
lemma myfpow (n:ℕ) (x:𝕋) : fourier (n:ℤ) x = (fourier (1:ℤ) x)^n := by
  induction n with
  | zero => simp [fourier_zero]
  | succ n ih =>
    rw [Nat.cast_succ, fourier_add]
    simpa [ih, pow_succ] using (rfl : fourier (n:ℤ) x * fourier 1 x = _)
lemma myterm (n:ℕ) (x y:𝕋) :
 fourier (n:ℤ) x * conj (fourier (n:ℤ) y) =
   (fourier (1:ℤ) x * conj (fourier (1:ℤ) y)) ^ n := by
 rw [myfpow, myfpow, map_pow]
 rw [mul_pow]
noncomputable def wker (N:ℕ) (p:𝕋×𝕋) : ℂ :=
 ((1/(N:ℝ)):ℂ) * ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), fourier k p.1 * conj (fourier k p.2)
lemma sumterm_range (N:ℕ) (x y:𝕋) :
 (∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ), fourier k x * conj (fourier k y)) =
 ∑ i ∈ Finset.range N, (fourier (1:ℤ) x * conj (fourier (1:ℤ) y))^(i+1) := by
 rw [sum_int_Icc_nat (fun k : ℤ => fourier k x * conj (fourier k y)) N]
 apply Finset.sum_congr rfl
 intro i hi
 change fourier ((i+1:ℕ):ℤ) x * conj (fourier ((i+1:ℕ):ℤ) y) = _
 rw [myterm]
lemma tnorm (x y:𝕋) : ‖fourier (1:ℤ) x * conj (fourier (1:ℤ) y)‖ = (1:ℝ) := by rw [norm_mul, myfnorm]; simp [myfnorm]
lemma wker_bound (N:ℕ) (p:𝕋×𝕋) : ‖wker N p‖ ≤ (1:ℝ) := by
  rcases p with ⟨x,y⟩
  unfold wker
  rw [norm_mul, sumterm_range]
  calc
   ‖((1 / (N:ℝ)) : ℂ)‖ * ‖∑ i ∈ Finset.range N, (fourier (1:ℤ) x * conj (fourier (1:ℤ) y)) ^ (i+1)‖
       ≤ ‖((1 / (N:ℝ)) : ℂ)‖ * ∑ i ∈ Finset.range N, ‖(fourier (1:ℤ) x * conj (fourier (1:ℤ) y)) ^ (i+1)‖ := by
         gcongr; exact norm_sum_le _ _
   _ = ‖((1 / (N:ℝ)) : ℂ)‖ * N := by
         congr 1
         simp [norm_pow, tnorm]
   _ ≤ 1 := by
      norm_cast
      by_cases h : N = 0
      · simp [h]
      · have : (0:ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero h)
        rw [norm_div, norm_one]
        simp [abs_of_pos this]
        field_simp
        simp
lemma sumrange_geom (t:ℂ) (N:ℕ) (ht:t≠1) :
 (∑ i ∈ Finset.range N, t^(i+1)) = t * ((t^N-1)/(t-1)) := by
 rw [show (∑ i ∈ Finset.range N, t^(i+1)) = t * ∑ i ∈ Finset.range N, t^i by
   rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [pow_succ']; ]
 rw [geom_sum_eq ht]
lemma geom_avg_zero (t:ℂ) (hu: ‖t‖ = 1) (ht: t ≠ 1) :
 Tendsto (fun N : ℕ => ((1/(N:ℝ)):ℂ) * (t * ((t^N-1)/(t-1)))) atTop (𝓝 0) := by
 rw [tendsto_zero_iff_norm_tendsto_zero]
 apply squeeze_zero' (g := fun N : ℕ => (2 / ‖t-1‖) / (N:ℝ))
 · exact Filter.Eventually.of_forall (fun n => norm_nonneg _)
 · filter_upwards [] with N
   simp only [norm_mul, norm_div]
   have hpow : ‖t^N - 1‖ ≤ (2:ℝ) := calc
     _ ≤ ‖t^N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
     _ = 2 := by rw [norm_pow, hu]; norm_num
   calc
    ‖(1:ℂ)‖ / ‖((N:ℝ):ℂ)‖ * (‖t‖ * (‖t^N - 1‖ / ‖t - 1‖))
      ≤ (‖(1:ℂ)‖ / ‖((N:ℝ):ℂ)‖) * (1 * (2 / ‖t-1‖)) := by rw [hu]; gcongr
    _ = (2 / ‖t-1‖) / (N:ℝ) := by
      simp [norm_one]
      norm_cast
      ring
 · have hh : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
   simpa using (tendsto_const_nhds.div_atTop hh : Tendsto (fun N:ℕ => (2 / ‖t-1‖) / (N:ℝ)) atTop (𝓝 0))
lemma pair_ne_t (x y : 𝕋) (h : x ≠ y) :
 fourier (1:ℤ) x * conj (fourier (1:ℤ) y) ≠ (1:ℂ) := by
 intro hz
 have hyu : conj (fourier (1:ℤ) y) * fourier (1:ℤ) y = 1 := by
   rw [mul_comm, Complex.mul_conj']; simp [myfnorm]
 have hxy : fourier (1:ℤ) x = fourier (1:ℤ) y := calc
  _ = (fourier (1:ℤ) x * conj (fourier (1:ℤ) y)) * fourier (1:ℤ) y := by rw [mul_assoc, hyu]; simp
  _ = _ := by rw [hz]; simp
 rw [fourier_one, fourier_one] at hxy
 have hc : (x.toCircle) = (y.toCircle) := Subtype.ext hxy
 exact h (AddCircle.injective_toCircle (by positivity : (2*Real.pi) ≠ 0) hc)
lemma wker_lim (p:𝕋×𝕋) :
 Tendsto (fun N : ℕ => wker N p) atTop (𝓝 ((Set.diagonal 𝕋).indicator (fun _ => (1:ℂ)) p)) := by
 rcases p with ⟨x,y⟩
 by_cases h : x = y
 · subst y
   have hv : (Set.diagonal 𝕋).indicator (fun _ => (1:ℂ)) (x,x) = 1 := by simp [Set.diagonal]
   rw [hv]
   -- wker diagonal is sequence zero at 0, one otherwise
   have hend : ∀ᶠ N : ℕ in atTop, wker N (x,x) = (1:ℂ) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    unfold wker
    rw [sumterm_range]
    have hterm : fourier (1:ℤ) x * conj (fourier (1:ℤ) x) = (1:ℂ) := by rw [Complex.mul_conj']; simp [myfnorm]
    simp only [hterm, one_pow]
    simp [hN.ne']
   exact (tendsto_congr' hend).2 tendsto_const_nhds
 · have hv : (Set.diagonal 𝕋).indicator (fun _ => (1:ℂ)) (x,y) = 0 := by
       simp [Set.diagonal, h]
   rw [hv]
   let t : ℂ := fourier (1:ℤ) x * conj (fourier (1:ℤ) y)
   have ht : t ≠ 1 := pair_ne_t _ _ h
   have hz := geom_avg_zero t (tnorm _ _) ht
   unfold wker
   simp only [sumterm_range]
   convert hz using 3 with N
   rw [sumrange_geom t N ht]
lemma wker_cont (N:ℕ) : Continuous (wker N : 𝕋×𝕋 → ℂ) := by
 unfold wker
 fun_prop
lemma int_kernel_lim (μ : Measure 𝕋) [IsProbabilityMeasure μ] :
 Tendsto (fun N : ℕ => ∫ p, wker N p ∂(μ.prod μ)) atTop
 (𝓝 (∫ p, (Set.diagonal 𝕋).indicator (fun _ => (1:ℂ)) p ∂(μ.prod μ))) := by
 apply tendsto_integral_of_dominated_convergence (μ:= μ.prod μ) (fun _ => (1:ℝ))
 · intro n; exact (wker_cont n).aestronglyMeasurable
 · exact integrable_const _
 · intro n; exact Filter.Eventually.of_forall (fun p => wker_bound n p)
 · exact Filter.Eventually.of_forall (fun p => wker_lim p)



-- a single character is bounded; the corresponding product kernel is integrable
lemma integrable_charprod (μ : Measure 𝕋) [IsFiniteMeasure μ] (k : ℤ) :
    Integrable (fun p : 𝕋 × 𝕋 => fourier k p.1 * conj (fourier k p.2)) (μ.prod μ) := by
  letI : IsFiniteMeasure (μ.prod μ) := by infer_instance
  apply Integrable.of_bound
    ((by fun_prop : Continuous (fun p : 𝕋 × 𝕋 =>
      fourier k p.1 * conj (fourier k p.2))).aestronglyMeasurable) (1:ℝ)
  exact Filter.Eventually.of_forall (fun p => by
    rw [norm_mul, Complex.norm_conj, myfnorm k p.1, myfnorm k p.2]
    norm_num)

-- one summand of the averaged norms is the integral of the product character
lemma coeff_sq_eq_prod_integral (μ : Measure 𝕋) [IsProbabilityMeasure μ] (k : ℤ) :
    ((‖fourierCoeffMeasure μ k‖ ^ 2 : ℝ) : ℂ) =
      ∫ p : 𝕋 × 𝕋, fourier k p.1 * conj (fourier k p.2) ∂(μ.prod μ) := by
  calc
    ((‖fourierCoeffMeasure μ k‖ ^ 2 : ℝ) : ℂ) =
        fourierCoeffMeasure μ k * conj (fourierCoeffMeasure μ k) :=
          by
            rw [Complex.ofReal_pow]
            exact (Complex.mul_conj' (fourierCoeffMeasure μ k)).symm
    _ = (∫ x : 𝕋, fourier k x ∂μ) *
          (∫ y : 𝕋, conj (fourier k y) ∂μ) := by
          unfold fourierCoeffMeasure
          have hc : (∫ y : 𝕋, conj (fourier k y) ∂μ) =
              conj (∫ y : 𝕋, fourier k y ∂μ) :=
            @integral_conj 𝕋 _ μ ℂ _ (fun y : 𝕋 => fourier k y)
          rw [hc]
    _ = _ := by
      symm
      exact integral_prod_mul (fun x : 𝕋 => fourier k x)
        (fun y : 𝕋 => conj (fourier k y))

-- identify the integral of the elementary averaged kernel with the (complexified)
-- finite Cesaro sum of squared coefficients
lemma avg_coeff_eq_kernel (μ : Measure 𝕋) [IsProbabilityMeasure μ] (N : ℕ) :
    (((1 / (N : ℝ)) *
          ∑ k ∈ Finset.Icc (1 : ℤ) (N:ℤ), ‖fourierCoeffMeasure μ k‖ ^ 2 : ℝ) : ℂ) =
      ∫ p : 𝕋 × 𝕋, wker N p ∂(μ.prod μ) := by
  classical
  letI : IsFiniteMeasure (μ.prod μ) := by infer_instance
  -- interchange the finite sum and the Bochner integral
  have hsum :
      (∫ p : 𝕋 × 𝕋,
          ∑ k ∈ Finset.Icc (1 : ℤ) (N:ℤ),
            (fourier k p.1 * conj (fourier k p.2)) ∂(μ.prod μ)) =
        ∑ k ∈ Finset.Icc (1 : ℤ) (N:ℤ),
          (∫ p : 𝕋 × 𝕋, fourier k p.1 * conj (fourier k p.2) ∂(μ.prod μ)) := by
    apply integral_finset_sum
    intro i hi
    exact integrable_charprod μ i
  -- the outside scalar is constant for the integral
  rw [show (∫ p : 𝕋 × 𝕋, wker N p ∂(μ.prod μ)) =
        (((1/(N:ℝ)):ℂ) *
          (∫ p : 𝕋 × 𝕋,
            ∑ k ∈ Finset.Icc (1:ℤ) (N:ℤ),
              (fourier k p.1 * conj (fourier k p.2)) ∂(μ.prod μ))) by
      unfold wker
      exact integral_const_mul _ _]
  rw [hsum]
  -- now it is the sum of the individual identities
  calc
    (((1 / (N : ℝ)) *
          ∑ k ∈ Finset.Icc (1 : ℤ) (N:ℤ), ‖fourierCoeffMeasure μ k‖ ^ 2 : ℝ) : ℂ) =
        ((((1 / (N : ℝ) : ℝ) : ℂ) *
          ((∑ k ∈ Finset.Icc (1 : ℤ) (N:ℤ), ‖fourierCoeffMeasure μ k‖ ^ 2 : ℝ) : ℂ))) := by
            rw [Complex.ofReal_mul]
    _ = ((((1 / (N : ℝ) : ℝ) : ℂ) *
          ∑ k ∈ Finset.Icc (1 : ℤ) (N:ℤ),
            ((‖fourierCoeffMeasure μ k‖ ^ 2 : ℝ) : ℂ))) := by
            rw [Complex.ofReal_sum]
    _ = ((((1 / (N : ℝ) : ℝ) : ℂ) *
          ∑ k ∈ Finset.Icc (1 : ℤ) (N:ℤ),
            (∫ p : 𝕋 × 𝕋, fourier k p.1 * conj (fourier k p.2) ∂(μ.prod μ)))) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          exact coeff_sq_eq_prod_integral μ k
    _ = (((1 / ((N:ℝ):ℂ)) *
          ∑ k ∈ Finset.Icc (1 : ℤ) (N:ℤ),
            (∫ p : 𝕋 × 𝕋, fourier k p.1 * conj (fourier k p.2) ∂(μ.prod μ)))) := by
          congr 1
          simpa using (Complex.ofReal_div (1:ℝ) (N:ℝ))




lemma measure_diag_eq_tsum (μ : Measure 𝕋) [IsProbabilityMeasure μ] :
    (μ.prod μ) (Set.diagonal 𝕋) = ∑' x : 𝕋, μ {x} * μ {x} := by
  classical
  let s : Set 𝕋 := {x | 0 < μ {x}}
  have hs : s.Countable := by
    dsimp [s]
    refine Measure.countable_meas_pos_of_disjoint_iUnion (μ:=μ)
      (As:= fun x : 𝕋 => ({x} : Set 𝕋)) (fun x => MeasurableSet.singleton x) ?_
    intro a b hab
    exact Set.disjoint_singleton_left.mpr (by simpa using hab)
  have hd : MeasurableSet (Set.diagonal 𝕋) :=
    isClosed_diagonal.measurableSet
  rw [Measure.prod_apply hd]
  have hfib : (fun x : 𝕋 => μ (Prod.mk x ⁻¹' (Set.diagonal 𝕋))) =
      (fun x : 𝕋 => μ {x}) := by
    funext x
    congr 1
    ext y
    simp [Set.diagonal, eq_comm]
  simp_rw [hfib]
  -- Restrict the lintegral to the countable set on which the integrand is nonzero.
  rw [← setLIntegral_eq_of_support_subset
        (μ:=μ) (f:= fun x : 𝕋 => μ {x}) (s:=s) (by
          intro x hx
          have hne : μ {x} ≠ 0 := (Function.mem_support.1 hx)
          exact (show 0 < μ {x} from (pos_iff_ne_zero.2 hne)))]
  rw [lintegral_countable (μ:=μ) (fun x : 𝕋 => μ {x}) hs]
  -- Fill in zero terms outside `s`.
  calc
    (∑' a : s, μ {(a : 𝕋)} * μ {(a : 𝕋)}) =
        ∑' x : 𝕋, s.indicator (fun x : 𝕋 => μ {x} * μ {x}) x :=
          tsum_subtype s (fun x : 𝕋 => μ {x} * μ {x})
    _ = _ := by
      apply tsum_congr
      intro x
      by_cases hx : x ∈ s
      · simp [Set.indicator_of_mem hx]
      · have hxn : ¬ 0 < μ {x} := by
          exact fun hp => hx hp
        have hz0 : μ {x} = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hxn)
        simp [Set.indicator, hx, hz0]

lemma diag_real_eq_atoms (μ : Measure 𝕋) [IsProbabilityMeasure μ] :
    (μ.prod μ).real (Set.diagonal 𝕋) =
      ∑' x : 𝕋, ((μ {x}).toReal) ^ 2 := by
  rw [Measure.real_def, measure_diag_eq_tsum μ]
  rw [ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro x
    rw [ENNReal.toReal_mul]
    ring
  · intro x
    exact ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)

/-ResultProofDefinitionsEnd-/


theorem wiener_atom_detection (μ : Measure (AddCircle (2 * Real.pi))) [IsProbabilityMeasure μ] :
    Tendsto
      (fun N : ℕ =>
        (1 / (N : ℝ)) *
          ∑ k ∈ Finset.Icc (1 : ℤ) N, ‖fourierCoeffMeasure μ k‖ ^ 2)
      atTop
      (𝓝 (∑' x : AddCircle (2 * Real.pi), ((μ {x}).toReal) ^ 2)) := by
  -- The analytic core: the normalized character kernels are uniformly bounded,
  -- and converge pointwise to the indicator of the diagonal.  `int_kernel_lim`
  -- is dominated convergence on the finite product probability space.
  have hdiag := int_kernel_lim μ
  have hmeas : MeasurableSet (Set.diagonal 𝕋) :=
    isClosed_diagonal.measurableSet
  have hconst :
      (∫ p : 𝕋 × 𝕋,
          (Set.diagonal 𝕋).indicator (fun _ => (1 : ℂ)) p ∂(μ.prod μ)) =
        (((μ.prod μ).real (Set.diagonal 𝕋) : ℝ) : ℂ) := by
    rw [integral_indicator_const (μ := μ.prod μ) (1 : ℂ) hmeas]
    exact (by
      simpa only [mul_one] using
        (Complex.real_smul
          (x := (μ.prod μ).real (Set.diagonal 𝕋)) (z := (1 : ℂ))))
  have hI :
      (∫ p : 𝕋 × 𝕋,
          (Set.diagonal 𝕋).indicator (fun _ => (1 : ℂ)) p ∂(μ.prod μ)) =
        ((∑' x : 𝕋, ((μ {x}).toReal) ^ 2 : ℝ) : ℂ) := by
    calc
      (∫ p : 𝕋 × 𝕋,
          (Set.diagonal 𝕋).indicator (fun _ => (1 : ℂ)) p ∂(μ.prod μ)) =
          (((μ.prod μ).real (Set.diagonal 𝕋) : ℝ) : ℂ) := hconst
      _ = ((∑' x : 𝕋, ((μ {x}).toReal) ^ 2 : ℝ) : ℂ) := by
        rw [diag_real_eq_atoms μ]
  rw [hI] at hdiag
  have hcomp :
      Tendsto
        (fun N : ℕ =>
          (((1 / (N : ℝ)) *
            ∑ k ∈ Finset.Icc (1 : ℤ) (N:ℤ), ‖fourierCoeffMeasure μ k‖ ^ 2 : ℝ) : ℂ))
        atTop
        (𝓝 (((∑' x : 𝕋, ((μ {x}).toReal) ^ 2) : ℝ) : ℂ)) := by
      exact Filter.Tendsto.congr'
        (Filter.Eventually.of_forall
          (fun N : ℕ => (avg_coeff_eq_kernel μ N).symm)) hdiag
  have hre :=
    (Complex.continuous_re.tendsto
      (((∑' x : 𝕋, ((μ {x}).toReal) ^ 2) : ℝ) : ℂ)).comp hcomp
  simpa only [Function.comp_def, Complex.ofReal_re] using hre

end Submission
