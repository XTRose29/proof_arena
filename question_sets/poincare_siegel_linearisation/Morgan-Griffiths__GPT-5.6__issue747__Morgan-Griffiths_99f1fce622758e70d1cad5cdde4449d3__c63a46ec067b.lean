import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Arith.lean

/- Some elementary arithmetic consequences of the Diophantine inequality.  The
predicate in the exercise is defined in the statement file, so I state these
lemmas in terms of its defining inequality rather than importing that file. -/
namespace PoincareSiegelSupport

/-- A positive constant divided by a (nonzero) integer to a real power is
strictly positive. -/
lemma pos_div_abs_int_rpow (C τ : ℝ) (hC : 0 < C) {q : ℤ} (hq : q ≠ 0) :
    0 < C / |(q : ℝ)| ^ τ := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hpos : 0 < |(q : ℝ)| := abs_pos.mpr hq'
  exact div_pos hC (Real.rpow_pos_of_pos hpos _)

/-- In particular a real number satisfying such an inequality is not equal
to any rational `p/q` with `q ≠ 0`.  It is useful to keep the conclusion
with integer numerator and denominator, to avoid all floor/rat casting noise
later. -/
lemma ne_int_div (α C τ : ℝ) (hC : 0 < C)
    (hbound : ∀ p q : ℤ, q ≠ 0 → C / |(q : ℝ)| ^ τ ≤
      |α - (p : ℝ) / (q : ℝ)|) :
    ∀ p q : ℤ, q ≠ 0 → α ≠ (p : ℝ) / (q : ℝ) := by
  intro p q hq he
  have hp := hbound p q hq
  have hpos := pos_div_abs_int_rpow C τ hC hq
  rw [he, sub_self, abs_zero] at hp
  linarith

/-- The same statement with a natural denominator. -/
lemma ne_int_div_nat (α C τ : ℝ) (hC : 0 < C)
    (hbound : ∀ p q : ℤ, q ≠ 0 → C / |(q : ℝ)| ^ τ ≤
      |α - (p : ℝ) / (q : ℝ)|)
    (p : ℤ) {n : ℕ} (hn : n ≠ 0) : α ≠ (p : ℝ) / (n : ℝ) := by
  have hnI : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa using (ne_int_div α C τ hC hbound p (n : ℤ) hnI)

end PoincareSiegelSupport

namespace PoincareSiegelSupport
open Complex

/-- Consequently the multiplier `exp(2π i α)` is not a root of unity.  The
rather explicit form of this lemma (natural exponents, with the real
inequality as input) has proved more pleasant to use for recursive power
series coefficients than a `¬ IsROU` coercion.
-/
lemma exp_two_pi_mul_pow_ne_one (α C τ : ℝ) (hC : 0 < C)
    (hbound : ∀ p q : ℤ, q ≠ 0 → C / |(q : ℝ)| ^ τ ≤
      |α - (p : ℝ) / (q : ℝ)|)
    {n : ℕ} (hn : n ≠ 0) :
    (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ))) ^ n ≠ 1 := by
  intro hpow
  have hexp :
      Complex.exp ((n:ℂ) * (2 * Real.pi * Complex.I * (α:ℂ))) = 1 := by
    rw [Complex.exp_nat_mul]
    exact hpow
  obtain ⟨k, hk⟩ := (Complex.exp_eq_one_iff.mp hexp)
  have hp : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hk' : (α:ℂ) * (n:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) =
      (k:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by
    convert hk using 1 <;> ring
  have hmul : (α:ℂ) * (n:ℂ) = (k:ℂ) :=
    mul_right_cancel₀ hp hk'
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  have hfracC : (α:ℂ) = (k:ℂ) / (n:ℂ) :=
    (eq_div_iff hnC).2 hmul
  have hfrac : α = (k:ℝ) / (n:ℝ) := by
    exact_mod_cast hfracC
  exact (ne_int_div_nat α C τ hC hbound k hn) hfrac

/-- The denominator occurring in Schröder recursion at order `n` is
nonzero. -/
lemma exp_two_pi_mul_pow_sub_self_ne_zero (α C τ : ℝ) (hC : 0 < C)
    (hbound : ∀ p q : ℤ, q ≠ 0 → C / |(q : ℝ)| ^ τ ≤
      |α - (p : ℝ) / (q : ℝ)|)
    {n : ℕ} (hn : 2 ≤ n) :
    (Complex.exp (2 * Real.pi * Complex.I * (α : ℂ))) ^ n -
        Complex.exp (2 * Real.pi * Complex.I * (α : ℂ)) ≠ 0 := by
  -- factor off the (non-zero) multiplier.
  let l : ℂ := Complex.exp (2 * Real.pi * Complex.I * (α : ℂ))
  have hl : l ≠ 0 := Complex.exp_ne_zero _
  have hpred : n - 1 ≠ 0 := by omega
  have hne : l ^ (n-1) ≠ 1 := by
    dsimp [l]
    exact exp_two_pi_mul_pow_ne_one α C τ hC hbound hpred
  -- rewriting `l^n = l^(n-1) l` is nicer than using natural subtraction
  have hnpos : 1 ≤ n := by omega
  have hnrep : n - 1 + 1 = n := by omega
  have hfactor : l ^ n - l = (l ^ (n-1) - 1) * l := by
    calc
      l ^ n - l = (l ^ (n-1)) * l - l := by
        rw [← pow_succ]
        simp only [hnrep]
      _ = (l ^ (n-1) - 1) * l := by ring
  change l ^ n - l ≠ 0
  rw [hfactor]
  exact mul_ne_zero (sub_ne_zero.mpr hne) hl

end PoincareSiegelSupport

-- END INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Arith.lean

-- BEGIN INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Taylor.lean

namespace PoincareSiegelSupport

/-- Extract the ordinary (one variable) convergent Taylor series from an
`AnalyticAt` complex germ. This packages the `FormalMultilinearSeries` API
into a scalar sequence; the convergence radius assertion is the one useful
for constructing Schröder series. -/
lemma analyticAt_exists_taylor (f:ℂ→ℂ) (hf: AnalyticAt ℂ f 0) :
    ∃ a:ℕ→ℂ,
      0 < (FormalMultilinearSeries.ofScalars ℂ a).radius ∧
      a 0 = f 0 ∧ a 1 = deriv f 0 ∧
      ∀ᶠ z in nhds (0:ℂ), f z = ∑' n:ℕ, a n * z ^ n := by
  let a : ℕ → ℂ := fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)
  have hp := hf.hasFPowerSeriesAt
  change HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0 at hp
  refine ⟨a, hp.radius_pos, ?_, ?_, ?_⟩
  · simp [a, iteratedDeriv_zero]
  · simp [a, iteratedDeriv_one]
  obtain ⟨r, hr⟩ := hp
  filter_upwards [Metric.eball_mem_nhds (0:ℂ) hr.r_pos] with z hz
  have hsum := hr.hasSum hz
  rw [zero_add] at hsum
  have heq := hsum.tsum_eq.symm
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using heq

/-- Two actual germs admitting exactly the same power series at the point
coincide on a neighbourhood (no identity theorem needed). -/
lemma HasFPowerSeriesAt.eventuallyEq_zero {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {f g : ℂ → ℂ} (hf : HasFPowerSeriesAt f p 0)
    (hg : HasFPowerSeriesAt g p 0) : f =ᶠ[nhds (0:ℂ)] g := by
  obtain ⟨r, hr⟩ := hf
  obtain ⟨s, hs⟩ := hg
  filter_upwards [Metric.eball_mem_nhds (0:ℂ) hr.r_pos,
    Metric.eball_mem_nhds (0:ℂ) hs.r_pos] with z hz hzs
  have h1 := hr.hasSum hz
  have h2 := hs.hasSum hzs
  rw [zero_add] at h1 h2
  exact HasSum.unique h1 h2

end PoincareSiegelSupport

-- END INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Taylor.lean

-- BEGIN INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Formal.lean
namespace PoincareSiegelSupport
open FormalMultilinearSeries
open scoped Topology

/-- The formal solution of the Schroeder equation.  This is the exact same
well-founded triangular recursion as `rightInv` in the analytic inverse
function theorem.  The nonlinear terms of degree `n` only involve blocks
of size `< n`. -/
noncomputable def schroederSeries (p : FormalMultilinearSeries ℂ ℂ ℂ) (l : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ
  | 0 => 0
  | 1 => ContinuousMultilinearMap.mkPiAlgebraFin ℂ 1 ℂ
  | n + 2 =>
    let q : FormalMultilinearSeries ℂ ℂ ℂ :=
      fun k => if k < n + 2 then schroederSeries p l k else 0
    ((l ^ (n + 2) - l)⁻¹) •
      (∑ c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset),
        p.compAlongComposition q c)

@[simp] lemma schroederSeries_zero (p : FormalMultilinearSeries ℂ ℂ ℂ) (l : ℂ) :
    schroederSeries p l 0 = 0 := by rw [schroederSeries]

@[simp] lemma schroederSeries_one (p : FormalMultilinearSeries ℂ ℂ ℂ) (l : ℂ) :
    schroederSeries p l 1 = ContinuousMultilinearMap.mkPiAlgebraFin ℂ 1 ℂ := by
  rw [schroederSeries]

/-- In the nonlinear summands all blocks have smaller size; hence replacing
the recursive series by its cutoff in the definition does nothing. -/
lemma schroeder_trunc_sum (p : FormalMultilinearSeries ℂ ℂ ℂ) (l : ℂ) (n : ℕ)
    (v : Fin (n+2) → ℂ) :
    ∑ c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset),
      p c.length
        (FormalMultilinearSeries.applyComposition
          (fun k : ℕ => if k < n+2 then schroederSeries p l k else 0) c v) =
    ∑ c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset),
      p c.length ((schroederSeries p l).applyComposition c v) := by
  have N : 0 < n + 2 := by omega
  refine Finset.sum_congr rfl ?_
  intro c hc
  apply p.congr rfl
  intro j hj1 hj2
  have H : ∀ k, c.blocksFun k < n + 2 := by
    -- same bookkeeping as `comp_rightInv_aux2`
    simp only [Set.mem_toFinset (s := {c : Composition (n+2) | 1 < c.length}),
      Set.mem_setOf_eq] at hc
    simp [← Composition.ne_single_iff N, Composition.eq_single_iff_length,
      ne_of_gt hc]
  simp [FormalMultilinearSeries.applyComposition, H]


/-- Every one-dimensional complex formal series with a nonresonant linear
coefficient has the following formal conjugacy. -/
lemma comp_schroederSeries (p : FormalMultilinearSeries ℂ ℂ ℂ) (l : ℂ)
    (hp1 : p.coeff 1 = l) (hp0 : p.coeff 0 = 0)
    (hne : ∀ n : ℕ, 2 ≤ n → l^n-l ≠ 0) :
    p.comp (schroederSeries p l) =
      (schroederSeries p l).compContinuousLinearMap
        (l • ContinuousLinearMap.id ℂ ℂ) := by
  classical
  apply FormalMultilinearSeries.ext
  intro n
  apply ContinuousMultilinearMap.ext
  intro v
  match n with
  | 0 =>
      rw [FormalMultilinearSeries.comp_coeff_zero']
      change p 0 (fun _ => 0) = _
      have z : p 0 (fun _ => 0) = p.coeff 0 := by
        -- coefficient is evaluation at the empty vector
        simpa [FormalMultilinearSeries.apply_eq_prod_smul_coeff, smul_eq_mul]
      rw [z, hp0]
      -- the right side is zero since the series has zero constant term
      
      -- compute the coefficient at zero of the precomposition
      change 0 = (schroederSeries p l 0)
          (⇑(l • ContinuousLinearMap.id ℂ ℂ) ∘ v)
      rw [schroederSeries_zero]
      rfl
  | 1 =>
      -- coefficient of composition at one
      rw [FormalMultilinearSeries.comp_coeff_one]
      -- reduce both sides to products of scalars by multilinearity
      -- all vectors in `Fin 1` are retained
      have hv : (fun _i : Fin 1 =>
          (schroederSeries p l 1) v) =
          (fun _i : Fin 1 => v 0) := by
        funext i
        fin_cases i
        simp [schroederSeries_one,
          ContinuousMultilinearMap.mkPiAlgebraFin_apply]
      rw [hv]
      have peval : p 1 (fun _i : Fin 1 => v 0) = l * v 0 := by
        simpa [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
          smul_eq_mul, hp1, mul_comm]
      rw [peval]
      
      rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
      simp [schroederSeries_one,
        ContinuousMultilinearMap.mkPiAlgebraFin_apply,
        Function.comp_def, mul_comm]
  | n+2 =>
      have N : 0 < n+2 := by omega
      let Sv : ℂ :=
        ∑ c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset),
          p c.length ((schroederSeries p l).applyComposition c v)
      have L : p 1 (fun _ : Fin 1 =>
            schroederSeries p l (n+2) v) =
          l * (schroederSeries p l (n+2) v) := by
        -- on one vector the product is that vector
        simpa [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
          smul_eq_mul, hp1, mul_comm]
      rw [FormalMultilinearSeries.comp_rightInv_aux1 N]
      have T :
        (∑ c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset),
          p.compAlongComposition
            (fun k => if k < n+2 then schroederSeries p l k else 0) c) v
        = Sv := by
          simp only [ContinuousMultilinearMap.sum_apply]
          exact schroeder_trunc_sum p l n v
      have Q : schroederSeries p l (n+2) v =
          (l^(n+2)-l)⁻¹ * Sv := by
        rw [schroederSeries]
        rw [ContinuousMultilinearMap.smul_apply]
        change (l^(n+2)-l)⁻¹ * _ = _
        rw [T]
      -- evaluate the right hand side after the scalar map in the inputs
      have R :
        ((schroederSeries p l).compContinuousLinearMap
          (l • ContinuousLinearMap.id ℂ ℂ)) (n+2) v =
          l^(n+2) * (schroederSeries p l (n+2) v) := by
        rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
        -- take l out of each coordinate
        -- ``apply_eq_prod_smul_coeff`` does exactly this in dimension one
        simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
        simp only [Pi.one_apply, smul_eq_mul]
        -- products distribute a constant product
        have P : (∏ i : Fin (n+2), l * v i) = l^(n+2) * ∏ i : Fin (n+2), v i := by
          classical
          calc
            ∏ i : Fin (n+2), l * v i =
                (∏ i : Fin (n+2), l) * ∏ i : Fin (n+2), v i := by
                  exact Finset.prod_mul_distrib
            _ = _ := by simp
        simp [Function.comp_def]
        -- after simplifying the continuous linear map the goal is a product
        change (∏ i : Fin (n+2), l * v i) *
          (schroederSeries p l).coeff (n+2) = _
        rw [P]
        ring
      change Sv + p 1 (fun _ : Fin 1 =>
          schroederSeries p l (n+2) v) = _
      rw [L, R, Q]
      -- now a scalar equality

      field_simp [hne (n+2) (by omega)]
      <;> ring

end PoincareSiegelSupport

namespace PoincareSiegelSupport
open FormalMultilinearSeries

/-- A formal series with positive radius is its own analytic germ.  Keeping this
small construction explicit is useful: nothing below asserts convergence for
the recursively constructed series. -/
lemma hasFPowerSeriesAt_sum (q : FormalMultilinearSeries ℂ ℂ ℂ)
    (hq : 0 < q.radius) : HasFPowerSeriesAt q.sum q 0 := by
  refine ⟨q.radius, le_rfl, hq, ?_⟩
  intro y hy
  have hs0 : Summable (fun n : ℕ => ‖q n (fun _ : Fin n => y)‖) :=
    q.summable_norm_apply hy
  have hs : Summable (fun n : ℕ => q n (fun _ : Fin n => y)) :=
    summable_norm_iff.mp hs0
  -- the definition of `sum` is the same series
  simpa [FormalMultilinearSeries.sum, zero_add] using hs.hasSum

/-- Once convergence of the recursively built series is supplied, the
remaining passage from formal equality to equality of germs uses only the
power-series API. This isolates the genuine small-divisor estimate. -/
lemma analytic_conjugate_of_radius
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {l : ℂ}
    (hf : HasFPowerSeriesAt f p 0)
    (hp0 : p.coeff 0 = 0) (hp1 : p.coeff 1 = l)
    (hne : ∀ n : ℕ, 2 ≤ n → l^n-l ≠ 0)
    (hq : 0 < (schroederSeries p l).radius) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = 0 ∧ deriv u 0 = 1 ∧
      ∀ᶠ z in nhds (0 : ℂ), f (u z) = u (l*z) := by
  classical
  let q := schroederSeries p l
  let L : ℂ →L[ℂ] ℂ := l • ContinuousLinearMap.id ℂ ℂ
  let u : ℂ → ℂ := q.sum
  have hu : HasFPowerSeriesAt u q 0 := hasFPowerSeriesAt_sum q hq
  have hu_an : AnalyticAt ℂ u 0 := hu.analyticAt
  have u0 : u 0 = 0 := by
    have z := hu.coeff_zero (fun _ : Fin 0 => (0:ℂ))
    simpa [q, schroederSeries_zero] using z.symm
  have uder : deriv u 0 = 1 := by
    rw [hu.deriv]
    simp [q, schroederSeries_one,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply]
  have heqformal : p.comp q = q.compContinuousLinearMap L := by
    exact comp_schroederSeries p l hp1 hp0 hne
  -- compose convergent germs
  have hcomp : HasFPowerSeriesAt (f ∘ u) (p.comp q) 0 := by
    -- composition theorem centers the outer series at `u 0`
    have hf' : HasFPowerSeriesAt f p (u 0) := by simpa [u0] using hf
    exact hf'.comp  hu
  have hucirc : HasFPowerSeriesAt (fun z : ℂ => u (l*z))
      (q.compContinuousLinearMap L) 0 := by
    have : HasFPowerSeriesAt (u ∘ L) (q.compContinuousLinearMap L) 0 := by
      have huL : HasFPowerSeriesAt u q (L 0) := by simpa [L] using hu
      exact huL.compContinuousLinearMap
    simpa [Function.comp_def, L] using this
  refine ⟨u, hu_an, u0, uder, ?_⟩
  have A : HasFPowerSeriesAt (f ∘ u) (q.compContinuousLinearMap L) 0 := by
    rwa [heqformal] at hcomp
  have ev := PoincareSiegelSupport.HasFPowerSeriesAt.eventuallyEq_zero A hucirc
  exact ev
end PoincareSiegelSupport

-- END INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Formal.lean

-- BEGIN INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/SmallDivisors.lean
/-! Elementary complex and trigonometric estimates for the small divisors. -/
namespace PoincareSiegelSupport

lemma norm_exp_I_sub_one (t : ℝ) :
    ‖Complex.exp ((t:ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (t/2)| := by
  rw [Complex.exp_ofReal_mul_I]
  have heq : (↑(Real.cos t) + ↑(Real.sin t) * Complex.I - (1:ℂ)) =
      (↑(Real.cos t - 1) : ℂ) + (↑(Real.sin t) : ℂ) * Complex.I := by
        push_cast
        ring
  rw [heq, Complex.norm_add_mul_I]
  have hs : 0 ≤ 2 * |Real.sin (t/2)| := by positivity
  have hinside : (Real.cos t - 1) ^ 2 + Real.sin t ^ 2 =
       (2 * |Real.sin (t/2)|) ^ 2 := by
    rw [show t = 2*(t/2) by ring, Real.cos_two_mul, Real.sin_two_mul]
    have hident := Real.sin_sq_add_cos_sq (t/2)
    have ht : 2 * (t/2) / 2 = t/2 := by ring
    rw [ht]
    simp only [mul_pow]
    rw [sq_abs]
    nlinarith
  rw [hinside, Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg hs]

lemma norm_exp_two_pi_I_sub_one (x:ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (x:ℂ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  have heq : (2 * Real.pi * Complex.I * (x:ℂ)) =
      ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
  rw [heq, norm_exp_I_sub_one]
  congr 1
  congr 1
  congr 1 <;> ring

/-- We use a half-open closest-integer convention only to get a convenient
interval on which the elementary linear sine bound applies. -/
lemma exists_int_abs_sub_le_half (x : ℝ) :
    ∃ k : ℤ, |x - (k : ℝ)| ≤ (1/2:ℝ) := by
  let k : ℤ := ⌊x + (1/2:ℝ)⌋
  refine ⟨k, ?_⟩
  have hle : (k:ℝ) ≤ x + (1/2:ℝ) := Int.floor_le _
  have hlt : x + (1/2:ℝ) < (k:ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

lemma abs_sin_pi_sub_int (x:ℝ) (k:ℤ) : |Real.sin (Real.pi * x)| =
    |Real.sin (Real.pi * (x - (k:ℝ)))| := by
  have heq : Real.pi * (x - (k:ℝ)) + k * Real.pi = Real.pi * x := by
    ring
  conv_lhs => rw [← heq]
  rw [Real.sin_add_int_mul_pi]
  rw [abs_mul]
  have hneg : |((-1 : ℝ) ^ k)| = 1 := by
    rw [abs_zpow]
    simp
  rw [hneg, one_mul]

/-- Linear lower bound for the chord with a chosen closest integer. -/
lemma four_mul_abs_sub_int_le_norm_exp (x:ℝ) (k:ℤ)
    (hk : |x - (k:ℝ)| ≤ (1/2:ℝ)) :
    4 * |x - (k:ℝ)| ≤
      ‖Complex.exp (2 * Real.pi * Complex.I * (x:ℂ)) - 1‖ := by
  rw [norm_exp_two_pi_I_sub_one x, abs_sin_pi_sub_int x k]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hyabs : |Real.pi * (x - (k:ℝ))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith
  have hsin := Real.mul_abs_le_abs_sin hyabs
  rw [abs_mul, abs_of_pos hpi] at hsin
  have hpine : (Real.pi:ℝ) ≠ 0 := ne_of_gt hpi
  have hsimp : 2 / Real.pi * (Real.pi * |x - (k:ℝ)|) =
        2 * |x - (k:ℝ)| := by field_simp
  rw [hsimp] at hsin
  nlinarith

/-- A version of the small divisor bound that avoids rearranging `rpow`s.
Keeping it as `n * (C / n^τ)` avoids any hypotheses on `τ`. -/
lemma diophantine_norm_pow_sub_one_lower
    (α C τ:ℝ) (hC:0<C)
    (hbound : ∀ p q:ℤ, q ≠ 0 → C / |(q:ℝ)|^τ ≤
      |α - (p:ℝ)/(q:ℝ)|)
    {n:ℕ} (hn:n ≠ 0) :
    4 * (n:ℝ) * (C / (n:ℝ)^τ) ≤
      ‖(Complex.exp (2 * Real.pi * Complex.I * (α:ℂ)))^ n - 1‖ := by
  obtain ⟨k,hk⟩ := exists_int_abs_sub_le_half ((n:ℝ)*α)
  have hlower := four_mul_abs_sub_int_le_norm_exp ((n:ℝ)*α) k hk
  have hexpeq : (Complex.exp (2 * Real.pi * Complex.I * (α:ℂ))) ^ n =
      Complex.exp (2 * Real.pi * Complex.I * (((n:ℝ)*α:ℝ):ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexpeq]
  have hnI : (n:ℤ) ≠ 0 := by exact_mod_cast hn
  have hb := hbound k (n:ℤ) hnI
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have habs : |((n:ℤ):ℝ)| = (n:ℝ) := by
    have hh : (((n:ℤ):ℝ)) = (n:ℝ) := by norm_cast
    rw [hh, abs_of_pos hnR]
  rw [habs] at hb
  have hb' : C / (n:ℝ)^τ ≤ |α - (k:ℝ)/(n:ℝ)| := by
    convert hb using 1 <;> norm_cast
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt hnR
  have hchange : |(n:ℝ) * α - (k:ℝ)| =
      (n:ℝ) * |α - (k:ℝ)/(n:ℝ)| := by
    calc
      |(n:ℝ)*α - (k:ℝ)| = |(n:ℝ) * (α - (k:ℝ)/(n:ℝ))| := by
        congr 1
        field_simp
      _ = |(n:ℝ)| * |α - (k:ℝ)/(n:ℝ)| := abs_mul _ _
      _ = (n:ℝ) * |α - (k:ℝ)/(n:ℝ)| := by rw [abs_of_pos hnR]
  rw [hchange] at hlower
  have hmult : (n:ℝ) * (C / (n:ℝ)^τ) ≤
      (n:ℝ) * |α - (k:ℝ)/(n:ℝ)| := by
    exact mul_le_mul_of_nonneg_left hb' (le_of_lt hnR)
  nlinarith


/-- The corresponding lower bound for the denominator in the homogeneous
coefficient recurrence.  Multiplication by the unit-modulus multiplier does
not change its norm. -/
lemma diophantine_norm_pow_sub_self_lower
    (α C τ:ℝ) (hC:0<C)
    (hbound : ∀ p q:ℤ, q ≠ 0 → C / |(q:ℝ)|^τ ≤
      |α - (p:ℝ)/(q:ℝ)|)
    {n:ℕ} (hn:2 ≤ n) :
    4 * (n-1:ℕ) * (C / ( (n-1:ℕ):ℝ)^τ) ≤
      ‖(Complex.exp (2 * Real.pi * Complex.I * (α:ℂ)))^ n -
        Complex.exp (2 * Real.pi * Complex.I * (α:ℂ))‖ := by
  let l := Complex.exp (2 * Real.pi * Complex.I * (α:ℂ))
  have hl : ‖l‖ = 1 := by
    dsimp [l]
    rw [Complex.norm_exp]
    have hz : (2 * (Real.pi:ℂ) * Complex.I * (α:ℂ)).re = 0 := by simp
    rw [hz, Real.exp_zero]
  have hnrep : n - 1 + 1 = n := by omega
  have hfac : l ^ n - l = (l ^ (n-1) - 1) * l := by
    calc
      l ^ n - l = (l ^ (n-1)) * l - l := by
        rw [← pow_succ]
        simp only [hnrep]
      _ = (l ^ (n-1) - 1) * l := by ring
  have hlower := diophantine_norm_pow_sub_one_lower α C τ hC hbound
      (n := n-1) (by omega)
  change _ ≤ ‖l ^ n - l‖
  rw [hfac, norm_mul, hl, mul_one]
  exact hlower

end PoincareSiegelSupport

-- END INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/SmallDivisors.lean

-- BEGIN INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Majorant.lean
namespace PoincareSiegelSupport
open FormalMultilinearSeries
open scoped BigOperators

/-- A norm recursion for the formal Schroeder solution.  This is the starting
point of any majorant/tree estimate: a vertex of total weight `n+2` splits
into the blocks of a (nontrivial) composition, and the factor at the vertex
is the inverse small divisor.  All the factors from recursive calls have
strictly smaller weights. -/
lemma schroederSeries_norm_rec (p : FormalMultilinearSeries ℂ ℂ ℂ) (l : ℂ) (n : ℕ) :
    ‖schroederSeries p l (n+2)‖ ≤ ‖(l^(n+2)-l)⁻¹‖ *
      (∑ c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset),
         ‖p c.length‖ * ∏ j, ‖schroederSeries p l (c.blocksFun j)‖) := by
  classical
  -- For a summand in the recursion every block of the composition has
  -- size strictly smaller than the parent.  Thus the cutoff series used to
  -- make the recursion well-founded agrees with the final series there.
  let q : FormalMultilinearSeries ℂ ℂ ℂ :=
    fun k => if k < n+2 then schroederSeries p l k else 0
  have hblocks : ∀ c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset),
      ∀ j, c.blocksFun j < n+2 := by
    intro c hc
    have N : 0 < n+2 := by omega
    -- the same elementary observation about a nonsingle composition that
    -- occurs in `schroeder_trunc_sum`.
    have hc' : 1 < c.length := by
      simpa using (show c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset) from hc)
    -- `blocksFun` for a nonsingle composition never equals the whole sum.
    intro j
    have H : ∀ k, c.blocksFun k < n + 2 := by
      simp [← Composition.ne_single_iff N, Composition.eq_single_iff_length,
        ne_of_gt hc']
    exact H j
  -- unfold the defining coefficient
  rw [schroederSeries]
  change ‖(l ^ (n + 2) - l)⁻¹ •
      (∑ c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset),
          p.compAlongComposition q c)‖ ≤ _
  rw [norm_smul]
  gcongr
  -- a norm of a sum is bounded by the sum of the bounds for each term
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro c hc
  refine (compAlongComposition_norm p q c).trans ?_
  -- On a block in this set the cutoff has disappeared.
  have h : ∀ j, ‖q (c.blocksFun j)‖ = ‖schroederSeries p l (c.blocksFun j)‖ := by
    intro j
    have hj := hblocks c hc j
    simp [q, hj]
  simp_rw [h]
  exact le_rfl


/-- A purely numerical (nonnegative, when the input data are) majorant
sequence.  `a k` is a bound for the `k`th coefficient of the original
series, and `d m` the inverse small divisor at a vertex of total weight `m`.
The cutoff is only there to present a well-founded definition; the next
lemma removes it on every actual summand. -/
noncomputable def schroederMajorant (a d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n+2 =>
    let b : ℕ → ℝ := fun k => if k < n+2 then schroederMajorant a d k else 0
    d (n+2) *
      (∑ c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset),
          a c.length * ∏ j, b (c.blocksFun j))

@[simp] lemma schroederMajorant_zero (a d : ℕ → ℝ) :
    schroederMajorant a d 0 = 0 := by rw [schroederMajorant]
@[simp] lemma schroederMajorant_one (a d : ℕ → ℝ) :
    schroederMajorant a d 1 = 1 := by rw [schroederMajorant]

lemma comp_blocks_lt {n : ℕ} (hn : 0 < n) (c : Composition n) (hc : 1 < c.length) :
    ∀ j, c.blocksFun j < n := by
  simp [← Composition.ne_single_iff hn, Composition.eq_single_iff_length,
    ne_of_gt hc]

/-- The cutoff in `schroederMajorant` is immaterial: every son in a
nonlinear composition is a strictly smaller natural number. -/
lemma schroederMajorant_rec (a d : ℕ → ℝ) (n : ℕ) :
    schroederMajorant a d (n+2) =
      d (n+2) *
        (∑ c ∈ ({c : Composition (n+2) | 1 < c.length}.toFinset),
            a c.length * ∏ j, schroederMajorant a d (c.blocksFun j)) := by
  classical
  rw [schroederMajorant]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  have hc' : 1 < c.length := by simpa using hc
  have hb := comp_blocks_lt (by omega : 0 < n+2) c hc'
  congr 1
  -- evaluate the cutoff on every block
  apply Finset.prod_congr rfl
  intro j hj
  simp [hb]

/-- Positivity of the numerical majorant.  Stating it explicitly makes
later coefficient comparisons use only order arithmetic on real numbers. -/
lemma schroederMajorant_nonneg
    {a d : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, 0 ≤ d k) :
    ∀ n, 0 ≤ schroederMajorant a d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n IH =>
    rcases n with (_|_|m)
    · simp
    · simp
    · rw [schroederMajorant_rec]
      have hterm : ∀ c ∈ ({c : Composition (m+2) | 1 < c.length}.toFinset),
          0 ≤ a c.length * ∏ j, schroederMajorant a d (c.blocksFun j) := by
        intro c hc
        apply mul_nonneg (ha _) ?_
        apply Finset.prod_nonneg
        intro j hj
        apply IH
        have hc' : 1 < c.length := by simpa using hc
        exact comp_blocks_lt (by omega : 0 < m+2) c hc' j
      exact mul_nonneg (hd _) (Finset.sum_nonneg hterm)

/-- The numerical recursion majorizes the norms of the coefficients of the
formal Schroeder series.  No arithmetic input about the small divisors is
used here; this separates the analytic/composition bookkeeping from the
Siegel estimate on trees. -/
lemma schroederSeries_le_majorant
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (l : ℂ)
    (a d : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, 0 ≤ d k)
    (hp : ∀ k, ‖p k‖ ≤ a k)
    (hdiv : ∀ k, ‖(l^k-l)⁻¹‖ ≤ d k) :
    ∀ n, ‖schroederSeries p l n‖ ≤ schroederMajorant a d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n IH =>
    rcases n with (_|_|m)
    · simp [schroederSeries_zero]
    · -- degree one is the identity in both definitions; its norm is one
      rw [schroederSeries_one, schroederMajorant_one]
      -- the scalar identity multilinear map has norm exactly one
      -- `mkPiAlgebraFin` is an isometry in dimension one.
      -- It suffices here to use the norm bound by one.
      simpa using (ContinuousMultilinearMap.norm_mkPiAlgebraFin ℂ 1 ℂ)
    · -- recursion inequalities and the inductive hypotheses on every block
      rw [schroederMajorant_rec]
      calc
        ‖schroederSeries p l (m+2)‖
            ≤ ‖(l^(m+2)-l)⁻¹‖ *
                (∑ c ∈ ({c : Composition (m+2) | 1 < c.length}.toFinset),
                   ‖p c.length‖ * ∏ j, ‖schroederSeries p l (c.blocksFun j)‖) :=
              schroederSeries_norm_rec p l m
        _ ≤ d (m+2) *
                (∑ c ∈ ({c : Composition (m+2) | 1 < c.length}.toFinset),
                   a c.length * ∏ j, schroederMajorant a d (c.blocksFun j)) := by
              have hqnon := schroederMajorant_nonneg ha hd
              -- First the factor at the root, then each term and each block.
              apply mul_le_mul (hdiv _) ?_ ?_ (hd _)
              · apply Finset.sum_le_sum
                intro c hc
                apply mul_le_mul (hp _) ?_ ?_ (ha _)
                · apply Finset.prod_le_prod
                  · intro j hj
                    exact norm_nonneg _
                  · intro j hj
                    apply IH
                    have hc' : 1 < c.length := by simpa using hc
                    exact comp_blocks_lt (by omega : 0 < m+2) c hc' j
                · apply Finset.prod_nonneg
                  intro j hj
                  exact norm_nonneg _
              · -- the left-hand finite sum is a sum of nonnegative products
                apply Finset.sum_nonneg
                intro c hc
                apply mul_nonneg (norm_nonneg _) ?_
                apply Finset.prod_nonneg
                intro j hj
                exact norm_nonneg _
end PoincareSiegelSupport

namespace PoincareSiegelSupport
open FormalMultilinearSeries

/-- A bounded geometric majorant is enough for a positive convergence radius.
This converse to `le_mul_pow_of_radius_pos` is convenient once all the
coefficient estimates have been reduced to numbers. -/
lemma radius_pos_of_le_mul_pow
    {q : FormalMultilinearSeries ℂ ℂ ℂ}
    {K S : ℝ} (hK : 0 ≤ K) (hS : 0 < S)
    (hq : ∀ n : ℕ, ‖q n‖ ≤ K * S^n) :
    0 < q.radius := by
  let rR : ℝ := (2*S)⁻¹
  have hrR : 0 < rR := by
    dsimp [rR]
    positivity
  let r : NNReal := ⟨rR, hrR.le⟩
  have hr : 0 < r := by
    exact hrR
  have hbound : ∀ n : ℕ, ‖q n‖ * (r:ℝ)^n ≤ K := by
    intro n
    calc
      ‖q n‖ * (r:ℝ)^n ≤ (K * S^n) * (r:ℝ)^n := by
        exact mul_le_mul_of_nonneg_right (hq n) (by positivity)
      _ = K * ((1/2:ℝ)^n) := by
        change (K * S^n) * ( (2*S)⁻¹)^n = _
        have hS0 : S ≠ 0 := ne_of_gt hS
        -- collect powers first
        rw [mul_assoc, ← mul_pow]
        have h : S * (2*S)⁻¹ = (1/2:ℝ) := by
          field_simp
          <;> ring
        rw [h]
      _ ≤ K := by
        have hpow : (1 / 2 : ℝ)^n ≤ 1 := by
          have : (0:ℝ) ≤ 1/2 := by norm_num
          exact pow_le_one₀ this (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left hpow hK]
  have H : (r : ENNReal) ≤ q.radius :=
    q.le_radius_of_bound K hbound
  exact lt_of_lt_of_le (by simpa using hr : (0:ENNReal) < r) H
end PoincareSiegelSupport
namespace PoincareSiegelSupport
open FormalMultilinearSeries Finset

/-- The composition-count part of the tree majorant (all small divisors
replaced by one) already has a positive convergence radius.  This is the
same elementary scalar majorant used for the analytic inverse theorem. -/
lemma schroederMajorant_one_aux
    (aSeq : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ aSeq k)
    {C r t : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (ha : ∀ k, aSeq k ≤ C * r^k)
    (n : ℕ) (hn : 2 ≤ n+1) :
    ∑ k ∈ Ico 1 (n+1), t^k * schroederMajorant aSeq (fun _ => 1) k ≤
      t + C * ∑ k ∈ Ico 2 (n+1),
        (r * ∑ j ∈ Ico 1 n,
          t^j * schroederMajorant aSeq (fun _ => 1) j)^k := by
  classical
  let b := schroederMajorant aSeq (fun _ => 1)
  have hb : ∀ j, 0 ≤ b j :=
    schroederMajorant_nonneg ha0 (by intro k; norm_num)
  change (∑ k ∈ Ico 1 (n+1), t^k * b k) ≤ _
  calc
    ∑ k ∈ Ico 1 (n+1), t^k * b k =
        t + ∑ k ∈ Ico 2 (n+1), t^k * b k := by
          -- split off the singleton `[1,2)` exactly as in the inverse
          -- series estimate
          simp only [show Ico (1:ℕ) 2 = {1} from Nat.Ico_succ_singleton 1,
            Finset.sum_singleton, b, schroederMajorant_one, pow_one,
            mul_one, ← Finset.sum_Ico_consecutive _ (by omega : (1:ℕ) ≤ 2) hn]
    _ = t + ∑ k ∈ Ico 2 (n+1), t^k *
          (∑ c ∈ ({c : Composition k | 1 < c.length}.toFinset),
              aSeq c.length * ∏ j, b (c.blocksFun j)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          have hk2 := (mem_Ico.1 hk).1
          obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 2 := by
            refine ⟨k-2, ?_⟩
            omega
          -- k = m+2, exactly the recursive coefficient
          apply congrArg (fun x : ℝ => t^(m+2) * x)
          simpa [b] using
            (schroederMajorant_rec aSeq (fun _ : ℕ => (1:ℝ)) m)
    _ ≤ t + ∑ k ∈ Ico 2 (n+1),
          t^k * (C *
            ∑ c ∈ ({c : Composition k | 1 < c.length}.toFinset),
              r^c.length * ∏ j, b (c.blocksFun j)) := by
          apply add_le_add_right ?_ t
          apply Finset.sum_le_sum
          intro k hk
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc
            (∑ c ∈ ({c : Composition k | 1 < c.length}.toFinset),
              aSeq c.length * ∏ j, b (c.blocksFun j))
                ≤ ∑ c ∈ ({c : Composition k | 1 < c.length}.toFinset),
                    (C * r^c.length) * ∏ j, b (c.blocksFun j) := by
                      apply Finset.sum_le_sum
                      intro c hc
                      apply mul_le_mul_of_nonneg_right (ha _) ?_
                      apply Finset.prod_nonneg
                      intro j hj
                      exact hb _
            _ = C * ∑ c ∈ ({c : Composition k | 1 < c.length}.toFinset),
                    r^c.length * ∏ j, b (c.blocksFun j) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro c hc
                      ring
    _ = t + C * (∑ k ∈ Ico 2 (n+1), t^k *
            ∑ c ∈ ({c : Composition k | 1 < c.length}.toFinset),
              r^c.length * ∏ j, b (c.blocksFun j)) := by
          congr 1
          rw [Finset.mul_sum]
          -- put the common scalar `C` in front
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ ≤ t + C * ∑ k ∈ Ico 2 (n+1),
        (r * ∑ j ∈ Ico 1 n, t^j * b j)^k := by
          apply add_le_add_right ?_ t
          apply mul_le_mul_of_nonneg_left ?_ hC
          have H := radius_right_inv_pos_of_radius_pos_aux1 n b hb hr ht
          simpa [mul_pow] using H
end PoincareSiegelSupport

namespace PoincareSiegelSupport
open FormalMultilinearSeries Finset
open Filter
open scoped Topology

lemma schroederMajorant_one_exp
    (aSeq : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ aSeq k)
    {C r : ℝ} (hC : 0 < C) (hr : 0 < r)
    (ha : ∀ k, aSeq k ≤ C * r^k) :
    ∃ K S : ℝ, 0 ≤ K ∧ 0 < S ∧
      ∀ n, schroederMajorant aSeq (fun _ => 1) n ≤ K * S^n := by
  classical
  let b := schroederMajorant aSeq (fun _ => 1)
  have hb : ∀ j, 0 ≤ b j :=
    schroederMajorant_nonneg ha0 (by intro k; norm_num)
  -- choose a small bookkeeping variable for the scalar majorant
  obtain ⟨t, ht, ht1, ht2⟩ :
      ∃ t : ℝ, 0 < t ∧ 8*C*r^2*t ≤ 1 ∧ r*2*t ≤ 1/2 := by
    have T : Tendsto (fun t : ℝ => 8*C*r^2*t) (𝓝 0)
        (𝓝 (8*C*r^2*0)) := tendsto_const_nhds.mul tendsto_id
    have A : ∀ᶠ t in 𝓝 0, 8*C*r^2*t < 1 := by
      apply (tendsto_order.1 T).2
      norm_num
    have T' : Tendsto (fun t : ℝ => r*2*t) (𝓝 0)
        (𝓝 (r*2*0)) := tendsto_const_nhds.mul tendsto_id
    have B : ∀ᶠ t in 𝓝 0, r*2*t < 1/2 := by
      apply (tendsto_order.1 T').2
      norm_num
    have Pos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := by
      filter_upwards [self_mem_nhdsWithin] with t ht using ht
    rcases (Pos.and ((A.and B).filter_mono inf_le_left)).exists with ⟨t, H⟩
    exact ⟨t, H.1, H.2.1.le, H.2.2.le⟩
  let Ssum (n : ℕ) := ∑ k ∈ Ico 1 n, t^k * b k
  have hS0 : ∀ n, 0 ≤ Ssum n := by
    intro n
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (by positivity) (hb _)
  have hSn : ∀ n, 1 ≤ n → Ssum n ≤ 2*t := by
    apply Nat.le_induction
    · simp [Ssum, ht.le]
    · intro n hn ih
      have hn2 : 2 ≤ n+1 := by omega
      have hrs : r * Ssum n ≤ 1/2 :=
        calc
          r * Ssum n ≤ r * (2*t) := by gcongr
          _ ≤ 1/2 := by simpa [mul_assoc] using ht2
      calc
        Ssum (n+1) ≤ t + C * ∑ k ∈ Ico 2 (n+1),
            (r * Ssum n)^k := by
              -- this is the numerical composition lemma
              exact schroederMajorant_one_aux aSeq ha0 hC.le hr.le ht.le ha n hn2
        _ = t + C *
              (((r*Ssum n)^2 - (r*Ssum n)^(n+1)) / (1-r*Ssum n)) := by
              rw [geom_sum_Ico' _ hn2]
              exact ne_of_lt (hrs.trans_lt (by norm_num))
        _ ≤ t + C * (((r*Ssum n)^2) / (1/2)) := by
              gcongr
              · simp only [sub_le_self_iff]
                exact pow_nonneg (mul_nonneg hr.le (hS0 n)) _
              · linarith only [hrs]
        _ = t + 2*C*(r*Ssum n)^2 := by ring
        _ ≤ t + 2*C*(r*(2*t))^2 := by
              have hnon : 0 ≤ r * Ssum n := mul_nonneg hr.le (hS0 n)
              have hnon' : 0 ≤ r * (2*t) := by positivity
              gcongr
        _ = (1 + 8*C*r^2*t)*t := by ring
        _ ≤ 2*t := by nlinarith
  refine ⟨2*t, t⁻¹, (by positivity), (by positivity), ?_⟩
  intro n
  rcases n with (_|n)
  · simp [b, schroederMajorant_zero, ht.le]
  · have hmem : n+1 ∈ Ico 1 (n+2) := mem_Ico.2 (by omega)
    have hterm : t^(n+1) * b (n+1) ≤ Ssum (n+2) :=
      Finset.single_le_sum (f := fun i => t^i * b i)
        (fun i hi => mul_nonneg (by positivity) (hb _)) hmem
    have H : t^(n+1) * b (n+1) ≤ 2*t :=
      hterm.trans (hSn (n+2) (by omega))
    have htPow : 0 < t^(n+1) := pow_pos ht _
    have H' : b (n+1) ≤ (2*t) * (t⁻¹)^(n+1) := by
      calc
        b (n+1) ≤ (2*t) / t^(n+1) :=
          (le_div_iff₀ htPow).2 (by simpa [mul_comm] using H)
        _ = (2*t) * (t⁻¹)^(n+1) := by
          rw [inv_pow]
          ring
    exact H'
end PoincareSiegelSupport

-- END INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Majorant.lean

-- BEGIN INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Numeric.lean
namespace PoincareSiegelSupport
open scoped BigOperators
open Finset

/-- finite ordered rooted trees.  Leaves have weight one; the predicate `Good`
    below rules out unary (and nullary) internal nodes. Using `Fin k` at a
    node gives a particularly convenient induction principle. -/
inductive SqrtTree where
  | leaf : SqrtTree
  | node (k : ℕ) (ch : Fin k → SqrtTree) : SqrtTree

namespace SqrtTree

def weight : SqrtTree → ℕ
  | leaf => 1
  | node _ ch => ∑ i, weight (ch i)
@[simp] lemma weight_leaf : weight leaf = 1 := rfl
@[simp] lemma weight_node (k) (ch) : weight (node k ch) = ∑ i, weight (ch i) := rfl

def Good : SqrtTree → Prop
  | leaf => True
  | node k ch => 2 ≤ k ∧ ∀ i, Good (ch i)
@[simp] lemma good_leaf : Good leaf := trivial
@[simp] lemma good_node {k} {ch : Fin k → SqrtTree} :
    Good (node k ch) ↔ 2 ≤ k ∧ ∀ i, Good (ch i) := Iff.rfl

lemma weight_pos : ∀ t : SqrtTree, Good t → 0 < weight t := by
  intro t
  induction t with
  | leaf => intro; simp
  | node k ch ih =>
    intro ht
    have hk : 2 ≤ k := ht.1
    -- one may sum the positive child weights
    have hpos : ∀ i : Fin k, 0 < weight (ch i) :=
      fun i => ih i (ht.2 i)
    haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    let i0 : Fin k := ⟨0, by omega⟩
    have : 0 < ∑ i : Fin k, weight (ch i) :=
      Finset.sum_pos' (fun i _ => Nat.zero_le _) (by
        refine ⟨i0, Finset.mem_univ _, hpos _⟩)
    simpa using this

/-- Every son of a good (non-leaf) node has smaller weight. -/
lemma child_lt {k : ℕ} {ch : Fin k → SqrtTree}
    (h : Good (node k ch)) (i : Fin k) :
    weight (ch i) < weight (node k ch) := by
  have hk := h.1
  have hpos : ∀ a : Fin k, 0 < weight (ch a) :=
    fun a => weight_pos _ (h.2 a)
  -- pick a second son
  let j : Fin k := if hi : i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hji : j ≠ i := by
    dsimp [j]
    split_ifs with hi
    · intro e
      have : (1:ℕ) = i.val := congrArg Fin.val e
      omega
    · intro e
      have : (0:ℕ) = i.val := congrArg Fin.val e
      exact hi this.symm
  have hh : weight (ch i) < ∑ a : Fin k, weight (ch a) :=
    Finset.single_lt_sum (f := fun a => weight (ch a)) hji (Finset.mem_univ _) (Finset.mem_univ _)
      (hpos j) (by intro b hb hb'; exact Nat.zero_le _)
  simpa using hh

/-- List of weights of the topmost `bad` roots in a tree.  This little
    pruning operation makes the usual Siegel counting lemma painless: below
    a bad root only topmost bad sons matter. -/
def tops (bad : ℕ → Prop) [DecidablePred bad] : SqrtTree → List ℕ
  | leaf => if bad 1 then [1] else []
  | node k ch =>
      if bad (weight (node k ch)) then [weight (node k ch)]
      else (List.ofFn (fun i => tops bad (ch i))).flatten

def bcount (bad : ℕ → Prop) [DecidablePred bad] : SqrtTree → ℕ
  | leaf => if bad 1 then 1 else 0
  | node k ch => (if bad (weight (node k ch)) then 1 else 0)
                    + ∑ i, bcount bad (ch i)

@[simp] lemma tops_leaf (bad : ℕ → Prop) [DecidablePred bad] :
    tops bad leaf = if bad 1 then [1] else [] := rfl
@[simp] lemma bcount_leaf (bad : ℕ → Prop) [DecidablePred bad] :
    bcount bad leaf = if bad 1 then 1 else 0 := rfl
lemma tops_node (bad : ℕ → Prop) [DecidablePred bad] (k) (ch : Fin k → SqrtTree) :
    tops bad (node k ch) =
      if bad (weight (node k ch)) then [weight (node k ch)]
      else (List.ofFn (fun i => tops bad (ch i))).flatten := rfl
lemma bcount_node (bad : ℕ → Prop) [DecidablePred bad] (k) (ch : Fin k → SqrtTree) :
    bcount bad (node k ch) =
      (if bad (weight (node k ch)) then 1 else 0) +
        ∑ i, bcount bad (ch i) := rfl

lemma mem_tops_bad {bad : ℕ → Prop} [DecidablePred bad]
    {t : SqrtTree} {x : ℕ} (hx : x ∈ tops bad t) : bad x := by
  induction t with
  | leaf =>
    by_cases h : bad 1
    · have e : x = 1 := by simpa [tops_leaf, h] using hx
      simpa [e] using h
    · simp [tops_leaf, h] at hx
  | node k ch ih =>
    rw [tops_node] at hx
    by_cases h : bad (weight (.node k ch))
    · rw [if_pos h] at hx
      have e : x = weight (.node k ch) := by simpa using hx
      simpa [e] using h
    · rw [if_neg h] at hx
      obtain ⟨l, hl, hh⟩ := List.mem_flatten.mp hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      exact ih i hh

/-- Pruned top roots have total mass at most the mass of the tree. -/
lemma sum_tops_le {bad : ℕ → Prop} [DecidablePred bad] :
    ∀ t, (tops bad t).sum ≤ weight t := by
  intro t
  induction t with
  | leaf =>
    by_cases h : bad 1 <;> simp [tops_leaf, h]
  | node k ch ih =>
    rw [tops_node]
    by_cases hb : bad (weight (.node k ch))
    · have hb' : bad (∑ i, weight (ch i)) := by simpa using hb
      simp [hb']
    · simp only [weight_node] at hb ⊢
      rw [if_neg hb]
      rw [List.sum_flatten]
      simpa [List.sum_ofFn, weight_node] using
        (Finset.sum_le_sum (fun i hi => ih i))

-- Real weight attached to a list of natural masses.
noncomputable def topValue (L : ℝ) (xs : List ℕ) : ℝ :=
  2*(xs.sum:ℕ)/L - (xs.length:ℕ)

lemma topValue_nil (L : ℝ) : topValue L [] = 0 := by simp [topValue]
@[simp] lemma topValue_single (L : ℝ) (n : ℕ) :
    topValue L [n] = 2*(n:ℝ)/L - 1 := by simp [topValue]
lemma topValue_append (L : ℝ) (xs ys : List ℕ) :
    topValue L (xs ++ ys) = topValue L xs + topValue L ys := by
  simp [topValue, List.sum_append, List.length_append, Nat.cast_add]; ring
lemma topValue_flatten (L : ℝ) (ls : List (List ℕ)) :
    topValue L ls.flatten = (ls.map (topValue L)).sum := by
  induction ls with
  | nil => simp [topValue_nil]
  | cons x xs ih => simp [topValue_append, ih]
lemma topValue_ofFn {k} (L : ℝ) (f : Fin k → List ℕ) :
    topValue L (List.ofFn f).flatten = ∑ i, topValue L (f i) := by
  rw [topValue_flatten]
  rw [List.map_ofFn]
  exact (List.sum_ofFn (f := fun i : Fin k => topValue L (f i)))

/-- The elementary forest count.  If bad labels are at least `L`, and two
    bad ancestors differ by at least `L`, a good tree of mass `n` contains at
    most `2n/L` bad vertices. The stronger pruned-list form is what makes the
    single-son case work. -/
lemma forest_aux (bad : ℕ → Prop) [DecidablePred bad]
    (h1 : ¬ bad 1) {L : ℝ} (hL : 0 < L)
    (hmin : ∀ {n}, bad n → L ≤ (n:ℝ))
    (hgap : ∀ {a b}, bad a → bad b → b < a → L ≤ (a:ℝ) - b) :
    ∀ t : SqrtTree, Good t →
      (bcount bad t : ℝ) ≤ topValue L (tops bad t) := by
  intro t
  induction t with
  | leaf =>
    intro ht
    simp [tops_leaf, bcount_leaf, h1, topValue]
  | node k ch ih =>
    intro ht
    have hk : 2 ≤ k := ht.1
    have hg : ∀ i, Good (ch i) := ht.2
    rw [bcount_node, tops_node]
    by_cases hb : bad (weight (.node k ch))
    · rw [if_pos hb, if_pos hb, topValue_single]
      push_cast
      let ys : List ℕ := (List.ofFn (fun i => tops bad (ch i))).flatten
      have hchild : (∑ i, (bcount bad (ch i) : ℝ)) ≤ topValue L ys := by
        dsimp [ys]
        rw [topValue_ofFn]
        exact Finset.sum_le_sum (fun i hi => ih i (hg i))
      have hs : ys.sum ≤ weight (.node k ch) := by
        dsimp [ys]
        rw [List.sum_flatten]
        simpa [List.sum_ofFn, weight_node] using
          (Finset.sum_le_sum (fun i hi => sum_tops_le (bad:=bad) (ch i)))
      have hbadlt : ∀ b ∈ ys, bad b ∧ b < weight (.node k ch) := by
        intro b hm
        have H : b ∈ (List.ofFn (fun i => tops bad (ch i))).flatten := hm
        obtain ⟨l, hl, hbl⟩ := List.mem_flatten.mp H
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hl
        subst l
        refine ⟨mem_tops_bad hbl, ?_⟩
        have ble : b ≤ weight (ch i) :=
          (List.le_sum_of_mem hbl).trans (sum_tops_le (bad:=bad) (ch i))
        exact lt_of_le_of_lt ble (child_lt ht i)
      have Htop : 1 + topValue L ys ≤ 2*(weight (.node k ch):ℝ)/L - 1 := by
        rcases eys : ys with _ | ⟨b, bs⟩
        · rw [topValue_nil]
          have mn := hmin hb
          have rat : (2:ℝ) ≤ 2*(weight (.node k ch):ℝ)/L := by
            apply (le_div_iff₀ hL).2
            nlinarith
          linarith
        · rcases bs with _ | ⟨c, cs⟩
          · rw [topValue_single]
            have blt := hbadlt b (by simpa [eys])
            have gap := hgap hb blt.1 blt.2
            have rat : (2:ℝ) ≤
                2*((weight (.node k ch):ℝ) - (b:ℝ))/L := by
              apply (le_div_iff₀ hL).2
              nlinarith
            have eqn : 2*((weight (.node k ch):ℝ) - (b:ℝ))/L =
                2*(weight (.node k ch):ℝ)/L - 2*(b:ℝ)/L := by ring
            rw [eqn] at rat
            linarith
          · unfold topValue
            have hs' : (b :: c :: cs).sum ≤ weight (.node k ch) := by
              simpa [eys] using hs
            have castle : (((b :: c :: cs).sum : ℕ) : ℝ) ≤
                (weight (.node k ch):ℝ) := by
                  exact_mod_cast hs'
            have len2 : (2:ℝ) ≤ ((b :: c :: cs).length : ℕ) := by
              push_cast
              have hn0 : (0:ℝ) ≤ (cs.length:ℝ) := by positivity
              simp
              linarith
            have rat : (2*(((b :: c :: cs).sum : ℕ):ℝ))/L ≤
                2*(weight (.node k ch):ℝ)/L := by
              apply (div_le_div_iff_of_pos_right hL).2
              nlinarith
            linarith
      calc
        1 + ∑ x, (bcount bad (ch x) : ℝ)
            ≤ 1 + topValue L ys := by linarith
        _ ≤ _ := Htop
    · rw [if_neg hb, if_neg hb]
      push_cast
      simp only [Nat.cast_zero, zero_add]
      rw [topValue_ofFn]
      exact Finset.sum_le_sum (fun i hi => ih i (hg i))

lemma forest_count (bad : ℕ → Prop) [DecidablePred bad]
    (h1 : ¬ bad 1) {L : ℝ} (hL : 0 < L)
    (hmin : ∀ {n}, bad n → L ≤ (n:ℝ))
    (hgap : ∀ {a b}, bad a → bad b → b < a → L ≤ (a:ℝ) - b) :
    ∀ t : SqrtTree, Good t →
      (bcount bad t : ℝ) ≤ 2*(weight t:ℝ)/L := by
  intro t hg
  have A := forest_aux bad h1 hL hmin hgap t hg
  have hs := sum_tops_le (bad:=bad) t
  calc
    (bcount bad t:ℝ) ≤ topValue L (tops bad t) := A
    _ ≤ 2*(weight t:ℝ)/L := by
      unfold topValue
      have castle : ((tops bad t).sum : ℝ) ≤ (weight t:ℝ) := by exact_mod_cast hs
      have lenpos : 0 ≤ ((tops bad t).length : ℝ) := by positivity
      have rat : (2*((tops bad t).sum : ℕ))/L ≤ 2*(weight t:ℝ)/L := by
        apply (div_le_div_iff_of_pos_right hL).2
        nlinarith
      linarith

end SqrtTree
end PoincareSiegelSupport

namespace PoincareSiegelSupport
-- convenient arithmetic ingredients for using `forest_count`
lemma unit_pow_sub_self_norm (l : ℂ) (hl : ‖l‖ = 1) (n : ℕ) (hn : 1 ≤ n) :
    ‖l^n - l‖ = ‖l^(n-1) - 1‖ := by
  have rep : n - 1 + 1 = n := by omega
  have fact : l^n - l = (l^(n-1) - 1) * l := by
    calc
      l^n - l = l^(n-1) * l - l := by rw [← pow_succ, rep]
      _ = (l^(n-1)-1)*l := by ring
  rw [fact, norm_mul, hl, mul_one]

lemma unit_sub_gap {l : ℂ} (hl : ‖l‖ = 1) {r s : ℕ} (hs : s ≤ r) :
    ‖l^(r-s) - 1‖ ≤ ‖l^r-1‖ + ‖l^s-1‖ := by
  have rep : r-s+s=r := by omega
  have id : (l^r-1) - (l^s-1) = (l^(r-s)-1)*l^s := by
    calc
      (l^r-1) - (l^s-1) = l^r - l^s := by ring
      _ = (l^(r-s)-1)*l^s := by rw [mul_sub_right_distrib, ← pow_add, rep]; ring
  have hn : ‖(l^(r-s)-1)*l^s‖ = ‖l^(r-s)-1‖ := by
    rw [norm_mul, norm_pow, hl, one_pow, mul_one]
  rw [← hn, ← id]
  exact norm_sub_le _ _

/-- It is harmless (and useful) to replace the real Diophantine exponent by a
larger positive integer. This lemma is deliberately very weak, but every
constant here is uniform in `q`. -/
lemma weak_integer_lower
    {l : ℂ} {C τ : ℝ} (hC : 0 < C)
    (h : ∀ n : ℕ, n ≠ 0 →
      4 * (n:ℝ) * (C / (n:ℝ)^τ) ≤ ‖l^n-1‖) :
    ∃ s : ℕ, 1 ≤ s ∧ ∀ n : ℕ, n ≠ 0 →
      C / (n:ℝ)^s ≤ ‖l^n-1‖ := by
  obtain ⟨s, hs⟩ := exists_nat_gt (max τ 0)
  have s0 : 1 ≤ s := by
    have : (0:ℝ) < s := lt_of_le_of_lt (le_max_right _ _) hs
    exact_mod_cast (Nat.pos_of_ne_zero (by intro e; simp [e] at this))
  refine ⟨s, s0, ?_⟩
  intro n hn
  have xn : (1:ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have st : τ ≤ (s:ℝ) := (le_max_left _ _).trans hs.le
  have pw : (n:ℝ)^τ ≤ (n:ℝ)^s := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le xn st
  have posτ : 0 < (n:ℝ)^τ := Real.rpow_pos_of_pos (by positivity) _
  have poss : 0 < (n:ℝ)^s := by positivity
  calc
    C / (n:ℝ)^s ≤ C / (n:ℝ)^τ := by
      exact (div_le_div_iff_of_pos_left hC poss posτ).2 pw
    _ ≤ 4*(n:ℝ)*(C/(n:ℝ)^τ) := by
      have p : 0 ≤ C/(n:ℝ)^τ := (div_pos hC posτ).le
      nlinarith
    _ ≤ _ := h n hn


end PoincareSiegelSupport

-- END INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Numeric.lean

-- BEGIN INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Weighted.lean
namespace PoincareSiegelSupport
open scoped BigOperators
open Finset
namespace SqrtTree

/-- product of the numerical divisors at the internal vertices -/
def dvalue (d : ℕ → ℝ) : SqrtTree → ℝ
 | .leaf => 1
 | .node k ch => d (weight (.node k ch)) * ∏ i, dvalue d (ch i)

/-- number of internal vertices -/
def vertices : SqrtTree → ℕ
 | .leaf => 0
 | .node k ch => 1 + ∑ i, vertices (ch i)

lemma weight_le_of_child {k} {ch : Fin k → SqrtTree} (i : Fin k) :
    weight (ch i) ≤ weight (.node k ch) := by
  classical
  -- it is one of the summands
  simpa [weight] using (Finset.single_le_sum (s:=(Finset.univ : Finset (Fin k)))
    (f:=fun j : Fin k => weight (ch j)) (fun j hj => Nat.zero_le _) (Finset.mem_univ i))

lemma weight_ge_two_node {k} {ch : Fin k → SqrtTree}
    (h : Good (.node k ch)) : 2 ≤ weight (.node k ch) := by
  classical
  have pos : ∀ i : Fin k, 1 ≤ weight (ch i) := fun i => (weight_pos _ (h.2 i))
  have hs : k ≤ ∑ i : Fin k, weight (ch i) := by
    simpa using (Finset.sum_le_sum (s:= (Finset.univ : Finset (Fin k)))
      (fun i hi => pos i))
  exact h.1.trans (by simpa using hs)

lemma vertices_lt_weight : ∀ t : SqrtTree, Good t → vertices t < weight t := by
  intro t ht
  induction t with
  | leaf => simp [vertices]
  | node k ch ih =>
    classical
    have hk : 2 ≤ k := ht.1
    have child : ∀ i, vertices (ch i) < weight (ch i) := fun i => ih i (ht.2 i)
    have hle : ∑ i : Fin k, (vertices (ch i) + 1) ≤
          ∑ i : Fin k, weight (ch i) := by
      exact Finset.sum_le_sum (fun i hi => child i)
    have heq : (∑ i : Fin k, (vertices (ch i) + 1)) =
          (∑ i : Fin k, vertices (ch i)) + k := by simp [Finset.sum_add_distrib]
    simp only [weight_node, vertices] at *
    rw [heq] at hle
    omega

lemma vertices_le_weight {t : SqrtTree} (h : Good t) : vertices t ≤ weight t :=
  (vertices_lt_weight t h).le

end SqrtTree
end PoincareSiegelSupport

namespace PoincareSiegelSupport
open scoped BigOperators
open Finset
open SqrtTree

/-- vertices whose divisor lies above the `j`th dyadic level.  We use a
slightly bigger first level (`2/C`, and at least one); a larger level only
improves the separation lemma. -/
def dyBad (d : ℕ → ℝ) (B q : ℝ) (j n : ℕ) : Prop :=
  2 ≤ n ∧ B * q^j < d n
noncomputable instance (d : ℕ → ℝ) (B q : ℝ) (j : ℕ) : DecidablePred (dyBad d B q j) :=
  Classical.decPred _

lemma pow_two_natCast (s j : ℕ) :
    ((2:ℝ)^s)^j = ((2:ℝ)^j)^s := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
lemma pow_mul_two (s j : ℕ) :
    (2:ℝ)^(s*j) = ((2:ℝ)^j)^s := by rw [← pow_mul, Nat.mul_comm]

/-- The elementary gap lemma. This is the only place where the unit complex
number enters the tree estimate. -/
lemma dyBad_count
    {l : ℂ} (hl : ‖l‖ = 1) {C : ℝ} (hC : 0 < C)
    {s : ℕ} (hs : 1 ≤ s)
    (d : ℕ → ℝ)
    (hdrel : ∀ n : ℕ, 2 ≤ n → d n = (‖l^(n-1)-1‖)⁻¹)
    (hpoly : ∀ n : ℕ, 2 ≤ n → d n ≤ C⁻¹ * ((n-1:ℕ):ℝ)^s)
    (hlow : ∀ n : ℕ, n ≠ 0 → C / (n:ℝ)^s ≤ ‖l^n-1‖)
    (B : ℝ) (hB : 2 * C⁻¹ ≤ B) :
    let q : ℝ := (2:ℝ)^s
    ∀ j : ℕ, ∀ t : SqrtTree, SqrtTree.Good t →
      (SqrtTree.bcount (dyBad d B q j) t : ℝ) ≤
        2 * (SqrtTree.weight t : ℝ) / (2:ℝ)^j := by
  classical
  dsimp
  let q : ℝ := (2:ℝ)^s
  have qpos : 0 < q := by dsimp [q]; positivity
  have Bpos : 0 < B := lt_of_lt_of_le (by
      have : 0 < C⁻¹ := by positivity
      nlinarith) hB
  intro j
  have Lpos : 0 < (2:ℝ)^j := by positivity
  have nob : ¬ dyBad d B q j 1 := by simp [dyBad]
  apply SqrtTree.forest_count (dyBad d B q j) nob Lpos
  · -- minimum weight of a marked vertex
    intro n hn
    have hn2 : 2 ≤ n := hn.1
    have hdn : B * q^j < d n := hn.2
    have upper := hpoly n hn2
    have Cp : 0 < C⁻¹ := by positivity
    -- if n were smaller than 2^j, the polynomial estimate contradicts the choice of B
    by_contra hnot
    have hnle : (n:ℝ) < (2:ℝ)^j := lt_of_not_ge hnot
    have nx : (((n-1:ℕ):ℝ)^s) ≤ (((2:ℝ)^j)^s) := by
      have h1 : ((n-1:ℕ):ℝ) ≤ (2:ℝ)^j := by
        have castsub : ((n-1:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast (Nat.sub_le n 1)
        linarith
      exact pow_le_pow_left₀ (by positivity) h1 _
    have qq : q^j = ((2:ℝ)^j)^s := by dsimp [q]; exact pow_two_natCast s j
    have lowbase : 2 * C⁻¹ * (((2:ℝ)^j)^s) ≤ B * q^j := by
      rw [qq]
      exact mul_le_mul_of_nonneg_right hB (by positivity)
    have u2 : C⁻¹ * (((n-1:ℕ):ℝ)^s) ≤ C⁻¹ * (((2:ℝ)^j)^s) :=
      mul_le_mul_of_nonneg_left nx Cp.le
    have strict : C⁻¹ * (((2:ℝ)^j)^s) < 2 * C⁻¹ * (((2:ℝ)^j)^s) := by
      have : 0 < C⁻¹ * (((2:ℝ)^j)^s) := by positivity
      nlinarith
    linarith
  · -- marked weights on a chain are separated by at least 2^j
    intro a b ha hb hba
    have a2 : 2 ≤ a := ha.1
    have b2 : 2 ≤ b := hb.1
    have da : B * q^j < d a := ha.2
    have db : B * q^j < d b := hb.2
    have Ba : 0 < B * q^j := mul_pos Bpos (pow_pos qpos _)
    -- translate being marked into a small norm
    have apos : 0 < ‖l^(a-1)-1‖ := by
      rw [hdrel a a2] at da
      by_contra z
      have z' : ‖l^(a-1)-1‖ = 0 := le_antisymm (le_of_not_gt z) (norm_nonneg _)
      simp [z'] at da
      linarith
    have bpos : 0 < ‖l^(b-1)-1‖ := by
      rw [hdrel b b2] at db
      by_contra z
      have z' : ‖l^(b-1)-1‖ = 0 := le_antisymm (le_of_not_gt z) (norm_nonneg _)
      simp [z'] at db
      linarith
    have sA : ‖l^(a-1)-1‖ < (B*q^j)⁻¹ := by
      rw [hdrel a a2] at da
      exact (lt_inv_comm₀ apos Ba).2 da
    have sB : ‖l^(b-1)-1‖ < (B*q^j)⁻¹ := by
      rw [hdrel b b2] at db
      exact (lt_inv_comm₀ bpos Ba).2 db
    have suble : b-1 ≤ a-1 := by omega
    have gap := unit_sub_gap (l:=l) hl suble
    have abpos : a-b ≠ 0 := by omega
    have castab : (((a-b):ℕ):ℝ) = (a:ℝ)-b := by
      rw [Nat.cast_sub (Nat.le_of_lt hba)]
    have lower := hlow (a-b) abpos
    have expid : a-1-(b-1) = a-b := by omega
    -- contradiction if gap < 2^j
    by_contra hnot
    have diff_lt : (a:ℝ)-b < (2:ℝ)^j := lt_of_not_ge hnot
    have diffpos : 0 < (a-b:ℕ) := Nat.sub_pos_of_lt hba
    have dle : (((a-b:ℕ):ℝ)^s) ≤ (((2:ℝ)^j)^s) := by
      apply pow_le_pow_left₀ (by positivity) (le_of_lt ?_) _
      rw [castab]
      exact diff_lt
    have dp : 0 < (((a-b:ℕ):ℝ)^s) := by positivity
    have tp : 0 < (((2:ℝ)^j)^s) := by positivity
    have frac : C / (((2:ℝ)^j)^s) ≤ C / ((a-b:ℕ):ℝ)^s := by
      exact (div_le_div_iff_of_pos_left hC tp dp).2 dle
    have up : ‖l^(a-b)-1‖ < 2 * (B*q^j)⁻¹ := by
      rw [← expid]
      calc
        _ ≤ ‖l^(a-1)-1‖ + ‖l^(b-1)-1‖ := gap
        _ < 2 * (B*q^j)⁻¹ := by linarith
    have qq : q^j = ((2:ℝ)^j)^s := by dsimp [q]; exact pow_two_natCast s j
    have invle : 2 * (B*q^j)⁻¹ ≤ C / (((2:ℝ)^j)^s) := by
      rw [qq]
      -- from B ≥ 2/C
      have bp : 0 < B * (((2:ℝ)^j)^s) := by positivity
      have t2 : 2 * C⁻¹ * (((2:ℝ)^j)^s) ≤ B * (((2:ℝ)^j)^s) :=
        mul_le_mul_of_nonneg_right hB (by positivity)
      -- `2/(B*T) ≤ C/T` after multiplication
      -- use `le_div_iff₀` twice
      have : 2 ≤ (C / (((2:ℝ)^j)^s)) * (B * (((2:ℝ)^j)^s)) := by
        -- simplify RHS to C*B
        have cb : 2 ≤ C * B := by
          have := (mul_le_mul_of_nonneg_left hB hC.le)
          -- C*(2*C⁻¹) = 2
          have ce : C * (2*C⁻¹) = 2 := by field_simp
          -- instantiate
          have hh : C * (2*C⁻¹) ≤ C * B := this
          linarith
        convert cb using 1 <;> field_simp <;> ring
      -- inv form
      have e : 2 * (B * (((2:ℝ)^j)^s))⁻¹ = 2 / (B * (((2:ℝ)^j)^s)) := by ring
      rw [e]
      exact (div_le_iff₀ bp).2 (by
        -- our this has factors reversed
        nlinarith)
    have low' : C / (((a:ℝ)-b)^s) ≤ ‖l^(a-b)-1‖ := by simpa [castab] using lower
    have frac' : C / (((2:ℝ)^j)^s) ≤ C / (((a:ℝ)-b)^s) := by simpa [castab] using frac
    linarith

end PoincareSiegelSupport

namespace PoincareSiegelSupport
open scoped BigOperators
open Finset SqrtTree

noncomputable def dylevel (d : ℕ → ℝ) (B q : ℝ) (w n : ℕ) : ℕ :=
  ((Finset.range w).filter (fun j => dyBad d B q j n)).card

lemma nat_le_two_pow (w : ℕ) : (w:ℝ) ≤ (2:ℝ)^w := by
  have : w ≤ 2^w := by
    induction w with
    | zero => norm_num
    | succ w iw =>
      rw [pow_succ]
      have hp : 0 < 2^w := pow_pos (by omega) _
      omega
  exact_mod_cast this

lemma dy_not_top
    {C : ℝ} (hC : 0 < C) {s : ℕ} (d : ℕ → ℝ)
    (hpoly : ∀ n : ℕ, 2 ≤ n → d n ≤ C⁻¹ * ((n-1:ℕ):ℝ)^s)
    (B : ℝ) (hB : 2 * C⁻¹ ≤ B)
    (w n : ℕ) (h2 : 2 ≤ n) (hnw : n ≤ w) :
    ¬ dyBad d B ((2:ℝ)^s) w n := by
  classical
  intro bad
  have hdn := bad.2
  have upper := hpoly n h2
  have Cp : 0 < C⁻¹ := by positivity
  have nx : (((n-1:ℕ):ℝ)^s) ≤ (((2:ℝ)^w)^s) := by
    have h1 : ((n-1:ℕ):ℝ) ≤ (2:ℝ)^w := by
      have cast1 : ((n-1:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast (Nat.sub_le n 1)
      have nw' : (n:ℝ) ≤ (w:ℝ) := by exact_mod_cast hnw
      exact cast1.trans (nw'.trans (nat_le_two_pow w))
    exact pow_le_pow_left₀ (by positivity) h1 _
  have qq : (((2:ℝ)^s)^w) = ((2:ℝ)^w)^s := pow_two_natCast s w
  rw [qq] at hdn
  have hbig : 2*C⁻¹ * (((2:ℝ)^w)^s) ≤ B * (((2:ℝ)^w)^s) :=
    mul_le_mul_of_nonneg_right hB (by positivity)
  have u2 : C⁻¹ * (((n-1:ℕ):ℝ)^s) ≤ C⁻¹ * (((2:ℝ)^w)^s) :=
    mul_le_mul_of_nonneg_left nx Cp.le
  have strict : C⁻¹ * (((2:ℝ)^w)^s) < 2*C⁻¹ * (((2:ℝ)^w)^s) := by
    have : 0 < C⁻¹ * (((2:ℝ)^w)^s) := by positivity
    nlinarith
  linarith

/-- A single internal vertex is paid for by one factor `B` and by one `q`
for each level at which it is marked. -/
lemma dy_factor
    {C : ℝ} (hC : 0 < C) {s : ℕ} (hs : 1 ≤ s)
    (d : ℕ → ℝ)
    (hpoly : ∀ n : ℕ, 2 ≤ n → d n ≤ C⁻¹ * ((n-1:ℕ):ℝ)^s)
    (B : ℝ) (hB : 2 * C⁻¹ ≤ B)
    (w n : ℕ) (h2 : 2 ≤ n) (hnw : n ≤ w) :
    d n ≤ B * (((2:ℝ)^s)^(dylevel d B ((2:ℝ)^s) w n)) := by
  classical
  let q : ℝ := (2:ℝ)^s
  let m : ℕ := dylevel d B q w n
  have q1 : 1 ≤ q := by dsimp [q]; exact one_le_pow₀ (by norm_num)
  have Bp : 0 < B := lt_of_lt_of_le (by
      have cp : 0 < C⁻¹ := by positivity
      nlinarith) hB
  change d n ≤ B * q^m
  by_contra notle
  have gt : B*q^m < d n := lt_of_not_ge notle
  -- the top level `w` cannot be marked
  have ntop := dy_not_top hC d hpoly B hB w n h2 hnw
  have m_le : m ≤ w := by
    dsimp [m, dylevel]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have mlt : m < w := by
    rcases eq_or_lt_of_le m_le with eq | lt
    · exfalso
      apply ntop
      have bm : dyBad d B q m n := ⟨h2, gt⟩
      simpa [q, ← eq] using bm
    · exact lt
  -- all levels up to m would then be marked
  have incl : Finset.range (m+1) ⊆
      (Finset.range w).filter (fun j => dyBad d B q j n) := by
    intro j hj
    have jm : j ≤ m := (Finset.mem_range.1 hj |> Nat.lt_succ_iff.mp)
    have jw : j < w := lt_of_le_of_lt jm mlt
    have powle : q^j ≤ q^m := by exact pow_le_pow_right₀ q1 jm
    have lev : B*q^j ≤ B*q^m :=
      mul_le_mul_of_nonneg_left powle Bp.le
    have bj : dyBad d B q j n := ⟨h2, lt_of_le_of_lt lev gt⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 jw, bj⟩
  have cards := Finset.card_le_card incl
  have big : m+1 ≤ m := by
    simpa [m, dylevel] using cards
  omega

end PoincareSiegelSupport

namespace PoincareSiegelSupport
open scoped BigOperators
open Finset SqrtTree

noncomputable def treelevels (d : ℕ → ℝ) (B q : ℝ) (w : ℕ) : SqrtTree → ℕ
 | .leaf => 0
 | .node k ch => dylevel d B q w (SqrtTree.weight (.node k ch)) +
                    ∑ i, treelevels d B q w (ch i)

lemma treelevels_eq (d : ℕ → ℝ) (B q : ℝ) (w : ℕ) :
    ∀ t : SqrtTree,
      treelevels d B q w t =
        ∑ j ∈ Finset.range w, SqrtTree.bcount (dyBad d B q j) t := by
  intro t
  induction t with
  | leaf =>
    classical
    simp [treelevels, SqrtTree.bcount_leaf, dyBad]
  | node k ch ih =>
    classical
    rw [treelevels]
    simp only [SqrtTree.bcount_node]
    -- peel the sum: a node contributes its own marks plus the marks in its sons
    calc
      dylevel d B q w (weight (.node k ch)) + ∑ i, treelevels d B q w (ch i) =
          dylevel d B q w (weight (.node k ch)) +
            ∑ i, ∑ j ∈ Finset.range w, bcount (dyBad d B q j) (ch i) := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              exact ih i
      _ = ∑ j ∈ Finset.range w,
            ((if dyBad d B q j (weight (.node k ch)) then 1 else 0) +
              ∑ i, bcount (dyBad d B q j) (ch i)) := by
          dsimp [dylevel]
          -- express card of filter as sum of indicators and interchange the finite sums
          -- `Finset.sum_comm`
          have cardeq : ((Finset.range w).filter
                (fun j => dyBad d B q j (∑ i, weight (ch i)))).card =
                ∑ j ∈ Finset.range w,
                  (if dyBad d B q j (∑ i, weight (ch i)) then 1 else 0) := by
            classical
            exact Finset.card_filter _ _
          rw [cardeq]
          -- both sides are finite distributivity; `simp [Finset.sum_add_distrib]`
          simp_rw [Finset.sum_add_distrib]
          -- sum over j of sum over i
          rw [Finset.sum_comm]
          -- check simp hopefully
          rfl

lemma half_geom (w : ℕ) :
    ∑ j ∈ Finset.range w, ((2:ℝ)^j)⁻¹ = 2 - 2 * ((2:ℝ)⁻¹)^w := by
  induction w with
  | zero => simp
  | succ w ih =>
    simp [Finset.sum_range_succ, ih]
    -- a last elementary geometric term
    have hp : (2:ℝ)^w ≠ 0 := by positivity
    field_simp
    <;> ring

lemma half_geom_le (w : ℕ) :
    ∑ j ∈ Finset.range w, ((2:ℝ)^j)⁻¹ ≤ 2 := by
  rw [half_geom]
  have : 0 ≤ ((2:ℝ)⁻¹)^w := by positivity
  linarith

lemma treelevels_bound
    {l : ℂ} (hl : ‖l‖ = 1) {C : ℝ} (hC : 0 < C)
    {s : ℕ} (hs : 1 ≤ s)
    (d : ℕ → ℝ)
    (hdrel : ∀ n : ℕ, 2 ≤ n → d n = (‖l^(n-1)-1‖)⁻¹)
    (hpoly : ∀ n : ℕ, 2 ≤ n → d n ≤ C⁻¹ * ((n-1:ℕ):ℝ)^s)
    (hlow : ∀ n : ℕ, n ≠ 0 → C / (n:ℝ)^s ≤ ‖l^n-1‖)
    (B : ℝ) (hB : 2 * C⁻¹ ≤ B)
    (w : ℕ) {t : SqrtTree} (ht : Good t) :
    (treelevels d B ((2:ℝ)^s) w t : ℝ) ≤ 4 * (weight t : ℝ) := by
  classical
  -- sum the separation bounds over the first `w` levels
  rw [treelevels_eq]
  push_cast
  have each : ∀ j ∈ Finset.range w,
      (bcount (dyBad d B ((2:ℝ)^s) j) t : ℝ) ≤
        2 * (weight t : ℝ) / (2:ℝ)^j := by
    intro j hj
    exact dyBad_count hl hC hs d hdrel hpoly hlow B hB j t ht
  calc
    (∑ j ∈ Finset.range w,
        (bcount (dyBad d B ((2:ℝ)^s) j) t : ℝ)) ≤
       ∑ j ∈ Finset.range w, (2 * (weight t : ℝ)) * ((2:ℝ)^j)⁻¹ := by
          apply Finset.sum_le_sum
          intro i hi
          have h := each i hi
          simpa [div_eq_mul_inv] using h
    _ = (2 * (weight t : ℝ)) *
          (∑ j ∈ Finset.range w, ((2:ℝ)^j)⁻¹) := by
          rw [Finset.mul_sum]
    _ ≤ (2 * (weight t : ℝ)) * 2 := by
          apply mul_le_mul_of_nonneg_left (half_geom_le w)
          positivity
    _ = 4 * (weight t : ℝ) := by ring

end PoincareSiegelSupport

namespace PoincareSiegelSupport
open scoped BigOperators
open Finset SqrtTree

lemma dvalue_nonneg {d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) : ∀ t : SqrtTree,
    0 ≤ SqrtTree.dvalue d t := by
  intro t
  induction t with
  | leaf => simp [SqrtTree.dvalue]
  | node k ch ih =>
    simp [SqrtTree.dvalue]
    exact mul_nonneg (hd _) (Finset.prod_nonneg (fun i hi => ih i))

lemma dvalue_paid
    {C : ℝ} (hC : 0 < C) {s : ℕ} (hs : 1 ≤ s)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hpoly : ∀ n : ℕ, 2 ≤ n → d n ≤ C⁻¹ * ((n-1:ℕ):ℝ)^s)
    (B : ℝ) (hB : 2 * C⁻¹ ≤ B)
    (w : ℕ) :
    ∀ t : SqrtTree, Good t → weight t ≤ w →
      SqrtTree.dvalue d t ≤
        B^(SqrtTree.vertices t) *
          (((2:ℝ)^s)^(treelevels d B ((2:ℝ)^s) w t)) := by
  intro t ht hw
  induction t with
  | leaf =>
      simp [SqrtTree.dvalue, SqrtTree.vertices, treelevels]
  | node k ch ih =>
      classical
      let q : ℝ := (2:ℝ)^s
      have Bp : 0 ≤ B := le_trans (by
          have : 0 < C⁻¹ := by positivity
          nlinarith) hB
      have qpos : 0 ≤ q := by dsimp [q]; positivity
      have hn : 2 ≤ weight (.node k ch) := weight_ge_two_node ht
      have fact : d (weight (.node k ch)) ≤
          B * q^(dylevel d B q w (weight (.node k ch))) :=
        dy_factor hC hs d hpoly B hB w _ hn hw
      have childw : ∀ i, weight (ch i) ≤ w := fun i =>
        (weight_le_of_child i).trans hw
      have prodle : (∏ i, SqrtTree.dvalue d (ch i)) ≤
          ∏ i : Fin k, (B^(vertices (ch i)) *
                    q^(treelevels d B q w (ch i))) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact dvalue_nonneg hd _
        · intro i hi
          exact ih i (ht.2 i) (childw i)
      -- multiply the factor and expand the powers
      change
        d (weight (.node k ch)) * (∏ i, SqrtTree.dvalue d (ch i)) ≤ _
      have step : d (weight (.node k ch)) * (∏ i, SqrtTree.dvalue d (ch i)) ≤
          (B * q^(dylevel d B q w (weight (.node k ch)))) *
            (∏ i : Fin k, (B^(vertices (ch i)) *
                    q^(treelevels d B q w (ch i)))) := by
        exact mul_le_mul fact prodle
          (Finset.prod_nonneg (fun i hi => dvalue_nonneg hd _))
          (by positivity)
      calc
       d (weight (.node k ch)) * (∏ i, SqrtTree.dvalue d (ch i)) ≤
          (B * q^(dylevel d B q w (weight (.node k ch)))) *
            (∏ i : Fin k, (B^(vertices (ch i)) *
                    q^(treelevels d B q w (ch i)))) := step
       _ = B^(vertices (.node k ch)) *
              q^(treelevels d B q w (.node k ch)) := by
            simp [q, vertices, treelevels, pow_add, Finset.prod_mul_distrib,
              Finset.prod_pow_eq_pow_sum]
            ring

lemma tree_divisor_exp
    {l : ℂ} (hl : ‖l‖ = 1) {C : ℝ} (hC : 0 < C)
    {s : ℕ} (hs : 1 ≤ s)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hdrel : ∀ n : ℕ, 2 ≤ n → d n = (‖l^(n-1)-1‖)⁻¹)
    (hpoly : ∀ n : ℕ, 2 ≤ n → d n ≤ C⁻¹ * ((n-1:ℕ):ℝ)^s)
    (hlow : ∀ n : ℕ, n ≠ 0 → C / (n:ℝ)^s ≤ ‖l^n-1‖) :
    let B : ℝ := max 1 (2*C⁻¹)
    let T : ℝ := B * ((2:ℝ)^s)^4
    ∀ t : SqrtTree, Good t → SqrtTree.dvalue d t ≤ T^(weight t) := by
  classical
  dsimp
  let B : ℝ := max 1 (2*C⁻¹)
  let q : ℝ := (2:ℝ)^s
  let T : ℝ := B * q^4
  have hB : 2*C⁻¹ ≤ B := by dsimp [B]; exact le_max_right _ _
  have B1 : 1 ≤ B := by dsimp [B]; exact le_max_left _ _
  have q1 : 1 ≤ q := by dsimp [q]; exact one_le_pow₀ (by norm_num)
  intro t ht
  let w := weight t
  have paid := dvalue_paid hC hs d hd hpoly B hB w t ht (by rfl)
  have vlev : vertices t ≤ w := SqrtTree.vertices_le_weight ht
  have llevR := treelevels_bound hl hC hs d hdrel hpoly hlow B hB w ht
  have llev : treelevels d B q w t ≤ 4*w := by
    dsimp [q, w]
    exact_mod_cast llevR
  have p1 : B^(vertices t) ≤ B^w := pow_le_pow_right₀ B1 vlev
  have p2 : q^(treelevels d B q w t) ≤ q^(4*w) := pow_le_pow_right₀ q1 llev
  have nn : 0 ≤ B^(vertices t) := by positivity
  have nw : 0 ≤ B^w := by positivity
  calc
    dvalue d t ≤ B^(vertices t) * q^(treelevels d B q w t) := paid
    _ ≤ B^w * q^(4*w) := mul_le_mul p1 p2 (by positivity) (by positivity)
    _ = (B * q^4)^w := by rw [mul_pow, ← pow_mul]; ring

end PoincareSiegelSupport

namespace PoincareSiegelSupport
open scoped BigOperators
open Finset SqrtTree

noncomputable def max0 (s : Finset ℝ) : ℝ :=
  (insert 0 s).max' (by exact ⟨0, mem_insert_self _ _⟩)
lemma max0_nonneg (s : Finset ℝ) : 0 ≤ max0 s := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
lemma le_max0 {s : Finset ℝ} {x : ℝ} (hx : x ∈ s) : x ≤ max0 s := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem hx)
lemma max0_spec (s : Finset ℝ) : max0 s = 0 ∨ max0 s ∈ s := by
  classical
  have M := Finset.max'_mem (insert 0 s) (by exact ⟨0, Finset.mem_insert_self _ _⟩)
  rcases Finset.mem_insert.1 M with h | h
  · exact Or.inl h
  · exact Or.inr h
lemma max0_le {s : Finset ℝ} {x : ℝ} (hx0 : 0 ≤ x)
    (h : ∀ y ∈ s, y ≤ x) : max0 s ≤ x := by
  classical
  apply (Finset.max'_le_iff _ _).2
  intro y hy
  rcases Finset.mem_insert.1 hy with e | e
  · simpa [e] using hx0
  · exact h y e

/-- maximal possible product of divisors in a tree of weight `n`, presented by
its dynamic program. The cutoff makes it a structural recursion on `n`. -/
noncomputable def divMax (d : ℕ → ℝ) : ℕ → ℝ
 | 0 => 1
 | 1 => 1
 | n+2 =>
   let b : ℕ → ℝ := fun k => if h : k < n+2 then divMax d k else 0
   max0 (({c : Composition (n+2) | 1 < c.length}.toFinset).image
      (fun c => d (n+2) * ∏ j, b (c.blocksFun j)))

@[simp] lemma divMax_zero (d : ℕ → ℝ) : divMax d 0 = 1 := by rw [divMax]
@[simp] lemma divMax_one (d : ℕ → ℝ) : divMax d 1 = 1 := by rw [divMax]
lemma divMax_rec (d : ℕ → ℝ) (n : ℕ) :
  divMax d (n+2) =
    max0 (({c : Composition (n+2) | 1 < c.length}.toFinset).image
      (fun c => d (n+2) * ∏ j, divMax d (c.blocksFun j))) := by
  classical
  rw [divMax]
  apply congrArg max0
  apply Finset.image_congr
  intro c hc
  have lt : ∀ j, c.blocksFun j < n+2 :=
    comp_blocks_lt (by omega : 0 < n+2) c (by simpa using hc)
  dsimp
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [lt]

lemma block_pos {n} (c : Composition n) (i : Fin c.length) : 0 < c.blocksFun i := by
  exact c.blocks_pos (List.get_mem _ _)

lemma divMax_nonneg (d : ℕ → ℝ) : ∀ n, 0 ≤ divMax d n := by
  intro n
  rcases n with (_|_|n)
  · simp
  · simp
  · rw [divMax_rec]
    exact max0_nonneg _
lemma divMax_item {d : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n)
    (c : Composition n) (hc : 1 < c.length) :
    d n * ∏ j, divMax d (c.blocksFun j) ≤ divMax d n := by
  classical
  generalize e : n-2 = m
  have eq : n = m+2 := by omega
  subst n
  rw [divMax_rec]
  apply le_max0
  refine Finset.mem_image.2 ⟨c, ?_, rfl⟩
  simpa using hc

/-- The maximum is achieved by a good tree, unless it is the harmless
zero inserted in the finite maximum. -/
lemma divMax_witness (d : ℕ → ℝ) : ∀ n : ℕ, n ≠ 0 →
    divMax d n = 0 ∨
      ∃ t : SqrtTree, Good t ∧ weight t = n ∧ SqrtTree.dvalue d t = divMax d n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n IH =>
    rcases n with (_|_|m)
    · contradiction
    · right
      exact ⟨.leaf, by simp, by simp, by simp [SqrtTree.dvalue]⟩
    · classical
      rw [divMax_rec]
      rcases max0_spec (({c : Composition (m+2) | 1 < c.length}.toFinset).image
        (fun c => d (m+2) * ∏ j, divMax d (c.blocksFun j))) with z | mem
      · exact Or.inl z
      · rcases Finset.mem_image.1 mem with ⟨c, hc, eq⟩
        have hc' : 1 < c.length := by simpa using hc
        have lt : ∀ i, c.blocksFun i < m+2 :=
          comp_blocks_lt (by omega) c hc'
        -- choose, for each nonzero child maximum, a realizing tree.
        by_cases anyz : ∃ i, divMax d (c.blocksFun i) = 0
        · left
          have prodz : (∏ i, divMax d (c.blocksFun i)) = 0 := by
            rcases anyz with ⟨i, hi⟩
            classical
            exact Finset.prod_eq_zero (Finset.mem_univ i) hi
          rw [← eq]
          simp [prodz]
        · push_neg at anyz
          have wit : ∀ i, ∃ t : SqrtTree, Good t ∧
              weight t = c.blocksFun i ∧ dvalue d t = divMax d (c.blocksFun i) := by
            intro i
            have nz : c.blocksFun i ≠ 0 := by
              have pp := block_pos c i
              omega
            rcases IH (c.blocksFun i) (lt i) nz with z | w
            · exact False.elim (anyz i z)
            · exact w
          choose t good wt val using wit
          right
          let T : SqrtTree := .node c.length t
          refine ⟨T, ?_, ?_, ?_⟩
          · exact ⟨by omega, good⟩
          · dsimp [T, weight]
            simpa [wt] using (Composition.sum_blocksFun c)
          · rw [← eq]
            simp [T, SqrtTree.dvalue]
            -- use the child values
            have sw : (∑ i, weight (t i)) = m+2 := by
              simpa [wt] using (Composition.sum_blocksFun c)
            rw [sw]
            apply congrArg (fun x => d (m+2) * x) ?_
            apply Finset.prod_congr rfl
            intro i hi
            exact val i

lemma divMax_tree_bound {d : ℕ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (bound : ∀ t : SqrtTree, Good t → dvalue d t ≤ T^(weight t)) :
    ∀ n, divMax d n ≤ T^n := by
  intro n
  rcases n with (_|n)
  · simp
  · have nz : n+1 ≠ 0 := by omega
    rcases divMax_witness d (n+1) nz with z | ⟨t, ht, wt, va⟩
    · rw [z]
      positivity
    · rw [← va, ← wt]
      exact bound t ht

lemma majorant_divMax {a d : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hd : ∀ n, 0 ≤ d n) :
    ∀ n, schroederMajorant a d n ≤
      divMax d n * schroederMajorant a (fun _ => 1) n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n IH =>
    rcases n with (_|_|m)
    · simp
    · simp
    · rw [schroederMajorant_rec, schroederMajorant_rec]
      let F := ({c : Composition (m+2) | 1 < c.length}.toFinset)
      have flatpos : ∀ k, 0 ≤ schroederMajorant a (fun _ => 1) k :=
        schroederMajorant_nonneg ha (by norm_num)
      have sdpos := schroederMajorant_nonneg ha hd
      have Dpos := divMax_nonneg d
      calc
       d (m+2) * (∑ c ∈ F,
          a c.length * ∏ j, schroederMajorant a d (c.blocksFun j)) ≤
          d (m+2) * (∑ c ∈ F,
            (a c.length * ∏ j, (divMax d (c.blocksFun j) *
                         schroederMajorant a (fun _ => 1) (c.blocksFun j)))) := by
            apply mul_le_mul_of_nonneg_left ?_ (hd _)
            apply Finset.sum_le_sum
            intro c hc
            apply mul_le_mul_of_nonneg_left ?_ (ha _)
            apply Finset.prod_le_prod
            · intro i hi
              exact sdpos _
            · intro i hi
              apply IH
              exact comp_blocks_lt (by omega : 0 < m+2) c (by simpa [F] using hc) i
       _ ≤ divMax d (m+2) *
            (∑ c ∈ F,
              a c.length * ∏ j, schroederMajorant a (fun _ => 1) (c.blocksFun j)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro c hc
          -- pull apart the products; all remaining factors are nonnegative
          rw [Finset.prod_mul_distrib]
          have item : d (m+2) * (∏ j, divMax d (c.blocksFun j)) ≤
                divMax d (m+2) :=
            divMax_item (by omega) c (by simpa [F] using hc)
          have non : 0 ≤ a c.length *
              (∏ j, schroederMajorant a (fun _ => 1) (c.blocksFun j)) :=
            mul_nonneg (ha _) (Finset.prod_nonneg (fun i hi => flatpos _))
          calc
            d (m+2) *
                (a c.length *
                  ((∏ j, divMax d (c.blocksFun j)) *
                    ∏ j, schroederMajorant a (fun _ => 1) (c.blocksFun j))) =
              (d (m+2) * (∏ j, divMax d (c.blocksFun j))) *
                (a c.length * ∏ j, schroederMajorant a (fun _ => 1) (c.blocksFun j)) := by ring
            _ ≤ divMax d (m+2) *
                (a c.length * ∏ j, schroederMajorant a (fun _ => 1) (c.blocksFun j)) :=
                  mul_le_mul_of_nonneg_right item non
       _ = divMax d (m+1+1) *
            ((fun _ : ℕ => (1:ℝ)) (m+2) *
              (∑ c ∈ F, a c.length * ∏ j,
                schroederMajorant a (fun _ => 1) (c.blocksFun j))) := by ring

/-- Numerical Siegel lemma for the composition majorant. The analytic series
has disappeared: only the unit-circle separation and the polynomial lower
bound remain. -/
lemma schroederMajorant_weighted_exp
    {l : ℂ} (hl : ‖l‖ = 1) {C : ℝ} (hC : 0 < C)
    {s : ℕ} (hs : 1 ≤ s)
    (a d : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hd : ∀ n, 0 ≤ d n)
    (hdrel : ∀ n : ℕ, 2 ≤ n → d n = (‖l^(n-1)-1‖)⁻¹)
    (hpoly : ∀ n : ℕ, 2 ≤ n → d n ≤ C⁻¹ * ((n-1:ℕ):ℝ)^s)
    (hlow : ∀ n : ℕ, n ≠ 0 → C / (n:ℝ)^s ≤ ‖l^n-1‖)
    (flat : ∃ K S : ℝ, 0 ≤ K ∧ 0 < S ∧
      ∀ n, schroederMajorant a (fun _ => 1) n ≤ K * S^n) :
    ∃ K S : ℝ, 0 ≤ K ∧ 0 < S ∧
      ∀ n, schroederMajorant a d n ≤ K * S^n := by
  classical
  let B : ℝ := max 1 (2*C⁻¹)
  let q : ℝ := (2:ℝ)^s
  let T : ℝ := B * q^4
  have B1 : 1 ≤ B := by dsimp [B]; exact le_max_left _ _
  have q1 : 1 ≤ q := by dsimp [q]; exact one_le_pow₀ (by norm_num)
  have Tpos : 0 < T := by dsimp [T]; positivity
  have trees : ∀ t : SqrtTree, Good t → dvalue d t ≤ T^(weight t) := by
    intro t ht
    exact tree_divisor_exp hl hC hs d hd hdrel hpoly hlow t ht
  have Dbound : ∀ n, divMax d n ≤ T^n := divMax_tree_bound Tpos.le trees
  rcases flat with ⟨K, R, k0, r0, hb⟩
  refine ⟨K, T*R, k0, mul_pos Tpos r0, ?_⟩
  intro n
  have one := majorant_divMax (a:=a) (d:=d) ha hd n
  have fp := schroederMajorant_nonneg ha (by intro k; norm_num : ∀ k, (0:ℝ) ≤ (fun _ => (1:ℝ)) k) n
  have dn := divMax_nonneg d n
  have bn := hb n
  calc
    schroederMajorant a d n ≤ divMax d n * schroederMajorant a (fun _ => 1) n := one
    _ ≤ T^n * (K * R^n) := by
      exact mul_le_mul (Dbound n) bn
        (schroederMajorant_nonneg ha (by intro k; norm_num) n)
        (by positivity)
    _ = K * (T*R)^n := by rw [mul_pow]; ring

end PoincareSiegelSupport

-- END INLINED FILE: Mathlib/Support/poincare_siegel_linearisation_e5c82ef09f/Weighted.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval
namespace ComplexAnalysis

/-!
# Poincaré–Siegel linearisation theorem

If `f : ℂ → ℂ` is holomorphic near `0` with `f 0 = 0` and multiplier
`f'(0) = λ = e^{2πiα}` for a Diophantine `α`, then `f` is locally
analytically conjugate to the rotation `z ↦ λ z`: there is a holomorphic
germ `u(z) = z + O(z²)` with `f(u(z)) = u(λ z)` near `0` — an analytic
solution of the Schröder equation.
-/

/-- A real `α` is **Diophantine** if there are `C > 0` and `τ : ℝ` such
that `C / |q|^τ ≤ |α − p/q|` for all integers `p, q` with `q ≠ 0`. The
exponent τ is implicitly ≥ 2 by Dirichlet's theorem. This implies α is
irrational, so `e^{2πiα}` is not a root of unity. -/
def IsDiophantine (α : ℝ) : Prop :=
  ∃ C τ : ℝ, 0 < C ∧ ∀ p q : ℤ, q ≠ 0 →
    C / |(q : ℝ)| ^ τ ≤ |α - (p : ℝ) / (q : ℝ)|



end ComplexAnalysis
end LeanEval

open LeanEval.ComplexAnalysis
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem poincare_siegel (α : ℝ) (_hα : IsDiophantine α)
    (lam : ℂ) (_hlam : lam = Complex.exp (2 * Real.pi * Complex.I * (α : ℂ)))
    (f : ℂ → ℂ) (_hf : AnalyticAt ℂ f 0) (_hf0 : f 0 = 0)
    (_hmult : deriv f 0 = lam) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = 0 ∧ deriv u 0 = 1 ∧
      ∀ᶠ z in nhds (0 : ℂ), f (u z) = u (lam * z) :=
/-ResultProofBegin-/by
  classical
  rcases _hα with ⟨C, τ, hC, hbound⟩
  have hlam0 : lam ≠ 0 := by
    rw [_hlam]
    exact Complex.exp_ne_zero _
  have hlamunit : ‖lam‖ = 1 := by
    rw [_hlam, Complex.norm_exp]
    have hz : (2 * (Real.pi:ℂ) * Complex.I * (α:ℂ)).re = 0 := by simp
    rw [hz, Real.exp_zero]
  have hlamroot : ∀ n : ℕ, n ≠ 0 → lam ^ n ≠ 1 := by
    intro n hn
    rw [_hlam]
    exact
      PoincareSiegelSupport.exp_two_pi_mul_pow_ne_one α C τ hC hbound hn
  have hdenom : ∀ n : ℕ, 2 ≤ n → lam ^ n - lam ≠ 0 := by
    intro n hn
    rw [_hlam]
    exact
      PoincareSiegelSupport.exp_two_pi_mul_pow_sub_self_ne_zero α C τ hC hbound hn
  have hsmall : ∀ n : ℕ, n ≠ 0 →
        4 * (n:ℝ) * (C / (n:ℝ)^τ) ≤ ‖lam ^ n - 1‖ := by
    intro n hn
    rw [_hlam]
    exact
      PoincareSiegelSupport.diophantine_norm_pow_sub_one_lower
        α C τ hC hbound hn
  have hsmall_denom : ∀ n : ℕ, 2 ≤ n →
        4 * (n-1:ℕ) * (C / ( (n-1:ℕ):ℝ)^τ) ≤ ‖lam ^ n - lam‖ := by
    intro n hn
    rw [_hlam]
    exact
      PoincareSiegelSupport.diophantine_norm_pow_sub_self_lower
        α C τ hC hbound hn
  obtain ⟨a, arad, a0, a1, ha⟩ :=
    PoincareSiegelSupport.analyticAt_exists_taylor f _hf
  have a0' : a 0 = 0 := a0.trans _hf0
  have a1' : a 1 = lam := a1.trans _hmult
  -- Work with the canonical Taylor series: this lets us use the full
  -- `HasFPowerSeriesAt.comp` API rather than coefficient identities of germs.
  let ap : ℕ → ℂ := fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ ap
  have hp : HasFPowerSeriesAt f p 0 := by
    simpa [p, ap] using _hf.hasFPowerSeriesAt
  have hp0 : p.coeff 0 = 0 := by
    simpa [p, ap, iteratedDeriv_zero] using _hf0
  have hp1 : p.coeff 1 = lam := by
    simpa [p, ap, iteratedDeriv_one] using _hmult
  have main_estimate :
      0 < (PoincareSiegelSupport.schroederSeries p lam).radius := by
    -- Coefficients of the given germ have a geometric majorant, from its
    -- (strictly) positive convergence radius. This is the starting point
    -- for the remaining Siegel small-divisor bound on the triangular series.
    have hp_pos : 0 < p.radius := hp.radius_pos
    obtain ⟨A, R, hA, hR, hp_bound⟩ :=
      FormalMultilinearSeries.le_mul_pow_of_radius_pos p hp_pos
    -- Strip the analytic part of the problem off once and for all.  What is
    -- left is a sequence of *numbers*.  This makes precise the usually
    -- implicit "tree majorant" in the proof.
    let aa : ℕ → ℝ := fun k => A * R^k
    let dd : ℕ → ℝ := fun k => ‖(lam^k-lam)⁻¹‖
    have haa : ∀ k, 0 ≤ aa k := by
      intro k
      dsimp [aa]
      exact mul_nonneg hA.le (by positivity)
    have hdd : ∀ k, 0 ≤ dd k := by
      intro k
      exact norm_nonneg _
    have hpaa : ∀ k, ‖p k‖ ≤ aa k := by
      intro k
      simpa [aa] using hp_bound k
    have hcoeff : ∀ n,
        ‖PoincareSiegelSupport.schroederSeries p lam n‖ ≤
          PoincareSiegelSupport.schroederMajorant aa dd n :=
      PoincareSiegelSupport.schroederSeries_le_majorant p lam aa dd haa hdd hpaa
        (by intro k; exact le_rfl)
    -- If all divisors at vertices are replaced with one this numerical
    -- composition recursion already has a geometric bound (the familiar
    -- inverse-series majorant).  Thus the outstanding growth is precisely
    -- the correlated product of small divisors, not the number of
    -- compositions.
    have hflat : ∃ K S : ℝ, 0 ≤ K ∧ 0 < S ∧
        ∀ n, PoincareSiegelSupport.schroederMajorant aa (fun _ => 1) n
              ≤ K * S^n := by
      apply PoincareSiegelSupport.schroederMajorant_one_exp aa haa hA hR
      intro n
      simpa [aa]
    -- A useful non-asymptotic consequence of the Diophantine estimate.  In
    -- particular no manipulation of formal power series is still hidden in
    -- the remaining purely numerical estimate below.
    have hdd_poly : ∀ k : ℕ, 2 ≤ k →
        dd k ≤
          (4 * ((k-1 : ℕ) : ℝ) *
            (C / (((k-1 : ℕ):ℝ)^τ)))⁻¹ := by
      intro k hk
      have hposNat : 0 < ( (k-1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < k-1)
      have hbpos : 0 <
          (4 * ((k-1 : ℕ) : ℝ) *
            (C / (((k-1 : ℕ):ℝ)^τ))) := by
        have hpw : 0 < (((k-1 : ℕ):ℝ)^τ) := by
          positivity
        exact mul_pos (mul_pos (by norm_num) hposNat) (div_pos hC hpw)
      have hlo := hsmall_denom k hk
      have hnpos : 0 < ‖lam^k - lam‖ :=
        lt_of_lt_of_le hbpos hlo
      change ‖(lam^k-lam)⁻¹‖ ≤ _
      rw [norm_inv]
      exact (inv_le_inv₀ hnpos hbpos).2 hlo
    -- The remaining step no longer involves multilinear maps.  It is the
    -- classical Siegel lemma on weighted composition trees: the product of
    -- the inverse small divisors along a tree of weight `n` is at most
    -- exponential in `n` (one may prove it by stratifying vertices
    -- dyadically).  The numerical recursion used here has one vertex for a
    -- composition and is well-founded since every block is smaller.
    obtain ⟨K, S, hK, hS, hnum⟩ :
        ∃ K S : ℝ, 0 ≤ K ∧ 0 < S ∧
          ∀ n : ℕ,
            PoincareSiegelSupport.schroederMajorant aa dd n ≤ K * S^n := by
      -- From this point on no analytic fact is involved.  It is useful not
      -- to carry a real exponent through the combinatorics: replacing it by
      -- a larger positive integer loses nothing.
      obtain ⟨s, hs, hlow⟩ :=
        PoincareSiegelSupport.weak_integer_lower (l:=lam) hC hsmall
      have hpoly : ∀ k : ℕ, 2 ≤ k →
          dd k ≤ C⁻¹ * ((k-1:ℕ):ℝ)^s := by
        intro k hk
        have r0 : k-1 ≠ 0 := by omega
        have lo := hlow (k-1) r0
        have rel := PoincareSiegelSupport.unit_pow_sub_self_norm lam hlamunit k
          (by omega : 1 ≤ k)
        have dpos : 0 < ‖lam^(k-1)-1‖ :=
          lt_of_lt_of_le (by positivity : 0 < C/((k-1:ℕ):ℝ)^s) lo
        dsimp [dd]
        rw [norm_inv, rel]
        calc
          (‖lam ^ (k-1) - 1‖)⁻¹ ≤ (C / ((k-1:ℕ):ℝ)^s)⁻¹ :=
            (inv_le_inv₀ dpos (by positivity : 0 < C/((k-1:ℕ):ℝ)^s)).2 lo
          _ = C⁻¹ * ((k-1:ℕ):ℝ)^s := by
            have cp : C ≠ 0 := ne_of_gt hC
            have rp : (((k-1:ℕ):ℝ)^s) ≠ 0 := by positivity
            field_simp
            <;> ring
      -- In a composition tree mark the vertices for which the divisor is
      -- large.  The pruning form of the forest lemma is often the cleanest
      -- way of using the separation of small divisors: if `L` is a spacing
      -- at one scale there are at most `2n/L` such vertices. It also covers
      -- non-full (arbitrary arity) trees, which are the ones in the recursion
      -- above.
      have prune (bad : ℕ → Prop) [DecidablePred bad]
          (hnob : ¬ bad 1) {L : ℝ} (hL : 0 < L)
          (hmin : ∀ {n}, bad n → L ≤ (n:ℝ))
          (hsep : ∀ {a b}, bad a → bad b → b < a → L ≤ (a:ℝ)-b) :
          ∀ t : PoincareSiegelSupport.SqrtTree,
            PoincareSiegelSupport.SqrtTree.Good t →
            (PoincareSiegelSupport.SqrtTree.bcount bad t : ℝ) ≤
              2 * (PoincareSiegelSupport.SqrtTree.weight t : ℝ) / L := by
        exact PoincareSiegelSupport.SqrtTree.forest_count bad hnob hL hmin hsep
      have badcount1 (j : ℕ) : ∀ t : PoincareSiegelSupport.SqrtTree,
          PoincareSiegelSupport.SqrtTree.Good t →
          (PoincareSiegelSupport.SqrtTree.bcount
              (fun n => 2 ≤ n ∧ dd n > (2:ℝ)^(s*j)) t : ℝ) ≤
             2 * (PoincareSiegelSupport.SqrtTree.weight t : ℝ) := by
        have H := prune (fun n => 2 ≤ n ∧ dd n > (2:ℝ)^(s*j))
          (by norm_num)
          (L:= (1:ℝ)) (by norm_num)
          (by
            intro n hn
            have hnat : 1 ≤ n := by omega
            exact_mod_cast hnat)
          (by
            intro a b ha hb hlt
            have ab : b + 1 ≤ a := by omega
            have abr : ((b:ℕ):ℝ) + 1 ≤ (a:ℕ) := by exact_mod_cast ab
            have e : (1:ℝ) ≤ (a:ℝ) - b := by
              linarith
            exact e)
        intro t ht
        have ht' := H t ht
        simpa using ht'
      have hdrel : ∀ n : ℕ, 2 ≤ n →
          dd n = (‖lam^(n-1)-1‖)⁻¹ := by
        intro n hn
        dsimp [dd]
        rw [norm_inv, PoincareSiegelSupport.unit_pow_sub_self_norm lam hlamunit n
          (by omega : 1 ≤ n)]
      exact PoincareSiegelSupport.schroederMajorant_weighted_exp
        hlamunit hC hs aa dd haa hdd hdrel hpoly hlow hflat
    apply PoincareSiegelSupport.radius_pos_of_le_mul_pow hK hS
    intro n
    exact (hcoeff n).trans (hnum n)
  exact PoincareSiegelSupport.analytic_conjugate_of_radius hp hp0 hp1
    hdenom main_estimate/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
