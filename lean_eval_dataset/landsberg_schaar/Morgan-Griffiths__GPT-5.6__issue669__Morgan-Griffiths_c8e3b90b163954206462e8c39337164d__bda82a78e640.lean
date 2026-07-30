import Mathlib

namespace Submission

namespace LeanEval.NumberTheory.LandsbergSchaar

/-!
# The Landsberg–Schaar relation

`landsberg_schaar`: for positive odd integers `p, q`,
`S(2q, p) = e^{iπ/4} · S(−p, 2q)`, where `S(q,p) = (1/√p) ∑_{x<p} e^{iπ x² q/p}`
is the normalized quadratic Gauss sum (the trusted helper `gaussS`, a non-hole).
Mathlib has the character-theoretic `gaussSum` (giving `|g|² = p`) and the
Jacobi-theta machinery, but neither the quadratic Gauss-sum value nor the
Landsberg–Schaar relation.

Category-(b) candidate from §120 of the Knill survey.
-/

open Complex Finset

/-- Knill's normalized finite quadratic exponential sum
`S(q, p) = (1/√p) ∑_{x=0}^{p−1} exp(i π x² q / p)`. -/
noncomputable def gaussS (q : ℤ) (p : ℕ) : ℂ :=
  (Real.sqrt p : ℂ)⁻¹ *
    ∑ x ∈ Finset.range p,
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((x : ℂ) ^ 2 * (q : ℂ) / (p : ℂ)))



end LeanEval.NumberTheory.LandsbergSchaar

open LeanEval.NumberTheory.LandsbergSchaar
open Complex Finset
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

lemma exp_even_period_zsmul_arg (n k:ℤ) (d b:ℕ) (hd:d≠0) :
    (Real.pi:ℂ)*Complex.I * (((((n + (d:ℤ)*k) : ℤ) : ℂ))^2 * (( (2*(b:ℕ) : ℕ) : ℂ)) / ((d:ℕ):ℂ)) =
      (Real.pi:ℂ)*Complex.I * (( (n:ℂ))^2 * (((2*b:ℕ):ℕ):ℂ) / (d:ℂ)) +
        (( (b:ℤ) * (2*n*k + (d:ℤ)*k^2) : ℤ) : ℂ) * (2*(Real.pi:ℂ)*Complex.I) := by
  have hd' : (d:ℂ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  ring

lemma exp_even_period_zsmul (n k:ℤ) (d b:ℕ) (hd:d≠0) :
    Complex.exp ((Real.pi:ℂ)*Complex.I * ((((n + (d:ℤ)*k :ℤ):ℂ))^2 * (((2*b:ℕ):ℕ):ℂ) / (d:ℂ))) =
    Complex.exp ((Real.pi:ℂ)*Complex.I * ((n:ℂ)^2 * (((2*b:ℕ):ℕ):ℂ) / (d:ℂ))) := by
  rw [exp_even_period_zsmul_arg n k d b hd, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  ring
lemma exp_neg_evenmod_period_zsmul_arg (n k:ℤ) (c b:ℕ) (hb:b≠0) :
 (Real.pi:ℂ)*Complex.I * (((((n + (2*b:ℕ)*k) : ℤ) : ℂ))^2 * ((-(c:ℤ) : ℤ) : ℂ) / ((2*b:ℕ):ℂ)) =
 (Real.pi:ℂ)*Complex.I * ((n:ℂ)^2 * ((-(c:ℤ) : ℤ) : ℂ) / ((2*b:ℕ):ℂ)) +
   (((-(c:ℤ)) * (n*k + (b:ℤ)*k^2)) : ℂ) * (2*(Real.pi:ℂ)*Complex.I) := by
 have hb' : ((2*b:ℕ):ℂ) ≠ 0 := by
   exact_mod_cast (by omega : (2*b:ℕ) ≠ 0)
 push_cast
 field_simp
 ring

lemma exp_neg_evenmod_period_zsmul (n k:ℤ) (c b:ℕ) (hb:b≠0) :
 Complex.exp ((Real.pi:ℂ)*Complex.I * (((((n + (2*b:ℕ)*k) : ℤ) : ℂ))^2 * ((-(c:ℤ) : ℤ) : ℂ) / ((2*b:ℕ):ℂ))) =
 Complex.exp ((Real.pi:ℂ)*Complex.I * ((n:ℂ)^2 * ((-(c:ℤ) : ℤ) : ℂ) / ((2*b:ℕ):ℂ))) := by
 rw [exp_neg_evenmod_period_zsmul_arg n k c b hb, Complex.exp_add]
 have h : Complex.exp ((((-(c:ℤ)) * (n*k + (b:ℤ)*k^2)) : ℤ) * (2*(Real.pi:ℂ)*Complex.I)) = 1 :=
   Complex.exp_int_mul_two_pi_mul_I _
 have he : Complex.exp (- (c:ℂ) * ((n:ℂ)*(k:ℂ) + (b:ℂ)*(k:ℂ)^2) * (2*(Real.pi:ℂ)*Complex.I)) = 1 := by
   convert h using 1 <;> push_cast <;> ring
 have hcast : - (c:ℂ) * ((n:ℂ)*(k:ℂ) + (b:ℂ)*(k:ℂ)^2) = (((-(c:ℤ)) * (n*k + (b:ℤ)*k^2)) : ℂ) := by
   push_cast
   ring
 rw [← hcast, he]
 ring
noncomputable def intDecomp (d:ℕ) (hd:0<d) : ℤ ≃ (Fin d × ℤ) where
 toFun n :=
   (⟨ Int.toNat (n % (d:ℤ)), by
       have hlt : n % (d:ℤ) < (d:ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hd)
       omega ⟩, n / (d:ℤ))
 invFun u := (u.1.val : ℤ) + (d:ℤ) * u.2
 left_inv n := by
   dsimp
   have hnon : 0 ≤ n % (d:ℤ) := Int.emod_nonneg _ (by omega)
   have hlt : n % (d:ℤ) < (d:ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hd)
   have hz : (Int.toNat (n % (d:ℤ)) : ℤ) = n % (d:ℤ) := by omega
   rw [hz]
   -- use ediv_emod_unique
   have hU := (Int.ediv_emod_unique (a:=n) (b:=(d:ℤ)) (r:= n % (d:ℤ)) (q:= n / (d:ℤ)) (by exact_mod_cast hd)).1
      (And.intro rfl rfl)
   exact hU.1
 right_inv u := by
   rcases u with ⟨r,k⟩
   dsimp
   apply Prod.ext
   · apply Fin.ext
     dsimp
     have hr0 : 0 ≤ (r.val:ℤ) := by exact_mod_cast (Nat.zero_le r.val)
     have hrlt : (r.val:ℤ) < (d:ℤ) := by exact_mod_cast r.isLt
     have hU := (Int.ediv_emod_unique (a:=(r.val:ℤ) + (d:ℤ)*k) (b:=(d:ℤ))
       (r:=(r.val:ℤ)) (q:=k) (by exact_mod_cast hd)).2
       (by constructor; rfl; exact ⟨hr0, hrlt⟩)
     have hmod : ((r.val:ℤ) + (d:ℤ)*k) % (d:ℤ) = (r.val:ℤ) := hU.2
     rw [hmod]
     omega
   · dsimp
     have hr0 : 0 ≤ (r.val:ℤ) := by exact_mod_cast (Nat.zero_le r.val)
     have hrlt : (r.val:ℤ) < (d:ℤ) := by exact_mod_cast r.isLt
     have hU := (Int.ediv_emod_unique (a:=(r.val:ℤ) + (d:ℤ)*k) (b:=(d:ℤ))
       (r:=(r.val:ℤ)) (q:=k) (by exact_mod_cast hd)).2
       (by constructor; rfl; exact ⟨hr0, hrlt⟩)
     exact hU.1
lemma Int.tsum_decomp {f:ℤ→ℂ} (hf:Summable f) (d:ℕ) (hd:0<d) :
  ∑' n:ℤ, f n = ∑ r:Fin d, ∑' k:ℤ, f ((r.val : ℤ) + (d:ℤ)*k) := by
  rw [← (intDecomp d hd).symm.tsum_eq f, Summable.tsum_prod, tsum_fintype]
  -- rw expression goal?
  · rfl
  · exact hf.comp_injective (intDecomp d hd).symm.injective
lemma summable_cexp_neg_pi_mul_int_sq {a:ℂ} (ha:0<a.re) :
 Summable (fun n:ℤ => Complex.exp (-(Real.pi:ℂ)*a*(n:ℂ)^2)) := by
 have h := (summable_jacobiTheta₂_term_iff (0:ℂ) (Complex.I*a)).2 (by simpa using ha)
 -- convert
 convert h using 1
 ext n
 simp [jacobiTheta₂_term]
 -- ring using I_sq
 ring_nf
 rw [Complex.I_sq]
 ring
lemma summable_rexp_neg_pi_int_sq :
 Summable (fun n:ℤ => Real.exp (-Real.pi * (n:ℝ)^2)) := by
 have h := summable_cexp_neg_pi_mul_int_sq (a:=(1:ℂ)) (by norm_num)
 have hn := h.norm
 convert hn using 1
 ext n
 rw [Complex.norm_exp]
 congr 1
 norm_cast
 simp

lemma tendsto_theta_twist_atTop (c:ℤ→ℂ) (hc:∀ n, ‖c n‖ ≤ 1) :
 Filter.Tendsto (fun u:ℝ => ∑' n:ℤ, Complex.exp (-(Real.pi:ℂ)*(u:ℂ)*(n:ℂ)^2) * c n)
   Filter.atTop (nhds (c 0)) := by
 have h := tendsto_tsum_of_dominated_convergence
   (𝓕:=Filter.atTop)
   (f:=fun u:ℝ => fun n:ℤ => Complex.exp (-(Real.pi:ℂ)*(u:ℂ)*(n:ℂ)^2) * c n)
   (g:=fun n:ℤ => if n=0 then c 0 else 0)
   summable_rexp_neg_pi_int_sq
   (by
     intro n
     by_cases hn:n=0
     · subst n; norm_num
     ·
       have hnpos : 0 < Real.pi * (n:ℝ)^2 := mul_pos Real.pi_pos (sq_pos_of_ne_zero (by exact_mod_cast hn))
       have ht : Filter.Tendsto (fun u:ℝ => -(Real.pi * (n:ℝ)^2) * u) Filter.atTop Filter.atBot :=
         Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hnpos) Filter.tendsto_id
       have he := Real.tendsto_exp_atBot.comp ht
       have hcplx : Filter.Tendsto (fun u:ℝ => (Real.exp (-(Real.pi * (n:ℝ)^2) * u) : ℂ)) Filter.atTop (nhds (0:ℂ)) :=
         (Complex.continuous_ofReal.tendsto 0).comp he
       have hterm : Filter.Tendsto (fun u:ℝ => ((Real.exp (-(Real.pi * (n:ℝ)^2) * u) : ℂ)) * c n)
         Filter.atTop (nhds ((0:ℂ)*c n)) := hcplx.mul_const _
       convert hterm using 1
       · ext u
         congr 1
         norm_cast
         <;> ring
       · simp [hn])
   (by
     filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with u hu n
     rw [norm_mul, Complex.norm_exp]
     have hs : 0 ≤ (n:ℝ)^2 := sq_nonneg _
     have hle : -Real.pi * u * (n:ℝ)^2 ≤ -Real.pi * (n:ℝ)^2 := by
       calc
        _ = (-Real.pi * (n:ℝ)^2) * u := by ring
        _ ≤ (-Real.pi * (n:ℝ)^2) * 1 := mul_le_mul_of_nonpos_left hu (by exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (neg_lt_zero.mpr Real.pi_pos)) hs)
        _ = _ := by ring
     have hre : ((n:ℂ)^2).re = (n:ℝ)^2 := by norm_cast
     have hnorm : Real.exp ((-(Real.pi:ℂ)*(u:ℂ)*(n:ℂ)^2).re) ≤ Real.exp (-Real.pi * (n:ℝ)^2) :=
       by simpa [Complex.mul_re, Complex.mul_im, hre] using (Real.exp_le_exp.mpr hle)
     calc
      _ ≤ Real.exp ((-(Real.pi:ℂ)*(u:ℂ)*(n:ℂ)^2).re) * 1 := mul_le_mul_of_nonneg_left (hc n) (by positivity)
      _ ≤ _ := by simpa using hnorm)
 simpa using h


/-- For a positive real number the complex square root factor occurring in
Poisson summation is just the (real) square root.  Keeping this elementary
conversion separate avoids having to choose branches later. -/
lemma ofReal_sqrt_cpow (a : ℝ) (ha : 0 ≤ a) :
    (Real.sqrt a : ℂ) = (a : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow]
  have h := Complex.ofReal_cpow ha (1/2:ℝ)
  convert h using 1 <;> norm_num

/-- A translated real Gaussian.  This is the form of Poisson summation that
is useful when the theta series is split into residue classes. -/
lemma sqrt_mul_gaussian_shift (a x : ℝ) (ha : 0 < a) :
    (Real.sqrt a : ℂ) *
          (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (a:ℂ) * ((k:ℂ) + (x:ℂ))^2))
      = (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) / (a:ℂ) * (n:ℂ)^2
                                  + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ))) := by
  have haC : ((a:ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hpow : (Real.sqrt a : ℂ) = (a:ℂ) ^ (1 / 2 : ℂ) :=
    ofReal_sqrt_cpow a (le_of_lt ha)
  have hpc : (a:ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro hh; have hh' := (Complex.cpow_eq_zero_iff _ _).1 hh; exact haC hh'.1
  have h := Complex.tsum_exp_neg_quadratic
       (a := (a:ℂ)) (by simpa using ha) (-(a:ℂ)*(x:ℂ))
  have hleft :
      (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (a:ℂ) * ((k:ℂ) + (x:ℂ))^2)) =
        Complex.exp (-(Real.pi:ℂ)*(a:ℂ)*(x:ℂ)^2) *
          (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ)*(a:ℂ)*(k:ℂ)^2
                                      + 2*(Real.pi:ℂ)* (-(a:ℂ)*(x:ℂ))*(k:ℂ))) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [← Complex.exp_add]
    congr 1
    ring
  have hright :
       Complex.exp (-(Real.pi:ℂ)*(a:ℂ)*(x:ℂ)^2) *
          (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)/(a:ℂ) *
                                     ((n:ℂ) + Complex.I * (-(a:ℂ)*(x:ℂ)))^2))
       = (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) / (a:ℂ) * (n:ℂ)^2
                                  + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ))) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [← Complex.exp_add]
    congr 1
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hleft, h]
  rw [div_eq_mul_inv]
  -- the square-root factor in Poisson summation cancels
  rw [hpow]
  -- after cancellation the remaining equality is `hright`
  calc
    (a:ℂ) ^ (1 / 2 : ℂ) *
          (Complex.exp (-(Real.pi:ℂ) * (a:ℂ) * (x:ℂ)^2) *
            ((1 * ((a:ℂ) ^ (1 / 2 : ℂ))⁻¹) *
              ∑' n : ℤ, Complex.exp
                (-(Real.pi:ℂ) / (a:ℂ) *
                  ((n:ℂ) + Complex.I * (-(a:ℂ)*(x:ℂ)))^2)))
        = Complex.exp (-(Real.pi:ℂ)*(a:ℂ)*(x:ℂ)^2) *
            (∑' n : ℤ, Complex.exp
              (-(Real.pi:ℂ)/(a:ℂ) *
                ((n:ℂ) + Complex.I * (-(a:ℂ)*(x:ℂ)))^2)) := by
          field_simp
    _ = _ := hright

/-- Boundary value of a single translated Gaussian.  Notice that no
uniformity in the translate is needed; later there will be only finitely
many of them. -/
lemma tendsto_sqrt_gaussian_shift (x : ℝ) :
    Filter.Tendsto
      (fun a : ℝ => (Real.sqrt a : ℂ) *
        (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (a:ℂ) * ((k:ℂ) + (x:ℂ))^2)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (1:ℂ)) := by
  let c : ℤ → ℂ := fun n =>
    Complex.exp (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ))
  have hc : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    dsimp [c]
    rw [Complex.norm_exp]
    have hz : (2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ)).re = 0 := by
      push_cast
      simp [Complex.mul_re]
    rw [hz]
    norm_num
  have ht := (tendsto_theta_twist_atTop c hc).comp
       (tendsto_inv_nhdsGT_zero (𝕜:=ℝ))
  have ht' : Filter.Tendsto
      (fun a : ℝ => ∑' n : ℤ,
          Complex.exp (-(Real.pi:ℂ)/(a:ℂ)*(n:ℂ)^2
                       + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (1:ℂ)) := by
    convert ht using 1
    · ext a
      apply tsum_congr
      intro n
      dsimp [c]
      rw [Complex.exp_add]
      congr 2
      push_cast
      rw [div_eq_mul_inv]
    · dsimp [c]
      norm_num
  -- the equality from Poisson summation holds throughout the punctured ray
  apply Filter.Tendsto.congr' _ ht'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (sqrt_mul_gaussian_shift a x ha).symm


/-- A Gaussian with a bounded periodic (or, in fact, arbitrary bounded)
coefficient is summable as soon as the real damping parameter is positive. -/
lemma summable_gaussian_mul_bounded
    (t : ℝ) (ht : 0 < t) (c : ℤ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) :
    Summable (fun n : ℤ =>
      Complex.exp (-(Real.pi:ℂ) * (t:ℂ) * (n:ℂ)^2) * c n) := by
  have he : Summable (fun n : ℤ =>
      Complex.exp (-(Real.pi:ℂ) * (t:ℂ) * (n:ℂ)^2)) :=
    summable_cexp_neg_pi_mul_int_sq (a := (t:ℂ)) (by simpa using ht)
  refine Summable.of_norm_bounded he.norm ?_
  intro n
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (hc n))

/-- Limit for a fixed congruence class modulo a positive integer.  It is the
translated Gaussian lemma with the harmless change of variables
`r + d k = d (k + r/d)`. -/
lemma tendsto_sqrt_gaussian_residue (d : ℕ) (hd : 0 < d) (r : ℤ) :
    Filter.Tendsto
      (fun s : ℝ => (Real.sqrt s : ℂ) *
        (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (s:ℂ) / (d:ℂ) *
                   (((r + (d:ℤ)*k : ℤ) : ℂ))^2)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds ((Real.sqrt (d:ℝ) : ℂ)⁻¹)) := by
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hsqd : (Real.sqrt (d:ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hdR)
  let x : ℝ := (r:ℝ) / (d:ℝ)
  have hscale : Filter.Tendsto (fun s : ℝ => s * (d:ℝ))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
    refine (tendsto_nhdsWithin_iff).2 ?_
    constructor
    · have h0 : Filter.Tendsto (fun s : ℝ => s * (d:ℝ))
          (nhds (0:ℝ)) (nhds ((0:ℝ) * (d:ℝ))) :=
          Filter.Tendsto.mul_const (d:ℝ) (Filter.tendsto_id)
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds h0)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hs hdR
  have hmain := (tendsto_sqrt_gaussian_shift x).comp hscale
  have hmul := Filter.Tendsto.const_mul
        ((Real.sqrt (d:ℝ) : ℂ)⁻¹) hmain
  have hmul' : Filter.Tendsto
      (fun s : ℝ => (Real.sqrt (d:ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (s * (d:ℝ)) : ℂ) *
            (∑' k : ℤ, Complex.exp
              (-(Real.pi:ℂ) * ((s * (d:ℝ)):ℂ) * ((k:ℂ) + (x:ℂ))^2))))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds ((Real.sqrt (d:ℝ) : ℂ)⁻¹)) := by
    convert hmul using 1 <;> simp
  apply Filter.Tendsto.congr' _ hmul'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : 0 ≤ s := le_of_lt hs
  have hsqrt : (Real.sqrt s : ℂ) =
          (Real.sqrt (d:ℝ) : ℂ)⁻¹ * (Real.sqrt (s * (d:ℝ)) : ℂ) := by
    rw [Real.sqrt_mul hs0]
    push_cast
    field_simp
  have hexp (k : ℤ) :
       Complex.exp (-(Real.pi:ℂ) * (s:ℂ) / (d:ℂ) *
                   (((r + (d:ℤ)*k : ℤ) : ℂ))^2)
       = Complex.exp
          (-(Real.pi:ℂ) * ((s * (d:ℝ)):ℂ) * ((k:ℂ) + (x:ℂ))^2) := by
    congr 1
    dsimp [x]
    push_cast
    field_simp
    ring
  have hsum :
      (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (s:ℂ) / (d:ℂ) *
                   (((r + (d:ℤ)*k : ℤ) : ℂ))^2)) =
      (∑' k : ℤ, Complex.exp
          (-(Real.pi:ℂ) * ((s * (d:ℝ)):ℂ) * ((k:ℂ) + (x:ℂ))^2)) :=
    tsum_congr hexp
  rw [hsum, hsqrt]
  ring



/-- The boundary value of a theta sum whose coefficient is periodic.  This is
also the little rational-boundary calculation one needs in passing from the
modular transformation to a finite Gauss sum.  The filter is from the
positive side; away from that filter none of the tsums are used. -/
lemma tendsto_sqrt_tsum_periodic (d : ℕ) (hd : 0 < d)
    (c : ℤ → ℂ)
    (hper : ∀ n k : ℤ, c (n + (d:ℤ) * k) = c n)
    (hc : ∀ n, ‖c n‖ ≤ 1) :
    Filter.Tendsto
      (fun s : ℝ => (Real.sqrt s : ℂ) *
        (∑' n : ℤ, Complex.exp
          (-(Real.pi:ℂ) * (s:ℂ) / (d:ℂ) * (n:ℂ)^2) * c n))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds ((Real.sqrt (d:ℝ) : ℂ)⁻¹ *
        (∑ r : Fin d, c (r.val : ℤ)))) := by
  -- first take the (finite) family of limits, one for each residue
  have hres (r : Fin d) : Filter.Tendsto
      (fun s : ℝ => (Real.sqrt s : ℂ) *
        (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (s:ℂ) / (d:ℂ) *
                  ((((r.val:ℤ) + (d:ℤ)*k : ℤ) : ℂ))^2) *
                    c (r.val:ℤ)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (((Real.sqrt (d:ℝ) : ℂ)⁻¹) * c (r.val:ℤ))) := by
    have hr := Filter.Tendsto.mul_const (c (r.val:ℤ))
        (tendsto_sqrt_gaussian_residue d hd (r.val:ℤ))
    convert hr using 1
    ext s
    rw [tsum_mul_right]
    ring
  have hfin : Filter.Tendsto
      (fun s : ℝ => ∑ r : Fin d,
          (Real.sqrt s : ℂ) *
            (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (s:ℂ) / (d:ℂ) *
                  ((((r.val:ℤ) + (d:ℤ)*k : ℤ) : ℂ))^2) *
                    c (r.val:ℤ)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (∑ r : Fin d,
          ((Real.sqrt (d:ℝ) : ℂ)⁻¹) * c (r.val:ℤ))) := by
    simpa using (tendsto_finset_sum (f := fun r (s:ℝ) =>
          (Real.sqrt s : ℂ) *
            (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (s:ℂ) / (d:ℂ) *
                  ((((r.val:ℤ) + (d:ℤ)*k : ℤ) : ℂ))^2) *
                    c (r.val:ℤ)))
          (a := fun r : Fin d =>
            ((Real.sqrt (d:ℝ) : ℂ)⁻¹) * c (r.val:ℤ)) Finset.univ
          (by
            intro r hr'
            exact hres r))
  have hfin' : Filter.Tendsto
      (fun s : ℝ => ∑ r : Fin d,
          (Real.sqrt s : ℂ) *
            (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (s:ℂ) / (d:ℂ) *
                  ((((r.val:ℤ) + (d:ℤ)*k : ℤ) : ℂ))^2) *
                    c (r.val:ℤ)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds ((Real.sqrt (d:ℝ) : ℂ)⁻¹ *
            (∑ r : Fin d, c (r.val:ℤ)))) := by
    simpa [Finset.mul_sum] using hfin
  -- On that filter the original tsum is summable, so that it may be split
  -- into those same residue classes.
  apply Filter.Tendsto.congr' _ hfin'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have ht : 0 < s / (d:ℝ) := div_pos hs hdR
  have hf0 := summable_gaussian_mul_bounded (s / (d:ℝ)) ht c hc
  have hf : Summable (fun n : ℤ =>
        Complex.exp (-(Real.pi:ℂ) * (s:ℂ) / (d:ℂ) * (n:ℂ)^2) * c n) := by
    convert hf0 using 1
    ext n
    congr 2
    push_cast
    rw [div_eq_mul_inv]
    ring
  rw [Int.tsum_decomp hf d hd]
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply tsum_congr
  intro k
  -- the factor `c` is constant on the class
  rw [hper]



/-- Poisson for a translated Gaussian with a complex damping coefficient.
It is sometimes convenient when approaching a rational point along a
non-vertical path. -/
lemma cpow_mul_gaussian_shift (a : ℂ) (x : ℝ) (ha : 0 < a.re) :
    a ^ (1 / 2 : ℂ) *
          (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * a * ((k:ℂ) + (x:ℂ))^2))
      = (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) / a * (n:ℂ)^2
                                  + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ))) := by
  have ha0 : a ≠ 0 := by
    intro h; simpa [h] using ha
  have hp : a ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h
    exact ha0 ((Complex.cpow_eq_zero_iff _ _).1 h).1
  have h := Complex.tsum_exp_neg_quadratic ha (-(a)*(x:ℂ))
  have hleft : (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * a * ((k:ℂ) + (x:ℂ))^2)) =
        Complex.exp (-(Real.pi:ℂ)*a*(x:ℂ)^2) *
          (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ)*a*(k:ℂ)^2
                                      + 2*(Real.pi:ℂ)* (-a*(x:ℂ))*(k:ℂ))) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [← Complex.exp_add]
    congr 1
    ring
  have hright :
       Complex.exp (-(Real.pi:ℂ)*a*(x:ℂ)^2) *
          (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)/a *
                                     ((n:ℂ) + Complex.I * (-a*(x:ℂ)))^2))
       = (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) / a * (n:ℂ)^2
                                  + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ))) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [← Complex.exp_add]
    congr 1
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hleft, h]
  rw [div_eq_mul_inv]
  calc
    a ^ (1 / 2 : ℂ) *
          (Complex.exp (-(Real.pi:ℂ) * a * (x:ℂ)^2) *
            ((1 * (a ^ (1 / 2 : ℂ))⁻¹) *
              ∑' n : ℤ, Complex.exp
                (-(Real.pi:ℂ) / a *
                  ((n:ℂ) + Complex.I * (-a*(x:ℂ)))^2)))
        = Complex.exp (-(Real.pi:ℂ)*a*(x:ℂ)^2) *
            (∑' n : ℤ, Complex.exp
              (-(Real.pi:ℂ)/a *
                ((n:ℂ) + Complex.I * (-a*(x:ℂ)))^2)) := by
          field_simp
    _ = _ := hright

/-- Nontangential boundary value of one translated Gaussian.  Expressing the
condition in terms of the real part of `a⁻¹` makes it directly usable for
rational theta paths. -/
lemma tendsto_cpow_gaussian_shift
   {ι : Type*} {L : Filter ι} (a : ι → ℂ) (x : ℝ)
   (ha : ∀ᶠ t in L, 0 < (a t).re)
   (hinv : Filter.Tendsto (fun t => (a t)⁻¹.re) L Filter.atTop) :
   Filter.Tendsto
    (fun t => (a t) ^ (1 / 2 : ℂ) *
       (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (a t) * ((k:ℂ) + (x:ℂ))^2)))
    L (nhds (1:ℂ)) := by
  have hpoint (n : ℤ) : Filter.Tendsto
      (fun t => Complex.exp (-(Real.pi:ℂ) / (a t) * (n:ℂ)^2
                                  + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ))) L
      (nhds (if n = 0 then 1 else 0)) := by
    by_cases hn : n = 0
    · subst n
      simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : ι => (1:ℂ)) L (nhds 1))
    · have hnR : 0 < (n:ℝ)^2 := sq_pos_of_ne_zero (by exact_mod_cast hn)
      have hu : Filter.Tendsto
            (fun t => (-Real.pi * (n:ℝ)^2) * ((a t)⁻¹.re)) L Filter.atBot :=
          Filter.Tendsto.const_mul_atTop_of_neg
            (by exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hnR) hinv
      have he : Filter.Tendsto
            (fun t => Real.exp ((-Real.pi * (n:ℝ)^2) * ((a t)⁻¹.re))) L
              (nhds (0:ℝ)) := Real.tendsto_exp_atBot.comp hu
      have hnorm : (fun t => ‖Complex.exp (-(Real.pi:ℂ) / (a t) * (n:ℂ)^2
                                  + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ))‖)
             = (fun t => Real.exp ((-Real.pi * (n:ℝ)^2) * ((a t)⁻¹.re))) := by
        funext t
        rw [Complex.norm_exp]
        congr 1
        rw [div_eq_mul_inv]
        -- the second exponent is purely imaginary
        have hre : ((n:ℂ)^2).re = (n:ℝ)^2 := by norm_cast
        have him : ((n:ℂ)^2).im = 0 := by norm_cast
        push_cast
        simp [Complex.mul_re, Complex.mul_im, hre, him]
        ring
      have hz : Filter.Tendsto
          (fun t => Complex.exp (-(Real.pi:ℂ) / (a t) * (n:ℂ)^2
                                  + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ))) L
          (nhds (0:ℂ)) :=
        (tendsto_zero_iff_norm_tendsto_zero.2 (by rw [hnorm]; exact he))
      simpa [hn] using hz
  have hdom : ∀ᶠ t in L, ∀ n : ℤ,
      ‖Complex.exp (-(Real.pi:ℂ) / (a t) * (n:ℂ)^2
                                  + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ))‖
       ≤ Real.exp (-Real.pi * (n:ℝ)^2) := by
    have hge : ∀ᶠ t in L, (1:ℝ) ≤ (a t)⁻¹.re :=
        (Filter.eventually_ge_atTop 1 |> (hinv.eventually ·))
    filter_upwards [hge] with t ht n
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hn0 : 0 ≤ (n:ℝ)^2 := sq_nonneg _
    have hm : (-Real.pi * (n:ℝ)^2) * ((a t)⁻¹.re)
           ≤ (-Real.pi * (n:ℝ)^2) * 1 :=
      mul_le_mul_of_nonpos_left ht
        (by exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (neg_lt_zero.mpr Real.pi_pos)) hn0)
    rw [mul_one] at hm
    convert hm using 1
    have hre : ((n:ℂ)^2).re = (n:ℝ)^2 := by norm_cast
    have him : ((n:ℂ)^2).im = 0 := by norm_cast
    push_cast
    simp [Complex.mul_re, Complex.mul_im, div_eq_mul_inv, hre, him]
    <;> ring
  have hts := tendsto_tsum_of_dominated_convergence
        (𝓕 := L)
        (f := fun t : ι => fun n : ℤ =>
          Complex.exp (-(Real.pi:ℂ) / (a t) * (n:ℂ)^2
                                  + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ)))
        (g := fun n : ℤ => if n = 0 then (1:ℂ) else 0)
        summable_rexp_neg_pi_int_sq hpoint hdom
  have hlim : Filter.Tendsto
       (fun t => ∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) / (a t) * (n:ℂ)^2
                                  + 2*(Real.pi:ℂ)*Complex.I*(n:ℂ)*(x:ℂ))) L
       (nhds (1:ℂ)) := by
    simpa using hts
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [ha] with t ht
  exact (cpow_mul_gaussian_shift (a t) x ht).symm



/-- A convenient specialization of the preceding boundary lemma: it is the
vertical boundary value of the Jacobi theta series at `2 b / d`. -/
lemma tendsto_jacobiTheta_rational (d b : ℕ) (hd : 0 < d) :
    Filter.Tendsto
      (fun s : ℝ => (Real.sqrt s : ℂ) *
        jacobiTheta (((2*b:ℕ):ℂ) / (d:ℂ) + Complex.I * (s:ℂ) / (d:ℂ)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds ((Real.sqrt (d:ℝ) : ℂ)⁻¹ *
        (∑ r : Fin d,
          Complex.exp ((Real.pi:ℂ) * Complex.I *
               ((r.val:ℂ)^2 * (((2*b:ℕ)):ℂ) / (d:ℂ)))))) := by
  let c : ℤ → ℂ := fun n =>
      Complex.exp ((Real.pi:ℂ) * Complex.I *
               ((n:ℂ)^2 * (((2*b:ℕ)):ℂ) / (d:ℂ)))
  have hper : ∀ n k : ℤ, c (n + (d:ℤ)*k) = c n := by
    intro n k
    dsimp [c]
    exact exp_even_period_zsmul n k d b (by omega)
  have hc : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    dsimp [c]
    rw [Complex.norm_exp]
    have hz : ((Real.pi:ℂ) * Complex.I *
               ((n:ℂ)^2 * (((2*b:ℕ)):ℂ) / (d:ℂ))).re = 0 := by
      have him : ((n:ℂ)^2).im = 0 := by norm_cast
      have hre : ((n:ℂ)^2).re = (n:ℝ)^2 := by norm_cast
      push_cast
      simp [Complex.mul_re, Complex.mul_im, him, hre]
    rw [hz]
    norm_num
  have h := tendsto_sqrt_tsum_periodic d hd c hper hc
  -- rewrite the series term-by-term
  convert h using 1
  · ext s
    congr 1
    unfold jacobiTheta
    apply tsum_congr
    intro n
    dsimp [c]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · rfl

lemma sqrt_mul_cpow_mul_real (s:ℝ) (hs:0<s) (B:ℂ) (hB:B≠0) :
 (Real.sqrt s:ℂ) * (((s:ℂ)*B)^(1/2:ℂ))⁻¹ = (B^(1/2:ℂ))⁻¹ := by
 have hsC : (s:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
 have he : ((s:ℂ)*B)^(1/2:ℂ) = ((s:ℂ)^(1/2:ℂ))*(B^(1/2:ℂ)) := by
   rw [Complex.cpow_def, if_neg (mul_ne_zero hsC hB),
       Complex.cpow_def, if_neg hsC,
       Complex.cpow_def, if_neg hB,
       Complex.log_ofReal_mul hs hB]
   rw [add_mul, Complex.exp_add, Complex.ofReal_log (le_of_lt hs)]
 have hsqrt : (Real.sqrt s:ℂ) = (s:ℂ)^(1/2:ℂ) := by
   rw [Real.sqrt_eq_rpow]
   have h := Complex.ofReal_cpow (le_of_lt hs) (1/2:ℝ)
   convert h using 1 <;> norm_num
 rw [he, mul_inv_rev]
 have hpow : (s:ℂ)^(1/2:ℂ) ≠ 0 := by
   intro h; exact hsC ((Complex.cpow_eq_zero_iff _ _).1 h).1
 rw [hsqrt]
 field_simp
open Complex
lemma cusp_factor_eval (P D:ℝ) (hP:0<P) (hD:0<D) :
 ((-Complex.I * ((D/P:ℝ):ℂ))^(1/2:ℂ))⁻¹ * (((P:ℝ):ℂ)^(1/2:ℂ))⁻¹
 = Complex.exp ((Real.pi:ℂ)*Complex.I/4) * (Real.sqrt D:ℂ)⁻¹ := by
 have hR : 0 < D/P := div_pos hD hP
 have hR0 : (((D/P:ℝ):ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt hR)
 have hnegI : (-Complex.I) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
 have he : (-Complex.I * ((D/P:ℝ):ℂ))^(1/2:ℂ)
        = ((D/P:ℝ):ℂ)^(1/2:ℂ) * Complex.exp (-(Real.pi:ℂ)*Complex.I/4) := by
   rw [mul_comm]
   rw [Complex.cpow_def, if_neg (mul_ne_zero hR0 hnegI),
       Complex.log_ofReal_mul hR hnegI]
   -- split
   rw [add_mul, Complex.exp_add]
   rw [Complex.ofReal_log (le_of_lt hR)]
   rw [← Complex.cpow_def_of_ne_zero hR0]
   rw [Complex.log_neg_I]
   congr 1
   ring
 have hsP : (((P:ℝ):ℂ)^(1/2:ℂ)) = (Real.sqrt P:ℂ) := by
   symm
   rw [Real.sqrt_eq_rpow]
   have z := Complex.ofReal_cpow (le_of_lt hP) (1/2:ℝ)
   convert z using 1 <;> norm_num
 have hsR : (((D/P:ℝ):ℂ)^(1/2:ℂ)) = (Real.sqrt (D/P):ℂ) := by
   symm
   rw [Real.sqrt_eq_rpow]
   have z := Complex.ofReal_cpow (le_of_lt hR) (1/2:ℝ)
   convert z using 1 <;> norm_num
 rw [he, hsR, hsP, mul_inv_rev]
 have hexp : (Complex.exp (-(Real.pi:ℂ)*Complex.I/4))⁻¹ =
          Complex.exp ((Real.pi:ℂ)*Complex.I/4) := by rw [← Complex.exp_neg]; congr 1; ring
 rw [hexp]
 have hsD : (Real.sqrt D:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_ne_zero'.mpr hD)
 have hsp : (Real.sqrt P:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_ne_zero'.mpr hP)
 have hsr : (Real.sqrt (D/P):ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_ne_zero'.mpr hR)
 have hmul : (Real.sqrt (D/P):ℝ) * Real.sqrt P = Real.sqrt D := by
   rw [← Real.sqrt_mul (le_of_lt hR)]
   congr 1
   field_simp
 field_simp
 exact_mod_cast hmul.symm





lemma summable_cgaussian_mul_bounded
    (a : ℂ) (ha : 0 < a.re) (c : ℤ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) :
    Summable (fun n : ℤ =>
      Complex.exp (-(Real.pi:ℂ) * a * (n:ℂ)^2) * c n) := by
  have he : Summable (fun n : ℤ =>
      Complex.exp (-(Real.pi:ℂ) * a * (n:ℂ)^2)) :=
    summable_cexp_neg_pi_mul_int_sq ha
  refine Summable.of_norm_bounded he.norm ?_
  intro n
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hc n)

lemma tendsto_cpow_tsum_periodic_scaled
    {ι : Type*} {L : Filter ι} (d : ℕ) (hd : 0 < d)
    (c : ℤ → ℂ)
    (hper : ∀ n k : ℤ, c (n + (d:ℤ) * k) = c n)
    (hc : ∀ n, ‖c n‖ ≤ 1)
    (a : ι → ℂ)
    (ha : ∀ᶠ t in L, 0 < (a t).re)
    (hinv : Filter.Tendsto (fun t => (a t)⁻¹.re) L Filter.atTop) :
    Filter.Tendsto
      (fun t => (a t) ^ (1 / 2 : ℂ) *
        (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ) * (a t) / (d:ℂ)^2 * (n:ℂ)^2) * c n))
      L (nhds (∑ r : Fin d, c (r.val:ℤ))) := by
  have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hres (r : Fin d) : Filter.Tendsto
      (fun t => (a t) ^ (1 / 2 : ℂ) *
        (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (a t) / (d:ℂ)^2 *
                 ((((r.val:ℤ) + (d:ℤ)*k : ℤ) : ℂ))^2) * c (r.val:ℤ)))
      L (nhds (c (r.val:ℤ))) := by
    let x : ℝ := (r.val:ℝ) / (d:ℝ)
    have hx := tendsto_cpow_gaussian_shift a x ha hinv
    have hx' := Filter.Tendsto.mul_const (c (r.val:ℤ)) hx
    have heq (t : ι) :
        (a t) ^ (1 / 2 : ℂ) *
          (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (a t) / (d:ℂ)^2 *
               ((((r.val:ℤ) + (d:ℤ)*k : ℤ) : ℂ))^2) * c (r.val:ℤ))
        = ((a t) ^ (1 / 2 : ℂ) *
            (∑' k : ℤ, Complex.exp
                (-(Real.pi:ℂ) * (a t) * ((k:ℂ) + (x:ℂ))^2))) * c (r.val:ℤ) := by
      have hk (k : ℤ) :
          Complex.exp (-(Real.pi:ℂ) * (a t) / (d:ℂ)^2 *
               ((((r.val:ℤ) + (d:ℤ)*k : ℤ) : ℂ))^2)
          = Complex.exp (-(Real.pi:ℂ) * (a t) * ((k:ℂ) + (x:ℂ))^2) := by
        congr 1
        dsimp [x]
        push_cast
        field_simp
        ring
      rw [tsum_mul_right]
      rw [tsum_congr hk]
      ring
    convert hx' using 1
    · ext t
      exact heq t
    · simp
  have hfin : Filter.Tendsto
      (fun t => ∑ r : Fin d, (a t) ^ (1 / 2 : ℂ) *
        (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (a t) / (d:ℂ)^2 *
             ((((r.val:ℤ) + (d:ℤ)*k : ℤ) : ℂ))^2) * c (r.val:ℤ)))
      L (nhds (∑ r : Fin d, c (r.val:ℤ))) := by
    simpa using
      (tendsto_finset_sum (f := fun r (t : ι) =>
          (a t) ^ (1 / 2 : ℂ) *
            (∑' k : ℤ, Complex.exp (-(Real.pi:ℂ) * (a t) / (d:ℂ)^2 *
               ((((r.val:ℤ) + (d:ℤ)*k : ℤ) : ℂ))^2) * c (r.val:ℤ)))
        (a := fun r : Fin d => c (r.val:ℤ)) Finset.univ
        (by intro r hr; exact hres r))
  apply Filter.Tendsto.congr' _ hfin
  filter_upwards [ha] with t ht
  have hcoef : 0 < (a t / (d:ℂ)^2).re := by
    have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
    have hn : (d:ℝ) ≠ 0 := ne_of_gt hdR
    have ee : (a t / (d:ℂ)^2).re = (a t).re / (d:ℝ)^2 := by
      simp [Complex.div_re, Complex.normSq, pow_two,
            Complex.mul_re, Complex.mul_im]
      field_simp
    rw [ee]
    exact div_pos ht (sq_pos_of_pos hdR)
  have hsum : Summable (fun n : ℤ =>
       Complex.exp (-(Real.pi:ℂ) * (a t) / (d:ℂ)^2 * (n:ℂ)^2) * c n) := by
    have h0 := summable_cgaussian_mul_bounded
        (a t / (d:ℂ)^2) hcoef c hc
    convert h0 using 1
    ext n
    congr 2
    ring
  rw [Int.tsum_decomp hsum d hd]
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  apply tsum_congr
  intro k
  rw [hper]

lemma tendsto_jacobiTheta_reciprocal_path (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) :
    Filter.Tendsto
      (fun s : ℝ =>
        (((p:ℂ) * (s:ℂ) * ((2*q:ℕ):ℂ) /
              (((2*q:ℕ):ℂ) + Complex.I * (s:ℂ))) ^ (1 / 2 : ℂ)) *
          jacobiTheta (- (1:ℂ) /
            ((((2*q:ℕ):ℂ)/(p:ℂ)) + Complex.I*(s:ℂ)/(p:ℂ))))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (∑ r : Fin (2*q),
          Complex.exp ((Real.pi:ℂ) * Complex.I *
            ((r.val:ℂ)^2 * ((-(p:ℤ):ℤ):ℂ) / ((2*q:ℕ):ℂ))))) := by
  let D : ℝ := (2*q:ℕ)
  let P : ℝ := p
  have hP : 0 < P := by dsimp [P]; exact_mod_cast hp
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (by omega : 0 < 2*q)
  have hP0 : P ≠ 0 := ne_of_gt hP
  have hD0 : D ≠ 0 := ne_of_gt hD
  let a : ℝ → ℂ := fun s =>
       (P:ℂ) * (s:ℂ) * (D:ℂ) / ((D:ℂ) + Complex.I * (s:ℂ))
  let c : ℤ → ℂ := fun n =>
       Complex.exp ((Real.pi:ℂ) * Complex.I *
         ((n:ℂ)^2 * ((-(p:ℤ):ℤ):ℂ) / ((2*q:ℕ):ℂ)))
  have hper : ∀ n k : ℤ, c (n + ((2*q:ℕ):ℤ)*k) = c n := by
    intro n k
    dsimp [c]
    exact exp_neg_evenmod_period_zsmul n k p q (by omega)
  have hc : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    dsimp [c]
    rw [Complex.norm_exp]
    have hz : ((Real.pi:ℂ) * Complex.I *
         ((n:ℂ)^2 * ((-(p:ℤ):ℤ):ℂ) / ((2*q:ℕ):ℂ))).re = 0 := by
      have hre : ((n:ℂ)^2).re = (n:ℝ)^2 := by norm_cast
      have him : ((n:ℂ)^2).im = 0 := by norm_cast
      push_cast
      simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
            Complex.normSq, pow_two]
    rw [hz]
    norm_num
  have ha : ∀ᶠ s : ℝ in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < (a s).re := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have e : (a s).re = P*s*D*D/(D^2+s^2) := by
      dsimp [a]
      simp [Complex.div_re, Complex.normSq,
            Complex.mul_re, Complex.mul_im]
      ring
    rw [e]
    have hdens : 0 < D^2 + s^2 := by nlinarith [sq_pos_of_pos hD, sq_nonneg s]
    have hnum : 0 < P*s*D*D := by
      exact mul_pos (mul_pos (mul_pos hP hs) hD) hD
    exact div_pos hnum hdens
  have hainv : Filter.Tendsto (fun s : ℝ => (a s)⁻¹.re)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) Filter.atTop := by
    have hbase := (tendsto_inv_nhdsGT_zero (𝕜:=ℝ))
    have hbase' := hbase.atTop_mul_const (by positivity : 0 < (P:ℝ)⁻¹)
    apply Filter.Tendsto.congr' _ hbase'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have ee : (a s)⁻¹.re = 1/(P*s) := by
      dsimp [a]
      rw [Complex.inv_re]
      simp [Complex.div_re, Complex.normSq,
            Complex.mul_re, Complex.mul_im]
      have hden : D*D + s*s ≠ 0 := by
        nlinarith [sq_pos_of_pos hD, sq_nonneg s]
      field_simp
    rw [ee]
    field_simp
  have hbig := tendsto_cpow_tsum_periodic_scaled
      (ι:=ℝ) (L:=nhdsWithin (0:ℝ) (Set.Ioi 0))
      (2*q) (by omega) c hper hc a ha hainv
  convert hbig using 1
  · ext s
    congr 1
    unfold jacobiTheta
    apply tsum_congr
    intro n
    dsimp [c]
    rw [← Complex.exp_add]
    congr 1
    have hzden : ((D:ℂ) + Complex.I*(s:ℂ)) ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      have hz : D = 0 := by simpa [Complex.mul_re, Complex.mul_im] using h'
      exact hD0 hz
    have hpC : (P:ℂ) ≠ 0 := by exact_mod_cast hP0
    have hdC : (D:ℂ) ≠ 0 := by exact_mod_cast hD0
    have hzpath :
          - (1:ℂ) / ((D:ℂ)/(P:ℂ) + Complex.I*(s:ℂ)/(P:ℂ))
          = -(P:ℂ)/(D:ℂ) +
              Complex.I * (a s) / (D:ℂ)^2 := by
      dsimp [a]
      field_simp
      ring
    dsimp [D, P] at hzpath hpC hdC ⊢
    rw [hzpath]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · rfl




open scoped UpperHalfPlane

/-- Equality of the two finite residue sums, obtained by taking the two
bounds of the theta transformation on the arc ` (2q+is)/p `. -/
lemma gauss_fin_reciprocal (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (∑ r : Fin (2*q), Complex.exp ((Real.pi:ℂ) * Complex.I *
       ((r.val:ℂ)^2 * ((-(p:ℤ):ℤ):ℂ) / ((2*q:ℕ):ℂ))))
    = ((-Complex.I) * ((((2*q:ℕ):ℝ)/(p:ℝ) : ℝ):ℂ)) ^ (1/2:ℂ) *
      (∑ r : Fin p, Complex.exp ((Real.pi:ℂ) * Complex.I *
       ((r.val:ℂ)^2 * (((2*q:ℕ)):ℂ) / (p:ℂ)))) := by
  let L : Filter ℝ := nhdsWithin (0:ℝ) (Set.Ioi 0)
  let D : ℝ := (2*q:ℕ)
  let P : ℝ := p
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (by omega : 0 < 2*q)
  have hP : 0 < P := by dsimp [P]; exact_mod_cast hp
  have hDC : (D:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have hPC : (P:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hP)
  let z : ℝ → ℂ := fun s => (D:ℂ)/(P:ℂ) + Complex.I*(s:ℂ)/(P:ℂ)
  let X : ℝ → ℂ := fun s => (P:ℂ)*(D:ℂ)/((D:ℂ)+Complex.I*(s:ℂ))
  let AA : ℂ := ∑ r : Fin p, Complex.exp ((Real.pi:ℂ) * Complex.I *
       ((r.val:ℂ)^2 * (((2*q:ℕ)):ℂ) / (p:ℂ)))
  let BB : ℂ := ∑ r : Fin (2*q), Complex.exp ((Real.pi:ℂ) * Complex.I *
       ((r.val:ℂ)^2 * ((-(p:ℤ):ℤ):ℂ) / ((2*q:ℕ):ℂ)))
  have hsC : Filter.Tendsto (fun s : ℝ => (s:ℂ)) L (nhds (0:ℂ)) :=
    (Complex.continuous_ofReal.tendsto (0:ℝ) |>
      tendsto_nhdsWithin_of_tendsto_nhds)
  have hz : Filter.Tendsto z L (nhds ((D:ℂ)/(P:ℂ))) := by
    dsimp [z]
    convert
      ( (tendsto_const_nhds.add
           ((tendsto_const_nhds.mul hsC).div_const (P:ℂ))) :
        Filter.Tendsto (fun s : ℝ => (D:ℂ)/(P:ℂ) + Complex.I*(s:ℂ)/(P:ℂ))
          L (nhds ((D:ℂ)/(P:ℂ) + Complex.I*0/(P:ℂ))) ) using 1 <;> simp
  have hX : Filter.Tendsto X L (nhds (P:ℂ)) := by
    have hd := (tendsto_const_nhds.add (tendsto_const_nhds.mul hsC) :
       Filter.Tendsto (fun s : ℝ => (D:ℂ)+Complex.I*(s:ℂ)) L
          (nhds ((D:ℂ)+Complex.I*0)))
    have hn : Filter.Tendsto (fun _ : ℝ => (P:ℂ)*(D:ℂ)) L
          (nhds ((P:ℂ)*(D:ℂ))) := tendsto_const_nhds
    have ht := hn.div hd (by simpa using hDC)
    convert ht using 1
    · rfl
    · congr 1
      simp [hDC]
  have hXp : Filter.Tendsto (fun s => (X s) ^ (1/2:ℂ)) L
        (nhds ((P:ℂ) ^ (1/2:ℂ))) := by
    exact hX.cpow tendsto_const_nhds (by
      apply Complex.ofReal_mem_slitPlane.2
      exact hP)
  have hzp : Filter.Tendsto (fun s => ((-Complex.I) * (z s)) ^ (1/2:ℂ)) L
        (nhds (((-Complex.I) * ((D:ℂ)/(P:ℂ))) ^ (1/2:ℂ))) := by
    have harg : ((-Complex.I) * ((D:ℂ)/(P:ℂ))) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      right
      -- the imaginary part is `-D/P`
      simp [Complex.mul_im, Complex.mul_re, Complex.div_im, Complex.div_re,
            Complex.normSq]
      exact ⟨ne_of_gt hD, ne_of_gt hP⟩
    exact ((Filter.Tendsto.const_mul (-Complex.I) hz).cpow tendsto_const_nhds harg)
  have hF : Filter.Tendsto
      (fun s : ℝ => (Real.sqrt s : ℂ) * jacobiTheta (z s)) L
      (nhds ((Real.sqrt (p:ℝ) : ℂ)⁻¹ * AA)) := by
    have hf := tendsto_jacobiTheta_rational p q hp
    dsimp [L]
    convert hf using 1 <;> rfl
  have hcalc : Filter.Tendsto
      (fun s : ℝ =>
         (X s) ^ (1/2:ℂ) * ((-Complex.I) * z s) ^ (1/2:ℂ) *
           ((Real.sqrt s : ℂ) * jacobiTheta (z s))) L
      (nhds (((P:ℂ)^(1/2:ℂ)) *
          (((-Complex.I) * ((D:ℂ)/(P:ℂ)))^(1/2:ℂ)) *
            ((Real.sqrt (p:ℝ) : ℂ)⁻¹ * AA))) :=
    (hXp.mul hzp).mul hF
  have heq :
      (fun s : ℝ =>
        (((p:ℂ) * (s:ℂ) * ((2*q:ℕ):ℂ) /
              (((2*q:ℕ):ℂ) + Complex.I * (s:ℂ))) ^ (1 / 2 : ℂ)) *
          jacobiTheta (- (1:ℂ) /
            ((((2*q:ℕ):ℂ)/(p:ℂ)) + Complex.I*(s:ℂ)/(p:ℂ))))
      =ᶠ[L]
      (fun s : ℝ =>
         (X s) ^ (1/2:ℂ) * ((-Complex.I) * z s) ^ (1/2:ℂ) *
           ((Real.sqrt s : ℂ) * jacobiTheta (z s))) := by
    filter_upwards [ (show ∀ᶠ s : ℝ in L, s ∈ Set.Ioi (0:ℝ) from
        self_mem_nhdsWithin) ] with s hs
    have hXs : X s ≠ 0 := by
      dsimp [X]
      have hdens : (D:ℂ)+Complex.I*(s:ℂ) ≠ 0 := by
        intro h
        have hh := congrArg Complex.re h
        have hz0 : D = 0 := by
          simpa [Complex.mul_re, Complex.mul_im] using hh
        exact (ne_of_gt hD) hz0
      exact div_ne_zero (mul_ne_zero hPC hDC) hdens
    have hscale :
        (((p:ℂ)*(s:ℂ)*((2*q:ℕ):ℂ) /
             (((2*q:ℕ):ℂ)+Complex.I*(s:ℂ))) ^ (1/2:ℂ))
        = (Real.sqrt s:ℂ) * (X s) ^ (1/2:ℂ) := by
      have harg : (p:ℂ)*(s:ℂ)*((2*q:ℕ):ℂ) /
             (((2*q:ℕ):ℂ)+Complex.I*(s:ℂ))
           = (s:ℂ) * (X s) := by
        dsimp [X, D, P]
        push_cast
        ring
      rw [harg]
      have hs0 : (s:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
      rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hs0 hXs),
          Complex.log_ofReal_mul hs hXs, add_mul, Complex.exp_add]
      rw [Complex.ofReal_log (le_of_lt hs)]
      rw [← Complex.cpow_def_of_ne_zero hs0,
          ← Complex.cpow_def_of_ne_zero hXs]
      rw [← ofReal_sqrt_cpow s (le_of_lt hs)]
    have hzpos : 0 < (z s).im := by
      dsimp [z]
      have he : (( (D:ℂ)/(P:ℂ) + Complex.I*(s:ℂ)/(P:ℂ))).im = s / P := by
        field_simp
        simp [Complex.mul_re, Complex.mul_im]
        field_simp
      change 0 < (( (D:ℂ)/(P:ℂ) + Complex.I*(s:ℂ)/(P:ℂ))).im
      rw [he]
      exact div_pos hs hP
    have hmod : jacobiTheta (- (1:ℂ) / (z s)) =
          ((-Complex.I) * (z s)) ^ (1/2:ℂ) * jacobiTheta (z s) := by
      let τ : ℍ := ⟨z s, hzpos⟩
      have hh := jacobiTheta_S_smul τ
      rw [UpperHalfPlane.modular_S_smul] at hh
      dsimp [τ] at hh
      convert hh using 1 <;> ring
    change
       (((p:ℂ)*(s:ℂ)*((2*q:ℕ):ℂ) /
             (((2*q:ℕ):ℂ)+Complex.I*(s:ℂ))) ^ (1/2:ℂ)) *
          jacobiTheta (-(1:ℂ) / z s)
       = _
    rw [hscale, hmod]
    ring
  have hR := tendsto_jacobiTheta_reciprocal_path p q hp hq
  have hother : Filter.Tendsto
      (fun s : ℝ =>
        (((p:ℂ) * (s:ℂ) * ((2*q:ℕ):ℂ) /
              (((2*q:ℕ):ℂ) + Complex.I * (s:ℂ))) ^ (1 / 2 : ℂ)) *
          jacobiTheta (- (1:ℂ) /
            ((((2*q:ℕ):ℂ)/(p:ℂ)) + Complex.I*(s:ℂ)/(p:ℂ))))
      L (nhds (((P:ℂ)^(1/2:ℂ)) *
          (((-Complex.I) * ((D:ℂ)/(P:ℂ)))^(1/2:ℂ)) *
            ((Real.sqrt (p:ℝ) : ℂ)⁻¹ * AA))) :=
    Filter.Tendsto.congr' heq.symm hcalc
  have hlimit : BB = ((P:ℂ)^(1/2:ℂ)) *
          (((-Complex.I) * ((D:ℂ)/(P:ℂ)))^(1/2:ℂ)) *
            ((Real.sqrt (p:ℝ) : ℂ)⁻¹ * AA) := by
    exact tendsto_nhds_unique (by
      dsimp [L, BB]
      convert hR using 1) hother
  have hsqrtp : (P:ℂ)^(1/2:ℂ) = (Real.sqrt (p:ℝ) : ℂ) := by
    simpa [P] using (ofReal_sqrt_cpow (p:ℝ) (by exact_mod_cast (le_of_lt hp))).symm
  have hsp : (Real.sqrt (p:ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hp))
  dsimp [AA, BB] at *
  rw [hsqrtp] at hlimit
  -- cancel the auxiliary square roots
  have hsimple :
      (∑ r : Fin (2*q), Complex.exp ((Real.pi:ℂ)*Complex.I *
       ((r.val:ℂ)^2 * ((-(p:ℤ):ℤ):ℂ) / ((2*q:ℕ):ℂ))))
       = (((-Complex.I) * ((D:ℂ)/(P:ℂ)))^(1/2:ℂ)) *
          (∑ r : Fin p, Complex.exp ((Real.pi:ℂ)*Complex.I *
       ((r.val:ℂ)^2 * (((2*q:ℕ)):ℂ) / (p:ℂ)))) := by
    -- after canceling `sqrt p`; keep the summands' order unchanged
    rw [hlimit]
    field_simp
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    congr 1 <;> ring
  simpa [D, P] using hsimple


lemma cpow_neg_I_mul_pos (t:ℝ) (ht:0<t) :
 ((-Complex.I)*(t:ℂ))^(1/2:ℂ) =
 (Real.sqrt t : ℂ) * Complex.exp (-(Real.pi:ℂ)*Complex.I/4) := by
 have he : (1/2:ℂ) = ((1/2:ℝ):ℂ) := by norm_num
 rw [he, Complex.cpow_ofReal]
 have hn : ‖(-Complex.I) * (t:ℂ)‖ = t := by
   rw [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg (le_of_lt ht)]
   simp
 have ha : ((-Complex.I) * (t:ℂ)).arg = -(Real.pi/2) := by
   rw [mul_comm]
   exact (Complex.arg_real_mul (-Complex.I) ht).trans Complex.arg_neg_I
 rw [hn, ha]
 rw [← Real.sqrt_eq_rpow]
 -- exp
 rw [show -(Real.pi:ℂ)*Complex.I/4 = ((-(Real.pi/4):ℝ):ℂ)*Complex.I by
       push_cast; ring]
 rw [Complex.exp_mul_I]
 congr 2 <;> push_cast <;> ring

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem landsberg_schaar (p q : ℕ) (hp : Odd p) (hq : Odd q) :
    gaussS (2 * q : ℕ) p
      = Complex.exp ((Real.pi : ℂ) * Complex.I / 4) * gaussS (-(p : ℤ)) (2 * q) :=
/-ResultProofBegin-/by
  classical
  have hp0 : 0 < p := hp.pos
  have hq0 : 0 < q := hq.pos
  let A : ℂ := ∑ r : Fin p, Complex.exp ((Real.pi:ℂ) * Complex.I *
       ((r.val:ℂ)^2 * (((2*q:ℕ)):ℂ) / (p:ℂ)))
  let B : ℂ := ∑ r : Fin (2*q), Complex.exp ((Real.pi:ℂ) * Complex.I *
       ((r.val:ℂ)^2 * ((-(p:ℤ):ℤ):ℂ) / ((2*q:ℕ):ℂ)))
  let K : ℂ := ((-Complex.I) * ((((2*q:ℕ):ℝ)/(p:ℝ) : ℝ):ℂ)) ^ (1/2:ℂ)
  have hrec : B = K * A := by
    dsimp [A, B, K]
    exact gauss_fin_reciprocal p q hp0 hq0
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp0
  have hdR : (0:ℝ) < ((2*q:ℕ):ℝ) := by
    exact_mod_cast (by omega : (0:ℕ) < 2*q)
  have hdiv : (0:ℝ) < ((2*q:ℕ):ℝ)/(p:ℝ) := div_pos hdR hpR
  have hK : K =
      (Real.sqrt (((2*q:ℕ):ℝ)/(p:ℝ)) : ℂ) *
        Complex.exp (-(Real.pi:ℂ)*Complex.I/4) := by
    dsimp [K]
    exact cpow_neg_I_mul_pos _ hdiv
  have hsp : (Real.sqrt (p:ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hpR)
  have hsd : (Real.sqrt ((2*q:ℕ):ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hdR)
  have hst : (Real.sqrt (((2*q:ℕ):ℝ)/(p:ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hdiv)
  have hmulR : Real.sqrt (((2*q:ℕ):ℝ)/(p:ℝ)) *
          Real.sqrt (p:ℝ) = Real.sqrt ((2*q:ℕ):ℝ) := by
    rw [← Real.sqrt_mul (le_of_lt hdiv)]
    congr 1
    field_simp
  have hmulC : (Real.sqrt (((2*q:ℕ):ℝ)/(p:ℝ)) : ℂ) *
          (Real.sqrt (p:ℝ) : ℂ) =
          (Real.sqrt ((2*q:ℕ):ℝ) : ℂ) := by
    exact_mod_cast hmulR
  have hphase : Complex.exp ((Real.pi:ℂ)*Complex.I/4) *
        Complex.exp (-(Real.pi:ℂ)*Complex.I/4) = (1:ℂ) := by
    rw [← Complex.exp_add]
    have hh : (Real.pi:ℂ)*Complex.I/4 +
        (-(Real.pi:ℂ)*Complex.I/4) = 0 := by ring
    rw [hh, Complex.exp_zero]
  have hcoef : (Real.sqrt (p:ℝ):ℂ)⁻¹ =
      Complex.exp ((Real.pi:ℂ)*Complex.I/4) *
        (Real.sqrt ((2*q:ℕ):ℝ):ℂ)⁻¹ *
          ((Real.sqrt (((2*q:ℕ):ℝ)/(p:ℝ)):ℂ) *
             Complex.exp (-(Real.pi:ℂ)*Complex.I/4)) := by
    -- the two phases cancel, and the positive real square roots multiply.
    calc
      _ = ((Real.sqrt ((2*q:ℕ):ℝ):ℂ)⁻¹ *
            (Real.sqrt (((2*q:ℕ):ℝ)/(p:ℝ)):ℂ)) := by
              field_simp
              rw [← hmulC]
              ring
      _ = _ := by
        rw [show Complex.exp ((Real.pi:ℂ)*Complex.I/4) *
             (Real.sqrt ((2*q:ℕ):ℝ):ℂ)⁻¹ *
             ((Real.sqrt (((2*q:ℕ):ℝ)/(p:ℝ)):ℂ) *
               Complex.exp (-(Real.pi:ℂ)*Complex.I/4)) =
             (Complex.exp ((Real.pi:ℂ)*Complex.I/4) *
                Complex.exp (-(Real.pi:ℂ)*Complex.I/4)) *
                ((Real.sqrt ((2*q:ℕ):ℝ):ℂ)⁻¹ *
                 (Real.sqrt (((2*q:ℕ):ℝ)/(p:ℝ)):ℂ)) by ring]
        rw [hphase]
        simp
  have hmain : (Real.sqrt (p:ℝ):ℂ)⁻¹ * A =
      Complex.exp ((Real.pi:ℂ)*Complex.I/4) *
        ((Real.sqrt ((2*q:ℕ):ℝ):ℂ)⁻¹ * B) := by
    rw [hrec, hK, hcoef]
    ring
  -- Replace the finite `Fin` sums by the identical range sums in `gaussS`.
  have hAP : A =
      (∑ x ∈ Finset.range p,
        Complex.exp ((Real.pi:ℂ) * Complex.I *
          ((x:ℂ)^2 * (((2*q:ℕ)):ℂ) / (p:ℂ)))) := by
    dsimp [A]
    exact Fin.sum_univ_eq_sum_range
      (fun x : ℕ => Complex.exp ((Real.pi:ℂ) * Complex.I *
          ((x:ℂ)^2 * (((2*q:ℕ)):ℂ) / (p:ℂ)))) p
  have hBD : B =
      (∑ x ∈ Finset.range (2*q),
        Complex.exp ((Real.pi:ℂ) * Complex.I *
          ((x:ℂ)^2 * ((-(p:ℤ):ℤ):ℂ) / ((2*q:ℕ):ℂ)))) := by
    dsimp [B]
    exact Fin.sum_univ_eq_sum_range
      (fun x : ℕ => Complex.exp ((Real.pi:ℂ) * Complex.I *
          ((x:ℂ)^2 * ((-(p:ℤ):ℤ):ℂ) / ((2*q:ℕ):ℂ)))) (2*q)
  rw [hAP, hBD] at hmain
  unfold gaussS
  push_cast
  simpa using hmain
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
