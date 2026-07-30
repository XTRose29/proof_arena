import ChallengeDeps

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/ApproxLimit.lean
section
open scoped Topology
open Filter

namespace WignerSupport

/-- A small two--limits lemma used in truncation arguments.  It is deliberately
stated with the slack `+ η`: elementary estimates generally give a strict
upper bound only after inserting such a slack.  No summability, or
interchange of the two limits, is hidden here. -/
lemma tendsto_of_approx_complex
    (u : ℕ → ℂ) (v : ℕ → ℕ → ℂ) (z : ℕ → ℂ) (a : ℂ)
    (e : ℕ → ℝ)
    (hv : ∀ R : ℕ, Tendsto (v R) atTop (𝓝 (z R)))
    (hz : Tendsto z atTop (𝓝 a))
    (he : Tendsto e atTop (𝓝 (0:ℝ)))
    (hclose : ∀ R : ℕ, ∀ η : ℝ, 0 < η →
       ∀ᶠ k : ℕ in atTop, ‖u k - v R k‖ < e R + η) :
    Tendsto u atTop (𝓝 a) := by
  apply (Metric.tendsto_nhds).2
  intro ε hε
  have ep : 0 < ε/4 := by linarith
  have he' : ∀ᶠ R : ℕ in atTop, dist (e R) (0:ℝ) < ε/4 :=
    ((Metric.tendsto_nhds).1 he) _ ep
  have hz' : ∀ᶠ R : ℕ in atTop, dist (z R) a < ε/4 :=
    ((Metric.tendsto_nhds).1 hz) _ ep
  have both : ∀ᶠ R : ℕ in atTop,
      dist (e R) (0:ℝ) < ε/4 ∧ dist (z R) a < ε/4 := by
    filter_upwards [he', hz'] with R hR hZ
    exact ⟨hR, hZ⟩
  obtain ⟨R, hER, hZR⟩ := both.exists
  have eR : e R < ε/4 := by
    have h : |e R| < ε/4 := by
      simpa [Real.dist_eq] using hER
    exact (abs_lt.mp h).2
  have hVR : ∀ᶠ k : ℕ in atTop, dist (v R k) (z R) < ε/4 :=
    ((Metric.tendsto_nhds).1 (hv R)) _ ep
  have hUR := hclose R (ε/4) ep
  filter_upwards [hVR, hUR] with k hk hvk
  have hUV : dist (u k) (v R k) < e R + ε/4 := by
    simpa [dist_eq_norm] using hvk
  calc
    dist (u k) a ≤ dist (u k) (v R k) + dist (v R k) a :=
      dist_triangle _ _ _
    _ ≤ dist (u k) (v R k) +
          (dist (v R k) (z R) + dist (z R) a) := by
        gcongr
        exact dist_triangle _ _ _
    _ < ε := by linarith

end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/ApproxLimit.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Deterministic.lean
section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Filter
namespace WignerSupport

noncomputable def cpoly (N:ℕ) (t x:ℝ) : ℂ :=
  ∑ l ∈ Finset.range N, ((((x*t:ℝ):ℂ) * Complex.I)^l) / (l.factorial:ℕ)

lemma norm_exp_I (t x:ℝ) : ‖Complex.exp ((((x*t:ℝ):ℂ)*Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma norm_cpoly_term_le (l N:ℕ) (hl:l<N) (t:ℝ) {x D:ℝ}
    (hD : 1 ≤ D) (hx : D < |x|) :
    ‖(((((x*t:ℝ):ℂ)*Complex.I)^l) / (l.factorial:ℕ))‖ ≤
       (|t|+1)^N * |x|^N := by
  rw [norm_div, norm_pow]
  have hn : ‖(((x*t:ℝ):ℂ)*Complex.I)‖ = |x| * |t| := by
    simp [abs_mul]
  rw [hn]
  have fac : (1:ℝ) ≤ ‖(l.factorial:ℂ)‖ := by
    have h : (1:ℝ) ≤ (l.factorial:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero l))
    simpa using h
  have denpos : 0 ≤ ‖(l.factorial:ℂ)‖ := norm_nonneg _
  calc
    (|x| * |t|)^l / ‖(l.factorial:ℂ)‖ ≤ (|x| * |t|)^l := by
      apply (div_le_self (by positivity) fac)
    _ = |x|^l * |t|^l := by ring
    _ ≤ |x|^N * (|t|+1)^N := by
      have x1 : 1 ≤ |x| := le_trans hD (le_of_lt hx)
      have tl : |t|^l ≤ (|t|+1)^N := by
        calc |t|^l ≤ (|t|+1)^l := by
                 exact pow_le_pow_left₀ (abs_nonneg t) (by linarith [abs_nonneg t]) _
             _ ≤ (|t|+1)^N := by
               exact pow_le_pow_right₀ (by linarith [abs_nonneg t]) (Nat.le_of_lt hl)
      have xl : |x|^l ≤ |x|^N := pow_le_pow_right₀ x1 (Nat.le_of_lt hl)
      exact mul_le_mul xl tl (by positivity) (by positivity)
    _ = (|t|+1)^N * |x|^N := by ring

lemma norm_cpoly_le (N:ℕ) (t:ℝ) {x D:ℝ}
    (hD : 1 ≤ D) (hx : D < |x|) :
    ‖cpoly N t x‖ ≤ (N:ℝ) * ((|t|+1)^N * |x|^N) := by
  unfold cpoly
  calc
    ‖∑ l ∈ Finset.range N, (((((x*t:ℝ):ℂ)*Complex.I)^l) / (l.factorial:ℕ))‖ ≤
      ∑ l ∈ Finset.range N, ‖(((((x*t:ℝ):ℂ)*Complex.I)^l) / (l.factorial:ℕ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _l ∈ Finset.range N, ((|t|+1)^N * |x|^N) := by
      gcongr with l hl
      exact norm_cpoly_term_le l N (Finset.mem_range.mp hl) t hD hx
    _ = (N:ℝ) * ((|t|+1)^N * |x|^N) := by simp

/-- A deliberately coarse tail estimate.  On the complement of a large
interval a fixed exponential polynomial costs only a high even moment. -/
lemma exp_poly_tail_point {N Q:ℕ} (hQ : N ≤ 2*Q) (t:ℝ)
    {x D:ℝ} (hD : 1 ≤ D) (hx : D < |x|) :
    ‖Complex.exp ((((x*t:ℝ):ℂ)*Complex.I)) - cpoly N t x‖ ≤
      (1 + (N:ℝ) * (|t|+1)^N * D^N) * (x^(2*Q) / D^(2*Q)) := by
  have ax : 1 ≤ |x| := hD.trans (le_of_lt hx)
  have Dpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have rat1 : 1 ≤ |x|^(2*Q) / D^(2*Q) := by
    apply (le_div_iff₀ (by positivity)).2
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ D) (le_of_lt hx) (2*Q)
    simpa using h
  have comp := norm_cpoly_le N t hD hx
  have xn : |x|^N ≤ (|x|^(2*Q) / D^(2*Q)) * D^N := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < D^(2*Q))).2
    calc
      |x|^N * D^(2*Q) = |x|^N * (D^(2*Q-N) * D^N) := by
        rw [← pow_add]
        congr 2 <;> omega
      _ ≤ |x|^N * (|x|^(2*Q-N) * D^N) := by
        gcongr
      _ = |x|^(2*Q) * D^N := by
        rw [← mul_assoc, ← pow_add]
        congr 2 <;> omega

  calc
    ‖Complex.exp ((((x*t:ℝ):ℂ)*Complex.I)) - cpoly N t x‖ ≤
      1 + ‖cpoly N t x‖ := by
        calc _ ≤ ‖Complex.exp ((((x*t:ℝ):ℂ)*Complex.I))‖ + ‖cpoly N t x‖ := norm_sub_le _ _
             _ = _ := by rw [norm_exp_I]
    _ ≤ 1 + (N:ℝ) * ((|t|+1)^N * |x|^N) := by linarith
    _ ≤ (1 + (N:ℝ) * (|t|+1)^N * D^N) * (|x|^(2*Q) / D^(2*Q)) := by
      have C0 : 0 ≤ (N:ℝ) * (|t|+1)^N := by positivity
      have q0 : 0 ≤ |x|^(2*Q) / D^(2*Q) := by positivity
      have mulx : (N:ℝ) * (|t|+1)^N * |x|^N ≤
          ((N:ℝ) * (|t|+1)^N * D^N) * (|x|^(2*Q) / D^(2*Q)) := by
        calc _ ≤ ((N:ℝ) * (|t|+1)^N) *
                    ((|x|^(2*Q) / D^(2*Q)) * D^N) := by
                      gcongr
             _ = _ := by ring
      linarith
    _ = (1 + (N:ℝ) * (|t|+1)^N * D^N) * (x^(2*Q) / D^(2*Q)) := by
      rw [Even.pow_abs (by exact ⟨Q, by omega⟩ : Even (2*Q)) x]
end WignerSupport
namespace WignerSupport
lemma exp_poly_compact (N:ℕ) (t:ℝ) {x D:ℝ} (hD:0 ≤ D)
    (hx : |x| ≤ D) (hN : |t| *D / ((N+1:ℕ):ℝ) ≤ (1:ℝ)/2) :
    ‖Complex.exp ((((x*t:ℝ):ℂ)*Complex.I)) - cpoly N t x‖ ≤
       (|t| *D)^N / (N.factorial:ℕ) * 2 := by
  have argnorm : ‖(((x*t:ℝ):ℂ)*Complex.I)‖ = |x| * |t| := by simp
  have small : ‖(((x*t:ℝ):ℂ)*Complex.I)‖ /
          ((N:ℕ).succ:ℝ) ≤ (1:ℝ)/2 := by
    rw [argnorm]
    apply le_trans ?_ hN
    have hmul : |x| * |t| ≤ |t| * D := by
      nlinarith [abs_nonneg t]
    exact div_le_div_of_nonneg_right hmul (by positivity)
  have b := Complex.exp_bound' (x:=(((x*t:ℝ):ℂ)*Complex.I)) (n:=N) (by simpa using small)
  unfold cpoly
  refine b.trans ?_
  -- same formula, only replace norm by its bound
  have learg : ‖(((x*t:ℝ):ℂ)*Complex.I)‖ ≤ |t| *D := by
    rw [argnorm]
    nlinarith [abs_nonneg t]
  have factpos : 0 ≤ (N.factorial:ℝ) := by positivity
  have : ‖(((x*t:ℝ):ℂ)*Complex.I)‖ ^ N ≤ (|t| *D)^N := by
    gcongr
  simpa using (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right this factpos) (by norm_num : (0:ℝ) ≤ 2))
end WignerSupport
namespace WignerSupport
/-- row error for a Taylor polynomial, controlled by a compact error and an even moment. -/
lemma row_exp_poly_bound (N Q n:ℕ) (hn:0<n) (hQ:N ≤ 2*Q) (t:ℝ)
    (b: Fin n → ℝ) {D E:ℝ} (hD: 1 ≤ D)
    (hN : |t| * D / ((N+1:ℕ):ℝ) ≤ (1:ℝ)/2)
    (hE : (|t| * D)^N / (N.factorial:ℕ) * 2 ≤ E) :
    ‖(n:ℝ)⁻¹ • (∑ j : Fin n,
        (Complex.exp (((((b j)*t:ℝ):ℂ)*Complex.I)) - cpoly N t (b j)))‖ ≤
      E + (1 + (N:ℝ) * (|t|+1)^N * D^N) /
            D^(2*Q) * ((n:ℝ)⁻¹ * ∑ j : Fin n, (b j)^(2*Q)) := by
  have nz : (0:ℝ) < n := by exact_mod_cast hn
  have C0 : 0 ≤ (1 + (N:ℝ) * (|t|+1)^N * D^N) := by positivity
  have E0 : 0 ≤ E := le_trans (by positivity) hE
  -- first take norms termwise
  calc
    ‖(n:ℝ)⁻¹ • (∑ j : Fin n,
        (Complex.exp (((((b j)*t:ℝ):ℂ)*Complex.I)) - cpoly N t (b j)))‖ =
       (n:ℝ)⁻¹ * ‖∑ j : Fin n,
        (Complex.exp (((((b j)*t:ℝ):ℂ)*Complex.I)) - cpoly N t (b j))‖ := by
          rw [norm_smul]; simp [Real.norm_eq_abs, abs_of_pos nz]
    _ ≤ (n:ℝ)⁻¹ * ∑ j : Fin n,
        ‖(Complex.exp (((((b j)*t:ℝ):ℂ)*Complex.I)) - cpoly N t (b j))‖ := by
          gcongr
          exact norm_sum_le _ _
    _ ≤ (n:ℝ)⁻¹ * ∑ j : Fin n,
        (E + (1 + (N:ℝ) * (|t|+1)^N * D^N) *
                ((b j)^(2*Q) / D^(2*Q))) := by
          gcongr with j hj
          by_cases hgood : |b j| ≤ D
          · have bd := exp_poly_compact N t (show 0 ≤ D by linarith) hgood hN
            have : ‖(Complex.exp (((((b j)*t:ℝ):ℂ)*Complex.I)) - cpoly N t (b j))‖ ≤ E :=
              bd.trans hE
            have rest : 0 ≤ (1 + (N:ℝ) * (|t|+1)^N * D^N) *
                ((b j)^(2*Q) / D^(2*Q)) := by
              have even : 0 ≤ (b j)^(2*Q) := Even.pow_nonneg (by exact ⟨Q, by omega⟩) _
              positivity
            linarith
          · have hh : D < |b j| := lt_of_not_ge hgood
            have bd := exp_poly_tail_point hQ t hD hh
            exact bd.trans (le_add_of_nonneg_left E0)
    _ = E + (1 + (N:ℝ) * (|t|+1)^N * D^N) /
            D^(2*Q) * ((n:ℝ)⁻¹ * ∑ j : Fin n, (b j)^(2*Q)) := by
      rw [Finset.sum_add_distrib]
      -- routine distributivity
      simp [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
      congr 2
      · field_simp
      · funext j
        ring
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Deterministic.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Extension.lean
section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace WignerSupport

/-- Dense rational convergence plus a common Lipschitz constant gives convergence at every
real argument.  This deterministic little lemma is the useful form of the separability
step in characteristic-function arguments. -/
lemma tendsto_of_rat_of_lipschitz (F : ℕ → ℝ → ℂ) (g : ℝ → ℂ) (hg : Continuous g)
    (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ n s t, ‖F n s - F n t‖ ≤ C * |s - t|)
    (hQ : ∀ q : ℚ, Tendsto (fun n : ℕ => F n (q : ℝ)) atTop (𝓝 (g (q : ℝ)))) :
    ∀ t : ℝ, Tendsto (fun n : ℕ => F n t) atTop (𝓝 (g t)) := by
  intro t
  rw [Metric.tendsto_atTop]
  intro ε hε
  have e3 : 0 < ε / 3 := by positivity
  obtain ⟨δ, δpos, hδ⟩ := (Metric.continuousAt_iff.1 (hg.continuousAt (x := t))) (ε/3) e3
  let d : ℝ := min δ (ε / (3 * (C+1)))
  have denpos : 0 < (3 * (C+1)) := mul_pos (by norm_num) (by linarith)
  have dpos : 0 < d := lt_min δpos (div_pos hε denpos)
  obtain ⟨q, qlo, qhi⟩ := exists_rat_btwn (show t - d < t + d by linarith)
  have hqt : |(q:ℝ) - t| < d := (abs_lt).2 ⟨by linarith, by linarith⟩
  have hdist : dist (q:ℝ) t < d := by simpa [Real.dist_eq] using hqt
  have hgd : dist (g (q:ℝ)) (g t) < ε/3 := hδ (lt_of_lt_of_le hdist (min_le_left _ _))
  have hCL : C * |t - (q:ℝ)| < ε/3 := by
    have hsmall : |t - (q:ℝ)| < ε / (3 * (C+1)) := by
      simpa [abs_sub_comm] using (lt_of_lt_of_le hqt (min_le_right _ _))
    calc
      C * |t - (q:ℝ)| ≤ (C+1) * |t - (q:ℝ)| := by
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (C+1) * (ε/(3*(C+1))) :=
        (mul_lt_mul_of_pos_left hsmall (by linarith))
      _ = ε/3 := by field_simp
  rcases (Metric.tendsto_atTop.1 (hQ q)) (ε/3) e3 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hmid : dist (F n (q:ℝ)) (g (q:ℝ)) < ε/3 := hN n hn
  -- triangular inequality, doing it in norms avoids any coercions on `dist`
  rw [Complex.dist_eq] at hmid hgd ⊢
  have hfirst : ‖F n t - F n (q:ℝ)‖ < ε/3 :=
    lt_of_le_of_lt (hL n t (q:ℝ)) hCL
  calc
    ‖F n t - g t‖ ≤
        ‖F n t - F n (q:ℝ)‖ + ‖F n (q:ℝ) - g (q:ℝ)‖ +
          ‖g (q:ℝ) - g t‖ := by
            calc
              ‖F n t - g t‖ = ‖(F n t - F n (q:ℝ)) +
                  (F n (q:ℝ) - g (q:ℝ)) + (g (q:ℝ) - g t)‖ := by ring_nf
              _ ≤ ‖F n t - F n (q:ℝ)‖ + ‖F n (q:ℝ) - g (q:ℝ)‖ +
                    ‖g (q:ℝ) - g t‖ := by
                    have hh := norm_add_le (F n t - F n (q:ℝ)) (F n (q:ℝ) - g (q:ℝ))
                    exact (norm_add_le _ _).trans (by
                      gcongr)
    _ < ε := by linarith

/-- The elementary global Lipschitz bound on the unitary exponential.  The estimate with
2 is convenient since it only uses the standard `norm_exp_sub_one_le` on the unit ball. -/
lemma norm_exp_mul_I_sub_exp_mul_I (a b : ℝ) :
    ‖Complex.exp ((a:ℂ) * Complex.I) - Complex.exp ((b:ℂ) * Complex.I)‖
      ≤ 2 * |a-b| := by
  have hp (u : ℝ) : ‖(u:ℂ) * Complex.I‖ = |u| := by
    simp [Complex.norm_mul, Real.norm_eq_abs]
  have hone (u : ℝ) : ‖Complex.exp ((u:ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have haux (u : ℝ) : ‖Complex.exp ((u:ℂ) * Complex.I) - 1‖ ≤ 2 * |u| := by
    by_cases h : |u| ≤ 1
    · have hz := Complex.norm_exp_sub_one_le (x := (u:ℂ) * Complex.I) (by rw [hp]; exact h)
      rw [hp] at hz
      exact hz
    · have hu : 1 ≤ |u| := le_of_lt (lt_of_not_ge h)
      calc
        ‖Complex.exp ((u:ℂ) * Complex.I) - 1‖ ≤
            ‖Complex.exp ((u:ℂ) * Complex.I)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hone]; norm_num
        _ ≤ 2 * |u| := by linarith
  -- factor out the second exponential, whose norm is one
  calc
    ‖Complex.exp ((a:ℂ) * Complex.I) - Complex.exp ((b:ℂ) * Complex.I)‖ =
        ‖Complex.exp ((b:ℂ) * Complex.I) *
          (Complex.exp (((a-b:ℝ):ℂ) * Complex.I) - 1)‖ := by
            congr 1
            rw [mul_sub]
            simp only [mul_one]
            rw [← Complex.exp_add]
            congr 2
            push_cast
            ring
    _ = ‖Complex.exp (((a-b:ℝ):ℂ) * Complex.I) - 1‖ := by
          rw [Complex.norm_mul, hone]; simp
    _ ≤ 2 * |a-b| := haux (a-b)

/-- Characteristic average of a finite list of real numbers. -/
noncomputable def finiteChar {n : ℕ} (v : Fin n → ℝ) (t : ℝ) : ℂ :=
  (n : ℝ)⁻¹ • ∑ j, Complex.exp (((v j * t : ℝ) : ℂ) * Complex.I)

/-- A first-moment Lipschitz estimate for finite characteristic averages. -/
lemma finiteChar_lipschitz {n : ℕ} (v : Fin n → ℝ) (s t : ℝ) :
    ‖finiteChar v s - finiteChar v t‖ ≤
      ((n:ℝ)⁻¹ * ∑ j, |v j|) * (2 * |s-t|) := by
  classical
  unfold finiteChar
  rw [← smul_sub]
  -- use the triangle inequality term by term
  calc
    ‖(n:ℝ)⁻¹ • ((∑ j, Complex.exp (((v j * s : ℝ):ℂ) * Complex.I)) -
          ∑ j, Complex.exp (((v j * t:ℝ):ℂ) * Complex.I))‖
        = |(n:ℝ)⁻¹| *
          ‖∑ j, (Complex.exp (((v j * s : ℝ):ℂ) * Complex.I) -
                    Complex.exp (((v j * t : ℝ):ℂ) * Complex.I))‖ := by
            rw [← Finset.sum_sub_distrib]
            simp [norm_smul, Real.norm_eq_abs]
    _ ≤ |(n:ℝ)⁻¹| *
          ∑ j, ‖Complex.exp (((v j * s : ℝ):ℂ) * Complex.I) -
                    Complex.exp (((v j * t : ℝ):ℂ) * Complex.I)‖ := by
            gcongr
            apply norm_sum_le
    _ ≤ |(n:ℝ)⁻¹| * ∑ j, (2 * |v j * s - v j * t|) := by
            gcongr with j hj
            exact norm_exp_mul_I_sub_exp_mul_I _ _
    _ = ((n:ℝ)⁻¹ * ∑ j, |v j|) * (2 * |s-t|) := by
          have hinv : 0 ≤ (n:ℝ)⁻¹ := by positivity
          rw [abs_of_nonneg hinv]
          -- distributivity and |ab|
          simp_rw [← mul_sub, abs_mul]
          -- now only a finite distributive calculation
          calc
            (n:ℝ)⁻¹ * ∑ x, 2 * (|v x| * |s-t|) =
                (n:ℝ)⁻¹ * ∑ x, |v x| * (2 * |s-t|) := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = ((n:ℝ)⁻¹ * ∑ j, |v j|) * (2 * |s-t|) := by
                  rw [← Finset.sum_mul]
                  ring

end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Extension.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Moments.lean
section

open scoped BigOperators ENNReal NNReal Topology
open Matrix Unitary

namespace WignerSupport

/-- Parseval/trace identity for a Hermitian complex matrix, in a form avoiding the ordering
of the eigenvalues. -/
lemma hermitian_sum_sq_eigen {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : A.IsHermitian) :
    ∑ i, ((h.eigenvalues i : ℂ) ^ 2) = (A * A).trace := by
  let D : Matrix n n ℂ := diagonal (fun i => (h.eigenvalues i : ℂ))
  let U := h.eigenvectorUnitary
  have hAA : A * A = conjStarAlgAut ℂ _ U (D * D) := by
    rw [h.spectral_theorem]
    change _ = _
    simpa [D, U] using
      (map_mul (conjStarAlgAut ℂ (Matrix n n ℂ) U)
        (diagonal (RCLike.ofReal ∘ h.eigenvalues))
        (diagonal (RCLike.ofReal ∘ h.eigenvalues))).symm
  rw [hAA, conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  -- the middle conjugating pair cancels
  rw [Unitary.coe_star_mul_self, one_mul]
  classical
  -- trace of a diagonal square
  simp [D, Matrix.trace, Matrix.mul_apply, pow_two]

/-- For a real symmetric matrix entered in `ℂ`, the real form of the trace identity. -/
lemma real_wigner_sq {α : Type*} (Y : ℕ → ℕ → α → ℝ)
    (herm : ∀ n a,
      Matrix.IsHermitian (fun i j : Fin n => ((Y (min (i:ℕ) j) (max (i:ℕ) j) a : ℝ) : ℂ)))
    (n : ℕ) (a : α) :
    ∑ i : Fin n, ((herm n a).eigenvalues i) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        (Y (min (i:ℕ) j) (max (i:ℕ) j) a) ^ 2 := by
  classical
  let A : Matrix (Fin n) (Fin n) ℂ :=
    fun i j => ((Y (min (i:ℕ) j) (max (i:ℕ) j) a : ℝ) : ℂ)
  let h : A.IsHermitian := herm n a
  have hh := hermitian_sum_sq_eigen A h
  have hEq : h = herm n a := rfl
  -- commute/cast to real
  have hc :
      ((∑ i : Fin n, ((herm n a).eigenvalues i) ^ 2 : ℝ) : ℂ) =
        ((∑ i : Fin n, ∑ j : Fin n,
          (Y (min (i:ℕ) j) (max (i:ℕ) j) a) ^ 2 : ℝ) : ℂ) := by
    classical
    simpa [A, hEq, Matrix.trace, Matrix.mul_apply, min_comm, max_comm, pow_two] using hh
  exact_mod_cast hc

/-- `|x|` is controlled by a quadratic moment plus one. -/
lemma abs_le_sq_add_one (x : ℝ) : |x| ≤ x^2 + 1 := by
  nlinarith [sq_nonneg (|x| - (1/2 : ℝ)), sq_abs x]

/-- A uniform quadratic bound for finite vectors implies a uniform first moment bound. -/
lemma mean_abs_le_of_mean_sq {n : ℕ} (hn : n ≠ 0) (v : Fin n → ℝ) (B : ℝ)
    (hB : (n:ℝ)⁻¹ * ∑ i, (v i)^2 ≤ B) :
    (n:ℝ)⁻¹ * ∑ i, |v i| ≤ B + 1 := by
  classical
  have hsum : (∑ i, |v i|) ≤ ∑ i, ((v i)^2 + 1) := by
    exact Finset.sum_le_sum (fun i hi => abs_le_sq_add_one (v i))
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hinv : 0 ≤ (n:ℝ)⁻¹ := by positivity
  calc
    (n:ℝ)⁻¹ * ∑ i, |v i| ≤ (n:ℝ)⁻¹ * ∑ i, ((v i)^2 + 1) :=
      mul_le_mul_of_nonneg_left hsum hinv
    _ = (n:ℝ)⁻¹ * ∑ i, (v i)^2 + 1 := by
      simp [Finset.sum_add_distrib]
      field_simp
    _ ≤ B + 1 := by linarith

end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Moments.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Semimom.lean
section
open scoped BigOperators ENNReal Topology
open MeasureTheory Real Filter Set intervalIntegral
namespace WignerSupport

-- sine-power integral on the half-turn interval; endpoints make recurrence clean
noncomputable def sinEven (m : ℕ) : ℝ :=
  ∫ x in (-(Real.pi/2))..(Real.pi/2), (Real.sin x)^(2*m)

lemma sinEven_zero : sinEven 0 = Real.pi := by
  simp [sinEven]

lemma sinEven_rec (m : ℕ) :
    sinEven (m+1) = ((2*m+1:ℕ):ℝ) / ((2*m+2:ℕ):ℝ) * sinEven m := by
  have h := @integral_sin_pow (a:=-(Real.pi/2)) (b:=Real.pi/2) (2*m)
  change (∫ x in (-(Real.pi/2))..(Real.pi/2), Real.sin x ^ (2*m+2)) = _ at h
  change _
  dsimp [sinEven]
  convert h using 1
  all_goals norm_num <;> push_cast <;> try ring <;> try omega

-- Catalan recurrence in reals, convenient closed beta value
lemma catalan_real_rec (m : ℕ) :
    (catalan (m+1) : ℝ) =
       ( (2:ℝ)*( (m:ℝ)*2 + 1) / ((m:ℝ)+2)) * (catalan m : ℝ) := by
  have h1 := succ_mul_catalan_eq_centralBinom (m+1)
  have h0 := succ_mul_catalan_eq_centralBinom m
  have hc := Nat.succ_mul_centralBinom_succ m
  have a1 : ((m+2:ℕ):ℝ) * (catalan (m+1):ℝ) = (Nat.centralBinom (m+1):ℝ) := by exact_mod_cast h1
  have a0 : ((m+1:ℕ):ℝ) * (catalan m:ℝ) = (Nat.centralBinom m:ℝ) := by exact_mod_cast h0
  have ac : ((m+1:ℕ):ℝ) * (Nat.centralBinom (m+1):ℝ) =
      (2:ℝ) * ((2*m+1:ℕ):ℝ) * (Nat.centralBinom m:ℝ) := by exact_mod_cast hc
  have z1 : ( (m:ℝ)+1) ≠ 0 := by positivity
  have z2 : ( (m:ℝ)+2) ≠ 0 := by positivity
  push_cast at a0 a1 ac ⊢
  field_simp
  nlinarith

-- moment on unit interval (not normalized), via sine substitution
noncomputable def unitSemiEven (m : ℕ) : ℝ :=
  ∫ x in (-1:ℝ)..1, x^(2*m) * Real.sqrt (1-x^2)

lemma unitSemiEven_eq (m : ℕ) :
    unitSemiEven m = sinEven m - sinEven (m+1) := by
  -- substitution x=sin u, cos nonnegative on this interval
  have sub := intervalIntegral.integral_comp_mul_deriv
    (a:=-(Real.pi/2)) (b:=Real.pi/2)
    (f:=Real.sin) (f':=Real.cos)
    (g:= fun x : ℝ => x^(2*m) * Real.sqrt (1-x^2))
    (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn
    (by fun_prop)
  -- sub : int (g (sin x) * cos)
  have eqint : (∫ x in (-(Real.pi/2))..(Real.pi/2),
          (Real.sin x)^(2*m) * Real.sqrt (1-(Real.sin x)^2) * Real.cos x) =
        ∫ x in (-(1:ℝ))..1, x^(2*m)*Real.sqrt (1-x^2) := by
    convert sub using 1 <;> simp
  have cosnon : ∀ x ∈ Set.uIcc (-(Real.pi/2)) (Real.pi/2),
        Real.sqrt (1-(Real.sin x)^2) = Real.cos x := by
    intro x hx
    have H : x ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
      simpa [uIcc_of_le (by linarith [Real.pi_pos] : -(Real.pi/2) ≤ Real.pi/2)] using hx
    have hxl : -(Real.pi/2) ≤ x := H.1
    have hxu : x ≤ Real.pi/2 := H.2
    exact (Real.cos_eq_sqrt_one_sub_sin_sq hxl hxu).symm
  calc
    unitSemiEven m = ∫ x in (-(Real.pi/2))..(Real.pi/2),
          (Real.sin x)^(2*m) * Real.sqrt (1-(Real.sin x)^2) * Real.cos x := eqint.symm
    _ = ∫ x in (-(Real.pi/2))..(Real.pi/2),
          ((Real.sin x)^(2*m) - (Real.sin x)^(2*(m+1))) := by
          apply intervalIntegral.integral_congr
          intro x hx
          change (Real.sin x)^(2*m) * Real.sqrt (1-(Real.sin x)^2) * Real.cos x = _
          rw [cosnon x hx]
          change (Real.sin x)^(2*m) * Real.cos x * Real.cos x = (Real.sin x)^(2*m) - (Real.sin x)^(2*(m+1))
          rw [show (Real.sin x)^(2*m) * Real.cos x * Real.cos x = (Real.sin x)^(2*m) * (Real.cos x)^2 by ring]
          rw [Real.cos_sq']
          rw [show (Real.sin x)^(2*(m+1)) = (Real.sin x)^(2*m) * (Real.sin x)^2 by ring]
          ring
    _ = sinEven m - sinEven (m+1) := by
          rw [intervalIntegral.integral_sub]
          · rfl
          · exact (Real.continuous_sin.pow _).intervalIntegrable _ _
          · exact (Real.continuous_sin.pow _).intervalIntegrable _ _

lemma scaled_unitSemiEven_eq (m : ℕ) :
    (2:ℝ)^(2*m+1) / Real.pi * unitSemiEven m = (catalan m : ℝ) := by
  have pi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have ju (r : ℕ) : unitSemiEven r =
       sinEven r * (1 / ((2*r+2:ℕ):ℝ)) := by
    rw [unitSemiEven_eq, sinEven_rec]
    push_cast
    have z : ( (r:ℝ)*2 + 2) ≠ 0 := by positivity
    field_simp
    ring
  induction m with
  | zero =>
    simp [ju, sinEven_zero, catalan_zero]
    field_simp
  | succ m ih =>
    rw [ju (m+1), sinEven_rec m]
    rw [ju m] at ih
    rw [catalan_real_rec]
    push_cast at ih ⊢
    have z1 : ( (m:ℝ)*2 + 2) ≠ 0 := by positivity
    have z2 : ( (m:ℝ)*2 + 4) ≠ 0 := by positivity
    have pp : Real.pi ≠ 0 := pi0
    rw [show (2:ℝ) ^ (2 * (m + 1) + 1) = 4 * (2:ℝ)^(2*m+1) by ring]
    field_simp at ih ⊢
    nlinarith

-- actual density moment, as an interval integral
lemma semi_interval_even (m : ℕ) :
  (∫ x in (-2:ℝ)..2,
       x^(2*m) * (Real.sqrt (4-x^2) / (2*Real.pi))) = (catalan m : ℝ) := by
  -- dilate x=2u
  let F : ℝ → ℝ := fun x => x^(2*m) * (Real.sqrt (4-x^2) / (2*Real.pi))
  have sub := intervalIntegral.integral_comp_mul_left
      (f:=F) (a:=(-1:ℝ)) (b:=1) (c:=2) (by norm_num : (2:ℝ) ≠ 0)
  have point (x:ℝ) : F (2*x) =
       ((2:ℝ)^(2*m)/Real.pi) * (x^(2*m) * Real.sqrt (1-x^2)) := by
    dsimp [F]
    rw [show (4-(2*x)^2:ℝ)=4*(1-x^2) by ring]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    rw [show Real.sqrt (4:ℝ)=2 by norm_num]
    rw [mul_pow]
    ring
  have eqsub : (∫ x in (-1:ℝ)..1, F (2*x)) =
       ((2:ℝ)^(2*m)/Real.pi) * unitSemiEven m := by
    simp_rw [point]
    rw [intervalIntegral.integral_const_mul]
    rfl
  have pi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have sc := scaled_unitSemiEven_eq m
  change (∫ x in (-2:ℝ)..2, F x) = _
  have val : (∫ x in (-2:ℝ)..2, F x) =
       (2:ℝ) * ((2:ℝ)^(2*m)/Real.pi * unitSemiEven m) := by
    rw [show (-2:ℝ) = 2 * (-1) by norm_num,
        show (2:ℝ) = 2 * 1 by norm_num]
    -- sub is half of integral
    have hh := sub
    rw [eqsub] at hh
    -- coerce smul to multiplication
    change (2:ℝ)^(2*m)/Real.pi * unitSemiEven m =
       (2:ℝ)⁻¹ * (∫ x in (2:ℝ)*(-1)..(2:ℝ)*1, F x) at hh
    linarith
  rw [val]
  convert sc using 1 <;> ring
end WignerSupport
namespace WignerSupport
lemma semi_interval_odd (m : ℕ) :
  (∫ x in (-2:ℝ)..2,
       x^(2*m+1) * (Real.sqrt (4-x^2) / (2*Real.pi))) = (0:ℝ) := by
  let F : ℝ → ℝ := fun x => x^(2*m+1) * (Real.sqrt (4-x^2) / (2*Real.pi))
  have neg (x:ℝ) : F (-x) = - F x := by
    dsimp [F]
    rw [show (-x)^(2*m+1) = -(x^(2*m+1)) by
      exact Odd.neg_pow (by exact ⟨m, by omega⟩) x]
    rw [show 4 - (-x)^2 = (4-x^2:ℝ) by ring]
    ring
  have h := intervalIntegral.integral_comp_neg (a:=(-2:ℝ)) (b:=2) F
  have h' : (∫ x in (-2:ℝ)..2, F x) = - ∫ x in (-2:ℝ)..2, F x := by
    calc
      _ = ∫ x in (-2:ℝ)..2, F (-x) := by
        simpa using h.symm
      _ = ∫ x in (-2:ℝ)..2, - F x := by simp_rw [neg]
      _ = _ := by rw [intervalIntegral.integral_neg]
  change (∫ x in (-2:ℝ)..2, F x) = _
  linarith

/-- The concrete withDensity measure, separated from the problem's name. -/
noncomputable def semicircleConcrete : Measure ℝ :=
  (volume.restrict (Set.Icc (-2 : ℝ) 2)).withDensity
    (fun x => ENNReal.ofReal (Real.sqrt (4 - x ^ 2) / (2 * Real.pi)))

lemma integrable_semipoly (p : ℕ) :
  Integrable (fun x : ℝ => x^p * (Real.sqrt (4-x^2) / (2*Real.pi)))
     (volume.restrict (Set.Icc (-2:ℝ) 2)) := by
  apply ContinuousOn.integrableOn_Icc
  fun_prop

lemma semicircleConcrete_moment_even (m:ℕ) :
  (∫ x : ℝ, x^(2*m) ∂semicircleConcrete) = (catalan m : ℝ) := by
  unfold semicircleConcrete
  rw [integral_withDensity_eq_integral_toReal_smul]
  · change (∫ x in Set.Icc (-2:ℝ) 2,
        (ENNReal.ofReal (Real.sqrt (4 - x^2)/(2*Real.pi))).toReal * x^(2*m)) = _
    have simppt (x:ℝ) :
      (ENNReal.ofReal (Real.sqrt (4 - x^2)/(2*Real.pi))).toReal =
        Real.sqrt (4-x^2)/(2*Real.pi) :=
      ENNReal.toReal_ofReal (by positivity)
    simp_rw [simppt]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-2:ℝ) ≤ 2)]
    convert semi_interval_even m using 1 <;>
      apply intervalIntegral.integral_congr <;> intro x hx <;> ring
  · fun_prop
  · filter_upwards [] with x
    exact ENNReal.ofReal_lt_top

lemma semicircleConcrete_moment_odd (m:ℕ) :
  (∫ x : ℝ, x^(2*m+1) ∂semicircleConcrete) = (0 : ℝ) := by
  unfold semicircleConcrete
  rw [integral_withDensity_eq_integral_toReal_smul]
  · change (∫ x in Set.Icc (-2:ℝ) 2,
        (ENNReal.ofReal (Real.sqrt (4 - x^2)/(2*Real.pi))).toReal * x^(2*m+1)) = _
    have simppt (x:ℝ) :
      (ENNReal.ofReal (Real.sqrt (4 - x^2)/(2*Real.pi))).toReal =
        Real.sqrt (4-x^2)/(2*Real.pi) :=
      ENNReal.toReal_ofReal (by positivity)
    simp_rw [simppt]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-2:ℝ) ≤ 2)]
    convert semi_interval_odd m using 1 <;>
      apply intervalIntegral.integral_congr <;> intro x hx <;> ring
  · fun_prop
  · filter_upwards [] with x
    exact ENNReal.ofReal_lt_top
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Semimom.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Walk.lean
section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace WignerSupport

/-- The upper triangular unordered edge carried by two natural labels. -/
def edgeNat (i j : ℕ) : {p : ℕ × ℕ // p.1 ≤ p.2} :=
  ⟨(min i j, max i j), (min_le_max : min i j ≤ max i j)⟩

@[simp] lemma edgeNat_fst (i j : ℕ) : (edgeNat i j).val.1 = min i j := rfl
@[simp] lemma edgeNat_snd (i j : ℕ) : (edgeNat i j).val.2 = max i j := rfl
lemma edgeNat_comm (i j : ℕ) : edgeNat i j = edgeNat j i := by
  ext <;> simp [edgeNat, min_comm, max_comm]

/-- If one coordinate in a finite product of independent centred variables occurs
exactly once, the expectation of that product is zero.  This is the small independence
lemma used in the closed-walk expansion; keeping the positions and the variables as
separate types is important since closed walks very often repeat edges. -/
lemma integral_prod_zero_of_unique
    {Ω ι α : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [DecidableEq ι] [Fintype α] [DecidableEq α]
    (Z : ι → Ω → ℝ)
    (hm : ∀ i, Measurable (Z i)) (hi : iIndepFun Z μ)
    (hz : ∀ i, (∫ a, Z i a ∂μ) = (0:ℝ))
    (e : α → ι) (u : α)
    (hu : ∀ a, e a = e u → a = u) :
    (∫ ω, (∏ a : α, Z (e a) ω) ∂μ) = 0 := by
  classical
  let S : Finset ι := (Finset.univ.erase u).image e
  have hnot : e u ∉ S := by
    intro h
    rcases Finset.mem_image.mp h with ⟨a, ha, he⟩
    have h' : a = u := hu a he
    subst a
    exact (Finset.notMem_erase u Finset.univ) ha
  -- The tuple of *other* coordinates is independent of the singleton coordinate.
  have hind_tuple :
      IndepFun (fun ω (i : S) => Z i.val ω)
        (fun ω (i : ({e u} : Finset ι)) => Z i.val ω) μ := by
    exact ProbabilityTheory.iIndepFun.indepFun_finset S {e u}
      (Finset.disjoint_singleton_right.mpr hnot) hi hm
  let phi : (S → ℝ) → ℝ := fun v =>
      ∏ a ∈ (Finset.univ.erase u),
        if h : e a ∈ S then v ⟨e a, h⟩ else 1
  have mphi : Measurable phi := by
    dsimp [phi]
    refine Finset.measurable_prod _ ?_
    intro a ha
    by_cases h : e a ∈ S
    · simpa [h] using (@measurable_pi_apply S (fun _ : S => ℝ) _ ⟨e a, h⟩)
    · simp [h]
  let psi : (({e u} : Finset ι) → ℝ) → ℝ := fun v =>
    v ⟨e u, by simp⟩
  have mpsi : Measurable psi := by
    unfold psi
    fun_prop
  have hind0 := hind_tuple.comp mphi mpsi
  have hind : IndepFun
      (fun ω => ∏ a ∈ (Finset.univ.erase u), Z (e a) ω)
      (Z (e u)) μ := by
    -- the dummy branch in `phi` is never taken in this finite product
    have phieval (ω : Ω) :
        phi (fun i : S => Z i.val ω) =
          ∏ a ∈ (Finset.univ.erase u), Z (e a) ω := by
      dsimp [phi]
      apply Finset.prod_congr rfl
      intro a ha
      have ha' : e a ∈ S := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simp [ha']
    have psieval (ω : Ω) :
        psi (fun i : ({e u} : Finset ι) => Z i.val ω) = Z (e u) ω := by
      simp [psi]
    simpa [Function.comp_def, phieval, psieval] using hind0
  have mleft : Measurable (fun ω => ∏ a ∈ (Finset.univ.erase u), Z (e a) ω) := by
    fun_prop
  have prodint := hind.integral_fun_mul_eq_mul_integral
      mleft.aestronglyMeasurable (hm (e u)).aestronglyMeasurable
  have reform (ω : Ω) :
      ((∏ a ∈ (Finset.univ.erase u), Z (e a) ω) * Z (e u) ω) =
        (∏ a : α, Z (e a) ω) := by
    simpa using
      (Finset.prod_erase_mul (s := (Finset.univ : Finset α))
        (f := fun a => Z (e a) ω) (a := u) (by simp))
  have eq0 :
      (∫ ω, (∏ a ∈ (Finset.univ.erase u), Z (e a) ω) * Z (e u) ω ∂μ)
        = 0 := by
    rw [prodint, hz]
    simp
  calc
    (∫ ω, (∏ a : α, Z (e a) ω) ∂μ) =
      ∫ ω, (∏ a ∈ (Finset.univ.erase u), Z (e a) ω) * Z (e u) ω ∂μ := by
        congr 1
        funext ω
        exact (reform ω).symm
    _ = 0 := eq0

end WignerSupport

namespace WignerSupport
open scoped BigOperators

section Paths
variable {κ R : Type*} [Fintype κ] [DecidableEq κ]
  [CommSemiring R]

/-- A rooted path has `p` vertices *after* its root. -/
def pathTerm (A : Matrix κ κ R) :
    (p : ℕ) → κ → (Fin p → κ) → R
  | 0, i, v => 1
  | p+1, i, v => A i (v 0) * pathTerm A p (v 0) (Fin.tail v)

def pathEnd : (p : ℕ) → κ → (Fin p → κ) → κ
  | 0, i, v => i
  | p+1, i, v => pathEnd p (v 0) (Fin.tail v)

@[simp] lemma pathTerm_zero (A : Matrix κ κ R) (i : κ) (v : Fin 0 → κ) :
    pathTerm A 0 i v = 1 := rfl
@[simp] lemma pathTerm_succ (A : Matrix κ κ R) (p : ℕ)
    (i : κ) (v : Fin (p+1) → κ) :
    pathTerm A (p+1) i v = A i (v 0) * pathTerm A p (v 0) (Fin.tail v) := rfl
@[simp] lemma pathEnd_zero (i : κ) (v : Fin 0 → κ) :
    pathEnd 0 i v = i := rfl
@[simp] lemma pathEnd_succ (p : ℕ) (i : κ) (v : Fin (p+1) → κ) :
    pathEnd (p+1) i v = pathEnd p (v 0) (Fin.tail v) := rfl

/-- Entry expansion with the final vertex only used as a test. This convention has a
particularly painless `p=0` case. -/
lemma pow_apply_eq_sum_paths (A : Matrix κ κ R) :
    ∀ (p : ℕ) (i j : κ),
      (A^p) i j =
        ∑ v : (Fin p → κ),
          if pathEnd p i v = j then pathTerm A p i v else 0 := by
  classical
  intro p
  induction p with
  | zero =>
    intro i j
    classical
    have single (f : Fin 0 → κ) : f = Fin.elim0 := Subsingleton.elim _ _
    classical
    simp [Matrix.one_apply, single]
  | succ p ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    -- first expand the shorter continuation
    simp_rw [ih]
    simp_rw [Finset.mul_sum]
    -- `simp_rw` only distributed the inner sum for a fixed first vertex.
    -- Turn the two finite sums into a sum over `Fin.cons`.
    calc
      (∑ x : κ, ∑ v : (Fin p → κ),
          A i x * (if pathEnd p x v = j then pathTerm A p x v else 0)) =
        ∑ t : κ × (Fin p → κ),
          A i t.1 *
            (if pathEnd p t.1 t.2 = j then pathTerm A p t.1 t.2 else 0) := by
              rw [Fintype.sum_prod_type]
      _ = ∑ v : (Fin (p+1) → κ),
          if pathEnd (p+1) i v = j then pathTerm A (p+1) i v else 0 := by
            -- change variables along `Fin.consEquiv`.
            symm
            calc
              (∑ v : (Fin (p+1) → κ),
                if pathEnd (p+1) i v = j then pathTerm A (p+1) i v else 0) =
                ∑ t : κ × (Fin p → κ),
                  (if pathEnd (p+1) i (Fin.cons t.1 t.2) = j then
                     pathTerm A (p+1) i (Fin.cons t.1 t.2) else 0) := by
                       exact (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (p+1) => κ))
                         (fun v => if pathEnd (p+1) i v = j then
                           pathTerm A (p+1) i v else 0)).symm
              _ = _ := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    by_cases h : pathEnd p t.1 t.2 = j
                    · simp [pathEnd_succ, pathTerm_succ, h]
                    · simp [pathEnd_succ, pathTerm_succ, h]

/-- Trace is the sum over rooted closed paths. Each rooted closed path has `p` edges;
the root is kept separate to make the zero-power identity exactly right. -/
lemma trace_pow_eq_sum_closedPaths (A : Matrix κ κ R) (p : ℕ) :
    Matrix.trace (A^p) =
      ∑ i : κ, ∑ v : (Fin p → κ),
        if pathEnd p i v = i then pathTerm A p i v else 0 := by
  classical
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i hi
  exact pow_apply_eq_sum_paths A p i i

end Paths
end WignerSupport

open Matrix Unitary
namespace WignerSupport
/-- Trace power identity (the square version in `Moments` is convenient for norm
bounds; moments need arbitrary powers). -/
lemma hermitian_sum_pow_eigen {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : A.IsHermitian) (p : ℕ) :
    ∑ i, ((h.eigenvalues i : ℂ) ^ p) = Matrix.trace (A ^ p) := by
  classical
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (h.eigenvalues i : ℂ))
  let U := h.eigenvectorUnitary
  have hAA : A ^ p = conjStarAlgAut ℂ _ U (D ^ p) := by
    rw [h.spectral_theorem]
    change _ = _
    simpa [D, U, Function.comp_def] using
      (map_pow (conjStarAlgAut ℂ (Matrix n n ℂ) U)
        (Matrix.diagonal (RCLike.ofReal ∘ h.eigenvalues)) p).symm
  rw [hAA, conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  rw [Unitary.coe_star_mul_self, one_mul]
  -- entries of a power of a diagonal matrix stay diagonal
  have diagpow : D ^ p = Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)^p) := by
    have hpifun : ((fun i => (h.eigenvalues i : ℂ)) ^ p) =
          (fun i => (h.eigenvalues i : ℂ)^p) := by
      ext i; rfl
    simpa [D, hpifun] using
      (map_pow (Matrix.diagonalRingHom (n := n) ℂ)
        (fun i => (h.eigenvalues i : ℂ)) p).symm
  simp [diagpow, Matrix.trace]
end WignerSupport
namespace WignerSupport
/-- Edges of a rooted path, in the same recursive convention as `pathTerm`. -/
def pathEdgesNat {p n : ℕ} :
    (i : Fin n) → (Fin p → Fin n) → (Fin p → {z : ℕ × ℕ // z.1 ≤ z.2}) :=
  match p with
  | 0 => fun i v => Fin.elim0
  | t+1 => fun i v =>
      Fin.cons (edgeNat i.val (v 0).val) (pathEdgesNat (p:=t) (v 0) (Fin.tail v))

@[simp] lemma pathEdgesNat_zero {n : ℕ} (i : Fin n) (v : Fin 0 → Fin n) :
    pathEdgesNat i v = Fin.elim0 := rfl
@[simp] lemma pathEdgesNat_succ_zero {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) :
    pathEdgesNat i v 0 = edgeNat i.val (v 0).val := rfl
@[simp] lemma pathEdgesNat_succ_succ {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (r : Fin p) :
    pathEdgesNat i v r.succ = pathEdgesNat (v 0) (Fin.tail v) r := rfl

/-- For a real symmetric array the rooted term is literally the product of its
upper-triangular coordinates. -/
lemma pathTerm_real_wigner {Ω : Type*} (Y : ℕ → ℕ → Ω → ℝ)
    (ω : Ω) (n p : ℕ) (i : Fin n) (v : Fin p → Fin n) :
    pathTerm (fun a b : Fin n =>
      Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v =
      ∏ r : Fin p, Y (pathEdgesNat i v r).val.1
        (pathEdgesNat i v r).val.2 ω := by
  induction p generalizing i with
  | zero => simp
  | succ p ih =>
    -- take the first edge off on both sides
    rw [pathTerm_succ, Fin.prod_univ_succ]
    rw [ih (v 0)]
    simp [edgeNat]

/-- A walk term with an edge used exactly once has expectation zero. This is the
usable form in the moment enumeration; no integrability of the other factors is
needed for the independence identity (the Bochner identity holds for measurable
compositions). -/
lemma integral_pathTerm_zero_of_unique_edge
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
      (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (hz : ∀ a b, a ≤ b → (∫ ω, Y a b ω ∂μ) = (0:ℝ))
    (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
    (u : Fin p)
    (hu : ∀ r, pathEdgesNat i v r = pathEdgesNat i v u → r = u) :
    (∫ ω, pathTerm (fun a b : Fin n =>
      Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v ∂μ) = 0 := by
  classical
  have hh : (fun ω => pathTerm (fun a b : Fin n =>
      Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v) =
      (fun ω => ∏ r : Fin p, Y (pathEdgesNat i v r).val.1
        (pathEdgesNat i v r).val.2 ω) := by
    funext ω
    exact pathTerm_real_wigner Y ω n p i v
  change (∫ ω, (fun ω => pathTerm (fun a b : Fin n =>
      Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v) ω ∂μ) = 0
  rw [hh]
  let Z : {z : ℕ × ℕ // z.1 ≤ z.2} → Ω → ℝ :=
    fun e => Y e.val.1 e.val.2
  have Zm : ∀ e, Measurable (Z e) := fun e => hm _ _
  have Zz : ∀ e, (∫ a, Z e a ∂μ) = (0:ℝ) :=
    fun e => hz _ _ e.property
  exact integral_prod_zero_of_unique μ Z Zm hi Zz
    (pathEdgesNat i v) u hu
end WignerSupport
namespace WignerSupport
lemma integrable_pathTerm_real_wigner
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ a b ω, |Y a b ω| ≤ B)
    (n p : ℕ) (i : Fin n) (v : Fin p → Fin n) :
    Integrable (fun ω => pathTerm (fun a b : Fin n =>
      Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v) μ := by
  have hh : (fun ω => pathTerm (fun a b : Fin n =>
      Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v) =
      (fun ω => ∏ r : Fin p, Y (pathEdgesNat i v r).val.1
        (pathEdgesNat i v r).val.2 ω) := by
    funext ω; exact pathTerm_real_wigner Y ω n p i v
  rw [hh]
  classical
  refine Integrable.of_bound (μ:=μ) (by fun_prop) (B^p) ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc
    (∏ r : Fin p, |Y (pathEdgesNat i v r).val.1
        (pathEdgesNat i v r).val.2 ω|) ≤
        ∏ _r : Fin p, B := by
          exact Finset.prod_le_prod (fun r hr => abs_nonneg _) (fun r hr => hb _ _ _)
    _ = B ^ p := by simp

end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Walk.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/MomentChar.lean
section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Filter
namespace WignerSupport

lemma catalan_le_four_pow' (n : ℕ) : catalan n ≤ 4^n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have h2 := Nat.centralBinom_le_four_pow n
  calc
    catalan n ≤ (n+1) * catalan n := by
      nlinarith
    _ = n.centralBinom := h
    _ ≤ 4^n := h2

lemma catalan_cast_le_four_pow (n : ℕ) : (catalan n : ℝ) ≤ (4:ℝ)^n := by
  exact_mod_cast (catalan_le_four_pow' n)

-- A convenient, deliberately generous cutoff.  Its square dominates both the
-- support radius and the exponential bound for Catalan moments.
noncomputable def momentRadius (s : ℝ) : ℝ := 8 * (s+1) + 2 * Real.sqrt s

lemma momentRadius_props {s : ℝ} (hs : 0 ≤ s) :
    1 ≤ momentRadius s ∧ Real.sqrt s * 2 ≤ momentRadius s ∧
    0 < momentRadius s ∧ (4*s) / (momentRadius s)^2 ≤ (1:ℝ)/2 ∧
    1 / (momentRadius s)^2 ≤ (1:ℝ)/2 := by
  dsimp [momentRadius]
  have sq0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have sp : 1 ≤ s+1 := by linarith
  have big : 8 ≤ 8*(s+1) := by nlinarith
  have d8 : 8 ≤ 8*(s+1)+2*Real.sqrt s := by nlinarith
  have Dpos : 0 < 8*(s+1)+2*Real.sqrt s := by linarith
  have sqbdd : 8*s ≤ (8*(s+1)+2*Real.sqrt s)^2 := by
    nlinarith [Real.sq_sqrt hs]
  have onebdd : 2 ≤ (8*(s+1)+2*Real.sqrt s)^2 := by nlinarith
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · exact Dpos
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos Dpos)).2
    nlinarith
  · apply (div_le_iff₀ (sq_pos_of_pos Dpos)).2
    nlinarith

-- one estimates the deterministic tail by two geometric sequences
lemma tailMoment_tendsto_zero {s D : ℝ} (hs : 0 ≤ s) (hD : 0 < D)
    (r1 : 4*s / D^2 < 1) (r0 : 1 / D^2 < 1) :
    Tendsto (fun Q : ℕ => ((catalan Q : ℝ) * s^Q + 1) / D^(2*Q)) atTop (𝓝 0) := by
  -- compare with `(4*s/D^2)^Q + (1/D^2)^Q` and squeeze
  have ratio0 : 0 ≤ 4*s / D^2 := by positivity
  have ratio00 : 0 ≤ 1 / D^2 := by positivity
  have lim1 : Tendsto (fun n : ℕ => (4*s / D^2)^n) atTop (𝓝 (0:ℝ)) := by
    have habs : |4*s / D^2| < 1 := by
      rw [abs_of_nonneg ratio0]; exact r1
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs)
  have lim0 : Tendsto (fun n : ℕ => (1 / D^2)^n) atTop (𝓝 (0:ℝ)) := by
    have habs : |1 / D^2| < 1 := by rw [abs_of_nonneg ratio00]; exact r0
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs)
  have upper : Tendsto (fun n : ℕ => (4*s / D^2)^n + (1 / D^2)^n)
      atTop (𝓝 (0:ℝ)) := by
    convert lim1.add lim0 using 1 <;> simp
  -- squeeze the concrete term between zero and the upper sequence
  refine squeeze_zero (fun n => ?_) (fun n => ?_) upper
  · exact div_nonneg (by positivity) (by positivity)
  · have dn : 0 < D^(2*n) := by positivity
    have four := catalan_cast_le_four_pow n
    have le1 : (catalan n : ℝ) * s^n ≤ (4:ℝ)^n * s^n := by
      exact mul_le_mul_of_nonneg_right four (by positivity)
    have eq1 : ((4*s / D^2)^n : ℝ) = ((4:ℝ)^n * s^n) / D^(2*n) := by
      rw [div_pow]
      rw [show (D^2:ℝ)^n = D^(2*n) by ring]
      rw [mul_pow]
    have eq0 : ((1 / D^2)^n : ℝ) = 1 / D^(2*n) := by
      rw [div_pow]
      rw [show (1:ℝ)^n = 1 by simp]
      rw [show (D^2:ℝ)^n = D^(2*n) by ring]
    rw [eq1, eq0]
    calc
      ((catalan n : ℝ) * s^n + 1) / D^(2*n)
        = ((catalan n : ℝ) * s^n) / D^(2*n) + 1 / D^(2*n) := by ring
      _ ≤ ((4:ℝ)^n * s^n) / D^(2*n) + 1 / D^(2*n) := by
          gcongr
      _ = _ := by ring

-- scalar multiple version used by the epsilon chase
lemma polyTail_tendsto_zero (N : ℕ) (t s D : ℝ) (hs : 0 ≤ s) (hD : 0 < D)
    (r1 : 4*s / D^2 < 1) (r0 : 1 / D^2 < 1) :
    Tendsto (fun Q : ℕ =>
      (1 + (N:ℝ) * (|t|+1)^N * D^N) / D^(2*Q) *
          ((catalan Q : ℝ) * s^Q + 1)) atTop (𝓝 (0:ℝ)) := by
  have h := tailMoment_tendsto_zero hs hD r1 r0
  have h' := h.const_mul (1 + (N:ℝ) * (|t|+1)^N * D^N)
  convert h' using 1
  · funext Q
    ring
  · simp

end WignerSupport

namespace WignerSupport
lemma cpoly_as_sum (N:ℕ) (t x:ℝ) :
    cpoly N t x =
      ∑ l ∈ Finset.range N,
        (((((t:ℝ):ℂ)*Complex.I)^l) / (l.factorial:ℕ)) *
          ((x^l:ℝ):ℂ) := by
  unfold cpoly
  apply Finset.sum_congr rfl
  intro l hl
  push_cast
  ring
end WignerSupport
namespace WignerSupport
open scoped ComplexConjugate
lemma row_cpoly_eq (N n : ℕ) (hn : 0 < n) (t : ℝ)
    (b : Fin n → ℝ) :
    (n:ℝ)⁻¹ • (∑ j : Fin n, cpoly N t (b j)) =
      ∑ l ∈ Finset.range N,
        (((((t:ℝ):ℂ)*Complex.I)^l) / (l.factorial:ℕ)) *
          ((( (n:ℝ)⁻¹ * ∑ j : Fin n, (b j)^l : ℝ)) : ℂ) := by
  classical
  -- expose real smul
  simp_rw [cpoly_as_sum]
  simp only [Complex.real_smul]
  push_cast
  -- exchange two finite sums and distribute scalars
  -- `simp` may handle
  simp_rw [Finset.mul_sum]
  --? 
  -- try reorganize
  rw [Finset.sum_comm]
  -- goal inspect
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j hj
  ring
end WignerSupport
namespace WignerSupport
lemma tendsto_row_cpoly_of_moments
    (b : ∀ k : ℕ, Fin (k+1) → ℝ) (L : ℕ → ℝ) (t : ℝ)
    (hpow : ∀ l : ℕ,
      Tendsto (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹ *
        (∑ j : Fin (k+1), (b k j)^l)) atTop (𝓝 (L l)))
    (N : ℕ) :
    Tendsto (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹ •
          (∑ j : Fin (k+1), cpoly N t (b k j))) atTop
      (𝓝 (∑ l ∈ Finset.range N,
        (((((t:ℝ):ℂ)*Complex.I)^l) / (l.factorial:ℕ)) * ((L l : ℝ) : ℂ))) := by
  classical
  have mono (l : ℕ) :
      Tendsto (fun k : ℕ =>
        (((((t:ℝ):ℂ)*Complex.I)^l) / (l.factorial:ℕ)) *
          ((( ((k+1:ℕ):ℝ)⁻¹ *
             (∑ j : Fin (k+1), (b k j)^l) : ℝ)) : ℂ)) atTop
        (𝓝 ((((((t:ℝ):ℂ)*Complex.I)^l) / (l.factorial:ℕ)) *
          ((L l : ℝ) : ℂ))) := by
    have coeLim : Tendsto (fun k : ℕ =>
          ((( ((k+1:ℕ):ℝ)⁻¹ *
             (∑ j : Fin (k+1), (b k j)^l) : ℝ)) : ℂ)) atTop
          (𝓝 ((L l : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hpow l)
    exact Filter.Tendsto.const_mul
      ((((t:ℝ):ℂ)*Complex.I)^l / (l.factorial:ℕ)) coeLim
  have hs := tendsto_finset_sum (Finset.range N)
      (fun l _ => mono l)
  -- rewrite the left row as the displayed finite sum
  convert hs using 1
  funext k
  exact row_cpoly_eq N (k+1) (by omega) t (b k)
end WignerSupport
namespace WignerSupport
lemma integral_cpoly_eq (N : ℕ) (t c : ℝ) (μ : Measure ℝ)
    (hint : ∀ l : ℕ, Integrable (fun x : ℝ => (c*x)^l) μ) :
    (∫ x : ℝ, cpoly N t (c*x) ∂μ) =
      ∑ l ∈ Finset.range N,
       (((((t:ℝ):ℂ)*Complex.I)^l) / (l.factorial:ℕ)) *
          (((∫ x : ℝ, (c*x)^l ∂μ : ℝ)) : ℂ) := by
  classical
  simp_rw [cpoly_as_sum]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [MeasureTheory.integral_const_mul]
    congr 1
    change (∫ x : ℝ, Complex.ofRealCLM ((c*x)^l) ∂μ) = _
    rw [Complex.ofRealCLM.integral_comp_comm (hint l)]
    rfl
  · intro l hl
    have hi : Integrable (fun x : ℝ => ((( (c*x)^l : ℝ)) : ℂ)) μ :=
      Complex.ofRealCLM.integrable_comp (hint l)
    exact hi.const_mul _
end WignerSupport
namespace WignerSupport
lemma exists_taylor_degree (t D ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, |t| * D / ((N+1:ℕ):ℝ) ≤ (1:ℝ)/2 ∧
       (|t| * D)^N / (N.factorial:ℕ) * 2 ≤ ε := by
  have first : ∀ᶠ N : ℕ in atTop,
      |t| * D / ((N+1:ℕ):ℝ) ≤ (1:ℝ)/2 := by
    obtain ⟨m, hm⟩ := exists_nat_ge (2 * (|t| * D))
    filter_upwards [eventually_ge_atTop m] with n hn
    have hge : (m:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (le_trans hn (Nat.le_add_right n 1))
    have v : 2 * (|t| * D) ≤ ((n+1:ℕ):ℝ) := le_trans hm hge
    apply (div_le_iff₀ (by positivity : (0:ℝ) < ((n+1:ℕ):ℝ))).2
    linarith
  have fac := (FloorSemiring.tendsto_pow_div_factorial_atTop (|t| * D : ℝ))
  have second : ∀ᶠ N : ℕ in atTop,
      (|t| * D)^N / (N.factorial:ℕ) < ε/2 :=
    fac (Iio_mem_nhds (by linarith))
  obtain ⟨N, hN, hE⟩ := (first.and second).exists
  refine ⟨N, hN, ?_⟩
  linarith
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/MomentChar.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Perturb.lean
section
open scoped BigOperators ENNReal NNReal Topology
open Matrix Unitary
open scoped ComplexConjugate

namespace WignerSupport
section
variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def hsSq (D : Matrix n n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (D i j)

lemma hsSq_nonneg (D : Matrix n n ℂ) : 0 ≤ hsSq D := by
  unfold hsSq
  exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => Complex.normSq_nonneg _))

lemma trace_star_mul_eq_hs (D : Matrix n n ℂ) :
    (Dᴴ * D).trace = (hsSq D : ℂ) := by
  classical
  unfold hsSq
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.normSq_eq_conj_mul_self]
  rw [Finset.sum_comm]

lemma hsSq_mul_left (U D : Matrix n n ℂ) (hu : Uᴴ * U = 1) :
    hsSq (U * D) = hsSq D := by
  apply Complex.ofReal_inj.mp
  rw [← trace_star_mul_eq_hs, ← trace_star_mul_eq_hs]
  rw [Matrix.conjTranspose_mul]
  have heq : (Dᴴ * Uᴴ) * (U * D) = Dᴴ * D := by
    calc
      _ = Dᴴ * (Uᴴ * U) * D := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu]; simp
  rw [heq]

lemma hsSq_mul_right (D V : Matrix n n ℂ) (hv : V * Vᴴ = 1) :
    hsSq (D * V) = hsSq D := by
  apply Complex.ofReal_inj.mp
  rw [← trace_star_mul_eq_hs, ← trace_star_mul_eq_hs]
  rw [Matrix.conjTranspose_mul]
  have heq : (Vᴴ * Dᴴ) * (D * V) = Vᴴ * (Dᴴ * D) * V := by
    simp only [Matrix.mul_assoc]
  rw [heq, Matrix.trace_mul_cycle]
  simp only [← Matrix.mul_assoc]
  rw [hv]
  simp

variable {A B : Matrix n n ℂ}

noncomputable def overlap (hA : A.IsHermitian) (hB : B.IsHermitian) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hB.eigenvectorUnitary : Matrix n n ℂ)

lemma overlap_unit_left (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (overlap hA hB)ᴴ * overlap hA hB = 1 := by
  classical
  unfold overlap
  rw [Matrix.conjTranspose_mul]
  -- starstar U
  rw [Matrix.conjTranspose_conjTranspose]
  -- (Vᴴ * U) * (Uᴴ * V)
  -- U * Uᴴ = 1
  calc
    _ = (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          ((hA.eigenvectorUnitary : Matrix n n ℂ) *
            (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ) *
          (hB.eigenvectorUnitary : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      have h1 : (hA.eigenvectorUnitary : Matrix n n ℂ) *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 := by
        simpa [← Matrix.star_eq_conjTranspose] using
          (Unitary.coe_mul_star_self hA.eigenvectorUnitary)
      have h2 : (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          (hB.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
        simpa [← Matrix.star_eq_conjTranspose] using
          (Unitary.coe_star_mul_self hB.eigenvectorUnitary)
      rw [h1]; simp [h2] 

lemma overlap_unit_right (hA : A.IsHermitian) (hB : B.IsHermitian) :
    overlap hA hB * (overlap hA hB)ᴴ = 1 := by
  classical
  unfold overlap
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          ((hB.eigenvectorUnitary : Matrix n n ℂ) *
            (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ) *
          (hA.eigenvectorUnitary : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      have h1 : (hB.eigenvectorUnitary : Matrix n n ℂ) *
          (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 := by
        simpa [← Matrix.star_eq_conjTranspose] using
          (Unitary.coe_mul_star_self hB.eigenvectorUnitary)
      have h2 : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
        simpa [← Matrix.star_eq_conjTranspose] using
          (Unitary.coe_star_mul_self hA.eigenvectorUnitary)
      rw [h1]; simp [h2]

noncomputable def weight (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) : ℝ :=
  Complex.normSq ((overlap hA hB) i j)

lemma weight_nonneg (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    0 ≤ weight hA hB i j := Complex.normSq_nonneg _

lemma weight_col (hA : A.IsHermitian) (hB : B.IsHermitian) (j : n) :
    (∑ i, weight hA hB i j) = 1 := by
  classical
  have h := congrArg (fun M : Matrix n n ℂ => M j j) (overlap_unit_left hA hB)
  simp [weight, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.normSq_eq_conj_mul_self] at h
  apply Complex.ofReal_inj.mp
  push_cast
  simpa [weight, Complex.normSq_eq_conj_mul_self] using h

lemma weight_row (hA : A.IsHermitian) (hB : B.IsHermitian) (i : n) :
    (∑ j, weight hA hB i j) = 1 := by
  classical
  have h := congrArg (fun M : Matrix n n ℂ => M i i) (overlap_unit_right hA hB)
  -- expression C i j * conj C i j
  simp [weight, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.mul_conj] at h
  apply Complex.ofReal_inj.mp
  push_cast
  simpa [weight, Complex.mul_conj] using h


lemma hs_eigen_sub (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hsSq (A - B) =
      ∑ i : n, ∑ j : n,
        (weight hA hB i j) *
          ((hA.eigenvalues i - hB.eigenvalues j)^2) := by
  classical
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let V : Matrix n n ℂ := hB.eigenvectorUnitary
  let da : Matrix n n ℂ := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  let db : Matrix n n ℂ := Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ))
  let C : Matrix n n ℂ := Uᴴ * V
  have hUl : U * Uᴴ = 1 := by
    dsimp [U]; simpa [← Matrix.star_eq_conjTranspose] using
      (Unitary.coe_mul_star_self hA.eigenvectorUnitary)
  have hUr : Uᴴ * U = 1 := by
    dsimp [U]; simpa [← Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self hA.eigenvectorUnitary)
  have hVl : V * Vᴴ = 1 := by
    dsimp [V]; simpa [← Matrix.star_eq_conjTranspose] using
      (Unitary.coe_mul_star_self hB.eigenvectorUnitary)
  have hVr : Vᴴ * V = 1 := by
    dsimp [V]; simpa [← Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self hB.eigenvectorUnitary)
  have hdiagA : A = U * da * Uᴴ := by
    simpa [U, da, Unitary.conjStarAlgAut_apply, ← Matrix.star_eq_conjTranspose,
      Function.comp_def] using hA.spectral_theorem
  have hdiagB : B = V * db * Vᴴ := by
    simpa [V, db, Unitary.conjStarAlgAut_apply, ← Matrix.star_eq_conjTranspose,
      Function.comp_def] using hB.spectral_theorem
  have heq : Uᴴ * (A - B) * V = da * C - C * db := by
    rw [hdiagA, hdiagB]
    dsimp [C]
    -- noncomm algebra expansion
    calc
      Uᴴ * (U * da * Uᴴ - V * db * Vᴴ) * V =
        (Uᴴ * U) * da * (Uᴴ * V) - (Uᴴ * V) * db * (Vᴴ * V) := by
          noncomm_ring
      _ = da * (Uᴴ * V) - (Uᴴ * V) * db := by rw [hUr, hVr]; simp
  calc
    hsSq (A - B) = hsSq (Uᴴ * (A-B) * V) := by
      calc
        _ = hsSq (Uᴴ * (A-B)) := (hsSq_mul_left Uᴴ (A-B) (by simpa using hUl)).symm
        _ = hsSq (Uᴴ * (A-B) * V) := (hsSq_mul_right _ V hVl).symm
    _ = hsSq (da * C - C * db) := by rw [heq]
    _ = _ := by
      unfold hsSq
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      -- the diagonal multiplications leave only one overlap entry
      change Complex.normSq ((da * C - C * db) i j) = _
      have hentry : (da * C - C * db) i j =
          ((hA.eigenvalues i - hB.eigenvalues j : ℝ) : ℂ) * C i j := by
        simp [da, db, Matrix.mul_apply, Matrix.diagonal, mul_ite, ite_mul]
        push_cast
        ring
      rw [hentry, Complex.normSq_mul, Complex.normSq_ofReal]
      dsimp [C, weight, overlap, U, V]
      ring

end
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Perturb.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/SLLNBound.lean
section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter Function

namespace WignerSupport

/-- Enumeration of independent upper-triangular entries using the square pairing on naturals.
    Writing the second coordinate as a difference keeps the Cantor code of all entries of an
    `n`-square below `n^2`. -/
def upperEnum (r : ℕ) : {p : ℕ × ℕ // p.1 ≤ p.2} :=
  ⟨(r.unpair.1, r.unpair.1 + r.unpair.2), Nat.le_add_right _ _⟩

lemma upperEnum_injective : Function.Injective upperEnum := by
  intro r s h
  have h1 : r.unpair.1 = s.unpair.1 := by
    have := congrArg (fun z : {p : ℕ × ℕ // p.1 ≤ p.2} => z.val.1) h
    simpa [upperEnum] using this
  have h2' : r.unpair.1 + r.unpair.2 = s.unpair.1 + s.unpair.2 := by
    have := congrArg (fun z : {p : ℕ × ℕ // p.1 ≤ p.2} => z.val.2) h
    simpa [upperEnum] using this
  have h2 : r.unpair.2 = s.unpair.2 := by omega
  have hu : r.unpair = s.unpair := Prod.ext h1 h2
  calc r = Nat.pair r.unpair.1 r.unpair.2 := (Nat.pair_unpair r).symm
       _ = Nat.pair s.unpair.1 s.unpair.2 := by rw [h1, h2]
       _ = s := Nat.pair_unpair _

noncomputable def upperSqSeq {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (r : ℕ) (ω : Ω) : ℝ :=
  (X r.unpair.1 (r.unpair.1 + r.unpair.2) ω)^2

lemma upperSqSeq_nonneg {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (r : ℕ) (ω : Ω) :
    0 ≤ upperSqSeq X r ω := sq_nonneg _

/-- A direct usable consequence of the scalar strong law for the squared entries. -/
lemma upperSqSeq_strongLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (h_indep : iIndepFun (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} => X ij.val.1 ij.val.2) μ)
    (h_iid : ∀ i j i' j', i ≤ j → i' ≤ j' →
      IdentDistrib (X i j) (X i' j') μ μ)
    (h_sq : ∀ i j, i ≤ j → Integrable (fun ω => (X i j ω)^2) μ)
    (h_var : ∀ i j, i ≤ j → ∫ ω, (X i j ω)^2 ∂μ = 1) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun m : ℕ => (∑ r ∈ Finset.range m, upperSqSeq X r ω) / (m:ℝ))
      atTop (𝓝 (1:ℝ)) := by
  let g : ℕ → {p : ℕ × ℕ // p.1 ≤ p.2} := upperEnum
  have hg : Function.Injective g := upperEnum_injective
  have hpre : iIndepFun
      (fun r : ℕ => X (g r).val.1 (g r).val.2) μ :=
    ProbabilityTheory.iIndepFun.precomp hg h_indep
  have hpre' : iIndepFun
      (fun r : ℕ => (fun x : ℝ => x^2) ∘ (X (g r).val.1 (g r).val.2)) μ :=
    ProbabilityTheory.iIndepFun.comp hpre _ (by intro i; fun_prop)
  have hsfun : (fun r : ℕ => (fun x : ℝ => x^2) ∘ (X (g r).val.1 (g r).val.2)) =
      upperSqSeq X := by
    funext r ω
    rfl
  rw [hsfun] at hpre'
  have hpw : Pairwise ((· ⟂ᵢ[μ] ·) on (upperSqSeq X)) := by
    intro i j hij
    exact ProbabilityTheory.iIndepFun.indepFun hpre' hij
  have hident : ∀ r : ℕ, IdentDistrib (upperSqSeq X r) (upperSqSeq X 0) μ μ := by
    intro r
    have h0 : ((0 : ℕ).unpair.1 : ℕ) = 0 := by decide
    have h0' : ((0 : ℕ).unpair.1 + (0 : ℕ).unpair.2 : ℕ) = 0 := by decide
    have hrle : r.unpair.1 ≤ r.unpair.1 + r.unpair.2 := Nat.le_add_right _ _
    have hi := h_iid r.unpair.1 (r.unpair.1 + r.unpair.2) 0 0 hrle (by omega)
    have hi' := hi.comp (by fun_prop : Measurable (fun x : ℝ => x^2))
    -- both sides are just spelling out the compositions
    change IdentDistrib (fun ω => (X r.unpair.1 (r.unpair.1 + r.unpair.2) ω)^2) (fun ω => (X 0 0 ω)^2) μ μ
    simpa [Function.comp_def] using hi'
  have hz : Integrable (upperSqSeq X 0) μ := by
    change Integrable (fun ω => (X 0 0 ω)^2) μ
    simpa using (h_sq 0 0 (by omega))
  have hsll := ProbabilityTheory.strong_law_ae_real (upperSqSeq X) hz hpw hident
  have hv : (∫ ω, upperSqSeq X 0 ω ∂μ) = (1:ℝ) := by
    change (∫ ω, (X 0 0 ω)^2 ∂μ) = (1:ℝ)
    simpa using (h_var 0 0 (by omega))
  simpa [hv] using hsll

end WignerSupport

namespace WignerSupport
open Function
/-- The sum of the squares in a symmetric `n` square is controlled by two consecutive
    square blocks of the independent enumeration.  This is just an injection with a
    bit recording whether an entry is below the diagonal. -/
lemma square_sum_le_enum {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n,
        (X (min (i:ℕ) j) (max (i:ℕ) j) ω)^2) ≤
      2 * (∑ r ∈ Finset.range (n^2), upperSqSeq X r ω) := by
  classical
  -- tagged code of an ordered pair
  let code : (Fin n × Fin n) → (Bool × ℕ) := fun p =>
    if h : p.1.val ≤ p.2.val then
      (false, Nat.pair p.1.val (p.2.val - p.1.val))
    else
      (true, Nat.pair p.2.val (p.1.val - p.2.val))
  let decode : (Bool × ℕ) → (ℕ × ℕ) := fun q =>
    if q.1 then
      let u := q.2.unpair.1
      let d := q.2.unpair.2
      (u+d,u)
    else
      let u := q.2.unpair.1
      let d := q.2.unpair.2
      (u,u+d)
  have hdec (p : Fin n × Fin n) : decode (code p) = (p.1.val, p.2.val) := by
    by_cases h : p.1.val ≤ p.2.val
    · have hf : p.1 ≤ p.2 := h
      have hc : code p = (false, Nat.pair p.1.val (p.2.val-p.1.val)) := by simp [code, hf]
      rw [hc]
      have hadd : p.1.val + (p.2.val-p.1.val) = p.2.val := by omega
      simp [decode, hadd]
    · have h' : p.2.val ≤ p.1.val := Nat.le_of_lt (Nat.lt_of_not_ge h)
      have hf : ¬ p.1 ≤ p.2 := by simpa using h
      have hc : code p = (true, Nat.pair p.2.val (p.1.val-p.2.val)) := by simp [code, hf]
      rw [hc]
      have hadd : p.2.val + (p.1.val-p.2.val) = p.1.val := by omega
      simp [decode, hadd]
  have hinj : Function.Injective code := by
    intro p q h
    have hh := congrArg decode h
    rw [hdec p, hdec q] at hh
    exact Prod.ext (Fin.ext (congrArg Prod.fst hh))
      (Fin.ext (congrArg Prod.snd hh))
  have hrange (p : Fin n × Fin n) : (code p).2 < n^2 := by
    by_cases h : p.1.val ≤ p.2.val
    · have h1 : p.1.val < n := p.1.isLt
      have h2 : p.2.val - p.1.val < n :=
        lt_of_le_of_lt (Nat.sub_le _ _) p.2.isLt
      have hm : max p.1.val (p.2.val - p.1.val) + 1 ≤ n :=
        (Nat.succ_le_iff).2 (max_lt h1 h2)
      have base := Nat.pair_lt_max_add_one_sq p.1.val (p.2.val - p.1.val)
      have powle := Nat.pow_le_pow_left hm 2
      have hc : (code p).2 = Nat.pair p.1.val (p.2.val-p.1.val) := by
        have hf : p.1 ≤ p.2 := h
        simp [code, hf]
      rw [hc]
      exact lt_of_lt_of_le base (by simpa using powle)
    · have h1 : p.2.val < n := p.2.isLt
      have h2 : p.1.val - p.2.val < n :=
        lt_of_le_of_lt (Nat.sub_le _ _) p.1.isLt
      have hm : max p.2.val (p.1.val - p.2.val) + 1 ≤ n :=
        (Nat.succ_le_iff).2 (max_lt h1 h2)
      have base := Nat.pair_lt_max_add_one_sq p.2.val (p.1.val - p.2.val)
      have powle := Nat.pow_le_pow_left hm 2
      have hc : (code p).2 = Nat.pair p.2.val (p.1.val-p.2.val) := by
        have hf : ¬ p.1 ≤ p.2 := by simpa using h
        simp [code, hf]
      rw [hc]
      exact lt_of_lt_of_le base (by simpa using powle)
  let s : Finset (Bool × ℕ) :=
    (Finset.univ.image code) -- image of all entries
  let full : Finset (Bool × ℕ) := Finset.univ.product (Finset.range (n^2))
  let v : (Bool × ℕ) → ℝ := fun q => upperSqSeq X q.2 ω
  have hsub : s ⊆ full := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    simp [full, hrange]
  have himg : (∑ q ∈ s, v q) = ∑ p : (Fin n × Fin n), v (code p) := by
    change (∑ q ∈ Finset.univ.image code, v q) = _
    simpa using (Finset.sum_image (s := (Finset.univ : Finset (Fin n × Fin n)))
      (f := v) (g := code) (fun p hp q hq h => hinj h))
  have hle : (∑ q ∈ s, v q) ≤ ∑ q ∈ full, v q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i hi hi'
      exact upperSqSeq_nonneg X _ _)
  have hfull : (∑ q ∈ full, v q) = 2 * (∑ r ∈ Finset.range (n^2), upperSqSeq X r ω) := by
    classical
    simp [full, v, Finset.sum_product]
  -- the tagged value is the original min/max entry
  have hval (p : Fin n × Fin n) :
      v (code p) = (X (min (p.1.val) p.2.val) (max (p.1.val) p.2.val) ω)^2 := by
    by_cases h : p.1.val ≤ p.2.val
    · have hf : p.1 ≤ p.2 := h
      have hc : (code p).2 = Nat.pair p.1.val (p.2.val-p.1.val) := by
        simp [code, hf]
      have mn : min p.1.val p.2.val = p.1.val := min_eq_left h
      have mx : max p.1.val p.2.val = p.2.val := max_eq_right h
      have hadd : p.1.val + (p.2.val-p.1.val) = p.2.val := by omega
      simp [v, hc, upperSqSeq, mn, mx, hadd]
    · have h' : p.2.val ≤ p.1.val := Nat.le_of_lt (Nat.lt_of_not_ge h)
      have hf : ¬ p.1 ≤ p.2 := by simpa using h
      have hc : (code p).2 = Nat.pair p.2.val (p.1.val-p.2.val) := by
        simp [code, hf]
      have mn : min p.1.val p.2.val = p.2.val := min_eq_right h'
      have mx : max p.1.val p.2.val = p.1.val := max_eq_left h'
      have hadd : p.2.val + (p.1.val-p.2.val) = p.1.val := by omega
      simp [v, hc, upperSqSeq, mn, mx, hadd]
  have ht : (∑ i : Fin n, ∑ j : Fin n,
        (X (min (i:ℕ) j) (max (i:ℕ) j) ω)^2) =
        ∑ p : (Fin n × Fin n), v (code p) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact (hval (i,j)).symm
  rw [ht, ← himg]
  calc
    (∑ q ∈ s, v q) ≤ ∑ q ∈ full, v q := hle
    _ = _ := hfull
end WignerSupport
namespace WignerSupport
open Function Set
/-- A convergent enumeration bounds the normalized sums of all symmetric squares. -/
lemma square_average_bdd {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (ω : Ω)
    (hlim : Tendsto
      (fun m : ℕ => (∑ r ∈ Finset.range m, upperSqSeq X r ω) / (m:ℝ))
      atTop (𝓝 (1:ℝ))) :
    ∃ C : ℝ, ∀ n : ℕ,
      (n:ℝ)⁻¹ * ((n:ℝ)⁻¹ *
        (∑ i : Fin n, ∑ j : Fin n,
          (X (min (i:ℕ) j) (max (i:ℕ) j) ω)^2)) ≤ C := by
  let u : ℕ → ℝ := fun m => (∑ r ∈ Finset.range m, upperSqSeq X r ω) / (m:ℝ)
  have hb := (Metric.isBounded_range_of_tendsto u hlim).bddAbove
  rcases bddAbove_def.1 hb with ⟨D, hD⟩
  have hu : ∀ m, u m ≤ D := fun m => hD _ ⟨m, rfl⟩
  have hD0 : 0 ≤ D := by
    have := hu 0
    simpa [u] using this
  refine ⟨2*D, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp
    exact hD0
  have nr : (0:ℝ) < (n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have nsq : (n:ℝ)^2 > 0 := sq_pos_of_pos nr
  have hs := square_sum_le_enum X ω n
  have hu' := hu (n^2)
  change ((∑ r ∈ Finset.range (n^2), upperSqSeq X r ω) /
       ((n^2 : ℕ) : ℝ)) ≤ D at hu'
  push_cast at hu'
  have hsum : (∑ r ∈ Finset.range (n^2), upperSqSeq X r ω) ≤ (n:ℝ)^2 * D := by
    calc
      (∑ r ∈ Finset.range (n^2), upperSqSeq X r ω) =
          (n:ℝ)^2 * ((∑ r ∈ Finset.range (n^2), upperSqSeq X r ω) / (n:ℝ)^2) := by field_simp
      _ ≤ (n:ℝ)^2 * D := mul_le_mul_of_nonneg_left hu' (le_of_lt nsq)
  have raw : (∑ i : Fin n, ∑ j : Fin n,
          (X (min (i:ℕ) j) (max (i:ℕ) j) ω)^2) ≤ 2 * ((n:ℝ)^2 * D) :=
    hs.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
  calc
    (n:ℝ)⁻¹ * ((n:ℝ)⁻¹ * (∑ i : Fin n, ∑ j : Fin n,
          (X (min (i:ℕ) j) (max (i:ℕ) j) ω)^2)) =
        ((n:ℝ)^2)⁻¹ * (∑ i : Fin n, ∑ j : Fin n,
          (X (min (i:ℕ) j) (max (i:ℕ) j) ω)^2) := by ring
    _ ≤ ((n:ℝ)^2)⁻¹ * (2 * ((n:ℝ)^2 * D)) :=
      mul_le_mul_of_nonneg_left raw (by positivity)
    _ = 2 * D := by field_simp
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/SLLNBound.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/WalkCount.lean
section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport

/-- The vertices seen by a walk written as a root followed by a list. -/
def walkVertices (i : ℕ) (xs : List ℕ) : Finset ℕ :=
  insert i xs.toFinset

/-- The (unoriented, upper-triangular) edges of a walk written as a root and a list. -/
def walkEdges (i : ℕ) : List ℕ →
    Finset {z : ℕ × ℕ // z.1 ≤ z.2}
  | [] => ∅
  | j :: xs => insert (edgeNat i j) (walkEdges j xs)

@[simp] lemma walkVertices_nil (i : ℕ) : walkVertices i [] = {i} := by
  simp [walkVertices]
@[simp] lemma walkVertices_cons (i j : ℕ) (xs : List ℕ) :
    walkVertices i (j :: xs) = insert i (walkVertices j xs) := by
  simp [walkVertices, List.toFinset_cons, Finset.insert_comm]

@[simp] lemma walkEdges_nil (i : ℕ) : walkEdges i [] = ∅ := rfl
@[simp] lemma walkEdges_cons (i j : ℕ) (xs : List ℕ) :
    walkEdges i (j :: xs) = insert (edgeNat i j) (walkEdges j xs) := rfl

lemma walkVertices_root_mem (i : ℕ) (xs : List ℕ) :
    i ∈ walkVertices i xs := by
  simp [walkVertices]

/-- Every endpoint of a previously traversed edge has already been seen.
This is the invariant that makes the usual graph bound `#vertices ≤ #edges + 1`
quite painless without introducing an abstract graph. -/
lemma walkEdges_endpoints
    (i : ℕ) (xs : List ℕ)
    (e : {z : ℕ × ℕ // z.1 ≤ z.2})
    (he : e ∈ walkEdges i xs) :
    e.val.1 ∈ walkVertices i xs ∧ e.val.2 ∈ walkVertices i xs := by
  classical
  induction xs generalizing i with
  | nil => simpa [walkEdges] using he
  | cons j ys ih =>
    have hmem : e = edgeNat i j ∨ e ∈ walkEdges j ys := by
      simpa [walkEdges] using he
    rcases hmem with hnew | hold
    · subst e
      -- `min` and `max` are the two endpoints.
      have hi : i ∈ walkVertices i (j::ys) := by
        simp [walkVertices]
      have hj0 : j ∈ walkVertices j ys := walkVertices_root_mem _ _
      have hj : j ∈ walkVertices i (j::ys) := by
        -- the continuation's root is kept in the outer insert
        simp [walkVertices]
      constructor
      · have hchoice : min i j = i ∨ min i j = j := min_choice _ _
        rcases hchoice with h | h
        · simpa [edgeNat, h] using hi
        · simpa [edgeNat, h] using hj
      · have hchoice : max i j = i ∨ max i j = j := max_choice _ _
        rcases hchoice with h | h
        · simpa [edgeNat, h] using hi
        · simpa [edgeNat, h] using hj
    · have ih' := ih (i := j) hold
      constructor
      · -- endpoints of a tail edge remain in the outer vertex set
        simpa [walkVertices] using (show
          e.val.1 ∈ insert i (walkVertices j ys) from
            (Finset.mem_insert_of_mem (ih'.1)))
      · simpa [walkVertices] using (show
          e.val.2 ∈ insert i (walkVertices j ys) from
            (Finset.mem_insert_of_mem (ih'.2)))

/-- A connected list walk has at most one more vertex than distinct edges.
Loops and repetitions need no special treatment. -/
lemma card_walkVertices_le_edges_add_one (i : ℕ) (xs : List ℕ) :
    (walkVertices i xs).card ≤ (walkEdges i xs).card + 1 := by
  classical
  induction xs generalizing i with
  | nil => simp [walkVertices, walkEdges]
  | cons j ys ih =>
    by_cases hi : i ∈ walkVertices j ys
    · have hv : walkVertices i (j::ys) = walkVertices j ys := by
        simp [walkVertices_cons, hi]
      have hs : walkEdges j ys ⊆ walkEdges i (j::ys) := by
        intro e he
        simp [walkEdges, he]
      have hc : (walkEdges j ys).card ≤ (walkEdges i (j::ys)).card :=
        Finset.card_le_card hs
      have I := ih (i := j)
      rw [hv]
      omega
    · have hne : edgeNat i j ∉ walkEdges j ys := by
        intro h
        have ep := walkEdges_endpoints j ys (edgeNat i j) h
        have hchoice : min i j = i ∨ min i j = j := min_choice _ _
        rcases hchoice with h1 | h1
        · exact hi (by simpa [edgeNat, h1] using ep.1)
        · have hchoice' : max i j = i ∨ max i j = j := max_choice _ _
          rcases hchoice' with h2 | h2
          · exact hi (by simpa [edgeNat, h2] using ep.2)
          · -- both min and max cannot both be the old endpoint unless the endpoints are equal
            have heq : i = j := by
              -- min = j and max = j force i=j
              omega
            subst i
            exact hi (walkVertices_root_mem j ys)
    
      have hvcard : (walkVertices i (j::ys)).card =
          (walkVertices j ys).card + 1 := by
        rw [walkVertices_cons, Finset.card_insert_of_notMem hi]
      have hecard : (walkEdges i (j::ys)).card =
          (walkEdges j ys).card + 1 := by
        simp [walkEdges, Finset.card_insert_of_notMem hne]
      rw [hvcard, hecard]
      have I := ih (i := j)
      omega

-- A path's list representation.  Keeping the root separate matches `pathTerm`.
def pathList {n p : ℕ} (v : Fin p → Fin n) : List ℕ :=
  List.ofFn (fun r : Fin p => (v r).val)

@[simp] lemma pathList_zero {n : ℕ} (v : Fin 0 → Fin n) :
    pathList v = [] := by
  simp [pathList]

/-- Taking the tail of a rooted path is just dropping the first item in its list. -/
@[simp] lemma pathList_succ {n p : ℕ} (v : Fin (p+1) → Fin n) :
    pathList v = (v 0).val :: pathList (Fin.tail v) := by
  unfold pathList
  rw [List.ofFn_succ]
  congr 1

-- Splitting the image of a successor `Fin`.  The little lemma keeps all later
-- graph statements independent of any arbitrary enumeration of `Fin`.
lemma image_univ_fin_succ {α : Type*} [DecidableEq α]
    {p : ℕ} (f : Fin (p+1) → α) :
    (Finset.univ.image f) =
      insert (f 0) (Finset.univ.image (fun r : Fin p => f r.succ)) := by
  classical
  ext a
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨r, -, hr⟩
    -- eliminate `r`, making the equality part of the motive
    revert hr
    refine Fin.cases ?_ (fun t => ?_) r
    · intro h
      exact Finset.mem_insert.mpr (Or.inl h.symm)
    · intro h
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, h⟩)
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, h.symm⟩
    · rcases Finset.mem_image.mp h with ⟨r, -, hr⟩
      exact Finset.mem_image.mpr ⟨r.succ, Finset.mem_univ _, hr⟩

/-- The finite image of the literal edge list agrees with the recursive list walk.
Using a `Finset.image` instead of a quotient graph is often easier in the moment bound. -/
lemma image_pathEdges_eq_walkEdges {n p : ℕ}
    (i : Fin n) (v : Fin p → Fin n) :
    (Finset.univ.image (pathEdgesNat i v)) =
      walkEdges i.val (pathList v) := by
  classical
  induction p generalizing i with
  | zero => simp [walkEdges, pathList]
  | succ p ih =>
    rw [image_univ_fin_succ (pathEdgesNat i v)]
    -- the zeroth edge is `(i,v 0)`, all remaining ones are the tail
    have hz : pathEdgesNat i v (0 : Fin (p+1)) = edgeNat i.val (v 0).val := rfl
    -- the function underlying the tail is definitionally the recursive one, but spelling it
    -- out with `funext` avoids rewriting a dependent `Finset.image` by hand below.
    have ht : (fun r : Fin p => pathEdgesNat i v r.succ) =
        pathEdgesNat (v 0) (Fin.tail v) := by
      funext r; rfl
    rw [hz, ht, ih (i := v 0)]
    rw [pathList_succ]
    rfl

/-- The vertices of the finite `Fin` path (as naturals) are its root plus the list image. -/
def pathVerticesFin {n p : ℕ} (i : Fin n) (v : Fin p → Fin n) : Finset ℕ :=
  walkVertices i.val (pathList v)

lemma card_pathVertices_le_edges_add_one {n p : ℕ} (i : Fin n)
    (v : Fin p → Fin n) :
    (pathVerticesFin i v).card ≤
      (Finset.univ.image (pathEdgesNat i v)).card + 1 := by
  classical
  simpa [pathVerticesFin, image_pathEdges_eq_walkEdges] using
    (card_walkVertices_le_edges_add_one i.val (pathList v))

/-- A fiber which contains two unequal indices has cardinality at least two. -/
lemma two_le_card_fiber_of_pair {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β)
    {u r : α} (hu : u ∈ s) (hr : r ∈ s) (hne : r ≠ u) (eqr : f r = f u) :
    2 ≤ (s.filter (fun a => f a = f u)).card := by
  classical
  have sub : {u, r} ⊆ s.filter (fun a => f a = f u) := by
    intro a ha
    have ha' : a = u ∨ a = r := by simpa [or_comm] using ha
    rcases ha' with rfl | rfl
    · simp [hu]
    · simp [hr, eqr]
  have cardpair : ({u, r} : Finset α).card = 2 := by
    have hne' : u ≠ r := Ne.symm hne
    simp [hne']
  have hc := Finset.card_le_card sub
  simpa [cardpair] using hc

/-- If every step of a finite path repeats some other step with the same unordered
edge, the number of distinct edges is at most `p/2`.  This is exactly the
fiber-count bound used after removing singleton edges. -/
lemma card_image_pathEdges_le_half {n p : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (rep : ∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧ pathEdgesNat i v r = pathEdgesNat i v u) :
    (Finset.univ.image (pathEdgesNat i v)).card ≤ p / 2 := by
  classical
  let f := pathEdgesNat i v
  let s : Finset (Fin p) := Finset.univ
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} := s.image f
  have each : ∀ e ∈ E, 2 ≤ (s.filter (fun a => f a = e)).card := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨u, hu, rfl⟩
    rcases rep u with ⟨r, hne, hr⟩
    exact two_le_card_fiber_of_pair s f hu (by simp [s]) hne hr
  have cnt : s.card = ∑ e ∈ E, (s.filter (fun a => f a = e)).card := by
    -- library `card_eq_sum_card_image` is the clean fiberwise formula
    dsimp [E]
    exact Finset.card_eq_sum_card_image f s
  have leq : (∑ _e ∈ E, 2) ≤
      ∑ e ∈ E, (s.filter (fun a => f a = e)).card := by
    exact Finset.sum_le_sum (fun e he => each e he)
  have Ebd : 2 * E.card ≤ p := by
    have scard : s.card = p := by simp [s]
    rw [← cnt] at leq
    rw [scard] at leq
    simpa [mul_comm, mul_left_comm, mul_assoc] using leq
  change E.card ≤ p / 2
  omega

/-- Combined graph/fiber bound.  A closed path will in addition impose `pathEnd=i`,
but no closedness is needed for the cardinal estimate itself. -/
lemma card_pathVertices_le_half_add_one {n p : ℕ} (i : Fin n)
    (v : Fin p → Fin n)
    (rep : ∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧ pathEdgesNat i v r = pathEdgesNat i v u) :
    (pathVerticesFin i v).card ≤ p / 2 + 1 := by
  have h1 := card_pathVertices_le_edges_add_one i v
  have h2 := card_image_pathEdges_le_half i v rep
  omega

end WignerSupport

namespace WignerSupport
/-- In the equality case of the graph bound (and with even length), every occupied
edge has a two-element fiber. This is the small extremal observation behind the
`variance` rather than a higher moment in the leading term. -/
lemma fibers_two_of_max_vertices {n p : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (heven : 2 ∣ p)
    (rep : ∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧ pathEdgesNat i v r = pathEdgesNat i v u)
    (hv : (pathVerticesFin i v).card = p / 2 + 1) :
    ∀ e ∈ (Finset.univ.image (pathEdgesNat i v)),
      ((Finset.univ : Finset (Fin p)).filter
        (fun r => pathEdgesNat i v r = e)).card = 2 := by
  classical
  let f := pathEdgesNat i v
  let s : Finset (Fin p) := Finset.univ
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} := s.image f
  have lower (e) (he : e ∈ E) :
      2 ≤ (s.filter (fun r => f r = e)).card := by
    rcases Finset.mem_image.mp he with ⟨u, hu, rfl⟩
    rcases rep u with ⟨r, hne, hr⟩
    exact two_le_card_fiber_of_pair s f hu (by simp [s]) hne hr
  have edgehi : E.card ≤ p/2 := by
    simpa [E, s, f] using (card_image_pathEdges_le_half i v rep)
  have edgelo : p/2 ≤ E.card := by
    have gr := card_pathVertices_le_edges_add_one i v
    change (pathVerticesFin i v).card ≤ E.card + 1 at gr
    rw [hv] at gr
    omega
  have edgeeq : E.card = p/2 := Nat.le_antisymm edgehi edgelo
  have cnt : s.card = ∑ e ∈ E, (s.filter (fun r => f r = e)).card := by
    exact Finset.card_eq_sum_card_image f s
  have scard : s.card = p := by simp [s]
  have sumval : (∑ e ∈ E, (s.filter (fun r => f r = e)).card) = 2 * E.card := by
    rw [← cnt, scard, edgeeq]
    omega
  intro e he
  have all_le : (∑ e' ∈ E, 2) ≤
      ∑ e' ∈ E, (s.filter (fun r => f r = e')).card :=
    Finset.sum_le_sum (fun a ha => lower a ha)
  -- If this fiber were larger than two it would make the whole sum larger.
  have notgt : ¬ 2 < (s.filter (fun r => f r = e)).card := by
    intro hgt
    have strict : (∑ e' ∈ E, 2) <
        ∑ e' ∈ E, (s.filter (fun r => f r = e')).card := by
      -- strictness in one summand
      exact Finset.sum_lt_sum (fun a ha => lower a ha) ⟨e, he, hgt⟩
    rw [sumval] at strict
    have consteq : (∑ _e ∈ E, 2) = 2 * E.card := by
      simp [mul_comm]
    rw [consteq] at strict
    exact (Nat.lt_irrefl _ strict)
  have lo := lower e he
  have eq : (s.filter (fun r => f r = e)).card = 2 := by omega
  simpa [s, f, E] using eq
end WignerSupport

namespace WignerSupport
/-- `pathVerticesFin` really is the image of the `(p+1)`-tuple gotten by
prepending the root. -/
lemma pathVertices_eq_image_cons {n p : ℕ} (i : Fin n) (v : Fin p → Fin n) :
    pathVerticesFin i v =
      (Finset.univ : Finset (Fin (p+1))).image
        (fun r => (@Fin.cons p (fun _ => Fin n) i v r).val) := by
  classical
  ext a
  simp [pathVerticesFin, walkVertices, pathList, List.mem_ofFn]
  constructor
  · intro h
    rcases h with h | ⟨r, hr⟩
    · refine ⟨0, ?_⟩
      simpa using h.symm
    · refine ⟨r.succ, ?_⟩
      simpa using hr
  · intro h
    rcases h with ⟨r, hr⟩
    revert hr
    refine Fin.cases ?_ (fun t => ?_) r
    · intro h
      exact Or.inl h.symm
    · intro h
      refine Or.inr ⟨t, ?_⟩
      simpa using h
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/WalkCount.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Compare.lean
section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Filter
open Matrix

namespace WignerSupport

/-- empirical characteristic sum of the eigenvalues of a Hermitian matrix, with the
natural `√n` scaling.  Keeping this definition in the deterministic part of the
argument is convenient for perturbation estimates. -/
noncomputable def eigenChar {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (t : ℝ) : ℂ :=
  (n:ℝ)⁻¹ • ∑ i : Fin n,
    Complex.exp (((((hA.eigenvalues i / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I)

/-- The overlap weights have total mass `n`.  This is the simple way of putting
both eigenvalue enumerations on the same finite sample space. -/
lemma weight_sum {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i : Fin n, ∑ j : Fin n, weight hA hB i j) = (n:ℝ) := by
  classical
  calc
    (∑ i : Fin n, ∑ j : Fin n, weight hA hB i j)
        = ∑ i : Fin n, (1:ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact weight_row hA hB i
    _ = _ := by simp

/-- Express a difference of the two characteristic sums using the overlap of the
unitary eigenbases.  This identity is useful because it does not assume any
alignment between the library's two enumerations of eigenvalues. -/
lemma eigenChar_sub_as_weight {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    eigenChar hA t - eigenChar hB t =
      (n:ℝ)⁻¹ •
        (∑ i : Fin n, ∑ j : Fin n,
          (weight hA hB i j : ℂ) *
          (Complex.exp (((((hA.eigenvalues i / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I) -
           Complex.exp (((((hB.eigenvalues j / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I))) := by
  classical
  unfold eigenChar
  rw [← smul_sub]
  congr 1
  let ea : Fin n → ℂ := fun i =>
    Complex.exp (((((hA.eigenvalues i / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I)
  let eb : Fin n → ℂ := fun j =>
    Complex.exp (((((hB.eigenvalues j / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I)
  change (∑ i, ea i) - ∑ j, eb j = _
  -- two telescoping insertions of the row/column sums
  calc
    (∑ i, ea i) - ∑ j, eb j =
        (∑ i : Fin n, ∑ j : Fin n,
              (weight hA hB i j : ℂ) * ea i) -
          (∑ i : Fin n, ∑ j : Fin n,
              (weight hA hB i j : ℂ) * eb j) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro i hi
            have hr : (∑ j : Fin n, weight hA hB i j) = (1:ℝ) :=
              weight_row hA hB i
            calc
              ea i = (1:ℂ) * ea i := by simp
              _ = (((∑ j : Fin n, weight hA hB i j : ℝ) : ℂ) * ea i) := by rw [hr]; simp
              _ = ∑ j : Fin n, (weight hA hB i j : ℂ) * ea i := by
                    push_cast
                    rw [Finset.sum_mul]
          · -- columns, followed by the harmless exchange of the two sums
            calc
              ∑ j : Fin n, eb j = ∑ j : Fin n, ∑ i : Fin n,
                    (weight hA hB i j : ℂ) * eb j := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      have hc : (∑ i : Fin n, weight hA hB i j) = (1:ℝ) :=
                        weight_col hA hB j
                      calc
                        eb j = (1:ℂ) * eb j := by simp
                        _ = (((∑ i : Fin n, weight hA hB i j : ℝ) : ℂ) * eb j) := by rw [hc]; simp
                        _ = ∑ i : Fin n, (weight hA hB i j : ℂ) * eb j := by
                              push_cast
                              rw [Finset.sum_mul]
              _ = ∑ i : Fin n, ∑ j : Fin n,
                    (weight hA hB i j : ℂ) * eb j := by
                      rw [Finset.sum_comm]
    _ = _ := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          -- now only distributivity in `ℂ`
          ring

/-- `|u| ≤ u²/(2δ)+δ/2` is the elementary (AM--GM) form of
Cauchy--Schwarz that avoids taking square roots in the perturbation estimate. -/
lemma abs_le_sq_div_add (u : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    |u| ≤ u^2 / (2*δ) + δ/2 := by
  have hsq : 0 ≤ (|u| - δ)^2 := sq_nonneg _
  have hd : 0 < (2:ℝ)*δ := by positivity
  -- multiply through by the positive denominator
  have heq : u^2 / (2*δ) + δ/2 - |u| = (|u|-δ)^2 / (2*δ) := by
    rw [← sq_abs u]
    field_simp
    <;> ring
  have hz : 0 ≤ u^2 / (2*δ) + δ/2 - |u| := by
    rw [heq]
    exact div_nonneg hsq (le_of_lt hd)
  linarith

/-- Deterministic Hoffman--Wielandt/Lipschitz consequence.  It compares two
Hermitian characteristic sums without making any choices about the order of
the eigenvalues.  The cost is their Hilbert--Schmidt distance divided by `n²`.
The small parameter formulation is especially handy for heavy tails: first
let `n → ∞`, then choose a cutoff, and finally let `δ ↓ 0`.

Only a finite-dimensional spectral calculation is used; no probability
appears here. -/
lemma eigenChar_sub_le_eps {n : ℕ} (hn : n ≠ 0)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖eigenChar hA t - eigenChar hB t‖ ≤
      (2 * |t|) * (((n:ℝ)⁻¹ * ((n:ℝ)⁻¹ * hsSq (A-B))) / (2*δ) + δ/2) := by
  classical
  have hnpos : (0:ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hsqrt : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hnpos
  have hinv : 0 ≤ (n:ℝ)⁻¹ := by positivity
  -- common denominator identity for a pair of eigenvalues
  let d : Fin n → Fin n → ℝ := fun i j =>
    hA.eigenvalues i - hB.eigenvalues j
  let u : Fin n → Fin n → ℝ := fun i j => d i j / Real.sqrt n
  let w : Fin n → Fin n → ℝ := fun i j => weight hA hB i j
  have hu (i j) :
      hA.eigenvalues i / Real.sqrt n - hB.eigenvalues j / Real.sqrt n = u i j := by
    dsimp [u, d]
    ring
  have husq (i j) : (u i j)^2 = (n:ℝ)⁻¹ * (d i j)^2 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt (le_of_lt hnpos)]
    simp [div_eq_inv_mul]
  have hmass : (∑ i : Fin n, ∑ j : Fin n, w i j) = (n:ℝ) := by
    simpa [w] using (weight_sum hA hB)
  have henergy : (∑ i : Fin n, ∑ j : Fin n, w i j * (d i j)^2)
        = hsSq (A-B) := by
    simpa [w, d] using (hs_eigen_sub hA hB).symm
  have huv : (∑ i : Fin n, ∑ j : Fin n, w i j * |u i j|) ≤
        (∑ i : Fin n, ∑ j : Fin n,
            w i j * ((u i j)^2 / (2*δ) + δ/2)) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hw : 0 ≤ w i j := weight_nonneg _ _ _ _
    exact mul_le_mul_of_nonneg_left (abs_le_sq_div_add (u i j) hδ) hw
  have huv' : (n:ℝ)⁻¹ * (∑ i : Fin n, ∑ j : Fin n, w i j * |u i j|) ≤
        ((n:ℝ)⁻¹ * ((n:ℝ)⁻¹ * hsSq (A-B))) / (2*δ) + δ/2 := by
    calc
      (n:ℝ)⁻¹ * (∑ i : Fin n, ∑ j : Fin n, w i j * |u i j|) ≤
          (n:ℝ)⁻¹ * (∑ i : Fin n, ∑ j : Fin n,
            w i j * ((u i j)^2 / (2*δ) + δ/2)) :=
              mul_le_mul_of_nonneg_left huv hinv
      _ = ((n:ℝ)⁻¹ * ((n:ℝ)⁻¹ * hsSq (A-B))) / (2*δ) + δ/2 := by
        -- split the two finite sums and use row/column mass once.
        simp_rw [mul_add]
        rw [show (∑ i : Fin n, ∑ j : Fin n,
              (w i j * ((u i j)^2 / (2*δ)) + w i j * (δ/2))) =
              (∑ i : Fin n, ∑ j : Fin n, w i j * ((u i j)^2 / (2*δ))) +
              (∑ i : Fin n, ∑ j : Fin n, w i j * (δ/2)) by
                simp_rw [Finset.sum_add_distrib]]
        have h1 : (∑ i : Fin n, ∑ j : Fin n, w i j * ((u i j)^2 / (2*δ))) =
            ((n:ℝ)⁻¹ * hsSq (A-B)) / (2*δ) := by
              -- put both constants in front and distribute them out of the nested sums
              calc
                (∑ i : Fin n, ∑ j : Fin n,
                    w i j * ((u i j)^2 / (2*δ))) =
                    ∑ i : Fin n, ∑ j : Fin n,
                      (((n:ℝ)⁻¹ / (2*δ)) * (w i j * (d i j)^2)) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [husq]
                        ring
                _ = (((n:ℝ)⁻¹ / (2*δ)) *
                      (∑ i : Fin n, ∑ j : Fin n, w i j * (d i j)^2)) := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro i hi
                        rw [Finset.mul_sum]
                _ = _ := by rw [henergy]
                           <;> ring
        have h2 : (∑ i : Fin n, ∑ j : Fin n, w i j * (δ/2)) =
            (n:ℝ) * (δ/2) := by
              calc
                (∑ i : Fin n, ∑ j : Fin n, w i j * (δ/2)) =
                    ∑ i : Fin n, (∑ j : Fin n, w i j) * (δ/2) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [Finset.sum_mul]
                _ = ∑ i : Fin n, (1:ℝ) * (δ/2) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      have hr : (∑ j : Fin n, w i j) = (1:ℝ) := by
                        simpa [w] using (weight_row hA hB i)
                      rw [hr]
                _ = _ := by simp
        rw [h1, h2]
        field_simp <;> ring
  rw [eigenChar_sub_as_weight hA hB t]
  -- the triangle inequality for the double finite sum, followed by the
  -- elementary Lipschitz bound for each exponential.
  calc
    ‖(n:ℝ)⁻¹ •
        (∑ i : Fin n, ∑ j : Fin n,
          (weight hA hB i j : ℂ) *
          (Complex.exp (((((hA.eigenvalues i / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I) -
           Complex.exp (((((hB.eigenvalues j / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I)))‖ ≤
       (n:ℝ)⁻¹ *
        (∑ i : Fin n, ∑ j : Fin n,
          w i j * (2 * |t| * |u i j|)) := by
            rw [norm_smul]
            rw [Real.norm_eq_abs, abs_of_nonneg hinv]
            gcongr 1
            -- twice the finite triangle inequality
            calc
              ‖(∑ i : Fin n, ∑ j : Fin n,
                (weight hA hB i j : ℂ) *
                (Complex.exp (((((hA.eigenvalues i / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I) -
                 Complex.exp (((((hB.eigenvalues j / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I)))‖ ≤
                  ∑ i : Fin n, ‖∑ j : Fin n,
                    (weight hA hB i j : ℂ) *
                    (Complex.exp (((((hA.eigenvalues i / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I) -
                     Complex.exp (((((hB.eigenvalues j / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I))‖ :=
                      norm_sum_le _ _
              _ ≤ ∑ i : Fin n, ∑ j : Fin n,
                    ‖(weight hA hB i j : ℂ) *
                    (Complex.exp (((((hA.eigenvalues i / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I) -
                     Complex.exp (((((hB.eigenvalues j / Real.sqrt n) * t : ℝ)) : ℂ) * Complex.I))‖ := by
                      apply Finset.sum_le_sum
                      intro i hi
                      exact norm_sum_le _ _
              _ ≤ ∑ i : Fin n, ∑ j : Fin n, w i j * (2 * |t| * |u i j|) := by
                    apply Finset.sum_le_sum
                    intro i hi
                    apply Finset.sum_le_sum
                    intro j hj
                    have hw : 0 ≤ w i j := weight_nonneg _ _ _ _
                    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                      abs_of_nonneg hw]
                    have he := norm_exp_mul_I_sub_exp_mul_I
                      ((hA.eigenvalues i / Real.sqrt n) * t)
                      ((hB.eigenvalues j / Real.sqrt n) * t)
                    -- substitute the common denominator
                    have hx : |(hA.eigenvalues i / Real.sqrt n) * t -
                                (hB.eigenvalues j / Real.sqrt n) * t| =
                                |t| * |u i j| := by
                          rw [← sub_mul]
                          rw [hu]
                          rw [abs_mul]
                          rw [mul_comm]
                    rw [hx] at he
                    dsimp [w]
                    gcongr
                    nlinarith
    _ ≤ _ := by
          -- rearrange the positive constant and use the AM--GM estimate above
          have hc : 0 ≤ (2 * |t|) := by positivity
          have heq :
              (n:ℝ)⁻¹ * (∑ i : Fin n, ∑ j : Fin n,
                 w i j * (2 * |t| * |u i j|)) =
                (2 * |t|) * ((n:ℝ)⁻¹ *
                  (∑ i : Fin n, ∑ j : Fin n, w i j * |u i j|)) := by
                    -- pull the constant out of both sums
                    -- use commutativity to make it a right constant
                    -- a short algebraic normalization is less fragile than `ring` on binders
                    calc
                      (n:ℝ)⁻¹ * (∑ i : Fin n, ∑ j : Fin n,
                         w i j * (2 * |t| * |u i j|)) =
                        (n:ℝ)⁻¹ * ((2 * |t|) *
                          (∑ i : Fin n, ∑ j : Fin n, w i j * |u i j|)) := by
                            congr 1
                            -- distributivity after putting the constant first
                            --
                            simp_rw [show ∀ (a b c : ℝ), a * (b*c) = b * (a*c) by
                              intro a b c; ring]
                            rw [Finset.mul_sum]
                            apply Finset.sum_congr rfl
                            intro i hi
                            rw [Finset.mul_sum]
                      _ = _ := by ring
          rw [heq]
          exact mul_le_mul_of_nonneg_left huv' hc

end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Compare.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Leading.lean
section

/-!
Some finite relabelling facts for the leading closed paths.  The labels of a
walk do not have an order: after its equality pattern is fixed the labels may
be chosen *injectively*.  Keeping this separate is useful, since counting
arbitrary maps from the used vertices gives `n^d` but the leading coefficient
uses the falling factorial.  Everything here includes the cases `d=0` and
`n<d`.
-/
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport

/-- Words with exactly the equality pattern of `g`.  It is important to ask
for the biconditional -- a mere implication would also contain all coarser
patterns. -/
def Relabels {m d n : ℕ} (g : Fin m → Fin d) :=
  {f : Fin m → Fin n // ∀ a b, f a = f b ↔ g a = g b}

noncomputable instance relabelsFintype {m d n : ℕ} (g : Fin m → Fin d) :
    Fintype (Relabels (n:=n) g) := by
  classical
  let t : Finset (Fin m → Fin n) :=
    (Finset.univ : Finset (Fin m → Fin n)).filter
      (fun f => ∀ a b, f a = f b ↔ g a = g b)
  exact Fintype.subtype t (by
    intro f
    simp [t])

/-- Once a word `g` hits all its `d` letters, relabelling it is the same as an
embedding of those letters.  We deliberately never choose an ordering of the
image of a labelled word.  Instead we choose one preimage of each letter of
`g`; the inverse laws only use the equality-pattern biconditional.
-/
noncomputable def relabelsEquivEmbedding {m d n : ℕ}
    (g : Fin m → Fin d) (hg : Function.Surjective g) :
    Relabels (n:=n) g ≃ (Fin d ↪ Fin n) := by
  classical
  choose s hs using hg
  let toE : Relabels (n:=n) g → (Fin d ↪ Fin n) := fun f =>
    { toFun := fun a => f.1 (s a)
      inj' := by
        intro a b h
        have h' : g (s a) = g (s b) := (f.2 _ _).1 h
        simpa [hs a, hs b] using h' }
  let fromE : (Fin d ↪ Fin n) → Relabels (n:=n) g := fun e =>
    ⟨fun r => e (g r), by
      intro a b
      exact ⟨fun h => e.injective h,
        fun h => congrArg (fun z => e z) h⟩⟩
  refine { toFun := toE, invFun := fromE,
           left_inv := ?_, right_inv := ?_ }
  · intro f
    apply Subtype.ext
    funext r
    -- `g (s (g r)) = g r`; the backwards half of the pattern says that
    -- these two occurrences of a letter of the original word coincide.
    exact (f.2 _ _).2 (hs (g r))
  · intro e
    apply Function.Embedding.ext
    intro a
    exact congrArg (fun z => e z) (hs a)

lemma card_relabels {m d n : ℕ} (g : Fin m → Fin d)
    (hg : Function.Surjective g) :
    Fintype.card (Relabels (n:=n) g) = Nat.descFactorial n d := by
  classical
  rw [Fintype.card_congr (relabelsEquivEmbedding (n:=n) g hg)]
  simpa using (Fintype.card_embedding_eq (α:=Fin d) (β:=Fin n))

/-- Injective changes of alphabet preserve the finite image of a word.  This is
usually the easiest way to transport the root/vertex cardinality conditions
in a path enumeration. -/
lemma card_image_comp_injective
    {α β γ : Type*} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (g : α → β) (e : β → γ) (he : Function.Injective e) :
    (Finset.univ.image (fun x => e (g x))).card =
      (Finset.univ.image g).card := by
  classical
  -- image in two steps, followed by an injective image
  have h := Finset.card_image_of_injective
      (Finset.univ.image g) (f := e) he
  rw [Finset.image_image] at h
  exact h

/-- The image of a surjective word has precisely its alphabet size. -/
lemma card_image_of_surjective_fin {m d : ℕ} (g : Fin m → Fin d)
    (hg : Function.Surjective g) :
    (Finset.univ.image g).card = d := by
  classical
  have hall : Finset.univ.image g = (Finset.univ : Finset (Fin d)) := by
    ext a
    constructor
    · intro _; simp
    · intro _
      rcases hg a with ⟨b, rfl⟩
      simp
  simp [hall]

/-- A pointwise equality pattern is exactly what is needed to recover an
injective choice of labels; in particular every occurrence of the same
abstract vertex is assigned the same concrete vertex.  The following
`Fin.cons` version is handy for rooted paths. -/
lemma card_rooted_relabels {p d n : ℕ}
    (root : Fin d) (tail : Fin p → Fin d)
    (hg : Function.Surjective (@Fin.cons p (fun _ => Fin d) root tail)) :
    Fintype.card (Relabels (n:=n)
      (@Fin.cons p (fun _ => Fin d) root tail)) = Nat.descFactorial n d := by
  classical
  exact card_relabels _ hg

end WignerSupport

namespace WignerSupport
open scoped BigOperators

/-- `pathEnd` is the last entry of the cons word.  This innocuous convention is
particularly useful at `p=0`: the last entry is then the root. -/
lemma pathEnd_eq_cons_last {n p : ℕ} (i : Fin n) (v : Fin p → Fin n) :
    pathEnd p i v =
      (@Fin.cons p (fun _ => Fin n) i v (Fin.last p)) := by
  induction p generalizing i with
  | zero => rfl
  | succ p ih =>
    -- after the first edge the continuation has root `v 0`
    rw [pathEnd_succ]
    rw [ih (v 0) (Fin.tail v)]
    -- the last slot of a nonempty `cons` is a successor
    change (Fin.cons (v 0) (Fin.tail v) (Fin.last p)) = _
    simp

/-- Equality of upper-triangular natural edges remembers the two endpoints
(up to order).  Spelling it as a disjunction makes transport along injective
relabelings elementary and avoids any decidable ordering choices on an
abstract vertex type. -/
lemma edgeNat_eq_iff {a b c d : ℕ} :
    edgeNat a b = edgeNat c d ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have h1 : min a b = min c d := congrArg (fun z => z.val.1) h
    have h2 : max a b = max c d := congrArg (fun z => z.val.2) h
    rcases le_total a b with ab | ba <;>
      rcases le_total c d with cd | dc
    · left
      simpa [min_eq_left ab, max_eq_right ab,
        min_eq_left cd, max_eq_right cd] using And.intro h1 h2
    · right
      have h' : a = d ∧ b = c := by
        simpa [min_eq_left ab, max_eq_right ab,
          min_eq_right dc, max_eq_left dc] using And.intro h1 h2
      exact h'
    · right
      have h' : a = d ∧ b = c := by
        -- in this orientation `min a b = b` and `min c d = c`;
        -- `h1,h2` give `b=c,a=d`.
        have z : b = c ∧ a = d := by
          simpa [min_eq_right ba, max_eq_left ba,
            min_eq_left cd, max_eq_right cd] using And.intro h1 h2
        exact ⟨z.2, z.1⟩
      exact h'
    · left
      have z : b = d ∧ a = c := by
        simpa [min_eq_right ba, max_eq_left ba,
          min_eq_right dc, max_eq_left dc] using And.intro h1 h2
      exact ⟨z.2, z.1⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩; rfl
    · rcases h with ⟨rfl, rfl⟩; exact edgeNat_comm _ _

/-- Replacing all vertices of a rooted word by an injective map preserves
closedness.  No order is put on the new labels. -/
lemma pathEnd_map
    {p : ℕ} {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (g : α → β) (i : α) (v : Fin p → α) :
    pathEnd p (g i) (fun r => g (v r)) = g (pathEnd p i v) := by
  induction p generalizing i with
  | zero => rfl
  | succ p ih =>
      exact ih (v 0) (Fin.tail v)

/-- The set of natural vertex values in an injectively relabelled `Fin` path
has the same cardinality. -/
lemma card_vertices_map_embedding {d n p : ℕ} (e : Fin d ↪ Fin n)
    (i : Fin d) (v : Fin p → Fin d) :
    (pathVerticesFin (e i) (fun r => e (v r))).card =
      (pathVerticesFin i v).card := by
  classical
  rw [pathVertices_eq_image_cons, pathVertices_eq_image_cons]
  -- taking `val` after the embedding is still injective on the old image
  let w : Fin (p+1) → Fin d := @Fin.cons p (fun _ => Fin d) i v
  have hw : (@Fin.cons p (fun _ => Fin n) (e i) (fun r => e (v r))) =
      (fun r => e (w r)) := by
        funext r
        refine Fin.cases ?_ (fun t => ?_) r <;> simp [w]
  rw [hw]
  have comp1 :
      (fun r : Fin (p+1) => ((fun r => e (w r)) r).val) =
        (fun r => (fun a : Fin d => (e a).val) (w r)) := rfl
  -- `Fin.val` and `e` are injective
  have h1 := card_image_comp_injective w
      (fun a : Fin d => (e a).val)
      (fun a b h => e.injective (Fin.ext h))
  have h2 := card_image_comp_injective w
      (fun a : Fin d => a.val)
      (fun a b h => Fin.ext h)
  change
    (Finset.univ.image (fun r : Fin (p+1) => (e (w r)).val)).card =
      (Finset.univ.image (fun r : Fin (p+1) => (w r).val)).card
  exact h1.trans h2.symm

/-- The equality pattern of the unordered edge *list* is also unchanged by an
injective relabelling.  Notice that this is stronger than preserving just the
number of distinct edges: it is what is used for the `rep` test. -/
lemma pathEdgesNat_map_eq_iff {d n p : ℕ} (e : Fin d ↪ Fin n)
    (i : Fin d) (v : Fin p → Fin d) (r s : Fin p) :
    pathEdgesNat (e i) (fun t => e (v t)) r =
        pathEdgesNat (e i) (fun t => e (v t)) s ↔
      pathEdgesNat i v r = pathEdgesNat i v s := by
  -- it is convenient to follow the two oriented endpoints during the recursion
  -- rather than compare minima of the two orders.
  have orient {d n p : ℕ} (e : Fin d ↪ Fin n)
      (i : Fin d) (v : Fin p → Fin d) (t : Fin p) :
      ∃ a b : Fin d,
        pathEdgesNat i v t = edgeNat a.val b.val ∧
        pathEdgesNat (e i) (fun u => e (v u)) t =
          edgeNat (e a).val (e b).val := by
    induction p generalizing i with
    | zero => exact Fin.elim0 t
    | succ p ih =>
      refine Fin.cases ?_ (fun t' => ?_) t
      · exact ⟨i, v 0, rfl, rfl⟩
      · have ht : Fin.tail (fun u => e (v u)) =
              (fun u => e (Fin.tail v u)) := by
              funext u; rfl
        simpa [ht] using (ih (v 0) (Fin.tail v) t')
  rcases orient e i v r with ⟨a,b,hr,hr'⟩
  rcases orient e i v s with ⟨c,d,hs,hs'⟩
  -- equality of unordered pairs is the symmetric two-endpoint disjunction;
  -- injectivity cancels the relabelling in either branch.
  rw [hr, hr', hs, hs']
  constructor
  · intro h
    rcases (edgeNat_eq_iff.mp h) with h | h
    · have ac : a = c := e.injective (Fin.ext h.1)
      have bd : b = d := e.injective (Fin.ext h.2)
      subst c; subst d
      rfl
    · have ad : a = d := e.injective (Fin.ext h.1)
      have bc : b = c := e.injective (Fin.ext h.2)
      subst d; subst c
      exact edgeNat_comm _ _
  · intro h
    rcases (edgeNat_eq_iff.mp h) with h | h
    · rcases h with ⟨ha,hb⟩
      have ha' : a = c := Fin.ext ha
      have hb' : b = d := Fin.ext hb
      subst c; subst d
      rfl
    · rcases h with ⟨ha,hb⟩
      have ha' : a = d := Fin.ext ha
      have hb' : b = c := Fin.ext hb
      subst d; subst c
      exact edgeNat_comm _ _

/-- The `rep` predicate used to delete singleton edges is invariant under an
injective relabelling. -/
lemma repeatedEdges_map_iff {d n p : ℕ} (e : Fin d ↪ Fin n)
    (i : Fin d) (v : Fin p → Fin d) :
    ( (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
        pathEdgesNat (e i) (fun t => e (v t)) r =
          pathEdgesNat (e i) (fun t => e (v t)) u)) ↔
      (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
        pathEdgesNat i v r = pathEdgesNat i v u) := by
  constructor <;> intro h u
  · rcases h u with ⟨r, hr, eq⟩
    exact ⟨r, hr, (pathEdgesNat_map_eq_iff e i v r u).1 eq⟩
  · rcases h u with ⟨r, hr, eq⟩
    exact ⟨r, hr, (pathEdgesNat_map_eq_iff e i v r u).2 eq⟩

end WignerSupport
namespace WignerSupport

/-- Predicate left in the pruned sum at the top number of vertices.  Making it
a separate (finite, decidable) predicate is useful: it depends only on the
equality pattern of the vertex word, not on the actual natural labels. -/
def IsLeadingPath {n p : ℕ} (i : Fin n) (v : Fin p → Fin n) : Prop :=
  pathEnd p i v = i ∧
  (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
      pathEdgesNat i v r = pathEdgesNat i v u) ∧
  (pathVerticesFin i v).card = p/2 + 1

lemma isLeadingPath_map_iff {d n p : ℕ} (e : Fin d ↪ Fin n)
    (i : Fin d) (v : Fin p → Fin d) :
    IsLeadingPath (e i) (fun t => e (v t)) ↔ IsLeadingPath i v := by
  constructor
  · rintro ⟨close, rep, verts⟩
    refine ⟨?_, (repeatedEdges_map_iff e i v).1 rep, ?_⟩
    · rw [pathEnd_map] at close
      exact e.injective close
    · rw [card_vertices_map_embedding] at verts
      exact verts
  · rintro ⟨close, rep, verts⟩
    refine ⟨?_, (repeatedEdges_map_iff e i v).2 rep, ?_⟩
    · rw [pathEnd_map, close]
    · simpa [card_vertices_map_embedding]
        using verts

/-- The analogous statement with the vertex word rather than its `cons`
pair.  The transports `Fin.cons`/`Fin.tail` are kept in this file so later
finite counts need not repeatedly unfold a dependent equivalence. -/
def IsLeadingWord (p n : ℕ) (w : Fin (p+1) → Fin n) : Prop :=
  IsLeadingPath (w 0) (Fin.tail w)

lemma cons_tail_zero_eq {p : ℕ} {α : Type*} (w : Fin (p+1) → α) :
    @Fin.cons p (fun _ => α) (w 0) (Fin.tail w) = w := by
  funext r; exact Fin.cases rfl (fun t => rfl) r

lemma tail_comp_embedding {d n p : ℕ} (e : Fin d ↪ Fin n)
    (w : Fin (p+1) → Fin d) :
    Fin.tail (fun r => e (w r)) = (fun r => e (Fin.tail w r)) := by
  funext r; rfl

lemma isLeadingWord_map_iff {d n p : ℕ} (e : Fin d ↪ Fin n)
    (w : Fin (p+1) → Fin d) :
    IsLeadingWord p n (fun r => e (w r)) ↔ IsLeadingWord p d w := by
  unfold IsLeadingWord
  change IsLeadingPath (e (w 0)) (Fin.tail (fun r => e (w r))) ↔ _
  rw [tail_comp_embedding]
  exact isLeadingPath_map_iff e (w 0) (Fin.tail w)

/-- The vertices of a surjective word, regarded as a rooted path, really fill
its alphabet.  The statement uses `pathVerticesFin` (natural labels), hence
the small `Fin.val` image calculation. -/
lemma card_vertices_tail_of_surj {d p : ℕ}
    (w : Fin (p+1) → Fin d) (hw : Function.Surjective w) :
    (pathVerticesFin (w 0) (Fin.tail w)).card = d := by
  classical
  rw [pathVertices_eq_image_cons, cons_tail_zero_eq]
  -- as above, `val` is injective on a finite `Fin`
  calc
    (Finset.univ.image (fun r : Fin (p+1) => (w r).val)).card =
        (Finset.univ.image w).card :=
          card_image_comp_injective w (fun a : Fin d => a.val)
            (fun a b h => Fin.ext h)
    _ = d := card_image_of_surjective_fin w hw

noncomputable instance leadingRelabelFintype {p d n : ℕ}
    (w : Fin (p+1) → Fin d) :
    Fintype {f : Relabels (n:=n) w // IsLeadingWord p n f.val} := by
  classical
  let t : Finset (Relabels (n:=n) w) :=
    (Finset.univ).filter (fun f => IsLeadingWord p n f.val)
  exact Fintype.subtype t (by intro f; simp [t])

/-- A fixed surjective leading word has exactly `n.descFactorial d`
realisations with a specified equality pattern.  This deliberately stops
*before* counting the equality patterns themselves (the Catalan step); it is
often the convenient clean finite inner sum in the moment proof. -/
lemma card_relabels_leadingWord {p d n : ℕ}
    (w : Fin (p+1) → Fin d) (surj : Function.Surjective w)
    (lead : IsLeadingWord p d w) :
    Fintype.card {f : Relabels (n:=n) w // IsLeadingWord p n f.val}
       = Nat.descFactorial n d := by
  classical
  -- every relabelling is composition by a unique embedding
  let E := relabelsEquivEmbedding (n:=n) w surj
  have all (f : Relabels (n:=n) w) : IsLeadingWord p n f.val := by
    -- Expanding the inverse is simpler than choosing representatives in the
    -- property of a word.
    have hf : f = E.symm (E f) := (E.symm_apply_apply f).symm
    rw [hf]
    -- the inverse sends an embedding to its composition with `w`
    change IsLeadingWord p n (fun r => (E f) (w r))
    exact (isLeadingWord_map_iff (E f) w).2 lead

  -- the property imposes no further restriction on the relabellings
  calc
    Fintype.card {f : Relabels (n:=n) w // IsLeadingWord p n f.val} =
        Fintype.card (Relabels (n:=n) w) := by
          let proj : {f : Relabels (n:=n) w // IsLeadingWord p n f.val} ≃
              Relabels (n:=n) w :=
            { toFun := fun f => f.val
              invFun := fun f => ⟨f, all f⟩
              left_inv := by intro f; cases f; rfl
              right_inv := by intro f; rfl }
          exact Fintype.card_congr proj
    _ = Nat.descFactorial n d := card_relabels w surj

end WignerSupport
namespace WignerSupport
/-- At the top value of the vertex bound the number of distinct edges is
exactly `p/2`; the inequality in the other direction is just connectivity.
This innocuous strengthening is handy when all integrals in the leading sum
are being replaced by the *same* scalar. -/
lemma card_edges_eq_half_of_max_vertices {n p : ℕ}
    (i : Fin n) (v : Fin p → Fin n)
    (rep : ∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
       pathEdgesNat i v r = pathEdgesNat i v u)
    (hmax : (pathVerticesFin i v).card = p/2 + 1) :
    (Finset.univ.image (pathEdgesNat i v)).card = p/2 := by
  have hi := card_image_pathEdges_le_half i v rep
  have lo0 := card_pathVertices_le_edges_add_one i v
  have lo : p/2 ≤ (Finset.univ.image (pathEdgesNat i v)).card := by
    rw [hmax] at lo0
    omega
  exact Nat.le_antisymm hi lo
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Leading.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Tail.lean
section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter Function
namespace WignerSupport

/-- hard cutoff, the convenient first heavy-tail approximation -/
noncomputable def tailX {Ω : Type*} (R : ℝ) (X : ℕ → ℕ → Ω → ℝ) (i j : ℕ) (ω : Ω) : ℝ :=
  if R < |X i j ω| then X i j ω else 0
noncomputable def cutX {Ω : Type*} (R : ℝ) (X : ℕ → ℕ → Ω → ℝ) (i j : ℕ) (ω : Ω) : ℝ :=
  if R < |X i j ω| then 0 else X i j ω

lemma add_tail_cut {Ω} (R : ℝ) (X : ℕ → ℕ → Ω → ℝ) (i j : ℕ) (ω : Ω) :
  cutX R X i j ω + tailX R X i j ω = X i j ω := by
  unfold cutX tailX; split_ifs <;> ring

lemma tail_sq_le {Ω} (R : ℝ) (X : ℕ → ℕ → Ω → ℝ) (i j : ℕ) (ω : Ω) :
  (tailX R X i j ω)^2 ≤ (X i j ω)^2 := by
  unfold tailX; split_ifs <;> nlinarith [sq_nonneg (X i j ω)]

lemma measurable_tail_fun (R : ℝ) : Measurable (fun x : ℝ => (if R < |x| then x else 0)^2) := by
  have hs : MeasurableSet {x : ℝ | R < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  exact (Measurable.ite hs measurable_id measurable_const).pow_const _

noncomputable def tailMean {Ω} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → ℕ → Ω → ℝ) (R : ℝ) : ℝ :=
  ∫ ω, (tailX R X 0 0 ω)^2 ∂μ

lemma tailSqSeq_strongLaw {Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (R : ℝ)
    (h_indep : iIndepFun (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} => X ij.val.1 ij.val.2) μ)
    (h_meas : ∀ i j, Measurable (X i j))
    (h_iid : ∀ i j i' j', i ≤ j → i' ≤ j' → IdentDistrib (X i j) (X i' j') μ μ)
    (h_sq : ∀ i j, i ≤ j → Integrable (fun ω => (X i j ω)^2) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun m : ℕ => (∑ r ∈ Finset.range m,
          upperSqSeq (tailX R X) r ω) / (m:ℝ))
      atTop (𝓝 (tailMean μ X R)) := by
  let g : ℕ → {p : ℕ × ℕ // p.1 ≤ p.2} := upperEnum
  have hp : iIndepFun (fun r : ℕ =>
       (fun x : ℝ => (if R < |x| then x else 0)^2) ∘
        (X (g r).val.1 (g r).val.2)) μ :=
    ProbabilityTheory.iIndepFun.comp
      (ProbabilityTheory.iIndepFun.precomp upperEnum_injective h_indep) _
        (by intro i; exact measurable_tail_fun R)
  have heq : (fun r : ℕ =>
       (fun x : ℝ => (if R < |x| then x else 0)^2) ∘
        (X (g r).val.1 (g r).val.2)) = upperSqSeq (tailX R X) := by
    funext r ω
    rfl
  rw [heq] at hp
  have pair : Pairwise ((· ⟂ᵢ[μ] ·) on (upperSqSeq (tailX R X))) := by
    intro i j hij
    exact ProbabilityTheory.iIndepFun.indepFun hp hij
  have ident : ∀ r : ℕ, IdentDistrib (upperSqSeq (tailX R X) r)
          (upperSqSeq (tailX R X) 0) μ μ := by
    intro r
    have hi := h_iid r.unpair.1 (r.unpair.1 + r.unpair.2) 0 0 (Nat.le_add_right _ _) (by omega)
    have hc := hi.comp (measurable_tail_fun R)
    -- compositions
    have e1 : (upperSqSeq (tailX R X) r) =
        ((fun x : ℝ => (if R < |x| then x else 0)^2) ∘
          X r.unpair.1 (r.unpair.1+r.unpair.2)) := by
      funext ω
      by_cases z : R < |X r.unpair.1 (r.unpair.1+r.unpair.2) ω| <;>
        simp [upperSqSeq, tailX, Function.comp_def, z]
    have e0 : (upperSqSeq (tailX R X) 0) =
        ((fun x : ℝ => (if R < |x| then x else 0)^2) ∘ X 0 0) := by
      funext ω
      by_cases z : R < |X 0 0 ω| <;>
        simp [upperSqSeq, tailX, Function.comp_def, z]
    simpa [e1, e0] using hc
  have integ : Integrable (upperSqSeq (tailX R X) 0) μ := by
    have h0 := h_sq 0 0 (by omega)
    change Integrable (fun ω => ((if R < |X 0 0 ω| then X 0 0 ω else 0) ^ 2)) μ
    -- dominated by squares
    apply Integrable.mono' h0
    · exact (measurable_tail_fun R).aestronglyMeasurable.comp_measurable
          (h_meas 0 0)
    · filter_upwards [] with ω
      split_ifs <;> simp [sq_nonneg]
  have hs := ProbabilityTheory.strong_law_ae_real (upperSqSeq (tailX R X)) integ pair ident
  simpa [tailMean, upperSqSeq, tailX] using hs
end WignerSupport
namespace WignerSupport
lemma tailMean_tendsto_zero {Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (hm : Measurable (X 0 0)) (hi : Integrable (fun ω => (X 0 0 ω)^2) μ) :
    Tendsto (fun r : ℕ => tailMean μ X (r:ℝ)) atTop (𝓝 0) := by
  let F : ℕ → Ω → ℝ := fun n ω => (tailX (n:ℝ) X 0 0 ω)^2
  have hfm : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    exact (measurable_tail_fun n).aestronglyMeasurable.comp_measurable hm
  have hbd : ∀ n ω, ‖F n ω‖ ≤ (X 0 0 ω)^2 := by
    intro n ω
    have hz : 0 ≤ F n ω := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hz]
    exact tail_sq_le _ _ _ _ _
  have hlim : ∀ ω, Tendsto (fun n => F n ω) atTop (𝓝 (0:ℝ)) := by
    intro ω
    have ev : ∀ᶠ n : ℕ in atTop, F n ω = 0 := by
      have ev' : ∀ᶠ n : ℕ in atTop, |X 0 0 ω| ≤ (n : ℝ) :=
        (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |X 0 0 ω|))
      filter_upwards [ev'] with n hn
      have hn' : ¬ (n:ℝ) < |X 0 0 ω| := not_lt_of_ge hn
      simp [F, tailX, hn']
    exact (tendsto_congr' ev).2 (tendsto_const_nhds)
  have ht := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := atTop) (F := F) (f := fun _ : Ω => (0:ℝ))
      (fun ω => (X 0 0 ω)^2)
      (Filter.Eventually.of_forall hfm)
      (Filter.Eventually.of_forall (fun n =>
          ae_of_all _ (hbd n))) hi (ae_of_all _ hlim)
  simpa [tailMean, F, tailX] using ht
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Tail.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/WalkMean.lean
section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport

section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Regroup the product in a real path by its unordered edges. This deterministic
identity is the bridge from the path notation to finite independent products. -/
lemma pathTerm_eq_prod_edges
    (Y : ℕ → ℕ → Ω → ℝ) (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
    (ω : Ω) :
    pathTerm (fun a b : Fin n =>
        Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v =
      ∏ e ∈ (Finset.univ.image (pathEdgesNat i v)),
        (Y e.val.1 e.val.2 ω) ^
          ((Finset.univ : Finset (Fin p)).filter
              (fun r => pathEdgesNat i v r = e)).card := by
  classical
  rw [pathTerm_real_wigner Y ω n p i v]
  -- use the fiberwise product identity for the map from steps to edges
  let s : Finset (Fin p) := Finset.univ
  let f := pathEdgesNat i v
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} := s.image f
  have hmaps : ∀ r ∈ s, f r ∈ E := fun r hr => Finset.mem_image.mpr ⟨r, hr, rfl⟩
  have grp := Finset.prod_fiberwise_of_maps_to'
        (s := s) (t := E) hmaps
        (f := fun e : {z : ℕ × ℕ // z.1 ≤ z.2} =>
          Y e.val.1 e.val.2 ω)
  -- each fiber is a product of a constant
  -- spell out the two abbreviations only at the last line
  classical
  simpa [s, f, E, Finset.prod_const] using grp.symm

/-- Independence on upper-triangular entries factors the expectation of a path
as a product of one-dimensional moments, one for each *distinct* edge.  The
multiplicity in the exponent is the size of the edge's fiber.  No centeredness
is needed here; singleton fibers are dealt with separately in `Walk`. -/
lemma integral_pathTerm_eq_prod_edges
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
      (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (n p : ℕ) (i : Fin n) (v : Fin p → Fin n) :
    (∫ ω, pathTerm (fun a b : Fin n =>
          Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v ∂μ) =
      ∏ e ∈ (Finset.univ.image (pathEdgesNat i v)),
        (∫ ω, (Y e.val.1 e.val.2 ω) ^
          ((Finset.univ : Finset (Fin p)).filter
            (fun r => pathEdgesNat i v r = e)).card ∂μ) := by
  classical
  let f := pathEdgesNat i v
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
    (Finset.univ : Finset (Fin p)).image f
  let m : {z : ℕ × ℕ // z.1 ≤ z.2} → ℕ := fun e =>
    ((Finset.univ : Finset (Fin p)).filter (fun r => f r = e)).card
  -- the distinct coordinates are indexed by the subtype of the finite image
  let Z : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ E} → Ω → ℝ :=
    fun e ω => (Y e.val.val.1 e.val.val.2 ω) ^ m e.val
  have pre : iIndepFun
      (fun e : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ E} =>
        Y e.val.val.1 e.val.val.2) μ :=
    ProbabilityTheory.iIndepFun.precomp (fun e₁ e₂ h => Subtype.ext h) hi
  have hZ : iIndepFun Z μ := by
    exact ProbabilityTheory.iIndepFun.comp pre
      (fun e (x : ℝ) => x ^ m e.val) (by intro e; fun_prop)
  have mZ : ∀ e, AEStronglyMeasurable (Z e) μ := by
    intro e
    exact (by fun_prop : Measurable (Z e)).aestronglyMeasurable
  have fact := ProbabilityTheory.iIndepFun.integral_fun_prod_eq_prod_integral
        hZ mZ
  have point (ω : Ω) :
      pathTerm (fun a b : Fin n =>
          Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v =
        ∏ e : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ E}, Z e ω := by
    rw [pathTerm_eq_prod_edges Y n p i v ω]
    -- product over a subtype is the same product over the attached finset
    change (∏ e ∈ E, (Y e.val.1 e.val.2 ω) ^ m e) =
      ∏ e : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ E},
        (Y e.val.val.1 e.val.val.2 ω) ^ m e.val
    -- the `Fintype` instance for this subtype is its attached finset
    change (∏ e ∈ E, (Y e.val.1 e.val.2 ω) ^ m e) =
      ∏ e ∈ E.attach, (Y e.val.val.1 e.val.val.2 ω) ^ m e.val
    exact (Finset.prod_attach E
      (fun e => (Y e.val.1 e.val.2 ω) ^ m e)).symm
  calc
    (∫ ω, pathTerm (fun a b : Fin n =>
          Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v ∂μ) =
        ∫ ω, ∏ e : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ E}, Z e ω ∂μ := by
          congr 1
          funext ω
          exact point ω
    _ = ∏ e : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ E},
          (∫ ω, Z e ω ∂μ) := fact
    _ = ∏ e ∈ (Finset.univ.image (pathEdgesNat i v)),
        (∫ ω, (Y e.val.1 e.val.2 ω) ^
          ((Finset.univ : Finset (Fin p)).filter
            (fun r => pathEdgesNat i v r = e)).card ∂μ) := by
          change
            (∏ e ∈ E.attach,
              (∫ ω, (Y e.val.val.1 e.val.val.2 ω) ^ m e.val ∂μ)) =
              ∏ e ∈ E, (∫ ω, (Y e.val.1 e.val.2 ω) ^ m e ∂μ)
          exact Finset.prod_attach E
             (fun e => (∫ ω, (Y e.val.1 e.val.2 ω) ^ m e ∂μ))

/-- In the extremal case where every unordered edge of a path occurs exactly
twice, all factors in the preceding product are second moments.  For the
centered cut, these moments are the common variance. -/
lemma integral_pathTerm_of_fiber_two
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
      (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (σ : ℝ)
    (hvar : ∀ a b, a ≤ b → (∫ ω, (Y a b ω)^2 ∂μ) = σ)
    (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
    (htwo : ∀ e ∈ (Finset.univ.image (pathEdgesNat i v)),
        ((Finset.univ : Finset (Fin p)).filter
           (fun r => pathEdgesNat i v r = e)).card = 2) :
    (∫ ω, pathTerm (fun a b : Fin n =>
          Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v ∂μ) =
       σ ^ (Finset.univ.image (pathEdgesNat i v)).card := by
  classical
  rw [integral_pathTerm_eq_prod_edges μ Y hm hi n p i v]
  -- all edge factors are the same;
  -- using `prod_congr` keeps the membership proof for `htwo` explicit.
  calc
    (∏ e ∈ Finset.univ.image (pathEdgesNat i v),
        (∫ ω, (Y e.val.1 e.val.2 ω) ^
          ((Finset.univ : Finset (Fin p)).filter
            (fun r => pathEdgesNat i v r = e)).card ∂μ)) =
      ∏ _e ∈ Finset.univ.image (pathEdgesNat i v), σ := by
        apply Finset.prod_congr rfl
        intro e he
        rw [htwo e he]
        exact hvar _ _ e.property
    _ = σ ^ (Finset.univ.image (pathEdgesNat i v)).card := by simp

end
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/WalkMean.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Cut.lean
section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport
/-- scalar hard cut used in `cutX` -/
noncomputable def cut (R : ℝ) (x : ℝ) : ℝ := if R < |x| then 0 else x
lemma cut_measurable (R : ℝ) : Measurable (cut R) := by
  unfold cut
  have hs : MeasurableSet {x : ℝ | R < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  exact Measurable.ite hs measurable_const measurable_id
lemma cut_bound {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |cut R x| ≤ R := by
  unfold cut
  split_ifs with h
  · simpa using hR
  · exact le_of_not_gt h
lemma cutX_comp {Ω} (R : ℝ) (Y : ℕ → ℕ → Ω → ℝ) (i j : ℕ) :
    cutX R Y i j = cut R ∘ Y i j := by
  funext ω; rfl
lemma cutX_measurable {Ω} [MeasurableSpace Ω]
    (R : ℝ) (Y : ℕ → ℕ → Ω → ℝ)
    (hy : ∀ i j, Measurable (Y i j)) (i j : ℕ) :
    Measurable (cutX R Y i j) := by
  rw [cutX_comp]
  exact (cut_measurable R).comp (hy i j)
lemma cutX_bound {Ω} {R : ℝ} (hR : 0 ≤ R)
    (Y : ℕ → ℕ → Ω → ℝ) (i j : ℕ) (ω : Ω) :
    |cutX R Y i j ω| ≤ R := by
  rw [cutX_comp]
  exact cut_bound hR _
/-- Every (fixed) moment of the hard truncation is integrable.  This is the
basic input for the elementary moment method; it uses only that our ambient
measure is finite, not a moment of the untruncated entries. -/
lemma cutX_pow_integrable {Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (R : ℝ) (hR : 0 ≤ R)
    (Y : ℕ → ℕ → Ω → ℝ) (hy : ∀ i j, Measurable (Y i j))
    (i j m : ℕ) : Integrable (fun ω => (cutX R Y i j ω)^m) μ := by
  have meas : Measurable (fun ω => (cutX R Y i j ω)^m) :=
    (cutX_measurable R Y hy i j).pow_const _
  refine Integrable.of_bound meas.aestronglyMeasurable (R^m) ?_
  filter_upwards [] with ω
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (cutX_bound hR Y i j ω) _
lemma cutX_indep {Ω} [MeasurableSpace Ω] (μ : Measure Ω) (R : ℝ)
    (Y : ℕ → ℕ → Ω → ℝ)
    (h : iIndepFun (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} =>
            Y ij.val.1 ij.val.2) μ) :
    iIndepFun (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} =>
            cutX R Y ij.val.1 ij.val.2) μ := by
  have q := ProbabilityTheory.iIndepFun.comp h
      (fun _ : {p : ℕ × ℕ // p.1 ≤ p.2} => cut R)
      (by intro i; exact cut_measurable R)
  simpa [cutX_comp, Function.comp_def, cutX, cut] using q
lemma cutX_ident {Ω} [MeasurableSpace Ω] (μ : Measure Ω) (R : ℝ)
    (Y : ℕ → ℕ → Ω → ℝ)
    (h : ∀ i j i' j', i ≤ j → i' ≤ j' →
      IdentDistrib (Y i j) (Y i' j') μ μ) :
    ∀ i j i' j', i ≤ j → i' ≤ j' →
      IdentDistrib (cutX R Y i j) (cutX R Y i' j') μ μ := by
  intro i j a b hij hab
  have z := (h i j a b hij hab).comp (cut_measurable R)
  simpa [cutX_comp, Function.comp_def, cutX, cut] using z
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Cut.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PathCard.lean
section

/-!
Small purely finite facts used in the bounded moment argument.  A labelled walk is a
map on `Fin (p+1)`; if it uses at most `d` labels it factors through `Fin d`.
It is tempting to replace this observation by the very crude bound
`n^(p+1)`, but that loses the power of `n` in the discarded (non-leading)
walks.  The statement below keeps all degeneracies (`d = 0`, `n = 0`)
honest.
-/
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport

/-- Factorisation of a list of labels with small range.  The hypothesis `m>0`
just supplies a dummy value to fill the coordinates of `Fin d` that the range
does not use.  No choices of an ordering of the labels go into the statement;
in the proof we may of course use `s.equivFin` for the finite image. -/
lemma factor_through_fin_of_card_image_le
    {m n d : ℕ} (hm : 0 < m) (g : Fin m → Fin n)
    (h : (Finset.univ.image g).card ≤ d) :
    ∃ k : Fin d → Fin n, ∃ l : Fin m → Fin d, ∀ r, k (l r) = g r := by
  classical
  let S : Finset (Fin n) := Finset.univ.image g
  have memg (r : Fin m) : g r ∈ S :=
    Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  -- Enumerate the finite range, and then include this enumeration into `Fin d`.
  let e : ({x // x ∈ S}) ≃ Fin S.card := S.equivFin
  let incl : Fin S.card → Fin d := fun a => Fin.castLE h a
  let l : Fin m → Fin d := fun r => incl (e ⟨g r, memg r⟩)
  -- Values of the putative inverse away from the range of `l` are irrelevant.
  let r₀ : Fin m := ⟨0, hm⟩
  let k : Fin d → Fin n := fun a =>
    if ha : a.val < S.card then
      ((e.symm ⟨a.val, ha⟩ : {x // x ∈ S}) : Fin n)
    else g r₀
  refine ⟨k, l, ?_⟩
  intro r
  have ha : (l r).val < S.card := by
    dsimp [l, incl]
    exact (e ⟨g r, memg r⟩).isLt
  dsimp [k]
  rw [dif_pos ha]
  -- `Fin.castLE` has the same value field, so the two `Fin S.card` below
  -- are judgmentally the same after `Fin.ext`.
  have hv : (⟨(l r).val, ha⟩ : Fin S.card) = e ⟨g r, memg r⟩ := by
    apply Fin.ext
    rfl
  rw [hv]
  simp

/-- There are at most `n^d d^m` words of length `m>0` on `n` letters that
use at most `d` different letters.

The proof uses *all* pairs `(k,l)` with `g = k ∘ l`; this deliberate
over-counting is useful.  It avoids Stirling numbers/partitions and is just
as sharp a power estimate in `n`. -/
lemma card_small_image_fun
    {m n d : ℕ} (hm : 0 < m) :
    Fintype.card
      {g : Fin m → Fin n // (Finset.univ.image g).card ≤ d} ≤
      n^d * d^m := by
  classical
  let G := {g : Fin m → Fin n // (Finset.univ.image g).card ≤ d}
  have fac (g : G) :
      ∃ kl : (Fin d → Fin n) × (Fin m → Fin d),
        ∀ r, kl.1 (kl.2 r) = g.val r := by
    rcases factor_through_fin_of_card_image_le hm g.val g.property with
      ⟨k,l,hl⟩
    exact ⟨(k,l), hl⟩
  choose t ht using fac
  have tinj : Function.Injective t := by
    intro a b hab
    apply Subtype.ext
    apply funext
    intro r
    calc
      a.val r = (t a).1 ((t a).2 r) := (ht a r).symm
      _ = (t b).1 ((t b).2 r) := by rw [hab]
      _ = b.val r := ht b r
  have first : Fintype.card G ≤
      Fintype.card ((Fin d → Fin n) × (Fin m → Fin d)) :=
    Fintype.card_le_of_injective t tinj
  have cprod : Fintype.card ((Fin d → Fin n) × (Fin m → Fin d)) =
      n^d * d^m := by
    simp [Fintype.card_prod, Fintype.card_fun]
  -- make the abbreviation `G` transparent in the result
  change Fintype.card G ≤ n^d * d^m
  simpa [cprod] using (first.trans_eq cprod)

-- The above last line is sometimes less pleasant to rewrite than a direct
-- `rw`; keep the following walk-specific corollary to insulate the counting
-- argument below from the chosen Fintype instance on a subtype.
/-- A rooted `p`-step walk with at most `d` labels satisfies the same bound.
The root and the tail are paired using `Fin.consEquiv`; hence `p+1`, not
`p`, is the word length. -/
lemma card_small_path_vertices {n p d : ℕ} :
    Fintype.card
      {z : (Fin n) × (Fin p → Fin n) //
        (pathVerticesFin z.1 z.2).card ≤ d} ≤
      n^d * d^(p+1) := by
  classical
  let H := {z : (Fin n) × (Fin p → Fin n) //
        (pathVerticesFin z.1 z.2).card ≤ d}
  let K := {g : (Fin (p+1) → Fin n) //
        (Finset.univ.image g).card ≤ d}
  let ce : (Fin n × (Fin p → Fin n)) ≃ (Fin (p+1) → Fin n) :=
    Fin.consEquiv (fun _ : Fin (p+1) => Fin n)
  let toK : H → K := fun z =>
    ⟨ce z.val, by
      -- Taking `val : Fin n → ℕ` does not change a finite image's card.
      have cv (g : Fin (p+1) → Fin n) :
          (Finset.univ.image g).card =
            (Finset.univ.image (fun r => (g r).val)).card := by
        -- compute the latter as the image under the injective `Fin.val`
        have hval := Finset.card_image_of_injective
          (Finset.univ.image g) (f := fun a : Fin n => a.val)
          (fun a b e => Fin.ext e)
        rw [Finset.image_image] at hval
        exact hval.symm
      rw [cv]
      change (Finset.univ.image
            (fun r => (@Fin.cons p (fun _ => Fin n) z.val.1 z.val.2 r).val)).card ≤ d
      rw [← pathVertices_eq_image_cons]
      exact z.property⟩
  have inj : Function.Injective toK := by
    intro a b hab
    have valh : ce a.val = ce b.val := congrArg Subtype.val hab
    have ab : a.val = b.val := ce.injective valh
    exact Subtype.ext ab
  have first : Fintype.card H ≤ Fintype.card K :=
    Fintype.card_le_of_injective toK inj
  have second : Fintype.card K ≤ n^d * d^(p+1) := by
    change Fintype.card
      {g : Fin (p+1) → Fin n // (Finset.univ.image g).card ≤ d} ≤ _
    exact card_small_image_fun (Nat.zero_lt_succ p)
  exact first.trans second

/-- Same inequality in the shape in which a double `Finset.sum` is normally
used. -/
lemma card_filter_small_path_vertices {n p d : ℕ} :
    ((Finset.univ : Finset (Fin n × (Fin p → Fin n))).filter
      (fun z => (pathVerticesFin z.1 z.2).card ≤ d)).card ≤
      n^d * d^(p+1) := by
  classical
  have h := card_small_path_vertices (n:=n) (p:=p) (d:=d)
  simpa only [Fintype.card_subtype] using h

/-- Pointwise bound on an expected walk.  The preceding files record
integrability separately; for probability measure `μ` the integral loses no
constant at all.  Keeping this elementary inequality in real absolute value
saves conversions between `ℂ` and `ℝ` in the trace estimates. -/
lemma abs_integral_pathTerm_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ a b ω, |Y a b ω| ≤ B)
    (n p : ℕ) (i : Fin n) (v : Fin p → Fin n) :
    |(∫ w, pathTerm (fun a b : Fin n =>
          Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)| ≤ B^p := by
  classical
  have point : ∀ w,
      ‖pathTerm (fun a b : Fin n =>
          Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v‖ ≤ B^p := by
    intro w
    rw [pathTerm_real_wigner Y w n p i v, Real.norm_eq_abs, Finset.abs_prod]
    calc
      (∏ r : Fin p, |Y (pathEdgesNat i v r).val.1
          (pathEdgesNat i v r).val.2 w|) ≤
          ∏ _r : Fin p, B := by
            exact Finset.prod_le_prod (fun r hr => abs_nonneg _)
              (fun r hr => hb _ _ _)
      _ = B^p := by simp
  have ineq := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ:=μ)
      (f:= fun w => pathTerm (fun a b : Fin n =>
          Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v)
      (C:=B^p)
      (ae_of_all _ point)
  -- `μ.real univ = 1` for a probability measure.
  simpa [Real.norm_eq_abs] using ineq

end WignerSupport

namespace WignerSupport
open Filter
/-- Losing one label in a rooted count is enough: after the usual normalization
the discarded part tends to zero.  This lemma is deliberately stated for
`k+1`; the `0`th matrix need not be divided by anything. -/
lemma tendsto_error_of_card_power
    (a : ℕ) (K : ℝ) (hK : 0 ≤ K) (e : ℕ → ℝ)
    (he : ∀ n, n ≠ 0 → |e n| ≤ (n:ℝ)^a * K) :
    Tendsto (fun k : ℕ => e (k+1) / (((k+1:ℕ):ℝ)^(a+1))) atTop (𝓝 0) := by
  have hi (k : ℕ) : (0:ℝ) < ((k+1:ℕ):ℝ) := by exact_mod_cast Nat.zero_lt_succ k
  have maj (k : ℕ) :
      |e (k+1) / (((k+1:ℕ):ℝ)^(a+1))| ≤ K / (((k:ℝ)+1)) := by
    have hp : (0:ℝ) < (((k+1:ℕ):ℝ)^(a+1)) := pow_pos (hi k) _
    rw [abs_div, abs_of_pos hp]
    calc
      |e (k+1)| / (((k+1:ℕ):ℝ)^(a+1)) ≤
          ((((k+1:ℕ):ℝ)^a) * K) / (((k+1:ℕ):ℝ)^(a+1)) := by
            apply div_le_div_of_nonneg_right (he _ (by omega)) (le_of_lt hp)
      _ = K / ((k:ℝ)+1) := by
            have hn : ((k:ℝ)+1) ≠ 0 := by positivity
            push_cast
            field_simp
            <;> ring
  have lim : Tendsto (fun k : ℕ => K / ((k:ℝ)+1)) atTop (𝓝 0) := by
    convert Filter.Tendsto.const_mul K
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)) using 1
    · funext k; ring
    · simp
  have ab : Tendsto
      (fun k : ℕ => |e (k+1) / (((k+1:ℕ):ℝ)^(a+1))|)
      atTop (𝓝 0) := by
    exact squeeze_zero (fun _ => abs_nonneg _) maj lim
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  simpa only [Real.norm_eq_abs] using ab
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PathCard.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Patterns.lean
section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The multiplicities of a word do not require its alphabet to be used
surjectively.  Only its finite image is relevant for relabelling. -/
lemma card_relabels_image {m d n : ℕ} (g : Fin m → Fin d) :
    Fintype.card (Relabels (n:=n) g) =
      Nat.descFactorial n ((Finset.univ.image g).card) := by
  classical
  let S : Finset (Fin d) := Finset.univ.image g
  let gs : Fin m → {a // a ∈ S} := fun r => ⟨g r, by
    dsimp [S]; simp⟩
  have gs_surj : Function.Surjective gs := by
    intro a
    rcases a with ⟨a, ha⟩
    rcases Finset.mem_image.mp ha with ⟨r, hr, eq⟩
    subst a
    exact ⟨r, rfl⟩
  -- just as in `relabelsEquivEmbedding`, a relabelling is an embedding on
  -- the actually used alphabet.  Using the subtype also handles `d>m`.
  choose s hs using gs_surj
  let toE : Relabels (n:=n) g → ({a // a ∈ S} ↪ Fin n) := fun f =>
    { toFun := fun a => f.val (s a)
      inj' := by
        intro a b h
        have h' : g (s a) = g (s b) := (f.property _ _).1 h
        have hsub : gs (s a) = gs (s b) := Subtype.ext h'
        exact (hs a) ▸ (hs b) ▸ hsub }
  let fromE : ({a // a ∈ S} ↪ Fin n) → Relabels (n:=n) g := fun e =>
    ⟨fun r => e (gs r), by
      intro a b
      constructor
      · intro h
        have hh : gs a = gs b := e.injective h
        exact congrArg Subtype.val hh
      · intro h
        have hh : gs a = gs b := by
          apply Subtype.ext
          simpa [gs] using h
        exact congrArg (fun z => e z) hh⟩
  let E : Relabels (n:=n) g ≃ ({a // a ∈ S} ↪ Fin n) :=
    { toFun := toE
      invFun := fromE
      left_inv := by
        intro f
        apply Subtype.ext
        funext r
        change f.val (s (gs r)) = f.val r
        apply (f.property _ _).2
        have e : gs (s (gs r)) = gs r := hs (gs r)
        exact congrArg Subtype.val e
      right_inv := by
        intro e
        apply Function.Embedding.ext
        intro a
        change e (gs (s a)) = e a
        exact congrArg (fun z => e z) (hs a) }
  rw [Fintype.card_congr E, Fintype.card_embedding_eq,
      Fintype.card_fin, Fintype.card_coe]

/-- An edge in a word is carried by the two consecutive letters. -/
lemma pathEdges_word {n p : ℕ} (w : Fin (p+1) → Fin n) (r : Fin p) :
    pathEdgesNat (w 0) (Fin.tail w) r =
      edgeNat (w r.castSucc).val (w r.succ).val := by
  induction p with
  | zero => exact Fin.elim0 r
  | succ p ih =>
    refine Fin.cases ?_ (fun r' => ?_) r
    · rfl
    · -- throw away the first letter; both indices are successors
      have ih' := ih (Fin.tail w) r'
      change pathEdgesNat (Fin.tail w 0) (Fin.tail (Fin.tail w)) r' = _
      rw [ih']
      rfl

/-- `pathVerticesFin` is the finite image of the vertex word (the cast to naturals
in the definition does not change its cardinality). -/
lemma card_vertices_word {n p : ℕ} (w : Fin (p+1) → Fin n) :
    (pathVerticesFin (w 0) (Fin.tail w)).card =
      (Finset.univ.image w).card := by
  classical
  rw [pathVertices_eq_image_cons, cons_tail_zero_eq]
  -- taking values of a `Fin` is injective
  exact card_image_comp_injective w (fun a : Fin n => a.val)
      (fun a b h => Fin.ext h)

/-- Equality pattern of a word. A Boolean matrix is a convenient finite type for
patterns and avoids quotients by the alphabet permutation action. -/
def wordPattern {m n : ℕ} (w : Fin m → Fin n) : Fin m → Fin m → Bool :=
  fun a b => decide (w a = w b)

lemma wordPattern_eq_iff {m n d : ℕ}
    (f : Fin m → Fin n) (g : Fin m → Fin d) :
    wordPattern f = wordPattern g ↔
      ∀ a b, f a = f b ↔ g a = g b := by
  classical
  constructor
  · intro he a b
    have h := congrFun (congrFun he a) b
    simpa [wordPattern] using h
  · intro h
    funext a b
    -- Booleans remember just the truth value
    simpa [wordPattern, propext (h a b)]

/-- Any two words with the same equality pattern have the same number of
letters in their image. -/
lemma card_image_eq_of_pattern {m n d : ℕ}
    (f : Fin m → Fin n) (g : Fin m → Fin d)
    (h : ∀ a b, f a = f b ↔ g a = g b) :
    (Finset.univ.image f).card = (Finset.univ.image g).card := by
  classical
  let A : Finset (Fin n) := Finset.univ.image f
  let B : Finset (Fin d) := Finset.univ.image g
  -- choose an occurrence for each letter of `f`
  have hf (x : {x // x ∈ A}) : ∃ r : Fin m, f r = x.val := by
    rcases Finset.mem_image.mp x.property with ⟨r, -, e⟩
    exact ⟨r, e⟩
  choose sf hsf using hf
  let F : {x // x ∈ A} → {y // y ∈ B} := fun x =>
    ⟨g (sf x), by
      dsimp [B]
      exact Finset.mem_image.mpr ⟨sf x, Finset.mem_univ _, rfl⟩⟩
  have iF : Function.Injective F := by
    intro x y e
    have ee : g (sf x) = g (sf y) := congrArg Subtype.val e
    have ff : f (sf x) = f (sf y) := (h _ _).2 ee
    apply Subtype.ext
    -- use the chosen occurrence equations
    simpa [hsf x, hsf y] using ff
  have le : A.card ≤ B.card := by
    have c := Fintype.card_le_of_injective F iF
    simpa only [Fintype.card_coe] using c
  -- and the reverse inequality
  have hg (x : {x // x ∈ B}) : ∃ r : Fin m, g r = x.val := by
    rcases Finset.mem_image.mp x.property with ⟨r, -, e⟩
    exact ⟨r, e⟩
  choose sg hsg using hg
  let G : {x // x ∈ B} → {y // y ∈ A} := fun x =>
    ⟨f (sg x), by
      dsimp [A]
      exact Finset.mem_image.mpr ⟨sg x, Finset.mem_univ _, rfl⟩⟩
  have iG : Function.Injective G := by
    intro x y e
    have ee : f (sg x) = f (sg y) := congrArg Subtype.val e
    have gg : g (sg x) = g (sg y) := (h _ _).1 ee
    apply Subtype.ext
    simpa [hsg x, hsg y] using gg
  have ge : B.card ≤ A.card := by
    have c := Fintype.card_le_of_injective G iG
    simpa only [Fintype.card_coe] using c
  exact Nat.le_antisymm le ge

/-- Closedness, repetitions and the maximal-cardinality test all depend only on
the equality pattern of the vertex word, and not on the numeric names given to
its letters. -/
lemma isLeadingWord_congr_pattern {p n d : ℕ}
    (f : Fin (p+1) → Fin n) (g : Fin (p+1) → Fin d)
    (h : ∀ a b, f a = f b ↔ g a = g b) :
    IsLeadingWord p n f ↔ IsLeadingWord p d g := by
  classical
  -- equality of two consecutive unordered pairs follows from `h` (or its
  -- converse). This is the only place where edges rather than vertices enter.
  have edgeeq (r s : Fin p) :
      pathEdgesNat (f 0) (Fin.tail f) r =
          pathEdgesNat (f 0) (Fin.tail f) s ↔
        pathEdgesNat (g 0) (Fin.tail g) r =
          pathEdgesNat (g 0) (Fin.tail g) s := by
    rw [pathEdges_word f r, pathEdges_word f s,
        pathEdges_word g r, pathEdges_word g s]
    rw [edgeNat_eq_iff, edgeNat_eq_iff]
    constructor
    · intro hh
      rcases hh with hh | hh
      · left
        exact ⟨congrArg Fin.val ((h _ _).1 (Fin.ext hh.1)),
          congrArg Fin.val ((h _ _).1 (Fin.ext hh.2))⟩
      · right
        exact ⟨congrArg Fin.val ((h _ _).1 (Fin.ext hh.1)),
          congrArg Fin.val ((h _ _).1 (Fin.ext hh.2))⟩
    · intro hh
      rcases hh with hh | hh
      · left
        exact ⟨congrArg Fin.val ((h _ _).2 (Fin.ext hh.1)),
          congrArg Fin.val ((h _ _).2 (Fin.ext hh.2))⟩
      · right
        exact ⟨congrArg Fin.val ((h _ _).2 (Fin.ext hh.1)),
          congrArg Fin.val ((h _ _).2 (Fin.ext hh.2))⟩
  unfold IsLeadingWord IsLeadingPath
  have endf : pathEnd p (f 0) (Fin.tail f) = f (Fin.last p) :=
    pathEnd_eq_cons_last (f 0) (Fin.tail f) |>.trans
      (congrFun (cons_tail_zero_eq f) (Fin.last p))
  have endg : pathEnd p (g 0) (Fin.tail g) = g (Fin.last p) :=
    pathEnd_eq_cons_last (g 0) (Fin.tail g) |>.trans
      (congrFun (cons_tail_zero_eq g) (Fin.last p))
  have verts :
      (pathVerticesFin (f 0) (Fin.tail f)).card =
        (pathVerticesFin (g 0) (Fin.tail g)).card := by
    rw [card_vertices_word, card_vertices_word]
    exact card_image_eq_of_pattern f g h
  constructor
  · rintro ⟨hc, hr, hm⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [endf] at hc
      rw [endg]
      exact (h _ _).1 hc
    · intro u
      rcases hr u with ⟨r, ne, eq⟩
      exact ⟨r, ne, (edgeeq r u).1 eq⟩
    · rw [← verts]
      exact hm
  · rintro ⟨hc, hr, hm⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [endg] at hc
      rw [endf]
      exact (h _ _).2 hc
    · intro u
      rcases hr u with ⟨r, ne, eq⟩
      exact ⟨r, ne, (edgeeq r u).2 eq⟩
    · rw [verts]
      exact hm

/-- Replace each letter by a chosen occurrence in the word. This realizes an
equality pattern on its own position set, hence on the universal alphabet
`Fin m`. -/
noncomputable def canonicalWord {m n : ℕ} (w : Fin m → Fin n) : Fin m → Fin m :=
  fun a => Classical.choose (show ∃ b : Fin m, w b = w a from ⟨a, rfl⟩)

lemma canonicalWord_spec {m n : ℕ} (w : Fin m → Fin n) (a : Fin m) :
    w (canonicalWord w a) = w a := by
  classical
  exact Classical.choose_spec (show ∃ b : Fin m, w b = w a from ⟨a, rfl⟩)

lemma canonicalWord_pattern {m n : ℕ} (w : Fin m → Fin n) :
    ∀ a b, w a = w b ↔ canonicalWord w a = canonicalWord w b := by
  classical
  intro a b
  constructor
  · intro e
    -- `choose` applied to identical fibers is definitionally equal after rewriting
    dsimp [canonicalWord]
    congr 1
    funext x
    apply propext
    constructor
    · intro hx; exact hx.trans e
    · intro hx; exact hx.trans e.symm
  · intro e
    have a' := canonicalWord_spec w a
    have b' := canonicalWord_spec w b
    rw [← a', ← b']
    exact congrArg (fun z => w z) e

/-- The finite set of equality patterns of leading words of length `p`. It is
independent of the ambient label set. -/
noncomputable def leadPatterns (p : ℕ) : Finset (Fin (p+1) → Fin (p+1) → Bool) :=
  ((Finset.univ : Finset (Fin (p+1) → Fin (p+1))).filter
      (fun w => IsLeadingWord p (p+1) w)).image wordPattern

lemma wordPattern_mem_of_leading {p n : ℕ} (w : Fin (p+1) → Fin n)
    (hw : IsLeadingWord p n w) : wordPattern w ∈ leadPatterns p := by
  classical
  let t : Fin (p+1) → Fin (p+1) := canonicalWord w
  have htpat : ∀ a b, w a = w b ↔ t a = t b := canonicalWord_pattern w
  have ht : IsLeadingWord p (p+1) t :=
    (isLeadingWord_congr_pattern w t htpat).1 hw
  have same : wordPattern t = wordPattern w :=
    (wordPattern_eq_iff t w).2 (fun a b => (htpat a b).symm)
  dsimp [leadPatterns]
  exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩,
    same⟩

/-- Fibres of a pattern are precisely relabellings of any representative.
In a leading word the number of used letters is `p/2+1`; thus every fibre has
falling-factorial size. -/
lemma card_words_pattern_of_leading {p d n : ℕ}
    (w : Fin (p+1) → Fin d) (hw : IsLeadingWord p d w) :
    ( (Finset.univ : Finset (Fin (p+1) → Fin n)).filter
        (fun f => wordPattern f = wordPattern w)).card =
      Nat.descFactorial n (p/2+1) := by
  classical
  -- equality of patterns is the `Relabels` condition
  let E : {f : Fin (p+1) → Fin n // wordPattern f = wordPattern w} ≃
      Relabels (n:=n) w :=
    { toFun := fun f => ⟨f.val,
          (wordPattern_eq_iff f.val w).1 f.property⟩
      invFun := fun f => ⟨f.val,
          (wordPattern_eq_iff f.val w).2 f.property⟩
      left_inv := by intro f; cases f; rfl
      right_inv := by intro f; cases f; rfl }
  have im : (Finset.univ.image w).card = p/2+1 := by
    rcases hw with ⟨cl, rep, mx⟩
    -- `card_vertices_word` removes the cast to naturals
    rw [card_vertices_word]
      at mx
    exact mx
  have c := card_relabels_image (n:=n) w
  have eqcard :
      Fintype.card {f : Fin (p+1) → Fin n // wordPattern f = wordPattern w}
         = Nat.descFactorial n (p/2+1) := by
    rw [Fintype.card_congr E, c, im]
  let T : Finset (Fin (p+1) → Fin n) :=
    (Finset.univ : Finset (Fin (p+1) → Fin n)).filter
      (fun f => wordPattern f = wordPattern w)
  let ET : {f // f ∈ T} ≃
      {f : Fin (p+1) → Fin n // wordPattern f = wordPattern w} :=
        Equiv.subtypeEquivRight (by intro f; simp [T])
  change T.card = _
  calc
    T.card = Fintype.card {f // f ∈ T} := (Fintype.card_coe T).symm
    _ = Fintype.card {f : Fin (p+1) → Fin n //
          wordPattern f = wordPattern w} := Fintype.card_congr ET
    _ = _ := eqcard

/-- Cardinal of all labelled leading paths is the number of equality patterns
times the falling factorial.  This lemma stops *exactly* at the Catalan
unlabelled count. -/
lemma card_leadingWords_eq_patterns_mul (p n : ℕ) :
    ((Finset.univ : Finset (Fin (p+1) → Fin n)).filter
        (fun w => IsLeadingWord p n w)).card =
      (leadPatterns p).card * Nat.descFactorial n (p/2+1) := by
  classical
  let pats := leadPatterns p
  let words : Finset (Fin (p+1) → Fin n) := Finset.univ
  -- Each leading word belongs to its unique Boolean pattern.
  have expand (f : Fin (p+1) → Fin n) :
      (if IsLeadingWord p n f then 1 else 0) =
        ∑ t ∈ pats, if wordPattern f = t then
              (if IsLeadingWord p n f then (1:ℕ) else 0) else 0 := by
    by_cases lf : IsLeadingWord p n f
    · have mem : wordPattern f ∈ pats := wordPattern_mem_of_leading f lf
      classical
      -- only the summand at `wordPattern f` survives
      have one : (∑ t ∈ pats, if wordPattern f = t then
              (if IsLeadingWord p n f then (1:ℕ) else 0) else 0) = 1 := by
        classical
        -- filter a single point by erasing it
        calc
          (∑ t ∈ pats, if wordPattern f = t then
              (if IsLeadingWord p n f then (1:ℕ) else 0) else 0) =
            ∑ t ∈ pats, if wordPattern f = t then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro a ha
              simp [lf]
          _ = 1 := by
              simp [mem]
      simpa [lf, one]
    · simp [lf]
  -- convert cardinalities to sums of indicators and regroup the finite rectangle
  classical
  calc
    ((Finset.univ : Finset (Fin (p+1) → Fin n)).filter
        (fun w => IsLeadingWord p n w)).card =
        ∑ f : (Fin (p+1) → Fin n),
             if IsLeadingWord p n f then (1:ℕ) else 0 := by
              simp
    _ = ∑ f : (Fin (p+1) → Fin n), ∑ t ∈ pats,
          if wordPattern f = t then
            (if IsLeadingWord p n f then (1:ℕ) else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro a ha
              exact expand a
    _ = ∑ t ∈ pats, ∑ f : (Fin (p+1) → Fin n),
          if wordPattern f = t then
            (if IsLeadingWord p n f then (1:ℕ) else 0) else 0 := by
              -- interchange two finite sums
              rw [Finset.sum_comm]
    _ = ∑ _t ∈ pats, Nat.descFactorial n (p/2+1) := by
          apply Finset.sum_congr rfl
          intro t ht
          rcases Finset.mem_image.mp ht with ⟨w, hw, wt⟩
          have leadw : IsLeadingWord p (p+1) w :=
            (Finset.mem_filter.mp hw).2
          -- words in a fibre of a leading representative are themselves leading
          have allLead (f : Fin (p+1) → Fin n)
              (eq : wordPattern f = t) : IsLeadingWord p n f := by
            have pat : wordPattern f = wordPattern w := eq.trans wt.symm
            exact (isLeadingWord_congr_pattern f w
              ((wordPattern_eq_iff f w).1 pat)).2 leadw
          have fibre := card_words_pattern_of_leading (n:=n) w leadw
          -- turn the inner indicator into the card of its pattern fibre
          have eqsum : (∑ f : (Fin (p+1) → Fin n),
              if wordPattern f = t then
                (if IsLeadingWord p n f then (1:ℕ) else 0) else 0) =
              ((Finset.univ : Finset (Fin (p+1) → Fin n)).filter
                   (fun f => wordPattern f = wordPattern w)).card := by
            classical
            -- both are indicator sums
            calc
              (∑ f : (Fin (p+1) → Fin n),
                if wordPattern f = t then
                  (if IsLeadingWord p n f then (1:ℕ) else 0) else 0) =
                ∑ f : (Fin (p+1) → Fin n),
                  if wordPattern f = wordPattern w then (1:ℕ) else 0 := by
                    apply Finset.sum_congr rfl
                    intro f hf
                    by_cases e : wordPattern f = t
                    · have ew : wordPattern f = wordPattern w := e.trans wt.symm
                      simp [e, ew, allLead f e, wt]
                    · have ew : wordPattern f ≠ wordPattern w := by
                        intro z
                        exact e (z.trans wt)
                      simp [e, ew]
              _ = _ := by simp
          rw [eqsum, fibre]
    _ = _ := by simp [pats, mul_comm]

/-- Cons and tail identify the path version used in the trace with words. -/
lemma card_leadingPaths_eq_patterns_mul (p n : ℕ) :
    ((Finset.univ : Finset (Fin n × (Fin p → Fin n))).filter
        (fun z : Fin n × (Fin p → Fin n) => IsLeadingPath z.1 z.2)).card =
      (leadPatterns p).card * Nat.descFactorial n (p/2+1) := by
  classical
  -- `Fin.consEquiv` is a bijection, so indicator sums agree termwise
  let e := Fin.consEquiv (fun _ : Fin (p+1) => Fin n)
  calc
    ((Finset.univ : Finset (Fin n × (Fin p → Fin n))).filter
        (fun z : Fin n × (Fin p → Fin n) => IsLeadingPath z.1 z.2)).card =
      ∑ z : (Fin n × (Fin p → Fin n)),
          if IsLeadingPath z.1 z.2 then (1:ℕ) else 0 := by simp
    _ = ∑ w : (Fin (p+1) → Fin n),
          if IsLeadingWord p n w then (1:ℕ) else 0 := by
            -- reindex using the equivalence; `symm` sends a pair to `cons`
            symm
            calc
              (∑ w : (Fin (p+1) → Fin n),
                if IsLeadingWord p n w then (1:ℕ) else 0) =
                ∑ z : (Fin n × (Fin p → Fin n)),
                  if IsLeadingWord p n (e z) then (1:ℕ) else 0 := by
                    exact (Equiv.sum_comp e
                      (fun w => if IsLeadingWord p n w then (1:ℕ) else 0)).symm
              _ = _ := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    rcases z with ⟨i,v⟩
                    dsimp [e]
                    change (if IsLeadingWord p n (Fin.cons i v) then (1:ℕ) else 0) = _
                    unfold IsLeadingWord
                    simp [Fin.tail_cons]
    _ = ((Finset.univ : Finset (Fin (p+1) → Fin n)).filter
          (fun w => IsLeadingWord p n w)).card := by simp
    _ = _ := card_leadingWords_eq_patterns_mul p n

end
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Patterns.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/CutCenter.lean
section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter

namespace WignerSupport

/-- The first and second moments of a hard cut of a single entry.
These constants are the ones which occur in the bounded Wigner theorem. -/
noncomputable def cutMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (R : ℝ) : ℝ :=
  ∫ ω, cutX R X 0 0 ω ∂μ

noncomputable def cutSecond {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (R : ℝ) : ℝ :=
  ∫ ω, (cutX R X 0 0 ω)^2 ∂μ

/-- variance of a truncated entry; making it explicit is useful since cutting does
not preserve either the mean or the variance. -/
noncomputable def cutVariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (R : ℝ) : ℝ :=
  cutSecond μ X R - (cutMean μ X R)^2

lemma cut_sq_le {Ω : Type*} (R : ℝ) (X : ℕ → ℕ → Ω → ℝ)
    (i j : ℕ) (ω : Ω) :
    (cutX R X i j ω)^2 ≤ (X i j ω)^2 := by
  unfold cutX
  split_ifs <;> nlinarith [sq_nonneg (X i j ω)]

lemma cut_abs_le {Ω : Type*} (R : ℝ) (X : ℕ → ℕ → Ω → ℝ)
    (i j : ℕ) (ω : Ω) :
    |cutX R X i j ω| ≤ |X i j ω| := by
  unfold cutX
  split_ifs <;> simp

/-- Pointwise a hard cut with integer radii eventually does nothing.  The elementary
lemma is kept separate from dominated convergence; it is also handy when replacing
integrands under an a.e. statement. -/
lemma cutX_tendsto_nat {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ)
    (i j : ℕ) (ω : Ω) :
    Tendsto (fun r : ℕ => cutX (r:ℝ) X i j ω) atTop (𝓝 (X i j ω)) := by
  have ev' : ∀ᶠ r : ℕ in atTop, |X i j ω| ≤ (r:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |X i j ω|)
  have ev : ∀ᶠ r : ℕ in atTop, cutX (r:ℝ) X i j ω = X i j ω := by
    filter_upwards [ev'] with r hr
    have hn : ¬ (r:ℝ) < |X i j ω| := not_lt_of_ge hr
    simp [cutX, hn]
  exact (tendsto_congr' ev).2 tendsto_const_nhds

lemma cutX_sq_tendsto_nat {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ)
    (i j : ℕ) (ω : Ω) :
    Tendsto (fun r : ℕ => (cutX (r:ℝ) X i j ω)^2) atTop
      (𝓝 ((X i j ω)^2)) := by
  simpa [Function.comp_def] using ((continuous_pow 2).tendsto _).comp (cutX_tendsto_nat X i j ω)


/-- The mean of the cut entry converges to the (integrable) uncut mean. -/
lemma cutMean_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (hm : Measurable (X 0 0)) (hi : Integrable (X 0 0) μ) :
    Tendsto (fun r : ℕ => cutMean μ X (r:ℝ)) atTop
       (𝓝 (∫ ω, X 0 0 ω ∂μ)) := by
  let F : ℕ → Ω → ℝ := fun r ω => cutX (r:ℝ) X 0 0 ω
  have hmeas (r : ℕ) : Measurable (cutX (r:ℝ) X 0 0) := by
    rw [cutX_comp]
    exact (cut_measurable (r:ℝ)).comp hm
  have hfm : ∀ r, AEStronglyMeasurable (F r) μ := by
    intro r
    exact (hmeas r).aestronglyMeasurable
  have hbd : ∀ r ω, ‖F r ω‖ ≤ |X 0 0 ω| := by
    intro r ω
    rw [Real.norm_eq_abs]
    exact cut_abs_le (r:ℝ) X 0 0 ω
  have hil : Integrable (fun ω => |X 0 0 ω|) μ := by
    simpa [Real.norm_eq_abs] using hi.norm
  have hlim : ∀ ω, Tendsto (fun r : ℕ => F r ω) atTop
        (𝓝 (X 0 0 ω)) := by
    intro ω
    exact cutX_tendsto_nat X 0 0 ω
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := atTop) (F := F) (f := fun ω => X 0 0 ω)
      (fun ω => |X 0 0 ω|)
      (Filter.Eventually.of_forall hfm)
      (Filter.Eventually.of_forall (fun r => ae_of_all _ (hbd r)))
      hil (ae_of_all _ hlim)
  simpa [cutMean, F] using h

/-- The second moment of the cut entry converges to the uncut second
moment, also without any moment of order greater than two. -/
lemma cutSecond_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (hm : Measurable (X 0 0))
    (hi : Integrable (fun ω => (X 0 0 ω)^2) μ) :
    Tendsto (fun r : ℕ => cutSecond μ X (r:ℝ)) atTop
       (𝓝 (∫ ω, (X 0 0 ω)^2 ∂μ)) := by
  let F : ℕ → Ω → ℝ := fun r ω => (cutX (r:ℝ) X 0 0 ω)^2
  have hmeas (r : ℕ) : Measurable (fun ω => (cutX (r:ℝ) X 0 0 ω)^2) := by
    have h0 : Measurable (cutX (r:ℝ) X 0 0) := by
      rw [cutX_comp]
      exact (cut_measurable (r:ℝ)).comp hm
    exact h0.pow_const _
  have hfm : ∀ r, AEStronglyMeasurable (F r) μ := by
    intro r
    exact (hmeas r).aestronglyMeasurable
  have hbd : ∀ r ω, ‖F r ω‖ ≤ (X 0 0 ω)^2 := by
    intro r ω
    have hz : 0 ≤ F r ω := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hz]
    exact cut_sq_le (r:ℝ) X 0 0 ω
  have hlim : ∀ ω, Tendsto (fun r : ℕ => F r ω) atTop
        (𝓝 ((X 0 0 ω)^2)) := by
    intro ω
    exact cutX_sq_tendsto_nat X 0 0 ω
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := atTop) (F := F)
      (f := fun ω => (X 0 0 ω)^2)
      (fun ω => (X 0 0 ω)^2)
      (Filter.Eventually.of_forall hfm)
      (Filter.Eventually.of_forall (fun r => ae_of_all _ (hbd r)))
      hi (ae_of_all _ hlim)
  simpa [cutSecond, F] using h

lemma cutVariance_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (hm : Measurable (X 0 0)) (h1 : Integrable (X 0 0) μ)
    (h2 : Integrable (fun ω => (X 0 0 ω)^2) μ) :
    Tendsto (fun r : ℕ => cutVariance μ X (r:ℝ)) atTop
       (𝓝 ((∫ ω, (X 0 0 ω)^2 ∂μ) - (∫ ω, X 0 0 ω ∂μ)^2)) := by
  have a := cutSecond_tendsto μ X hm h2
  have b := cutMean_tendsto μ X hm h1
  simpa [cutVariance] using (a.sub (b.pow 2))

/-- Algebraic variance identity for the cut.  This lemma is a useful guard:
the hard cut is not centered.  It says exactly which semicircle should be
used in the bounded approximation. -/
lemma cutVariance_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ) (R : ℝ)
    (hm : Measurable (X 0 0)) (h1 : Integrable (X 0 0) μ)
    (h2 : Integrable (fun ω => (X 0 0 ω)^2) μ) :
    cutVariance μ X R =
      ∫ ω, (cutX R X 0 0 ω - cutMean μ X R)^2 ∂μ := by
  let f : Ω → ℝ := fun ω => cutX R X 0 0 ω
  let b : ℝ := cutMean μ X R
  have fm : Measurable f := by
    dsimp [f]
    rw [cutX_comp]
    exact (cut_measurable R).comp hm
  have fi : Integrable f μ := by
    have aux : Integrable (fun ω => |X 0 0 ω|) μ := by
      simpa [Real.norm_eq_abs] using h1.norm
    refine Integrable.mono' aux fm.aestronglyMeasurable ?_
    filter_upwards [] with ω
    dsimp [f]
    exact cut_abs_le R X 0 0 ω
  have f2m : Measurable (fun ω => (f ω)^2) := fm.pow_const _
  have f2i : Integrable (fun ω => (f ω)^2) μ := by
    refine Integrable.mono' h2 f2m.aestronglyMeasurable ?_
    filter_upwards [] with ω
    have hz : 0 ≤ (f ω)^2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hz]
    exact cut_sq_le R X 0 0 ω
  have fib : (∫ ω, f ω ∂μ) = b := by rfl
  have f2b : (∫ ω, (f ω)^2 ∂μ) = cutSecond μ X R := by rfl
  have ci : Integrable (fun _ : Ω => b^2) μ :=
    MeasureTheory.integrable_const _
  have cfi : Integrable (fun ω => (-2*b) * f ω) μ :=
    fi.const_mul _
  have alg (ω : Ω) : (f ω - b)^2 = (f ω)^2 + ((-2*b) * f ω) + b^2 := by ring
  have intalg : (∫ ω, (f ω - b)^2 ∂μ) =
      (∫ ω, (f ω)^2 ∂μ) + (∫ ω, (-2*b) * f ω ∂μ) +
        (∫ _ : Ω, b^2 ∂μ) := by
    calc
      (∫ ω, (f ω - b)^2 ∂μ) =
          ∫ ω, ((f ω)^2 + ((-2*b) * f ω)) + b^2 ∂μ := by
            apply integral_congr_ae
            exact ae_of_all _ (fun ω => by change (f ω - b)^2 = _; exact alg ω)
      _ = (∫ ω, ((f ω)^2 + ((-2*b) * f ω)) ∂μ) +
            (∫ _ : Ω, b^2 ∂μ) := by
              -- express the integrands as sums of functions
              have ha := MeasureTheory.integral_add (f2i.add cfi) ci
              exact ha
      _ = _ := by
              rw [MeasureTheory.integral_add f2i cfi]
  have cross : (∫ ω, (-2*b) * f ω ∂μ) = (-2*b) * b := by
    rw [MeasureTheory.integral_const_mul]
    exact congrArg (fun t : ℝ => (-2*b) * t) fib
  have one : (∫ _ : Ω, b^2 ∂μ) = b^2 := by
    rw [MeasureTheory.integral_const]
    simp
  unfold cutVariance
  -- both sides have now been evaluated in elementary reals
  change cutSecond μ X R - (cutMean μ X R)^2 =
      (∫ ω, (f ω - b)^2 ∂μ)
  rw [intalg, cross, one, f2b]
  change cutSecond μ X R - b^2 = cutSecond μ X R + (-2*b) * b + b^2
  ring

lemma cutVariance_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ) (R : ℝ)
    (hm : Measurable (X 0 0)) (h1 : Integrable (X 0 0) μ)
    (h2 : Integrable (fun ω => (X 0 0 ω)^2) μ) :
    0 ≤ cutVariance μ X R := by
  rw [cutVariance_eq_integral μ X R hm h1 h2]
  exact MeasureTheory.integral_nonneg_of_ae
    (ae_of_all _ (fun ω => sq_nonneg _))

end WignerSupport

namespace WignerSupport

/-- Centering a hard cut.  This is the bounded triangular entry to which the
standard closed-walk theorem is applied.  The constant is that of the common
`(0,0)` entry, not a family of unrelated means. -/
noncomputable def centeredCut {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : ℝ) (X : ℕ → ℕ → Ω → ℝ)
    (i j : ℕ) (ω : Ω) : ℝ :=
  cutX R X i j ω - cutMean μ X R

lemma centeredCut_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : ℝ) (X : ℕ → ℕ → Ω → ℝ)
    (i j : ℕ) :
    centeredCut μ R X i j =
      (fun x : ℝ => cut R x - cutMean μ X R) ∘ X i j := by
  funext ω
  rfl

lemma centeredCut_measurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : ℝ) (X : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ i j, Measurable (X i j)) (i j : ℕ) :
    Measurable (centeredCut μ R X i j) := by
  rw [centeredCut_comp]
  exact ((cut_measurable R).sub measurable_const).comp (hm i j)

lemma centeredCut_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {R : ℝ} (hR : 0 ≤ R)
    (X : ℕ → ℕ → Ω → ℝ) (i j : ℕ) (ω : Ω) :
    |centeredCut μ R X i j ω| ≤ R + |cutMean μ X R| := by
  unfold centeredCut
  calc
    |cutX R X i j ω - cutMean μ X R| ≤
        |cutX R X i j ω| + |cutMean μ X R| := abs_sub _ _
    _ ≤ R + |cutMean μ X R| := by
      gcongr
      exact cutX_bound hR X i j ω

lemma centeredCut_indep {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : ℝ) (X : ℕ → ℕ → Ω → ℝ)
    (h : iIndepFun (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} =>
             X ij.val.1 ij.val.2) μ) :
    iIndepFun (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} =>
             centeredCut μ R X ij.val.1 ij.val.2) μ := by
  have hfun : Measurable (fun x : ℝ => cut R x - cutMean μ X R) :=
    (cut_measurable R).sub measurable_const
  have hc := ProbabilityTheory.iIndepFun.comp h
      (fun _ : {p : ℕ × ℕ // p.1 ≤ p.2} =>
         (fun x : ℝ => cut R x - cutMean μ X R))
      (by intro i; exact hfun)
  simpa [centeredCut_comp, Function.comp_def, centeredCut, cutX, cut] using hc

lemma centeredCut_ident {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : ℝ) (X : ℕ → ℕ → Ω → ℝ)
    (h : ∀ i j i' j', i ≤ j → i' ≤ j' →
       IdentDistrib (X i j) (X i' j') μ μ) :
    ∀ i j i' j', i ≤ j → i' ≤ j' →
       IdentDistrib (centeredCut μ R X i j)
          (centeredCut μ R X i' j') μ μ := by
  intro i j a b hij hab
  have funm : Measurable (fun x : ℝ => cut R x - cutMean μ X R) :=
    (cut_measurable R).sub measurable_const
  have hh := (h i j a b hij hab).comp funm
  simpa [centeredCut_comp, Function.comp_def, centeredCut, cutX, cut] using hh

lemma centeredCut_pow_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (R : ℝ) (hR : 0 ≤ R)
    (X : ℕ → ℕ → Ω → ℝ) (hm : ∀ i j, Measurable (X i j))
    (i j m : ℕ) :
    Integrable (fun ω => (centeredCut μ R X i j ω)^m) μ := by
  have meas : Measurable (fun ω => (centeredCut μ R X i j ω)^m) :=
    (centeredCut_measurable μ R X hm i j).pow_const _
  refine Integrable.of_bound meas.aestronglyMeasurable
      ((R + |cutMean μ X R|)^m) ?_
  filter_upwards [] with ω
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (centeredCut_bound μ hR X i j ω) _

private lemma __CutCenter_cut_integrable_entry {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : ℝ) (X : ℕ → ℕ → Ω → ℝ)
    (i j : ℕ) (hm : Measurable (X i j)) (hi : Integrable (X i j) μ) :
    Integrable (fun ω => cutX R X i j ω) μ := by
  have mm : Measurable (cutX R X i j) := by
    rw [cutX_comp]
    exact (cut_measurable R).comp hm
  have hnorm : Integrable (fun ω => |X i j ω|) μ := by
    simpa [Real.norm_eq_abs] using hi.norm
  refine Integrable.mono' hnorm mm.aestronglyMeasurable ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  exact cut_abs_le R X i j ω

/-- The common centering really sets every upper entry's mean to zero. -/
lemma centeredCut_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ℝ) (hR : 0 ≤ R) (X : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ i j, Measurable (X i j))
    (hi : ∀ i j, i ≤ j → Integrable (X i j) μ)
    (hid : ∀ i j i' j', i ≤ j → i' ≤ j' →
       IdentDistrib (X i j) (X i' j') μ μ) :
    ∀ i j, i ≤ j →
       ∫ ω, centeredCut μ R X i j ω ∂μ = 0 := by
  intro i j hij
  have hh := centeredCut_ident μ R X hid i j 0 0 hij (by omega)
  rw [hh.integral_eq]
  have f0 : Integrable (fun ω => cutX R X 0 0 ω) μ :=
    __CutCenter_cut_integrable_entry μ R X 0 0 (hm _ _) (hi 0 0 (by omega))
  have c0 : Integrable (fun _ : Ω => cutMean μ X R) μ :=
    MeasureTheory.integrable_const _
  change (∫ ω, cutX R X 0 0 ω - cutMean μ X R ∂μ) = 0
  rw [MeasureTheory.integral_sub f0 c0, MeasureTheory.integral_const]
  simp [cutMean]

/-- Its common second centered moment is the variance of the cut, not the
second (uncentered) moment. -/
lemma centeredCut_second {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ℝ) (hR : 0 ≤ R) (X : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ i j, Measurable (X i j))
    (hi : ∀ i j, i ≤ j → Integrable (X i j) μ)
    (hi2 : Integrable (fun ω => (X 0 0 ω)^2) μ)
    (hid : ∀ i j i' j', i ≤ j → i' ≤ j' →
       IdentDistrib (X i j) (X i' j') μ μ) :
    ∀ i j, i ≤ j →
       ∫ ω, (centeredCut μ R X i j ω)^2 ∂μ = cutVariance μ X R := by
  intro i j hij
  have hh := centeredCut_ident μ R X hid i j 0 0 hij (by omega)
  -- compose on the underlying scalar value, not on `Ω`
  have hs := hh.comp (by fun_prop : Measurable (fun x : ℝ => x^2))
  have eqint := hs.integral_eq
  change (∫ ω, (centeredCut μ R X i j ω)^2 ∂μ) = _
  have ei : (∫ ω, (centeredCut μ R X i j ω)^2 ∂μ) =
      (∫ ω, (centeredCut μ R X 0 0 ω)^2 ∂μ) := by
    simpa [Function.comp_def] using eqint
  rw [ei]
  have v := cutVariance_eq_integral μ X R (hm 0 0) (hi 0 0 (by omega)) hi2
  symm
  -- pointwise the centered `(0,0)` expression is exactly this integral
  simpa [centeredCut] using v

end WignerSupport
namespace WignerSupport
lemma cut_zero (x : ℝ) : cut 0 x = 0 := by
  unfold cut
  split_ifs with h
  · rfl
  · have ax : |x| = 0 := le_antisymm (le_of_not_gt h) (abs_nonneg _)
    simpa using (abs_eq_zero.mp ax)
lemma cutX_zero {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (i j : ℕ) (ω : Ω) :
    cutX 0 X i j ω = 0 := cut_zero _
lemma cutMean_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : cutMean μ X 0 = 0 := by
  unfold cutMean
  simp [cutX_zero]
lemma cutSecond_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : cutSecond μ X 0 = 0 := by
  unfold cutSecond
  simp [cutX_zero]
lemma cutVariance_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) : cutVariance μ X 0 = 0 := by
  simp [cutVariance, cutSecond_zero, cutMean_zero]
lemma centeredCut_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ) (i j : ℕ) (ω : Ω) :
    centeredCut μ 0 X i j ω = 0 := by
  simp [centeredCut, cutX_zero, cutMean_zero]
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/CutCenter.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PatternLimit.lean
section
open Filter
open scoped BigOperators Topology
namespace WignerSupport

attribute [local instance] Classical.propDecidable
/-- For fixed length the labellings of an equality pattern are asymptotically
`n^d`. This small falling-factorial limit is often what is lost when using
`n^(p+1)` arbitrary vertex lists. The shift `k+1` avoids a denominator at 0. -/
lemma tendsto_descFactorial_div_pow (d : ℕ) :
    Tendsto
      (fun k : ℕ => (Nat.descFactorial (k+1) d : ℝ) / ((k+1:ℕ):ℝ)^d)
      atTop (𝓝 (1:ℝ)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hfac : ∀ᶠ k : ℕ in atTop, d ≤ k+1 :=
      (eventually_ge_atTop (d-1)) |>.mono (by
        intro k hk; omega)
    have hfne (k : ℕ) : (0:ℝ) < (k+1:ℕ) := by
      exact_mod_cast (Nat.zero_lt_succ k)
    have onefactor : Tendsto
        (fun k : ℕ => (((k+1:ℕ):ℝ) - (d:ℝ)) / ((k+1:ℕ):ℝ))
        atTop (𝓝 (1:ℝ)) := by
      have invlim : Tendsto (fun k : ℕ => 1 / ((k+1:ℕ):ℝ))
          atTop (𝓝 (0:ℝ)) := by
        simpa using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have dl := (Filter.Tendsto.const_mul (d:ℝ) invlim)
      have sub : Tendsto
          (fun k : ℕ => (1:ℝ) - (d:ℝ) * (1 / ((k+1:ℕ):ℝ)))
          atTop (𝓝 ((1:ℝ) - (d:ℝ) * 0)) :=
            (tendsto_const_nhds.sub dl)
      convert sub using 1
      · funext k
        have hn : ((k+1:ℕ):ℝ) ≠ 0 := ne_of_gt (hfne k)
        field_simp
      · simp
    have prodlim := onefactor.mul ih
    -- recurrence of `descFactorial`; eventually the natural subtraction casts
    -- to real subtraction since `k+1 ≥ d`.
    have prodlim' : Tendsto
        (fun k : ℕ => ((((k+1:ℕ):ℝ) - (d:ℝ)) / ((k+1:ℕ):ℝ)) *
          ((Nat.descFactorial (k+1) d : ℝ) / ((k+1:ℕ):ℝ)^d))
        atTop (𝓝 (1:ℝ)) := by
      convert prodlim using 1 <;> simp
    apply prodlim'.congr'
    filter_upwards [hfac] with k hk
    rw [Nat.descFactorial_succ]
    rw [Nat.cast_mul, Nat.cast_sub hk]
    rw [pow_succ]
    have hn : ((k+1:ℕ):ℝ) ≠ 0 := ne_of_gt (hfne k)
    field_simp

/-- Consequently the leading-path coefficient divided by the moment scale
has limit equal to the finite **unlabelled** pattern count. -/
lemma tendsto_card_leadingPaths_normalized (p : ℕ) :
    Tendsto
      (fun k : ℕ =>
        (((Finset.univ : Finset
            (Fin (k+1) × (Fin p → Fin (k+1)))).filter
              (fun z : Fin (k+1) × (Fin p → Fin (k+1)) =>
                IsLeadingPath z.1 z.2)).card : ℝ) /
              (((k+1:ℕ):ℝ)^(p/2+1)))
      atTop (𝓝 ((leadPatterns p).card : ℝ)) := by
  have base := tendsto_descFactorial_div_pow (p/2+1)
  have c := Filter.Tendsto.const_mul ((leadPatterns p).card : ℝ) base
  convert c using 1
  · funext k
    rw [card_leadingPaths_eq_patterns_mul]
    push_cast
    ring
  · simp

end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PatternLimit.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/EqualityWalk.lean
section

namespace WignerSupport
/-! Equality in the elementary connected-walk bound is much stronger than just its
cardinality assertion. Read a word from the *right*. At a step `i,j` either `i`
has already occurred in the remaining suffix, in which case the edge `ij` has
already occurred too, or both are new. This is the elementary tree invariant;
it is independent of an ordering of the labels. -/
open scoped BigOperators

/-- equality at one node of a rooted list descends to the suffix, and detects
exactly when the current edge is old. -/
lemma walk_eq_suffix (i j : ℕ) (xs : List ℕ)
    (h : (walkVertices i (j::xs)).card = (walkEdges i (j::xs)).card + 1) :
    (walkVertices j xs).card = (walkEdges j xs).card + 1 ∧
      (i ∈ walkVertices j xs ↔ edgeNat i j ∈ walkEdges j xs) := by
  classical
  let V := walkVertices j xs
  let E := walkEdges j xs
  have base : V.card ≤ E.card + 1 := by
    dsimp [V, E]
    exact card_walkVertices_le_edges_add_one j xs
  by_cases hi : i ∈ V
  · have hv : walkVertices i (j::xs) = V := by
      simpa [V] using (walkVertices_cons i j xs).trans (Finset.insert_eq_of_mem hi)
    have incard : (walkEdges i (j::xs)).card ≤ E.card + 1 := by
      rw [walkEdges_cons]
      dsimp [E]
      exact Finset.card_insert_le _ _
    have hc : (walkEdges i (j::xs)).card = E.card - 0 ∨ True := Or.inr trivial
    have nomore : edgeNat i j ∈ E := by
      by_contra hn
      have ec : (walkEdges i (j::xs)).card = E.card + 1 := by
        rw [walkEdges_cons]
        dsimp [E] at hn ⊢
        exact Finset.card_insert_of_notMem hn
      rw [hv, ec] at h
      omega
    have ew : walkEdges i (j::xs) = E := by
      rw [walkEdges_cons]
      dsimp [E] at nomore ⊢
      exact Finset.insert_eq_of_mem nomore
    constructor
    · rw [hv, ew] at h
      exact h
    · exact ⟨fun _ => nomore, fun _ => hi⟩
  · have hnew : edgeNat i j ∉ E := by
      intro he
      have ep := walkEdges_endpoints j xs (edgeNat i j) (by simpa [E] using he)
      have hchoice : min i j = i ∨ min i j = j := min_choice _ _
      rcases hchoice with h1 | h1
      · exact hi (by simpa [edgeNat, V, h1] using ep.1)
      · have hchoice' : max i j = i ∨ max i j = j := max_choice _ _
        rcases hchoice' with h2 | h2
        · exact hi (by simpa [edgeNat, V, h2] using ep.2)
        · have heq : i = j := by omega
          subst i
          exact hi (by
            dsimp [V]
            exact walkVertices_root_mem j xs)
    have hv : (walkVertices i (j::xs)).card = V.card + 1 := by
      rw [walkVertices_cons, Finset.card_insert_of_notMem (by simpa [V] using hi)]
    have he : (walkEdges i (j::xs)).card = E.card + 1 := by
      rw [walkEdges_cons, Finset.card_insert_of_notMem (by simpa [E] using hnew)]
    constructor
    · rw [hv] at h
      rw [he] at h
      have hh : V.card = E.card + 1 := by omega
      simpa [V, E] using hh
    · constructor <;> intro z
      · exact False.elim (hi z)
      · exact False.elim (hnew z)

/-- With equality globally, every right suffix has equality. `getD` chooses a
harmless default root after the list has ended. -/
lemma walk_eq_drop (i : ℕ) (xs : List ℕ)
    (h : (walkVertices i xs).card = (walkEdges i xs).card + 1) (k : ℕ) :
    let pre := (i :: xs).getD k i
    let rest := (i :: xs).drop (k+1)
    (walkVertices pre rest).card = (walkEdges pre rest).card + 1 := by
  induction k generalizing i xs with
  | zero => simpa using h
  | succ k ih =>
      cases xs with
      | nil => simp [walkVertices, walkEdges]
      | cons j ys =>
        have t := (walk_eq_suffix i j ys h).1
        by_cases hk : k < (j::ys).length
        · have eqd : (j::ys).getD k i = (j::ys).getD k j := by
            simp [List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem hk]
          dsimp
          rw [List.getD_cons_succ]
          rw [eqd]
          -- strip the first letter from the double drop
          have I := (ih (i:=j) (xs:=ys) t)
          dsimp at I
          convert I using 1 <;> simp [List.drop_succ_cons, Nat.add_assoc]
        · have hk' : (j::ys).length ≤ k := Nat.le_of_not_gt hk
          have dropnil : (j::ys).drop k = [] :=
            List.drop_eq_nil_of_le hk'
          have gi : (j::ys).getD k i = i := List.getD_eq_default _ _ hk'
          dsimp
          rw [List.getD_cons_succ]
          rw [gi]
          have hy : ys.length ≤ k := by
            have z := hk'
            simp at z
            omega
          simp [List.drop_eq_nil_of_le hy, walkVertices, walkEdges]

/-- Equality means that, looking rightwards, a step is novel precisely when
its starting letter is novel. This form is often the easiest way to recover
the tree/Dyck parenthesis matching. -/
lemma walk_new_iff (i j : ℕ) (xs : List ℕ)
    (h : (walkVertices i (j::xs)).card = (walkEdges i (j::xs)).card + 1) :
    (i ∉ walkVertices j xs ↔ edgeNat i j ∉ walkEdges j xs) := by
  classical
  simpa using not_congr (walk_eq_suffix i j xs h).2

end WignerSupport

namespace WignerSupport
open scoped BigOperators

/-- A walk that has as many vertices as edges plus one contains no loops.
Here edges are the actual upper triangular pairs, so this also rules out
hidden diagonal edges before one passes to a `SimpleGraph`. -/
lemma walk_eq_no_self (i : ℕ) (xs : List ℕ)
    (h : (walkVertices i xs).card = (walkEdges i xs).card + 1) :
    ∀ a : ℕ, edgeNat a a ∉ walkEdges i xs := by
  classical
  induction xs generalizing i with
  | nil => simp [walkEdges]
  | cons j ys ih =>
      have hh := walk_eq_suffix i j ys h
      have tailNo : ∀ a, edgeNat a a ∉ walkEdges j ys := ih j hh.1
      intro a ha
      rw [walkEdges_cons] at ha
      have cases : edgeNat a a = edgeNat i j ∨
          edgeNat a a ∈ walkEdges j ys := by
        simpa using ha
      rcases cases with eq | old
      · have dis : (a = i ∧ a = j) ∨ (a = j ∧ a = i) :=
          (edgeNat_eq_iff.mp eq)
        have ij : i = j := by rcases dis with d|d <;> omega
        subst i
        have root : j ∈ walkVertices j ys := walkVertices_root_mem _ _
        have oldloop : edgeNat j j ∈ walkEdges j ys := hh.2.1 root
        exact (tailNo j) oldloop
      · exact (tailNo a) old

/-- Equality descendant for a leading path stated in list language. This is
the conversion that permits chronological arguments without dependent `Fin`
indices. No parity assumption is needed: equality of vertices in the leading
case already forces equality of edge count by the connected-walk bound. -/
lemma leading_walk_eq {n p : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (rep : ∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧ pathEdgesNat i v r = pathEdgesNat i v u)
    (mx : (pathVerticesFin i v).card = p/2 + 1) :
    (walkVertices i.val (pathList v)).card =
      (walkEdges i.val (pathList v)).card + 1 := by
  have ec := card_edges_eq_half_of_max_vertices i v rep mx
  have vc : (walkVertices i.val (pathList v)).card = p/2 + 1 := by
    exact mx
  have ee : (walkEdges i.val (pathList v)).card = p/2 := by
    simpa [image_pathEdges_eq_walkEdges] using ec
  omega

/-- Thus no step of a leading word can be a loop. This small observation is an
annoying prerequisite for treating its finite edge set as a simple tree. -/
lemma leading_no_self {n p : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (rep : ∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧ pathEdgesNat i v r = pathEdgesNat i v u)
    (mx : (pathVerticesFin i v).card = p/2 + 1) :
    ∀ a : ℕ, edgeNat a a ∉ walkEdges i.val (pathList v) := by
  exact walk_eq_no_self _ _ (leading_walk_eq i v rep mx)

/-- Right-to-left old-edge criterion for a (nonempty) leading path. -/
lemma leading_old_iff {n p : ℕ} (i : Fin n) (v : Fin (p+1) → Fin n)
    (rep : ∀ u : Fin (p+1), ∃ r : Fin (p+1), r ≠ u ∧
      pathEdgesNat i v r = pathEdgesNat i v u)
    (mx : (pathVerticesFin i v).card = (p+1)/2 + 1) :
    (i.val ∈ walkVertices (v 0).val (pathList (Fin.tail v)) ↔
      edgeNat i.val (v 0).val ∈ walkEdges (v 0).val (pathList (Fin.tail v))) := by
  have h := leading_walk_eq i v rep mx
  rw [pathList_succ] at h
  exact (walk_eq_suffix _ _ _ h).2

end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/EqualityWalk.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/GraphTree.lean
section
open SimpleGraph
namespace WignerSupport
open scoped Sym2
-- work on the finite alphabet actually seen by the word
abbrev WalkVert (i : ℕ) (xs : List ℕ) := {a : ℕ // a ∈ walkVertices i xs}

def walkGraph (i : ℕ) (xs : List ℕ) : SimpleGraph (WalkVert i xs) :=
  SimpleGraph.fromRel (fun a b : WalkVert i xs => edgeNat a.val b.val ∈ walkEdges i xs)

lemma walkGraph_adj {i xs} (a b : WalkVert i xs) :
    (walkGraph i xs).Adj a b ↔ a ≠ b ∧ edgeNat a.val b.val ∈ walkEdges i xs := by
  change (a ≠ b ∧ (_ ∨ _)) ↔ _
  constructor
  · rintro ⟨ne,h|h⟩
    · exact ⟨ne,h⟩
    · exact ⟨ne, by simpa [edgeNat_comm] using h⟩
  · rintro ⟨ne,h⟩
    exact ⟨ne, Or.inl h⟩

/-- Injective sorted endpoints: natural sorted pairs and `Sym2 ℕ` carry the
same information. -/
lemma sorted_sym_inj {e f : {z : ℕ × ℕ // z.1 ≤ z.2}}
    (h : s(e.val.1,e.val.2) = s(f.val.1,f.val.2)) : e = f := by
  rcases (Sym2.eq_iff.mp h) with h | h
  · apply Subtype.ext
    exact Prod.ext h.1 h.2
  · apply Subtype.ext
    -- in the swapped case both ordered pairs are still determined
    have a := e.property
    have b := f.property
    have e1 : e.val.1 = f.val.1 := by omega
    have e2 : e.val.2 = f.val.2 := by omega
    exact Prod.ext e1 e2

section
variable (i : ℕ) (xs : List ℕ)

private def __GraphTree_edgeImage (e : {a // a ∈ walkEdges i xs}) : Sym2 (WalkVert i xs) :=
  s( (⟨e.val.val.1, (walkEdges_endpoints i xs e.val e.property).1⟩ : WalkVert i xs),
     (⟨e.val.val.2, (walkEdges_endpoints i xs e.val e.property).2⟩ : WalkVert i xs) )

private lemma __GraphTree_edgeImage_inj : Function.Injective (__GraphTree_edgeImage i xs) := by
  intro a b h
  dsimp [__GraphTree_edgeImage] at h
  have eq : (a.val : {z : ℕ × ℕ // z.1 ≤ z.2}) = b.val :=
    sorted_sym_inj (by
      -- forget membership proofs in the walk vertices
      have z := h
      -- Sym2 equality has endpoint pairs
      rcases (Sym2.eq_iff.mp z) with c|c
      · apply Sym2.eq_iff.mpr
        left
        exact ⟨congrArg Subtype.val c.1, congrArg Subtype.val c.2⟩
      · apply Sym2.eq_iff.mpr
        right
        exact ⟨congrArg Subtype.val c.1, congrArg Subtype.val c.2⟩)
  exact Subtype.ext eq

private lemma __GraphTree_edgeImage_mem (hloop : ∀ a : ℕ, edgeNat a a ∉ walkEdges i xs)
    (e : {a // a ∈ walkEdges i xs}) :
    __GraphTree_edgeImage i xs e ∈ (walkGraph i xs).edgeSet := by
  dsimp [__GraphTree_edgeImage]
  rw [SimpleGraph.mem_edgeSet]
  rw [walkGraph_adj]
  constructor
  · intro hsame
    have vv := congrArg Subtype.val hsame
    have eqv : e.val.val.1 = e.val.val.2 := vv
    have ee : e.val = edgeNat e.val.val.1 e.val.val.1 := by
      apply Subtype.ext
      dsimp [edgeNat]
      simp
      exact Prod.ext rfl eqv.symm
    exact hloop e.val.val.1 (ee ▸ e.property)
  · have hpair : edgeNat e.val.val.1 e.val.val.2 = e.val := by
      apply Subtype.ext
      dsimp [edgeNat]
      simp [min_eq_left e.val.property, max_eq_right e.val.property]
    simpa [hpair] using e.property

private lemma __GraphTree_edgeImage_surj (hloop : ∀ a : ℕ, edgeNat a a ∉ walkEdges i xs)
    (z : Sym2 (WalkVert i xs)) (hz : z ∈ (walkGraph i xs).edgeSet) :
    ∃ e : {a // a ∈ walkEdges i xs}, __GraphTree_edgeImage i xs e = z := by
  induction z using Sym2.inductionOn with
  | _ a b =>
    have ad : (walkGraph i xs).Adj a b :=
      (SimpleGraph.mem_edgeSet _).1 hz
    have ab := (walkGraph_adj a b).1 ad
    let e0 : {u : ℕ × ℕ // u.1 ≤ u.2} := edgeNat a.val b.val
    have ee : e0 ∈ walkEdges i xs := ab.2
    refine ⟨⟨e0, ee⟩, ?_⟩
    dsimp [__GraphTree_edgeImage, e0, edgeNat]
    by_cases le : a.val ≤ b.val
    · simp [min_eq_left le, max_eq_right le]
    · have le' : b.val ≤ a.val := le_of_not_ge le
      -- endpoints are in the opposite order, Sym2 swaps
      have : s((b), (a)) = (s(a,b) : Sym2 (WalkVert i xs)) :=
        (Sym2.eq_swap)
      -- the subtype membership proofs are irrelevant
      simpa [min_eq_right le', max_eq_left le'] using this

/-- The unordered edge set of the graph of the word has exactly the number of
literal (upper-triangular) edges of the word, as soon as loops are ruled out. -/
lemma card_walkGraph_edges (hloop : ∀ a : ℕ, edgeNat a a ∉ walkEdges i xs) :
    Nat.card (walkGraph i xs).edgeSet = (walkEdges i xs).card := by
  classical
  letI : Fintype (WalkVert i xs) := Fintype.ofFinite _
  letI : Fintype {e : Sym2 (WalkVert i xs) // e ∈ (walkGraph i xs).edgeSet} :=
    Fintype.ofFinite _
  let f : {a // a ∈ walkEdges i xs} ≃ {e : Sym2 (WalkVert i xs) // e ∈ (walkGraph i xs).edgeSet} :=
    { toFun := fun e => ⟨__GraphTree_edgeImage i xs e, __GraphTree_edgeImage_mem i xs hloop e⟩
      invFun := fun z => Classical.choose (__GraphTree_edgeImage_surj i xs hloop z.val z.property)
      left_inv := by
        intro a
        have z := Classical.choose_spec (__GraphTree_edgeImage_surj i xs hloop
          (__GraphTree_edgeImage i xs a) (__GraphTree_edgeImage_mem i xs hloop a))
        exact __GraphTree_edgeImage_inj i xs z
      right_inv := by
        intro z
        apply Subtype.ext
        exact Classical.choose_spec (__GraphTree_edgeImage_surj i xs hloop z.val z.property) }
  rw [Nat.card_eq_fintype_card]
  -- the vertices and edgeSet are finite (subtypes of finite objects)
  exact (Fintype.card_congr f).symm.trans (Fintype.card_coe _)
end
end WignerSupport

namespace WignerSupport
open SimpleGraph
private lemma __GraphTree_reachable_piece (i : ℕ) (xs : List ℕ)
    (hloop : ∀ a : ℕ, edgeNat a a ∉ walkEdges i xs)
    (cur : ℕ) (ys : List ℕ)
    (he : walkEdges cur ys ⊆ walkEdges i xs)
    (hv : walkVertices cur ys ⊆ walkVertices i xs)
    (a : ℕ) (ha : a ∈ walkVertices cur ys) :
    (walkGraph i xs).Reachable
      (⟨cur, hv (walkVertices_root_mem _ _)⟩ : WalkVert i xs)
      (⟨a, hv ha⟩ : WalkVert i xs) := by
  classical
  induction ys generalizing cur with
  | nil =>
      have eq : a = cur := by simpa [walkVertices] using ha
      subst a
      exact SimpleGraph.Walk.reachable SimpleGraph.Walk.nil
  | cons j zs ih =>
    have allv : walkVertices cur (j::zs) =
          insert cur (walkVertices j zs) := walkVertices_cons _ _ _
    by_cases ac : a = cur
    · subst a
      exact SimpleGraph.Walk.reachable SimpleGraph.Walk.nil
    · have aj : a ∈ walkVertices j zs := by
        rw [allv] at ha
        simpa [ac] using ha
      have sube : walkEdges j zs ⊆ walkEdges i xs := by
        intro z hz
        apply he
        exact (by simp [walkEdges, hz])
      have subv : walkVertices j zs ⊆ walkVertices i xs := by
        intro z hz
        apply hv
        rw [allv]
        exact Finset.mem_insert_of_mem hz
      have stepmem : edgeNat cur j ∈ walkEdges i xs := by
        apply he
        simp [walkEdges]
      have ne : (⟨cur, hv (walkVertices_root_mem _ _)⟩ : WalkVert i xs) ≠
          ⟨j, subv (walkVertices_root_mem _ _)⟩ := by
        intro z
        have z' : cur = j := congrArg Subtype.val z
        subst j
        exact hloop cur stepmem
      have adj : (walkGraph i xs).Adj
          (⟨cur, hv (walkVertices_root_mem _ _)⟩ : WalkVert i xs)
          (⟨j, subv (walkVertices_root_mem _ _)⟩ : WalkVert i xs) :=
        (walkGraph_adj _ _).2 ⟨ne, stepmem⟩
      have tail := ih j sube subv aj
      exact ⟨SimpleGraph.Walk.cons adj
           (Classical.choice tail)⟩

lemma walkGraph_connected (i : ℕ) (xs : List ℕ)
    (hloop : ∀ a : ℕ, edgeNat a a ∉ walkEdges i xs) :
    (walkGraph i xs).Connected := by
  classical
  have reach (a : WalkVert i xs) :
      (walkGraph i xs).Reachable
        (⟨i, walkVertices_root_mem _ _⟩ : WalkVert i xs) a := by
    exact __GraphTree_reachable_piece i xs hloop i xs (by rfl) (by rfl) a.val a.property
  have pre : (walkGraph i xs).Preconnected := by
    intro a b
    exact (reach a).symm.trans (reach b)
  letI : Nonempty (WalkVert i xs) :=
    ⟨⟨i, walkVertices_root_mem _ _⟩⟩
  exact ⟨pre⟩

lemma walkGraph_isTree (i : ℕ) (xs : List ℕ)
    (heq : (walkVertices i xs).card = (walkEdges i xs).card + 1) :
    (walkGraph i xs).IsTree := by
  classical
  letI : Fintype (WalkVert i xs) := Fintype.ofFinite _
  have loop := walk_eq_no_self i xs heq
  apply (SimpleGraph.isTree_iff_connected_and_card).2
  refine ⟨walkGraph_connected i xs loop, ?_⟩
  rw [card_walkGraph_edges]
  · rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    omega
  · exact loop

lemma leading_walk_tree {n p : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (h : IsLeadingPath i v) :
    (walkGraph i.val (pathList v)).IsTree :=
  walkGraph_isTree _ _ (leading_walk_eq i v h.2.1 h.2.2)

end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/GraphTree.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Parity.lean
section
namespace WignerSupport
open SimpleGraph

/-- Endpoint of a rooted list walk. -/
def walkLast (i : ℕ) (xs : List ℕ) : ℕ := xs.getLastD i
@[simp] lemma walkLast_nil (i : ℕ) : walkLast i [] = i := rfl
@[simp] lemma walkLast_cons (i j : ℕ) (xs : List ℕ) :
    walkLast i (j::xs) = walkLast j xs := by
  change (j::xs).getLastD i = xs.getLastD j
  exact List.getLastD_cons

/-- The `Fin` endpoint agrees with the list endpoint, including the empty path. -/
lemma pathEnd_val_eq_walkLast {n p : ℕ} (i : Fin n) (v : Fin p → Fin n) :
    (pathEnd p i v).val = walkLast i.val (pathList v) := by
  induction p generalizing i with
  | zero => simp [walkLast]
  | succ p ih =>
    rw [pathEnd_succ, pathList_succ, walkLast_cons]
    exact ih (v 0) (Fin.tail v)

/- A very small parity lemma.  On two colors, being different amounts to
flipping parity. Keeping it on naturals (rather than subtracting in `Fin 2`)
helps when applying it to a list chain. -/
private lemma __Parity_fin2_flip {a b : Fin 2} (h : a ≠ b) :
    (b.val % 2) = (a.val + 1) % 2 := by
  have hn : a.val ≠ b.val := by
    intro e
    exact h (Fin.ext e)
  omega

/-- Colors along a chain in two colors alternate. This is useful for ruling out
odd, closed leading paths before any enumeration. -/
lemma chain_fin2_last (col : ℕ → Fin 2) (i : ℕ) (xs : List ℕ)
    (h : List.Chain (fun a b : ℕ => col a ≠ col b) i xs) :
    (col (walkLast i xs)).val % 2 = ((col i).val + xs.length) % 2 := by
  induction xs generalizing i with
  | nil => simp [walkLast]
  | cons j ys ih =>
      have hh := (List.chain_cons).1 h
      have h0 : col i ≠ col j := hh.1
      have ht : List.Chain (fun a b : ℕ => col a ≠ col b) j ys := hh.2
      have I := ih j ht
      rw [walkLast_cons]
      rw [I]
      have sw := __Parity_fin2_flip h0
      simp [List.length_cons]
      omega
end WignerSupport

namespace WignerSupport
open SimpleGraph
/-- A closed equality walk has even length. The proof fixes the tree of the
whole word and colors it by distance from the root. Subwalks are only used to
check consecutive edges; they never change the ambient tree. -/
lemma even_length_of_closed_eq_walk (i : ℕ) (xs : List ℕ)
    (heq : (walkVertices i xs).card = (walkEdges i xs).card + 1)
    (hclose : walkLast i xs = i) : 2 ∣ xs.length := by
  classical
  let G := walkGraph i xs
  have tree : G.IsTree := walkGraph_isTree i xs heq
  let root : WalkVert i xs := ⟨i, walkVertices_root_mem _ _⟩
  let C : G.Coloring (Fin 2) := tree.coloringTwoOfVert root
  let c : ℕ → Fin 2 := fun a =>
    if h : a ∈ walkVertices i xs then C ⟨a,h⟩ else 0
  have cadj {a b : ℕ} (ha : a ∈ walkVertices i xs)
      (hb : b ∈ walkVertices i xs) (hne : a ≠ b)
      (hab : edgeNat a b ∈ walkEdges i xs) : c a ≠ c b := by
    have ad : G.Adj (⟨a,ha⟩ : WalkVert i xs) ⟨b,hb⟩ := by
      apply (walkGraph_adj _ _).2
      constructor
      · intro h
        exact hne (congrArg Subtype.val h)
      · exact hab
    have d := C.valid ad
    simpa [c, ha, hb] using d
  have chainPiece (cur : ℕ) (ys : List ℕ)
      (hv : walkVertices cur ys ⊆ walkVertices i xs)
      (hed : walkEdges cur ys ⊆ walkEdges i xs) :
      List.Chain (fun a b : ℕ => c a ≠ c b) cur ys := by
    induction ys generalizing cur with
    | nil => simp [List.Chain]
    | cons j zs ih =>
      have hc : cur ∈ walkVertices i xs := hv (walkVertices_root_mem _ _)
      have hj0 : j ∈ walkVertices cur (j::zs) := by
        rw [walkVertices_cons]
        exact Finset.mem_insert_of_mem (walkVertices_root_mem _ _)
      have hj : j ∈ walkVertices i xs := hv hj0
      have e : edgeNat cur j ∈ walkEdges i xs := by
        apply hed
        simp [walkEdges]
      have ne : cur ≠ j := by
        intro eq
        subst j
        exact (walk_eq_no_self i xs heq cur) e
      have step : c cur ≠ c j := cadj hc hj ne e
      have tv : walkVertices j zs ⊆ walkVertices i xs := by
        intro a ha
        apply hv
        rw [walkVertices_cons]
        exact Finset.mem_insert_of_mem ha
      have te : walkEdges j zs ⊆ walkEdges i xs := by
        intro a ha
        apply hed
        simp [walkEdges, ha]
      exact (List.chain_cons).2 ⟨step, ih j tv te⟩
  have ch := chainPiece i xs (by intro a h; exact h) (by intro a h; exact h)
  have par := chain_fin2_last c i xs ch
  rw [hclose] at par
  have modzero : xs.length % 2 = 0 := by omega
  omega

/-- Every leading path is even.  In particular the odd moments have no
maximal equality words; this is independent of its alphabet. -/
lemma leading_even {n p : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (h : IsLeadingPath i v) : 2 ∣ p := by
  have eq := leading_walk_eq i v h.2.1 h.2.2
  have endnat : walkLast i.val (pathList v) = i.val := by
    rw [← pathEnd_val_eq_walkLast]
    exact congrArg Fin.val h.1
  have ev := even_length_of_closed_eq_walk i.val (pathList v) eq endnat
  simpa [pathList] using ev

lemma leadingWord_even {p n : ℕ} (w : Fin (p+1) → Fin n)
    (h : IsLeadingWord p n w) : 2 ∣ p := by
  exact leading_even (w 0) (Fin.tail w) h

/-- There are no Boolean leading equality patterns at odd length. -/
lemma leadPatterns_eq_empty_of_odd (p : ℕ) (ho : ¬ 2 ∣ p) :
    leadPatterns p = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hp
  rcases hp with ⟨pat, hp⟩
  rcases Finset.mem_image.mp hp with ⟨w, hw, eq⟩
  have l : IsLeadingWord p (p+1) w := (Finset.mem_filter.mp hw).2
  exact ho (leadingWord_even w l)
end WignerSupport

namespace WignerSupport
lemma walkLast_mem (i : ℕ) (xs : List ℕ) : walkLast i xs ∈ walkVertices i xs := by
  induction xs generalizing i with
  | nil => simp
  | cons j ys ih =>
    rw [walkLast_cons, walkVertices_cons]
    exact Finset.mem_insert_of_mem (ih j)

/-- The first edge of a nonempty leading closed walk is visible again in its
suffix. This is the first half of the usual first-return decomposition (the
choice of its returning index is handled separately); it is often easy to
lose it by reasoning only with cardinalities. -/
lemma leading_first_edge_mem_tail {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v) :
    edgeNat i.val (v 0).val ∈
      walkEdges (v 0).val (pathList (Fin.tail v)) := by
  have last : walkLast (v 0).val (pathList (Fin.tail v)) = i.val := by
    rw [← pathEnd_val_eq_walkLast]
    have z : pathEnd p (v 0) (Fin.tail v) = i := by
      simpa [pathEnd_succ] using h.1
    exact congrArg Fin.val z
  have mem : i.val ∈ walkVertices (v 0).val (pathList (Fin.tail v)) := by
    rw [← last]
    exact walkLast_mem _ _
  have iff := leading_old_iff i v h.2.1 h.2.2
  exact iff.1 mem

lemma leading_fibers_two {n p : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (h : IsLeadingPath i v) :
    ∀ e ∈ (Finset.univ.image (pathEdgesNat i v)),
      ((Finset.univ : Finset (Fin p)).filter
        (fun r => pathEdgesNat i v r = e)).card = 2 := by
  exact fibers_two_of_max_vertices i v (leading_even i v h) h.2.1 h.2.2
end WignerSupport

namespace WignerSupport
private lemma __Parity_eq_of_mem_card_two {α : Type*} [DecidableEq α]
    (S : Finset α) (hc : S.card = 2)
    {a b c : α} (ha : a ∈ S) (hb : b ∈ S) (hz : c ∈ S)
    (ab : a ≠ b) (ac : a ≠ c) : b = c := by
  classical
  by_contra bc
  have sub : ({a,b,c} : Finset α) ⊆ S := by
    intro x hx
    have cases : x = a ∨ x = b ∨ x = c := by simpa using hx
    rcases cases with rfl | rfl | rfl <;> assumption
  have cd : ({a,b,c} : Finset α).card = 3 := by
    simp [ab, ac, bc]
  have le := Finset.card_le_card sub
  omega

/-- The first edge has a unique further occurrence. Indices are now indices in
*the suffix*, i.e. the required full-word occurrence is `r.succ`. This is the
finite first-return index; its orientation will later be fixed using the tree
cut. -/
lemma leading_first_edge_unique {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v) :
    ∃! r : Fin p,
      pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val := by
  classical
  have mem := leading_first_edge_mem_tail i v h
  have mem' : edgeNat i.val (v 0).val ∈
       (Finset.univ.image (pathEdgesNat (v 0) (Fin.tail v))) := by
    -- the list-tail and finite-tail edge images agree
    simpa [image_pathEdges_eq_walkEdges] using mem
  rcases Finset.mem_image.mp mem' with ⟨r, hr, eqr⟩
  refine ⟨r, eqr, ?_⟩
  intro s eqs
  let e := edgeNat i.val (v 0).val
  let T : Finset (Fin (p+1)) := (Finset.univ : Finset (Fin (p+1))).filter
       (fun t => pathEdgesNat i v t = e)
  have eall : e ∈ (Finset.univ.image (pathEdgesNat i v)) := by
    apply Finset.mem_image.mpr
    exact ⟨0, Finset.mem_univ _, rfl⟩
  have cardT : T.card = 2 := leading_fibers_two i v h e eall
  have zero : (0 : Fin (p+1)) ∈ T := by
    simp [T, e]
  have rr : r.succ ∈ T := by
    have : pathEdgesNat i v r.succ = e := by simpa [e] using eqr
    simp [T, this]
  have ss : s.succ ∈ T := by
    have : pathEdgesNat i v s.succ = e := by simpa [e] using eqs
    simp [T, this]
  have rs : (r.succ : Fin (p+1)) = s.succ := by
    exact __Parity_eq_of_mem_card_two T cardT zero rr ss
      (Fin.succ_ne_zero r).symm (Fin.succ_ne_zero s).symm
  have rs' : s.succ = r.succ := rs.symm
  exact Fin.succ_inj.mp rs'
end WignerSupport

namespace WignerSupport
lemma leadPatterns_zero_card : (leadPatterns 0).card = 1 := by
  classical
  rw [← Nat.mul_one ((leadPatterns 0).card)]
  have h := card_leadingWords_eq_patterns_mul 0 1
  -- There is only one word on the singleton alphabet and it is leading.
  have allfun : ∀ w : Fin (0+1) → Fin 1, IsLeadingWord 0 1 w := by
    intro w
    unfold IsLeadingWord IsLeadingPath
    refine ⟨rfl, ?_, ?_⟩
    · intro u; exact Fin.elim0 u
    · -- its vertex set is the single root
      have only : (w (0 : Fin 1)) = (0 : Fin 1) := Subsingleton.elim _ _
      simp [pathVerticesFin, pathList]
  have onefun :
      ((Finset.univ : Finset (Fin (0+1) → Fin 1)).filter
        (fun w => IsLeadingWord 0 1 w)).card = 1 := by
    have feq : ((Finset.univ : Finset (Fin (0+1) → Fin 1)).filter
        (fun w => IsLeadingWord 0 1 w)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro w hw
      exact allfun w
    rw [feq]
    simp [Fintype.card_fun]
  calc
    (leadPatterns 0).card * 1 =
      ((Finset.univ : Finset (Fin (0+1) → Fin 1)).filter
        (fun w => IsLeadingWord 0 1 w)).card := by
          simpa [Nat.descFactorial] using h.symm
    _ = 1 := onefun
end WignerSupport

namespace WignerSupport
/-- `walk_eq_suffix` holds not only for the head of a leading contour but at
*any* position of it. The formulation with a list prefix avoids shifts between
the `Fin` position of an edge and the vertex position of its starting letter. -/
lemma walk_old_iff_at_split (i : ℕ) (xs pre : List ℕ) (a b : ℕ)
    (zs : List ℕ)
    (heq : (walkVertices i xs).card = (walkEdges i xs).card + 1)
    (hword : i :: xs = pre ++ a :: b :: zs) :
    (a ∈ walkVertices b zs ↔ edgeNat a b ∈ walkEdges b zs) := by
  have hdrop := walk_eq_drop i xs heq pre.length
  -- compute the harmless defaults using the displayed split
  have gd : (i::xs).getD pre.length i = a := by
    rw [hword]
    simp [List.getD_eq_getElem?_getD]
  have dr : (i::xs).drop (pre.length+1) = b::zs := by
    rw [hword, List.drop_append]
    simp
  dsimp at hdrop
  rw [gd] at hdrop
  have dr' : xs.drop pre.length = b::zs := by
    simpa [List.drop_succ_cons] using dr
  rw [dr'] at hdrop
  exact (walk_eq_suffix a b zs hdrop).2
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Parity.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/FirstReturn.lean
section

namespace WignerSupport

/-- The endpoint operation on rooted list-walks respects concatenation. This
is just bookkeeping for first-return arguments. -/
lemma walkLast_append (i : ℕ) (xs ys : List ℕ) :
    walkLast i (xs ++ ys) = walkLast (walkLast i xs) ys := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, walkLast_cons]
      exact ih x

/-- A literal edge of a rooted list-walk is attained between two consecutive
positions of the cons-list. This is the positional version of the finite
`walkEdges`; unlike the `Finset.image` formulation it remembers how far along
the word the occurrence sits. -/
lemma mem_walkEdges_pos (i : ℕ) (xs : List ℕ)
    (e : {z : ℕ × ℕ // z.1 ≤ z.2})
    (he : e ∈ walkEdges i xs) :
    ∃ (t : ℕ) (ht : t < xs.length),
      e = edgeNat ((i :: xs)[t]'(by simp; omega))
                  ((i :: xs)[t+1]'(by simp; omega)) := by
  induction xs generalizing i with
  | nil => simpa [walkEdges] using he
  | cons j ys ih =>
      have cases : e = edgeNat i j ∨ e ∈ walkEdges j ys := by
        simpa [walkEdges] using he
      rcases cases with h0 | htail
      · refine ⟨0, by simp, ?_⟩
        simpa using h0
      · rcases ih (i := j) htail with ⟨t, ht, hval⟩
        refine ⟨t+1, by simp; omega, ?_⟩
        -- in positions greater than zero both getElems of the cons agree
        -- with the corresponding positions in its tail
        simpa [List.getElem_cons_succ, Nat.add_assoc] using hval

/-- Reading a suffix of a `Fin` word cannot create an occurrence at its
first, already removed, position. More concretely: an edge seen in the part
after positions `r,r+1` has a suffix-word index strictly larger than `r`.
Here the suffix word is the word with letters `v 0, v 1, ...`; its edges
are the ones rooted at `v 0`. -/
lemma mem_walkEdges_after_index
    {n p : ℕ} (v : Fin (p+1) → Fin n) (r : Fin p)
    (e : {z : ℕ × ℕ // z.1 ≤ z.2})
    (he : e ∈ walkEdges (v r.succ).val ((pathList v).drop (r.val+2))) :
    ∃ s : Fin p, r.val < s.val ∧
       pathEdgesNat (v 0) (Fin.tail v) s = e := by
  classical
  let L : List ℕ := pathList v
  have hlen : L.length = p+1 := by simp [L, pathList]
  have hk : r.val + 1 < L.length := by
    rw [hlen]
    omega
  let Z : List ℕ := L.drop (r.val+2)
  have root_eq : (v r.succ).val = L[r.val+1]'(by omega) := by
    dsimp [L]
    -- values of the path list are exactly the values of the letters
    have hh := (List.getElem_ofFn
      (f := fun t : Fin (p+1) => (v t).val)
      (i := r.val+1) (by simp [pathList]))
    -- `simp` normalizes the successor `Fin` proof fields
    simpa [pathList] using hh.symm
  obtain ⟨t, ht, hv⟩ := mem_walkEdges_pos
      (v r.succ).val ((pathList v).drop (r.val+2)) e he
  have hZlen : ((pathList v).drop (r.val+2)).length =
       (p+1) - (r.val+2) := by simp [pathList]
  have bound : r.val + 1 + t < p := by
    -- t is a position in the dropped tail
    have := ht
    rw [hZlen] at this
    omega
  let s : Fin p := ⟨r.val + 1 + t, bound⟩
  refine ⟨s, by dsimp [s]; omega, ?_⟩
  -- an edge at suffix index `s` has consecutive endpoints in `L` at
  -- positions `s` and `s+1`.
  rw [pathEdges_word v s]
  have hv' := hv
  -- replace the cons-root-and-tail endpoints in `hv` by endpoints of `L`
  have first :
       (((v r.succ).val :: L.drop (r.val+2))[t]'(by
           have hvv := ht
           simp [pathList] at hvv ⊢
           omega)) =
        L[r.val+1+t]'(by rw [hlen]; omega) := by
    by_cases tz : t = 0
    · subst t
      simpa [root_eq]
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero tz
      -- inside the dropped list, getElem_drop shifts by `r+2`
      have hdrop :
          ((L.drop (r.val+2))[u]'(by
              -- length of the drop
              simp [hlen]
              have hvv := ht
              -- `ht` now is for (u+1) in the tail
              change u + 1 < ((pathList v).drop (r.val + 2)).length at hvv
              simp [pathList] at hvv ⊢
              omega)) = L[r.val+2+u]'(by rw [hlen]; omega) := by
            exact List.getElem_drop (xs:=L) (i:=r.val+2) (j:=u)
      simpa [List.getElem_cons_succ, Nat.add_assoc,
             Nat.add_left_comm, Nat.add_comm] using hdrop
  have second :
       (((v r.succ).val :: L.drop (r.val+2))[t+1]'(by simp; omega)) =
        L[r.val+1+(t+1)]'(by rw [hlen]; omega) := by
    -- index `t+1` is in the list-part of the cons
    have hdrop :
        ((L.drop (r.val+2))[t]'(by
            have hvv := ht
            simpa [L, pathList] using hvv)) =
          L[(r.val+2)+t]'(by rw [hlen]; omega) := by
        exact List.getElem_drop (xs:=L) (i:=r.val+2) (j:=t)
    simpa [L, List.getElem_cons_succ, Nat.add_assoc,
             Nat.add_left_comm, Nat.add_comm] using hdrop
  rw [first, second] at hv'
  -- Finally read those two entries of `L` as values of `v`.
  have ev1 : L[r.val+1+t]'(by rw [hlen]; omega) =
      (v s.castSucc).val := by
    dsimp [L]
    have hh := (List.getElem_ofFn
      (f := fun z : Fin (p+1) => (v z).val)
      (i := r.val+1+t) (by simp [pathList]; omega))
    simpa [pathList, s, Nat.add_assoc,
           Nat.add_left_comm, Nat.add_comm] using hh
  have ev2 : L[r.val+1+(t+1)]'(by rw [hlen]; omega) =
      (v s.succ).val := by
    dsimp [L]
    have hh := (List.getElem_ofFn
      (f := fun z : Fin (p+1) => (v z).val)
      (i := r.val+1+(t+1)) (by simp [pathList]; omega))
    simpa [pathList, s, Nat.add_assoc,
           Nat.add_left_comm, Nat.add_comm] using hh
  rw [ev1, ev2] at hv'
  exact hv'.symm

end WignerSupport

namespace WignerSupport
lemma list_split_two {α : Type*} (L : List α) (k : ℕ)
    (h : k+1 < L.length) :
    L = L.take k ++ L[k]'(by omega) :: L[k+1]'h :: L.drop (k+2) := by
  have e0 := List.take_append_drop k L
  have e1 := List.drop_eq_getElem_cons (l:=L) (i:=k) (by omega)
  have e2 := List.drop_eq_getElem_cons (l:=L) (i:=k+1) h
  -- put the two heads back into the append decomposition
  rw [e1, e2] at e0
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using e0.symm

/-- At its second (and only other) occurrence, the first edge of a leading
word is traversed **towards** the old root. The point is orientation, not
merely the multiplicity supplied by `leading_first_edge_unique`.

The proof uses the equality-walk suffix criterion: if that second occurrence
were again outward from the root, then the final root, still lying in its
right suffix, would force a *third* occurrence of the same edge. -/
lemma leading_second_edge_return {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    (v r.castSucc).val = (v 0).val ∧ (v r.succ).val = i.val := by
  classical
  let L : List ℕ := pathList v
  have len : L.length = p+1 := by simp [L, pathList]
  have kk : r.val + 1 < L.length := by rw [len]; omega
  have aget : L[r.val]'(by omega) = (v r.castSucc).val := by
    change (List.ofFn (fun z : Fin (p+1) => (v z).val))[r.val] =
       (v r.castSucc).val
    have hh := (List.getElem_ofFn
       (f := fun z : Fin (p+1) => (v z).val)
       (i := r.val) (by simp))
    rw [hh]
    congr 1
  have bget : L[r.val+1]'kk = (v r.succ).val := by
    dsimp [L] at kk ⊢
    have hh := (List.getElem_ofFn
       (f := fun z : Fin (p+1) => (v z).val)
       (i := r.val+1) (by simp))
    simpa [pathList, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh
  have orient :
      ((v r.castSucc).val = i.val ∧ (v r.succ).val = (v 0).val) ∨
      ((v r.castSucc).val = (v 0).val ∧ (v r.succ).val = i.val) := by
    have e := hr
    rw [pathEdges_word v r] at e
    exact (edgeNat_eq_iff.mp e)
  rcases orient with out | back
  · exfalso
    -- split the full natural word at this occurrence
    let Z : List ℕ := L.drop (r.val+2)
    have splitL : L = L.take r.val ++
        (v r.castSucc).val :: (v r.succ).val :: Z := by
      have sp := list_split_two L r.val kk
      simpa [aget, bget, Z] using sp
    have splitFull : i.val :: pathList v =
        (i.val :: L.take r.val) ++
          (v r.castSucc).val :: (v r.succ).val :: Z := by
      simpa [L] using congrArg (List.cons i.val) splitL
    have eqwalk :
        (walkVertices i.val (pathList v)).card =
          (walkEdges i.val (pathList v)).card + 1 :=
      leading_walk_eq i v h.2.1 h.2.2
    have iff := walk_old_iff_at_split i.val (pathList v)
       (i.val :: L.take r.val) (v r.castSucc).val (v r.succ).val Z
       eqwalk splitFull
    have closed : walkLast i.val (pathList v) = i.val := by
      rw [← pathEnd_val_eq_walkLast]
      exact congrArg Fin.val h.1
    have suffixLast : walkLast (v r.succ).val Z = i.val := by
      -- peel off the prefix and the two displayed letters from the endpoint
      -- of the closed walk
      rw [show pathList v = L from rfl, splitL,
          walkLast_append, walkLast_cons, walkLast_cons] at closed
      exact closed
    have oldvertex : (v r.castSucc).val ∈
          walkVertices (v r.succ).val Z := by
      rw [out.1]
      rw [← suffixLast]
      exact walkLast_mem _ _
    have later : edgeNat (v r.castSucc).val (v r.succ).val ∈
          walkEdges (v r.succ).val Z := iff.1 oldvertex
    have later' : edgeNat i.val (v 0).val ∈
          walkEdges (v r.succ).val ((pathList v).drop (r.val+2)) := by
      have zz : Z = (pathList v).drop (r.val+2) := by rfl
      rw [← zz]
      simpa [out.1, out.2] using later
    obtain ⟨s, gt, hs⟩ := mem_walkEdges_after_index v r
        (edgeNat i.val (v 0).val) later'
    have uniq := (leading_first_edge_unique i v h)
    rcases uniq with ⟨r0, hr0, only⟩
    have r_eq : r = r0 := (only r hr)
    have s_eq : s = r0 := (only s hs)
    have eqrs : r = s := r_eq.trans s_eq.symm
    have neq : r ≠ s := by
      intro q
      have := gt
      simpa [q] using this
    exact neq eqrs
  · exact back

end WignerSupport

namespace WignerSupport
/-- Packaged first return: both the index and its direction. Keeping the
index in `Fin p` (edges of the word with the head removed) is helpful in
the Catalan split: `r.val` is the length of the child excursion. -/
lemma leading_first_return {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v) :
    ∃! r : Fin p,
       pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val ∧
       (v r.castSucc).val = (v 0).val ∧ (v r.succ).val = i.val := by
  classical
  rcases leading_first_edge_unique i v h with ⟨r, hr, hu⟩
  refine ⟨r, ⟨hr, leading_second_edge_return i v h r hr⟩, ?_⟩
  intro s hs
  exact hu s hs.1
end WignerSupport

namespace WignerSupport
open SimpleGraph
/-- Evenness also applies to a *subwalk* closed in a fixed equality-tree. It
is important not to assert that an arbitrary subwalk itself satisfies the
cardinality equality. We color the ambient tree once and restrict its proper
two-coloring along the displayed subwalk. -/
lemma even_length_of_subwalk (i : ℕ) (xs : List ℕ)
    (heq : (walkVertices i xs).card = (walkEdges i xs).card + 1)
    (cur : ℕ) (ys : List ℕ)
    (hv : walkVertices cur ys ⊆ walkVertices i xs)
    (hed : walkEdges cur ys ⊆ walkEdges i xs)
    (hclose : walkLast cur ys = cur) : 2 ∣ ys.length := by
  classical
  let G := walkGraph i xs
  have tree : G.IsTree := walkGraph_isTree i xs heq
  let root : WalkVert i xs := ⟨i, walkVertices_root_mem _ _⟩
  let C : G.Coloring (Fin 2) := tree.coloringTwoOfVert root
  let c : ℕ → Fin 2 := fun a =>
    if h : a ∈ walkVertices i xs then C ⟨a,h⟩ else 0
  have cadj {a b : ℕ} (ha : a ∈ walkVertices i xs)
      (hb : b ∈ walkVertices i xs) (hne : a ≠ b)
      (hab : edgeNat a b ∈ walkEdges i xs) : c a ≠ c b := by
    have ad : G.Adj (⟨a,ha⟩ : WalkVert i xs) ⟨b,hb⟩ := by
      apply (walkGraph_adj _ _).2
      constructor
      · intro h
        exact hne (congrArg Subtype.val h)
      · exact hab
    have d := C.valid ad
    simpa [c, ha, hb] using d
  have chainPiece (u : ℕ) (zs : List ℕ)
      (hsV : walkVertices u zs ⊆ walkVertices i xs)
      (hsE : walkEdges u zs ⊆ walkEdges i xs) :
      List.Chain (fun a b : ℕ => c a ≠ c b) u zs := by
    induction zs generalizing u with
    | nil => simp [List.Chain]
    | cons j tl ih =>
      have hu : u ∈ walkVertices i xs := hsV (walkVertices_root_mem _ _)
      have hj0 : j ∈ walkVertices u (j::tl) := by
        rw [walkVertices_cons]
        exact Finset.mem_insert_of_mem (walkVertices_root_mem _ _)
      have hj : j ∈ walkVertices i xs := hsV hj0
      have ee : edgeNat u j ∈ walkEdges i xs := by
        apply hsE
        simp [walkEdges]
      have ne : u ≠ j := by
        intro q
        subst j
        exact (walk_eq_no_self i xs heq u) ee
      have tv : walkVertices j tl ⊆ walkVertices i xs := by
        intro a ha
        apply hsV
        rw [walkVertices_cons]
        exact Finset.mem_insert_of_mem ha
      have te : walkEdges j tl ⊆ walkEdges i xs := by
        intro a ha
        apply hsE
        simp [walkEdges, ha]
      exact (List.chain_cons).2 ⟨cadj hu hj ne ee, ih j tv te⟩
  have ch := chainPiece cur ys hv hed
  have par := chain_fin2_last c cur ys ch
  rw [hclose] at par
  have modzero : ys.length % 2 = 0 := by omega
  omega
end WignerSupport

namespace WignerSupport
lemma walkVertices_take_subset (i : ℕ) (xs : List ℕ) (k : ℕ) :
    walkVertices i (xs.take k) ⊆ walkVertices i xs := by
  classical
  simp only [walkVertices]
  intro a ha
  simp at ha ⊢
  rcases ha with ha | ha
  · exact Or.inl ha
  · exact Or.inr (List.mem_of_mem_take ha)

lemma walkEdges_take_subset (i : ℕ) (xs : List ℕ) (k : ℕ) :
    walkEdges i (xs.take k) ⊆ walkEdges i xs := by
  classical
  induction k generalizing i xs with
  | zero => simp
  | succ k ih =>
    cases xs with
    | nil => simp
    | cons j tl =>
      change insert (edgeNat i j) (walkEdges j (tl.take k)) ⊆
        insert (edgeNat i j) (walkEdges j tl)
      intro a ha
      simp at ha ⊢
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (ih j tl ha)

lemma walkVertices_tail_subset (i j : ℕ) (xs : List ℕ) :
    walkVertices j xs ⊆ walkVertices i (j::xs) := by
  classical
  rw [walkVertices_cons]
  exact Finset.subset_insert _ _
lemma walkEdges_tail_subset (i j : ℕ) (xs : List ℕ) :
    walkEdges j xs ⊆ walkEdges i (j::xs) := by
  classical
  intro e he
  simp [walkEdges, he]

/-- The child part of a first-return split has even length. This is still an
ambient-tree assertion (no assertion yet that the child and root alphabets
become disjoint after the cut). -/
lemma leading_first_return_even {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    2 ∣ r.val := by
  classical
  let T : List ℕ := pathList (Fin.tail v)
  let mid : List ℕ := T.take r.val
  have tl : pathList v = (v 0).val :: T := pathList_succ v
  have mlast : walkLast (v 0).val mid = (v 0).val := by
    -- the last vertex before the returning edge is exactly the child again
    have back := (leading_second_edge_return i v h r hr).1
    by_cases z : r.val = 0
    · simp [mid, z]
    · obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero z
      -- the last element of the prefix is the letter at position `u` of T,
      -- namely `v r.castSucc`
      have ulen : u < T.length := by simp [T, pathList]; omega
      have tk : T.take r.val = T.take u ++ [T[u]'ulen] := by
        rw [hu]
        simpa using (List.take_concat_get' T u ulen).symm
      have elem : T[u]'ulen = (v r.castSucc).val := by
        change (List.ofFn (fun z : Fin p => ((Fin.tail v) z).val))[u] = _
        have hh := (List.getElem_ofFn
            (f := fun z : Fin p => ((Fin.tail v) z).val)
            (i:=u) (by simp [pathList]; omega))
        -- both indices name the same position of `v`
        have cast : (Fin.tail v ⟨u, by omega⟩) = v r.castSucc := by
          change v ⟨u+1, by omega⟩ = v r.castSucc
          congr 1
          apply Fin.ext
          simp [hu]
        calc
          _ = ((Fin.tail v) ⟨u, by omega⟩).val := by
            convert hh using 1 <;> rfl
          _ = _ := congrArg (fun z : Fin n => z.val) cast
      -- endpoint of a nonempty prefix is its final letter
      simp [mid, tk, walkLast_append, elem, back]
  have amb : (walkVertices i.val (pathList v)).card =
      (walkEdges i.val (pathList v)).card + 1 :=
    leading_walk_eq i v h.2.1 h.2.2
  have hv1 : walkVertices (v 0).val mid ⊆
       walkVertices i.val (pathList v) := by
    have a := walkVertices_take_subset (v 0).val T r.val
    have b := walkVertices_tail_subset i.val (v 0).val T
    rw [tl]
    exact fun x hx => b (a hx)
  have he1 : walkEdges (v 0).val mid ⊆
       walkEdges i.val (pathList v) := by
    have a := walkEdges_take_subset (v 0).val T r.val
    have b := walkEdges_tail_subset i.val (v 0).val T
    rw [tl]
    exact fun x hx => b (a hx)
  have ev := even_length_of_subwalk i.val (pathList v) amb
     (v 0).val mid hv1 he1 mlast
  have le : r.val ≤ T.length := by
    simpa [T, pathList] using (Nat.le_of_lt r.isLt)
  have lm : mid.length = r.val := by
    dsimp [mid]
    exact List.length_take_of_le le
  simpa [lm] using ev
end WignerSupport

namespace WignerSupport
/-- In particular the bridge picked by a first-return split is a genuine
edge, not a disguised loop. -/
lemma leading_head_ne {n p : ℕ} (i : Fin n) (v : Fin (p+1) → Fin n)
    (h : IsLeadingPath i v) : (v 0).val ≠ i.val := by
  intro bad
  have mem : edgeNat i.val (v 0).val ∈ walkEdges i.val (pathList v) := by
    rw [pathList_succ]
    simp [walkEdges]
  have noself := leading_no_self i v h.2.1 h.2.2 i.val
  apply noself
  simpa [bad]
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/FirstReturn.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Bridge.lean
section
open SimpleGraph
open scoped Sym2
namespace WignerSupport

/-- An edge met in the open child excursion of a first-return split has a
suffix index before the returning index.  Keeping the strict inequality is
important: the returning edge is not part of the excursion. -/
lemma mem_childEdges_before_index {n p : ℕ}
    (v : Fin (p+1) → Fin n) (r : Fin p)
    (e : {z : ℕ × ℕ // z.1 ≤ z.2})
    (he : e ∈ walkEdges (v 0).val
       ((pathList (Fin.tail v)).take r.val)) :
    ∃ s : Fin p, s.val < r.val ∧
      pathEdgesNat (v 0) (Fin.tail v) s = e := by
  classical
  obtain ⟨t, ht, hv⟩ := mem_walkEdges_pos (v 0).val
       ((pathList (Fin.tail v)).take r.val) e he
  have rle : r.val ≤ (pathList (Fin.tail v)).length := by
    simp [pathList]
  have lenmid : ((pathList (Fin.tail v)).take r.val).length = r.val :=
    List.length_take_of_le rle
  have tr : t < r.val := by simpa [lenmid] using ht
  let s : Fin p := ⟨t, lt_trans tr r.isLt⟩
  refine ⟨s, tr, ?_⟩
  rw [pathEdges_word v s]
  have hv' := hv
  -- compute the two positions directly in the cons list.  This avoids
  -- transports of the `getElem` bound through a dependent equality of takes.
  have aidx :
       (((v 0).val :: (pathList (Fin.tail v)).take r.val)[t]'(by
          simp [lenmid]; omega)) =
         (v s.castSucc).val := by
    by_cases tz : t = 0
    · subst t
      simp [s]
    · obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero tz
      subst t
      rw [List.getElem_cons_succ]
      rw [List.getElem_take]
      have hh := (List.getElem_ofFn
        (f := fun z : Fin p => ((Fin.tail v) z).val)
        (i := u) (by simp [pathList]; omega))
      -- both successor indices refer to the same element of `v`
      simpa [pathList, s, Fin.tail, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hh
  have bidx :
       (((v 0).val :: (pathList (Fin.tail v)).take r.val)[t+1]'(by
          simp [lenmid]; omega)) =
         (v s.succ).val := by
    rw [List.getElem_cons_succ]
    rw [List.getElem_take]
    have hh := (List.getElem_ofFn
      (f := fun z : Fin p => ((Fin.tail v) z).val)
      (i := t) (by simp [pathList]; omega))
    simpa [pathList, s, Fin.tail, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hh
  rw [aidx, bidx] at hv'
  exact hv'.symm

end WignerSupport

namespace WignerSupport
/-- Neither side of a first-return split uses the root edge internally.  This
is stronger than saying it is first: in a leading word every literal edge has
*fibre two*, so after the return there is no third copy either. -/
lemma leading_split_edge_not_mem {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    edgeNat i.val (v 0).val ∉
       walkEdges (v 0).val ((pathList (Fin.tail v)).take r.val) ∧
    edgeNat i.val (v 0).val ∉
       walkEdges i.val ((pathList (Fin.tail v)).drop (r.val+1)) := by
  classical
  have uniq := leading_first_edge_unique i v h
  rcases uniq with ⟨r0, hr0, only⟩
  have rr0 : r = r0 := only r hr
  have child : edgeNat i.val (v 0).val ∉
       walkEdges (v 0).val ((pathList (Fin.tail v)).take r.val) := by
    intro bad
    obtain ⟨s, lt, hs⟩ :=
      mem_childEdges_before_index v r (edgeNat i.val (v 0).val) bad
    have eq : s = r0 := only s hs
    have sr : s = r := eq.trans rr0.symm
    have : s.val < r.val := lt
    simpa [sr] using this
  refine ⟨child, ?_⟩
  intro bad
  have back := (leading_second_edge_return i v h r hr).2
  have he : edgeNat i.val (v 0).val ∈
       walkEdges (v r.succ).val ((pathList v).drop (r.val+2)) := by
    have dr : (pathList v).drop (r.val+2) =
        (pathList (Fin.tail v)).drop (r.val+1) := by
      rw [pathList_succ]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [back, dr]
    exact bad
  obtain ⟨s, gt, hs⟩ := mem_walkEdges_after_index v r
       (edgeNat i.val (v 0).val) he
  have eq : s = r0 := only s hs
  have sr : s = r := eq.trans rr0.symm
  have : r.val < s.val := gt
  simpa [sr] using this
end WignerSupport

namespace WignerSupport
/-- Both pieces of the split are pieces of the ambient word. -/
lemma leading_split_subsets {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    (walkEdges (v 0).val ((pathList (Fin.tail v)).take r.val) ⊆
       walkEdges i.val (pathList v)) ∧
    (walkVertices (v 0).val ((pathList (Fin.tail v)).take r.val) ⊆
       walkVertices i.val (pathList v)) ∧
    (walkEdges i.val ((pathList (Fin.tail v)).drop (r.val+1)) ⊆
       walkEdges i.val (pathList v)) ∧
    (walkVertices i.val ((pathList (Fin.tail v)).drop (r.val+1)) ⊆
       walkVertices i.val (pathList v)) := by
  classical
  let T : List ℕ := pathList (Fin.tail v)
  have tl : pathList v = (v 0).val :: T := pathList_succ v
  have chE : walkEdges (v 0).val (T.take r.val) ⊆
       walkEdges i.val (pathList v) := by
    have a := walkEdges_take_subset (v 0).val T r.val
    have b := walkEdges_tail_subset i.val (v 0).val T
    rw [tl]
    exact fun x hx => b (a hx)
  have chV : walkVertices (v 0).val (T.take r.val) ⊆
       walkVertices i.val (pathList v) := by
    have a := walkVertices_take_subset (v 0).val T r.val
    have b := walkVertices_tail_subset i.val (v 0).val T
    rw [tl]
    exact fun x hx => b (a hx)
  refine ⟨chE, chV, ?_, ?_⟩
  · -- every trailing edge has a (strictly) later suffix index
    intro e he
    have back := (leading_second_edge_return i v h r hr).2
    have he' : e ∈ walkEdges (v r.succ).val
        ((pathList v).drop (r.val+2)) := by
      have dr : (pathList v).drop (r.val+2) = T.drop (r.val+1) := by
        dsimp [T]
        rw [pathList_succ]
        simp
      rw [back, dr]
      exact he
    obtain ⟨s, gt, hs⟩ := mem_walkEdges_after_index v r e he'
    -- a suffix edge is the successor full edge
    have full : pathEdgesNat i v s.succ = e := by simpa using hs
    have memim : e ∈ (Finset.univ.image (pathEdgesNat i v)) :=
      Finset.mem_image.mpr ⟨s.succ, Finset.mem_univ _, full⟩
    simpa [image_pathEdges_eq_walkEdges] using memim
  · -- and its letters occur literally in the full word
    intro a ha
    have cases : a = i.val ∨ a ∈ (T.drop (r.val+1)) := by
      simpa [walkVertices] using ha
    rcases cases with hroot | ha'
    · subst a; exact walkVertices_root_mem _ _
    · have inT : a ∈ T := List.mem_of_mem_drop ha'
      have inv : (v 0).val ∈ ((v 0).val :: T) := by simp
      have inL : a ∈ pathList v := by rw [tl]; simp [inT]
      exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr inL)
end WignerSupport

namespace WignerSupport
open SimpleGraph
open scoped Sym2
/-- A piece not using a literal edge is reachable in the graph with that
edge deleted.  `walkGraph` uses subtyped natural vertices whereas
`deleteEdges` uses `Sym2`; the conversion of sorted pairs is the little
point of this lemma. -/
lemma reachable_piece_deleteEdge
    (i : ℕ) (xs : List ℕ)
    (hloop : ∀ a : ℕ, edgeNat a a ∉ walkEdges i xs)
    (u v : ℕ) (hu : u ∈ walkVertices i xs) (hv₀ : v ∈ walkVertices i xs)
    (cur : ℕ) (ys : List ℕ)
    (heSub : walkEdges cur ys ⊆ walkEdges i xs)
    (hvSub : walkVertices cur ys ⊆ walkVertices i xs)
    (avoid : edgeNat u v ∉ walkEdges cur ys)
    (a : ℕ) (ha : a ∈ walkVertices cur ys) :
    ((walkGraph i xs).deleteEdges
       {s( (⟨u, hu⟩ : WalkVert i xs), (⟨v, hv₀⟩ : WalkVert i xs))}).Reachable
       (⟨cur, hvSub (walkVertices_root_mem _ _)⟩ : WalkVert i xs)
       (⟨a, hvSub ha⟩ : WalkVert i xs) := by
  classical
  induction ys generalizing cur with
  | nil =>
      have eq : a = cur := by simpa [walkVertices] using ha
      subst a
      exact SimpleGraph.Walk.reachable SimpleGraph.Walk.nil
  | cons j zs ih =>
    have allv : walkVertices cur (j::zs) =
           insert cur (walkVertices j zs) := walkVertices_cons _ _ _
    by_cases ac : a = cur
    · subst a
      exact SimpleGraph.Walk.reachable SimpleGraph.Walk.nil
    · have aj : a ∈ walkVertices j zs := by
        rw [allv] at ha
        simpa [ac] using ha
      have sube : walkEdges j zs ⊆ walkEdges i xs := by
        intro z hz
        apply heSub
        simp [walkEdges, hz]
      have subv : walkVertices j zs ⊆ walkVertices i xs := by
        intro z hz
        apply hvSub
        rw [allv]
        exact Finset.mem_insert_of_mem hz
      have stepmem0 : edgeNat cur j ∈ walkEdges cur (j::zs) := by
        simp [walkEdges]
      have stepmem : edgeNat cur j ∈ walkEdges i xs := heSub stepmem0
      have tailavoid : edgeNat u v ∉ walkEdges j zs := by
        intro e
        apply avoid
        exact (by simp [walkEdges, e])
      have stepavoid : edgeNat u v ≠ edgeNat cur j := by
        intro eq
        apply avoid
        have ee : edgeNat u v ∈ walkEdges cur (j::zs) := by
          rw [eq]
          exact stepmem0
        exact ee
      have nevert :
          (⟨cur, hvSub (walkVertices_root_mem _ _)⟩ : WalkVert i xs) ≠
            ⟨j, subv (walkVertices_root_mem _ _)⟩ := by
        intro z
        have z' : cur = j := congrArg Subtype.val z
        subst j
        exact hloop cur stepmem
      have symne :
          s( (⟨cur, hvSub (walkVertices_root_mem _ _)⟩ : WalkVert i xs),
             (⟨j, subv (walkVertices_root_mem _ _)⟩ : WalkVert i xs)) ∉
          ({s( (⟨u, hu⟩ : WalkVert i xs), (⟨v, hv₀⟩ : WalkVert i xs))} :
               Set (Sym2 (WalkVert i xs))) := by
        intro hmem
        have eqsym :
          s( (⟨cur, hvSub (walkVertices_root_mem _ _)⟩ : WalkVert i xs),
             (⟨j, subv (walkVertices_root_mem _ _)⟩ : WalkVert i xs)) =
          s( (⟨u, hu⟩ : WalkVert i xs), (⟨v, hv₀⟩ : WalkVert i xs)) := by
            simpa using hmem
        rcases (Sym2.eq_iff.mp eqsym) with hh | hh
        · have h1 : cur = u := congrArg Subtype.val hh.1
          have h2 : j = v := congrArg Subtype.val hh.2
          exact stepavoid (by simp [h1, h2, edgeNat_comm])
        · have h1 : cur = v := congrArg Subtype.val hh.1
          have h2 : j = u := congrArg Subtype.val hh.2
          exact stepavoid (by simp [h1, h2, edgeNat_comm])
      have adjG : (walkGraph i xs).Adj
          (⟨cur, hvSub (walkVertices_root_mem _ _)⟩ : WalkVert i xs)
          (⟨j, subv (walkVertices_root_mem _ _)⟩ : WalkVert i xs) :=
        (walkGraph_adj _ _).2 ⟨nevert, stepmem⟩
      have adj : ((walkGraph i xs).deleteEdges
         {s( (⟨u, hu⟩ : WalkVert i xs), (⟨v, hv₀⟩ : WalkVert i xs))}).Adj
          (⟨cur, hvSub (walkVertices_root_mem _ _)⟩ : WalkVert i xs)
          (⟨j, subv (walkVertices_root_mem _ _)⟩ : WalkVert i xs) :=
        (SimpleGraph.deleteEdges_adj).2 ⟨adjG, symne⟩
      have tail := ih j sube subv tailavoid aj
      exact ⟨SimpleGraph.Walk.cons adj (Classical.choice tail)⟩
end WignerSupport

namespace WignerSupport
open SimpleGraph
open scoped Sym2
/-- The open child excursion and the remaining root word of a first return
have disjoint alphabets.  They are in different components after the bridge
`i--v₀` is removed from the equality tree. -/
lemma leading_split_vertices_disjoint {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    Disjoint
      (walkVertices (v 0).val ((pathList (Fin.tail v)).take r.val))
      (walkVertices i.val ((pathList (Fin.tail v)).drop (r.val+1))) := by
  classical
  let xs : List ℕ := pathList v
  have loop : ∀ a : ℕ, edgeNat a a ∉ walkEdges i.val xs :=
     leading_no_self i v h.2.1 h.2.2
  have tree : (walkGraph i.val xs).IsTree := leading_walk_tree i v h
  have sub := leading_split_subsets i v h r hr
  have no := leading_split_edge_not_mem i v h r hr
  let mid : List ℕ := (pathList (Fin.tail v)).take r.val
  let rest : List ℕ := (pathList (Fin.tail v)).drop (r.val+1)
  have chE : walkEdges (v 0).val mid ⊆ walkEdges i.val xs := sub.1
  have chV : walkVertices (v 0).val mid ⊆ walkVertices i.val xs := sub.2.1
  have roE : walkEdges i.val rest ⊆ walkEdges i.val xs := sub.2.2.1
  have roV : walkVertices i.val rest ⊆ walkVertices i.val xs := sub.2.2.2
  have avu : i.val ∈ walkVertices i.val xs := walkVertices_root_mem _ _
  have avv : (v 0).val ∈ walkVertices i.val xs := by
    have : (v 0).val ∈ pathList v := by
      rw [pathList_succ]
      simp
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr this)
  let I : WalkVert i.val xs := ⟨i.val, avu⟩
  let J : WalkVert i.val xs := ⟨(v 0).val, avv⟩
  have edgeM : edgeNat i.val (v 0).val ∈ walkEdges i.val xs := by
    dsimp [xs]
    rw [pathList_succ]
    simp [walkEdges]
  have headne : (v 0).val ≠ i.val := leading_head_ne i v h
  have Ine : I ≠ J := by
    intro eq
    exact headne (congrArg Subtype.val eq).symm
  have adj : (walkGraph i.val xs).Adj I J :=
     (walkGraph_adj _ _).2 ⟨Ine, edgeM⟩
  have es : s(I,J) ∈ (walkGraph i.val xs).edgeSet :=
     (SimpleGraph.mem_edgeSet _).2 adj
  have bridge : (walkGraph i.val xs).IsBridge s(I,J) :=
     (SimpleGraph.isAcyclic_iff_forall_isBridge.mp tree.isAcyclic) es
  have notreach : ¬ ((walkGraph i.val xs).deleteEdges {s(I,J)}).Reachable I J :=
     (SimpleGraph.isBridge_iff).1 bridge
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have ra := reachable_piece_deleteEdge i.val xs loop
        i.val (v 0).val avu avv
        i.val rest roE roV no.2 a hb
  have ca := reachable_piece_deleteEdge i.val xs loop
        i.val (v 0).val avu avv
        (v 0).val mid chE chV no.1 a ha
  -- both reach the same subtyped vertex in the deleted graph
  apply notreach
  have RI : I =
       (⟨i.val, roV (walkVertices_root_mem _ _)⟩ : WalkVert i.val xs) := rfl
  have RJ : J =
       (⟨(v 0).val, chV (walkVertices_root_mem _ _)⟩ : WalkVert i.val xs) := rfl
  have XX : (⟨a, roV hb⟩ : WalkVert i.val xs) =
            (⟨a, chV ha⟩ : WalkVert i.val xs) := rfl
  -- concatenate the two routes, reversing the child one
  exact (by
    simpa [I, J] using (ra.trans ca.symm) :
      ((walkGraph i.val xs).deleteEdges {s(I,J)}).Reachable I J)
end WignerSupport
namespace WignerSupport
/-- Endpoints of the two open pieces.  These are honest closed walks; the
only omitted edges are the outward bridge and its returning copy. -/
lemma leading_split_child_closed {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    walkLast (v 0).val ((pathList (Fin.tail v)).take r.val) = (v 0).val := by
  classical
  let T : List ℕ := pathList (Fin.tail v)
  let mid : List ℕ := T.take r.val
  change walkLast (v 0).val mid = (v 0).val
  have back := (leading_second_edge_return i v h r hr).1
  by_cases z : r.val = 0
  · simp [mid, z]
  · obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero z
    have ulen : u < T.length := by
      simp [T, pathList]
      omega
    have tk : T.take r.val = T.take u ++ [T[u]'ulen] := by
      rw [hu]
      simpa using (List.take_concat_get' T u ulen).symm
    have elem : T[u]'ulen = (v r.castSucc).val := by
      change (List.ofFn (fun z : Fin p => ((Fin.tail v) z).val))[u] = _
      have hh := (List.getElem_ofFn
          (f := fun z : Fin p => ((Fin.tail v) z).val)
          (i:=u) (by simp [pathList]; omega))
      have cast : (Fin.tail v ⟨u, by omega⟩) = v r.castSucc := by
        change v ⟨u+1, by omega⟩ = v r.castSucc
        congr 1
        apply Fin.ext
        simp [hu]
      calc
        _ = ((Fin.tail v) ⟨u, by omega⟩).val := by
          convert hh using 1 <;> rfl
        _ = _ := congrArg (fun z : Fin n => z.val) cast
    simp [mid, tk, walkLast_append, elem, back]

lemma leading_split_root_closed {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    walkLast i.val ((pathList (Fin.tail v)).drop (r.val+1)) = i.val := by
  classical
  let T : List ℕ := pathList (Fin.tail v)
  let mid : List ℕ := T.take r.val
  let rest : List ℕ := T.drop (r.val+1)
  have rlt : r.val < T.length := by simp [T, pathList]
  -- the letter immediately after `mid` is the end of the returning edge
  have ret : T[r.val]'rlt = i.val := by
    have back := (leading_second_edge_return i v h r hr).2
    change (List.ofFn (fun z : Fin p => ((Fin.tail v) z).val))[r.val] = _
    have hh := (List.getElem_ofFn
      (f := fun z : Fin p => ((Fin.tail v) z).val)
      (i:=r.val) (by simp [pathList]))
    calc
      _ = ((Fin.tail v) ⟨r.val, r.isLt⟩).val := by
        convert hh using 1 <;> rfl
      _ = (v r.succ).val := rfl
      _ = _ := back
  have splitT : T = T.take r.val ++ T[r.val]'rlt :: T.drop (r.val+1) := by
    have d := List.drop_eq_getElem_cons (l:=T) (i:=r.val) rlt
    have ta := List.take_append_drop r.val T
    rw [d] at ta
    exact ta.symm
  have closed : walkLast i.val (pathList v) = i.val := by
    rw [← pathEnd_val_eq_walkLast]
    exact congrArg Fin.val h.1
  rw [pathList_succ] at closed
  -- peel the bridge, the child prefix, and the return letter from the closed word
  rw [show pathList (Fin.tail v) = T from rfl, splitT,
      walkLast_cons, walkLast_append, walkLast_cons] at closed
  -- after the prefix we see the return letter `i`
  rw [ret] at closed
  simpa [rest] using closed
end WignerSupport
namespace WignerSupport
lemma walkEdges_append (cur : ℕ) (as bs : List ℕ) :
    walkEdges cur (as ++ bs) =
      walkEdges cur as ∪ walkEdges (walkLast cur as) bs := by
  induction as generalizing cur with
  | nil => simp [walkEdges, walkLast]
  | cons j tl ih =>
      simp [walkEdges, walkLast_cons, ih, Finset.insert_union]

lemma walkVertices_append (cur : ℕ) (as bs : List ℕ) :
    walkVertices cur (as ++ bs) =
      walkVertices cur as ∪ walkVertices (walkLast cur as) bs := by
  classical
  -- the old endpoint is already a vertex of the prefix
  induction as generalizing cur with
  | nil => simp [walkVertices]
  | cons j tl ih =>
      simp [walkVertices_cons, ih, Finset.insert_union]

/-- In fact the finite edge set of the full word is obtained by adjoining
just the bridge to the edge sets of the two pieces. -/
lemma leading_split_edges_union {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    walkEdges i.val (pathList v) =
      insert (edgeNat i.val (v 0).val)
       (walkEdges (v 0).val ((pathList (Fin.tail v)).take r.val) ∪
        walkEdges i.val ((pathList (Fin.tail v)).drop (r.val+1))) := by
  classical
  let T : List ℕ := pathList (Fin.tail v)
  let mid : List ℕ := T.take r.val
  let rest : List ℕ := T.drop (r.val+1)
  have rlt : r.val < T.length := by simp [T, pathList]
  have ret : T[r.val]'rlt = i.val := by
    have back := (leading_second_edge_return i v h r hr).2
    change (List.ofFn (fun z : Fin p => ((Fin.tail v) z).val))[r.val] = _
    have hh := (List.getElem_ofFn
      (f := fun z : Fin p => ((Fin.tail v) z).val)
      (i:=r.val) (by simp [pathList]))
    calc
      _ = ((Fin.tail v) ⟨r.val, r.isLt⟩).val := by convert hh using 1 <;> rfl
      _ = (v r.succ).val := rfl
      _ = _ := back
  have splitT : T = mid ++ i.val :: rest := by
    have d := List.drop_eq_getElem_cons (l:=T) (i:=r.val) rlt
    have ta := List.take_append_drop r.val T
    rw [d] at ta
    simpa [mid, rest, ret] using ta.symm
  have childLast := leading_split_child_closed i v h r hr
  change walkEdges i.val (pathList v) =
      insert (edgeNat i.val (v 0).val)
       (walkEdges (v 0).val mid ∪ walkEdges i.val rest)
  rw [pathList_succ, show pathList (Fin.tail v) = T from rfl, splitT]
  rw [walkEdges_cons, walkEdges_append]
  -- the endpoint of `mid` is the child
  change walkLast (v 0).val mid = _ at childLast
  rw [childLast]
  simp [walkEdges, edgeNat_comm, Finset.union_assoc,
    Finset.union_left_comm, Finset.union_comm]

lemma leading_split_edges_disjoint {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    Disjoint
       (walkEdges (v 0).val ((pathList (Fin.tail v)).take r.val))
       (walkEdges i.val ((pathList (Fin.tail v)).drop (r.val+1))) := by
  classical
  have vd := leading_split_vertices_disjoint i v h r hr
  apply Finset.disjoint_left.mpr
  intro e h1 h2
  have a1 := (walkEdges_endpoints _ _ e h1).1
  have a2 := (walkEdges_endpoints _ _ e h2).1
  exact (Finset.disjoint_left.mp vd) a1 a2
end WignerSupport
namespace WignerSupport
lemma leading_split_vertices_union {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    walkVertices i.val (pathList v) =
       walkVertices (v 0).val ((pathList (Fin.tail v)).take r.val) ∪
       walkVertices i.val ((pathList (Fin.tail v)).drop (r.val+1)) := by
  classical
  let T : List ℕ := pathList (Fin.tail v)
  let mid : List ℕ := T.take r.val
  let rest : List ℕ := T.drop (r.val+1)
  have rlt : r.val < T.length := by simp [T, pathList]
  have ret : T[r.val]'rlt = i.val := by
    have back := (leading_second_edge_return i v h r hr).2
    change (List.ofFn (fun z : Fin p => ((Fin.tail v) z).val))[r.val] = _
    have hh := (List.getElem_ofFn
      (f := fun z : Fin p => ((Fin.tail v) z).val)
      (i:=r.val) (by simp [pathList]))
    calc
      _ = ((Fin.tail v) ⟨r.val, r.isLt⟩).val := by convert hh using 1 <;> rfl
      _ = (v r.succ).val := rfl
      _ = _ := back
  have splitT : T = mid ++ i.val :: rest := by
    have d := List.drop_eq_getElem_cons (l:=T) (i:=r.val) rlt
    have ta := List.take_append_drop r.val T
    rw [d] at ta
    simpa [mid, rest, ret] using ta.symm
  have childLast := leading_split_child_closed i v h r hr
  change walkVertices i.val (pathList v) =
       walkVertices (v 0).val mid ∪ walkVertices i.val rest
  rw [pathList_succ, show pathList (Fin.tail v) = T from rfl, splitT]
  rw [walkVertices_cons, walkVertices_append]
  change walkLast (v 0).val mid = _ at childLast
  rw [childLast]
  simp [walkVertices_cons]
  -- the old root is already present in `rest`
  ext z
  by_cases zi : z = i.val
  · subst z
    simp [walkVertices]
  · simp [zi]
    intro hz
    subst z
    left
    exact walkVertices_root_mem _ _
end WignerSupport
namespace WignerSupport
/-- Consequently each open piece separately attains the connected-walk
bound. This is the equality input for normalising the two smaller leading
words. -/
lemma leading_split_piece_eq {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    ((walkVertices (v 0).val ((pathList (Fin.tail v)).take r.val)).card =
      (walkEdges (v 0).val ((pathList (Fin.tail v)).take r.val)).card + 1) ∧
    ((walkVertices i.val ((pathList (Fin.tail v)).drop (r.val+1))).card =
      (walkEdges i.val ((pathList (Fin.tail v)).drop (r.val+1))).card + 1) := by
  classical
  let U := walkVertices (v 0).val ((pathList (Fin.tail v)).take r.val)
  let W := walkVertices i.val ((pathList (Fin.tail v)).drop (r.val+1))
  let A := walkEdges (v 0).val ((pathList (Fin.tail v)).take r.val)
  let B := walkEdges i.val ((pathList (Fin.tail v)).drop (r.val+1))
  let e := edgeNat i.val (v 0).val
  have vd : Disjoint U W := leading_split_vertices_disjoint i v h r hr
  have ed : Disjoint A B := leading_split_edges_disjoint i v h r hr
  have en := leading_split_edge_not_mem i v h r hr
  have eA : e ∉ A := en.1
  have eB : e ∉ B := en.2
  have vu : walkVertices i.val (pathList v) = U ∪ W :=
    leading_split_vertices_union i v h r hr
  have eu : walkEdges i.val (pathList v) = insert e (A ∪ B) :=
    leading_split_edges_union i v h r hr
  have allEq : (walkVertices i.val (pathList v)).card =
      (walkEdges i.val (pathList v)).card + 1 :=
    leading_walk_eq i v h.2.1 h.2.2
  rw [vu, eu, Finset.card_union_of_disjoint vd,
      Finset.card_insert_of_notMem (by simp [eA, eB]),
      Finset.card_union_of_disjoint ed] at allEq
  have lu : U.card ≤ A.card + 1 := by
    exact card_walkVertices_le_edges_add_one _ _
  have lw : W.card ≤ B.card + 1 := by
    exact card_walkVertices_le_edges_add_one _ _
  change U.card = A.card + 1 ∧ W.card = B.card + 1
  omega
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/Bridge.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/SplitPath.lean
section
open scoped BigOperators ENNReal NNReal Topology
namespace WignerSupport

/-- Turn a bounded list of natural labels back into a `Fin` path.
The list language is useful for first-return cuts; this inverse to `pathList`
lets us state the two cut pieces as honest smaller rooted paths, including the
empty piece. -/
def listPath {n : ℕ} (xs : List ℕ)
    (h : ∀ a ∈ xs, a < n) : Fin xs.length → Fin n :=
  fun r => ⟨xs[r.val], h _ (List.getElem_mem r.isLt)⟩

@[simp] lemma pathList_listPath {n : ℕ} (xs : List ℕ)
    (h : ∀ a ∈ xs, a < n) : pathList (listPath xs h) = xs := by
  unfold pathList listPath
  change List.ofFn (fun r : Fin xs.length => xs[r.val]) = xs
  exact List.ofFn_getElem

lemma pathEnd_listPath_val {n : ℕ} (i : Fin n) (xs : List ℕ)
    (h : ∀ a ∈ xs, a < n) :
    (pathEnd xs.length i (listPath xs h)).val = walkLast i.val xs := by
  rw [pathEnd_val_eq_walkLast, pathList_listPath]

@[simp] lemma pathVertices_listPath {n : ℕ} (i : Fin n)
    (xs : List ℕ) (h : ∀ a ∈ xs, a < n) :
    pathVerticesFin i (listPath xs h) = walkVertices i.val xs := by
  simp [pathVerticesFin, pathList_listPath]

lemma image_edges_listPath {n : ℕ} (i : Fin n)
    (xs : List ℕ) (h : ∀ a ∈ xs, a < n) :
    (Finset.univ.image (pathEdgesNat i (listPath xs h))) =
      walkEdges i.val xs := by
  simpa [pathList_listPath] using
    (image_pathEdges_eq_walkEdges i (listPath xs h))

/-- All letters of a finite path have the ambient bound; the list/cut
constructions below only store naturals. -/
lemma mem_walkVertices_path_bound {n p : ℕ} (i : Fin n)
    (v : Fin p → Fin n) {a : ℕ}
    (ha : a ∈ walkVertices i.val (pathList v)) : a < n := by
  classical
  have hm : a = i.val ∨ a ∈ pathList v := by
    simpa [walkVertices] using ha
  rcases hm with hm | hm
  · simpa [hm] using i.isLt
  · have hv : ∃ r : Fin p, (v r).val = a := by
      simpa [pathList] using (show a ∈ List.ofFn (fun r : Fin p => (v r).val) from hm)
    rcases hv with ⟨r, rfl⟩
    exact (v r).isLt

/-- Data carried by a cut piece, written in `Fin` language.  We deliberately
only put the equality `#V=#E+1` here, not the repeated-edge conclusion: the
latter uses the bridge/fibre argument.  This avoids accidentally treating a
subwalk of an equality walk as equality without the cut hypotheses. -/
structure ClosedEqPiece (n : ℕ) (root : Fin n) (xs : List ℕ) where
  bound : ∀ a ∈ xs, a < n
  closed : pathEnd xs.length root (listPath xs bound) = root
  eqcard : (pathVerticesFin root (listPath xs bound)).card =
    (Finset.univ.image (pathEdgesNat root (listPath xs bound))).card + 1

/-- Both words left by deleting a leading first-return edge are bona fide
closed equality paths in the original alphabet.  This is the safe input to
normalising each word by its first occurrences; no assertion about edge
multiplicity is smuggled into the conversion. -/
lemma leading_split_closedEqPieces {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    let mid : List ℕ := (pathList (Fin.tail v)).take r.val
    let rest : List ℕ := (pathList (Fin.tail v)).drop (r.val+1)
    ClosedEqPiece n (v 0) mid ∧ ClosedEqPiece n i rest := by
  classical
  dsimp
  let mid : List ℕ := (pathList (Fin.tail v)).take r.val
  let rest : List ℕ := (pathList (Fin.tail v)).drop (r.val+1)
  have sub := leading_split_subsets i v h r hr
  have hmV : walkVertices (v 0).val mid ⊆
        walkVertices i.val (pathList v) := sub.2.1
  have hrV : walkVertices i.val rest ⊆
        walkVertices i.val (pathList v) := sub.2.2.2
  have mbound : ∀ a ∈ mid, a < n := by
    intro a ha
    apply mem_walkVertices_path_bound i v
    apply hmV
    have : a ∈ walkVertices (v 0).val mid := by
      -- a letter is of course one of the vertices of its word
      exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr ha)
    exact this
  have rbound : ∀ a ∈ rest, a < n := by
    intro a ha
    apply mem_walkVertices_path_bound i v
    apply hrV
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr ha)
  have closem0 : walkLast (v 0).val mid = (v 0).val :=
    leading_split_child_closed i v h r hr
  have closer0 : walkLast i.val rest = i.val :=
    leading_split_root_closed i v h r hr
  have closes {root : Fin n} {xs : List ℕ}
      (bd : ∀ a ∈ xs, a < n)
      (cl : walkLast root.val xs = root.val) :
      pathEnd xs.length root (listPath xs bd) = root := by
    apply Fin.ext
    rw [pathEnd_listPath_val]
    exact cl
  have eqs := leading_split_piece_eq i v h r hr
  have eqm :
      (pathVerticesFin (v 0) (listPath mid mbound)).card =
        (Finset.univ.image (pathEdgesNat (v 0) (listPath mid mbound))).card + 1 := by
    rw [pathVertices_listPath, image_edges_listPath]
    exact eqs.1
  have eqr :
      (pathVerticesFin i (listPath rest rbound)).card =
        (Finset.univ.image (pathEdgesNat i (listPath rest rbound))).card + 1 := by
    rw [pathVertices_listPath, image_edges_listPath]
    exact eqs.2
  -- keep the fields explicit: the proof argument to `listPath` in a field is
  -- part of the dependent structure
  change ClosedEqPiece n (v 0) mid ∧ ClosedEqPiece n i rest
  exact ⟨⟨mbound, closes mbound closem0, eqm⟩,
    ⟨rbound, closes rbound closer0, eqr⟩⟩

/-- In particular both smaller words have even length. This is a useful
sanity check on first-return slicing and will be used before dividing their
lengths by two in the Catalan recursion. -/
lemma ClosedEqPiece.even {n : ℕ} {root : Fin n} {xs : List ℕ}
    (z : ClosedEqPiece n root xs) : 2 ∣ xs.length := by
  have vEq : (walkVertices root.val xs).card =
        (walkEdges root.val xs).card + 1 := by
    simpa [pathVertices_listPath, image_edges_listPath] using z.eqcard
  have cl : walkLast root.val xs = root.val := by
    have tt := congrArg Fin.val z.closed
    simpa [pathEnd_listPath_val] using tt
  exact even_length_of_closed_eq_walk root.val xs vEq cl

lemma leading_split_piece_even' {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (r : Fin p)
    (hr : pathEdgesNat (v 0) (Fin.tail v) r = edgeNat i.val (v 0).val) :
    2 ∣ ((pathList (Fin.tail v)).take r.val).length ∧
    2 ∣ ((pathList (Fin.tail v)).drop (r.val+1)).length := by
  have pc := leading_split_closedEqPieces i v h r hr
  exact ⟨pc.1.even, pc.2.even⟩
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/SplitPath.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/RepeatedPiece.lean
section
open SimpleGraph
open scoped Sym2
namespace WignerSupport

/-- In a *closed* equality list-walk an occurrence of an edge cannot be its
only occurrence. This is the small bridge argument that is easy to lose when
cutting a leading contour into two list pieces.  No `Fin` choice of letters is
involved here. -/
lemma closed_eq_step_seen_elsewhere (o : ℕ) (xs : List ℕ)
    (heq : (walkVertices o xs).card = (walkEdges o xs).card + 1)
    (hcl : walkLast o xs = o)
    (k : ℕ) (hk : k < xs.length) :
    let pre := xs.take k
    let b := xs[k]
    let a := walkLast o pre
    edgeNat a b ∈ walkEdges o pre ∨
      edgeNat a b ∈ walkEdges b (xs.drop (k+1)) := by
  classical
  let pre : List ℕ := xs.take k
  let zs : List ℕ := xs.drop (k+1)
  let a : ℕ := walkLast o pre
  let b : ℕ := xs[k]
  dsimp
  change edgeNat a b ∈ walkEdges o pre ∨ edgeNat a b ∈ walkEdges b zs
  have sp : xs = pre ++ b :: zs := by
    have e := List.take_append_drop k xs
    have d := List.drop_eq_getElem_cons (l:=xs) (i:=k) hk
    rw [d] at e
    simpa [pre, zs, b] using e.symm
  have memedge : edgeNat a b ∈ walkEdges o xs := by
    rw [sp, walkEdges_append]
    change edgeNat a b ∈ walkEdges o pre ∪ walkEdges a (b::zs)
    exact Finset.mem_union_right _ (by simp [walkEdges])
  have av : a ∈ walkVertices o xs := by
    rw [sp, walkVertices_append]
    exact Finset.mem_union_left _ (walkLast_mem o pre)
  have bv : b ∈ walkVertices o xs := by
    rw [sp, walkVertices_append]
    change b ∈ walkVertices o pre ∪ walkVertices a (b :: zs)
    exact Finset.mem_union_right _ (by
      rw [walkVertices_cons]
      exact Finset.mem_insert_of_mem (walkVertices_root_mem _ _))
  by_contra noBoth
  have no : edgeNat a b ∉ walkEdges o pre ∧
      edgeNat a b ∉ walkEdges b zs := by
    push_neg at noBoth
    -- `by_contra` on a disjunction gives both negations
    exact noBoth
  have nonloop : ∀ z : ℕ, edgeNat z z ∉ walkEdges o xs :=
    walk_eq_no_self o xs heq
  have abne : a ≠ b := by
    intro eq
    have em : edgeNat a a = edgeNat a b := by rw [eq]
    exact nonloop a (by rw [em]; exact memedge)
  let A : WalkVert o xs := ⟨a, av⟩
  let B : WalkVert o xs := ⟨b, bv⟩
  let O : WalkVert o xs := ⟨o, walkVertices_root_mem _ _⟩
  have ABne : A ≠ B := by
    intro h
    exact abne (congrArg Subtype.val h)
  have adj : (walkGraph o xs).Adj A B :=
    (walkGraph_adj _ _).2 ⟨ABne, memedge⟩
  have tree : (walkGraph o xs).IsTree := walkGraph_isTree _ _ heq
  have bridge : (walkGraph o xs).IsBridge s(A,B) :=
    (SimpleGraph.isAcyclic_iff_forall_isBridge.mp tree.isAcyclic)
      ((SimpleGraph.mem_edgeSet _).2 adj)
  have nreach :
      ¬ ((walkGraph o xs).deleteEdges {s(A,B)}).Reachable A B :=
    (SimpleGraph.isBridge_iff).1 bridge
  -- The prefix and the closed suffix avoid the displayed edge; hence in the
  -- graph with that edge removed they connect the two endpoints through the
  -- old root, a contradiction.
  have pE : walkEdges o pre ⊆ walkEdges o xs := by
    rw [sp, walkEdges_append]
    exact Finset.subset_union_left
  have pV : walkVertices o pre ⊆ walkVertices o xs := by
    rw [sp, walkVertices_append]
    exact Finset.subset_union_left
  have sE : walkEdges b zs ⊆ walkEdges o xs := by
    rw [sp, walkEdges_append]
    intro e ee
    refine Finset.mem_union_right _ ?_
    -- the join edge plus the suffix are precisely the second append part
    change e ∈ walkEdges (walkLast o pre) (b::zs)
    change e ∈ walkEdges a (b::zs)
    simp [walkEdges, ee]
  have sV : walkVertices b zs ⊆ walkVertices o xs := by
    rw [sp, walkVertices_append]
    intro z hz
    refine Finset.mem_union_right _ ?_
    change z ∈ walkVertices a (b::zs)
    rw [walkVertices_cons]
    exact Finset.mem_insert_of_mem hz
  have pa :
      ((walkGraph o xs).deleteEdges {s(A,B)}).Reachable O A := by
    -- prefix endpoint is its last vertex
    have r := reachable_piece_deleteEdge o xs nonloop
      a b av bv o pre pE pV no.1 a (walkLast_mem _ _)
    -- only proof fields of the subtypes differ
    simpa [A, B, O] using r
  have lastpre : walkLast o pre = a := rfl
  have closez : walkLast b zs = o := by
    have cc := hcl
    rw [sp, walkLast_append, walkLast_cons] at cc
    exact cc
  have rootz : o ∈ walkVertices b zs := by
    rw [← closez]
    exact walkLast_mem _ _
  have bo :
      ((walkGraph o xs).deleteEdges {s(A,B)}).Reachable B O := by
    have r := reachable_piece_deleteEdge o xs nonloop
      a b av bv b zs sE sV no.2 o rootz
    simpa [A, B, O] using r
  exact nreach (pa.symm.trans bo.symm)


/-- Consecutive-position version of the edge of a finite list path.  This is
what lets `mem_walkEdges_pos` on a cut piece be shifted back to a full word;
unfolding `pathEdgesNat` across `Fin.tail` at a successor causes the classic
off-by-one. -/
lemma pathEdges_listPath_pos {n : ℕ} (root : Fin n)
    (xs : List ℕ) (bd : ∀ a ∈ xs, a < n) (r : Fin xs.length) :
 pathEdgesNat root (listPath xs bd) r =
   edgeNat ((root.val :: xs)[r.val]'(by simp))
           ((root.val :: xs)[r.val+1]'(by simp)) := by
 let w : Fin (xs.length+1) → Fin n :=
        @Fin.cons xs.length (fun _ => Fin n) root (listPath xs bd)
 have desc := pathEdges_word w r
 have eqtail : Fin.tail w = listPath xs bd := by funext x; rfl
 have eqroot : w 0 = root := rfl
 rw [eqtail, eqroot] at desc
 rw [desc]
 congr 1
 · dsimp [w]
   by_cases rz : r.val = 0
   · have rc : r.castSucc = (0 : Fin (xs.length+1)) := Fin.ext rz
     rw [rc]
     simp [rz]
   · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero rz
     have kk : k < xs.length := by omega
     have rc : r.castSucc = Fin.succ ⟨k, kk⟩ := by apply Fin.ext; simp [hk]
     rw [rc, Fin.cons_succ]
     change xs[k] = (root.val :: xs)[r.val]
     simpa [hk, List.getElem_cons_succ]
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/RepeatedPiece.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PieceLeading.lean
section
open scoped BigOperators ENNReal NNReal Topology Sym2
open SimpleGraph
namespace WignerSupport

/-- The endpoint of the length `k` prefix of a rooted list is the element at
position `k` of the word with the root prepended.  Writing this once avoids
casting a `take` proof through `List.getElem` every time a literal edge of a
piece is compared with `pathEdgesNat`. -/
lemma walkLast_take_get (o : ℕ) (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    walkLast o (xs.take k) =
      (o :: xs)[k]'(by simp; omega) := by
  induction xs generalizing o k with
  | nil => simp at hk
  | cons x ys ih =>
      cases k with
      | zero => simp [walkLast]
      | succ k =>
        have hk' : k < ys.length := by
          simpa using hk
        have h := ih (o := x) (k := k) hk'
        -- after the first letter both the `take` and the position are successors
        simpa [walkLast_cons, List.getElem_cons_succ] using h

end WignerSupport
namespace WignerSupport
lemma pathEdges_listPath_at_split {n : ℕ} (root : Fin n) (xs : List ℕ)
    (bd : ∀ a ∈ xs, a < n) (u : Fin xs.length) :
    pathEdgesNat root (listPath xs bd) u =
      edgeNat (walkLast root.val (xs.take u.val))
        (xs[u.val]) := by
  rw [pathEdges_listPath_pos]
  have hp := walkLast_take_get root.val xs u.val u.isLt
  -- the element following prefix position `u` in the cons-list is the
  -- `u`-th element of the tail
  have hb : (root.val :: xs)[u.val+1]'(by simp) = xs[u.val] := by
    simp [List.getElem_cons_succ]
  rw [hp, hb]
end WignerSupport
namespace WignerSupport
/-- If each displayed step of a list word has already occurred to its left or
will occur to its right, then the finite rooted path made from that list has
no singleton edge.  The inequalities are important: the occurrence returned
by the prefix has a *smaller* path index and the one returned by the suffix a
*larger* one.  Thus no occurrence can alias the displayed index after the
`take`/`drop` transports. -/
lemma repeated_edges_listPath_of_seen {n : ℕ} (root : Fin n) (xs : List ℕ)
    (bd : ∀ a ∈ xs, a < n)
    (hseen : ∀ k : ℕ, ∀ hk : k < xs.length,
      let b := xs[k]
      let a := walkLast root.val (xs.take k)
      edgeNat a b ∈ walkEdges root.val (xs.take k) ∨
        edgeNat a b ∈ walkEdges b (xs.drop (k+1))) :
    ∀ u : Fin xs.length, ∃ r : Fin xs.length, r ≠ u ∧
      pathEdgesNat root (listPath xs bd) r =
        pathEdgesNat root (listPath xs bd) u := by
  classical
  intro u
  let a : ℕ := walkLast root.val (xs.take u.val)
  let b : ℕ := xs[u.val]
  let e : {z : ℕ × ℕ // z.1 ≤ z.2} := edgeNat a b
  have us : edgeNat a b ∈ walkEdges root.val (xs.take u.val) ∨
        edgeNat a b ∈ walkEdges b (xs.drop (u.val+1)) := by
    simpa [a, b] using (hseen u.val u.isLt)
  have eu : pathEdgesNat root (listPath xs bd) u = e := by
    dsimp [e, a, b]
    exact pathEdges_listPath_at_split root xs bd u
  -- add the root back to regard this word as the usual `cons` path in the
  -- positional lemmas for prefixes and suffixes
  let w : Fin (xs.length+1) → Fin n :=
      @Fin.cons xs.length (fun _ => Fin n) root (listPath xs bd)
  have wt : Fin.tail w = listPath xs bd := by
    funext r
    rfl
  have w0 : w 0 = root := rfl
  have ltail : pathList (Fin.tail w) = xs := by
    rw [wt, pathList_listPath]
  have lw : pathList w = root.val :: xs := by
    rw [pathList_succ, ltail]
    rfl
  rcases us with pre | suf
  · have pre' : e ∈ walkEdges (w 0).val
          ((pathList (Fin.tail w)).take u.val) := by
        simpa [e, w0, ltail] using pre
    obtain ⟨s, hslt, hseq⟩ :=
      mem_childEdges_before_index (v := w) (r := u) (e := e) pre'
    have hseq' : pathEdgesNat root (listPath xs bd) s = e := by
      simpa [w0, wt] using hseq
    refine ⟨s, ?_, hseq'.trans eu.symm⟩
    intro hsu
    have : s.val = u.val := congrArg Fin.val hsu
    omega
  · have wsu : (w u.succ).val = b := by
        dsimp [w, b, listPath]
        rfl
    have dropword : (pathList w).drop (u.val+2) = xs.drop (u.val+1) := by
        rw [lw]
        -- the first `drop` removes the root of the cons-list
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have suf' : e ∈ walkEdges (w u.succ).val
          ((pathList w).drop (u.val+2)) := by
        rw [wsu, dropword]
        simpa [e] using suf
    obtain ⟨s, hslt, hseq⟩ :=
      mem_walkEdges_after_index (v := w) (r := u) (e := e) suf'
    have hseq' : pathEdgesNat root (listPath xs bd) s = e := by
      simpa [w0, wt] using hseq
    refine ⟨s, ?_, hseq'.trans eu.symm⟩
    intro hsu
    have : s.val = u.val := congrArg Fin.val hsu
    omega
end WignerSupport
namespace WignerSupport
/-- A closed equality piece becomes leading as soon as its (already repeated)
edges have the inherited *upper* fibre bound two.  Equality of a connected
subwalk by itself is not enough; e.g. traversing a single bridge four times is
a closed equality walk.  This lemma isolates exactly the extra input which a
first-return piece must inherit from `leading_fibers_two` of the ambient word. -/
lemma ClosedEqPiece.isLeading_of_rep_of_fiber_le_two
    {n : ℕ} {root : Fin n} {xs : List ℕ}
    (z : ClosedEqPiece n root xs)
    (rep : ∀ u : Fin xs.length, ∃ r : Fin xs.length, r ≠ u ∧
      pathEdgesNat root (listPath xs z.bound) r =
        pathEdgesNat root (listPath xs z.bound) u)
    (hi : ∀ e ∈ (Finset.univ.image
                  (pathEdgesNat root (listPath xs z.bound))),
        ((Finset.univ : Finset (Fin xs.length)).filter
          (fun r => pathEdgesNat root (listPath xs z.bound) r = e)).card ≤ 2) :
    IsLeadingPath root (listPath xs z.bound) := by
  classical
  let f := pathEdgesNat root (listPath xs z.bound)
  let s : Finset (Fin xs.length) := Finset.univ
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} := s.image f
  have lo (e) (he : e ∈ E) : 2 ≤ (s.filter (fun r => f r = e)).card := by
    rcases Finset.mem_image.mp he with ⟨u, hu, rfl⟩
    rcases rep u with ⟨r, ne, hr⟩
    exact two_le_card_fiber_of_pair s f hu (by simp [s]) ne hr
  have eqtwo (e) (he : e ∈ E) :
      (s.filter (fun r => f r = e)).card = 2 := by
    have upper : (s.filter (fun r => f r = e)).card ≤ 2 := by
      simpa [s, E, f] using hi e (by simpa [s, E, f] using he)
    exact Nat.le_antisymm upper (lo e he)
  have cnt : s.card = ∑ e ∈ E, (s.filter (fun r => f r = e)).card := by
    exact Finset.card_eq_sum_card_image f s
  have all : xs.length = 2 * E.card := by
    have ssz : s.card = xs.length := by simp [s]
    -- every summand of the image fibre is exactly two
    calc
      xs.length = s.card := ssz.symm
      _ = ∑ e ∈ E, (s.filter (fun r => f r = e)).card := cnt
      _ = ∑ _e ∈ E, 2 := by
            apply Finset.sum_congr rfl
            intro e he
            exact eqtwo e he
      _ = 2 * E.card := by simp [mul_comm]
  have ec : E.card = xs.length / 2 := by omega
  have mx :
      (pathVerticesFin root (listPath xs z.bound)).card = xs.length / 2 + 1 := by
    have zc := z.eqcard
    change (pathVerticesFin root (listPath xs z.bound)).card =
       (Finset.univ.image (pathEdgesNat root (listPath xs z.bound))).card + 1 at zc
    have eident : E =
        (Finset.univ.image (pathEdgesNat root (listPath xs z.bound))) := by
          rfl
    rw [← eident, ec] at zc
    exact zc
  exact ⟨z.closed, rep, mx⟩
end WignerSupport
namespace WignerSupport
/-- Fibre cardinalities only decrease on an injectively embedded set of
positions.  Keeping the occurrence map, not just containment of the two edge
*images*, is essential for the upper bound on a first-return piece. -/
lemma fiber_card_le_of_indexEmbedding
    {pa pb : ℕ}
    (F : Fin pa → {z : ℕ × ℕ // z.1 ≤ z.2})
    (G : Fin pb → {z : ℕ × ℕ // z.1 ≤ z.2})
    (emb : Fin pa ↪ Fin pb)
    (compat : ∀ u, F u = G (emb u)) (e : {z : ℕ × ℕ // z.1 ≤ z.2}) :
    ((Finset.univ : Finset (Fin pa)).filter (fun r => F r = e)).card ≤
      ((Finset.univ : Finset (Fin pb)).filter (fun r => G r = e)).card := by
  classical
  let A : Finset (Fin pa) :=
    (Finset.univ : Finset (Fin pa)).filter (fun r => F r = e)
  let B : Finset (Fin pb) :=
    (Finset.univ : Finset (Fin pb)).filter (fun r => G r = e)
  let m : {r // r ∈ A} → {r // r ∈ B} := fun r =>
    ⟨emb r.val, by
      dsimp [A] at r
      have hr : F r.val = e := (Finset.mem_filter.mp r.property).2
      dsimp [B]
      simp [← compat r.val, hr]⟩
  have inj : Function.Injective m := by
    intro r s h
    apply Subtype.ext
    exact emb.injective (congrArg Subtype.val h)
  have c := Fintype.card_le_of_injective m inj
  change A.card ≤ B.card
  simpa only [Fintype.card_coe] using c
end WignerSupport
namespace WignerSupport
/-- Throwing away the initial root edge shifts every subsequent tail index by
one. This tiny compatibility is useful when injecting occurrences of the
child excursion into the ambient contour. -/
lemma pathEdges_tail_shift {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (u : Fin p) :
    pathEdgesNat (v 0) (Fin.tail v) u =
      pathEdgesNat i v u.succ := by
  let W : Fin ((p+1)+1) → Fin n :=
      @Fin.cons (p+1) (fun _ => Fin n) i v
  have wt : Fin.tail W = v := by funext z; rfl
  have wz : W 0 = i := rfl
  rw [pathEdges_word v u]
  have h := pathEdges_word W u.succ
  rw [wt, wz] at h
  rw [h]
  rfl
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PieceLeading.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PieceFiber.lean
section
open scoped BigOperators ENNReal NNReal Topology
namespace WignerSupport

/-- Edge at a position of a `take` word is the edge at the same position
of the full list word.  The proof arguments supplying the `Fin` bounds need
not agree. -/
lemma pathEdges_take_compat {n : ℕ} (root : Fin n)
    (xs : List ℕ) (k : ℕ)
    (bd : ∀ a ∈ xs, a < n)
    (bt : ∀ a ∈ xs.take k, a < n)
    (u : Fin (xs.take k).length) :
    pathEdgesNat root (listPath (xs.take k) bt) u =
      pathEdgesNat root (listPath xs bd)
        (⟨u.val, by
          have he : (xs.take k).length ≤ xs.length := by simp
          exact lt_of_lt_of_le u.isLt he⟩ : Fin xs.length) := by
  classical
  rw [pathEdges_listPath_at_split, pathEdges_listPath_at_split]
  congr 1
  · -- the prefixes have the same list
    have hk : u.val ≤ k := by
      have he : (xs.take k).length ≤ k := by simp
      exact le_trans (Nat.le_of_lt u.isLt) he
    simp [List.take_take, Nat.min_eq_left hk]
  · -- and the following letter is unchanged by `take`
    exact List.getElem_take

/-- Edges of a `drop off` suffix embed at indices `off+j` in the original
list word, once the root at the cut really is the endpoint of the prefix. -/
lemma pathEdges_drop_compat {n : ℕ} (root0 root1 : Fin n)
    (xs : List ℕ) (off : ℕ)
    (bd : ∀ a ∈ xs, a < n)
    (br : ∀ a ∈ xs.drop off, a < n)
    (hend : walkLast root0.val (xs.take off) = root1.val)
    (u : Fin (xs.drop off).length) :
    pathEdgesNat root1 (listPath (xs.drop off) br) u =
      pathEdgesNat root0 (listPath xs bd)
        (⟨off + u.val, by
          have hj : u.val < xs.length - off := by
            simpa using u.isLt
          omega⟩ : Fin xs.length) := by
  classical
  rw [pathEdges_listPath_at_split, pathEdges_listPath_at_split]
  congr 1
  · -- concatenate the two prefix pieces
    rw [List.take_add]
    -- `off + u` is the prefix at this edge
    simp [walkLast_append, hend]
  · -- following letter of a `drop`
    simpa [Nat.add_comm] using
      (List.getElem_drop (xs := xs) (i := off) (j := u.val)
        (h := u.isLt))

end WignerSupport

namespace WignerSupport
lemma pathEdges_pathList_cast {n p : ℕ} (root : Fin n)
    (w : Fin p → Fin n) (bd : ∀ a ∈ pathList w, a < n)
    (u : Fin (pathList w).length) :
    pathEdgesNat root (listPath (pathList w) bd) u =
      pathEdgesNat root w (⟨u.val, by simpa [pathList] using u.isLt⟩ : Fin p) := by
  classical
  let r : Fin p := ⟨u.val, by simpa [pathList] using u.isLt⟩
  let W : Fin (p+1) → Fin n := @Fin.cons p (fun _ => Fin n) root w
  have htail : Fin.tail W = w := by funext j; rfl
  have hzero : W 0 = root := rfl
  have desc := pathEdges_word W r
  rw [htail, hzero] at desc
  rw [pathEdges_listPath_pos]
  change edgeNat _ _ = pathEdgesNat root w r
  rw [desc]
  congr 1
  · -- element at position r in root::word
    by_cases z : r.val = 0
    · have rr : r.castSucc = (0 : Fin (p+1)) := Fin.ext z
      rw [rr]
      have zv : u.val = 0 := by simpa [r] using z
      simp [zv, W]
    · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero z
      have kl : k < (pathList w).length := by
        have ru := u.isLt
        change u.val < _ at ru
        have eqv : u.val = k+1 := by simpa [r] using hk
        rw [eqv] at ru
        omega
      have kp : k < p := by simpa [pathList] using kl
      have rr : r.castSucc = Fin.succ ⟨k,kp⟩ := by
        apply Fin.ext
        simp [hk]
      rw [rr]
      change (root.val :: pathList w)[u.val] = (w ⟨k,kp⟩).val
      have uv : u.val = k+1 := by simpa [r] using hk
      simp [uv, List.getElem_cons_succ]
      -- index is a successor in the cons list
      simpa [pathList] using
        (List.getElem_ofFn (f := fun z : Fin p => (w z).val)
          (i := k) (by simp [pathList]; exact kp))
  · -- the next position is the tail letter r
    have rp : r.val < p := r.isLt
    -- both simplify at a successor of the cons
    change (root.val :: pathList w)[u.val+1] = (w r).val
    simp [List.getElem_cons_succ]
    -- the tail is an `ofFn`
    have ofn := (List.getElem_ofFn (f := fun z : Fin p => (w z).val)
        (i := r.val) (by simpa [pathList] using rp))
    simpa [r, pathList] using ofn
end WignerSupport

namespace WignerSupport
lemma leading_split_piece_fiber_le_two {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (t : Fin p)
    (ht : pathEdgesNat (v 0) (Fin.tail v) t = edgeNat i.val (v 0).val) :
    let mid : List ℕ := (pathList (Fin.tail v)).take t.val
    let rest : List ℕ := (pathList (Fin.tail v)).drop (t.val+1)
    let zm : ClosedEqPiece n (v 0) mid :=
      (leading_split_closedEqPieces i v h t ht).1
    let zr : ClosedEqPiece n i rest :=
      (leading_split_closedEqPieces i v h t ht).2
    (∀ e ∈ (Finset.univ.image
          (pathEdgesNat (v 0) (listPath mid zm.bound))),
        ((Finset.univ : Finset (Fin mid.length)).filter
          (fun r => pathEdgesNat (v 0) (listPath mid zm.bound) r = e)).card ≤ 2) ∧
    (∀ e ∈ (Finset.univ.image
          (pathEdgesNat i (listPath rest zr.bound))),
        ((Finset.univ : Finset (Fin rest.length)).filter
          (fun r => pathEdgesNat i (listPath rest zr.bound) r = e)).card ≤ 2) := by
  classical
  dsimp
  let T : List ℕ := pathList (Fin.tail v)
  let mid : List ℕ := T.take t.val
  let rest : List ℕ := T.drop (t.val+1)
  have pcs := leading_split_closedEqPieces i v h t ht
  change ClosedEqPiece n (v 0) mid ∧ ClosedEqPiece n i rest at pcs
  let zm : ClosedEqPiece n (v 0) mid := pcs.1
  let zr : ClosedEqPiece n i rest := pcs.2
  change
    (∀ e ∈ (Finset.univ.image
          (pathEdgesNat (v 0) (listPath mid zm.bound))),
        ((Finset.univ : Finset (Fin mid.length)).filter
          (fun r => pathEdgesNat (v 0) (listPath mid zm.bound) r = e)).card ≤ 2) ∧
    (∀ e ∈ (Finset.univ.image
          (pathEdgesNat i (listPath rest zr.bound))),
        ((Finset.univ : Finset (Fin rest.length)).filter
          (fun r => pathEdgesNat i (listPath rest zr.bound) r = e)).card ≤ 2)
  have lenT : T.length = p := by simp [T, pathList]
  have bdT : ∀ a ∈ T, a < n := by
    intro a ha
    -- membership of `ofFn` gives a tail index
    have ex : ∃ r : Fin p, ((Fin.tail v) r).val = a := by
      simpa [T, pathList] using ha
    rcases ex with ⟨r, rfl⟩
    exact ((Fin.tail v) r).isLt
  -- the returning letter ends the prefix at root `i`
  have hend : walkLast (v 0).val (T.take (t.val+1)) = i.val := by
    -- appending the return edge after the closed child excursion
    have rlt : t.val < T.length := by simpa [lenT] using t.isLt
    have ret : T[t.val]'rlt = i.val := by
      have back := (leading_second_edge_return i v h t ht).2
      change (List.ofFn (fun r : Fin p => ((Fin.tail v) r).val))[t.val] = _
      have ofn := (List.getElem_ofFn
          (f := fun r : Fin p => ((Fin.tail v) r).val)
          (i := t.val) (by simpa [pathList] using t.isLt))
      calc
        _ = ((Fin.tail v) t).val := by convert ofn using 1 <;> rfl
        _ = _ := back
    have child := leading_split_child_closed i v h t ht
    change walkLast (v 0).val (T.take t.val) = (v 0).val at child
    have spl : T.take (t.val+1) = T.take t.val ++ [T[t.val]'rlt] := by
      simpa using (List.take_concat_get' T t.val rlt).symm
    rw [spl, walkLast_append, ret]
    simp [child, walkLast_cons]
  constructor
  · intro e he
    -- inject the positions of the middle word (shifted by the root edge)
    let emb : Fin mid.length ↪ Fin (p+1) :=
      ⟨fun u => ⟨u.val+1, by
          have uT : u.val < p := by
            have hm : mid.length ≤ t.val := by simp [mid]
            have : u.val < t.val := lt_of_lt_of_le u.isLt hm
            exact lt_of_lt_of_le this (Nat.le_of_lt t.isLt)
          omega⟩,
       by
        intro a b eq
        apply Fin.ext
        have ev := congrArg Fin.val eq
        dsimp at ev
        omega⟩
    let FM : Fin mid.length → {z : ℕ × ℕ // z.1 ≤ z.2} :=
      pathEdgesNat (v 0) (listPath mid zm.bound)
    let GG : Fin (p+1) → {z : ℕ × ℕ // z.1 ≤ z.2} := pathEdgesNat i v
    have comp : ∀ u, FM u = GG (emb u) := by
      intro u
      -- first keep it in the tail list `T`
      have tak := pathEdges_take_compat (v 0) T t.val bdT zm.bound
          (show Fin (T.take t.val).length from u)
      have ll := pathEdges_pathList_cast (v 0) (Fin.tail v) bdT
          (⟨u.val, by
            have hle : mid.length ≤ T.length := by simp [mid]
            exact lt_of_lt_of_le u.isLt hle⟩ : Fin (pathList (Fin.tail v)).length)
      dsimp [FM, GG, mid] at tak ⊢
      -- `tak` followed by replacing `T` by the list of the tail
      -- and then throwing the omitted root edge back in
      -- the indices have the same value, hence are the same `Fin`
      have step1 :
          pathEdgesNat (v 0) (listPath (T.take t.val) zm.bound) u =
            pathEdgesNat (v 0) (listPath T bdT)
              (⟨u.val, by
                have hle : mid.length ≤ T.length := by simp [mid]
                exact lt_of_lt_of_le u.isLt hle⟩ : Fin T.length) := by
            simpa [mid] using tak
      -- transport `T = pathList (Fin.tail v)`
      have step2 :
          pathEdgesNat (v 0) (listPath T bdT)
              (⟨u.val, by
                have hle : mid.length ≤ T.length := by simp [mid]
                exact lt_of_lt_of_le u.isLt hle⟩ : Fin T.length) =
            pathEdgesNat (v 0) (Fin.tail v)
              (⟨u.val, by
                have mt : mid.length ≤ t.val := by simp [mid]
                have uv : u.val < t.val := lt_of_lt_of_le u.isLt mt
                exact lt_of_lt_of_le uv (Nat.le_of_lt t.isLt)⟩ : Fin p) := by
            -- `T` is definitionally the path list
            dsimp [T]
            simpa using ll
      have tailshift := pathEdges_tail_shift i v
          (⟨u.val, by
            have mt : mid.length ≤ t.val := by simp [mid]
            have uv : u.val < t.val := lt_of_lt_of_le u.isLt mt
            exact lt_of_lt_of_le uv (Nat.le_of_lt t.isLt)⟩ : Fin p)
      -- the embedding value is its successor
      calc
        pathEdgesNat (v 0) (listPath (T.take t.val) zm.bound) u =
            pathEdgesNat (v 0) (listPath T bdT)
              (⟨u.val, by
                have hle : mid.length ≤ T.length := by simp [mid]
                exact lt_of_lt_of_le u.isLt hle⟩ : Fin T.length) := step1
        _ = pathEdgesNat (v 0) (Fin.tail v)
              (⟨u.val, by
                have mt : mid.length ≤ t.val := by simp [mid]
                have uv : u.val < t.val := lt_of_lt_of_le u.isLt mt
                exact lt_of_lt_of_le uv (Nat.le_of_lt t.isLt)⟩ : Fin p) := step2
        _ = pathEdgesNat i v (emb u) := by
              have hts := tailshift
              -- successors have value `u+1`
              simpa [emb] using hts
    have car := fiber_card_le_of_indexEmbedding FM GG emb comp e
    have ge : e ∈ (Finset.univ.image GG) := by
      rcases Finset.mem_image.mp he with ⟨u, hu, eu⟩
      have cc := comp u
      exact Finset.mem_image.mpr ⟨emb u, Finset.mem_univ _, eu ▸ cc.symm⟩
    have tw := leading_fibers_two i v h e ge
    change ((Finset.univ : Finset (Fin mid.length)).filter
       (fun r => FM r = e)).card ≤ 2
    exact car.trans_eq tw
  · intro e he
    -- suffix positions start immediately after the returning edge
    let emb : Fin rest.length ↪ Fin (p+1) :=
      ⟨fun u => ⟨(t.val+1) + u.val + 1, by
          have ur : u.val < p - (t.val+1) := by
            simpa [rest, lenT] using u.isLt
          omega⟩,
       by
        intro a b eq
        apply Fin.ext
        have ev := congrArg Fin.val eq
        dsimp at ev
        omega⟩
    let FR : Fin rest.length → {z : ℕ × ℕ // z.1 ≤ z.2} :=
      pathEdgesNat i (listPath rest zr.bound)
    let GG : Fin (p+1) → {z : ℕ × ℕ // z.1 ≤ z.2} := pathEdgesNat i v
    have comp : ∀ u, FR u = GG (emb u) := by
      intro u
      have dr := pathEdges_drop_compat (v 0) i T (t.val+1) bdT zr.bound hend
          (show Fin (T.drop (t.val+1)).length from u)
      have fullindex : (t.val+1) + u.val < p := by
        have ur : u.val < p - (t.val+1) := by simpa [rest, lenT] using u.isLt
        omega
      have ll := pathEdges_pathList_cast (v 0) (Fin.tail v) bdT
          (⟨(t.val+1)+u.val, (by simpa [pathList] using fullindex)⟩ : Fin (pathList (Fin.tail v)).length)
      have step1 :
          pathEdgesNat i (listPath rest zr.bound) u =
            pathEdgesNat (v 0) (listPath T bdT)
              (⟨(t.val+1)+u.val, by rw [lenT]; exact fullindex⟩ : Fin T.length) := by
          simpa [rest] using dr
      have step2 :
          pathEdgesNat (v 0) (listPath T bdT)
              (⟨(t.val+1)+u.val, by rw [lenT]; exact fullindex⟩ : Fin T.length) =
            pathEdgesNat (v 0) (Fin.tail v)
              (⟨(t.val+1)+u.val, fullindex⟩ : Fin p) := by
          dsimp [T]
          simpa using ll
      have sh := pathEdges_tail_shift i v
          (⟨(t.val+1)+u.val, fullindex⟩ : Fin p)
      dsimp [FR, GG]
      calc
        pathEdgesNat i (listPath rest zr.bound) u =
            pathEdgesNat (v 0) (listPath T bdT)
              (⟨(t.val+1)+u.val, by rw [lenT]; exact fullindex⟩ : Fin T.length) := step1
        _ = pathEdgesNat (v 0) (Fin.tail v)
              (⟨(t.val+1)+u.val, fullindex⟩ : Fin p) := step2
        _ = pathEdgesNat i v (emb u) := by
              simpa [emb, Nat.add_assoc] using sh
    have car := fiber_card_le_of_indexEmbedding FR GG emb comp e
    have ge : e ∈ (Finset.univ.image GG) := by
      rcases Finset.mem_image.mp he with ⟨u, hu, eu⟩
      have cc := comp u
      exact Finset.mem_image.mpr ⟨emb u, Finset.mem_univ _, eu ▸ cc.symm⟩
    have tw := leading_fibers_two i v h e ge
    change ((Finset.univ : Finset (Fin rest.length)).filter
       (fun r => FR r = e)).card ≤ 2
    exact car.trans_eq tw
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PieceFiber.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PatternGraft.lean
section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Equality of fibres of two words gives an honest equivalence on the
actually used alphabets.  This is often more convenient than counting the
fibres: it also remembers where every occurrence is sent. -/
lemma exists_rangeEquiv_of_rel {ι α β : Type*}
    (f : ι → α) (g : ι → β)
    (h : ∀ i j, f i = f j ↔ g i = g j) :
    ∃ e : (Set.range f ≃ Set.range g),
      ∀ i : ι, e ⟨f i, Set.mem_range_self i⟩ =
        ⟨g i, Set.mem_range_self i⟩ := by
  classical
  -- choose a representative occurrence of every used letter on either side
  choose sf hsf using (fun x : Set.range f => x.property)
  choose sg hsg using (fun x : Set.range g => x.property)
  -- `Set.mem_range` produces equations with the chosen occurrence first.
  -- Keeping both equations named makes the inverse calculations painless.
  let F : Set.range f → Set.range g := fun x =>
    ⟨g (sf x), Set.mem_range_self (sf x)⟩
  let G : Set.range g → Set.range f := fun y =>
    ⟨f (sg y), Set.mem_range_self (sg y)⟩
  have F_spec (i : ι) : F ⟨f i, Set.mem_range_self i⟩ =
      ⟨g i, Set.mem_range_self i⟩ := by
    apply Subtype.ext
    change g (sf ⟨f i, Set.mem_range_self i⟩) = g i
    apply (h _ _).1
    -- representative equation
    have z := hsf (⟨f i, Set.mem_range_self i⟩ : Set.range f)
    -- `z : f (sf _) = (..).val`
    simpa using z
  have G_spec (i : ι) : G ⟨g i, Set.mem_range_self i⟩ =
      ⟨f i, Set.mem_range_self i⟩ := by
    apply Subtype.ext
    change f (sg ⟨g i, Set.mem_range_self i⟩) = f i
    apply (h _ _).2
    have z := hsg (⟨g i, Set.mem_range_self i⟩ : Set.range g)
    simpa using z
  have left (x : Set.range f) : G (F x) = x := by
    rcases x with ⟨x, i, rfl⟩
    rw [F_spec]
    exact G_spec _
  have right (y : Set.range g) : F (G y) = y := by
    rcases y with ⟨y, i, rfl⟩
    rw [G_spec]
    exact F_spec _
  exact ⟨{ toFun := F, invFun := G, left_inv := left, right_inv := right }, F_spec⟩
end
end WignerSupport

namespace WignerSupport
section
variable {ι κ α β δ : Type*}
/-- If two alphabets, each carrying the same equality relation, are disjoint,
then their tagged union carries the same equality relation.  This is the tiny
set-theoretic part of the first-return/grafting argument.  The tags are
important: without disjointness equality across the two pieces would create
spurious patterns. -/
lemma sum_elim_rel_of_disjoint
    (c : ι → α) (r : κ → α)
    (c' : ι → β) (r' : κ → β)
    (hc : ∀ i j, c i = c j ↔ c' i = c' j)
    (hr : ∀ i j, r i = r j ↔ r' i = r' j)
    (hd : Disjoint (Set.range c) (Set.range r))
    (hd' : Disjoint (Set.range c') (Set.range r')) :
    ∀ u v : ι ⊕ κ,
      Sum.elim c r u = Sum.elim c r v ↔
        Sum.elim c' r' u = Sum.elim c' r' v := by
  have cross {i : ι} {j : κ} : c i ≠ r j := by
    intro h
    have hmeet : r j ∈ (Set.range c ∩ Set.range r) :=
      ⟨⟨i, h⟩, ⟨j, rfl⟩⟩
    exact (Set.disjoint_left.1 hd hmeet.1 hmeet.2)
  have cross' {i : ι} {j : κ} : c' i ≠ r' j := by
    intro h
    exact Set.disjoint_left.1 hd' (Set.mem_range_self i) (h ▸ Set.mem_range_self j)
  intro u v
  cases u with
  | inl i =>
    cases v with
    | inl j => exact hc i j
    | inr j =>
      change c i = r j ↔ c' i = r' j
      exact ⟨fun h => (cross h).elim, fun h => (cross' h).elim⟩
  | inr i =>
    cases v with
    | inl j =>
      change r i = c j ↔ r' i = c' j
      exact ⟨fun h => (cross h.symm).elim,
        fun h => (cross' h.symm).elim⟩
    | inr j => exact hr i j

lemma sum_elim_rel_comp_of_disjoint
    (c : ι → α) (r : κ → α)
    (c' : ι → β) (r' : κ → β)
    (hc : ∀ i j, c i = c j ↔ c' i = c' j)
    (hr : ∀ i j, r i = r j ↔ r' i = r' j)
    (hd : Disjoint (Set.range c) (Set.range r))
    (hd' : Disjoint (Set.range c') (Set.range r'))
    (tag : δ → ι ⊕ κ) :
    ∀ u v : δ,
      Sum.elim c r (tag u) = Sum.elim c r (tag v) ↔
        Sum.elim c' r' (tag u) = Sum.elim c' r' (tag v) := by
  intro u v
  exact sum_elim_rel_of_disjoint c r c' r' hc hr hd hd' (tag u) (tag v)
end
end WignerSupport
namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Positions of a grafted word.  It consists of a root letter, the whole
child word, and the root word again; the two copies of the root are tagged
by the *same* root position. -/
def graftTag (m k : ℕ) (z : Fin (m+k+3)) : Fin (m+1) ⊕ Fin (k+1) :=
  if h0 : z.val = 0 then
    Sum.inr ⟨0, Nat.zero_lt_succ k⟩
  else if hm : z.val < m+2 then
    Sum.inl ⟨z.val-1, by omega⟩
  else
    Sum.inr ⟨z.val-(m+2), by omega⟩

/-- The word obtained by adjoining a new bridge from the old root to a
child excursion.  The child positions include its initial vertex; the root
positions include the (single) distinguished root. -/
def graftWord {α : Type*} {m k : ℕ}
    (child : Fin (m+1) → α) (root : Fin (k+1) → α) :
    Fin (m+k+3) → α :=
  fun u => Sum.elim child root (graftTag m k u)

lemma graftWord_rel_of_disjoint {α β : Type*} {m k : ℕ}
    (c : Fin (m+1) → α) (r : Fin (k+1) → α)
    (c' : Fin (m+1) → β) (r' : Fin (k+1) → β)
    (hc : ∀ i j, c i = c j ↔ c' i = c' j)
    (hr : ∀ i j, r i = r j ↔ r' i = r' j)
    (hd : Disjoint (Set.range c) (Set.range r))
    (hd' : Disjoint (Set.range c') (Set.range r')) :
    ∀ i j, graftWord c r i = graftWord c r j ↔
      graftWord c' r' i = graftWord c' r' j := by
  exact sum_elim_rel_comp_of_disjoint c r c' r' hc hr hd hd'
    (graftTag m k)

lemma cons_listPath_val_mem_walkVertices {n : ℕ} (root : Fin n)
    (xs : List ℕ) (bd : ∀ a ∈ xs, a < n) (u : Fin (xs.length+1)) :
    ((@Fin.cons xs.length (fun _ => Fin n) root (listPath xs bd)) u).val ∈
      walkVertices root.val xs := by
  classical
  refine Fin.cases ?_ (fun j => ?_) u
  · exact walkVertices_root_mem _ _
  · -- a tail letter is literally the corresponding entry of the list
    unfold walkVertices listPath
    simp

/-- `walkVertices` is the finite, value-valued version of the ranges of
`root :: xs`.  Consequently bridge disjointness for the two list pieces is
exactly disjointness of the used alphabets of the two finite words. -/
lemma disjoint_ranges_cons_listPath {n : ℕ}
    (child root : Fin n) (xs ys : List ℕ)
    (bx : ∀ a ∈ xs, a < n) (by' : ∀ a ∈ ys, a < n)
    (h : Disjoint (walkVertices child.val xs) (walkVertices root.val ys)) :
    Disjoint
      (Set.range (@Fin.cons xs.length (fun _ => Fin n) child (listPath xs bx)))
      (Set.range (@Fin.cons ys.length (fun _ => Fin n) root (listPath ys by'))) := by
  classical
  apply Set.disjoint_left.2
  intro z hz hzr
  rcases hz with ⟨i, rfl⟩
  rcases hzr with ⟨j, eq⟩
  have memc := cons_listPath_val_mem_walkVertices child xs bx i
  have memr := cons_listPath_val_mem_walkVertices root ys by' j
  have ev :
      ((@Fin.cons xs.length (fun _ => Fin n) child (listPath xs bx)) i).val =
      ((@Fin.cons ys.length (fun _ => Fin n) root (listPath ys by')) j).val :=
        congrArg Fin.val eq.symm
  exact Finset.disjoint_left.1 h memc (ev ▸ memr)
end
end WignerSupport

namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
-- evaluation formula for the grafted word
lemma graftWord_zero {α : Type*} {m k : ℕ}
    (b : α) (x : Fin m → α) (a : α) (y : Fin k → α) :
    graftWord (@Fin.cons m (fun _ => α) b x)
      (@Fin.cons k (fun _ => α) a y) (0 : Fin (m+k+3)) = a := by
  simp [graftWord, graftTag]

lemma graftWord_child {α : Type*} {m k : ℕ}
    (b : α) (x : Fin m → α) (a : α) (y : Fin k → α)
    (j : Fin (m+1)) :
    graftWord (@Fin.cons m (fun _ => α) b x)
      (@Fin.cons k (fun _ => α) a y)
      (⟨j.val+1, by omega⟩ : Fin (m+k+3)) =
        (@Fin.cons m (fun _ => α) b x) j := by
  have nz : j.val + 1 ≠ 0 := by omega
  have le : j.val + 1 < m + 2 := by omega
  simp [graftWord, graftTag, nz, le]

lemma graftWord_roottail {α : Type*} {m k : ℕ}
    (b : α) (x : Fin m → α) (a : α) (y : Fin k → α)
    (j : Fin (k+1)) :
    graftWord (@Fin.cons m (fun _ => α) b x)
      (@Fin.cons k (fun _ => α) a y)
      (⟨m+2+j.val, by omega⟩ : Fin (m+k+3)) =
        (@Fin.cons k (fun _ => α) a y) j := by
  have nz : m + 2 + j.val ≠ 0 := by omega
  have nl : ¬ m + 2 + j.val < m + 2 := by omega
  have sub : m + 2 + j.val - (m+2) = j.val := by omega
  simp [graftWord, graftTag, nz, nl, sub]
end
end WignerSupport

namespace WignerSupport
/-- Literal list of a first-return split.  The second traversal of the
bridge contributes the old root (not the child); getting this letter right
is the small orientation issue that would otherwise spoil grafting equality
patterns. -/
lemma leading_split_word_list {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (h : IsLeadingPath i v)
    (t : Fin p)
    (ht : pathEdgesNat (v 0) (Fin.tail v) t = edgeNat i.val (v 0).val) :
    i.val :: pathList v =
      i.val :: (v 0).val ::
        ((pathList (Fin.tail v)).take t.val ++
          i.val :: (pathList (Fin.tail v)).drop (t.val+1)) := by
  classical
  let T : List ℕ := pathList (Fin.tail v)
  have len : T.length = p := by simp [T, pathList]
  have lt : t.val < T.length := by simpa [len] using t.isLt
  have vv : pathList v = (v 0).val :: T := by
    dsimp [T, pathList]
    -- a word is its head followed by its tail
    have ofn := (List.ofFn_cons (v 0).val
       (fun r : Fin p => ((Fin.tail v) r).val))
    -- compare the functions; both are values of `v`
    have c : (@Fin.cons p (fun _ => ℕ) (v 0).val
        (fun r : Fin p => ((Fin.tail v) r).val)) =
        (fun r : Fin (p+1) => (v r).val) := by
      funext r
      refine Fin.cases ?_ (fun j => ?_) r
      · rfl
      · rfl
    simpa [c] using ofn
  rw [vv]
  congr 2
  -- split off the returning letter at index `t`
  have spl : T.take t.val ++ T.drop t.val = T := List.take_append_drop _ _
  have ret : T[t.val]'lt = i.val := by
    have back := (leading_second_edge_return i v h t ht).2
    change (List.ofFn (fun r : Fin p => ((Fin.tail v) r).val))[t.val] = _
    have ofn := (List.getElem_ofFn
      (f := fun r : Fin p => ((Fin.tail v) r).val)
      (i := t.val) (by simp))
    calc
      _ = ((Fin.tail v) t).val := by convert ofn using 1 <;> rfl
      _ = _ := back
  have decomp : T.drop t.val = T[t.val]'lt :: T.drop (t.val+1) := by
    have one := (List.drop_eq_getElem_cons (l:=T) lt)
    -- library states drop at `n`; simplify the proof argument
    simpa using one
  calc
    T = T.take t.val ++ T.drop t.val := spl.symm
    _ = T.take t.val ++ (T[t.val]'lt :: T.drop (t.val+1)) := by rw [decomp]
    _ = T.take t.val ++ (i.val :: T.drop (t.val+1)) := by rw [ret]
end WignerSupport

namespace WignerSupport
lemma wordPattern_graft_of_disjoint {n d m k : ℕ}
    (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
    (c' : Fin (m+1) → Fin d) (r' : Fin (k+1) → Fin d)
    (hc : wordPattern c = wordPattern c')
    (hr : wordPattern r = wordPattern r')
    (hd : Disjoint (Set.range c) (Set.range r))
    (hd' : Disjoint (Set.range c') (Set.range r')) :
    wordPattern (graftWord c r) = wordPattern (graftWord c' r') := by
  apply (wordPattern_eq_iff _ _).2
  have ec := (wordPattern_eq_iff c c').1 hc
  have er := (wordPattern_eq_iff r r').1 hr
  exact graftWord_rel_of_disjoint c r c' r' ec er hd hd'
end WignerSupport

namespace WignerSupport
/-- Fin-valued form of the bridge separation for the two leading pieces.
Unlike the finite `walkVertices` statement, this can feed directly to equality
pattern lemmas. -/
lemma leading_split_ranges_disjoint {n p : ℕ} (i : Fin n)
    (v : Fin (p+1) → Fin n) (z : IsLeadingPath i v)
    (t : Fin p)
    (ht : pathEdgesNat (v 0) (Fin.tail v) t = edgeNat i.val (v 0).val) :
    let mid : List ℕ := (pathList (Fin.tail v)).take t.val
    let rest : List ℕ := (pathList (Fin.tail v)).drop (t.val+1)
    let zm : ClosedEqPiece n (v 0) mid :=
      (leading_split_closedEqPieces i v z t ht).1
    let zr : ClosedEqPiece n i rest :=
      (leading_split_closedEqPieces i v z t ht).2
    Disjoint
      (Set.range (@Fin.cons mid.length (fun _ => Fin n) (v 0)
        (listPath mid zm.bound)))
      (Set.range (@Fin.cons rest.length (fun _ => Fin n) i
        (listPath rest zr.bound))) := by
  dsimp
  let mid : List ℕ := (pathList (Fin.tail v)).take t.val
  let rest : List ℕ := (pathList (Fin.tail v)).drop (t.val+1)
  have co := leading_split_closedEqPieces i v z t ht
  change ClosedEqPiece n (v 0) mid ∧ ClosedEqPiece n i rest at co
  let zm : ClosedEqPiece n (v 0) mid := co.1
  let zr : ClosedEqPiece n i rest := co.2
  change Disjoint
      (Set.range (@Fin.cons mid.length (fun _ => Fin n) (v 0)
        (listPath mid zm.bound)))
      (Set.range (@Fin.cons rest.length (fun _ => Fin n) i
        (listPath rest zr.bound)))
  apply disjoint_ranges_cons_listPath
  have hb := leading_split_vertices_disjoint i v z t ht
  change Disjoint (walkVertices (v 0).val mid)
      (walkVertices i.val rest) at hb
  exact hb
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PatternGraft.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/SplitGraftProof.lean
section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Literal order of the positions of a graft.  Notice that the old root
is present twice: once at position `0` and once as the first position of
`r`.  This is the source of the two root letters in a first-return split. -/
lemma ofFn_graftWord {α : Type*} {m k : ℕ}
    (c : Fin (m+1) → α) (r : Fin (k+1) → α) :
    List.ofFn (graftWord c r) =
      r 0 :: (List.ofFn c ++ List.ofFn r) := by
 classical
 apply List.ext_getElem
 · simp <;> omega
 · intro z hz hz'
   by_cases h0 : z = 0
   · subst z
     simp [graftWord, graftTag]
   · have hpos : 0 < z := Nat.pos_of_ne_zero h0
     obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
     -- z=w+1
     by_cases hm : w+1 < m+2
     · have wlt : w < m+1 := by omega
       let j : Fin (m+1) := ⟨w, wlt⟩
       have hjlen : w < (List.ofFn c).length := by simpa using wlt
       rw [List.getElem_ofFn]
       rw [List.getElem_cons_succ]
       rw [List.getElem_append_left hjlen]
       rw [List.getElem_ofFn]
       -- evaluate the tag
       dsimp [graftWord, graftTag]
       have nz : w + 1 ≠ 0 := by omega
       have lt : w + 1 < m + 2 := hm
       simp [nz, lt]
     · have hbnd : w + 1 < m + k + 3 := by simp at hz; omega
       have low : m + 2 ≤ w+1 := by omega
       -- write w+1=m+2+j
       have wlow : m+1 ≤ w := by omega
       obtain ⟨j, eqj⟩ := Nat.exists_eq_add_of_le wlow
       -- eqj : w = m+1 + j? check orientation
       -- use obtain value then substitute w
       subst w
       have jlt : j < k+1 := by omega
       rw [List.getElem_ofFn]
       -- peel the leading root, then the append
       -- the index after the leading cons is `m+1+j`
       rw [List.getElem_cons_succ]
       have hright : (List.ofFn c).length ≤ m + 1 + j := by simp
       rw [List.getElem_append_right hright]
       rw [List.getElem_ofFn]
       dsimp [graftWord, graftTag]
       have nz : m + 2 + j ≠ 0 := by omega
       have nlt : ¬ (m + 2 + j < m + 2) := by omega
       have hh : ¬ m + 1 + j ≤ m := by omega
       simp [hh]


/-- The finite word `Fin.cons i v` of a leading path is literally the
word obtained by grafting its child-side and root-side first-return pieces.
All transports of the domain are made through the displayed length equality;
there is no tacit assumption that either piece is nonempty. -/
lemma leading_split_word_eq_graft {n a : ℕ} (i : Fin n)
    (v : Fin (a+1) → Fin n) (z : IsLeadingPath i v)
    (t : Fin a)
    (ht : pathEdgesNat (v 0) (Fin.tail v) t = edgeNat i.val (v 0).val) :
    let mid : List ℕ := (pathList (Fin.tail v)).take t.val
    let rest : List ℕ := (pathList (Fin.tail v)).drop (t.val+1)
    let zm : ClosedEqPiece n (v 0) mid :=
      (leading_split_closedEqPieces i v z t ht).1
    let zr : ClosedEqPiece n i rest :=
      (leading_split_closedEqPieces i v z t ht).2
    let len : mid.length + rest.length + 3 = a + 2 := by
      -- the tail of the tail has length `a`
      have h1 : mid.length = t.val := by
        apply List.length_take_of_le
        have : t.val ≤ (pathList (Fin.tail v)).length := by
          simp [pathList]
        exact this
      have h2 : rest.length = a - (t.val+1) := by simp [rest, pathList]
      omega
    (Fin.cons i v) =
      (fun u : Fin (a+2) =>
        graftWord
          (@Fin.cons mid.length (fun _ => Fin n) (v 0)
            (listPath mid zm.bound))
          (@Fin.cons rest.length (fun _ => Fin n) i
            (listPath rest zr.bound))
          (Fin.cast len.symm u)) := by
  classical
  dsimp
  let mid : List ℕ := (pathList (Fin.tail v)).take t.val
  let rest : List ℕ := (pathList (Fin.tail v)).drop (t.val+1)
  have pcs := leading_split_closedEqPieces i v z t ht
  change ClosedEqPiece n (v 0) mid ∧ ClosedEqPiece n i rest at pcs
  let zm : ClosedEqPiece n (v 0) mid := pcs.1
  let zr : ClosedEqPiece n i rest := pcs.2
  let len : mid.length + rest.length + 3 = a + 2 := by
    have h1 : mid.length = t.val := by
      dsimp [mid]
      apply List.length_take_of_le
      simp [pathList]
    have h2 : rest.length = a - (t.val+1) := by
      dsimp [rest]
      simp [pathList]
    omega
  change (Fin.cons i v) =
    (fun u : Fin (a+2) =>
      graftWord
        (@Fin.cons mid.length (fun _ => Fin n) (v 0)
          (listPath mid zm.bound))
        (@Fin.cons rest.length (fun _ => Fin n) i
          (listPath rest zr.bound))
        (Fin.cast len.symm u))
  -- equality of `Fin n` valued words is best checked on the ordinary list of
  -- values. `pathList` already is this list of values.
  let child : Fin (mid.length+1) → Fin n :=
    @Fin.cons mid.length (fun _ => Fin n) (v 0) (listPath mid zm.bound)
  let root : Fin (rest.length+1) → Fin n :=
    @Fin.cons rest.length (fun _ => Fin n) i (listPath rest zr.bound)
  let G : Fin (mid.length + rest.length + 3) → Fin n := graftWord child root
  have childtail :
      List.ofFn (fun j : Fin mid.length =>
        (listPath mid zm.bound j).val) = mid := by
    change List.ofFn (fun j : Fin mid.length => mid[j]) = mid
    exact List.ofFn_getElem
  have roottail :
      List.ofFn (fun j : Fin rest.length =>
        (listPath rest zr.bound j).val) = rest := by
    change List.ofFn (fun j : Fin rest.length => rest[j]) = rest
    exact List.ofFn_getElem
  have childVals : (List.ofFn child).map Fin.val = (v 0).val :: mid := by
    -- `ofFn_cons` and `listPath` give back precisely `mid`
    simpa [child, List.ofFn_cons, List.map_cons, Function.comp_def]
      using congrArg (List.cons (v 0).val) childtail
  have rootVals : (List.ofFn root).map Fin.val = i.val :: rest := by
    simpa [root, List.ofFn_cons, List.map_cons, Function.comp_def]
      using congrArg (List.cons i.val) roottail
  have origVals : (List.ofFn (Fin.cons i v)).map Fin.val =
      i.val :: pathList v := by
    change _ = i.val :: List.ofFn (fun j : Fin (a+1) => (v j).val)
    simp [List.ofFn_cons, List.map_cons, Function.comp_def]
  have splitvals : i.val :: pathList v =
      i.val :: (v 0).val :: (mid ++ i.val :: rest) := by
    simpa [mid, rest] using (leading_split_word_list i v z t ht)
  have GV : (List.ofFn G).map Fin.val =
      i.val :: ( (v 0).val :: (mid ++ i.val :: rest)) := by
    calc
      (List.ofFn G).map Fin.val =
          ((List.ofFn root)[0]).val ::
              ((List.ofFn child).map Fin.val ++ (List.ofFn root).map Fin.val) := by
            -- first map the graft ordering lemma
            rw [show G = graftWord child root by rfl]
            rw [ofFn_graftWord child root]
            simp
      _ = i.val :: ((v 0).val :: (mid ++ i.val :: rest)) := by
            have hroot0 : (List.ofFn root)[0] = i := by simp [root]
            rw [hroot0, childVals, rootVals]
            simp
  -- comparison after casting the domain.  `List.ofFn` commutes with this
  -- cast; avoiding that lemma directly is easier by appealing to equality
  -- of entries at a position of the common length.
  funext u
  apply Fin.ext
  -- The two lists of values agree; evaluate at `u`.
  have LV : (List.ofFn (Fin.cons i v)).map Fin.val =
      (List.ofFn G).map Fin.val := by
    rw [origVals, splitvals, GV]
  have getu := congrArg (fun L : List ℕ => L[u.val]?) LV
  have hu : u.val < a + 2 := u.isLt
  have hu' : u.val < mid.length + rest.length + 3 := by
    -- `len` has the order of lengths used by `G`
    simpa [len] using hu
  have hval : ((@Fin.cons (a+1) (fun _ => Fin n) i v) u).val =
      (G ⟨u.val, hu'⟩).val := by
    -- optional indexing of an `ofFn` is insensitive to the proof argument
    -- first expose the optional indexing of `ofFn`, before `simp` can
    -- expand `ofFn_succ`.
    simp only [List.getElem?_map] at getu
    simp only [List.getElem?_ofFn] at getu
    simp [hu, hu'] at getu
    exact getu
  -- and casting the argument only changes its bound proof
  simpa [G, Fin.cast] using hval

end
end WignerSupport

namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
/-- Grafting commutes with a transport of the total length.  This is the
form in which equality of the two smaller patterns is usually used: the
ambient path has length `p`, whereas the two pieces have lengths `m` and
`k`. -/
lemma wordPattern_cast_graft_of_disjoint {n d m k p : ℕ}
    (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
    (c' : Fin (m+1) → Fin d) (r' : Fin (k+1) → Fin d)
    (h : m+k+3 = p)
    (hc : wordPattern c = wordPattern c')
    (hr : wordPattern r = wordPattern r')
    (sep : Disjoint (Set.range c) (Set.range r))
    (sep' : Disjoint (Set.range c') (Set.range r')) :
    wordPattern (fun u : Fin p => graftWord c r (Fin.cast h.symm u)) =
      wordPattern (fun u : Fin p => graftWord c' r' (Fin.cast h.symm u)) := by
  classical
  have same := wordPattern_graft_of_disjoint c r c' r' hc hr sep sep'
  have rel := (wordPattern_eq_iff (graftWord c r)
      (graftWord c' r')).1 same
  apply (wordPattern_eq_iff _ _).2
  intro u v
  exact rel (Fin.cast h.symm u) (Fin.cast h.symm v)
end
end WignerSupport

namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
lemma graftWord_zero' {α : Type*} {m k : ℕ}
    (c : Fin (m+1) → α) (r : Fin (k+1) → α) :
    graftWord c r (0 : Fin (m+k+3)) = r 0 := by
 simp [graftWord, graftTag]
lemma graftWord_child' {α : Type*} {m k : ℕ}
    (c : Fin (m+1) → α) (r : Fin (k+1) → α)
    (j : Fin (m+1)) :
    graftWord c r (⟨j.val+1, by omega⟩ : Fin (m+k+3)) = c j := by
 rw [← cons_tail_zero_eq c, ← cons_tail_zero_eq r]
 exact graftWord_child _ _ _ _ j
lemma graftWord_roottail' {α : Type*} {m k : ℕ}
    (c : Fin (m+1) → α) (r : Fin (k+1) → α)
    (j : Fin (k+1)) :
    graftWord c r (⟨m+2+j.val, by omega⟩ : Fin (m+k+3)) = r j := by
 rw [← cons_tail_zero_eq c, ← cons_tail_zero_eq r]
 exact graftWord_roottail _ _ _ _ j

lemma image_graftWord {α : Type*} [DecidableEq α] {m k : ℕ}
    (c : Fin (m+1) → α) (r : Fin (k+1) → α) :
    (Finset.univ.image (graftWord c r)) =
      (Finset.univ.image c) ∪ (Finset.univ.image r) := by
 classical
 ext z
 constructor
 · intro h
   rcases Finset.mem_image.mp h with ⟨u,-,rfl⟩
   -- use tag expression
   change Sum.elim c r (graftTag m k u) ∈ _
   cases hh : graftTag m k u with
   | inl a =>
       exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
   | inr a =>
       exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
 · intro h
   rcases Finset.mem_union.mp h with h|h
   · rcases Finset.mem_image.mp h with ⟨j,-,rfl⟩
     exact Finset.mem_image.mpr ⟨(⟨j.val+1, by omega⟩ : Fin (m+k+3)), Finset.mem_univ _, graftWord_child' c r j⟩
   · rcases Finset.mem_image.mp h with ⟨j,-,rfl⟩
     exact Finset.mem_image.mpr ⟨(⟨m+2+j.val, by omega⟩ : Fin (m+k+3)), Finset.mem_univ _, graftWord_roottail' c r j⟩

lemma graftWord_isLeading {n m k : ℕ}
 (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
 (hc : IsLeadingWord m n c) (hr : IsLeadingWord k n r)
 (sep : Disjoint (Set.range c) (Set.range r)) :
 IsLeadingWord (m+k+2) n (graftWord c r) := by
 classical
 let w : Fin (m+k+3) → Fin n := graftWord c r
 have cclose : c (Fin.last m) = c 0 := by
   have en := pathEnd_eq_cons_last (c 0) (Fin.tail c)
   have cc := hc.1
   change pathEnd m (c 0) (Fin.tail c) = c 0 at cc
   have all := cons_tail_zero_eq c
   -- use lemma derived
   rw [en] at cc
   simpa [all] using cc
 have rclose : r (Fin.last k) = r 0 := by
   have en := pathEnd_eq_cons_last (r 0) (Fin.tail r)
   have rr := hr.1
   change pathEnd k (r 0) (Fin.tail r) = r 0 at rr
   rw [en] at rr
   simpa [cons_tail_zero_eq r] using rr
 have w0 : w 0 = r 0 := graftWord_zero' c r
 have wec (j : Fin (m+1)) :
     w (⟨j.val+1, by omega⟩ : Fin (m+k+3)) = c j := graftWord_child' c r j
 have wer (j : Fin (k+1)) :
     w (⟨m+2+j.val, by omega⟩ : Fin (m+k+3)) = r j := graftWord_roottail' c r j
 -- closed
 have wclose : pathEnd (m+k+2) (w 0) (Fin.tail w) = w 0 := by
   rw [pathEnd_eq_cons_last]
   rw [cons_tail_zero_eq w]
   have hidx : (Fin.last (m+k+2)) =
       (⟨m+2+k, by omega⟩ : Fin (m+k+3)) := by
     apply Fin.ext
     change m+k+2 = m+2+k
     omega
   rw [hidx]
   have wh : w (⟨m+2+k, by omega⟩ : Fin (m+k+3)) = r (Fin.last k) := by
     simpa using (wer (Fin.last k))
   rw [wh, rclose, w0]
 -- repetitions. restate edge formula
 have ew (u : Fin (m+k+2)) :
     pathEdgesNat (w 0) (Fin.tail w) u =
       edgeNat (w u.castSucc).val (w u.succ).val := pathEdges_word w u
 have ec (u : Fin m) :
     pathEdgesNat (w 0) (Fin.tail w)
       (⟨u.val+1, by omega⟩ : Fin (m+k+2)) =
       pathEdgesNat (c 0) (Fin.tail c) u := by
   rw [ew, pathEdges_word c u]
   change edgeNat
       (w (⟨u.val+1, by omega⟩ : Fin (m+k+3))).val
       (w (⟨u.val+2, by omega⟩ : Fin (m+k+3))).val = _
   rw [show w (⟨u.val+1, by omega⟩ : Fin (m+k+3)) = c u.castSucc by
     simpa using (wec (u.castSucc))]
   rw [show w (⟨u.val+2, by omega⟩ : Fin (m+k+3)) = c u.succ by
     simpa using (wec (u.succ))]
 have er (u : Fin k) :
     pathEdgesNat (w 0) (Fin.tail w)
       (⟨m+2+u.val, by omega⟩ : Fin (m+k+2)) =
       pathEdgesNat (r 0) (Fin.tail r) u := by
   rw [ew, pathEdges_word r u]
   change edgeNat
       (w (⟨m+2+u.val, by omega⟩ : Fin (m+k+3))).val
       (w (⟨m+2+(u.val+1), by omega⟩ : Fin (m+k+3))).val = _
   rw [show w (⟨m+2+u.val, by omega⟩ : Fin (m+k+3)) = r u.castSucc by
     simpa using (wer (u.castSucc))]
   rw [show w (⟨m+2+(u.val+1), by omega⟩ : Fin (m+k+3)) = r u.succ by
     simpa using (wer (u.succ))]
 have e0 : pathEdgesNat (w 0) (Fin.tail w)
       (0 : Fin (m+k+2)) = edgeNat (r 0).val (c 0).val := by
   rw [ew]
   change edgeNat (w (0 : Fin (m+k+3))).val
       (w (1 : Fin (m+k+3))).val = _
   rw [w0]
   rw [show w (1 : Fin (m+k+3)) = c 0 by
     simpa using (wec (0 : Fin (m+1)))]
 have eb : pathEdgesNat (w 0) (Fin.tail w)
       (⟨m+1, by omega⟩ : Fin (m+k+2)) = edgeNat (r 0).val (c 0).val := by
   rw [ew]
   change edgeNat (w (⟨m+1, by omega⟩ : Fin (m+k+3))).val
       (w (⟨m+2, by omega⟩ : Fin (m+k+3))).val = _
   have q1 : w (⟨m+1, by omega⟩ : Fin (m+k+3)) = c (Fin.last m) := by
     simpa using (wec (Fin.last m))
   have q2 : w (⟨m+2, by omega⟩ : Fin (m+k+3)) = r 0 := by
     simpa using (wer (0 : Fin (k+1)))
   rw [q1, q2, cclose]
   exact edgeNat_comm _ _
 have wrep : ∀ u : Fin (m+k+2), ∃ s : Fin (m+k+2), s ≠ u ∧
       pathEdgesNat (w 0) (Fin.tail w) s =
       pathEdgesNat (w 0) (Fin.tail w) u := by
   intro u
   by_cases z0 : u.val = 0
   · refine ⟨⟨m+1, by omega⟩, ?_, ?_⟩
     · intro h; have vv := congrArg Fin.val h; simp [z0] at vv
     · have uu : u = (0 : Fin (m+k+2)) := Fin.ext z0
       rw [uu, e0, eb]
   · by_cases low : u.val < m+1
     · have pos : 0 < u.val := Nat.pos_of_ne_zero z0
       let j : Fin m := ⟨u.val-1, by omega⟩
       rcases hc.2.1 j with ⟨l, nl, eql⟩
       let s : Fin (m+k+2) := ⟨l.val+1, by omega⟩
       refine ⟨s, ?_, ?_⟩
       · intro eq
         have va := congrArg Fin.val eq
         have lj : l = j := by apply Fin.ext; dsimp [s] at va; dsimp [j]; omega
         exact nl lj
       · have uid : u = (⟨j.val+1, by omega⟩ : Fin (m+k+2)) := by
             apply Fin.ext; dsimp [j]; omega
         change pathEdgesNat (w 0) (Fin.tail w)
             (⟨l.val+1, by omega⟩ : Fin (m+k+2)) = _
         rw [ec l, uid, ec j]
         exact eql
     · by_cases midx : u.val = m+1
       · refine ⟨(0 : Fin (m+k+2)), ?_, ?_⟩
         · intro eq; have va := congrArg Fin.val eq; simp [midx] at va
         · have uu : u = (⟨m+1, by omega⟩ : Fin (m+k+2)) := Fin.ext midx
           rw [uu, e0, eb]
       · have ge : m+2 ≤ u.val := by omega
         let j : Fin k := ⟨u.val-(m+2), by omega⟩
         rcases hr.2.1 j with ⟨l, nl, eql⟩
         let s : Fin (m+k+2) := ⟨m+2+l.val, by omega⟩
         refine ⟨s, ?_, ?_⟩
         · intro eq
           have va := congrArg Fin.val eq
           have lj : l = j := by apply Fin.ext; dsimp [s] at va; dsimp [j]; omega
           exact nl lj
         · have uid : u = (⟨m+2+j.val, by omega⟩ : Fin (m+k+2)) := by
               apply Fin.ext; dsimp [j]; omega
           change pathEdgesNat (w 0) (Fin.tail w)
               (⟨m+2+l.val, by omega⟩ : Fin (m+k+2)) = _
           rw [er l, uid, er j]
           exact eql
 -- vertices of a word are its image
 have img := image_graftWord c r
 have finsep : Disjoint (Finset.univ.image c) (Finset.univ.image r) := by
   apply Finset.disjoint_left.2
   intro a ha hb
   rcases Finset.mem_image.mp ha with ⟨x,hx,hx'⟩
   rcases Finset.mem_image.mp hb with ⟨y,hy,hy'⟩
   exact Set.disjoint_left.1 sep (Set.mem_range.mpr ⟨x,hx'⟩)
       (Set.mem_range.mpr ⟨y,hy'⟩)
 -- use card_vertices_word orientations
 have ccard : (Finset.univ.image c).card = m/2+1 := by
   rw [← card_vertices_word c]
   exact hc.2.2
 have rcard : (Finset.univ.image r).card = k/2+1 := by
   rw [← card_vertices_word r]
   exact hr.2.2
 have me : 2 ∣ m := leading_even (c 0) (Fin.tail c) (by simpa [IsLeadingWord, Fin.tail_cons] using hc)
 have ke : 2 ∣ k := leading_even (r 0) (Fin.tail r) (by simpa [IsLeadingWord, Fin.tail_cons] using hr)
 have arith : (m/2+1)+(k/2+1) = (m+k+2)/2+1 := by omega
 -- assemble
 unfold IsLeadingWord IsLeadingPath
 refine ⟨wclose, wrep, ?_⟩
 rw [card_vertices_word]
 change (Finset.univ.image w).card = _
 change (Finset.univ.image (graftWord c r)).card = _
 rw [img, Finset.card_union_of_disjoint finsep, ccard, rcard]
 exact arith
end
end WignerSupport

namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
/-- Equality of two *positions' edges* is a property of the equality
pattern of the whole word.  This version is exposed because the
first-return index is chosen by an equality against the first edge. -/
lemma word_edges_eq_congr_pattern {p n d : ℕ}
    (f : Fin (p+1) → Fin n) (g : Fin (p+1) → Fin d)
    (h : wordPattern f = wordPattern g) (u v : Fin p) :
    pathEdgesNat (f 0) (Fin.tail f) u =
          pathEdgesNat (f 0) (Fin.tail f) v ↔
      pathEdgesNat (g 0) (Fin.tail g) u =
          pathEdgesNat (g 0) (Fin.tail g) v := by
  classical
  have rel := (wordPattern_eq_iff f g).1 h
  rw [pathEdges_word f u, pathEdges_word f v,
      pathEdges_word g u, pathEdges_word g v]
  rw [edgeNat_eq_iff, edgeNat_eq_iff]
  -- just equality of the two endpoints, possibly interchanged
  constructor
  · intro z
    rcases z with z|z
    · left
      refine ⟨?_, ?_⟩
      · exact congrArg Fin.val ((rel _ _).1 (Fin.ext z.1))
      · exact congrArg Fin.val ((rel _ _).1 (Fin.ext z.2))
    · right
      refine ⟨?_, ?_⟩
      · exact congrArg Fin.val ((rel _ _).1 (Fin.ext z.1))
      · exact congrArg Fin.val ((rel _ _).1 (Fin.ext z.2))
  · intro z
    rcases z with z|z
    · left
      refine ⟨?_, ?_⟩
      · exact congrArg Fin.val ((rel _ _).2 (Fin.ext z.1))
      · exact congrArg Fin.val ((rel _ _).2 (Fin.ext z.2))
    · right
      refine ⟨?_, ?_⟩
      · exact congrArg Fin.val ((rel _ _).2 (Fin.ext z.1))
      · exact congrArg Fin.val ((rel _ _).2 (Fin.ext z.2))

/-- The returning occurrence of the root edge is determined by the equality
pattern. Consequently the `Fin a` used for splitting an equality pattern is
canonical--two representatives cannot choose different child lengths. -/
lemma leading_return_index_eq_of_pattern {n d a : ℕ}
    (i : Fin n) (v : Fin (a+1) → Fin n)
    (i' : Fin d) (v' : Fin (a+1) → Fin d)
    (z : IsLeadingPath i v) (z' : IsLeadingPath i' v')
    (hp : wordPattern (Fin.cons i v) = wordPattern (Fin.cons i' v'))
    (t s : Fin a)
    (ht : pathEdgesNat (v 0) (Fin.tail v) t = edgeNat i.val (v 0).val)
    (hs : pathEdgesNat (v' 0) (Fin.tail v') s = edgeNat i'.val (v' 0).val) :
    t = s := by
  classical
  let f : Fin (a+2) → Fin n := Fin.cons i v
  let g : Fin (a+2) → Fin d := Fin.cons i' v'
  -- the first edge of the full word
  have firstf : pathEdgesNat (f 0) (Fin.tail f) (0 : Fin (a+1)) =
        edgeNat i.val (v 0).val := by
    rw [pathEdges_word f (0 : Fin (a+1))]
    rfl
  have firstg : pathEdgesNat (g 0) (Fin.tail g) (0 : Fin (a+1)) =
        edgeNat i'.val (v' 0).val := by
    rw [pathEdges_word g (0 : Fin (a+1))]
    rfl
  have tailf (l : Fin a) :
      pathEdgesNat (f 0) (Fin.tail f)
        (⟨l.val+1, by omega⟩ : Fin (a+1)) =
          pathEdgesNat (v 0) (Fin.tail v) l := by
    rw [pathEdges_word f (⟨l.val+1, by omega⟩ : Fin (a+1)),
        pathEdges_word v l]
    rfl
  have tailg (l : Fin a) :
      pathEdgesNat (g 0) (Fin.tail g)
        (⟨l.val+1, by omega⟩ : Fin (a+1)) =
          pathEdgesNat (v' 0) (Fin.tail v') l := by
    rw [pathEdges_word g (⟨l.val+1, by omega⟩ : Fin (a+1)),
        pathEdges_word v' l]
    rfl
  -- transfer the equality for `t` through the full-word pattern
  have fet : pathEdgesNat (f 0) (Fin.tail f)
        (⟨t.val+1, by omega⟩ : Fin (a+1)) =
        pathEdgesNat (f 0) (Fin.tail f) (0 : Fin (a+1)) := by
    rw [tailf, firstf]
    exact ht
  have hp' : wordPattern f = wordPattern g := hp
  have get : pathEdgesNat (g 0) (Fin.tail g)
        (⟨t.val+1, by omega⟩ : Fin (a+1)) =
        pathEdgesNat (g 0) (Fin.tail g) (0 : Fin (a+1)) :=
    (word_edges_eq_congr_pattern f g hp'
       (⟨t.val+1, by omega⟩ : Fin (a+1)) (0 : Fin (a+1))).1 fet
  have tgood : pathEdgesNat (v' 0) (Fin.tail v') t =
      edgeNat i'.val (v' 0).val := by
    rw [← tailg, ← firstg]
    exact get
  -- `z'` has exactly one non-head occurrence of this edge.
  have un := leading_first_edge_unique i' v' z'
  rcases un with ⟨q,hq,hu⟩
  exact (hu t tgood).trans (hu s hs).symm
end
end WignerSupport

namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
/-- The forward half of the recursion takes place in the *unlabelled*
finite set as well.  It is often useful to use this before replacing the
alphabet by its canonical word. -/
lemma wordPattern_graft_mem {n m k : ℕ}
    (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
    (hc : IsLeadingWord m n c) (hr : IsLeadingWord k n r)
    (hd : Disjoint (Set.range c) (Set.range r)) :
    wordPattern (graftWord c r) ∈ leadPatterns (m+k+2) := by
  apply wordPattern_mem_of_leading
  exact graftWord_isLeading c r hc hr hd
end
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/SplitGraftProof.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PatternRec.lean
section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A distinguished representative of an unlabelled equality pattern of
leading words.  This is chosen in the universal alphabet `Fin (p+1)`;
its particular choice will never be used. -/
noncomputable def patternRep {p : ℕ}
    (P : {P // P ∈ leadPatterns p}) : Fin (p+1) → Fin (p+1) :=
  Classical.choose (Finset.mem_image.1 P.property)

lemma patternRep_leading {p : ℕ} (P : {P // P ∈ leadPatterns p}) :
    IsLeadingWord p (p+1) (patternRep P) := by
  classical
  exact (Finset.mem_filter.1
    (Classical.choose_spec (Finset.mem_image.1 P.property)).1).2

lemma patternRep_pattern {p : ℕ} (P : {P // P ∈ leadPatterns p}) :
    wordPattern (patternRep P) = P.val := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.1 P.property)).2

-- separated canonical copies of two alphabets
private def __PatternRec_embChild (m k : ℕ) : Fin (m+1) → Fin (m+k+2) :=
  fun j => ⟨j.val, by omega⟩
private def __PatternRec_embRoot (m k : ℕ) : Fin (k+1) → Fin (m+k+2) :=
  fun j => ⟨m+1+j.val, by omega⟩

@[simp] lemma embChild_val {m k : ℕ} (j : Fin (m+1)) :
    (__PatternRec_embChild m k j).val = j.val := rfl
@[simp] lemma embRoot_val {m k : ℕ} (j : Fin (k+1)) :
    (__PatternRec_embRoot m k j).val = m+1+j.val := rfl

lemma embChild_inj {m k : ℕ} : Function.Injective (__PatternRec_embChild m k) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change a.val = b.val at hh
  exact hh
lemma embRoot_inj {m k : ℕ} : Function.Injective (__PatternRec_embRoot m k) := by
  intro a b h; apply Fin.ext; have hh := congrArg Fin.val h; dsimp [__PatternRec_embRoot] at hh; omega
lemma emb_ranges_disjoint {m k : ℕ}
  (c : Fin (m+1) → Fin (m+1)) (r : Fin (k+1) → Fin (k+1)) :
  Disjoint (Set.range (fun j => __PatternRec_embChild m k (c j)))
    (Set.range (fun j => __PatternRec_embRoot m k (r j))) := by
  apply Set.disjoint_left.2
  intro x hx hy
  rcases hx with ⟨u, rfl⟩
  rcases hy with ⟨w, h⟩
  have hv := congrArg Fin.val h
  dsimp [__PatternRec_embChild, __PatternRec_embRoot] at hv
  have lu := (c u).isLt
  omega

private noncomputable def __PatternRec_childCopy {m k : ℕ}
    (P : {P // P ∈ leadPatterns m}) : Fin (m+1) → Fin (m+k+2) :=
  fun j => __PatternRec_embChild m k (patternRep P j)
private noncomputable def __PatternRec_rootCopy {m k : ℕ}
    (P : {P // P ∈ leadPatterns k}) : Fin (k+1) → Fin (m+k+2) :=
  fun j => __PatternRec_embRoot m k (patternRep P j)

lemma childCopy_pattern {m k : ℕ} (P : {P // P ∈ leadPatterns m}) :
    wordPattern (__PatternRec_childCopy (k:=k) P) = P.val := by
  -- same pattern as its representative, since the embedding is injective
  have ee : wordPattern (__PatternRec_childCopy (k:=k) P) = wordPattern (patternRep P) := by
    apply (wordPattern_eq_iff _ _).2
    intro a b
    dsimp [__PatternRec_childCopy]
    exact ⟨fun h => embChild_inj h,
      fun h => congrArg (__PatternRec_embChild m k) h⟩
  exact ee.trans (patternRep_pattern P)
lemma rootCopy_pattern {m k : ℕ} (P : {P // P ∈ leadPatterns k}) :
    wordPattern (__PatternRec_rootCopy (m:=m) P) = P.val := by
  have ee : wordPattern (__PatternRec_rootCopy (m:=m) P) = wordPattern (patternRep P) := by
    apply (wordPattern_eq_iff _ _).2
    intro a b
    dsimp [__PatternRec_rootCopy]
    exact ⟨fun h => embRoot_inj h,
      fun h => congrArg (__PatternRec_embRoot m k) h⟩
  exact ee.trans (patternRep_pattern P)

lemma childCopy_leading {m k : ℕ} (P : {P // P ∈ leadPatterns m}) :
    IsLeadingWord m (m+k+2) (__PatternRec_childCopy (k:=k) P) := by
  exact (isLeadingWord_congr_pattern _ _
    ((wordPattern_eq_iff _ _).1 ((childCopy_pattern (k:=k) P).trans
        (patternRep_pattern P).symm))).2
      (patternRep_leading P)
lemma rootCopy_leading {m k : ℕ} (P : {P // P ∈ leadPatterns k}) :
    IsLeadingWord k (m+k+2) (__PatternRec_rootCopy (m:=m) P) := by
  exact (isLeadingWord_congr_pattern _ _
    ((wordPattern_eq_iff _ _).1 ((rootCopy_pattern (m:=m) P).trans
        (patternRep_pattern P).symm))).2
      (patternRep_leading P)
lemma copies_disjoint {m k : ℕ}
    (P : {P // P ∈ leadPatterns m}) (Q : {P // P ∈ leadPatterns k}) :
    Disjoint (Set.range (__PatternRec_childCopy (k:=k) P))
      (Set.range (__PatternRec_rootCopy (m:=m) Q)) := by
  exact emb_ranges_disjoint (patternRep P) (patternRep Q)

/-- Graft two patterns using the separated canonical representatives. -/
noncomputable def joinPattern {m k : ℕ}
    (P : {P // P ∈ leadPatterns m}) (Q : {P // P ∈ leadPatterns k}) :
      {P // P ∈ leadPatterns (m+k+2)} :=
  ⟨wordPattern (graftWord (__PatternRec_childCopy (k:=k) P) (__PatternRec_rootCopy (m:=m) Q)),
    wordPattern_mem_of_leading _
      (graftWord_isLeading (__PatternRec_childCopy (k:=k) P) (__PatternRec_rootCopy (m:=m) Q)
        (childCopy_leading P) (rootCopy_leading Q) (copies_disjoint P Q))⟩

lemma joinPattern_val {m k : ℕ}
    (P : {P // P ∈ leadPatterns m}) (Q : {P // P ∈ leadPatterns k}) :
    (joinPattern P Q).val =
      wordPattern (graftWord (__PatternRec_childCopy (k:=k) P) (__PatternRec_rootCopy (m:=m) Q)) := rfl

/-- Equality of whole grafted patterns determines the child and root
patterns.  We state this also with different label alphabets; restriction to
the visible blocks of positions is all that is used. -/
lemma graft_pattern_cancel {n d m k : ℕ}
    (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
    (c' : Fin (m+1) → Fin d) (r' : Fin (k+1) → Fin d)
    (h : wordPattern (graftWord c r) = wordPattern (graftWord c' r')) :
    wordPattern c = wordPattern c' ∧ wordPattern r = wordPattern r' := by
  classical
  have hh := (wordPattern_eq_iff (graftWord c r) (graftWord c' r')).1 h
  constructor
  · apply (wordPattern_eq_iff c c').2
    intro i j
    have e := hh (⟨i.val+1, by omega⟩ : Fin (m+k+3))
                  (⟨j.val+1, by omega⟩ : Fin (m+k+3))
    simpa [graftWord_child'] using e
  · apply (wordPattern_eq_iff r r').2
    intro i j
    have e := hh (⟨m+2+i.val, by omega⟩ : Fin (m+k+3))
                  (⟨m+2+j.val, by omega⟩ : Fin (m+k+3))
    simpa [graftWord_roottail'] using e

lemma joinPattern_injective {m k : ℕ} :
    Function.Injective (fun z :
      ({P // P ∈ leadPatterns m}) × ({P // P ∈ leadPatterns k}) =>
        joinPattern z.1 z.2) := by
  intro x y h
  rcases x with ⟨P,Q⟩
  rcases y with ⟨P',Q'⟩
  change joinPattern P Q = joinPattern P' Q' at h
  have hv : wordPattern (graftWord (__PatternRec_childCopy (k:=k) P) (__PatternRec_rootCopy (m:=m) Q)) =
        wordPattern (graftWord (__PatternRec_childCopy (k:=k) P') (__PatternRec_rootCopy (m:=m) Q')) :=
    congrArg Subtype.val h
  have both := graft_pattern_cancel _ _ _ _ hv
  have hp : (P : Fin (m+1) → Fin (m+1) → Bool) = P' := by
    simpa [childCopy_pattern (k:=k) P, childCopy_pattern (k:=k) P']
      using both.1
  have hq : (Q : Fin (k+1) → Fin (k+1) → Bool) = Q' := by
    simpa [rootCopy_pattern (m:=m) Q, rootCopy_pattern (m:=m) Q']
      using both.2
  cases P with
  | mk P hp0 =>
    cases P' with
    | mk P' hp' =>
      dsimp at hp
      cases hp
      cases Q with
      | mk Q hq0 =>
        cases Q' with
        | mk Q' hq' =>
          dsimp at hq
          cases hq
          rfl


/-- Grafting does not depend on the chosen separated copies.  This is the
surjectivity direction at a *fixed* first-return index. -/
lemma joinPattern_of_words {n m k : ℕ}
    (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
    (hc : IsLeadingWord m n c) (hr : IsLeadingWord k n r)
    (sep : Disjoint (Set.range c) (Set.range r)) :
    (joinPattern
      (⟨wordPattern c, wordPattern_mem_of_leading c hc⟩ :
        {P // P ∈ leadPatterns m})
      (⟨wordPattern r, wordPattern_mem_of_leading r hr⟩ :
        {P // P ∈ leadPatterns k})).val
        = wordPattern (graftWord c r) := by
  classical
  let P : {P // P ∈ leadPatterns m} :=
      ⟨wordPattern c, wordPattern_mem_of_leading c hc⟩
  let Q : {P // P ∈ leadPatterns k} :=
      ⟨wordPattern r, wordPattern_mem_of_leading r hr⟩
  change wordPattern
      (graftWord (__PatternRec_childCopy (k:=k) P) (__PatternRec_rootCopy (m:=m) Q)) =
        wordPattern (graftWord c r)
  apply wordPattern_graft_of_disjoint
  · exact (childCopy_pattern (k:=k) P)
  · exact (rootCopy_pattern (m:=m) Q)
  · exact copies_disjoint P Q
  · exact sep

/-- For a graft its non-head occurrence of the bridge occurs after the
whole child word.  Its index in the tail is `m`. -/
lemma graft_return_index {n m k : ℕ}
    (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
    (hc : IsLeadingWord m n c) :
    let w : Fin (m+k+3) → Fin n := graftWord c r
    pathEdgesNat ((Fin.tail w) 0) (Fin.tail (Fin.tail w))
      (⟨m, by omega⟩ : Fin (m+k+1)) =
        edgeNat (w 0).val ((Fin.tail w) 0).val := by
  classical
  dsimp
  let w : Fin (m+k+3) → Fin n := graftWord c r
  have e1 := pathEdges_word (w:= (Fin.tail w))
      (⟨m, by omega⟩ : Fin (m+k+1))
  -- the edge just after the last child letter
  have cm : w (⟨m+1, by omega⟩ : Fin (m+k+3)) =
        c (Fin.last m) := by
    simpa [w] using (graftWord_child' c r (Fin.last m))
  have rr : w (⟨m+2, by omega⟩ : Fin (m+k+3)) = r 0 := by
    simpa [w] using (graftWord_roottail' c r (0 : Fin (k+1)))
  have c0 : w (⟨1, by omega⟩ : Fin (m+k+3)) = c 0 := by
    simpa [w] using (graftWord_child' c r (0 : Fin (m+1)))
  have z0 : w 0 = r 0 := by simpa [w] using (graftWord_zero' c r)
  rw [e1]
  -- tail positions are word positions one later
  change edgeNat
      (w (⟨m+1, by omega⟩ : Fin (m+k+3))).val
      (w (⟨m+2, by omega⟩ : Fin (m+k+3))).val =
        edgeNat (w 0).val (w 1).val
  rw [cm, rr]
  have wone : w (1 : Fin (m+k+3)) = c 0 := by
    simpa using c0
  rw [wone, z0]

  have en := pathEnd_eq_cons_last (c 0) (Fin.tail c)
  have cl := hc.1
  change pathEnd m (c 0) (Fin.tail c) = c 0 at cl
  rw [en] at cl
  rw [cons_tail_zero_eq c] at cl
  rw [cl]
  exact edgeNat_comm _ _


/-- The length arithmetic for a first-return cut. -/
lemma split_len (a : ℕ) (t : Fin a) :
    t.val + (a - (t.val+1)) + 2 = a+1 := by omega

/-- Candidate pattern in total length `a+1` associated to a split index
`t` and a pair of smaller patterns.  The only transport is the displayed
length equality. -/
noncomputable def splitJoin (a : ℕ) (t : Fin a)
    (P : {P // P ∈ leadPatterns t.val})
    (Q : {P // P ∈ leadPatterns (a-(t.val+1))}) :
    {P // P ∈ leadPatterns (a+1)} :=
  (Eq.mp (congrArg (fun p : ℕ => {P // P ∈ leadPatterns p})
      (split_len a t)) (joinPattern P Q))


-- Casting a whole word only changes its length index.
def castWord {p q : ℕ} {α : Type*} (h : p = q) (w : Fin p → α) : Fin q → α :=
  fun u => w (Fin.cast h.symm u)
@[simp] lemma castWord_rfl {p : ℕ} {α : Type*} (w : Fin p → α) :
    castWord rfl w = w := by rfl
lemma castWord_apply_val {p q : ℕ} {α : Type*} (h : p = q)
    (w : Fin p → α) (i : ℕ) (hi : i < q) :
    castWord h w ⟨i,hi⟩ = w ⟨i, by simpa [h] using hi⟩ := by
  subst q; rfl

lemma castWord_leading {p q n : ℕ} (h : p = q)
    (w : Fin (p+1) → Fin n) (hw : IsLeadingWord p n w) :
    IsLeadingWord q n (castWord (congrArg (fun z => z+1) h) w) := by
  subst q
  simpa using hw

/-- For a prescribed return time no quotient by relabellings remains: the
number of grafted patterns is the product of the two smaller numbers. -/
lemma card_image_joinPattern (m k : ℕ) :
    ((Finset.univ : Finset
      (({P // P ∈ leadPatterns m}) × ({P // P ∈ leadPatterns k}))).image
        (fun z => joinPattern z.1 z.2)).card =
      (leadPatterns m).card * (leadPatterns k).card := by
  classical
  rw [Finset.card_image_of_injective _ joinPattern_injective]
  simp

end
end WignerSupport

namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
lemma graft_pattern_length_unique {n d m k m' k' : ℕ}
    (H : m+k+2 = m'+k'+2)
    (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
    (c' : Fin (m'+1) → Fin d) (r' : Fin (k'+1) → Fin d)
    (hc : IsLeadingWord m n c) (hr : IsLeadingWord k n r)
    (hc' : IsLeadingWord m' d c') (hr' : IsLeadingWord k' d r')
    (sep : Disjoint (Set.range c) (Set.range r))
    (sep' : Disjoint (Set.range c') (Set.range r'))
    (pat : wordPattern (graftWord c r) =
      wordPattern (castWord (by omega : m'+k'+3 = m+k+3)
        (graftWord c' r'))) : m = m' := by
  classical
  let w : Fin (m+k+3) → Fin n := graftWord c r
  let w' : Fin (m+k+3) → Fin d :=
      castWord (by omega : m'+k'+3 = m+k+3) (graftWord c' r')
  let v : Fin (m+k+2) → Fin n := Fin.tail w
  let v' : Fin (m+k+2) → Fin d := Fin.tail w'
  have zall : IsLeadingWord (m+k+2) n w :=
    graftWord_isLeading c r hc hr sep
  have z : IsLeadingPath (w 0) v := by
    change IsLeadingPath (w 0) (Fin.tail w)
    exact zall
  have z'all : IsLeadingWord (m+k+2) d w' := by
    let hh : m'+k'+2 = m+k+2 := by omega
    have zz := castWord_leading hh (graftWord c' r')
        (graftWord_isLeading c' r' hc' hr' sep')
    -- the two equality proofs used for the cast are irrelevant
    simpa [w'] using zz
  have z' : IsLeadingPath (w' 0) v' := by
    change IsLeadingPath (w' 0) (Fin.tail w')
    exact z'all
  let t : Fin (m+k+1) := ⟨m, by omega⟩
  let u : Fin (m+k+1) := ⟨m', by omega⟩
  have ht : pathEdgesNat (v 0) (Fin.tail v) t =
      edgeNat (w 0).val (v 0).val := by
    simpa [w, v, t] using (graft_return_index c r hc)
  have hs : pathEdgesNat (v' 0) (Fin.tail v') u =
      edgeNat (w' 0).val (v' 0).val := by
    -- compute consecutive positions of the cast word
    rw [pathEdges_word v' u]
    change edgeNat (w' (⟨m'+1, by omega⟩ : Fin (m+k+3))).val
        (w' (⟨m'+2, by omega⟩ : Fin (m+k+3))).val =
      edgeNat (w' 0).val (w' 1).val
    have aa : w' (⟨m'+1, by omega⟩ : Fin (m+k+3)) =
        c' (Fin.last m') := by
      dsimp [w']
      rw [castWord_apply_val]
      simpa using (graftWord_child' c' r' (Fin.last m'))
    have bb : w' (⟨m'+2, by omega⟩ : Fin (m+k+3)) = r' 0 := by
      dsimp [w']
      rw [castWord_apply_val]
      simpa using (graftWord_roottail' c' r' (0 : Fin (k'+1)))
    have cc : w' (0 : Fin (m+k+3)) = r' 0 := by
      dsimp [w']
      rw [castWord_apply_val]
      simpa using (graftWord_zero' c' r')
    have dd : w' (1 : Fin (m+k+3)) = c' 0 := by
      dsimp [w']
      rw [castWord_apply_val]
      simpa using (graftWord_child' c' r' (0 : Fin (m'+1)))
    rw [aa, bb, cc, dd]
    have cl := hc'.1
    change pathEnd m' (c' 0) (Fin.tail c') = c' 0 at cl
    rw [pathEnd_eq_cons_last, cons_tail_zero_eq c'] at cl
    rw [cl]
    exact edgeNat_comm _ _
  have same : t = u := by
    have pp : wordPattern (Fin.cons (w 0) v) =
          wordPattern (Fin.cons (w' 0) v') := by
      simpa [w, w', v, v', cons_tail_zero_eq] using pat
    exact leading_return_index_eq_of_pattern (w 0) v (w' 0) v'
      z z' pp t u ht hs
  have sv := congrArg Fin.val same
  change m = m' at sv
  exact sv
end
end WignerSupport
namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
lemma cast_pattern_val {p q n : ℕ} (h : p = q)
    (w : Fin (p+1) → Fin n) (hw : wordPattern w ∈ leadPatterns p) :
    (Eq.mp (congrArg (fun z : ℕ => {P // P ∈ leadPatterns z}) h)
      (⟨wordPattern w, hw⟩ : {P // P ∈ leadPatterns p})).val =
       wordPattern (castWord (congrArg (fun z => z+1) h) w) := by
  subst q
  rfl

lemma splitJoin_val (a : ℕ) (t : Fin a)
    (P : {P // P ∈ leadPatterns t.val})
    (Q : {P // P ∈ leadPatterns (a-(t.val+1))}) :
    (splitJoin a t P Q).val =
      wordPattern (castWord
        (congrArg (fun z => z+1) (split_len a t))
        (graftWord (__PatternRec_childCopy (k:=a-(t.val+1)) P)
                    (__PatternRec_rootCopy (m:=t.val) Q))) := by
  unfold splitJoin joinPattern
  simpa using (cast_pattern_val (split_len a t)
    (graftWord (__PatternRec_childCopy (k:=a-(t.val+1)) P)
      (__PatternRec_rootCopy (m:=t.val) Q)) (joinPattern P Q).property)
end
end WignerSupport
namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
lemma wordPattern_cast_cancel2 {p q u n d : ℕ}
    (hp : p = u) (hq : q = u)
    (f : Fin p → Fin n) (g : Fin q → Fin d)
    (h : wordPattern (castWord hp f) = wordPattern (castWord hq g)) :
    wordPattern f = wordPattern (castWord (hq.trans hp.symm) g) := by
  subst u
  subst q
  simpa using h

/-- Codes for the first-return decomposition of a nonempty leading pattern. -/
def SplitCode (a : ℕ) :=
  (t : Fin a) ×'
    (({P // P ∈ leadPatterns t.val}) ×
     ({P // P ∈ leadPatterns (a-(t.val+1))}))
-- explicit interpretation avoids any quotient on alphabets
noncomputable def codePattern {a : ℕ} (z : SplitCode a) :
    {P // P ∈ leadPatterns (a+1)} :=
  splitJoin a z.1 z.2.1 z.2.2

lemma codePattern_injective (a : ℕ) :
    Function.Injective (@codePattern a) := by
  classical
  intro x y hxy
  rcases x with ⟨t, P, Q⟩
  rcases y with ⟨s, P', Q'⟩
  change splitJoin a t P Q = splitJoin a s P' Q' at hxy
  have eqcast :
      wordPattern (castWord
        (congrArg (fun z => z+1) (split_len a t))
        (graftWord (__PatternRec_childCopy (k:=a-(t.val+1)) P)
          (__PatternRec_rootCopy (m:=t.val) Q))) =
      wordPattern (castWord
        (congrArg (fun z => z+1) (split_len a s))
        (graftWord (__PatternRec_childCopy (k:=a-(s.val+1)) P')
          (__PatternRec_rootCopy (m:=s.val) Q'))) := by
    simpa [splitJoin_val] using congrArg Subtype.val hxy
  have eqpat : wordPattern
        (graftWord (__PatternRec_childCopy (k:=a-(t.val+1)) P)
          (__PatternRec_rootCopy (m:=t.val) Q)) =
      wordPattern (castWord
        ((congrArg (fun z => z+1) (split_len a s)).trans
         (congrArg (fun z => z+1) (split_len a t)).symm)
        (graftWord (__PatternRec_childCopy (k:=a-(s.val+1)) P')
          (__PatternRec_rootCopy (m:=s.val) Q'))) := by
    exact wordPattern_cast_cancel2 _ _ _ _ eqcast
  have idx : t.val = s.val := by
    exact graft_pattern_length_unique
      (m:=t.val) (k:=a-(t.val+1))
      (m':=s.val) (k':=a-(s.val+1))
      (split_len a t |>.trans (split_len a s).symm)
      (__PatternRec_childCopy (k:=a-(t.val+1)) P) (__PatternRec_rootCopy (m:=t.val) Q)
      (__PatternRec_childCopy (k:=a-(s.val+1)) P') (__PatternRec_rootCopy (m:=s.val) Q')
      (childCopy_leading P) (rootCopy_leading Q)
      (childCopy_leading P') (rootCopy_leading Q')
      (copies_disjoint P Q) (copies_disjoint P' Q')
      (by
        -- proof irrelevance identifies the casts
        simpa using eqpat)
  have tt : t = s := Fin.ext idx
  subst s
  -- same cut; the injectivity at a fixed length was already proved
  have xy : (P,Q) = (P',Q') := by
    apply joinPattern_injective
    -- remove the common transport from splitJoin equality
    have z := hxy
    unfold splitJoin at z
    -- `Eq.mp` along that transport is injective
    have inj : Function.Injective
        (fun w : {P // P ∈ leadPatterns (t.val + (a-(t.val+1)) + 2)} =>
          Eq.mp (congrArg (fun p : ℕ => {P // P ∈ leadPatterns p})
            (split_len a t)) w) := by
            intro u v e
            have := congrArg (fun q : {P // P ∈ leadPatterns (a+1)} =>
              Eq.mp (congrArg (fun p : ℕ => {P // P ∈ leadPatterns p})
                (split_len a t).symm) q) e
            simpa using this
    exact inj z
  cases xy
  rfl
end
end WignerSupport
namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
lemma splitJoin_of_words {a n : ℕ} (t : Fin a)
    (c : Fin (t.val+1) → Fin n)
    (r : Fin (a-(t.val+1)+1) → Fin n)
    (hc : IsLeadingWord t.val n c)
    (hr : IsLeadingWord (a-(t.val+1)) n r)
    (sep : Disjoint (Set.range c) (Set.range r)) :
    (splitJoin a t
      (⟨wordPattern c, wordPattern_mem_of_leading c hc⟩)
      (⟨wordPattern r, wordPattern_mem_of_leading r hr⟩)).val =
      wordPattern
        (castWord (congrArg (fun z => z+1) (split_len a t))
          (graftWord c r)) := by
  classical
  rw [splitJoin_val]
  -- congruence before the length cast
  have base := joinPattern_of_words c r hc hr sep
  -- simpler graft relation on separated copies provided by this identity
  apply (wordPattern_eq_iff _ _).2
  intro i j
  -- both sides are value equalities after casting; use graft relation
  have hrel := (wordPattern_eq_iff
    (graftWord (__PatternRec_childCopy (k:=a-(t.val+1))
       (⟨wordPattern c, wordPattern_mem_of_leading c hc⟩ :
         {P // P ∈ leadPatterns t.val}))
     (__PatternRec_rootCopy (m:=t.val)
       (⟨wordPattern r, wordPattern_mem_of_leading r hr⟩ :
         {P // P ∈ leadPatterns (a-(t.val+1))})))
    (graftWord c r)).1 base
  exact hrel _ _
end
end WignerSupport
namespace WignerSupport
noncomputable instance instFintypeSplitCode (a : ℕ) : Fintype (SplitCode a) := by
  classical
  unfold SplitCode
  infer_instance
lemma card_SplitCode (a : ℕ) :
    Fintype.card (SplitCode a) =
      ∑ t : Fin a, (leadPatterns t.val).card *
        (leadPatterns (a-(t.val+1))).card := by
  classical
  change @Fintype.card (SplitCode a) (instFintypeSplitCode a) = _
  let e : SplitCode a ≃
      ((t : Fin a) ×' (({P // P ∈ leadPatterns t.val}) ×
        ({P // P ∈ leadPatterns (a-(t.val+1))}))) := Equiv.refl _
  rw [Fintype.card_congr e]
  rw [Fintype.card_congr (Equiv.psigmaEquivSigma _)]
  simp [Fintype.card_sigma, Fintype.card_prod]

lemma sum_le_card_patterns (a : ℕ) :
    (∑ t : Fin a, (leadPatterns t.val).card *
      (leadPatterns (a-(t.val+1))).card) ≤
        (leadPatterns (a+1)).card := by
  classical
  have card := Fintype.card_le_of_injective (@codePattern a)
    (codePattern_injective a)
  rw [card_SplitCode] at card
  simpa using card
end WignerSupport
namespace WignerSupport
lemma range_castWord {p q : ℕ} {α : Type*} (h : p = q)
    (w : Fin p → α) : Set.range (castWord h w) = Set.range w := by
  subst q
  rfl
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PatternRec.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PatternSurj.lean
section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport
noncomputable section
attribute [local instance] Classical.propDecidable
lemma leading_split_pieces_leading {n a : ℕ} (i : Fin n)
    (v : Fin (a+1) → Fin n) (z : IsLeadingPath i v)
    (t : Fin a)
    (ht : pathEdgesNat (v 0) (Fin.tail v) t = edgeNat i.val (v 0).val) :
    let mid : List ℕ := (pathList (Fin.tail v)).take t.val
    let rest : List ℕ := (pathList (Fin.tail v)).drop (t.val+1)
    let zm : ClosedEqPiece n (v 0) mid :=
      (leading_split_closedEqPieces i v z t ht).1
    let zr : ClosedEqPiece n i rest :=
      (leading_split_closedEqPieces i v z t ht).2
    IsLeadingPath (v 0) (listPath mid zm.bound) ∧
      IsLeadingPath i (listPath rest zr.bound) := by
  classical
  dsimp
  let mid : List ℕ := (pathList (Fin.tail v)).take t.val
  let rest : List ℕ := (pathList (Fin.tail v)).drop (t.val+1)
  have pcs := leading_split_closedEqPieces i v z t ht
  change ClosedEqPiece n (v 0) mid ∧ ClosedEqPiece n i rest at pcs
  let zm : ClosedEqPiece n (v 0) mid := pcs.1
  let zr : ClosedEqPiece n i rest := pcs.2
  change IsLeadingPath (v 0) (listPath mid zm.bound) ∧
      IsLeadingPath i (listPath rest zr.bound)
  have eqp := leading_split_piece_eq i v z t ht
  change (walkVertices (v 0).val mid).card =
        (walkEdges (v 0).val mid).card + 1 ∧
      (walkVertices i.val rest).card =
        (walkEdges i.val rest).card + 1 at eqp
  have clm := leading_split_child_closed i v z t ht
  change walkLast (v 0).val mid = (v 0).val at clm
  have clr := leading_split_root_closed i v z t ht
  change walkLast i.val rest = i.val at clr
  have upp := leading_split_piece_fiber_le_two i v z t ht
  change
    (∀ e ∈ (Finset.univ.image
          (pathEdgesNat (v 0) (listPath mid zm.bound))),
        ((Finset.univ : Finset (Fin mid.length)).filter
          (fun r => pathEdgesNat (v 0) (listPath mid zm.bound) r = e)).card ≤ 2) ∧
    (∀ e ∈ (Finset.univ.image
          (pathEdgesNat i (listPath rest zr.bound))),
        ((Finset.univ : Finset (Fin rest.length)).filter
          (fun r => pathEdgesNat i (listPath rest zr.bound) r = e)).card ≤ 2)
      at upp
  have seenm : ∀ k : ℕ, ∀ hk : k < mid.length,
      let b := mid[k]
      let aa := walkLast (v 0).val (mid.take k)
      edgeNat aa b ∈ walkEdges (v 0).val (mid.take k) ∨
        edgeNat aa b ∈ walkEdges b (mid.drop (k+1)) := by
      intro k hk
      exact closed_eq_step_seen_elsewhere (v 0).val mid eqp.1 clm k hk
  have seenr : ∀ k : ℕ, ∀ hk : k < rest.length,
      let b := rest[k]
      let aa := walkLast i.val (rest.take k)
      edgeNat aa b ∈ walkEdges i.val (rest.take k) ∨
        edgeNat aa b ∈ walkEdges b (rest.drop (k+1)) := by
      intro k hk
      exact closed_eq_step_seen_elsewhere i.val rest eqp.2 clr k hk
  have repm : ∀ u : Fin mid.length, ∃ r : Fin mid.length, r ≠ u ∧
          pathEdgesNat (v 0) (listPath mid zm.bound) r =
            pathEdgesNat (v 0) (listPath mid zm.bound) u :=
      repeated_edges_listPath_of_seen (v 0) mid zm.bound seenm
  have repr : ∀ u : Fin rest.length, ∃ r : Fin rest.length, r ≠ u ∧
          pathEdgesNat i (listPath rest zr.bound) r =
            pathEdgesNat i (listPath rest zr.bound) u :=
      repeated_edges_listPath_of_seen i rest zr.bound seenr
  exact ⟨ClosedEqPiece.isLeading_of_rep_of_fiber_le_two zm repm upp.1,
    ClosedEqPiece.isLeading_of_rep_of_fiber_le_two zr repr upp.2⟩

lemma cast_graft_cast_components {α : Type*} {m k m' k' p : ℕ}
    (hm : m = m') (hk : k = k')
    (h0 : m+k+3 = p) (h1 : m'+k'+3 = p)
    (c : Fin (m+1) → α) (r : Fin (k+1) → α) :
    castWord h1
        (graftWord
          (castWord (congrArg (fun z : ℕ => z+1) hm) c)
          (castWord (congrArg (fun z : ℕ => z+1) hk) r)) =
      castWord h0 (graftWord c r) := by
  subst m'
  subst k'
  rfl

lemma codePattern_surjective (a : ℕ) :
    Function.Surjective (@codePattern a) := by
  classical
  intro P
  let w : Fin (a+2) → Fin (a+2) := patternRep P
  have hw : IsLeadingWord (a+1) (a+2) w := patternRep_leading P
  let i : Fin (a+2) := w 0
  let v : Fin (a+1) → Fin (a+2) := Fin.tail w
  have z : IsLeadingPath i v := by
    simpa [i, v, IsLeadingWord] using hw
  obtain ⟨t, ht, _hunt⟩ := leading_first_edge_unique i v z
  let mid : List ℕ := (pathList (Fin.tail v)).take t.val
  let rest : List ℕ := (pathList (Fin.tail v)).drop (t.val+1)
  have pcs := leading_split_closedEqPieces i v z t ht
  change ClosedEqPiece (a+2) (v 0) mid ∧ ClosedEqPiece (a+2) i rest at pcs
  let zm : ClosedEqPiece (a+2) (v 0) mid := pcs.1
  let zr : ClosedEqPiece (a+2) i rest := pcs.2
  let c0 : Fin (mid.length+1) → Fin (a+2) :=
    @Fin.cons mid.length (fun _ => Fin (a+2)) (v 0)
      (listPath mid zm.bound)
  let r0 : Fin (rest.length+1) → Fin (a+2) :=
    @Fin.cons rest.length (fun _ => Fin (a+2)) i
      (listPath rest zr.bound)
  have hm : mid.length = t.val := by
    dsimp [mid]
    apply List.length_take_of_le
    simp [pathList]
  have hk : rest.length = a-(t.val+1) := by
    dsimp [rest]
    simp [pathList]
  let c : Fin (t.val+1) → Fin (a+2) :=
    castWord (congrArg (fun z : ℕ => z+1) hm) c0
  let r : Fin (a-(t.val+1)+1) → Fin (a+2) :=
    castWord (congrArg (fun z : ℕ => z+1) hk) r0
  have lp := leading_split_pieces_leading i v z t ht
  change IsLeadingPath (v 0) (listPath mid zm.bound) ∧
      IsLeadingPath i (listPath rest zr.bound) at lp
  have lc0 : IsLeadingWord mid.length (a+2) c0 := by
    unfold IsLeadingWord
    simpa [c0] using lp.1
  have lr0 : IsLeadingWord rest.length (a+2) r0 := by
    unfold IsLeadingWord
    simpa [r0] using lp.2
  have lc : IsLeadingWord t.val (a+2) c := by
    simpa [c] using (castWord_leading hm c0 lc0)
  have lr : IsLeadingWord (a-(t.val+1)) (a+2) r := by
    simpa [r] using (castWord_leading hk r0 lr0)
  have sep0 : Disjoint (Set.range c0) (Set.range r0) := by
    have h := leading_split_ranges_disjoint i v z t ht
    change Disjoint (Set.range (@Fin.cons mid.length (fun _ => Fin (a+2))
        (v 0) (listPath mid zm.bound)))
      (Set.range (@Fin.cons rest.length (fun _ => Fin (a+2))
        i (listPath rest zr.bound))) at h
    simpa [c0, r0] using h
  have sep : Disjoint (Set.range c) (Set.range r) := by
    dsimp [c, r]
    rw [range_castWord, range_castWord]
    exact sep0
  let C : {P // P ∈ leadPatterns t.val} :=
    ⟨wordPattern c, wordPattern_mem_of_leading c lc⟩
  let D : {P // P ∈ leadPatterns (a-(t.val+1))} :=
    ⟨wordPattern r, wordPattern_mem_of_leading r lr⟩
  refine ⟨⟨t, (C, D)⟩, ?_⟩
  apply Subtype.ext
  have valcode :
      (splitJoin a t C D).val =
        wordPattern (castWord
          (congrArg (fun z : ℕ => z+1) (split_len a t))
          (graftWord c r)) := by
    dsimp [C, D]
    simpa using (splitJoin_of_words (a:=a) t c r lc lr sep)
  change (splitJoin a t C D).val = P.val
  rw [valcode]
  let h0 : mid.length + rest.length + 3 = a+2 := by
    omega
  let h1 : t.val + (a-(t.val+1)) + 3 = a+2 := by
    have ss := split_len a t
    omega
  have word0 : (Fin.cons i v) = castWord h0 (graftWord c0 r0) := by
    have hh := leading_split_word_eq_graft i v z t ht
    change (Fin.cons i v) =
      (fun u : Fin (a+2) =>
        graftWord
          (@Fin.cons mid.length (fun _ => Fin (a+2)) (v 0)
            (listPath mid zm.bound))
          (@Fin.cons rest.length (fun _ => Fin (a+2)) i
            (listPath rest zr.bound))
          (Fin.cast h0.symm u)) at hh
    change (Fin.cons i v) =
        (fun u : Fin (a+2) =>
          graftWord c0 r0 (Fin.cast h0.symm u))
    exact hh
  have wordcast : castWord
          (congrArg (fun z : ℕ => z+1) (split_len a t))
          (graftWord c r) = castWord h0 (graftWord c0 r0) := by
    have comp := cast_graft_cast_components hm hk h0 h1 c0 r0
    simpa [c, r] using comp
  have wc : (Fin.cons i v) = w := by
    simpa [i, v] using (cons_tail_zero_eq w)
  have finalw : castWord
          (congrArg (fun z : ℕ => z+1) (split_len a t))
          (graftWord c r) = w := by
    rw [wordcast]
    exact word0.symm.trans wc
  rw [finalw]
  exact patternRep_pattern P

lemma card_patterns_succ (a : ℕ) :
    (leadPatterns (a+1)).card =
      ∑ t : Fin a, (leadPatterns t.val).card *
        (leadPatterns (a-(t.val+1))).card := by
  classical
  have eqc : Fintype.card (SplitCode a) =
      Fintype.card {P // P ∈ leadPatterns (a+1)} :=
    Fintype.card_congr
      (Equiv.ofBijective (@codePattern a)
        ⟨codePattern_injective a, codePattern_surjective a⟩)
  rw [card_SplitCode] at eqc
  simpa using eqc.symm
end
end WignerSupport

namespace WignerSupport
open scoped BigOperators
-- odd edge lengths have no maximal contour
lemma card_patterns_odd_zero (p : ℕ) (hp : ¬ 2 ∣ p) :
    (leadPatterns p).card = 0 := by
  classical
  rw [leadPatterns_eq_empty_of_odd p hp]
  simp

lemma card_patterns_even_catalan (m : ℕ) :
    (leadPatterns (2*m)).card = catalan m := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simpa using leadPatterns_zero_card
    | succ u =>
      have recu := card_patterns_succ (2*u+1)
      have recu' :
          (leadPatterns (2*(u+1))).card =
            ∑ t : Fin (2*u+1),
              (leadPatterns t.val).card *
                (leadPatterns ((2*u+1)-(t.val+1))).card := by
            have eqn : 2*(u+1) = (2*u+1)+1 := by omega
            rw [eqn]
            exact recu
      let f : Fin (2*u+1) → ℕ := fun t =>
          (leadPatterns t.val).card *
            (leadPatterns ((2*u+1)-(t.val+1))).card
      let g : Fin (u+1) → ℕ := fun j =>
          catalan j.val * catalan (u-j.val)
      have discard :
          (∑ t : Fin (2*u+1), f t) =
            ∑ t ∈ ((Finset.univ : Finset (Fin (2*u+1))).filter
              (fun t => 2 ∣ t.val)), f t := by
        classical
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro x hx hxnot
        have nd : ¬ 2 ∣ x.val := by
          simpa using hxnot
        have zc := card_patterns_odd_zero x.val nd
        simp [f, zc]
      have reindex :
          (∑ t ∈ ((Finset.univ : Finset (Fin (2*u+1))).filter
              (fun t => 2 ∣ t.val)), f t) =
            ∑ j : Fin (u+1), g j := by
        classical
        -- use the doubling bijection from `0,...,u` onto the even indices
        symm
        apply Finset.sum_bij
          (s := (Finset.univ : Finset (Fin (u+1))))
          (t := (Finset.univ : Finset (Fin (2*u+1))).filter
              (fun t => 2 ∣ t.val))
          (fun j _ => (⟨2*j.val, by omega⟩ : Fin (2*u+1)))
        · intro j hj
          simp
        · intro j hj k hk eq
          apply Fin.ext
          have e := congrArg Fin.val eq
          dsimp at e
          omega
        · intro t ht
          have ev : 2 ∣ t.val := (Finset.mem_filter.1 ht).2
          rcases ev with ⟨q, eq⟩
          have qlt : q < u+1 := by
            have tl := t.isLt
            omega
          refine ⟨(⟨q, qlt⟩ : Fin (u+1)), by simp, ?_⟩
          apply Fin.ext
          dsimp
          omega
        · intro j hj
          have jle : j.val ≤ u := Nat.le_of_lt_succ j.isLt
          have huj : u - j.val < u+1 := by omega
          have ind1 := ih j.val (by omega)
          have ind2 := ih (u-j.val) huj
          have restEq : (2*u+1)-(2*j.val+1) = 2*(u-j.val) := by omega
          change catalan j.val * catalan (u-j.val) = f ⟨2*j.val, _⟩
          change catalan j.val * catalan (u-j.val) =
            (leadPatterns (2*j.val)).card *
              (leadPatterns ((2*u+1)-(2*j.val+1))).card
          rw [restEq, ind1, ind2]
      calc
        (leadPatterns (2 * (u+1))).card =
            ∑ t : Fin (2*u+1), f t := by
              simpa [f] using recu'
        _ = ∑ j : Fin (u+1), g j := discard.trans reindex
        _ = catalan (u+1) := by
              simpa [g] using (catalan_succ u).symm

end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PatternSurj.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PairMean.lean
section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Monomials belonging to disjoint finite collections of upper-triangular
edges are independent.  Repetitions *inside* a monomial are harmless; it is
the images of the two edge lists which must be disjoint.  This is the
covariance-zero stratum in the bounded doubled-walk calculation. -/
lemma integral_mul_pathTerm_of_disjoint
    (μ : Measure Ω)
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
      (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (n n' p q : ℕ) (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n') (w : Fin q → Fin n')
    (hEF : Disjoint
      (Finset.univ.image (pathEdgesNat i v))
      (Finset.univ.image (pathEdgesNat j w))) :
    (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n' =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ) =
      (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
      (∫ a, pathTerm (fun b c : Fin n' =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ) := by
  classical
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
      Finset.univ.image (pathEdgesNat i v)
  let F : Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
      Finset.univ.image (pathEdgesNat j w)
  let M : {z : ℕ × ℕ // z.1 ≤ z.2} → ℕ := fun e =>
      ((Finset.univ : Finset (Fin p)).filter
        (fun x => pathEdgesNat i v x = e)).card
  let N : {z : ℕ × ℕ // z.1 ≤ z.2} → ℕ := fun e =>
      ((Finset.univ : Finset (Fin q)).filter
        (fun x => pathEdgesNat j w x = e)).card
  let U : Ω → ({e // e ∈ E} → ℝ) := fun a e =>
      Y e.val.val.1 e.val.val.2 a
  let V : Ω → ({e // e ∈ F} → ℝ) := fun a e =>
      Y e.val.val.1 e.val.val.2 a
  have base :
      (fun a (e : {e // e ∈ E}) =>
          Y e.val.val.1 e.val.val.2 a) ⟂ᵢ[μ]
      (fun a (e : {e // e ∈ F}) =>
          Y e.val.val.1 e.val.val.2 a) := by
    exact ProbabilityTheory.iIndepFun.indepFun_finset E F hEF hi
      (fun e => hm _ _)
  let φ : ({e // e ∈ E} → ℝ) → ℝ := fun x =>
      ∏ e : {e // e ∈ E}, x e ^ M e.val
  let ψ : ({e // e ∈ F} → ℝ) → ℝ := fun x =>
      ∏ e : {e // e ∈ F}, x e ^ N e.val
  have mφ : Measurable φ := by
    unfold φ
    fun_prop
  have mψ : Measurable ψ := by
    unfold ψ
    fun_prop
  have indep : (φ ∘ U) ⟂ᵢ[μ] (ψ ∘ V) :=
    IndepFun.comp base mφ mψ
  have mx : AEStronglyMeasurable (φ ∘ U) μ :=
    (mφ.comp (by unfold U; fun_prop)).aestronglyMeasurable
  have my : AEStronglyMeasurable (ψ ∘ V) μ :=
    (mψ.comp (by unfold V; fun_prop)).aestronglyMeasurable
  have fact := indep.integral_mul_eq_mul_integral mx my
  have one (a : Ω) : (φ ∘ U) a =
      pathTerm (fun b c : Fin n =>
         Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v := by
    rw [pathTerm_eq_prod_edges Y n p i v a]
    change (∏ e ∈ E.attach,
      (Y e.val.val.1 e.val.val.2 a) ^ M e.val) =
      ∏ e ∈ E, (Y e.val.1 e.val.2 a) ^ M e
    exact Finset.prod_attach E (fun z => (Y z.val.1 z.val.2 a) ^ M z)
  have two (a : Ω) : (ψ ∘ V) a =
      pathTerm (fun b c : Fin n' =>
         Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w := by
    rw [pathTerm_eq_prod_edges Y n' q j w a]
    change (∏ e ∈ F.attach,
      (Y e.val.val.1 e.val.val.2 a) ^ N e.val) =
      ∏ e ∈ F, (Y e.val.1 e.val.2 a) ^ N e
    exact Finset.prod_attach F (fun z => (Y z.val.1 z.val.2 a) ^ N z)
  -- substitute the deterministic regroupings at the very end
  have eq1 : (φ ∘ U) = (fun a =>
      pathTerm (fun b c : Fin n =>
         Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v) := funext one
  have eq2 : (ψ ∘ V) = (fun a =>
      pathTerm (fun b c : Fin n' =>
         Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w) := funext two
  rw [eq1, eq2] at fact
  simpa using fact
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PairMean.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PairVar.lean
section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace WignerSupport
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Factor the expectation of the product of two path monomials by the union
of their unordered edges.  The exponents add on the intersection.  This is
the doubled-word analogue of `integral_pathTerm_eq_prod_edges` and is useful
before doing any estimates: a singleton of the union kills the whole term. -/
lemma integral_mul_pathTerm_eq_prod_union
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
      (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (n n' p q : ℕ) (i : Fin n) (v : Fin p → Fin n)
      (j : Fin n') (w : Fin q → Fin n') :
    (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n' =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ) =
      ∏ e ∈ ((Finset.univ.image (pathEdgesNat i v)) ∪
              (Finset.univ.image (pathEdgesNat j w))),
        (∫ a, (Y e.val.1 e.val.2 a) ^
          (((Finset.univ : Finset (Fin p)).filter
             (fun r => pathEdgesNat i v r = e)).card +
           ((Finset.univ : Finset (Fin q)).filter
             (fun r => pathEdgesNat j w r = e)).card) ∂μ) := by
  classical
  let f := pathEdgesNat i v
  let g := pathEdgesNat j w
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
    (Finset.univ : Finset (Fin p)).image f
  let F : Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
    (Finset.univ : Finset (Fin q)).image g
  let S : Finset {z : ℕ × ℕ // z.1 ≤ z.2} := E ∪ F
  let M : {z : ℕ × ℕ // z.1 ≤ z.2} → ℕ := fun e =>
    ((Finset.univ : Finset (Fin p)).filter (fun r => f r = e)).card
  let N : {z : ℕ × ℕ // z.1 ≤ z.2} → ℕ := fun e =>
    ((Finset.univ : Finset (Fin q)).filter (fun r => g r = e)).card
  let Z : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ S} → Ω → ℝ :=
    fun e a => (Y e.val.val.1 e.val.val.2 a) ^ (M e.val + N e.val)
  have pre : iIndepFun
      (fun e : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ S} =>
         Y e.val.val.1 e.val.val.2) μ :=
    ProbabilityTheory.iIndepFun.precomp (fun e₁ e₂ h => Subtype.ext h) hi
  have hZ : iIndepFun Z μ := by
    exact ProbabilityTheory.iIndepFun.comp pre
      (fun e (x : ℝ) => x ^ (M e.val + N e.val)) (by intro e; fun_prop)
  have mZ : ∀ e, AEStronglyMeasurable (Z e) μ := by
    intro e
    exact (by fun_prop : Measurable (Z e)).aestronglyMeasurable
  have fact := ProbabilityTheory.iIndepFun.integral_fun_prod_eq_prod_integral
       hZ mZ
  -- Outside the image of a list of edges its multiplicity is zero.
  have mzero {e : {z : ℕ × ℕ // z.1 ≤ z.2}} (he : e ∉ E) : M e = 0 := by
    dsimp [M]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro r hr hEq
    apply he
    exact Finset.mem_image.mpr ⟨r, by simp, hEq⟩
  have nzero {e : {z : ℕ × ℕ // z.1 ≤ z.2}} (he : e ∉ F) : N e = 0 := by
    dsimp [N]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro r hr hEq
    apply he
    exact Finset.mem_image.mpr ⟨r, by simp, hEq⟩
  have point (a : Ω) :
      pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n' =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w =
        ∏ e : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ S}, Z e a := by
    rw [pathTerm_eq_prod_edges Y n p i v a,
        pathTerm_eq_prod_edges Y n' q j w a]
    change (∏ e ∈ E, (Y e.val.1 e.val.2 a) ^ M e) *
        (∏ e ∈ F, (Y e.val.1 e.val.2 a) ^ N e) =
      ∏ e ∈ S.attach,
        (Y e.val.val.1 e.val.val.2 a) ^ (M e.val + N e.val)
    rw [Finset.prod_attach S (fun e =>
      (Y e.val.1 e.val.2 a) ^ (M e + N e))]
    -- put both products on the union; the missing factors are powers `0`
    have eprod :
        (∏ e ∈ S, (Y e.val.1 e.val.2 a) ^ M e) =
          ∏ e ∈ E, (Y e.val.1 e.val.2 a) ^ M e := by
      symm
      apply Finset.prod_subset (by
        intro x hx
        exact Finset.mem_union_left F hx)
      intro e heS heE
      -- the extra factors are one
      rw [mzero heE]
      simp
    have fprod :
        (∏ e ∈ S, (Y e.val.1 e.val.2 a) ^ N e) =
          ∏ e ∈ F, (Y e.val.1 e.val.2 a) ^ N e := by
      symm
      apply Finset.prod_subset (by
        intro x hx
        exact Finset.mem_union_right E hx)
      intro e heS heF
      rw [nzero heF]
      simp
    -- distribute the product over the two exponents on S
    calc
      (∏ e ∈ E, (Y e.val.1 e.val.2 a) ^ M e) *
          (∏ e ∈ F, (Y e.val.1 e.val.2 a) ^ N e) =
        (∏ e ∈ S, (Y e.val.1 e.val.2 a) ^ M e) *
          (∏ e ∈ S, (Y e.val.1 e.val.2 a) ^ N e) := by rw [eprod, fprod]
      _ = ∏ e ∈ S,
            ((Y e.val.1 e.val.2 a) ^ M e *
             (Y e.val.1 e.val.2 a) ^ N e) := by
            rw [← Finset.prod_mul_distrib]
      _ = ∏ e ∈ S,
            (Y e.val.1 e.val.2 a) ^ (M e + N e) := by
            apply Finset.prod_congr rfl
            intro x hx
            rw [← pow_add]
  calc
    (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n' =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ) =
      ∫ a, ∏ e : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ S}, Z e a ∂μ := by
        congr 1
        funext a
        exact point a
    _ = ∏ e : {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ S},
          (∫ a, Z e a ∂μ) := fact
    _ = ∏ e ∈ ((Finset.univ.image (pathEdgesNat i v)) ∪
              (Finset.univ.image (pathEdgesNat j w))),
        (∫ a, (Y e.val.1 e.val.2 a) ^
          (((Finset.univ : Finset (Fin p)).filter
             (fun r => pathEdgesNat i v r = e)).card +
           ((Finset.univ : Finset (Fin q)).filter
             (fun r => pathEdgesNat j w r = e)).card) ∂μ) := by
        change
          (∏ e ∈ S.attach,
            (∫ a, (Y e.val.val.1 e.val.val.2 a) ^
                (M e.val + N e.val) ∂μ)) =
          ∏ e ∈ S,
            (∫ a, (Y e.val.1 e.val.2 a) ^ (M e + N e) ∂μ)
        exact Finset.prod_attach S
          (fun e => (∫ a, (Y e.val.1 e.val.2 a) ^ (M e + N e) ∂μ))

/-- A singleton edge of the *union* of two walks kills the mixed moment.
The edge may belong to either walk or to both; the assertion is about the
sum of the two fiber cardinalities. -/
lemma integral_mul_pathTerm_zero_of_unique_union
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
      (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (hz : ∀ a b, a ≤ b → (∫ ω, Y a b ω ∂μ) = (0:ℝ))
    (n n' p q : ℕ) (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n') (w : Fin q → Fin n')
    (e : {z : ℕ × ℕ // z.1 ≤ z.2})
    (he : e ∈ ((Finset.univ.image (pathEdgesNat i v)) ∪
              (Finset.univ.image (pathEdgesNat j w))))
    (hcard :
       ((Finset.univ : Finset (Fin p)).filter
          (fun r => pathEdgesNat i v r = e)).card +
       ((Finset.univ : Finset (Fin q)).filter
          (fun r => pathEdgesNat j w r = e)).card = 1) :
    (∫ a, pathTerm (fun b c : Fin n =>
           Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
         pathTerm (fun b c : Fin n' =>
           Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ) = 0 := by
  classical
  rw [integral_mul_pathTerm_eq_prod_union μ Y hm hi n n' p q i v j w]
  -- the selected factor is a first moment
  apply Finset.prod_eq_zero_iff.mpr
  refine ⟨e, he, ?_⟩
  rw [hcard]
  simpa using hz e.val.1 e.val.2 e.property

end WignerSupport


namespace WignerSupport
open scoped Sym2
open SimpleGraph

/-- Vertices and unordered edges of two paths in the same alphabet. -/
def pairVertices {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n) : Finset ℕ :=
  pathVerticesFin i v ∪ pathVerticesFin j w

def pairEdges {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n) :
    Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
  (Finset.univ.image (pathEdgesNat i v)) ∪
    (Finset.univ.image (pathEdgesNat j w))

abbrev PairVert {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n) :=
  {a : ℕ // a ∈ pairVertices i v j w}

def pairGraph {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n) :
    SimpleGraph (PairVert i v j w) :=
  SimpleGraph.fromRel (fun a b : PairVert i v j w =>
    edgeNat a.val b.val ∈ pairEdges i v j w)

lemma pairGraph_adj {n p q : ℕ} {i : Fin n} {v : Fin p → Fin n}
    {j : Fin n} {w : Fin q → Fin n}
    (a b : PairVert i v j w) :
    (pairGraph i v j w).Adj a b ↔
      a ≠ b ∧ edgeNat a.val b.val ∈ pairEdges i v j w := by
  change (a ≠ b ∧ (_ ∨ _)) ↔ _
  constructor
  · rintro ⟨h,h'|h'⟩
    · exact ⟨h,h'⟩
    · exact ⟨h, by simpa [edgeNat_comm] using h'⟩
  · rintro ⟨h,h'⟩
    exact ⟨h, Or.inl h'⟩

/-- Reachability supplied by a list piece inside the doubled graph.  Loops in
an arbitrary word may be skipped; no no-loop assumption is hidden here. -/
lemma pair_reachable_piece {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n)
    (cur : ℕ) (xs : List ℕ)
    (he : walkEdges cur xs ⊆ pairEdges i v j w)
    (hv : walkVertices cur xs ⊆ pairVertices i v j w)
    (a : ℕ) (ha : a ∈ walkVertices cur xs) :
    (pairGraph i v j w).Reachable
      (⟨cur, hv (walkVertices_root_mem _ _)⟩ : PairVert i v j w)
      (⟨a, hv ha⟩ : PairVert i v j w) := by
  classical
  induction xs generalizing cur with
  | nil =>
      have eq : a = cur := by simpa [walkVertices] using ha
      subst a
      exact SimpleGraph.Walk.reachable SimpleGraph.Walk.nil
  | cons b ys ih =>
      have allv : walkVertices cur (b::ys) =
          insert cur (walkVertices b ys) := walkVertices_cons _ _ _
      by_cases ac : a = cur
      · subst a
        exact SimpleGraph.Walk.reachable SimpleGraph.Walk.nil
      · have ab : a ∈ walkVertices b ys := by
          rw [allv] at ha
          simpa [ac] using ha
        have sube : walkEdges b ys ⊆ pairEdges i v j w := by
          intro z hz
          apply he
          exact (by simp [walkEdges, hz])
        have subv : walkVertices b ys ⊆ pairVertices i v j w := by
          intro z hz
          apply hv
          rw [allv]
          exact Finset.mem_insert_of_mem hz
        have tail := ih b sube subv ab
        by_cases cb : cur = b
        · -- crossing a loop contributes no step to a simple-graph walk
          have same :
              (⟨cur, hv (walkVertices_root_mem _ _)⟩ : PairVert i v j w) =
                ⟨b, subv (walkVertices_root_mem _ _)⟩ := by
            apply Subtype.ext
            exact cb
          rw [same]
          exact tail
        · have stepmem : edgeNat cur b ∈ pairEdges i v j w := by
            apply he
            simp [walkEdges]
          have ne :
              (⟨cur, hv (walkVertices_root_mem _ _)⟩ : PairVert i v j w) ≠
                ⟨b, subv (walkVertices_root_mem _ _)⟩ := by
            intro z
            exact cb (congrArg Subtype.val z)
          have adj : (pairGraph i v j w).Adj
              (⟨cur, hv (walkVertices_root_mem _ _)⟩ : PairVert i v j w)
              (⟨b, subv (walkVertices_root_mem _ _)⟩ : PairVert i v j w) :=
            (pairGraph_adj _ _).2 ⟨ne, stepmem⟩
          exact ⟨SimpleGraph.Walk.cons adj (Classical.choice tail)⟩

lemma pairGraph_connected_of_vertex
    {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (w : Fin q → Fin n)
    {x : ℕ} (hx₁ : x ∈ pathVerticesFin i v)
      (hx₂ : x ∈ pathVerticesFin j w) :
    (pairGraph i v j w).Connected := by
  classical
  have sub1 : walkVertices i.val (pathList v) ⊆ pairVertices i v j w := by
    intro y hy
    exact Finset.mem_union_left _ hy
  have sub2 : walkVertices j.val (pathList w) ⊆ pairVertices i v j w := by
    intro y hy
    exact Finset.mem_union_right _ hy
  have esub1 : walkEdges i.val (pathList v) ⊆ pairEdges i v j w := by
    intro z hz
    rw [← image_pathEdges_eq_walkEdges] at hz
    exact Finset.mem_union_left _ hz
  have esub2 : walkEdges j.val (pathList w) ⊆ pairEdges i v j w := by
    intro z hz
    rw [← image_pathEdges_eq_walkEdges] at hz
    exact Finset.mem_union_right _ hz
  have R1 (y : ℕ) (hy : y ∈ walkVertices i.val (pathList v)) :
      (pairGraph i v j w).Reachable
        (⟨i.val, sub1 (walkVertices_root_mem _ _)⟩ : PairVert i v j w)
        (⟨y, sub1 hy⟩ : PairVert i v j w) :=
    pair_reachable_piece i v j w i.val (pathList v) esub1 sub1 y hy
  have R2 (y : ℕ) (hy : y ∈ walkVertices j.val (pathList w)) :
      (pairGraph i v j w).Reachable
        (⟨j.val, sub2 (walkVertices_root_mem _ _)⟩ : PairVert i v j w)
        (⟨y, sub2 hy⟩ : PairVert i v j w) :=
    pair_reachable_piece i v j w j.val (pathList w) esub2 sub2 y hy
  have hxv1 : x ∈ walkVertices i.val (pathList v) := hx₁
  have hxv2 : x ∈ walkVertices j.val (pathList w) := hx₂
  have connectRoots :
      (pairGraph i v j w).Reachable
        (⟨i.val, sub1 (walkVertices_root_mem _ _)⟩ : PairVert i v j w)
        (⟨j.val, sub2 (walkVertices_root_mem _ _)⟩ : PairVert i v j w) := by
    have a := R1 x hxv1
    have b := R2 x hxv2
    have same :
        (⟨x, sub1 hxv1⟩ : PairVert i v j w) =
          (⟨x, sub2 hxv2⟩ : PairVert i v j w) := by rfl
    rw [same] at a
    exact a.trans b.symm
  have reach (z : PairVert i v j w) :
      (pairGraph i v j w).Reachable
        (⟨i.val, sub1 (walkVertices_root_mem _ _)⟩ : PairVert i v j w) z := by
    have mem := z.property
    change z.val ∈ pathVerticesFin i v ∪ pathVerticesFin j w at mem
    rcases Finset.mem_union.mp mem with h|h
    · have r := R1 z.val h
      simpa using r
    · have r := R2 z.val h
      have rr := connectRoots.trans r
      simpa using rr
  have pre : (pairGraph i v j w).Preconnected := by
    intro a b
    exact (reach a).symm.trans (reach b)
  letI : Nonempty (PairVert i v j w) :=
    ⟨⟨i.val, sub1 (walkVertices_root_mem _ _)⟩⟩
  exact ⟨pre⟩

lemma pairGraph_connected_of_edge
    {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (w : Fin q → Fin n)
    (hh : (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty) :
    (pairGraph i v j w).Connected := by
  classical
  rcases hh with ⟨e, he⟩
  have he1 : e ∈ Finset.univ.image (pathEdgesNat i v) := (Finset.mem_inter.mp he).1
  have he2 : e ∈ Finset.univ.image (pathEdgesNat j w) := (Finset.mem_inter.mp he).2
  have ep1 := walkEdges_endpoints i.val (pathList v) e
       (by simpa [image_pathEdges_eq_walkEdges] using he1)
  have ep2 := walkEdges_endpoints j.val (pathList w) e
       (by simpa [image_pathEdges_eq_walkEdges] using he2)
  exact pairGraph_connected_of_vertex i v j w ep1.1 ep2.1

-- The sorted endpoint map on `Sym2` remembers a unique natural unordered edge.
private def __PairVar_symNat {V : Type*} (val : V → ℕ)
    : Sym2 V → {z : ℕ × ℕ // z.1 ≤ z.2} :=
  Sym2.lift ⟨fun a b => edgeNat (val a) (val b), by
    intro a b
    exact edgeNat_comm _ _⟩

private lemma __PairVar_symNat_pair {V : Type*} (val : V → ℕ) (a b : V) :
    __PairVar_symNat val (s(a,b)) = edgeNat (val a) (val b) := rfl

-- Injectivity after remembering that vertices are subtypes of ℕ.
private lemma __PairVar_symNat_inj_sub {S : Finset ℕ} :
    Function.Injective (__PairVar_symNat (fun a : {a : ℕ // a ∈ S} => a.val)) := by
  classical
  intro z z' h
  induction z using Sym2.inductionOn with
  | _ a b =>
    induction z' using Sym2.inductionOn with
    | _ c d =>
      change edgeNat a.val b.val = edgeNat c.val d.val at h
      have hmin : min a.val b.val = min c.val d.val :=
        congrArg (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => e.val.1) h
      have hmax : max a.val b.val = max c.val d.val :=
        congrArg (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => e.val.2) h
      have mk {x y : {a : ℕ // a ∈ S}} {u v : {a : ℕ // a ∈ S}}
          (h1 : x.val = u.val) (h2 : y.val = v.val) : s(x,y) = s(u,v) := by
        apply Sym2.eq_iff.mpr
        left
        exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      by_cases ab : a.val ≤ b.val
      · by_cases cd : c.val ≤ d.val
        · have e1 : a.val = c.val := by
            simpa [edgeNat, min_eq_left ab, min_eq_left cd] using hmin
          have e2 : b.val = d.val := by
            simpa [edgeNat, max_eq_right ab, max_eq_right cd] using hmax
          exact mk e1 e2
        · have dc : d.val ≤ c.val := le_of_not_ge cd
          apply Sym2.eq_iff.mpr
          right
          have e1 : a.val = d.val := by
            simpa [edgeNat, min_eq_left ab, min_eq_right dc] using hmin
          have e2 : b.val = c.val := by
            simpa [edgeNat, max_eq_right ab, max_eq_left dc] using hmax
          exact ⟨Subtype.ext e1, Subtype.ext e2⟩
      · have ba : b.val ≤ a.val := le_of_not_ge ab
        by_cases cd : c.val ≤ d.val
        · apply Sym2.eq_iff.mpr
          right
          have e1 : a.val = d.val := by
            simpa [edgeNat, max_eq_left ba, max_eq_right cd] using hmax
          have e2 : b.val = c.val := by
            simpa [edgeNat, min_eq_right ba, min_eq_left cd] using hmin
          exact ⟨Subtype.ext e1, Subtype.ext e2⟩
        · have dc : d.val ≤ c.val := le_of_not_ge cd
          have e1 : a.val = c.val := by
            simpa [edgeNat, max_eq_left ba, max_eq_left dc] using hmax
          have e2 : b.val = d.val := by
            simpa [edgeNat, min_eq_right ba, min_eq_right dc] using hmin
          exact mk e1 e2

lemma card_pairGraph_edges_le {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n) :
    Nat.card (pairGraph i v j w).edgeSet ≤
      (pairEdges i v j w).card := by
  classical
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} := pairEdges i v j w
  let val : PairVert i v j w → ℕ := fun a => a.val
  have key : ∀ z0 : Sym2 (PairVert i v j w),
      z0 ∈ (pairGraph i v j w).edgeSet → __PairVar_symNat val z0 ∈ E := by
    intro z0
    induction z0 using Sym2.inductionOn with
    | _ a b =>
      intro hz
      have ad : (pairGraph i v j w).Adj a b :=
        (SimpleGraph.mem_edgeSet _).1 hz
      exact (pairGraph_adj _ _).1 ad |>.2
  have mem (z : (pairGraph i v j w).edgeSet) :
      __PairVar_symNat val z.val ∈ E := key z.val z.property
  let f : (pairGraph i v j w).edgeSet →
      {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ E} :=
    fun z => ⟨__PairVar_symNat val z.val, mem z⟩
  have inj : Function.Injective f := by
    intro a b hab
    have vals : __PairVar_symNat val a.val = __PairVar_symNat val b.val :=
      congrArg Subtype.val hab
    have sy : a.val = b.val := by
      exact (@__PairVar_symNat_inj_sub (pairVertices i v j w)) vals
    exact Subtype.ext sy
  letI : Fintype (PairVert i v j w) := Fintype.ofFinite _
  letI : Fintype (pairGraph i v j w).edgeSet := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective f inj
  rw [Nat.card_eq_fintype_card]
  simpa [E] using h

lemma card_pairVertices_le_edges_add_one_of_edge
    {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (w : Fin q → Fin n)
    (hh : (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty) :
    (pairVertices i v j w).card ≤ (pairEdges i v j w).card + 1 := by
  classical
  have conn := pairGraph_connected_of_edge i v j w hh
  have c := conn.card_vert_le_card_edgeSet_add_one
  have e := card_pairGraph_edges_le i v j w
  letI : Fintype (PairVert i v j w) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at c
  exact c.trans (Nat.add_le_add_right e 1)

end WignerSupport

namespace WignerSupport
/-- If no edge of the doubled list is a singleton, at most half as many
unordered edges as positions occur. -/
lemma card_pairEdges_le_half_of_union
    {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (w : Fin q → Fin n)
    (two : ∀ e ∈ pairEdges i v j w,
       2 ≤ ((Finset.univ : Finset (Fin p)).filter
             (fun r => pathEdgesNat i v r = e)).card +
           ((Finset.univ : Finset (Fin q)).filter
             (fun r => pathEdgesNat j w r = e)).card) :
    (pairEdges i v j w).card ≤ (p+q)/2 := by
  classical
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
       (Finset.univ : Finset (Fin p)).image (pathEdgesNat i v)
  let F : Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
       (Finset.univ : Finset (Fin q)).image (pathEdgesNat j w)
  let S : Finset {z : ℕ × ℕ // z.1 ≤ z.2} := E ∪ F
  let M : {z : ℕ × ℕ // z.1 ≤ z.2} → ℕ := fun e =>
       ((Finset.univ : Finset (Fin p)).filter
          (fun r => pathEdgesNat i v r = e)).card
  let N : {z : ℕ × ℕ // z.1 ≤ z.2} → ℕ := fun e =>
       ((Finset.univ : Finset (Fin q)).filter
          (fun r => pathEdgesNat j w r = e)).card
  have mz {e} (he : e ∉ E) : M e = 0 := by
    dsimp [M]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro r hr hEq
    apply he
    exact Finset.mem_image.mpr ⟨r, by simp, hEq⟩
  have nz {e} (he : e ∉ F) : N e = 0 := by
    dsimp [N]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro r hr hEq
    apply he
    exact Finset.mem_image.mpr ⟨r, by simp, hEq⟩
  have cm : ∑ e ∈ E, M e = p := by
    have h := Finset.card_eq_sum_card_image (pathEdgesNat i v)
         (Finset.univ : Finset (Fin p))
    -- this formula has the opposite orientation
    simpa [E, M] using h.symm
  have cn : ∑ e ∈ F, N e = q := by
    have h := Finset.card_eq_sum_card_image (pathEdgesNat j w)
         (Finset.univ : Finset (Fin q))
    simpa [F, N] using h.symm
  have cM : ∑ e ∈ S, M e = p := by
    calc
      ∑ e ∈ S, M e = ∑ e ∈ E, M e := by
        symm
        apply Finset.sum_subset (by
          intro x hx
          exact Finset.mem_union_left _ hx)
        intro e heS heE
        exact mz heE
      _ = p := cm
  have cN : ∑ e ∈ S, N e = q := by
    calc
      ∑ e ∈ S, N e = ∑ e ∈ F, N e := by
        symm
        apply Finset.sum_subset (by
          intro x hx
          exact Finset.mem_union_right _ hx)
        intro e heS heF
        exact nz heF
      _ = q := cn
  have each : (∑ _e ∈ S, 2) ≤ ∑ e ∈ S, (M e + N e) := by
    exact Finset.sum_le_sum (fun e he => two e he)
  have sumMN : (∑ e ∈ S, (M e + N e)) = p+q := by
    rw [Finset.sum_add_distrib]
    -- both are sums with a double binder
    rw [cM, cN]
  have twice : 2 * S.card ≤ p+q := by
    rw [sumMN] at each
    simpa [mul_comm, mul_left_comm, mul_assoc] using each
  change S.card ≤ (p+q)/2
  omega
end WignerSupport

namespace WignerSupport
/-- Labelling bound for *two* rooted words.  The domain has `p+q+2`
letters (two roots); keeping that second root is important in variance
counts. -/
lemma card_small_pair_vertices {n p q d : ℕ} :
    Fintype.card
      {z : (Fin n × (Fin p → Fin n)) × (Fin n × (Fin q → Fin n)) //
        (pairVertices z.1.1 z.1.2
          z.2.1 z.2.2).card ≤ d} ≤
        n^d * d^((p+1)+(q+1)) := by
  classical
  let H :=
      {z : (Fin n × (Fin p → Fin n)) × (Fin n × (Fin q → Fin n)) //
        (pairVertices z.1.1 z.1.2
          z.2.1 z.2.2).card ≤ d}
  let K := {g : (Fin ((p+1)+(q+1)) → Fin n) //
        (Finset.univ.image g).card ≤ d}
  let join (z : (Fin n × (Fin p → Fin n)) ×
                   (Fin n × (Fin q → Fin n))) :
        Fin ((p+1)+(q+1)) → Fin n := fun u =>
      Sum.elim
        (@Fin.cons p (fun _ => Fin n) z.1.1 z.1.2)
        (@Fin.cons q (fun _ => Fin n) z.2.1 z.2.2)
        (finSumFinEquiv.symm u)
  have imjoin (z : (Fin n × (Fin p → Fin n)) ×
                   (Fin n × (Fin q → Fin n))) :
      (Finset.univ.image (join z)) =
        (Finset.univ.image
          (@Fin.cons p (fun _ => Fin n) z.1.1 z.1.2)) ∪
        (Finset.univ.image
          (@Fin.cons q (fun _ => Fin n) z.2.1 z.2.2)) := by
    ext a
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨u, -, hu⟩
      generalize eq : finSumFinEquiv.symm u = y at hu
      cases y with
      | inl r =>
        apply Finset.mem_union_left
          (Finset.univ.image
            (@Fin.cons q (fun _ => Fin n) z.2.1 z.2.2))
        exact Finset.mem_image.mpr ⟨r, by simp, (by simpa [join, eq] using hu)⟩
      | inr r =>
        apply Finset.mem_union_right
          (Finset.univ.image
            (@Fin.cons p (fun _ => Fin n) z.1.1 z.1.2))
        exact Finset.mem_image.mpr ⟨r, by simp, (by simpa [join, eq] using hu)⟩
    · intro h
      rcases Finset.mem_union.mp h with h|h
      · rcases Finset.mem_image.mp h with ⟨r, -, hr⟩
        refine Finset.mem_image.mpr
          ⟨finSumFinEquiv (Sum.inl r), by simp, ?_⟩
        change Sum.elim _ _ (finSumFinEquiv.symm
          (finSumFinEquiv (Sum.inl r))) = a
        simpa using hr
      · rcases Finset.mem_image.mp h with ⟨r, -, hr⟩
        refine Finset.mem_image.mpr
          ⟨finSumFinEquiv (Sum.inr r), by simp, ?_⟩
        change Sum.elim _ _ (finSumFinEquiv.symm
          (finSumFinEquiv (Sum.inr r))) = a
        simpa using hr
  have cards (z : (Fin n × (Fin p → Fin n)) ×
                   (Fin n × (Fin q → Fin n))) :
      (Finset.univ.image (join z)).card =
        (pairVertices z.1.1 z.1.2 z.2.1 z.2.2).card := by
    let A : Fin (p+1) → Fin n :=
        @Fin.cons p (fun _ => Fin n) z.1.1 z.1.2
    let B : Fin (q+1) → Fin n :=
        @Fin.cons q (fun _ => Fin n) z.2.1 z.2.2
    let T : Finset (Fin n) := (Finset.univ.image A) ∪
         (Finset.univ.image B)
    have j : (Finset.univ.image (join z)) = T := imjoin z
    rw [j]
    have inj := Finset.card_image_of_injective T
      (f := fun x : Fin n => x.val) (fun a b h => Fin.ext h)
    -- the natural image of `T` is the union of the two path vertex images
    have valT : T.image (fun x : Fin n => x.val) =
        pairVertices z.1.1 z.1.2 z.2.1 z.2.2 := by
      dsimp [T]
      rw [Finset.image_union, Finset.image_image, Finset.image_image]
      change
        (Finset.univ.image
          (fun r => (@Fin.cons p (fun _ => Fin n) z.1.1 z.1.2 r).val)) ∪
        (Finset.univ.image
          (fun r => (@Fin.cons q (fun _ => Fin n) z.2.1 z.2.2 r).val)) = _
      simp [pairVertices, pathVertices_eq_image_cons]
    rw [← valT]
    exact inj.symm
  let toK : H → K := fun z =>
    ⟨join z.val, by
      rw [cards]
      exact z.property⟩
  have jin : Function.Injective join := by
    intro a b h
    have hfun (r : Fin (p+1)) :
        (@Fin.cons p (fun _ => Fin n) a.1.1 a.1.2 r) =
          (@Fin.cons p (fun _ => Fin n) b.1.1 b.1.2 r) := by
      have := congrFun h (finSumFinEquiv (Sum.inl r))
      simpa [join] using this
    have hfun' (r : Fin (q+1)) :
        (@Fin.cons q (fun _ => Fin n) a.2.1 a.2.2 r) =
          (@Fin.cons q (fun _ => Fin n) b.2.1 b.2.2 r) := by
      have := congrFun h (finSumFinEquiv (Sum.inr r))
      simpa [join] using this
    have h1 : a.1 = b.1 :=
      (Fin.consEquiv (fun _ : Fin (p+1) => Fin n)).injective
        (funext hfun)
    have h2 : a.2 = b.2 :=
      (Fin.consEquiv (fun _ : Fin (q+1) => Fin n)).injective
        (funext hfun')
    exact Prod.ext h1 h2
  have tk : Function.Injective toK := by
    intro a b h
    exact Subtype.ext (jin (congrArg Subtype.val h))
  have first : Fintype.card H ≤ Fintype.card K :=
    Fintype.card_le_of_injective toK tk
  have second : Fintype.card K ≤ n^d * d^((p+1)+(q+1)) := by
    change Fintype.card
      {g : Fin ((p+1)+(q+1)) → Fin n //
        (Finset.univ.image g).card ≤ d} ≤ _
    exact card_small_image_fun (by omega)
  exact first.trans second

lemma card_filter_small_pair_vertices {n p q d : ℕ} :
    ((Finset.univ : Finset
       ((Fin n × (Fin p → Fin n)) × (Fin n × (Fin q → Fin n)))).filter
       (fun z => (pairVertices z.1.1 z.1.2 z.2.1 z.2.2).card ≤ d)).card ≤
       n^d * d^((p+1)+(q+1)) := by
  classical
  have h := card_small_pair_vertices (n:=n) (p:=p) (q:=q) (d:=d)
  simpa only [Fintype.card_subtype] using h
end WignerSupport
namespace WignerSupport
variable {Ω : Type*} [MeasurableSpace Ω]
/-- Cardinal-one form of singleton pruning. -/
lemma integral_pathTerm_zero_of_fiber_one
    (μ : Measure Ω)
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
      (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (hz : ∀ a b, a ≤ b → (∫ ω, Y a b ω ∂μ) = (0:ℝ))
    (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
    (e : {z : ℕ × ℕ // z.1 ≤ z.2})
    (he : e ∈ Finset.univ.image (pathEdgesNat i v))
    (one : ((Finset.univ : Finset (Fin p)).filter
       (fun r => pathEdgesNat i v r = e)).card = 1) :
    (∫ a, pathTerm (fun b c : Fin n =>
       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) = 0 := by
  classical
  rcases Finset.mem_image.mp he with ⟨u, hu, eq⟩
  have uniq : ∀ r, pathEdgesNat i v r = pathEdgesNat i v u → r = u := by
    intro r hr
    by_contra ne
    have tw := two_le_card_fiber_of_pair
       (Finset.univ : Finset (Fin p)) (pathEdgesNat i v)
       (by simp : u ∈ (Finset.univ : Finset (Fin p)))
       (by simp : r ∈ (Finset.univ : Finset (Fin p))) ne hr
    -- replace the distinguished edge in the displayed fibre by `u`
    have ou : ((Finset.univ : Finset (Fin p)).filter
        (fun k => pathEdgesNat i v k = pathEdgesNat i v u)).card = 1 := by
      simpa [eq] using one
    omega
  exact integral_pathTerm_zero_of_unique_edge μ Y hm hi hz n p i v u uniq

/-- If a doubled word has a singleton, one of its individual means and
also its mixed mean vanish; consequently its covariance vanishes exactly,
not just by a norm estimate. -/
lemma covariance_pathTerm_zero_of_unique_union
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
      (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (hz : ∀ a b, a ≤ b → (∫ ω, Y a b ω ∂μ) = (0:ℝ))
    (n p q : ℕ) (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (w : Fin q → Fin n)
    (e : {z : ℕ × ℕ // z.1 ≤ z.2})
    (he : e ∈ pairEdges i v j w)
    (one :
       ((Finset.univ : Finset (Fin p)).filter
          (fun r => pathEdgesNat i v r = e)).card +
       ((Finset.univ : Finset (Fin q)).filter
          (fun r => pathEdgesNat j w r = e)).card = 1) :
    (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ) -
      (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
      (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ) = 0 := by
  classical
  let M := ((Finset.univ : Finset (Fin p)).filter
          (fun r => pathEdgesNat i v r = e)).card
  let N := ((Finset.univ : Finset (Fin q)).filter
          (fun r => pathEdgesNat j w r = e)).card
  have mix : (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ) = 0 :=
    integral_mul_pathTerm_zero_of_unique_union μ Y hm hi hz
       n n p q i v j w e he one
  rw [mix]
  have ar : M = 1 ∧ N = 0 ∨ M = 0 ∧ N = 1 := by omega
  rcases ar with ar|ar
  · have ev : e ∈ (Finset.univ.image (pathEdgesNat i v)) := by
      by_contra h
      have z : M = 0 := by
        dsimp [M]
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro r hr rr
        exact h (Finset.mem_image.mpr ⟨r, by simp, rr⟩)
      omega
    have zero := integral_pathTerm_zero_of_fiber_one μ Y hm hi hz n p i v e ev ar.1
    rw [zero]
    ring
  · have ev : e ∈ (Finset.univ.image (pathEdgesNat j w)) := by
      by_contra h
      have zc : N = 0 := by
        dsimp [N]
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro r hr rr
        exact h (Finset.mem_image.mpr ⟨r, by simp, rr⟩)
      omega
    have zero := integral_pathTerm_zero_of_fiber_one μ Y hm hi hz n q j w e ev ar.2
    rw [zero]
    ring
end WignerSupport
namespace WignerSupport
variable {Ω : Type*} [MeasurableSpace Ω]
lemma abs_integral_mul_pathTerm_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ a b ω, |Y a b ω| ≤ B)
    (n p q : ℕ) (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (w : Fin q → Fin n) :
    |(∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ)| ≤
       B^(p+q) := by
  classical
  have one (a : Ω) :
      |pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v| ≤ B^p := by
    rw [pathTerm_real_wigner Y a n p i v, Finset.abs_prod]
    calc
      (∏ r : Fin p, |Y (pathEdgesNat i v r).val.1
           (pathEdgesNat i v r).val.2 a|) ≤ ∏ _r : Fin p, B := by
             exact Finset.prod_le_prod (fun r hr => abs_nonneg _)
               (fun r hr => hb _ _ _)
      _ = B^p := by simp
  have two (a : Ω) :
      |pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w| ≤ B^q := by
    rw [pathTerm_real_wigner Y a n q j w, Finset.abs_prod]
    calc
      (∏ r : Fin q, |Y (pathEdgesNat j w r).val.1
           (pathEdgesNat j w r).val.2 a|) ≤ ∏ _r : Fin q, B := by
             exact Finset.prod_le_prod (fun r hr => abs_nonneg _)
               (fun r hr => hb _ _ _)
      _ = B^q := by simp
  have point (a : Ω) :
      ‖pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w‖ ≤ B^(p+q) := by
    rw [Real.norm_eq_abs, abs_mul, pow_add]
    exact mul_le_mul (one a) (two a) (abs_nonneg _) (pow_nonneg hB _)
  simpa [Real.norm_eq_abs] using
    (MeasureTheory.norm_integral_le_of_norm_le_const (μ:=μ)
      (f:= fun a =>
        pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w)
      (C:=B^(p+q)) (ae_of_all _ point))

lemma abs_covariance_pathTerm_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ a b ω, |Y a b ω| ≤ B)
    (n p q : ℕ) (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (w : Fin q → Fin n) :
    |(∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ) -
      (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
      (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ)| ≤
       2 * B^(p+q) := by
  have aa := abs_integral_mul_pathTerm_le μ Y B hB hb n p q i v j w
  have bb := abs_integral_pathTerm_le μ Y B hB hb n p i v
  have cc := abs_integral_pathTerm_le μ Y B hB hb n q j w
  calc
    |(∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ) -
      (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
      (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ)| ≤
      |(∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ)| +
      |(∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
       (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) q j w ∂μ)| := abs_sub _ _
    _ ≤ B^(p+q) + B^(p+q) := by
      gcongr
      rw [abs_mul, pow_add]
      exact mul_le_mul bb cc (abs_nonneg _) (pow_nonneg hB _)
    _ = 2 * B^(p+q) := by ring
end WignerSupport
namespace WignerSupport
lemma one_le_pair_fiber {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n)
    (e : {z : ℕ × ℕ // z.1 ≤ z.2}) (he : e ∈ pairEdges i v j w) :
    1 ≤ ((Finset.univ : Finset (Fin p)).filter
             (fun r => pathEdgesNat i v r = e)).card +
         ((Finset.univ : Finset (Fin q)).filter
             (fun r => pathEdgesNat j w r = e)).card := by
  classical
  rcases Finset.mem_union.mp he with h|h
  · rcases Finset.mem_image.mp h with ⟨r, -, eq⟩
    have pos : 1 ≤ ((Finset.univ : Finset (Fin p)).filter
             (fun x => pathEdgesNat i v x = e)).card := by
      have : r ∈ ((Finset.univ : Finset (Fin p)).filter
             (fun x => pathEdgesNat i v x = e)) := by simp [eq]
      exact (Finset.one_le_card).mpr ⟨r, this⟩
    omega
  · rcases Finset.mem_image.mp h with ⟨r, -, eq⟩
    have pos : 1 ≤ ((Finset.univ : Finset (Fin q)).filter
             (fun x => pathEdgesNat j w x = e)).card := by
      have : r ∈ ((Finset.univ : Finset (Fin q)).filter
             (fun x => pathEdgesNat j w x = e)) := by simp [eq]
      exact (Finset.one_le_card).mpr ⟨r, this⟩
    omega
end WignerSupport

namespace WignerSupport
open scoped Sym2
open SimpleGraph
/-- A literal loop in the doubled edge alphabet is invisible to the simple
pair graph. Consequently its edge set injects into the alphabet with that
loop erased. This is the small strictness fact needed in the extremal
connected-tree variance count. -/
lemma card_pairGraph_edges_le_erase_loop {n p q : ℕ}
    (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n) (x : ℕ)
    (hx : edgeNat x x ∈ pairEdges i v j w) :
    Nat.card (pairGraph i v j w).edgeSet ≤
      (pairEdges i v j w).card - 1 := by
  classical
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
      (pairEdges i v j w).erase (edgeNat x x)
  let val : PairVert i v j w → ℕ := fun a => a.val
  have key : ∀ z0 : Sym2 (PairVert i v j w),
      z0 ∈ (pairGraph i v j w).edgeSet → __PairVar_symNat val z0 ∈ E := by
    intro z0 hz
    have orig : __PairVar_symNat val z0 ∈ pairEdges i v j w := by
      induction z0 using Sym2.inductionOn with
      | _ a b =>
        have ad : (pairGraph i v j w).Adj a b :=
          (SimpleGraph.mem_edgeSet _).1 hz
        exact (pairGraph_adj _ _).1 ad |>.2
    have ne : __PairVar_symNat val z0 ≠ edgeNat x x := by
      intro eq
      induction z0 using Sym2.inductionOn with
      | _ a b =>
        have ad : (pairGraph i v j w).Adj a b :=
          (SimpleGraph.mem_edgeSet _).1 hz
        have ab := (pairGraph_adj _ _).1 ad
        change edgeNat a.val b.val = edgeNat x x at eq
        have e1 : min a.val b.val = x := by
          have h := congrArg (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => e.val.1) eq
          simpa [edgeNat] using h
        have e2 : max a.val b.val = x := by
          have h := congrArg (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => e.val.2) eq
          simpa [edgeNat] using h
        have sameVal : a.val = b.val := by omega
        exact ab.1 (Subtype.ext sameVal)
    exact (Finset.mem_erase).2 ⟨ne, orig⟩
  have mem (z : (pairGraph i v j w).edgeSet) :
      __PairVar_symNat val z.val ∈ E := key z.val z.property
  let f : (pairGraph i v j w).edgeSet →
        {e : {z : ℕ × ℕ // z.1 ≤ z.2} // e ∈ E} :=
      fun z => ⟨__PairVar_symNat val z.val, mem z⟩
  have inj : Function.Injective f := by
    intro a b hab
    have vals : __PairVar_symNat val a.val = __PairVar_symNat val b.val :=
      congrArg Subtype.val hab
    have sy : a.val = b.val := by
      exact (@__PairVar_symNat_inj_sub (pairVertices i v j w)) vals
    exact Subtype.ext sy
  letI : Fintype (PairVert i v j w) := Fintype.ofFinite _
  letI : Fintype (pairGraph i v j w).edgeSet := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective f inj
  rw [Nat.card_eq_fintype_card]
  have cardE : E.card = (pairEdges i v j w).card - 1 := by
    dsimp [E]
    exact Finset.card_erase_of_mem hx
  simpa [Fintype.card_coe, cardE] using h

/-- In the tight connected count the doubled alphabet has no literal loops. -/
lemma pairEdges_no_self_of_tight {n p q : ℕ}
    (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n)
    (hh : (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty)
    (tight : (pairVertices i v j w).card =
              (pairEdges i v j w).card + 1) :
    ∀ x : ℕ, edgeNat x x ∉ pairEdges i v j w := by
  classical
  intro x hx
  have conn := pairGraph_connected_of_edge i v j w hh
  have c := conn.card_vert_le_card_edgeSet_add_one
  letI : Fintype (PairVert i v j w) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at c
  have e := card_pairGraph_edges_le_erase_loop i v j w x hx
  have chain : (pairVertices i v j w).card ≤
        ((pairEdges i v j w).card - 1) + 1 :=
    c.trans (Nat.add_le_add_right e 1)
  have pos : 0 < (pairEdges i v j w).card :=
    Finset.card_pos.mpr ⟨edgeNat x x, hx⟩
  omega

/-- Tightness makes the pair graph itself a finite tree. -/
lemma pairGraph_isTree_of_tight {n p q : ℕ}
    (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n)
    (hh : (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty)
    (tight : (pairVertices i v j w).card =
              (pairEdges i v j w).card + 1) :
    (pairGraph i v j w).IsTree := by
  classical
  have conn := pairGraph_connected_of_edge i v j w hh
  have c := conn.card_vert_le_card_edgeSet_add_one
  have el := card_pairGraph_edges_le i v j w
  letI : Fintype (PairVert i v j w) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at c
  have eqe : Nat.card (pairGraph i v j w).edgeSet =
      (pairEdges i v j w).card := by omega
  apply (SimpleGraph.isTree_iff_connected_and_card).2
  refine ⟨conn, ?_⟩
  letI : Fintype (pairGraph i v j w).edgeSet := Fintype.ofFinite _
  have ve : Nat.card (PairVert i v j w) =
        (pairVertices i v j w).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have done : Nat.card (pairGraph i v j w).edgeSet + 1 =
        Nat.card (PairVert i v j w) := by omega
  simpa [Nat.card_eq_fintype_card] using done
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PairVar.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PairDrop.lean
section
open scoped Sym2 BigOperators
open SimpleGraph
namespace WignerSupport

/-- One word in a doubled alphabet embeds as a graph hom into the pair graph. -/
def firstWalkHom {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n) :
    walkGraph i.val (pathList v) →g pairGraph i v j w where
  toFun a := ⟨a.val, Finset.mem_union_left _ a.property⟩
  map_rel' := by
    intro a b h
    have hh := (walkGraph_adj _ _).1 h
    apply (pairGraph_adj _ _).2
    refine ⟨?_, ?_⟩
    · intro z
      exact hh.1 (Subtype.ext (congrArg (fun x : PairVert i v j w => x.val) z))
    · exact Finset.mem_union_left _ (by
        rw [image_pathEdges_eq_walkEdges]
        exact hh.2)

lemma firstWalkHom_inj {n p q : ℕ} (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n) :
    Function.Injective (firstWalkHom i v j w) := by
  intro a b eq
  exact Subtype.ext (congrArg (fun x : PairVert i v j w => x.val) eq)

/-- In a tight doubled tree, either component walk has the familiar equality
`vertices = edges+1`. Tightness first rules out all literal loops; then the
component graph injects into the pair tree, hence is acyclic. Connectedness
and the finite tree count finish the numerical equality. -/
lemma first_walk_eq_of_pair_tight {n p q : ℕ}
    (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n)
    (hh : (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty)
    (tight : (pairVertices i v j w).card =
              (pairEdges i v j w).card + 1) :
    (walkVertices i.val (pathList v)).card =
      (walkEdges i.val (pathList v)).card + 1 := by
  classical
  letI : Fintype (WalkVert i.val (pathList v)) := Fintype.ofFinite _
  have noPair := pairEdges_no_self_of_tight i v j w hh tight
  have no : ∀ x : ℕ, edgeNat x x ∉ walkEdges i.val (pathList v) := by
    intro x hx
    apply noPair x
    apply Finset.mem_union_left
    simpa [image_pathEdges_eq_walkEdges] using hx
  have ac : (walkGraph i.val (pathList v)).IsAcyclic :=
    SimpleGraph.IsAcyclic.comap (firstWalkHom i v j w)
      (firstWalkHom_inj i v j w)
      (pairGraph_isTree_of_tight i v j w hh tight).isAcyclic
  have tr : (walkGraph i.val (pathList v)).IsTree :=
    ⟨walkGraph_connected _ _ no, ac⟩
  have cnt := (SimpleGraph.isTree_iff_connected_and_card.mp tr).2
  have ce := card_walkGraph_edges i.val (pathList v) no
  rw [ce] at cnt
  -- the vertices of the subtype `WalkVert` have the finset's cardinal
  simpa [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.add_comm] using cnt.symm

lemma second_walk_eq_of_pair_tight {n p q : ℕ}
    (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n)
    (hh : (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty)
    (tight : (pairVertices i v j w).card =
              (pairEdges i v j w).card + 1) :
    (walkVertices j.val (pathList w)).card =
      (walkEdges j.val (pathList w)).card + 1 := by
  have meet : (Finset.univ.image (pathEdgesNat j w) ∩
            Finset.univ.image (pathEdgesNat i v)).Nonempty := by
    simpa [Finset.inter_comm] using hh
  have sw := first_walk_eq_of_pair_tight j w i v meet
  -- pair sets are unions, so tightness is symmetric
  apply sw
  simpa [pairVertices, pairEdges, Finset.union_comm] using tight

end WignerSupport
namespace WignerSupport
-- Need the list/Fin compatibility for the repeated occurrence lemma.
-- (qualified import below also supplies the harmless bound casts.)
end WignerSupport
namespace WignerSupport
lemma first_fiber_two_of_pair_tight {n p q : ℕ}
    (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n)
    (hh : (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty)
    (tight : (pairVertices i v j w).card =
              (pairEdges i v j w).card + 1)
    (cl : pathEnd p i v = i) :
    ∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
      pathEdgesNat i v r = pathEdgesNat i v u := by
  classical
  let xs : List ℕ := pathList v
  have bd : ∀ a ∈ xs, a < n := by
    intro a ha
    exact mem_walkVertices_path_bound i v
      (show a ∈ walkVertices i.val (pathList v) from by
        dsimp [xs] at ha
        -- vertices are root inserted with the tail letters
        simpa [walkVertices] using (show a = i.val ∨ a ∈ pathList v
          from Or.inr ha))
  have eqw : (walkVertices i.val xs).card =
        (walkEdges i.val xs).card + 1 := by
    simpa [xs] using first_walk_eq_of_pair_tight i v j w hh tight
  have cls : walkLast i.val xs = i.val := by
    have z := pathEnd_val_eq_walkLast i v
    rw [cl] at z
    simpa [xs] using z.symm
  have seen : ∀ k : ℕ, ∀ hk : k < xs.length,
      let b := xs[k]
      let a := walkLast i.val (xs.take k)
      edgeNat a b ∈ walkEdges i.val (xs.take k) ∨
        edgeNat a b ∈ walkEdges b (xs.drop (k+1)) := by
    intro k hk
    exact closed_eq_step_seen_elsewhere i.val xs eqw cls k hk
  have rep := repeated_edges_listPath_of_seen i xs bd seen
  intro u
  let u' : Fin xs.length :=
      ⟨u.val, by simpa [xs, pathList] using u.isLt⟩
  rcases rep u' with ⟨r', ne, er⟩
  let r : Fin p :=
      ⟨r'.val, by simpa [xs, pathList] using r'.isLt⟩
  refine ⟨r, ?_, ?_⟩
  · intro h
    apply ne
    apply Fin.ext
    simpa [r, u'] using (congrArg Fin.val h)
  · have l1 := pathEdges_pathList_cast i v bd r'
    have l2 := pathEdges_pathList_cast i v bd u'
    -- both casts have the original values
    simpa [r, u'] using (l1.symm.trans (er.trans l2))

lemma second_fiber_two_of_pair_tight {n p q : ℕ}
    (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin q → Fin n)
    (hh : (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty)
    (tight : (pairVertices i v j w).card =
              (pairEdges i v j w).card + 1)
    (cl : pathEnd q j w = j) :
    ∀ u : Fin q, ∃ r : Fin q, r ≠ u ∧
      pathEdgesNat j w r = pathEdgesNat j w u := by
  have meet : (Finset.univ.image (pathEdgesNat j w) ∩
            Finset.univ.image (pathEdgesNat i v)).Nonempty := by
    simpa [Finset.inter_comm] using hh
  apply first_fiber_two_of_pair_tight j w i v meet
  · simpa [pairVertices, pairEdges, Finset.union_comm] using tight
  · exact cl

/-- A strict version of the half-edge count. If one fibre of a doubled word
has at least four positions while every fibre has two, a whole edge is lost
when both words have length `p`. -/
lemma card_pairEdges_lt_p_of_four {n p : ℕ}
    (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin p → Fin n)
    (e0 : {z : ℕ × ℕ // z.1 ≤ z.2}) (h0 : e0 ∈ pairEdges i v j w)
    (four : 4 ≤ ((Finset.univ : Finset (Fin p)).filter
              (fun r => pathEdgesNat i v r = e0)).card +
              ((Finset.univ : Finset (Fin p)).filter
              (fun r => pathEdgesNat j w r = e0)).card)
    (two : ∀ e ∈ pairEdges i v j w,
       2 ≤ ((Finset.univ : Finset (Fin p)).filter
              (fun r => pathEdgesNat i v r = e)).card +
            ((Finset.univ : Finset (Fin p)).filter
              (fun r => pathEdgesNat j w r = e)).card) :
    (pairEdges i v j w).card < p := by
  classical
  let E : Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
    (Finset.univ : Finset (Fin p)).image (pathEdgesNat i v)
  let F : Finset {z : ℕ × ℕ // z.1 ≤ z.2} :=
    (Finset.univ : Finset (Fin p)).image (pathEdgesNat j w)
  let S : Finset {z : ℕ × ℕ // z.1 ≤ z.2} := E ∪ F
  let M : {z : ℕ × ℕ // z.1 ≤ z.2} → ℕ := fun e =>
    ((Finset.univ : Finset (Fin p)).filter
      (fun r => pathEdgesNat i v r = e)).card
  let N : {z : ℕ × ℕ // z.1 ≤ z.2} → ℕ := fun e =>
    ((Finset.univ : Finset (Fin p)).filter
      (fun r => pathEdgesNat j w r = e)).card
  have mz {e} (he : e ∉ E) : M e = 0 := by
    dsimp [M]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro r hr eq
    exact he (Finset.mem_image.mpr ⟨r, by simp, eq⟩)
  have nz {e} (he : e ∉ F) : N e = 0 := by
    dsimp [N]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro r hr eq
    exact he (Finset.mem_image.mpr ⟨r, by simp, eq⟩)
  have cM : ∑ e ∈ S, M e = p := by
    calc
      _ = ∑ e ∈ E, M e := by
        symm
        apply Finset.sum_subset (by intro x hx; exact Finset.mem_union_left _ hx)
        intro z hz hne; exact mz hne
      _ = p := by
        have h := Finset.card_eq_sum_card_image (pathEdgesNat i v)
              (Finset.univ : Finset (Fin p))
        simpa [E, M] using h.symm
  have cN : ∑ e ∈ S, N e = p := by
    calc
      _ = ∑ e ∈ F, N e := by
        symm
        apply Finset.sum_subset (by intro x hx; exact Finset.mem_union_right _ hx)
        intro z hz hne; exact nz hne
      _ = p := by
        have h := Finset.card_eq_sum_card_image (pathEdgesNat j w)
              (Finset.univ : Finset (Fin p))
        simpa [F, N] using h.symm
  have sumMN : (∑ e ∈ S, (M e + N e)) = p+p := by
    rw [Finset.sum_add_distrib, cM, cN]
  have oth : ∀ e ∈ S.erase e0, 2 ≤ M e + N e := by
    intro e he
    apply two e
    exact (Finset.mem_of_mem_erase he)
  have strong : 2 * (S.erase e0).card + 4 ≤
        ∑ e ∈ S, (M e + N e) := by
    have low : (∑ _e ∈ S.erase e0, 2) ≤
          ∑ e ∈ S.erase e0, (M e + N e) :=
      Finset.sum_le_sum (fun e he => oth e he)
    have mem0 : e0 ∈ S := h0
    have split := Finset.sum_erase_add _ (fun e => M e + N e) mem0
    -- split : sum on erase + value = sum on S
    calc
      2 * (S.erase e0).card + 4 =
          (∑ _e ∈ S.erase e0, 2) + 4 := by simp; ring
      _ ≤ (∑ e ∈ S.erase e0, (M e + N e)) + (M e0 + N e0) :=
          Nat.add_le_add low four
      _ = ∑ e ∈ S, (M e + N e) := split
  have mem0 : e0 ∈ S := h0
  have erase : (S.erase e0).card + 1 = S.card :=
    Finset.card_erase_add_one mem0
  rw [sumMN] at strong
  change S.card < p
  omega

private lemma __PairDrop_two_mem_filter_of_repeat {p : ℕ}
    {α : Type*} [DecidableEq α] (f : Fin p → α) (e : α) (u : Fin p)
    (hu : f u = e) (rep : ∃ r : Fin p, r ≠ u ∧ f r = f u) :
    2 ≤ ((Finset.univ : Finset (Fin p)).filter (fun r => f r = e)).card := by
  classical
  rcases rep with ⟨r, ne, hr⟩
  have um : u ∈ (Finset.univ : Finset (Fin p)).filter (fun r => f r = e) := by simp [hu]
  have rm : r ∈ (Finset.univ : Finset (Fin p)).filter (fun r => f r = e) := by
    simp [hr, hu]
  have ss : ({u, r} : Finset (Fin p)) ⊆
      (Finset.univ : Finset (Fin p)).filter (fun r => f r = e) := by
    intro z hz
    simp at hz
    rcases hz with h|h
    · simpa [h] using um
    · simpa [h] using rm
  have card := Finset.card_le_card ss
  simpa [Finset.card_pair ne.symm] using card

/-- The extremal `p+1` of the crude doubled count cannot occur for two
*closed* words with a common edge. In a tight tree each component is a
closed equality walk; hence every occurrence of the common edge has a
second occurrence in that component. Its union fibre has at least four,
contradicting the tight half-edge budget. -/
lemma card_pairVertices_le_p_of_closed {n p : ℕ}
    (i : Fin n) (v : Fin p → Fin n)
    (j : Fin n) (w : Fin p → Fin n)
    (ci : pathEnd p i v = i) (cj : pathEnd p j w = j)
    (hh : (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty)
    (two : ∀ e ∈ pairEdges i v j w,
       2 ≤ ((Finset.univ : Finset (Fin p)).filter
              (fun r => pathEdgesNat i v r = e)).card +
            ((Finset.univ : Finset (Fin p)).filter
              (fun r => pathEdgesNat j w r = e)).card) :
    (pairVertices i v j w).card ≤ p := by
  classical
  have E := card_pairEdges_le_half_of_union i v j w two
  have Ech : (pairEdges i v j w).card ≤ p := by
    have id : (p+p)/2 = p := by omega
    simpa [id] using E
  have V := card_pairVertices_le_edges_add_one_of_edge i v j w hh
  by_contra bad
  have ec : (pairEdges i v j w).card = p := by omega
  have vc : (pairVertices i v j w).card =
        (pairEdges i v j w).card + 1 := by omega
  rcases hh with ⟨e, he⟩
  have ei : e ∈ Finset.univ.image (pathEdgesNat i v) :=
      (Finset.mem_inter.mp he).1
  have ej : e ∈ Finset.univ.image (pathEdgesNat j w) :=
      (Finset.mem_inter.mp he).2
  rcases Finset.mem_image.mp ei with ⟨ui, _, hui⟩
  rcases Finset.mem_image.mp ej with ⟨uj, _, huj⟩
  -- use the repeated-position conclusions in the two closed component trees
  have repi := first_fiber_two_of_pair_tight i v j w
      (show (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty from ⟨e, he⟩)
      vc ci ui
  have repj := second_fiber_two_of_pair_tight i v j w
      (show (Finset.univ.image (pathEdgesNat i v) ∩
            Finset.univ.image (pathEdgesNat j w)).Nonempty from ⟨e, he⟩)
      vc cj uj
  have one : 2 ≤ ((Finset.univ : Finset (Fin p)).filter
             (fun r => pathEdgesNat i v r = e)).card :=
    __PairDrop_two_mem_filter_of_repeat (pathEdgesNat i v) e ui hui repi
  have another : 2 ≤ ((Finset.univ : Finset (Fin p)).filter
             (fun r => pathEdgesNat j w r = e)).card :=
    __PairDrop_two_mem_filter_of_repeat (pathEdgesNat j w) e uj huj repj
  have four : 4 ≤ ((Finset.univ : Finset (Fin p)).filter
             (fun r => pathEdgesNat i v r = e)).card +
             ((Finset.univ : Finset (Fin p)).filter
             (fun r => pathEdgesNat j w r = e)).card := by omega
  have lt := card_pairEdges_lt_p_of_four i v j w e
       (Finset.mem_union_left _ ei) four two
  omega
end WignerSupport

namespace WignerSupport
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω]
/-- Centered iid path covariances of two closed `p`-words are supported on
at most `p` labels. This combines the disjoint/singleton cancellations with
the tight-tree obstruction. Keeping it as a support lemma avoids repeating
the probabilistic algebra in each finite trace. -/
lemma covariance_pathTerm_zero_of_big_closed
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
       (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (hz : ∀ a b, a ≤ b → (∫ w, Y a b w ∂μ) = (0:ℝ))
    (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (u : Fin p → Fin n)
    (ci : pathEnd p i v = i) (cj : pathEnd p j u = j)
    (big : ¬ (pairVertices i v j u).card ≤ p) :
    (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
        pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ) -
      (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
      (∫ a, pathTerm (fun b c : Fin n =>
          Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ) = 0 := by
  classical
  by_cases dj : Disjoint (Finset.univ.image (pathEdgesNat i v))
                      (Finset.univ.image (pathEdgesNat j u))
  · rw [integral_mul_pathTerm_of_disjoint μ Y hm hi n n p p i v j u dj]
    ring
  · have meet : (Finset.univ.image (pathEdgesNat i v) ∩
                     Finset.univ.image (pathEdgesNat j u)).Nonempty :=
        Finset.not_disjoint_iff_nonempty_inter.mp dj
    by_cases every : ∀ e ∈ pairEdges i v j u,
             2 ≤ ((Finset.univ : Finset (Fin p)).filter
                    (fun r => pathEdgesNat i v r = e)).card +
                  ((Finset.univ : Finset (Fin p)).filter
                    (fun r => pathEdgesNat j u r = e)).card
    · exact False.elim
        (big (card_pairVertices_le_p_of_closed i v j u ci cj meet every))
    · push_neg at every
      rcases every with ⟨e, he, lt⟩
      have lo := one_le_pair_fiber i v j u e he
      have one : ((Finset.univ : Finset (Fin p)).filter
                    (fun r => pathEdgesNat i v r = e)).card +
                  ((Finset.univ : Finset (Fin p)).filter
                    (fun r => pathEdgesNat j u r = e)).card = 1 := by omega
      exact covariance_pathTerm_zero_of_unique_union
             μ Y hm hi hz n p p i v j u e he one
end WignerSupport
namespace WignerSupport
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω]
/-- Polynomial, **summable** fixed trace-variance bound after the tight-tree
cancellation. The normalization of two traces is `n^(p+2)`, so `n^p`
here is the crucial two-power saving. -/
lemma abs_sum_cov_closed_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
       (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (hz : ∀ a b, a ≤ b → (∫ w, Y a b w ∂μ) = (0:ℝ))
    (B : ℝ) (B0 : 0 ≤ B) (hb : ∀ i j ω, |Y i j ω| ≤ B)
    (n p : ℕ) :
    |∑ i : Fin n, ∑ v : (Fin p → Fin n),
       ∑ j : Fin n, ∑ u : (Fin p → Fin n),
         if pathEnd p i v = i ∧ pathEnd p j u = j then
           ((∫ a, pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
             pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ) -
            (∫ a, pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
            (∫ a, pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ))
         else 0| ≤
       ((n:ℝ)^p * (p:ℝ)^((p+1)+(p+1))) * (2 * B^(p+p)) := by
  classical
  let cov (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (u : Fin p → Fin n) : ℝ :=
           (∫ a, pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
             pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ) -
            (∫ a, pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
            (∫ a, pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ)
  let T (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (u : Fin p → Fin n) : ℝ :=
       if pathEnd p i v = i ∧ pathEnd p j u = j then cov i v j u else 0
  let S : Finset ((Fin n × (Fin p → Fin n)) ×
                  (Fin n × (Fin p → Fin n))) :=
       Finset.univ.filter
         (fun z => (pairVertices z.1.1 z.1.2 z.2.1 z.2.2).card ≤ p)
  have point (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (u : Fin p → Fin n) : |T i v j u| ≤ 2 * B^(p+p) := by
    dsimp [T]
    split_ifs
    · exact abs_covariance_pathTerm_le μ Y B B0 hb n p p i v j u
    · have pow : 0 ≤ B^(p+p) := pow_nonneg B0 _
      simp [pow]
  have outside (i : Fin n) (v : Fin p → Fin n)
       (j : Fin n) (u : Fin p → Fin n)
       (hnot : ((i,v),(j,u)) ∉ S) : T i v j u = 0 := by
    dsimp [S] at hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    dsimp [T]
    by_cases h : pathEnd p i v = i ∧ pathEnd p j u = j
    · simp [h, cov,
        covariance_pathTerm_zero_of_big_closed μ Y hm hi hz n p i v j u h.1 h.2 hnot]
    · simp [h]
  have collapse :
       (∑ i : Fin n, ∑ v : (Fin p → Fin n),
         ∑ j : Fin n, ∑ u : (Fin p → Fin n), T i v j u) =
           ∑ z ∈ S, T z.1.1 z.1.2 z.2.1 z.2.2 := by
    calc
      _ = ∑ a : (Fin n × (Fin p → Fin n)),
            ∑ b : (Fin n × (Fin p → Fin n)),
                T a.1 a.2 b.1 b.2 := by
                  simp_rw [Fintype.sum_prod_type]
      _ = ∑ z : ((Fin n × (Fin p → Fin n)) ×
                   (Fin n × (Fin p → Fin n))),
                T z.1.1 z.1.2 z.2.1 z.2.2 := by
                  exact (Fintype.sum_prod_type
                    (fun z : ((Fin n × (Fin p → Fin n)) ×
                               (Fin n × (Fin p → Fin n))) =>
                       T z.1.1 z.1.2 z.2.1 z.2.2)).symm
      _ = ∑ z ∈ S, T z.1.1 z.1.2 z.2.1 z.2.2 := by
            symm
            apply Finset.sum_subset (by intro x hx; simp)
            intro z hz hn
            exact outside z.1.1 z.1.2 z.2.1 z.2.2 hn
  change |∑ i : Fin n, ∑ v : (Fin p → Fin n),
         ∑ j : Fin n, ∑ u : (Fin p → Fin n), T i v j u| ≤ _
  rw [collapse]
  calc
    |∑ z ∈ S, T z.1.1 z.1.2 z.2.1 z.2.2| ≤
      ∑ z ∈ S, |T z.1.1 z.1.2 z.2.1 z.2.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ S, (2 * B^(p+p)) :=
          Finset.sum_le_sum (fun z hz => point z.1.1 z.1.2 z.2.1 z.2.2)
    _ = (S.card:ℝ) * (2 * B^(p+p)) := by simp
    _ ≤ ((n^p * p^((p+1)+(p+1)) : ℕ):ℝ) * (2 * B^(p+p)) := by
          have non : 0 ≤ (2 * B^(p+p)) := by positivity
          gcongr
          dsimp [S]
          exact_mod_cast (card_filter_small_pair_vertices
             (n:=n) (p:=p) (q:=p) (d:=p))
    _ = ((n:ℝ)^p * (p:ℝ)^((p+1)+(p+1))) * (2 * B^(p+p)) := by
          push_cast
          ring
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/PairDrop.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/TraceConc.lean
section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Matrix
namespace WignerSupport
variable {Ω : Type*} [MeasurableSpace Ω]

lemma memLp_pathTerm_real_wigner
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ a b ω, |Y a b ω| ≤ B)
    (n p : ℕ) (i : Fin n) (v : Fin p → Fin n) :
    MemLp (fun ω => pathTerm (fun a b : Fin n =>
      Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v) 2 μ := by
  classical
  have meas : StronglyMeasurable (fun ω => pathTerm (fun a b : Fin n =>
      Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v) := by
    rw [show (fun ω => pathTerm (fun a b : Fin n =>
        Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v) =
      (fun ω => ∏ r : Fin p, Y (pathEdgesNat i v r).val.1
        (pathEdgesNat i v r).val.2 ω) by
          funext ω; exact pathTerm_real_wigner Y ω n p i v]
    exact Measurable.stronglyMeasurable (by fun_prop)
  apply MemLp.of_bound (μ:=μ) meas.aestronglyMeasurable (B^p)
  filter_upwards [] with ω
  have eq := pathTerm_real_wigner Y ω n p i v
  rw [eq, Real.norm_eq_abs, Finset.abs_prod]
  calc
    (∏ r : Fin p, |Y (pathEdgesNat i v r).val.1
        (pathEdgesNat i v r).val.2 ω|) ≤
        ∏ _r : Fin p, B := by
          exact Finset.prod_le_prod (fun r hr => abs_nonneg _)
            (fun r hr => hb _ _ _)
    _ = B ^ p := by simp

/-- The real trace of the symmetric array attached to `Y`. -/
noncomputable def rootedTrace (Y : ℕ → ℕ → Ω → ℝ)
    (n p : ℕ) (ω : Ω) : ℝ :=
  Matrix.trace (@npowRec (Matrix (Fin n) (Fin n) ℝ)
    Matrix.one Matrix.instMulOfFintypeOfAddCommMonoid p
      ((fun a b : Fin n => Y (min (a:ℕ) b) (max (a:ℕ) b) ω) :
        Matrix (Fin n) (Fin n) ℝ))

lemma rootedTrace_eq_sum (Y : ℕ → ℕ → Ω → ℝ)
    (n p : ℕ) (ω : Ω) :
    rootedTrace Y n p ω =
      ∑ i : Fin n, ∑ v : (Fin p → Fin n),
        if pathEnd p i v = i then
          pathTerm (fun a b : Fin n =>
            Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v else 0 := by
  classical
  unfold rootedTrace
  let A : Matrix (Fin n) (Fin n) ℝ :=
      (fun a b : Fin n => Y (min (a:ℕ) b) (max (a:ℕ) b) ω)
  change Matrix.trace (@npowRec (Matrix (Fin n) (Fin n) ℝ)
    Matrix.one Matrix.instMulOfFintypeOfAddCommMonoid p A) = _
  change Matrix.trace (A ^ p) = _
  exact (trace_pow_eq_sum_closedPaths A p)


lemma memLp_rootedTrace (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ a b ω, |Y a b ω| ≤ B)
    (n p : ℕ) : MemLp (rootedTrace Y n p) 2 μ := by
  classical
  let T : (Fin n) → (Fin p → Fin n) → Ω → ℝ := fun i v ω =>
    if pathEnd p i v = i then
      pathTerm (fun a b : Fin n =>
        Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p i v else 0
  have mt (i : Fin n) (v : Fin p → Fin n) : MemLp (T i v) 2 μ := by
    by_cases h : pathEnd p i v = i
    · simpa [T, h] using
        (memLp_pathTerm_real_wigner μ Y hm B hB hb n p i v)
    · simpa [T, h] using
        (memLp_const (μ:=μ) (p:=(2:ℝ≥0∞)) (α:=Ω) (c:=(0:ℝ)))
  have ms : MemLp (fun ω => ∑ i : Fin n, ∑ v : (Fin p → Fin n), T i v ω) 2 μ := by
    have A (i : Fin n) : MemLp (fun ω => ∑ v : (Fin p → Fin n), T i v ω) 2 μ := by
      have h := (memLp_finsetSum' (μ:=μ) (p:=(2:ℝ≥0∞))
          (Finset.univ : Finset (Fin p → Fin n)) (fun v hv => mt i v))
      have eqf : (∑ v : (Fin p → Fin n), T i v) =
          (fun ω => ∑ v : (Fin p → Fin n), T i v ω) := by
        ext ω
        simp [Finset.sum_apply]
      rw [eqf] at h
      exact h
    have h := (memLp_finsetSum' (μ:=μ) (p:=(2:ℝ≥0∞))
        (Finset.univ : Finset (Fin n)) (fun i hi => A i))
    have eqf : (∑ i : Fin n, (fun ω => ∑ v : (Fin p → Fin n), T i v ω)) =
          (fun ω => ∑ i : Fin n, ∑ v : (Fin p → Fin n), T i v ω) := by
      ext ω
      simp [Finset.sum_apply]
    rw [eqf] at h
    exact h
  have funext_eq : rootedTrace Y n p =
      (fun ω => ∑ i : Fin n, ∑ v : (Fin p → Fin n), T i v ω) := by
    funext ω
    simpa [T] using (rootedTrace_eq_sum Y n p ω)
  rw [funext_eq]
  exact ms

/-- A trace variance is the finite double sum of the closed path covariances.
This identity keeps the closed indicators explicit. -/
lemma variance_rootedTrace_eq_sum_cov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ a b ω, |Y a b ω| ≤ B)
    (n p : ℕ) :
    Var[rootedTrace Y n p; μ] =
      ∑ i : Fin n, ∑ v : (Fin p → Fin n),
       ∑ j : Fin n, ∑ u : (Fin p → Fin n),
         if pathEnd p i v = i ∧ pathEnd p j u = j then
           ((∫ a, pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
             pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ) -
            (∫ a, pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
            (∫ a, pathTerm (fun b c : Fin n =>
               Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ))
         else 0 := by
  classical
  let T : (Fin n × (Fin p → Fin n)) → Ω → ℝ := fun z ω =>
    if pathEnd p z.1 z.2 = z.1 then
      pathTerm (fun a b : Fin n =>
        Y (min (a:ℕ) b) (max (a:ℕ) b) ω) p z.1 z.2 else 0
  have mt (z : Fin n × (Fin p → Fin n)) : MemLp (T z) 2 μ := by
    rcases z with ⟨i,v⟩
    by_cases h : pathEnd p i v = i
    · simpa [T, h] using
        (memLp_pathTerm_real_wigner μ Y hm B hB hb n p i v)
    · simpa [T, h] using
        (memLp_const (μ:=μ) (p:=(2:ℝ≥0∞)) (α:=Ω) (c:=(0:ℝ)))
  have funext_eq : rootedTrace Y n p =
      (fun ω => ∑ z : (Fin n × (Fin p → Fin n)), T z ω) := by
    funext ω
    rw [rootedTrace_eq_sum]
    rw [Fintype.sum_prod_type]
  rw [funext_eq]
  rw [variance_fun_sum (μ:=μ) mt]
  -- flatten the two product indices
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  -- now the covariance of two closed summands
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro u hu
  by_cases ci : pathEnd p i v = i
  · by_cases cj : pathEnd p j u = j
    · have A := memLp_pathTerm_real_wigner μ Y hm B hB hb n p i v
      have D := memLp_pathTerm_real_wigner μ Y hm B hB hb n p j u
      simpa [T, ci, cj, covariance_eq_sub A D]
        using (covariance_eq_sub (μ:=μ) (mt (i,v)) (mt (j,u)))
    · have zfun : (T (j,u)) = (fun _ : Ω => (0:ℝ)) := by funext x; simp [T,cj]
      simp [T, ci, cj, covariance, zfun]
  · have zfun : (T (i,v)) = (fun _ : Ω => (0:ℝ)) := by funext x; simp [T,ci]
    simp [T, ci, covariance, zfun]
open Filter
variable {α : Type*} [MeasurableSpace α]
/-- Borel--Cantelli consequence of Chebyshev: summable variance quotients force
pointwise convergence to the mean. Keeping the raw quotient avoids a choice of
normalisation in the applications. -/
lemma ae_tendsto_sub_mean_of_summable_variance
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ)
    (hf : ∀ k, MemLp (f k) 2 μ)
    (hs : ∀ ε : ℝ, 0 < ε →
       (∑' k : ℕ,
          ENNReal.ofReal (Var[f k; μ] / ε^2)) ≠ ∞) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun k => f k ω - ∫ x, f k x ∂μ) Filter.atTop (nhds (0:ℝ)) := by
  -- first apply Borel--Cantelli at the thresholds `1/(m+1)`
  have ev (m : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in Filter.atTop,
      ¬ (((m+1:ℕ):ℝ)⁻¹ ≤ |f k ω - ∫ x, f k x ∂μ|) := by
    let ε : ℝ := ((m+1:ℕ):ℝ)⁻¹
    have ep : 0 < ε := by dsimp [ε]; positivity
    have meas (k : ℕ) : μ {ω | ε ≤ |f k ω - ∫ x, f k x ∂μ|} ≤
          ENNReal.ofReal (Var[f k; μ] / ε^2) := by
      exact ProbabilityTheory.meas_ge_le_variance_div_sq (μ:=μ) (hf k) ep
    have tsum : (∑' k : ℕ, μ {ω | ε ≤ |f k ω - ∫ x, f k x ∂μ|}) ≠ ∞ :=
      ne_top_of_le_ne_top (hs ε ep) (ENNReal.tsum_le_tsum meas)
    exact MeasureTheory.ae_eventually_notMem tsum
  have all : ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
      ¬ (((m+1:ℕ):ℝ)⁻¹ ≤ |f k ω - ∫ x, f k x ∂μ|) :=
    MeasureTheory.ae_all_iff.2 ev
  filter_upwards [all] with ω hω
  rw [Metric.tendsto_atTop]
  intro δ hd
  rcases exists_nat_one_div_lt hd with ⟨m, hm⟩
  have eqeps : (1 / ((m:ℝ) + 1)) = (((m+1:ℕ):ℝ)⁻¹) := by
    push_cast
    simp [one_div]
  have lt : (((m+1:ℕ):ℝ)⁻¹) < δ := eqeps ▸ hm
  have evt := hω m
  rcases (eventually_atTop.1 evt) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  have sm := hN k hk
  have aa : |f k ω - ∫ x, f k x ∂μ| < (((m+1:ℕ):ℝ)⁻¹) :=
    lt_of_not_ge sm
  simpa [Real.dist_eq] using (aa.trans lt)
variable {Ω' : Type*} [MeasurableSpace Ω']
open MeasureTheory ProbabilityTheory
lemma variance_rootedTrace_le
    (μ : Measure Ω') [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω' → ℝ)
    (hm : ∀ a b, Measurable (Y a b))
    (hi : iIndepFun
       (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (hz : ∀ a b, a ≤ b → (∫ w, Y a b w ∂μ) = (0:ℝ))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i j ω, |Y i j ω| ≤ B)
    (n p : ℕ) :
    Var[rootedTrace Y n p; μ] ≤
       ((n:ℝ)^p * (p:ℝ)^((p+1)+(p+1))) * (2 * B^(p+p)) := by
  rw [variance_rootedTrace_eq_sum_cov μ Y hm B hB hb n p]
  exact (le_abs_self _).trans
    (abs_sum_cov_closed_le μ Y hm hi hz B hB hb n p)
end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/TraceConc.lean

-- BEGIN INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/TraceLimit.lean
section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
namespace WignerSupport

/-- The normalization for a real trace moment of order `p` in the empirical
matrix `n^{-1/2}Y`.  Keeping the square root (rather than `p/2`) is important
at odd orders: its square is `n^(p+2)`, and the variance estimate is then
summable. -/
noncomputable def traceScale (n p : ℕ) : ℝ :=
  (n:ℝ) * (Real.sqrt (n:ℝ))^p

lemma traceScale_sq (n p : ℕ) :
    (traceScale n p)^2 = (n:ℝ)^2 * (n:ℝ)^p := by
  unfold traceScale
  have hn : (0:ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
  rw [mul_pow]
  rw [show ((Real.sqrt (n:ℝ))^p)^2 =
      (Real.sqrt (n:ℝ))^(p*2) by ring]
  rw [mul_comm p 2, pow_mul, Real.sq_sqrt hn]

lemma traceScale_pos {n p : ℕ} (hn : 0 < n) : 0 < traceScale n p := by
  unfold traceScale
  have h : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 h
  positivity

lemma inv_traceScale_bound (n p : ℕ) (hn : 0 < n) (C : ℝ) :
    ((traceScale n p)⁻¹)^2 * ((n:ℝ)^p * C) = C / (n:ℝ)^2 := by
  have xn : (0:ℝ) < n := by exact_mod_cast hn
  have nz : traceScale n p ≠ 0 := ne_of_gt (traceScale_pos hn)
  have npnz : (n:ℝ)^p ≠ 0 := by positivity
  have hsq := traceScale_sq n p
  rw [inv_pow, hsq]
  field_simp


lemma sqrt_pow_sq_nat (n m : ℕ) :
    ((Real.sqrt (n:ℝ))^m)^2 = (n:ℝ)^m := by
  have hn : (0:ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
  rw [show ((Real.sqrt (n:ℝ))^m)^2 = (Real.sqrt (n:ℝ))^(2*m) by ring]
  rw [pow_mul, Real.sq_sqrt hn]

@[simp] lemma traceScale_even (n m : ℕ) :
    traceScale n (2*m) = (n:ℝ)^(m+1) := by
  unfold traceScale
  rw [show 2*m = m*2 by omega]
  rw [pow_mul, sqrt_pow_sq_nat, pow_succ]
  ring

lemma traceScale_odd (n m : ℕ) :
    traceScale n (2*m+1) = (n:ℝ)^(m+1) * Real.sqrt n := by
  unfold traceScale
  rw [pow_add]
  rw [show ((Real.sqrt (n:ℝ))^(2*m)) =
      ((Real.sqrt (n:ℝ))^m)^2 by ring]
  rw [sqrt_pow_sq_nat, pow_succ]
  ring

lemma integral_rootedTrace_div_const
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → ℕ → Ω → ℝ)
    (n p : ℕ) (c : ℝ) :
    (∫ w, rootedTrace Y n p w / c ∂μ) =
      (∫ w, rootedTrace Y n p w ∂μ) / c := by
  simp only [div_eq_mul_inv]
  rw [MeasureTheory.integral_mul_const]

lemma summable_succ_sq_inv_real :
    Summable (fun k : ℕ => (((k+1:ℕ):ℝ)^2)⁻¹) := by
  have h : Summable (fun k : ℕ => ((k:ℝ)^2)⁻¹) :=
    (Real.summable_nat_pow_inv).2 (by norm_num)
  exact (summable_nat_add_iff
      (f:= (fun k : ℕ => ((k:ℝ)^2)⁻¹)) 1).2 h

/-- A direct Borel--Cantelli corollary for bounded Wigner arrays.  The
normalised trace is compared with its (finite-dimensional) expectation.  It
is useful to keep this as a separate lemma: the square-root normalization at
odd orders is easy to lose if one works only with `p/2`.

This lemma is purely the concentration step.  It says nothing about the
mean, the Catalan computation, or about analytic approximation of a test
function. -/
lemma ae_normalized_rootedTrace_sub_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ℕ → ℕ → Ω → ℝ)
    (hm : ∀ i j, Measurable (Y i j))
    (hi : iIndepFun
       (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ)
    (hz : ∀ a b, a ≤ b → (∫ w, Y a b w ∂μ) = (0:ℝ))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i j ω, |Y i j ω| ≤ B)
    (p : ℕ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun k : ℕ =>
          rootedTrace Y (k+1) p ω / traceScale (k+1) p -
             ∫ x, rootedTrace Y (k+1) p x / traceScale (k+1) p ∂μ)
        atTop (𝓝 (0:ℝ)) := by
  let f : ℕ → Ω → ℝ := fun k ω =>
      rootedTrace Y (k+1) p ω / traceScale (k+1) p
  have hf (k : ℕ) : MemLp (f k) 2 μ := by
    let c : ℝ := (traceScale (k+1) p)⁻¹
    have h := memLp_rootedTrace μ Y hm B hB hb (k+1) p
    have h' := h.const_mul c
    -- write the quotient as a scalar product
    simpa [f, c, div_eq_inv_mul] using h'
  let C : ℝ := ((p:ℝ)^((p+1)+(p+1))) * (2 * B^(p+p))
  have C0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have var_le (k : ℕ) :
      Var[f k; μ] ≤ C / (((k+1:ℕ):ℝ)^2) := by
    let n : ℕ := k+1
    have hn : 0 < n := by dsimp [n]; omega
    have vbound := variance_rootedTrace_le μ Y hm hi hz B hB hb n p
    have vbound' :
        Var[rootedTrace Y n p; μ] ≤ (n:ℝ)^p * C := by
      simpa [C, mul_assoc] using vbound
    -- variance scales exactly under a constant multiplier
    calc
      Var[f k; μ] =
          ((traceScale n p)⁻¹)^2 *
            Var[rootedTrace Y n p; μ] := by
              have h := ProbabilityTheory.variance_const_mul
                 ((traceScale n p)⁻¹) (rootedTrace Y n p) μ
              -- `n=k+1`
              dsimp [f]
              change
                Var[(fun ω => rootedTrace Y n p ω /
                    traceScale n p); μ] = _
              simpa [div_eq_inv_mul] using h
      _ ≤ ((traceScale n p)⁻¹)^2 * ((n:ℝ)^p * C) := by
              exact mul_le_mul_of_nonneg_left vbound'
                (sq_nonneg _)
      _ = C / (((k+1:ℕ):ℝ)^2) := by
              simpa [n] using inv_traceScale_bound n p hn C
  have hs : ∀ ε : ℝ, 0 < ε →
       (∑' k : ℕ, ENNReal.ofReal (Var[f k; μ] / ε^2)) ≠ ∞ := by
    intro ε hε
    let A : ℝ := C / ε^2
    have A0 : 0 ≤ A := by dsimp [A]; positivity
    let g : ℕ → ℝ := fun k => A * (((k+1:ℕ):ℝ)^2)⁻¹
    have g0 (k : ℕ) : 0 ≤ g k := by
      dsimp [g]
      positivity
    have gs : Summable g := by
      dsimp [g]
      exact Summable.mul_left A summable_succ_sq_inv_real
    have gsn : Summable (fun k => (g k).toNNReal) :=
      Summable.toNNReal gs
    have gtop :
        (∑' k : ℕ, ((g k).toNNReal : ENNReal)) ≠ ∞ :=
      ENNReal.tsum_coe_ne_top_iff_summable.mpr gsn
    have point (k : ℕ) :
        ENNReal.ofReal (Var[f k; μ] / ε^2) ≤
          ((g k).toNNReal : ENNReal) := by
      have sqp : 0 < ε^2 := sq_pos_of_pos hε
      have le : Var[f k; μ] / ε^2 ≤ g k := by
        have m := var_le k
        -- all constants are positive; division keeps the inequality
        calc
          Var[f k; μ] / ε^2 ≤ (C / (((k+1:ℕ):ℝ)^2)) / ε^2 :=
            (div_le_div_of_nonneg_right m (le_of_lt sqp))
          _ = g k := by
            dsimp [g, A]
            -- merely a rearrangement of divisions
            ring
      have eqg : ENNReal.ofReal (g k) = ((g k).toNNReal : ENNReal) := by
        rw [ENNReal.ofReal_eq_coe_nnreal (g0 k),
            Real.toNNReal_of_nonneg (g0 k)]
      rw [← eqg]
      exact ENNReal.ofReal_le_ofReal le
    exact ne_top_of_le_ne_top gtop (ENNReal.tsum_le_tsum point)
  exact ae_tendsto_sub_mean_of_summable_variance μ f hf hs

end WignerSupport

end
-- END INLINED FILE: Mathlib/Support/wigner_semicircle_e1c3703c06/TraceLimit.lean

-- BEGIN INLINED MAIN PRELUDE


set_option maxHeartbeats 1200000


open LeanEval.Analysis.WignerSemicircleProblem
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

open scoped BigOperators

/-- The elementary normalization integral for the density in `semicircleLaw`.
    We keep this real-valued function separate while doing the calculation; the
    definition of the law uses its `ENNReal.ofReal`. -/
private noncomputable def semicircleDensityReal (x : ℝ) : ℝ :=
  Real.sqrt (4 - x^2) / (2 * Real.pi)

private lemma semicircleDensityReal_continuous :
    Continuous semicircleDensityReal := by
  unfold semicircleDensityReal
  fun_prop

private lemma semicircleDensityReal_nonneg (x : ℝ) :
    0 ≤ semicircleDensityReal x := by
  unfold semicircleDensityReal
  positivity

private lemma semicircleDensityReal_two (x : ℝ) :
    semicircleDensityReal (2*x) = Real.sqrt (1-x^2) / Real.pi := by
  unfold semicircleDensityReal
  rw [show (4 - (2*x)^2) = 4 * (1 - x^2) by ring]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show Real.sqrt (4:ℝ) = 2 by norm_num]
  ring

private lemma semicircleDensityReal_integral :
    (∫ x in (-2 : ℝ)..2, semicircleDensityReal x) = 1 := by
  have hcomp := intervalIntegral.integral_comp_mul_left
    (f := semicircleDensityReal) (a := (-1 : ℝ)) (b := 1) (c := 2)
      (by norm_num : (2 : ℝ) ≠ 0)
  simp [semicircleDensityReal_two] at hcomp
  rw [integral_sqrt_one_sub_sq] at hcomp
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold semicircleDensityReal at hcomp ⊢
  rw [intervalIntegral.integral_div] at hcomp ⊢
  field_simp [hp] at hcomp ⊢
  linarith

private lemma semicircleDensityReal_integrable :
    Integrable semicircleDensityReal
      (volume.restrict (Set.Icc (-2 : ℝ) 2)) := by
  exact semicircleDensityReal_continuous.continuousOn.integrableOn_Icc

private lemma semicircleLaw_apply_univ : semicircleLaw Set.univ = 1 := by
  -- `withDensity` is defined by a lintegral; reducing it to a real integral
  -- avoids any change-of-density or finiteness assumptions.
  change ((volume.restrict (Set.Icc (-2 : ℝ) 2)).withDensity
    (fun x => ENNReal.ofReal (semicircleDensityReal x))) Set.univ = 1
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  rw [Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    semicircleDensityReal_integrable
      (ae_of_all _ semicircleDensityReal_nonneg)]
  have hset : (∫ x in Set.Icc (-2 : ℝ) 2,
      semicircleDensityReal x) = 1 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
    exact semicircleDensityReal_integral
  rw [hset]
  norm_num

noncomputable instance semicircleLaw_isProbabilityMeasure :
    IsProbabilityMeasure semicircleLaw := ⟨semicircleLaw_apply_univ⟩

/-- All nonempty empirical spectral measures have mass one.  The empty
index type is the sole exception and never affects an `atTop` limit. -/
lemma empiricalSpectralMeasureHerm_apply_univ
    {n : ℕ} {W : Matrix (Fin n) (Fin n) ℂ} (hW : W.IsHermitian) :
    empiricalSpectralMeasureHerm hW Set.univ =
      (n : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞) := by
  rw [empiricalSpectralMeasureHerm, Measure.smul_apply]
  simp [Finset.sum_apply]

noncomputable instance empiricalSpectralMeasureHerm_isProbabilityMeasure
    {n : ℕ} [NeZero n] {W : Matrix (Fin n) (Fin n) ℂ}
    (hW : W.IsHermitian) :
    IsProbabilityMeasure (empiricalSpectralMeasureHerm hW) := by
  refine ⟨?_⟩
  rw [empiricalSpectralMeasureHerm_apply_univ hW]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (NeZero.ne n))
    (ENNReal.natCast_ne_top n)


/-- To use the library weak-topology the empirical measures are packaged as
probability measures.  We drop the empty `0 × 0` matrix by indexing with
`k+1`; this also avoids a spurious zero mass at the beginning of a sequence. -/
noncomputable def wignerEmpiricalProbability {Ω : Type*}
    (X : ℕ → ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) :
    ProbabilityMeasure ℝ := by
  let n : ℕ := k + 1
  letI : NeZero n := ⟨by omega⟩
  let h := wignerMatrix_isHermitian X n ω
  exact ⟨(empiricalSpectralMeasureHerm h).map
      (fun x : ℝ => x / Real.sqrt n),
    @MeasureTheory.Measure.isProbabilityMeasure_map _ _ _ _
      (empiricalSpectralMeasureHerm h)
      (empiricalSpectralMeasureHerm_isProbabilityMeasure h)
      (fun x : ℝ => x / Real.sqrt n) (by fun_prop)⟩

@[simp]
lemma wignerEmpiricalProbability_apply {Ω : Type*}
    (X : ℕ → ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) :
    ((wignerEmpiricalProbability X ω k : ProbabilityMeasure ℝ) : Measure ℝ) =
      (empiricalSpectralMeasureHerm
        (wignerMatrix_isHermitian X (k+1) ω)).map
          (fun x : ℝ => x / Real.sqrt (k+1)) := by
  classical
  simp [wignerEmpiricalProbability]

/-- A purely finite-dimensional identity: integration against the push-forward of the
    empirical measure is the arithmetic mean over the eigenvalues.  No
    probability is involved here.  Stating this for `n = 0` as well is useful;
    in that case both sides are zero. -/
lemma empiricalSpectralMeasureHerm_integral_map
    {n : ℕ} {W : Matrix (Fin n) (Fin n) ℂ} (hW : W.IsHermitian)
    (T : ℝ → ℝ) (hT : Measurable T) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂ (empiricalSpectralMeasureHerm hW).map T) =
      (n : ℝ)⁻¹ * ∑ j : Fin n, f (T (hW.eigenvalues j)) := by
  rw [MeasureTheory.integral_map hT.aemeasurable hf.aestronglyMeasurable]
  dsimp [empiricalSpectralMeasureHerm]
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_finsetSum_measure]
  · simp
  · intro i hi
    refine MeasureTheory.integrable_dirac ?_
    simp


lemma empiricalSpectralMeasureHerm_integral_map_complex
    {n : ℕ} {W : Matrix (Fin n) (Fin n) ℂ} (hW : W.IsHermitian)
    (T : ℝ → ℝ) (hT : Measurable T) (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ x, f x ∂ (empiricalSpectralMeasureHerm hW).map T) =
      (n : ℝ)⁻¹ • ∑ j : Fin n, f (T (hW.eigenvalues j)) := by
  rw [MeasureTheory.integral_map hT.aemeasurable hf.aestronglyMeasurable]
  dsimp [empiricalSpectralMeasureHerm]
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_finsetSum_measure]
  · simp
  · intro i hi
    refine MeasureTheory.integrable_dirac ?_
    simp

lemma wignerEmpiricalProbability_charFun {Ω : Type*}
    (X : ℕ → ℕ → Ω → ℝ) (ω : Ω) (k : ℕ) (t : ℝ) :
    MeasureTheory.charFun
       (wignerEmpiricalProbability X ω k : Measure ℝ) t =
      ((k+1 : ℕ) : ℝ)⁻¹ •
        (∑ j : Fin (k+1),
          Complex.exp
            (((((wignerMatrix_isHermitian X (k+1) ω).eigenvalues j /
                  Real.sqrt (k+1)) * t : ℝ) : ℂ) * Complex.I)) := by
  rw [wignerEmpiricalProbability_apply]
  rw [MeasureTheory.charFun_apply]
  convert empiricalSpectralMeasureHerm_integral_map_complex
      (wignerMatrix_isHermitian X (k+1) ω)
      (fun x : ℝ => x / Real.sqrt (k+1)) (by fun_prop)
      (fun x : ℝ =>
        Complex.exp ((((t * x : ℝ) : ℂ)) * Complex.I))
      (by fun_prop) using 1 <;> simp [mul_comm]

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem wigner_semicircle {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ)
    (_hX_meas : ∀ i j, Measurable (X i j))
    (_hX_indep : iIndepFun
      (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} => X ij.val.1 ij.val.2) μ)
    (_hX_iid : ∀ i j i' j', i ≤ j → i' ≤ j' →
      ProbabilityTheory.IdentDistrib (X i j) (X i' j') μ μ)
    (_hX_int : ∀ i j, i ≤ j → Integrable (X i j) μ)
    (_hX_sq_int : ∀ i j, i ≤ j → Integrable (fun ω => (X i j ω) ^ 2) μ)
    (_hX_mean : ∀ i j, i ≤ j → ∫ ω, X i j ω ∂μ = 0)
    (_hX_var : ∀ i j, i ≤ j → ∫ ω, (X i j ω) ^ 2 ∂μ = 1) :
    ∀ᵐ ω ∂μ,
      ∀ (f : ℝ → ℝ), Continuous f → (∃ M, ∀ x, ‖f x‖ ≤ M) →
        Tendsto
          (fun n : ℕ =>
            ∫ x, f x ∂ (empiricalSpectralMeasureHerm
              (wignerMatrix_isHermitian X n ω)).map
                (fun x : ℝ => x / Real.sqrt n))
          atTop (𝓝 (∫ x, f x ∂semicircleLaw)) :=
/-ResultProofBegin-/ by
  -- The maps in the statement are only push-forwards of finite empirical
  -- measures.  Removing this layer is an exact elementary reduction.  What
  -- remains is the probabilistic Wigner theorem for the averages of the
  -- eigenvalues themselves.
  let ν₀ : ProbabilityMeasure ℝ :=
    ⟨semicircleLaw, semicircleLaw_isProbabilityMeasure⟩
  -- At this point the remaining genuinely probabilistic step can be expressed
  -- by characteristic functions.  Everything after this assertion is the
  -- Levy convergence theorem and the bookkeeping of empirical sums.
  have hexponential :
      ∀ᵐ ω ∂μ, ∀ t : ℝ,
        Tendsto
          (fun k : ℕ =>
            ((k+1 : ℕ) : ℝ)⁻¹ •
              (∑ j : Fin (k+1),
                Complex.exp
                  (((((wignerMatrix_isHermitian X (k+1) ω).eigenvalues j /
                        Real.sqrt (k+1)) * t : ℝ) : ℂ) * Complex.I)))
          atTop
          (𝓝 (MeasureTheory.charFun (semicircleLaw) t)) := by
    -- The value `t = 0` is deterministic (it is only the total mass of the
    -- empirical measure).  Isolating it is convenient in any characteristic-
    -- function proof; the analytic/probabilistic assertion needed below is at
    -- nonzero frequencies.
    have hnz :
        ∀ᵐ ω ∂μ, ∀ t : ℝ, t ≠ 0 →
          Tendsto
            (fun k : ℕ =>
              ((k+1 : ℕ) : ℝ)⁻¹ •
                (∑ j : Fin (k+1),
                  Complex.exp
                    (((((wignerMatrix_isHermitian X (k+1) ω).eigenvalues j /
                          Real.sqrt (k+1)) * t : ℝ) : ℂ) * Complex.I)))
            atTop
            (𝓝 (MeasureTheory.charFun (semicircleLaw) t)) := by
      -- Active probabilistic core left after enumeration: convergence at rational
      -- frequencies.  The passage from this countable assertion to all real
      -- frequencies is now supplied below by a genuine uniform moment bound.
      let P : Ω → ℚ → Prop := fun ω q =>
            Tendsto
              (fun k : ℕ =>
                ((k+1 : ℕ) : ℝ)⁻¹ •
                  (∑ j : Fin (k+1),
                    Complex.exp
                      (((((wignerMatrix_isHermitian X (k+1) ω).eigenvalues j /
                            Real.sqrt (k+1)) * (q:ℝ) : ℝ) : ℂ) * Complex.I)))
              atTop (𝓝 (MeasureTheory.charFun (semicircleLaw) (q:ℝ)))
      have hfixed : ∀ q : ℚ, q ≠ 0 → ∀ᵐ ω ∂μ, P ω q := by
        -- A useful first finite-variance reduction is rigorous: every hard
        -- cutoff of the entries has an a.s. strong law for its discarded
        -- Hilbert--Schmidt mass.  The dominated-convergence lemma in `Tail`
        -- also says that these deterministic means tend to zero.
        have htailall : ∀ᵐ ω ∂μ, ∀ R : ℕ,
            Tendsto
              (fun m : ℕ =>
                 (∑ r ∈ Finset.range m,
                    WignerSupport.upperSqSeq
                       (WignerSupport.tailX (R:ℝ) X) r ω) / (m:ℝ))
              atTop
              (𝓝 (WignerSupport.tailMean μ X (R:ℝ))) := by
          rw [MeasureTheory.ae_all_iff]
          intro R
          exact WignerSupport.tailSqSeq_strongLaw μ X (R:ℝ)
            _hX_indep _hX_meas _hX_iid _hX_sq_int
        have htailzero : Tendsto
            (fun R : ℕ => WignerSupport.tailMean μ X (R:ℝ))
            atTop (𝓝 (0:ℝ)) :=
          WignerSupport.tailMean_tendsto_zero μ X (_hX_meas 0 0)
              (_hX_sq_int 0 0 (by omega))
        intro q hq
        -- At a fixed cutoff all entries have all moments.  The sole
        -- stochastic assertion which is still needed is the bounded iid
        -- Wigner theorem.  It is stated here with its *correct* variance:
        -- hard cutting is neither centered nor normalized.  A possible
        -- nonzero mean is only the harmless rank-one constant matrix, while
        -- the bulk radius is the variance below.
        have hbounded : ∀ᵐ ω ∂μ, ∀ R : ℕ,
            Tendsto
              (fun k : ℕ =>
                WignerSupport.eigenChar
                  (wignerMatrix_isHermitian
                     (WignerSupport.centeredCut μ (R:ℝ) X) (k+1) ω) (q:ℝ))
              atTop
              (𝓝 (MeasureTheory.charFun semicircleLaw
                 (Real.sqrt (WignerSupport.cutVariance μ X (R:ℝ)) *
                    (q:ℝ)))) := by
          -- It remains a fixed positive cutoff -- there is no hidden
          -- uncountable intersection here.  Record all the hypotheses for
          -- that core explicitly, since centering a hard cut is a delicate
          -- point with finite second moments.
          rw [MeasureTheory.ae_all_iff]
          intro R
          have R0 : 0 ≤ (R:ℝ) := by exact_mod_cast (Nat.zero_le R)
          let Y : ℕ → ℕ → Ω → ℝ := WignerSupport.centeredCut μ (R:ℝ) X
          have Ym : ∀ i j, Measurable (Y i j) :=
            WignerSupport.centeredCut_measurable μ (R:ℝ) X _hX_meas
          have Yb : ∀ i j ω, |Y i j ω| ≤
                (R:ℝ) + |WignerSupport.cutMean μ X (R:ℝ)| :=
            WignerSupport.centeredCut_bound μ R0 X
          have Yi : iIndepFun
              (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} =>
                Y ij.val.1 ij.val.2) μ :=
            WignerSupport.centeredCut_indep μ (R:ℝ) X _hX_indep
          have Yid : ∀ i j i' j', i ≤ j → i' ≤ j' →
              IdentDistrib (Y i j) (Y i' j') μ μ :=
            WignerSupport.centeredCut_ident μ (R:ℝ) X _hX_iid
          have Ypow : ∀ i j m : ℕ,
              Integrable (fun a => (Y i j a)^m) μ :=
            WignerSupport.centeredCut_pow_integrable μ (R:ℝ) R0 X _hX_meas
          have Ymean : ∀ i j, i ≤ j →
              ∫ a, Y i j a ∂μ = 0 :=
            WignerSupport.centeredCut_mean_zero μ (R:ℝ) R0 X
              _hX_meas _hX_int _hX_iid
          have Yvar : ∀ i j, i ≤ j →
              ∫ a, (Y i j a)^2 ∂μ = WignerSupport.cutVariance μ X (R:ℝ) :=
            WignerSupport.centeredCut_second μ (R:ℝ) R0 X
              _hX_meas _hX_int (_hX_sq_int 0 0 (by omega)) _hX_iid
          change ∀ᵐ ω ∂μ,
            Tendsto
              (fun k : ℕ => WignerSupport.eigenChar
                  (wignerMatrix_isHermitian Y (k+1) ω) (q:ℝ))
              atTop
              (𝓝 (MeasureTheory.charFun semicircleLaw
                (Real.sqrt (WignerSupport.cutVariance μ X (R:ℝ)) * (q:ℝ))))
          -- Strip the first genuinely probabilistic step off the moment argument.
          -- The path convention here keeps a root and `p` subsequent vertices.  In
          -- particular the formula is valid at `p=0`, something which is easy to
          -- lose when writing cyclic tuples.  Independence really is indexed by
          -- unordered upper-triangular edges; reversing an edge does not create a
          -- new random variable.
          have Yedge : iIndepFun
              (fun e : {z : ℕ × ℕ // z.1 ≤ z.2} => Y e.val.1 e.val.2) μ := Yi
          have Yzero : ∀ a b, a ≤ b →
              (∫ w, Y a b w ∂μ) = (0:ℝ) := Ymean
          have hwalkzero (n p : ℕ) (i : Fin n)
              (v : Fin p → Fin n) (u : Fin p)
              (hu : ∀ r, WignerSupport.pathEdgesNat i v r =
                    WignerSupport.pathEdgesNat i v u → r = u) :
              (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                    Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ) = 0 := by
            exact WignerSupport.integral_pathTerm_zero_of_unique_edge
              μ Y Ym Yedge Yzero n p i v u hu
          have hprune (n p : ℕ) (i : Fin n)
              (v : Fin p → Fin n)
              (hv : ¬ (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                 WignerSupport.pathEdgesNat i v r =
                   WignerSupport.pathEdgesNat i v u)) :
              (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                 Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ) = 0 := by
            classical
            push_neg at hv
            rcases hv with ⟨u, hu⟩
            apply hwalkzero n p i v u
            intro r he
            by_contra ne
            exact hu r ne he
          have hpath (n p : ℕ) (w : Ω) :
              let A : Matrix (Fin n) (Fin n) ℝ :=
                fun a b => Y (min (a:ℕ) b) (max (a:ℕ) b) w
              Matrix.trace (A^p) =
                ∑ i : Fin n, ∑ v : (Fin p → Fin n),
                  if WignerSupport.pathEnd p i v = i then
                    WignerSupport.pathTerm A p i v else 0 := by
            dsimp
            exact WignerSupport.trace_pow_eq_sum_closedPaths _ _
          have hprunesum (n p : ℕ) :
              (∑ i : Fin n, ∑ v : (Fin p → Fin n),
                if WignerSupport.pathEnd p i v = i then
                  (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                    Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ) else 0) =
              (∑ i : Fin n, ∑ v : (Fin p → Fin n),
                if WignerSupport.pathEnd p i v = i then
                  if (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                       WignerSupport.pathEdgesNat i v r =
                         WignerSupport.pathEdgesNat i v u) then
                    (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                      Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                  else 0 else 0) := by
            classical
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro v hv
            by_cases close : WignerSupport.pathEnd p i v = i
            · simp only [close, if_true]
              by_cases rep : (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                       WignerSupport.pathEdgesNat i v r =
                         WignerSupport.pathEdgesNat i v u)
              · simp [rep]
              · simp [rep, hprune n p i v rep]
            · simp [close]
          have hdiag (n p : ℕ) (w : Ω) :
              ∑ i : Fin n,
                 (((wignerMatrix_isHermitian Y n w).eigenvalues i : ℂ)^p) =
                 Matrix.trace ((wignerMatrix Y n w)^p) := by
            exact WignerSupport.hermitian_sum_pow_eigen _ _ _
          have htermint (n p : ℕ) (i : Fin n) (v : Fin p → Fin n) :
              Integrable (fun w => WignerSupport.pathTerm (fun a b : Fin n =>
                Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v) μ := by
            exact WignerSupport.integrable_pathTerm_real_wigner μ Y Ym
              ((R:ℝ) + |WignerSupport.cutMean μ X (R:ℝ)|) (by positivity)
              Yb n p i v
          -- The elementary graph bound behind the first power count is worth stating
          -- precisely: the image of a repeated edge list has at most `p/2`
          -- elements, and a connected list walk has at most one more vertex.
          -- In particular all repeated closed walks use at most `p/2+1`
          -- labels.  This is a *label* statement, not an enumeration estimate.
          have hvertices (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
              (rep : ∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                WignerSupport.pathEdgesNat i v r =
                  WignerSupport.pathEdgesNat i v u) :
              (WignerSupport.pathVerticesFin i v).card ≤ p/2 + 1 := by
            exact WignerSupport.card_pathVertices_le_half_add_one i v rep
          have hlabeltuple (n p : ℕ) (i : Fin n) (v : Fin p → Fin n) :
              WignerSupport.pathVerticesFin i v =
                (Finset.univ : Finset (Fin (p+1))).image
                  (fun r =>
                    (@Fin.cons p (fun _ => Fin n) i v r).val) := by
            exact WignerSupport.pathVertices_eq_image_cons i v
          have hedge (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
              (rep : ∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                WignerSupport.pathEdgesNat i v r =
                  WignerSupport.pathEdgesNat i v u) :
              (Finset.univ.image (WignerSupport.pathEdgesNat i v)).card ≤ p/2 := by
            exact WignerSupport.card_image_pathEdges_le_half i v rep
          -- All expectations of path monomials factor *by distinct edges*, rather
          -- than by positions in the walk.  This is often the missing distinction
          -- when using `iIndepFun` on a cyclic tuple with repeated edges.
          have hedgemean (n p : ℕ) (i : Fin n) (v : Fin p → Fin n) :
              (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                    Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ) =
                ∏ e ∈ (Finset.univ.image (WignerSupport.pathEdgesNat i v)),
                  (∫ w, (Y e.val.1 e.val.2 w) ^
                    ((Finset.univ : Finset (Fin p)).filter
                      (fun r => WignerSupport.pathEdgesNat i v r = e)).card ∂μ) := by
            exact WignerSupport.integral_pathTerm_eq_prod_edges μ Y Ym Yedge n p i v
          -- Equality in the label bound forces all edge fibers to be pairs;
          -- on these leading walks the preceding product is simply `variance^#edges`.
          have hleading (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
              (heven : 2 ∣ p)
              (rep : ∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                WignerSupport.pathEdgesNat i v r =
                  WignerSupport.pathEdgesNat i v u)
              (hcard : (WignerSupport.pathVerticesFin i v).card = p/2 + 1) :
              (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                    Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ) =
                (WignerSupport.cutVariance μ X (R:ℝ)) ^
                  (Finset.univ.image (WignerSupport.pathEdgesNat i v)).card := by
            have htwo := WignerSupport.fibers_two_of_max_vertices i v heven rep hcard
            exact WignerSupport.integral_pathTerm_of_fiber_two
              μ Y Ym Yedge (WignerSupport.cutVariance μ X (R:ℝ)) Yvar
              n p i v htwo
          -- finite Fubini for the rooted expansion.  Its integrability is not
          -- automatic for an arbitrary tuple; it uses the bounded-cut estimate.
          let Ap : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℝ :=
            fun n w a b => Y (min (a:ℕ) b) (max (a:ℕ) b) w
          have htraceint (n p : ℕ) :
              (∫ w, Matrix.trace
                ((Ap n w)^p)
                   ∂μ) =
                ∑ i : Fin n, ∑ v : (Fin p → Fin n),
                  if WignerSupport.pathEnd p i v = i then
                    (∫ w, WignerSupport.pathTerm
                      (fun a b : Fin n =>
                        Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                  else 0 := by
            classical
            let T : (Fin n) → (Fin p → Fin n) → Ω → ℝ := fun i v w =>
              if WignerSupport.pathEnd p i v = i then
                WignerSupport.pathTerm
                  (fun a b : Fin n =>
                    Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v
              else 0
            have tInt (i : Fin n) (v : Fin p → Fin n) :
                Integrable (T i v) μ := by
              by_cases h : WignerSupport.pathEnd p i v = i
              · simpa [T, h] using htermint n p i v
              · simp [T, h]
            calc
              (∫ w, Matrix.trace
                ((Ap n w)^p)
                   ∂μ) =
                  ∫ w, ∑ i : Fin n, ∑ v : (Fin p → Fin n), T i v w ∂μ := by
                    congr 1
                    funext w
                    simpa [T, Ap] using (hpath n p w)
              _ = ∑ i : Fin n, ∑ v : (Fin p → Fin n),
                    ∫ w, T i v w ∂μ := by
                  rw [MeasureTheory.integral_finset_sum]
                  · apply Finset.sum_congr rfl
                    intro i hi
                    rw [MeasureTheory.integral_finset_sum]
                    intro v hv
                    exact tInt i v
                  · intro i hi
                    exact MeasureTheory.integrable_finset_sum _
                        (fun v hv => tInt i v)
              _ = _ := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro v hv
                by_cases h : WignerSupport.pathEnd p i v = i
                · simp [T, h]
                · simp [T, h]
          -- Thus the expected trace can be written with no singleton-edge
          -- summands at all.  This rewrites `hprunesum` at the level of an
          -- actual (integrable) trace rather than a formal tuple.
          have htracepruned (n p : ℕ) :
              (∫ w, Matrix.trace ((Ap n w)^p) ∂μ) =
                (∑ i : Fin n, ∑ v : (Fin p → Fin n),
                  if WignerSupport.pathEnd p i v = i then
                    if (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                         WignerSupport.pathEdgesNat i v r =
                           WignerSupport.pathEdgesNat i v u) then
                      (∫ w, WignerSupport.pathTerm
                        (fun a b : Fin n =>
                          Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                    else 0 else 0) := by
            calc
              (∫ w, Matrix.trace ((Ap n w)^p) ∂μ) =
                (∑ i : Fin n, ∑ v : (Fin p → Fin n),
                  if WignerSupport.pathEnd p i v = i then
                    (∫ w, WignerSupport.pathTerm
                      (fun a b : Fin n =>
                        Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                  else 0) := htraceint n p
              _ = _ := hprunesum n p
          -- In the rooted trace expansion `hpath`, `hwalkzero` removes *all*
          -- tuples with a singleton edge before any estimate.  Subsequent terms
          -- therefore use at most `p/2` distinct edges.  The unresolved bounded
          -- case is now the enumeration/variance argument for those repeated-edge
          -- rooted paths (the Catalan, non-crossing shapes give the main term) and
          -- its a.s. upgrade; no independence lemma for individual monomials is
          -- being silently assumed.  The graph/fiber lemmas above isolate the
          -- equality case (variance factors) but do not yet count its rooted
          -- equality patterns: that is the noncrossing-tree/Catalan step,
          -- followed by the variance estimate for sums of bounded monomials.
          by_cases rz : R = 0
          · subst R
            have zmat (n : ℕ) (w : Ω) : wignerMatrix Y n w = 0 := by
              ext i j
              simp [wignerMatrix, Y, WignerSupport.centeredCut_zero]
            have zeig (n : ℕ) (w : Ω) (j : Fin n) :
                (wignerMatrix_isHermitian Y n w).eigenvalues j = 0 := by
              let h := wignerMatrix_isHermitian Y n w
              have hv := h.mulVec_eigenvectorBasis j
              have leftzero :
                  Matrix.mulVec (wignerMatrix Y n w) (⇑(h.eigenvectorBasis j)) = 0 := by
                simp [zmat]
              have se : (h.eigenvalues j) •
                    ⇑(h.eigenvectorBasis j) = 0 := hv.symm.trans leftzero
              have pair : ((h.eigenvalues j) = 0) ∨
                  (((h.eigenvectorBasis j : EuclideanSpace ℂ (Fin n)) :
                      (Fin n → ℂ)) = 0) := by
                exact smul_eq_zero.mp se
              rcases pair with hz | hz
              · exact hz
              · have no : (((h.eigenvectorBasis j : EuclideanSpace ℂ (Fin n)) :
                          (Fin n → ℂ))) ≠ 0 := by
                    intro hfun
                    have hlp : (h.eigenvectorBasis j :
                          EuclideanSpace ℂ (Fin n)) = 0 := by
                      apply PiLp.ext (fun t => ?_)
                      exact congrFun hfun t
                    have one := h.eigenvectorBasis.norm_eq_one j
                    rw [hlp, norm_zero] at one
                    norm_num at one
                exact False.elim (no hz)
            -- the pointwise limit is already the constant characteristic
            -- function `1`; the zero-size matrix is not used here (`k+1`).
            filter_upwards [] with w
            have left :
              (fun k : ℕ => WignerSupport.eigenChar
                    (wignerMatrix_isHermitian Y (k+1) w) (q:ℝ)) =
                 (fun _k : ℕ => (1:ℂ)) := by
              funext k
              simp [WignerSupport.eigenChar, zeig]
              have hn : ((k:ℝ)+1) ≠ 0 := by
                exact_mod_cast (Nat.succ_ne_zero k)
              field_simp
            rw [left]
            have target :
                MeasureTheory.charFun semicircleLaw
                   (Real.sqrt (WignerSupport.cutVariance μ X 0) * (q:ℝ)) =
                  (1:ℂ) := by
                simp [WignerSupport.cutVariance_zero]
            convert (tendsto_const_nhds :
              Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 (1:ℂ))) using 1
            simpa using target
          ·
            -- Positive cutoffs are the genuinely bounded moment problem.
            -- For later power counts it is important that the remaining
            -- rooted walks occupy only `p/2+1` labels.  The following uniform
            -- inequalities are now packaged without a hidden `n^(p+1)`.
            let B : ℝ := (R:ℝ) + |WignerSupport.cutMean μ X (R:ℝ)|
            have B0 : 0 ≤ B := by dsimp [B]; positivity
            have termbd (n p : ℕ) (i : Fin n) (v : Fin p → Fin n) :
                |(∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                    Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)| ≤ B^p := by
              exact WignerSupport.abs_integral_pathTerm_le μ Y B B0 Yb n p i v
            have labelcnt (n p : ℕ) :
                ((Finset.univ : Finset (Fin n × (Fin p → Fin n))).filter
                  (fun z => (WignerSupport.pathVerticesFin z.1 z.2).card ≤
                    p/2 + 1)).card ≤ n^(p/2+1) * (p/2+1)^(p+1) := by
              exact WignerSupport.card_filter_small_path_vertices
                (n:=n) (p:=p) (d:=p/2+1)
            -- A convenient consequence for the pruned trace: no matter what
            -- the labels are, it is bounded by the above power.  This is the
            -- first estimate that actually loses a power of `n`; replacing it
            -- by `n^(p+1)` makes the moment method circular.
            have traceBound (n p : ℕ) :
                |∫ w, Matrix.trace ((Ap n w)^p) ∂μ| ≤
                  (n:ℝ)^(p/2+1) * ((p/2+1:ℕ):ℝ)^(p+1) * B^p := by
              classical
              rw [htracepruned]
              let S : Finset (Fin n × (Fin p → Fin n)) :=
                Finset.univ.filter
                  (fun z => (WignerSupport.pathVerticesFin z.1 z.2).card ≤ p/2+1)
              let val : Fin n → (Fin p → Fin n) → ℝ := fun i v =>
                ∫ w, WignerSupport.pathTerm
                     (fun a b : Fin n =>
                          Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ
              let T : Fin n → (Fin p → Fin n) → ℝ := fun i v =>
                if WignerSupport.pathEnd p i v = i then
                  if (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                        WignerSupport.pathEdgesNat i v r =
                          WignerSupport.pathEdgesNat i v u)
                  then val i v else 0 else 0
              have point (i : Fin n) (v : Fin p → Fin n) :
                  |T i v| ≤ B^p := by
                dsimp [T]
                split_ifs
                · exact termbd n p i v
                · simpa using (pow_nonneg B0 p)
                · simpa using (pow_nonneg B0 p)
              have outside (i : Fin n) (v : Fin p → Fin n)
                    (hi : (i,v) ∉ S) : T i v = 0 := by
                dsimp [S] at hi
                simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    not_le] at hi
                dsimp [T]
                by_cases c : WignerSupport.pathEnd p i v = i
                · simp only [c, if_true]
                  by_cases rep : (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                        WignerSupport.pathEdgesNat i v r =
                          WignerSupport.pathEdgesNat i v u)
                  · have le := hvertices n p i v rep
                    omega
                  · simp [rep]
                · simp [c]
              have collapse :
                  (∑ i : Fin n, ∑ v : (Fin p → Fin n), T i v) =
                    ∑ z ∈ S, T z.1 z.2 := by
                classical
                -- zero extension of a restricted finite sum
                calc
                  (∑ i : Fin n, ∑ v : (Fin p → Fin n), T i v) =
                      ∑ z : (Fin n × (Fin p → Fin n)), T z.1 z.2 := by
                        rw [Fintype.sum_prod_type]
                  _ = ∑ z ∈ S, T z.1 z.2 := by
                        symm
                        apply Finset.sum_subset (by intro _ h; simp)
                        intro z hz hzall
                        have out : z ∉ S := hzall
                        exact (outside z.1 z.2 out)
              change |∑ i : Fin n, ∑ v : (Fin p → Fin n),
                (if WignerSupport.pathEnd p i v = i then
                    if (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                         WignerSupport.pathEdgesNat i v r =
                           WignerSupport.pathEdgesNat i v u) then
                      (∫ w, WignerSupport.pathTerm
                        (fun a b : Fin n =>
                          Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                    else 0 else 0)| ≤ _
              change |∑ i : Fin n, ∑ v : (Fin p → Fin n), T i v| ≤ _
              rw [collapse]
              calc
                |∑ z ∈ S, T z.1 z.2| ≤
                    ∑ z ∈ S, |T z.1 z.2| := by
                      exact Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ _z ∈ S, B^p := by
                      exact Finset.sum_le_sum (fun z hz => point z.1 z.2)
                _ = (S.card:ℝ) * B^p := by simp
                _ ≤ ((n^(p/2+1) * (p/2+1)^(p+1) : ℕ):ℝ) * B^p := by
                      gcongr
                      dsimp [S]
                      exact_mod_cast labelcnt n p
                _ = (n:ℝ)^(p/2+1) * ((p/2+1:ℕ):ℝ)^(p+1) * B^p := by
                      push_cast
                      ring
            -- and the strict part of the vertex bound is genuinely lower order.
            -- Only the equality shapes (closed trees whose edges are paired)
            -- survive after dividing an even `p` trace by `n^(p/2+1)`.
            have strictBound (n p : ℕ) :
                |∑ i : Fin n, ∑ v : (Fin p → Fin n),
                  if WignerSupport.pathEnd p i v = i then
                    if (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                        WignerSupport.pathEdgesNat i v r =
                          WignerSupport.pathEdgesNat i v u) then
                      if (WignerSupport.pathVerticesFin i v).card < p/2+1
                      then (∫ w, WignerSupport.pathTerm
                        (fun a b : Fin n =>
                          Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                      else 0
                    else 0 else 0| ≤
                    (n:ℝ)^(p/2) * ((p/2:ℕ):ℝ)^(p+1) * B^p := by
              classical
              let S : Finset (Fin n × (Fin p → Fin n)) :=
                Finset.univ.filter
                  (fun z => (WignerSupport.pathVerticesFin z.1 z.2).card ≤ p/2)
              let val : Fin n → (Fin p → Fin n) → ℝ := fun i v =>
                ∫ w, WignerSupport.pathTerm
                     (fun a b : Fin n =>
                          Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ
              let T : Fin n → (Fin p → Fin n) → ℝ := fun i v =>
                if WignerSupport.pathEnd p i v = i then
                  if (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                        WignerSupport.pathEdgesNat i v r =
                          WignerSupport.pathEdgesNat i v u) then
                    if (WignerSupport.pathVerticesFin i v).card < p/2+1
                    then val i v else 0 else 0 else 0
              have point (i : Fin n) (v : Fin p → Fin n) :
                  |T i v| ≤ B^p := by
                dsimp [T]
                split_ifs
                · exact termbd n p i v
                all_goals simpa using (pow_nonneg B0 p)
              have outside (i : Fin n) (v : Fin p → Fin n)
                    (hi : (i,v) ∉ S) : T i v = 0 := by
                dsimp [S] at hi
                simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    not_le] at hi
                dsimp [T]
                by_cases c : WignerSupport.pathEnd p i v = i
                · simp only [c, if_true]
                  by_cases rep : (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                        WignerSupport.pathEdgesNat i v r =
                          WignerSupport.pathEdgesNat i v u)
                  · simp only [rep, if_true]
                    have bad : ¬ (WignerSupport.pathVerticesFin i v).card <
                        p/2 + 1 := by omega
                    simp [bad]
                  · simp [rep]
                · simp [c]
              have collapse :
                  (∑ i : Fin n, ∑ v : (Fin p → Fin n), T i v) =
                    ∑ z ∈ S, T z.1 z.2 := by
                classical
                calc
                  (∑ i : Fin n, ∑ v : (Fin p → Fin n), T i v) =
                      ∑ z : (Fin n × (Fin p → Fin n)), T z.1 z.2 := by
                        rw [Fintype.sum_prod_type]
                  _ = ∑ z ∈ S, T z.1 z.2 := by
                        symm
                        apply Finset.sum_subset (by intro _ h; simp)
                        intro z hz hnot
                        exact (outside z.1 z.2 hnot)
              change |∑ i : Fin n, ∑ v : (Fin p → Fin n), T i v| ≤ _
              rw [collapse]
              calc
                |∑ z ∈ S, T z.1 z.2| ≤
                    ∑ z ∈ S, |T z.1 z.2| := by
                       exact Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ _z ∈ S, B^p := by
                      exact Finset.sum_le_sum (fun z hz => point z.1 z.2)
                _ = (S.card:ℝ) * B^p := by simp
                _ ≤ ((n^(p/2) * (p/2)^(p+1) : ℕ):ℝ) * B^p := by
                      gcongr
                      dsimp [S]
                      exact_mod_cast
                        (WignerSupport.card_filter_small_path_vertices
                           (n:=n) (p:=p) (d:=p/2))
                _ = (n:ℝ)^(p/2) * ((p/2:ℕ):ℝ)^(p+1) * B^p := by
                      push_cast
                      ring
            let bad : ℕ → ℕ → ℝ := fun n p =>
                ∑ i : Fin n, ∑ v : (Fin p → Fin n),
                  if WignerSupport.pathEnd p i v = i then
                    if (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                        WignerSupport.pathEdgesNat i v r =
                          WignerSupport.pathEdgesNat i v u) then
                      if (WignerSupport.pathVerticesFin i v).card < p/2+1
                      then (∫ w, WignerSupport.pathTerm
                        (fun a b : Fin n =>
                          Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                      else 0 else 0 else 0
            have strictVanish (p : ℕ) : Tendsto
                (fun k : ℕ => bad (k+1) p /
                    (((k+1:ℕ):ℝ)^(p/2+1))) atTop (𝓝 (0:ℝ)) := by
              let K : ℝ := ((p/2:ℕ):ℝ)^(p+1) * B^p
              have K0 : 0 ≤ K := by
                dsimp [K]
                positivity
              apply WignerSupport.tendsto_error_of_card_power
                (p/2) K K0 (fun n => bad n p)
              intro n hn
              calc
                |bad n p| ≤
                    (n:ℝ)^(p/2) * ((p/2:ℕ):ℝ)^(p+1) * B^p := by
                      exact strictBound n p
                _ = (n:ℝ)^(p/2) * K := by dsimp [K]; ring
            -- It remains to enumerate the equality case in the pruned sum.
            -- First isolate its value from its count.  These are finite sums;
            -- no limit or probability is hidden in the following reduction.
            -- On a top-cardinality repeated walk not only are its edge fibres
            -- pairs (`hleading`), but the edge *image* has cardinality `p/2`.
            -- Thus every such term is literally the same scalar.
            have hleadval (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
                (hep : 2 ∣ p) (rep : ∀ u : Fin p, ∃ r : Fin p,
                  r ≠ u ∧ WignerSupport.pathEdgesNat i v r =
                    WignerSupport.pathEdgesNat i v u)
                (mx : (WignerSupport.pathVerticesFin i v).card = p/2+1) :
                (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                    Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ) =
                  (WignerSupport.cutVariance μ X (R:ℝ))^(p/2) := by
              rw [hleading n p i v hep rep mx]
              rw [WignerSupport.card_edges_eq_half_of_max_vertices i v rep mx]
            -- Pairing the root and its tail by `Fin.cons` shows why ordinary
            -- label maps are not counted by `n^(m+1)`: after fixing an equality
            -- pattern they are *injective* choices of `m+1` labels.
            -- The support lemma deliberately works even for `n<m+1`.
            have hlabels (p d n : ℕ)
                (w : Fin (p+1) → Fin d) (surj : Function.Surjective w)
                (lw : WignerSupport.IsLeadingWord p d w) :
                Fintype.card { f : WignerSupport.Relabels (n:=n) w //
                    WignerSupport.IsLeadingWord p n f.val } =
                      Nat.descFactorial n d := by
              exact WignerSupport.card_relabels_leadingWord w surj lw
            -- Write the top sum without integrals.  The remaining finite
            -- coefficient is precisely the number of equality patterns of a
            -- closed contour. In informal proofs this simple reduction is
            -- frequently where arbitrary `n^(p+1)` words get mistaken for
            -- labelled trees.
            classical
            let L (n p : ℕ) : Finset (Fin n × (Fin p → Fin n)) :=
                Finset.univ.filter
                  (fun z => WignerSupport.IsLeadingPath z.1 z.2)
            have hleadSum (n p : ℕ) (hep : 2 ∣ p) :
                (∑ i : Fin n, ∑ v : (Fin p → Fin n),
                  if WignerSupport.IsLeadingPath i v then
                    (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                       Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                  else 0) =
                  ((L n p).card : ℝ) *
                    (WignerSupport.cutVariance μ X (R:ℝ))^(p/2) := by
              classical
              let val : Fin n → (Fin p → Fin n) → ℝ := fun i v =>
                    if WignerSupport.IsLeadingPath i v then
                      (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                        Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                    else 0
              have each (i : Fin n) (v : Fin p → Fin n) :
                  val i v = if WignerSupport.IsLeadingPath i v then
                    (WignerSupport.cutVariance μ X (R:ℝ))^(p/2) else 0 := by
                dsimp [val]
                split_ifs with h
                · rcases h with ⟨hc,hr,hm⟩
                  exact hleadval n p i v hep hr hm
                · rfl
              change (∑ i : Fin n, ∑ v : (Fin p → Fin n), val i v) = _
              simp_rw [each]
              classical
              -- an indicator sum is the cardinality of its support
              have rewriteSum :
                  (∑ i : Fin n, ∑ v : (Fin p → Fin n),
                     if WignerSupport.IsLeadingPath i v then
                       (WignerSupport.cutVariance μ X (R:ℝ))^(p/2) else 0) =
                    ∑ z ∈ L n p,
                       (WignerSupport.cutVariance μ X (R:ℝ))^(p/2) := by
                calc
                  (∑ i : Fin n, ∑ v : (Fin p → Fin n),
                    if WignerSupport.IsLeadingPath i v then
                      (WignerSupport.cutVariance μ X (R:ℝ))^(p/2) else 0) =
                    ∑ z : (Fin n × (Fin p → Fin n)),
                      (if WignerSupport.IsLeadingPath z.1 z.2 then
                        (WignerSupport.cutVariance μ X (R:ℝ))^(p/2) else 0) := by
                          rw [Fintype.sum_prod_type]
                  _ = ∑ z ∈ L n p,
                        (WignerSupport.cutVariance μ X (R:ℝ))^(p/2) := by
                          classical
                          dsimp [L]
                          exact (Finset.sum_filter
                            (s := (Finset.univ : Finset (Fin n × (Fin p → Fin n))))
                            (fun z => WignerSupport.IsLeadingPath z.1 z.2)
                            (fun _ => (WignerSupport.cutVariance μ X (R:ℝ))^(p/2))).symm
              rw [rewriteSum]
              simp
            -- `hlabels` disposes of all *labellings* in this finite
            -- coefficient.  The genuinely unlabelled assertion now left is
            -- that the closed maximal equality patterns (equivalently contour
            -- walks of rooted plane trees) are Catalan.  Subsequent variance
            -- and concentration estimates for the bounded matrix are parked
            -- behind this exact count rather than an `n^(p+1)` over-estimate.
            -- No edge of a walk with fewer vertices contributes to this count;
            -- those have already been paid for by `strictVanish`.
            have hLcard (n p : ℕ) :
                (L n p).card =
                  (WignerSupport.leadPatterns p).card *
                    Nat.descFactorial n (p/2+1) := by
              classical
              simpa [L] using
                (WignerSupport.card_leadingPaths_eq_patterns_mul p n)
            /- The quotient by relabellings is now an actual finite object.
               In particular the labellings of a fixed equality pattern
               really are a falling factorial, not `n^(p+1)`.  This was the
               nuisance in transporting the singleton-pruning bound to the
               leading coefficient. -/
            have hleadSum_patterns (n p : ℕ) (hep : 2 ∣ p) :
                (∑ i : Fin n, ∑ v : (Fin p → Fin n),
                  if WignerSupport.IsLeadingPath i v then
                    (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                       Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                  else 0) =
                  (((WignerSupport.leadPatterns p).card : ℝ) *
                    (Nat.descFactorial n (p/2+1) : ℝ)) *
                      (WignerSupport.cutVariance μ X (R:ℝ))^(p/2) := by
              rw [hleadSum n p hep, hLcard]
              push_cast
              ring
            have splitTrace (n p : ℕ) :
                (∫ w, Matrix.trace ((Ap n w)^p) ∂μ) =
                  bad n p +
                  (∑ i : Fin n, ∑ v : (Fin p → Fin n),
                    if WignerSupport.IsLeadingPath i v then
                      (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                         Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                    else 0) := by
              classical
              rw [htracepruned]
              dsimp [bad]
              -- split each repeated closed summand by the strict or equal
              -- vertex count; the uniform bound `hvertices` rules out a
              -- larger case.
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro v hv
              by_cases c : WignerSupport.pathEnd p i v = i
              · simp only [c, if_true]
                by_cases rep : (∀ u : Fin p, ∃ r : Fin p, r ≠ u ∧
                      WignerSupport.pathEdgesNat i v r =
                        WignerSupport.pathEdgesNat i v u)
                · simp only [rep, if_true]
                  have le := hvertices n p i v rep
                  by_cases small :
                    (WignerSupport.pathVerticesFin i v).card < p/2+1
                  · have nl : ¬ WignerSupport.IsLeadingPath i v := by
                      intro z
                      exact (Nat.ne_of_lt small) z.2.2
                    simp [small, nl]
                  · have eq : (WignerSupport.pathVerticesFin i v).card =
                              p/2+1 := by omega
                    have lead : WignerSupport.IsLeadingPath i v :=
                      ⟨c, rep, eq⟩
                    simp [small, lead]
                · have nl : ¬ WignerSupport.IsLeadingPath i v := by
                    intro h
                    exact rep h.2.1
                  simp [rep, nl]
              · have nl : ¬ WignerSupport.IsLeadingPath i v := by
                    intro h; exact c h.1
                simp [c, nl]
            -- Expected trace at a fixed even order: the maximal labelled
            -- paths have an honest limit, since the falling factorial divided
            -- by `n^d` tends to one.  The smaller vertex strata vanish by one
            -- full power of `n` (`strictVanish`).  This step isolates the
            -- **unlabelled** coefficient with no analytic or probabilistic
            -- assumption.
            have traceMoment (p : ℕ) (hep : 2 ∣ p) :
                Tendsto
                  (fun k : ℕ =>
                    (∫ w, Matrix.trace ((Ap (k+1) w)^p) ∂μ) /
                      (((k+1:ℕ):ℝ)^(p/2+1))) atTop
                  (𝓝 (((WignerSupport.leadPatterns p).card : ℝ) *
                     (WignerSupport.cutVariance μ X (R:ℝ))^(p/2))) := by
              let c : ℝ := (WignerSupport.cutVariance μ X (R:ℝ))^(p/2)
              have top : Tendsto
                  (fun k : ℕ =>
                    (∑ i : Fin (k+1), ∑ v : (Fin p → Fin (k+1)),
                      if WignerSupport.IsLeadingPath i v then
                        (∫ w, WignerSupport.pathTerm (fun a b : Fin (k+1) =>
                          Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                      else 0) / (((k+1:ℕ):ℝ)^(p/2+1))) atTop
                    (𝓝 (((WignerSupport.leadPatterns p).card : ℝ) * c)) := by
                have base := WignerSupport.tendsto_card_leadingPaths_normalized p
                have cc := base.mul_const c
                convert cc using 1
                · funext k
                  rw [hleadSum (k+1) p hep]
                  dsimp [c, L]
                  ring
              have bot := strictVanish p
              have both := bot.add top
              convert both using 1
              · funext k
                rw [splitTrace]
                ring
              · simp [c]
            -- In the equality stratum one has much more than the raw cardinal
            -- bound. Reading a word from the *right*, an old vertex is exactly
            -- an old edge; no step is a loop. These facts are what let one
            -- regard its finite edge set as an honest tree, rather than a
            -- connected multigraph with possible diagonal edges. They are useful
            -- for the first-return (Dyck) recursion below.
            have htreesuffix (n p : ℕ) (i : Fin n) (v : Fin (p+1) → Fin n)
                (hi : WignerSupport.IsLeadingPath i v) :
                 (i.val ∈ WignerSupport.walkVertices (v 0).val
                       (WignerSupport.pathList (Fin.tail v)) ↔
                   WignerSupport.edgeNat i.val (v 0).val ∈
                     WignerSupport.walkEdges (v 0).val
                       (WignerSupport.pathList (Fin.tail v))) := by
              exact WignerSupport.leading_old_iff i v hi.2.1 hi.2.2
            have htreelist (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
                (hi : WignerSupport.IsLeadingPath i v) :
                (WignerSupport.walkVertices i.val
                    (WignerSupport.pathList v)).card =
                  (WignerSupport.walkEdges i.val
                    (WignerSupport.pathList v)).card + 1 := by
              exact WignerSupport.leading_walk_eq i v hi.2.1 hi.2.2
            have htreenoloop (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
                (hi : WignerSupport.IsLeadingPath i v) :
                ∀ a : ℕ, WignerSupport.edgeNat a a ∉
                    WignerSupport.walkEdges i.val (WignerSupport.pathList v) := by
              exact WignerSupport.leading_no_self i v hi.2.1 hi.2.2
            have htreegraph (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
                (hi : WignerSupport.IsLeadingPath i v) :
                (WignerSupport.walkGraph i.val
                  (WignerSupport.pathList v)).IsTree := by
              exact WignerSupport.leading_walk_tree i v hi
            -- In particular consecutive letters, when viewed in this graph,
            -- change their distance from the root by one. Thus their up/down
            -- signs form the parenthesis word used for the remaining unlabelled
            -- Catalan count.
            have htreeheight (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
                (hi : WignerSupport.IsLeadingPath i v)
                (a b : WignerSupport.WalkVert i.val (WignerSupport.pathList v))
                (adj : (WignerSupport.walkGraph i.val
                    (WignerSupport.pathList v)).Adj a b) :
                (WignerSupport.walkGraph i.val (WignerSupport.pathList v)).dist
                      (⟨i.val, WignerSupport.walkVertices_root_mem _ _⟩) a =
                  (WignerSupport.walkGraph i.val (WignerSupport.pathList v)).dist
                      (⟨i.val, WignerSupport.walkVertices_root_mem _ _⟩) b + 1 ∨
                (WignerSupport.walkGraph i.val (WignerSupport.pathList v)).dist
                      (⟨i.val, WignerSupport.walkVertices_root_mem _ _⟩) b =
                  (WignerSupport.walkGraph i.val (WignerSupport.pathList v)).dist
                      (⟨i.val, WignerSupport.walkVertices_root_mem _ _⟩) a + 1 := by
              exact (htreegraph n p i v hi).dist_eq_dist_add_one_of_adj _ adj
            -- The remaining coefficient is a completely *unlabelled* one.
            -- All dependence on the ambient matrix size has disappeared:
            -- it is the cardinal of Boolean equality patterns of leading
            -- words.  Proving it is Catalan is the planar tree/first-return
            -- recursion (afterwards one still performs the usual bounded
            -- variance upgrade).  Earlier bounds `n^(p+1)` cannot be used
            -- here since the exact scalar just above is needed.
            -- Odd orders cannot contribute in the equality stratum.  This is
            -- not just an algebraic convenience: a leading contour lives in a
            -- (simple) tree, hence is a genuinely even closed walk. The lemma
            -- colors that finite tree by distance mod two and also supplies the
            -- unique further occurrence of the root edge, the index used in
            -- the first-return Catalan decomposition.
            have hevenPath (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
                (z : WignerSupport.IsLeadingPath i v) : 2 ∣ p := by
              exact WignerSupport.leading_even i v z
            have hfirstIndex (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v) :
                ∃! t : Fin a,
                  WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val := by
              exact WignerSupport.leading_first_edge_unique i v z
            have hpatOdd (p : ℕ) (ho : ¬ 2 ∣ p) :
                WignerSupport.leadPatterns p = ∅ :=
              WignerSupport.leadPatterns_eq_empty_of_odd p ho
            -- The suffix criterion is also valid at the second occurrence,
            -- not just at the head.  A prefix here consists of the letters
            -- *before* its starting vertex.  This is the convenient form for
            -- orienting `hfirstIndex` (the final root in `zs` prevents a
            -- second outward crossing).
            have hposition (n p : ℕ) (i : Fin n) (v : Fin p → Fin n)
                (z : WignerSupport.IsLeadingPath i v)
                (pre zs : List ℕ) (a b : ℕ)
                (sp : i.val :: WignerSupport.pathList v =
                  pre ++ a :: b :: zs) :
                (a ∈ WignerSupport.walkVertices b zs ↔
                   WignerSupport.edgeNat a b ∈
                     WignerSupport.walkEdges b zs) := by
              exact WignerSupport.walk_old_iff_at_split i.val
                (WignerSupport.pathList v) pre a b zs
                (htreelist n p i v z) sp
            have traceOdd (p : ℕ) (ho : ¬ 2 ∣ p) :
                Tendsto
                  (fun k : ℕ =>
                    (∫ w, Matrix.trace ((Ap (k+1) w)^p) ∂μ) /
                      (((k+1:ℕ):ℝ)^(p/2+1))) atTop (𝓝 (0:ℝ)) := by
              -- The strict part already loses a full vertex.  The split into
              -- strict and leading paths is valid without any parity
              -- assumption; on the leading half `leading_even` is a
              -- contradiction.
              have none (n : ℕ) (i : Fin n) (v : Fin p → Fin n) :
                  ¬ WignerSupport.IsLeadingPath i v := by
                intro z
                exact ho (hevenPath n p i v z)
              have vanish (n : ℕ) :
                  (∑ i : Fin n, ∑ v : (Fin p → Fin n),
                    if WignerSupport.IsLeadingPath i v then
                      (∫ w, WignerSupport.pathTerm (fun a b : Fin n =>
                         Y (min (a:ℕ) b) (max (a:ℕ) b) w) p i v ∂μ)
                    else 0) = 0 := by
                classical
                apply Finset.sum_eq_zero
                intro i hi
                apply Finset.sum_eq_zero
                intro v hv
                simp [none n i v]
              have eqfun :
                  (fun k : ℕ =>
                    (∫ w, Matrix.trace ((Ap (k+1) w)^p) ∂μ) /
                      (((k+1:ℕ):ℝ)^(p/2+1))) =
                  (fun k : ℕ => bad (k+1) p /
                      (((k+1:ℕ):ℝ)^(p/2+1))) := by
                funext k
                rw [splitTrace, vanish]
                simp
              rw [eqfun]
              exact strictVanish p
            -- For even length the unresolved finite coefficient is now only
            -- the unlabelled one; the empty contour is its base case.
            have hpatZero : (WignerSupport.leadPatterns 0).card = 1 :=
              WignerSupport.leadPatterns_zero_card
            -- The next step is to orient the occurrence `hfirstIndex`: removing
            -- the root edge in `htreegraph` separates the child subtree.  That
            -- first-return split gives the Catalan convolution for the Boolean
            -- equality patterns. No loose `n^(p+1)` bound can stand in for that
            -- coefficient. Concentration of the bounded trace follows the same
            -- paired-edge split.
            -- `hfirstIndex` was still unoriented; cardinal-two alone does
            -- not say whether that second traversal is out of or into the
            -- root.  Equality at *every* right suffix (`hposition`) fixes
            -- the direction: had it been out again, the final root in the
            -- suffix would force a third occurrence.  The positional list
            -- argument is packaged separately so indices in the dropped
            -- word cannot silently alias the returning one.
            have hfirstReturn (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v) :
                ∃! t : Fin a,
                  WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                      WignerSupport.edgeNat i.val (v 0).val ∧
                    (v t.castSucc).val = (v 0).val ∧
                    (v t.succ).val = i.val := by
              exact WignerSupport.leading_first_return i v z
            -- The excursion on the child side has even length.  It is useful
            -- to record this without (incorrectly) assuming that an arbitrary
            -- subwalk already has equality cardinality of its own.  It follows
            -- by restricting the two-colouring of the ambient equality tree.
            have hfirstReturnEven (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                2 ∣ t.val := by
              exact WignerSupport.leading_first_return_even i v z t ht
            -- With the returning edge now oriented and its child-side
            -- excursion even, the still missing finite step is the bridge
            -- separation in this tree: after deleting the root-child edge
            -- the middle word and the remaining word use disjoint alphabets,
            -- except for the prescribed root. Relabel each by its first
            -- occurrences to obtain two `leadPatterns`; grafting them is the
            -- inverse. This is the genuine Catalan first-return coefficient
            -- (and subsequently the paired-edge variance estimate), not a
            -- replacement by an `n^(p+1)` bound.
            -- The bridge separation itself is not a heuristic.  In the
            -- equality tree the first edge is a bridge.  Its two occurrences
            -- have just been identified above.  Neither of the two open
            -- pieces contains that edge (the fibre has cardinal two); regarding
            -- them as walks in `walkGraph.deleteEdges` therefore puts them in
            -- different connected components.  This is the delicate missing
            -- implication in the usual informal first-return argument.
            have hbridge (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                Disjoint
                  (WignerSupport.walkVertices (v 0).val
                    ((WignerSupport.pathList (Fin.tail v)).take t.val))
                  (WignerSupport.walkVertices i.val
                    ((WignerSupport.pathList (Fin.tail v)).drop (t.val+1))) := by
              exact WignerSupport.leading_split_vertices_disjoint i v z t ht
            have hchildClosed (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                WignerSupport.walkLast (v 0).val
                    ((WignerSupport.pathList (Fin.tail v)).take t.val) =
                      (v 0).val := by
              exact WignerSupport.leading_split_child_closed i v z t ht
            have hrootClosed (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                WignerSupport.walkLast i.val
                    ((WignerSupport.pathList (Fin.tail v)).drop (t.val+1)) =
                      i.val := by
              exact WignerSupport.leading_split_root_closed i v z t ht
            -- and equality of the connected-walk bound descends to each
            -- open piece (their vertices and edges form a disjoint union,
            -- with just the bridge added on the full word).
            have hpEq (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                ((WignerSupport.walkVertices (v 0).val
                    ((WignerSupport.pathList (Fin.tail v)).take t.val)).card =
                  (WignerSupport.walkEdges (v 0).val
                    ((WignerSupport.pathList (Fin.tail v)).take t.val)).card + 1) ∧
                ((WignerSupport.walkVertices i.val
                    ((WignerSupport.pathList (Fin.tail v)).drop (t.val+1))).card =
                  (WignerSupport.walkEdges i.val
                    ((WignerSupport.pathList (Fin.tail v)).drop (t.val+1))).card + 1) := by
              exact WignerSupport.leading_split_piece_eq i v z t ht
            -- Put the two list words back into finite paths.  This is not a
            -- harmless coercion: a piece may be empty and its alphabet need
            -- not be full.  Keeping the bounds as fields avoids the common
            -- off-by-one at `t=0`.
            have hpieceFin (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                let mid : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).take t.val
                let rest : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
                WignerSupport.ClosedEqPiece n (v 0) mid ∧
                  WignerSupport.ClosedEqPiece n i rest := by
              exact WignerSupport.leading_split_closedEqPieces i v z t ht
            have hpieceParity (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                2 ∣ ((WignerSupport.pathList (Fin.tail v)).take t.val).length ∧
                2 ∣ ((WignerSupport.pathList (Fin.tail v)).drop
                  (t.val+1)).length := by
              exact WignerSupport.leading_split_piece_even' i v z t ht
            -- Equality alone does not say that a displayed step in a closed
            -- piece is paired.  The little bridge argument is now available
            -- without relabelling: deleting that edge in the equality tree
            -- connects the two endpoints through the old root unless the
            -- occurrence is in the prefix or in the suffix.
            have hpieceStep (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                (∀ (k : ℕ)
                   (hk : k < ((WignerSupport.pathList (Fin.tail v)).take t.val).length),
                   let mid := (WignerSupport.pathList (Fin.tail v)).take t.val
                   let b := mid[k]
                   let aa := WignerSupport.walkLast (v 0).val (mid.take k)
                   WignerSupport.edgeNat aa b ∈
                        WignerSupport.walkEdges (v 0).val (mid.take k) ∨
                     WignerSupport.edgeNat aa b ∈
                        WignerSupport.walkEdges b (mid.drop (k+1))) ∧
                (∀ (k : ℕ)
                   (hk : k < ((WignerSupport.pathList (Fin.tail v)).drop (t.val+1)).length),
                   let rest := (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
                   let b := rest[k]
                   let aa := WignerSupport.walkLast i.val (rest.take k)
                   WignerSupport.edgeNat aa b ∈
                        WignerSupport.walkEdges i.val (rest.take k) ∨
                     WignerSupport.edgeNat aa b ∈
                        WignerSupport.walkEdges b (rest.drop (k+1))) := by
              let mid : List ℕ :=
                  (WignerSupport.pathList (Fin.tail v)).take t.val
              let rest : List ℕ :=
                  (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
              have eqp := WignerSupport.leading_split_piece_eq i v z t ht
              have clp : WignerSupport.walkLast (v 0).val mid =
                    (v 0).val :=
                WignerSupport.leading_split_child_closed i v z t ht
              have clr : WignerSupport.walkLast i.val rest = i.val :=
                WignerSupport.leading_split_root_closed i v z t ht
              change
                (∀ (k : ℕ) (hk : k < mid.length),
                  let b := mid[k]
                  let aa := WignerSupport.walkLast (v 0).val (mid.take k)
                  WignerSupport.edgeNat aa b ∈
                    WignerSupport.walkEdges (v 0).val (mid.take k) ∨
                  WignerSupport.edgeNat aa b ∈
                    WignerSupport.walkEdges b (mid.drop (k+1))) ∧
                (∀ (k : ℕ) (hk : k < rest.length),
                  let b := rest[k]
                  let aa := WignerSupport.walkLast i.val (rest.take k)
                  WignerSupport.edgeNat aa b ∈
                    WignerSupport.walkEdges i.val (rest.take k) ∨
                  WignerSupport.edgeNat aa b ∈
                    WignerSupport.walkEdges b (rest.drop (k+1)))
              constructor
              · intro k hk
                exact WignerSupport.closed_eq_step_seen_elsewhere
                   (v 0).val mid eqp.1 clp k hk
              · intro k hk
                exact WignerSupport.closed_eq_step_seen_elsewhere
                   i.val rest eqp.2 clr k hk
            -- Every edge displayed inside either of the two resulting words
            -- has a *different positional occurrence inside that same word*.
            -- This is a repeated-edge statement, not merely containment in the
            -- original path's edge image.  In particular the index produced by
            -- `hpieceStep` cannot be the displayed `Fin` index after the
            -- `take`/`drop` casts.  Keeping the bound argument of `listPath`
            -- explicit lets us handle the empty piece without any transports.
            have hpieceRep (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                let mid : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).take t.val
                let rest : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
                (∀ (bd : ∀ b ∈ mid, b < n),
                    ∀ u : Fin mid.length, ∃ r : Fin mid.length, r ≠ u ∧
                      WignerSupport.pathEdgesNat (v 0)
                          (WignerSupport.listPath mid bd) r =
                        WignerSupport.pathEdgesNat (v 0)
                          (WignerSupport.listPath mid bd) u) ∧
                (∀ (bd : ∀ b ∈ rest, b < n),
                    ∀ u : Fin rest.length, ∃ r : Fin rest.length, r ≠ u ∧
                      WignerSupport.pathEdgesNat i
                          (WignerSupport.listPath rest bd) r =
                        WignerSupport.pathEdgesNat i
                          (WignerSupport.listPath rest bd) u) := by
              dsimp
              let mid : List ℕ :=
                (WignerSupport.pathList (Fin.tail v)).take t.val
              let rest : List ℕ :=
                (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
              have seen := hpieceStep n a i v z t ht
              change
                (∀ (k : ℕ) (hk : k < mid.length),
                  let b := mid[k]
                  let aa := WignerSupport.walkLast (v 0).val (mid.take k)
                  WignerSupport.edgeNat aa b ∈
                    WignerSupport.walkEdges (v 0).val (mid.take k) ∨
                  WignerSupport.edgeNat aa b ∈
                    WignerSupport.walkEdges b (mid.drop (k+1))) ∧
                (∀ (k : ℕ) (hk : k < rest.length),
                  let b := rest[k]
                  let aa := WignerSupport.walkLast i.val (rest.take k)
                  WignerSupport.edgeNat aa b ∈
                    WignerSupport.walkEdges i.val (rest.take k) ∨
                  WignerSupport.edgeNat aa b ∈
                    WignerSupport.walkEdges b (rest.drop (k+1))) at seen
              change
                (∀ (bd : ∀ b ∈ mid, b < n),
                  ∀ u : Fin mid.length, ∃ r : Fin mid.length, r ≠ u ∧
                    WignerSupport.pathEdgesNat (v 0)
                        (WignerSupport.listPath mid bd) r =
                      WignerSupport.pathEdgesNat (v 0)
                        (WignerSupport.listPath mid bd) u) ∧
                (∀ (bd : ∀ b ∈ rest, b < n),
                  ∀ u : Fin rest.length, ∃ r : Fin rest.length, r ≠ u ∧
                    WignerSupport.pathEdgesNat i
                        (WignerSupport.listPath rest bd) r =
                      WignerSupport.pathEdgesNat i
                        (WignerSupport.listPath rest bd) u)
              constructor
              · intro bd
                exact WignerSupport.repeated_edges_listPath_of_seen
                  (v 0) mid bd seen.1
              · intro bd
                exact WignerSupport.repeated_edges_listPath_of_seen
                  i rest bd seen.2
            -- Precisely the remaining obstruction to calling them
            -- leading is now an *upper* fibre estimate.  The elementary
            -- counting that turns lower repetitions plus this upper estimate
            -- into `length/2` vertices is isolated in `PieceLeading`.
            have hpieceLead_of_upper (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                let mid : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).take t.val
                let rest : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
                let zm : WignerSupport.ClosedEqPiece n (v 0) mid :=
                    (WignerSupport.leading_split_closedEqPieces i v z t ht).1
                let zr : WignerSupport.ClosedEqPiece n i rest :=
                    (WignerSupport.leading_split_closedEqPieces i v z t ht).2
                (∀ e ∈ (Finset.univ.image
                    (WignerSupport.pathEdgesNat (v 0)
                      (WignerSupport.listPath mid zm.bound))),
                    ((Finset.univ : Finset (Fin mid.length)).filter
                      (fun r => WignerSupport.pathEdgesNat (v 0)
                        (WignerSupport.listPath mid zm.bound) r = e)).card ≤ 2) →
                (∀ e ∈ (Finset.univ.image
                    (WignerSupport.pathEdgesNat i
                      (WignerSupport.listPath rest zr.bound))),
                    ((Finset.univ : Finset (Fin rest.length)).filter
                      (fun r => WignerSupport.pathEdgesNat i
                        (WignerSupport.listPath rest zr.bound) r = e)).card ≤ 2) →
                WignerSupport.IsLeadingPath (v 0)
                      (WignerSupport.listPath mid zm.bound) ∧
                  WignerSupport.IsLeadingPath i
                      (WignerSupport.listPath rest zr.bound) := by
              dsimp
              let mid : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).take t.val
              let rest : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
              have pcs := WignerSupport.leading_split_closedEqPieces i v z t ht
              change WignerSupport.ClosedEqPiece n (v 0) mid ∧
                    WignerSupport.ClosedEqPiece n i rest at pcs
              let zm : WignerSupport.ClosedEqPiece n (v 0) mid := pcs.1
              let zr : WignerSupport.ClosedEqPiece n i rest := pcs.2
              change
                (∀ e ∈ (Finset.univ.image
                    (WignerSupport.pathEdgesNat (v 0)
                      (WignerSupport.listPath mid zm.bound))),
                    ((Finset.univ : Finset (Fin mid.length)).filter
                      (fun r => WignerSupport.pathEdgesNat (v 0)
                        (WignerSupport.listPath mid zm.bound) r = e)).card ≤ 2) →
                (∀ e ∈ (Finset.univ.image
                    (WignerSupport.pathEdgesNat i
                      (WignerSupport.listPath rest zr.bound))),
                    ((Finset.univ : Finset (Fin rest.length)).filter
                      (fun r => WignerSupport.pathEdgesNat i
                        (WignerSupport.listPath rest zr.bound) r = e)).card ≤ 2) →
                WignerSupport.IsLeadingPath (v 0)
                    (WignerSupport.listPath mid zm.bound) ∧
                  WignerSupport.IsLeadingPath i
                    (WignerSupport.listPath rest zr.bound)
              intro hm hr
              have reps := hpieceRep n a i v z t ht
              change
                (∀ (bd : ∀ b ∈ mid, b < n), ∀ u : Fin mid.length,
                    ∃ r : Fin mid.length, r ≠ u ∧
                      WignerSupport.pathEdgesNat (v 0)
                        (WignerSupport.listPath mid bd) r =
                      WignerSupport.pathEdgesNat (v 0)
                        (WignerSupport.listPath mid bd) u) ∧
                (∀ (bd : ∀ b ∈ rest, b < n), ∀ u : Fin rest.length,
                    ∃ r : Fin rest.length, r ≠ u ∧
                      WignerSupport.pathEdgesNat i
                        (WignerSupport.listPath rest bd) r =
                      WignerSupport.pathEdgesNat i
                        (WignerSupport.listPath rest bd) u) at reps
              refine ⟨?_, ?_⟩
              · exact WignerSupport.ClosedEqPiece.isLeading_of_rep_of_fiber_le_two
                  zm (reps.1 zm.bound) hm
              · exact WignerSupport.ClosedEqPiece.isLeading_of_rep_of_fiber_le_two
                  zr (reps.2 zr.bound) hr
            -- The promised upper estimate really does follow by an injection
            -- of *positions*, not merely an inclusion of edge images.  Child
            -- edges keep their tail index and are shifted once for the root
            -- letter; root-suffix edges are shifted by `t+2`.  Both maps are
            -- embeddings into `Fin (a+1)`.  Thus a fibre in either word is a
            -- sub-fibre of an ambient one, whose cardinal is exactly two.
            have hpieceUpper (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                let mid : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).take t.val
                let rest : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
                let zm : WignerSupport.ClosedEqPiece n (v 0) mid :=
                    (WignerSupport.leading_split_closedEqPieces i v z t ht).1
                let zr : WignerSupport.ClosedEqPiece n i rest :=
                    (WignerSupport.leading_split_closedEqPieces i v z t ht).2
                (∀ e ∈ (Finset.univ.image
                    (WignerSupport.pathEdgesNat (v 0)
                      (WignerSupport.listPath mid zm.bound))),
                    ((Finset.univ : Finset (Fin mid.length)).filter
                      (fun r => WignerSupport.pathEdgesNat (v 0)
                        (WignerSupport.listPath mid zm.bound) r = e)).card ≤ 2) ∧
                (∀ e ∈ (Finset.univ.image
                    (WignerSupport.pathEdgesNat i
                      (WignerSupport.listPath rest zr.bound))),
                    ((Finset.univ : Finset (Fin rest.length)).filter
                      (fun r => WignerSupport.pathEdgesNat i
                        (WignerSupport.listPath rest zr.bound) r = e)).card ≤ 2) := by
              exact WignerSupport.leading_split_piece_fiber_le_two i v z t ht
            -- Consequently the finite pieces are honest leading paths.  This
            -- is the step that was still implicit if one just compared the
            -- equality cardinalities of their vertex sets.
            have hpieceLead (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                let mid : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).take t.val
                let rest : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
                let zm : WignerSupport.ClosedEqPiece n (v 0) mid :=
                    (WignerSupport.leading_split_closedEqPieces i v z t ht).1
                let zr : WignerSupport.ClosedEqPiece n i rest :=
                    (WignerSupport.leading_split_closedEqPieces i v z t ht).2
                WignerSupport.IsLeadingPath (v 0)
                    (WignerSupport.listPath mid zm.bound) ∧
                  WignerSupport.IsLeadingPath i
                    (WignerSupport.listPath rest zr.bound) := by
              dsimp
              let mid : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).take t.val
              let rest : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
              have pcs := WignerSupport.leading_split_closedEqPieces i v z t ht
              change WignerSupport.ClosedEqPiece n (v 0) mid ∧
                    WignerSupport.ClosedEqPiece n i rest at pcs
              let zm : WignerSupport.ClosedEqPiece n (v 0) mid := pcs.1
              let zr : WignerSupport.ClosedEqPiece n i rest := pcs.2
              change WignerSupport.IsLeadingPath (v 0)
                    (WignerSupport.listPath mid zm.bound) ∧
                  WignerSupport.IsLeadingPath i
                    (WignerSupport.listPath rest zr.bound)
              have upp := hpieceUpper n a i v z t ht
              change
                (∀ e ∈ (Finset.univ.image
                    (WignerSupport.pathEdgesNat (v 0)
                      (WignerSupport.listPath mid zm.bound))),
                    ((Finset.univ : Finset (Fin mid.length)).filter
                      (fun r => WignerSupport.pathEdgesNat (v 0)
                        (WignerSupport.listPath mid zm.bound) r = e)).card ≤ 2) ∧
                (∀ e ∈ (Finset.univ.image
                    (WignerSupport.pathEdgesNat i
                      (WignerSupport.listPath rest zr.bound))),
                    ((Finset.univ : Finset (Fin rest.length)).filter
                      (fun r => WignerSupport.pathEdgesNat i
                        (WignerSupport.listPath rest zr.bound) r = e)).card ≤ 2)
                     at upp
              exact hpieceLead_of_upper n a i v z t ht upp.1 upp.2
            -- In particular each piece defines a genuine *unlabelled* Boolean
            -- pattern.  No surjectivity of its ambient alphabet is needed:
            -- `wordPattern_mem_of_leading` replaces a word by a choice of one
            -- occurrence of each of its letters.  This is the right input
            -- for a Catalan convolution.
            have hpiecePatterns (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                let mid : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).take t.val
                let rest : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
                let zm : WignerSupport.ClosedEqPiece n (v 0) mid :=
                    (WignerSupport.leading_split_closedEqPieces i v z t ht).1
                let zr : WignerSupport.ClosedEqPiece n i rest :=
                    (WignerSupport.leading_split_closedEqPieces i v z t ht).2
                WignerSupport.wordPattern
                    (@Fin.cons mid.length (fun _ => Fin n) (v 0)
                      (WignerSupport.listPath mid zm.bound)) ∈
                      WignerSupport.leadPatterns mid.length ∧
                WignerSupport.wordPattern
                    (@Fin.cons rest.length (fun _ => Fin n) i
                      (WignerSupport.listPath rest zr.bound)) ∈
                      WignerSupport.leadPatterns rest.length := by
              dsimp
              let mid : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).take t.val
              let rest : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
              have pcs := WignerSupport.leading_split_closedEqPieces i v z t ht
              change WignerSupport.ClosedEqPiece n (v 0) mid ∧
                    WignerSupport.ClosedEqPiece n i rest at pcs
              let zm : WignerSupport.ClosedEqPiece n (v 0) mid := pcs.1
              let zr : WignerSupport.ClosedEqPiece n i rest := pcs.2
              change WignerSupport.wordPattern
                    (@Fin.cons mid.length (fun _ => Fin n) (v 0)
                        (WignerSupport.listPath mid zm.bound)) ∈
                       WignerSupport.leadPatterns mid.length ∧
                    WignerSupport.wordPattern
                    (@Fin.cons rest.length (fun _ => Fin n) i
                        (WignerSupport.listPath rest zr.bound)) ∈
                       WignerSupport.leadPatterns rest.length
              have lp := hpieceLead n a i v z t ht
              change WignerSupport.IsLeadingPath (v 0)
                    (WignerSupport.listPath mid zm.bound) ∧
                  WignerSupport.IsLeadingPath i
                    (WignerSupport.listPath rest zr.bound) at lp
              constructor
              · apply WignerSupport.wordPattern_mem_of_leading
                    (@Fin.cons mid.length (fun _ => Fin n)
                      (v 0) (WignerSupport.listPath mid zm.bound))
                unfold WignerSupport.IsLeadingWord
                simpa [Fin.tail_cons] using lp.1
              · apply WignerSupport.wordPattern_mem_of_leading
                    (@Fin.cons rest.length (fun _ => Fin n)
                      i (WignerSupport.listPath rest zr.bound))
                unfold WignerSupport.IsLeadingWord
                simpa [Fin.tail_cons] using lp.2
            /- The open pieces are now genuine smaller leading paths.  What
               remains at this single finite coefficient is their quotient by
               the roots and disjoint alphabets: normalise each root-word by
               first occurrences (using `leadPatterns`) and graft them back
               across their first-return bridge.  That bijection gives the
               Catalan recursion for the unlabelled coefficient; after that
               one still needs the standard doubled-walk variance/concentration
               estimate for the bounded trace. -/
            -- Besides being closed leading pieces, the two alphabets
            -- really are separate *on the nose*.  This is stronger than just
            -- their edge images being disjoint.  It is the input needed to
            -- glue equality patterns: otherwise a child letter could
            -- accidentally equal a root letter after relabelling.
            have hpieceRanges (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                let mid : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).take t.val
                let rest : List ℕ :=
                    (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
                let zm : WignerSupport.ClosedEqPiece n (v 0) mid :=
                    (WignerSupport.leading_split_closedEqPieces i v z t ht).1
                let zr : WignerSupport.ClosedEqPiece n i rest :=
                    (WignerSupport.leading_split_closedEqPieces i v z t ht).2
                Disjoint
                  (Set.range (@Fin.cons mid.length (fun _ => Fin n) (v 0)
                    (WignerSupport.listPath mid zm.bound)))
                  (Set.range (@Fin.cons rest.length (fun _ => Fin n) i
                    (WignerSupport.listPath rest zr.bound))) := by
              dsimp
              let mid : List ℕ :=
                   (WignerSupport.pathList (Fin.tail v)).take t.val
              let rest : List ℕ :=
                   (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
              have pcs := WignerSupport.leading_split_closedEqPieces i v z t ht
              change WignerSupport.ClosedEqPiece n (v 0) mid ∧
                    WignerSupport.ClosedEqPiece n i rest at pcs
              let zm : WignerSupport.ClosedEqPiece n (v 0) mid := pcs.1
              let zr : WignerSupport.ClosedEqPiece n i rest := pcs.2
              change Disjoint
                  (Set.range (@Fin.cons mid.length (fun _ => Fin n) (v 0)
                    (WignerSupport.listPath mid zm.bound)))
                  (Set.range (@Fin.cons rest.length (fun _ => Fin n) i
                    (WignerSupport.listPath rest zr.bound)))
              apply WignerSupport.disjoint_ranges_cons_listPath
              have hb := WignerSupport.leading_split_vertices_disjoint i v z t ht
              change Disjoint
                (WignerSupport.walkVertices (v 0).val mid)
                (WignerSupport.walkVertices i.val rest) at hb
              exact hb
            -- There is no ambiguity about the word reconstructed from the
            -- two pieces. The returning bridge contributes the root again.
            -- This literal list identity is useful because pieces of length
            -- zero do occur in the Catalan boundary terms.
            have hsplitWord (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                i.val :: WignerSupport.pathList v =
                  i.val :: (v 0).val ::
                    ((WignerSupport.pathList (Fin.tail v)).take t.val ++
                      i.val :: (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)) := by
              exact WignerSupport.leading_split_word_list i v z t ht
            -- Abstractly, gluing equality patterns along such separated
            -- alphabets is lossless. This finite lemma works even when
            -- either smaller piece is empty; the two copies of the old root
            -- receive the same root tag.
            have hpieceLengths (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (t : Fin a) :
                ((WignerSupport.pathList (Fin.tail v)).take t.val).length = t.val ∧
                ((WignerSupport.pathList (Fin.tail v)).drop (t.val+1)).length =
                    a - (t.val+1) := by
              have le : t.val ≤ (WignerSupport.pathList (Fin.tail v)).length := by
                simp [WignerSupport.pathList]
              constructor
              · exact List.length_take_of_le le
              · simp [WignerSupport.pathList]
            have hpatGraft {n d m k : ℕ}
                (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
                (c' : Fin (m+1) → Fin d) (r' : Fin (k+1) → Fin d)
                (hc : WignerSupport.wordPattern c = WignerSupport.wordPattern c')
                (hr : WignerSupport.wordPattern r = WignerSupport.wordPattern r')
                (sep : Disjoint (Set.range c) (Set.range r))
                (sep' : Disjoint (Set.range c') (Set.range r')) :
                WignerSupport.wordPattern (WignerSupport.graftWord c r) =
                  WignerSupport.wordPattern (WignerSupport.graftWord c' r') := by
              exact WignerSupport.wordPattern_graft_of_disjoint c r c' r' hc hr sep sep'
            -- On finite words, not just their lists of numeral labels, the
            -- first-return decomposition is literally a graft.  The transport
            -- of `Fin` is indispensable here: the child and root can be empty
            -- and `length_take` is not a definitional equality.  In
            -- particular no injectivity of the ambient labels has been used.
            have hsplitGraft (n a : ℕ) (i : Fin n)
                (v : Fin (a+1) → Fin n) (z : WignerSupport.IsLeadingPath i v)
                (t : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val) :
                let mid : List ℕ :=
                  (WignerSupport.pathList (Fin.tail v)).take t.val
                let rest : List ℕ :=
                  (WignerSupport.pathList (Fin.tail v)).drop (t.val+1)
                let zm : WignerSupport.ClosedEqPiece n (v 0) mid :=
                  (WignerSupport.leading_split_closedEqPieces i v z t ht).1
                let zr : WignerSupport.ClosedEqPiece n i rest :=
                  (WignerSupport.leading_split_closedEqPieces i v z t ht).2
                let len : mid.length + rest.length + 3 = a + 2 := by
                  have h1 : mid.length = t.val := by
                    apply List.length_take_of_le
                    simp [WignerSupport.pathList]
                  have h2 : rest.length = a - (t.val+1) := by
                    simp [rest, WignerSupport.pathList]
                  omega
                (Fin.cons i v) =
                  (fun u : Fin (a+2) =>
                    WignerSupport.graftWord
                      (@Fin.cons mid.length (fun _ => Fin n) (v 0)
                        (WignerSupport.listPath mid zm.bound))
                      (@Fin.cons rest.length (fun _ => Fin n) i
                        (WignerSupport.listPath rest zr.bound))
                      (Fin.cast len.symm u)) := by
              exact WignerSupport.leading_split_word_eq_graft i v z t ht
            have hsplitPat {n d m k p : ℕ}
                (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
                (c' : Fin (m+1) → Fin d) (r' : Fin (k+1) → Fin d)
                (len : m+k+3=p)
                (hc : WignerSupport.wordPattern c = WignerSupport.wordPattern c')
                (hr : WignerSupport.wordPattern r = WignerSupport.wordPattern r')
                (sep : Disjoint (Set.range c) (Set.range r))
                (sep' : Disjoint (Set.range c') (Set.range r')) :
                WignerSupport.wordPattern
                    (fun u : Fin p =>
                      WignerSupport.graftWord c r (Fin.cast len.symm u)) =
                  WignerSupport.wordPattern
                    (fun u : Fin p =>
                      WignerSupport.graftWord c' r' (Fin.cast len.symm u)) := by
              exact WignerSupport.wordPattern_cast_graft_of_disjoint
                c r c' r' len hc hr sep sep'
            -- Conversely a pair of closed leading words on disjoint alphabets
            -- always makes a leading word after adjoining the bridge.  One has
            -- to repeat the bridge edge itself; this assertion is false for a
            -- naive concatenation that traverses it only once.  Thus at the
            -- single-coefficient obstruction both directions of the split are
            -- now exact, not only inclusion of their vertex sets.
            have hgraftLeading {n m k : ℕ}
                (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
                (hc : WignerSupport.IsLeadingWord m n c)
                (hr : WignerSupport.IsLeadingWord k n r)
                (sep : Disjoint (Set.range c) (Set.range r)) :
                  WignerSupport.IsLeadingWord (m+k+2) n
                     (WignerSupport.graftWord c r) := by
              exact WignerSupport.graftWord_isLeading c r hc hr sep
            have hgraftPattern {n m k : ℕ}
                (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
                (hc : WignerSupport.IsLeadingWord m n c)
                (hr : WignerSupport.IsLeadingWord k n r)
                (sep : Disjoint (Set.range c) (Set.range r)) :
                WignerSupport.wordPattern (WignerSupport.graftWord c r) ∈
                    WignerSupport.leadPatterns (m+k+2) := by
              exact WignerSupport.wordPattern_graft_mem c r hc hr sep
            -- Even the position of that bridge is intrinsic to a Boolean
            -- equality pattern.  Moving to a different labelled representative
            -- cannot change the index selected by `hfirstIndex`: compare the
            -- two positions as edges of the whole cons word first, and only
            -- then take their tails.
            have hreturnPattern {n d a : ℕ}
                (i : Fin n) (v : Fin (a+1) → Fin n)
                (i' : Fin d) (v' : Fin (a+1) → Fin d)
                (z : WignerSupport.IsLeadingPath i v)
                (z' : WignerSupport.IsLeadingPath i' v')
                (hp : WignerSupport.wordPattern (Fin.cons i v) =
                      WignerSupport.wordPattern (Fin.cons i' v'))
                (t s : Fin a)
                (ht : WignerSupport.pathEdgesNat (v 0) (Fin.tail v) t =
                    WignerSupport.edgeNat i.val (v 0).val)
                (hs : WignerSupport.pathEdgesNat (v' 0) (Fin.tail v') s =
                    WignerSupport.edgeNat i'.val (v' 0).val) : t = s := by
              exact WignerSupport.leading_return_index_eq_of_pattern
                i v i' v' z z' hp t s ht hs
            -- At a fixed child length the quotient operation is represented by
            -- a genuine map on the finite unlabelled sets.  Its definition
            -- uses two separated copies of the alphabets; thus it is valid even
            -- when either closed excursion has length zero.
            have hjoinInj (m k : ℕ) :
                Function.Injective
                  (fun z :
                    ({P // P ∈ WignerSupport.leadPatterns m}) ×
                      ({P // P ∈ WignerSupport.leadPatterns k}) =>
                    WignerSupport.joinPattern z.1 z.2) := by
              exact WignerSupport.joinPattern_injective
            have hjoinCard (m k : ℕ) :
                ((Finset.univ : Finset
                    (({P // P ∈ WignerSupport.leadPatterns m}) ×
                     ({P // P ∈ WignerSupport.leadPatterns k}))).image
                    (fun z => WignerSupport.joinPattern z.1 z.2)).card =
                  (WignerSupport.leadPatterns m).card *
                    (WignerSupport.leadPatterns k).card := by
              exact WignerSupport.card_image_joinPattern m k
            have hjoinWords {n m k : ℕ}
                (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
                (hc : WignerSupport.IsLeadingWord m n c)
                (hr : WignerSupport.IsLeadingWord k n r)
                (sep : Disjoint (Set.range c) (Set.range r)) :
                (WignerSupport.joinPattern
                  (⟨WignerSupport.wordPattern c,
                    WignerSupport.wordPattern_mem_of_leading c hc⟩ :
                    {P // P ∈ WignerSupport.leadPatterns m})
                  (⟨WignerSupport.wordPattern r,
                    WignerSupport.wordPattern_mem_of_leading r hr⟩ :
                    {P // P ∈ WignerSupport.leadPatterns k})).val =
                    WignerSupport.wordPattern (WignerSupport.graftWord c r) := by
              exact WignerSupport.joinPattern_of_words c r hc hr sep
            -- Different return times are disjoint even before summing the
            -- recursion.  This was a genuine positional issue: Boolean
            -- pattern equality is compared after transporting both words to
            -- the common length, and only then are the two tail indices
            -- compared.
            have hcodeInj (a : ℕ) : Function.Injective
                (@WignerSupport.codePattern a) := by
              exact WignerSupport.codePattern_injective a
            have hpatLower (a : ℕ) :
                (∑ t : Fin a,
                    (WignerSupport.leadPatterns t.val).card *
                      (WignerSupport.leadPatterns (a-(t.val+1))).card) ≤
                    (WignerSupport.leadPatterns (a+1)).card := by
              exact WignerSupport.sum_le_card_patterns a
            have hsplitJoin {a n : ℕ} (t : Fin a)
                (c : Fin (t.val+1) → Fin n)
                (r : Fin (a-(t.val+1)+1) → Fin n)
                (hc : WignerSupport.IsLeadingWord t.val n c)
                (hr : WignerSupport.IsLeadingWord (a-(t.val+1)) n r)
                (sep : Disjoint (Set.range c) (Set.range r)) :
                (WignerSupport.splitJoin a t
                  (⟨WignerSupport.wordPattern c,
                     WignerSupport.wordPattern_mem_of_leading c hc⟩)
                  (⟨WignerSupport.wordPattern r,
                     WignerSupport.wordPattern_mem_of_leading r hr⟩)).val =
                  WignerSupport.wordPattern
                    (WignerSupport.castWord
                      (congrArg (fun z : ℕ => z+1)
                        (WignerSupport.split_len a t))
                      (WignerSupport.graftWord c r)) := by
              exact WignerSupport.splitJoin_of_words t c r hc hr sep
            have hreturnCut {n d m k m' k' : ℕ}
                (eqLen : m+k+2 = m'+k'+2)
                (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
                (c' : Fin (m'+1) → Fin d) (r' : Fin (k'+1) → Fin d)
                (hc : WignerSupport.IsLeadingWord m n c)
                (hr : WignerSupport.IsLeadingWord k n r)
                (hc' : WignerSupport.IsLeadingWord m' d c')
                (hr' : WignerSupport.IsLeadingWord k' d r')
                (sep : Disjoint (Set.range c) (Set.range r))
                (sep' : Disjoint (Set.range c') (Set.range r'))
                (pat : WignerSupport.wordPattern (WignerSupport.graftWord c r) =
                  WignerSupport.wordPattern
                    (WignerSupport.castWord
                      (by omega : m'+k'+3=m+k+3)
                      (WignerSupport.graftWord c' r'))) : m = m' := by
              exact WignerSupport.graft_pattern_length_unique eqLen c r c' r'
                hc hr hc' hr' sep sep' pat
            have hjoinReturn {n m k : ℕ}
                (c : Fin (m+1) → Fin n) (r : Fin (k+1) → Fin n)
                (hc : WignerSupport.IsLeadingWord m n c) :
                let w : Fin (m+k+3) → Fin n :=
                    WignerSupport.graftWord c r
                WignerSupport.pathEdgesNat ((Fin.tail w) 0)
                    (Fin.tail (Fin.tail w))
                    (⟨m, by omega⟩ : Fin (m+k+1)) =
                  WignerSupport.edgeNat (w 0).val
                    ((Fin.tail w) 0).val := by
              exact WignerSupport.graft_return_index c r hc
            -- At this point the **injective** side of the unlabelled
            -- first-return recursion is an actual finite theorem, not a
            -- power bound.  `hpatLower` says the disjoint union of the two
            -- smaller pattern sets at all cut positions embeds in the big
            -- one (`hcodeInj`); `hsplitJoin` realizes the word attached to a
            -- pair and `hreturnCut` rules out a second cut.  What is not
            -- supplied by such an injection is the reverse inequality:
            -- every big pattern must be shown equal to the `splitJoin` of
            -- its two `take`/`drop` pieces.  When doing that transport one
            -- must cast `mid.length=t.val` and
            -- `rest.length=a-(t.val+1)` *before* forming the Boolean
            -- matrix.  Otherwise the pieces live in different finite
            -- position types and one silently proves only the labelled
            -- bound again.  After this surjectivity/Catalan coefficient the
            -- remaining bounded iid argument is the usual doubled-walk
            -- variance plus the a.s. upgrade.
            have hpatSurj (a : ℕ) :
                Function.Surjective (@WignerSupport.codePattern a) := by
              exact WignerSupport.codePattern_surjective a
            -- In particular the previously displayed lower bound is sharp:
            -- the return code is a bijection, not merely an embedding.  All
            -- proof obligations about `take`/`drop` casts live in the
            -- surjectivity lemma, so there is no ambient label count here.
            have hpatRec (a : ℕ) :
                (WignerSupport.leadPatterns (a+1)).card =
                  ∑ t : Fin a,
                    (WignerSupport.leadPatterns t.val).card *
                      (WignerSupport.leadPatterns (a-(t.val+1))).card := by
              exact WignerSupport.card_patterns_succ a
            have hpatCatalan (m : ℕ) :
                (WignerSupport.leadPatterns (2*m)).card = catalan m := by
              exact WignerSupport.card_patterns_even_catalan m
            -- Thus the finite, unlabelled obstruction is genuinely the
            -- Catalan coefficient.  The remaining positive-cutoff assertion
            -- in `hbounded` is no longer an enumeration statement; it is the
            -- variance/concentration upgrade for bounded trace monomials
            -- (and then the analytic moment/characteristic-function step).
            have traceMomentCat (m : ℕ) :
                Tendsto
                  (fun k : ℕ =>
                    (∫ w, Matrix.trace ((Ap (k+1) w)^(2*m)) ∂μ) /
                      (((k+1:ℕ):ℝ)^(m+1))) atTop
                  (𝓝 ((catalan m : ℝ) *
                     (WignerSupport.cutVariance μ X (R:ℝ))^m)) := by
              have tr := traceMoment (2*m) (by omega)
              have hh : (2*m)/2 = m := by omega
              simpa [hh, hpatCatalan m] using tr
            -- In the subsequent doubled-walk variance, disjoint edge
            -- alphabets cancel exactly.  This is stronger than simply bounding
            -- two expectations separately: it removes **all** independent
            -- pairs before any labelling estimate.
            have hpairDisjoint (n n' p q' : ℕ)
                (i : Fin n) (v : Fin p → Fin n)
                (j : Fin n') (u : Fin q' → Fin n')
                (dj : Disjoint
                  (Finset.univ.image (WignerSupport.pathEdgesNat i v))
                  (Finset.univ.image (WignerSupport.pathEdgesNat j u))) :
                (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
                     WignerSupport.pathTerm (fun b c : Fin n' =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) q' j u ∂μ) =
                  (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
                  (∫ a, WignerSupport.pathTerm (fun b c : Fin n' =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) q' j u ∂μ) := by
              exact WignerSupport.integral_mul_pathTerm_of_disjoint
                μ Y Ym Yedge n n' p q' i v j u dj
            -- There is a second cancellation which is just as important as
            -- disjointness.  In a doubled word the relevant fibre is the *sum*
            -- of the two multiplicities.  A singleton in that union has mean
            -- zero, and one of the two individual factors has mean zero too;
            -- hence it kills covariance exactly.  Counting all labelled pairs
            -- before this pruning loses another full power of `n`.
            have hpairSingleton (n p q' : ℕ)
                (i : Fin n) (v : Fin p → Fin n)
                (j : Fin n) (u : Fin q' → Fin n)
                (e : {z : ℕ × ℕ // z.1 ≤ z.2})
                (he : e ∈ WignerSupport.pairEdges i v j u)
                (one :
                  ((Finset.univ : Finset (Fin p)).filter
                    (fun r => WignerSupport.pathEdgesNat i v r = e)).card +
                  ((Finset.univ : Finset (Fin q')).filter
                    (fun r => WignerSupport.pathEdgesNat j u r = e)).card = 1) :
                (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
                     WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) q' j u ∂μ) -
                  (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
                  (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) q' j u ∂μ) = 0 := by
              exact WignerSupport.covariance_pathTerm_zero_of_unique_union
                μ Y Ym Yedge Yzero n p q' i v j u e he one
            -- The elementary graph count for a doubled word is now honest.
            -- If the edge alphabets meet, the union graph is connected (loops
            -- may simply be skipped). Thus it has at most `#edges+1`
            -- vertices. This statement uses the two roots; conflating them is
            -- an incorrect variance argument for nonmatching walks.
            have hpairConnected (n p q' : ℕ)
                (i : Fin n) (v : Fin p → Fin n)
                (j : Fin n) (u : Fin q' → Fin n)
                (hh : (Finset.univ.image (WignerSupport.pathEdgesNat i v) ∩
                       Finset.univ.image (WignerSupport.pathEdgesNat j u)).Nonempty) :
                (WignerSupport.pairVertices i v j u).card ≤
                   (WignerSupport.pairEdges i v j u).card + 1 := by
              exact WignerSupport.card_pairVertices_le_edges_add_one_of_edge
                i v j u hh
            have hpairHalf (n p q' : ℕ)
                (i : Fin n) (v : Fin p → Fin n)
                (j : Fin n) (u : Fin q' → Fin n)
                (two : ∀ e ∈ WignerSupport.pairEdges i v j u,
                   2 ≤ ((Finset.univ : Finset (Fin p)).filter
                          (fun r => WignerSupport.pathEdgesNat i v r = e)).card +
                       ((Finset.univ : Finset (Fin q')).filter
                          (fun r => WignerSupport.pathEdgesNat j u r = e)).card) :
                (WignerSupport.pairEdges i v j u).card ≤ (p+q')/2 := by
              exact WignerSupport.card_pairEdges_le_half_of_union i v j u two
            -- For *closed* trace words the apparent top stratum drops
            -- once more.  A tight connected pair would be a tree; each
            -- component is then a closed equality walk, so its common edge
            -- is traversed again within that component.  The common union
            -- fibre has four positions and contradicts the half-edge
            -- budget.  Notice the two closure hypotheses: without them the
            -- earlier `p+1` bound really is sharp.
            have hpairVertTight (n p : ℕ)
                (i : Fin n) (v : Fin p → Fin n)
                (j : Fin n) (u : Fin p → Fin n)
                (ci : WignerSupport.pathEnd p i v = i)
                (cj : WignerSupport.pathEnd p j u = j)
                (hh : (Finset.univ.image (WignerSupport.pathEdgesNat i v) ∩
                       Finset.univ.image (WignerSupport.pathEdgesNat j u)).Nonempty)
                (two : ∀ e ∈ WignerSupport.pairEdges i v j u,
                   2 ≤ ((Finset.univ : Finset (Fin p)).filter
                          (fun r => WignerSupport.pathEdgesNat i v r = e)).card +
                       ((Finset.univ : Finset (Fin p)).filter
                          (fun r => WignerSupport.pathEdgesNat j u r = e)).card) :
                (WignerSupport.pairVertices i v j u).card ≤ p := by
              exact WignerSupport.card_pairVertices_le_p_of_closed
                 i v j u ci cj hh two
            -- Combining the two deterministic facts leaves at most `p+1`
            -- labels for a surviving covariance of two `p`-step walks.  The
            -- labelling estimate again factors through the finite image; it
            -- is `n^(p+1)`, not `n^(2p+2)`.
            have hpairVert (n p : ℕ)
                (i : Fin n) (v : Fin p → Fin n)
                (j : Fin n) (u : Fin p → Fin n)
                (hh : (Finset.univ.image (WignerSupport.pathEdgesNat i v) ∩
                       Finset.univ.image (WignerSupport.pathEdgesNat j u)).Nonempty)
                (two : ∀ e ∈ WignerSupport.pairEdges i v j u,
                   2 ≤ ((Finset.univ : Finset (Fin p)).filter
                          (fun r => WignerSupport.pathEdgesNat i v r = e)).card +
                       ((Finset.univ : Finset (Fin p)).filter
                          (fun r => WignerSupport.pathEdgesNat j u r = e)).card) :
                (WignerSupport.pairVertices i v j u).card ≤ p+1 := by
              have a := hpairConnected n p p i v j u hh
              have b := hpairHalf n p p i v j u two
              have id : (p+p)/2 = p := by omega
              omega
            have hpairLabels (n p d : ℕ) :
                ((Finset.univ : Finset
                  ((Fin n × (Fin p → Fin n)) ×
                   (Fin n × (Fin p → Fin n)))).filter
                  (fun z => (WignerSupport.pairVertices
                       z.1.1 z.1.2 z.2.1 z.2.2).card ≤ d)).card ≤
                    n^d * d^((p+1)+(p+1)) := by
              exact WignerSupport.card_filter_small_pair_vertices
                (n:=n) (p:=p) (q:=p) (d:=d)
            -- No analytic estimate was used in the cancellations. For the
            -- remaining summands it is enough to keep this robust bound; it
            -- follows from the pointwise cut, without any moment above the
            -- cutoff.
            have hpairBound (n p q' : ℕ)
                (i : Fin n) (v : Fin p → Fin n)
                (j : Fin n) (u : Fin q' → Fin n) :
                |(∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
                     WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) q' j u ∂μ) -
                  (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
                  (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) q' j u ∂μ)| ≤
                    2 * B^(p+q') := by
              exact WignerSupport.abs_covariance_pathTerm_le
                μ Y B B0 Yb n p q' i v j u
            -- These facts can already be used for an exact *support*
            -- statement for the doubled covariance.  Thus the pending power
            -- improvement really concerns only the connected top stratum,
            -- not a cloud of singleton/disconnected words.
            have hpairOutside (n p : ℕ)
                (i : Fin n) (v : Fin p → Fin n)
                (j : Fin n) (u : Fin p → Fin n)
                (big : ¬ (WignerSupport.pairVertices i v j u).card ≤ p+1) :
                (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
                     WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ) -
                  (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
                  (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ) = 0 := by
              classical
              by_cases dj : Disjoint
                    (Finset.univ.image (WignerSupport.pathEdgesNat i v))
                    (Finset.univ.image (WignerSupport.pathEdgesNat j u))
              · rw [hpairDisjoint n n p p i v j u dj]
                ring
              · have meet : (Finset.univ.image
                         (WignerSupport.pathEdgesNat i v) ∩
                         Finset.univ.image
                         (WignerSupport.pathEdgesNat j u)).Nonempty :=
                        Finset.not_disjoint_iff_nonempty_inter.mp dj
                by_cases every : ∀ e ∈ WignerSupport.pairEdges i v j u,
                       2 ≤ ((Finset.univ : Finset (Fin p)).filter
                              (fun r => WignerSupport.pathEdgesNat i v r = e)).card +
                           ((Finset.univ : Finset (Fin p)).filter
                              (fun r => WignerSupport.pathEdgesNat j u r = e)).card
                · exact False.elim (big (hpairVert n p i v j u meet every))
                · push_neg at every
                  rcases every with ⟨e, he, lt⟩
                  have lo := WignerSupport.one_le_pair_fiber i v j u e he
                  have on :
                       ((Finset.univ : Finset (Fin p)).filter
                              (fun r => WignerSupport.pathEdgesNat i v r = e)).card +
                           ((Finset.univ : Finset (Fin p)).filter
                              (fun r => WignerSupport.pathEdgesNat j u r = e)).card = 1 := by
                        omega
                  exact hpairSingleton n p p i v j u e he on
            -- On closed trace summands this is a strict cut, not the crude
            -- `p+1` one: the tight common tree has been excluded above.
            have hpairClosedOutside (n p : ℕ)
                (i : Fin n) (v : Fin p → Fin n)
                (j : Fin n) (u : Fin p → Fin n)
                (ci : WignerSupport.pathEnd p i v = i)
                (cj : WignerSupport.pathEnd p j u = j)
                (big : ¬ (WignerSupport.pairVertices i v j u).card ≤ p) :
                (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v *
                     WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ) -
                  (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p i v ∂μ) *
                  (∫ a, WignerSupport.pathTerm (fun b c : Fin n =>
                       Y (min (b:ℕ) c) (max (b:ℕ) c) a) p j u ∂μ) = 0 := by
              exact WignerSupport.covariance_pathTerm_zero_of_big_closed
                 μ Y Ym Yedge Yzero n p i v j u ci cj big
            -- The finite summation estimate is packaged after the tight-tree cut;
            -- its normalisation is `n^p`, two powers below the square trace.
            have hpairVariance (n p : ℕ) :=
              WignerSupport.abs_sum_cov_closed_le
                μ Y Ym Yedge Yzero B B0 Yb n p
            -- In particular the feared connected-tree stratum is now gone
            -- on closed trace summands (`hpairClosedOutside`): a shared bridge
            -- occurs twice in each component of a tight pair tree.  Its four
            -- positions contradict the half-edge budget. `hpairVariance`
            -- records the resulting `n^p` summable variance bound as an
            -- actual finite sum. The remaining bounded-cutoff theorem is the
            -- analytic/concentration upgrade from these fixed trace moments
            -- to characteristic functions (polynomial approximation).
            have rootAp (n s : ℕ) (x : Ω) :
                WignerSupport.rootedTrace Y n s x =
                   Matrix.trace ((Ap n x)^s) := by
              rfl
            -- Square summability uses the genuine normalization
            -- `n * (√n)^p`.  At odd orders replacing this by `n^(p/2+1)`
            -- would only give a harmonic variance, so Borel--Cantelli would
            -- not apply.
            have hfluct (p : ℕ) :
                ∀ᵐ w ∂μ,
                  Tendsto
                    (fun k : ℕ =>
                      Matrix.trace ((Ap (k+1) w)^p) /
                          WignerSupport.traceScale (k+1) p -
                        ∫ x, Matrix.trace ((Ap (k+1) x)^p) /
                          WignerSupport.traceScale (k+1) p ∂μ)
                    atTop (𝓝 (0:ℝ)) := by
              have h := WignerSupport.ae_normalized_rootedTrace_sub_mean
                  μ Y Ym Yedge Yzero B B0 Yb p
              simpa [rootAp] using h
            have hfluctAll :
                ∀ᵐ w ∂μ, ∀ p : ℕ,
                  Tendsto
                    (fun k : ℕ =>
                      Matrix.trace ((Ap (k+1) w)^p) /
                          WignerSupport.traceScale (k+1) p -
                        ∫ x, Matrix.trace ((Ap (k+1) x)^p) /
                          WignerSupport.traceScale (k+1) p ∂μ)
                    atTop (𝓝 (0:ℝ)) := by
              exact MeasureTheory.ae_all_iff.2 hfluct
            have meanEven (m : ℕ) :
                Tendsto
                  (fun k : ℕ =>
                    ∫ x, Matrix.trace ((Ap (k+1) x)^(2*m)) /
                      WignerSupport.traceScale (k+1) (2*m) ∂μ)
                  atTop
                  (𝓝 ((catalan m : ℝ) *
                    (WignerSupport.cutVariance μ X (R:ℝ))^m)) := by
              have tr := traceMomentCat m
              convert tr using 1
              funext k
              -- pull the deterministic scale out of the Bochner integral
              simp only [WignerSupport.traceScale_even, div_eq_mul_inv]
              rw [MeasureTheory.integral_mul_const]
            have invSqrt : Tendsto
                (fun k : ℕ => (Real.sqrt ((k+1:ℕ):ℝ))⁻¹)
                atTop (𝓝 (0:ℝ)) := by
              have castTop : Tendsto (fun k : ℕ => ((k+1:ℕ):ℝ))
                    atTop atTop := by
                exact (tendsto_natCast_atTop_atTop (R:=ℝ)).comp
                    (Filter.tendsto_add_atTop_nat 1)
              have sqTop := Real.tendsto_sqrt_atTop.comp castTop
              exact tendsto_inv_atTop_zero.comp sqTop
            have meanOdd (m : ℕ) :
                Tendsto
                  (fun k : ℕ =>
                    ∫ x, Matrix.trace ((Ap (k+1) x)^(2*m+1)) /
                       WignerSupport.traceScale (k+1) (2*m+1) ∂μ)
                  atTop (𝓝 (0:ℝ)) := by
              have ho : ¬ 2 ∣ (2*m+1) := by omega
              have tr := traceOdd (2*m+1) ho
              have hh : (2*m+1)/2 = m := by omega
              have tr' : Tendsto
                  (fun k : ℕ =>
                    (∫ w, Matrix.trace ((Ap (k+1) w)^(2*m+1)) ∂μ) /
                         (((k+1:ℕ):ℝ)^(m+1)))
                    atTop (𝓝 (0:ℝ)) := by
                simpa [hh] using tr
              have both := tr'.mul invSqrt
              have final : Tendsto
                  (fun k : ℕ =>
                    ((∫ w, Matrix.trace ((Ap (k+1) w)^(2*m+1)) ∂μ) /
                         (((k+1:ℕ):ℝ)^(m+1))) *
                       (Real.sqrt ((k+1:ℕ):ℝ))⁻¹)
                    atTop (𝓝 (0:ℝ)) := by simpa using both
              convert final using 1
              funext k
              simp only [WignerSupport.traceScale_odd, div_eq_mul_inv]
              rw [MeasureTheory.integral_mul_const]
              have nz : (((k+1:ℕ):ℝ)^(m+1)) ≠ 0 := by positivity
              have ns : (Real.sqrt ((k+1:ℕ):ℝ)) ≠ 0 := by positivity
              field_simp
            have hmoment : ∀ᵐ w ∂μ, ∀ m : ℕ,
                (Tendsto
                  (fun k : ℕ => Matrix.trace ((Ap (k+1) w)^(2*m)) /
                     WignerSupport.traceScale (k+1) (2*m))
                  atTop (𝓝 ((catalan m : ℝ) *
                    (WignerSupport.cutVariance μ X (R:ℝ))^m))) ∧
                (Tendsto
                  (fun k : ℕ => Matrix.trace ((Ap (k+1) w)^(2*m+1)) /
                     WignerSupport.traceScale (k+1) (2*m+1))
                  atTop (𝓝 (0:ℝ))) := by
              filter_upwards [hfluctAll] with w hw
              intro m
              constructor
              · have fl := hw (2*m)
                have ad := fl.add (meanEven m)
                convert ad using 1
                · funext k
                  ring
                · ring
              · have fl := hw (2*m+1)
                have ad := fl.add (meanOdd m)
                convert ad using 1
                · funext k
                  ring
                · ring
            have diagReal (n p : ℕ) (w : Ω) :
                (∑ i : Fin n,
                    ((wignerMatrix_isHermitian Y n w).eigenvalues i)^p) =
                  Matrix.trace ((Ap n w)^p) := by
              have cEntry : ∀ r : ℕ, ∀ a b : Fin n,
                  ((((Ap n w)^r) a b : ℝ) : ℂ) =
                    (((wignerMatrix Y n w)^r) a b) := by
                intro r
                induction r with
                | zero =>
                    intro a b
                    by_cases h : a = b
                    · subst b; simp
                    · simp [h]
                | succ r ih =>
                    intro a b
                    rw [pow_succ, pow_succ]
                    simp only [Matrix.mul_apply]
                    push_cast
                    apply Finset.sum_congr rfl
                    intro k hk
                    rw [ih a k, show
                         (((Ap n w) k b : ℝ) : ℂ) =
                           (wignerMatrix Y n w) k b by rfl]
              have cTrace :
                  (((Matrix.trace ((Ap n w)^p) : ℝ)) : ℂ) =
                    Matrix.trace ((wignerMatrix Y n w)^p) := by
                simp only [Matrix.trace, Matrix.diag]
                push_cast
                apply Finset.sum_congr rfl
                intro k hk
                exact cEntry p k k
              have d := hdiag n p w
              -- both sides of the complex spectral identity are the casts of
              -- the preceding real numbers
              apply Complex.ofReal_inj.mp
              calc
                ((∑ i : Fin n,
                    ((wignerMatrix_isHermitian Y n w).eigenvalues i)^p : ℝ) : ℂ)
                    = ∑ i : Fin n,
                        (((wignerMatrix_isHermitian Y n w).eigenvalues i : ℂ)^p) := by
                          simp
                _ = Matrix.trace ((wignerMatrix Y n w)^p) := d
                _ = ((Matrix.trace ((Ap n w)^p) : ℝ) : ℂ) := cTrace.symm
            have empPow (n p : ℕ) (w : Ω) (hn : 0 < n) :
                (n:ℝ)⁻¹ *
                    (∑ j : Fin n,
                       ((wignerMatrix_isHermitian Y n w).eigenvalues j /
                          Real.sqrt n)^p) =
                  Matrix.trace ((Ap n w)^p) /
                      WignerSupport.traceScale n p := by
              have nz : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
              have ns : Real.sqrt (n:ℝ) ≠ 0 := by positivity
              have nsp : (Real.sqrt (n:ℝ))^p ≠ 0 := pow_ne_zero _ ns
              simp_rw [div_pow]
              simp_rw [div_eq_mul_inv]
              rw [← Finset.sum_mul]
              rw [diagReal n p w]
              unfold WignerSupport.traceScale
              field_simp
              <;> ring
            have hspectral : ∀ᵐ w ∂μ, ∀ m : ℕ,
                (Tendsto
                  (fun k : ℕ =>
                    (((k+1:ℕ):ℝ))⁻¹ *
                      (∑ j : Fin (k+1),
                          ((wignerMatrix_isHermitian Y (k+1) w).eigenvalues j /
                             Real.sqrt (k+1))^(2*m)))
                  atTop (𝓝 ((catalan m : ℝ) *
                    (WignerSupport.cutVariance μ X (R:ℝ))^m))) ∧
                (Tendsto
                  (fun k : ℕ =>
                    (((k+1:ℕ):ℝ))⁻¹ *
                      (∑ j : Fin (k+1),
                          ((wignerMatrix_isHermitian Y (k+1) w).eigenvalues j /
                             Real.sqrt (k+1))^(2*m+1)))
                  atTop (𝓝 (0:ℝ))) := by
              filter_upwards [hmoment] with w hw
              intro m
              rcases hw m with ⟨he, ho⟩
              constructor
              · convert he using 1
                funext k
                simpa [Nat.cast_add, Nat.cast_one] using (empPow (k+1) (2*m) w (by omega))
              · convert ho using 1
                funext k
                simpa [Nat.cast_add, Nat.cast_one] using (empPow (k+1) (2*m+1) w (by omega))
            -- The stochastic part is now completely removed.  What is left
            -- is a deterministic method-of-moments lemma for triangular
            -- empirical measures on the line.  It includes the identification
            -- of the semicircle moments (and their dilates).  Notice that no
            -- measurability or independence occurs in its formulation.
            have moment_to_char : ∀ (σ t : ℝ), 0 ≤ σ →
                ∀ a : ∀ k : ℕ, Fin (k+1) → ℝ,
                (∀ m : ℕ, Tendsto
                   (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹ *
                       (∑ j : Fin (k+1), (a k j)^(2*m)))
                   atTop (𝓝 ((catalan m : ℝ) * σ^m))) →
                (∀ m : ℕ, Tendsto
                   (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹ *
                       (∑ j : Fin (k+1), (a k j)^(2*m+1)))
                   atTop (𝓝 (0:ℝ))) →
                Tendsto
                   (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹ •
                     (∑ j : Fin (k+1),
                       Complex.exp ((((a k j * t : ℝ)) : ℂ) * Complex.I)))
                   atTop (𝓝 (MeasureTheory.charFun semicircleLaw
                      (Real.sqrt σ * t))) := by
              intro σ t hσ a he ho
              -- Convergence of moments immediately gives deterministic
              -- eventual bounds at every even order.  These are the tail
              -- estimates one needs before using Weierstrass on a compact
              -- interval; without them polynomial approximation of the
              -- character on all of `ℝ` would be invalid.
              have evenBound (m : ℕ) : ∀ᶠ k : ℕ in atTop,
                  (((k+1:ℕ):ℝ))⁻¹ *
                       (∑ j : Fin (k+1), (a k j)^(2*m)) <
                    (catalan m : ℝ) * σ^m + 1 := by
                have h := he m
                exact h (Iio_mem_nhds (lt_add_one _))
              have sqBound : ∀ᶠ k : ℕ in atTop,
                  (((k+1:ℕ):ℝ))⁻¹ *
                        (∑ j : Fin (k+1), (a k j)^2) < σ + 1 := by
                have b := evenBound 1
                simpa using b
              -- extraction beyond `sqBound` is entirely deterministic: use
              -- higher `evenBound` to throw away `|x|>D`, approximate
              -- `exp (itx)` by polynomials on `[-D,D]`, then let `D→∞`;
              -- one also identifies the compactly-supported target moments
              -- `Catalan m * σ^m` from the semicircle density.
              -- The target moments themselves require a genuine interval integral.  In
              -- particular they are not consequences of its total mass: the square
              -- root density at the end-points has to be handled by a sine
              -- substitution.  Keeping these two identities here makes the remaining
              -- step a purely deterministic approximation theorem.
              have semi_def : semicircleLaw = WignerSupport.semicircleConcrete := by
                rfl
              have semiEven (m : ℕ) :
                  (∫ x : ℝ, x^(2*m) ∂semicircleLaw) = (catalan m : ℝ) := by
                rw [semi_def]
                exact WignerSupport.semicircleConcrete_moment_even m
              have semiOdd (m : ℕ) :
                  (∫ x : ℝ, x^(2*m+1) ∂semicircleLaw) = (0:ℝ) := by
                rw [semi_def]
                exact WignerSupport.semicircleConcrete_moment_odd m
              have semiInt (p : ℕ) : Integrable (fun x : ℝ => x^p) semicircleLaw := by
                -- with density on a compact interval; reduce to a continuous
                -- bounded-weight function on that interval
                rw [semi_def]
                unfold WignerSupport.semicircleConcrete
                rw [integrable_withDensity_iff]
                · constructor
                  · -- strongly measurable for the restricted carrier
                    fun_prop
                  · -- finite weighted norm integral follows by compactness
                    have hp : Integrable
                        (fun x : ℝ => x^p *
                          (Real.sqrt (4-x^2)/(2*Real.pi)))
                        (volume.restrict (Set.Icc (-2:ℝ) 2)) :=
                          WignerSupport.integrable_semipoly p
                    -- the scalar norm has the same absolute value
                    have hn (x : ℝ) : 0 ≤ Real.sqrt (4-x^2)/(2*Real.pi) := by positivity
                    simpa [HasFiniteIntegral, Real.norm_eq_abs,
                      ENNReal.toReal_ofReal (hn _)]
                      using hp.hasFiniteIntegral
                · fun_prop
                · exact Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
              -- scaling the target by `√σ` gives exactly the moments on the
              -- right of the triangular array.  This is the last piece of
              -- measure theory needed by the remaining analytic approximation.
              have targetEven (m : ℕ) :
                  (∫ x : ℝ, (Real.sqrt σ * x)^(2*m) ∂semicircleLaw) =
                    (catalan m : ℝ) * σ^m := by
                simp_rw [mul_pow]
                rw [MeasureTheory.integral_const_mul]
                rw [semiEven m]
                rw [show (Real.sqrt σ)^(2*m) = σ^m by
                  rw [pow_mul, Real.sq_sqrt hσ]]
                ring
              have targetOdd (m : ℕ) :
                  (∫ x : ℝ, (Real.sqrt σ * x)^(2*m+1) ∂semicircleLaw) =
                    (0:ℝ) := by
                simp_rw [mul_pow]
                rw [MeasureTheory.integral_const_mul]
                rw [semiOdd m]
                simp
              -- Remaining active hole: analytic Taylor/polynomial approximation for
              -- these deterministic finite empirical rows.  All moments of the
              -- compactly supported target have now been computed in the kernel;
              -- the open step contains no random variables or density calculation.
              -- A quantitative deterministic reduction.  The following estimate makes the
              -- usual "polynomial approximation" legitimate for these unbounded rows:
              -- outside a compact interval a fixed Taylor polynomial is paid for by a
              -- *single higher even moment*.  In particular there is no (false)
              -- uniform bound on the largest entry of a row.
              have rowTaylor (N Q : ℕ) (hQ : N ≤ 2*Q) (D : ℝ)
                  (hD : 1 ≤ D)
                  (hN : |t| * D / ((N+1:ℕ):ℝ) ≤ (1:ℝ)/2)
                  (E : ℝ)
                  (hE : (|t| * D)^N / (N.factorial:ℕ) * 2 ≤ E) :
                  ∀ᶠ k : ℕ in atTop,
                    ‖(((k+1:ℕ):ℝ))⁻¹ •
                        (∑ j : Fin (k+1),
                          (Complex.exp (((((a k j)*t:ℝ):ℂ)*Complex.I)) -
                             WignerSupport.cpoly N t (a k j)))‖ ≤
                      E + (1 + (N:ℝ) * (|t|+1)^N * D^N) / D^(2*Q) *
                        ((catalan Q : ℝ) * σ^Q + 1) := by
                have eb := evenBound Q
                filter_upwards [eb] with k hk
                have one := WignerSupport.row_exp_poly_bound
                   N Q (k+1) (by omega) hQ t (a k) hD hN hE
                have coef0 : 0 ≤ (1 + (N:ℝ) * (|t|+1)^N * D^N) /
                       D^(2*Q) := by positivity
                exact one.trans (add_le_add_right
                  (mul_le_mul_of_nonneg_left (le_of_lt hk) coef0) E)
              -- The comparison integral lives on an actual compact set.  It
              -- is useful to record this at the level of `ae`: a density on a
              -- restricted measure cannot put mass outside the restriction.
              have targetSupport : ∀ᵐ x : ℝ ∂semicircleLaw,
                    |Real.sqrt σ * x| ≤ Real.sqrt σ * 2 := by
                rw [semi_def]
                unfold WignerSupport.semicircleConcrete
                have base : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Icc (-2:ℝ) 2)),
                       x ∈ Set.Icc (-2:ℝ) 2 :=
                    MeasureTheory.ae_restrict_mem (by exact measurableSet_Icc)
                have ac := MeasureTheory.withDensity_absolutelyContinuous
                  (volume.restrict (Set.Icc (-2:ℝ) 2))
                  (fun x : ℝ => ENNReal.ofReal
                    (Real.sqrt (4 - x ^ 2) / (2 * Real.pi)))
                filter_upwards [ac.ae_le base] with x hx
                have ha : |x| ≤ (2:ℝ) := (abs_le).2 ⟨by linarith [hx.1], hx.2⟩
                rw [abs_mul]
                rw [abs_of_nonneg (Real.sqrt_nonneg _)]
                rw [show (2:ℝ) = |(2:ℝ)| by norm_num]
                exact mul_le_mul_of_nonneg_left (by simpa using ha) (Real.sqrt_nonneg _)
              -- Compact part of the comparison integral, with its genuine
              -- factorial (a triangle bound by `exp |x|` is useless here).
              have targetTaylor (N : ℕ) (D E : ℝ)
                  (hD : Real.sqrt σ * 2 ≤ D)
                  (hN : |t| * D / ((N+1:ℕ):ℝ) ≤ (1:ℝ)/2)
                  (hE : (|t| * D)^N / (N.factorial:ℕ) * 2 ≤ E) :
                  ‖(∫ x : ℝ,
                       (Complex.exp (((((Real.sqrt σ*x)*t:ℝ):ℂ)*Complex.I)) -
                          WignerSupport.cpoly N t (Real.sqrt σ*x))
                        ∂semicircleLaw)‖ ≤ E := by
                have pt : ∀ᵐ x : ℝ ∂semicircleLaw,
                    ‖(Complex.exp (((((Real.sqrt σ*x)*t:ℝ):ℂ)*Complex.I)) -
                          WignerSupport.cpoly N t (Real.sqrt σ*x))‖ ≤ E := by
                  filter_upwards [targetSupport] with x hx
                  exact (WignerSupport.exp_poly_compact N t
                    (le_trans (by positivity : (0:ℝ) ≤ Real.sqrt σ * 2) hD)
                    (hx.trans hD) hN).trans hE
                calc
                  ‖(∫ x : ℝ,
                       (Complex.exp (((((Real.sqrt σ*x)*t:ℝ):ℂ)*Complex.I)) -
                          WignerSupport.cpoly N t (Real.sqrt σ*x))
                        ∂semicircleLaw)‖ ≤ ∫ _x : ℝ, E ∂semicircleLaw := by
                      exact MeasureTheory.norm_integral_le_of_norm_le
                        (integrable_const _) pt
                  _ = E := by simp
              -- Only a scalar epsilon chase (Taylor degree, then one higher
              -- moment) remains; all exchanges of sums and integrals have now
              -- got explicit quantitative bounds above.
              -- convergence of every power to the corresponding moment of the
              -- dilated compact law
              have powlim (l : ℕ) :
                  Tendsto (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹ *
                      (∑ j : Fin (k+1), (a k j)^l)) atTop
                    (𝓝 (∫ x : ℝ, (Real.sqrt σ*x)^l ∂semicircleLaw)) := by
                rcases Nat.even_or_odd l with evn | odd
                · rcases evn with ⟨m, hm⟩
                  have hmn : l = 2*m := by omega
                  simpa [hmn, targetEven m] using he m
                · rcases odd with ⟨m, hm⟩
                  have hmn : l = 2*m+1 := by omega
                  simpa [hmn, targetOdd m] using ho m
              have poly (N : ℕ) :
                  Tendsto (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹ •
                    (∑ j : Fin (k+1), WignerSupport.cpoly N t (a k j)))
                    atTop (𝓝 (∫ x : ℝ,
                      WignerSupport.cpoly N t (Real.sqrt σ*x)
                        ∂semicircleLaw)) := by
                have z := WignerSupport.tendsto_row_cpoly_of_moments
                    a (fun l => ∫ x : ℝ,
                       (Real.sqrt σ*x)^l ∂semicircleLaw) t powlim N
                rw [WignerSupport.integral_cpoly_eq N t (Real.sqrt σ)
                  semicircleLaw (fun l => by
                    have h := semiInt l
                    simpa [mul_pow] using h.const_mul ((Real.sqrt σ)^l))]
                exact z
              -- turn the quantitative estimates into convergence
              rw [Metric.tendsto_nhds]
              intro ε hε
              let D : ℝ := WignerSupport.momentRadius σ
              have dprops := WignerSupport.momentRadius_props hσ
              have d1 : 1 ≤ D := dprops.1
              have dsupp : Real.sqrt σ * 2 ≤ D := dprops.2.1
              have dp : 0 < D := dprops.2.2.1
              have dr1 : 4*σ / D^2 < (1:ℝ) :=
                lt_of_le_of_lt dprops.2.2.2.1 (by norm_num)
              have dr0 : 1 / D^2 < (1:ℝ) :=
                lt_of_le_of_lt dprops.2.2.2.2 (by norm_num)
              -- first fix the compact Taylor degree; this is the only place
              -- factorial growth is used.
              obtain ⟨N, hN, hsmall⟩ :=
                WignerSupport.exists_taylor_degree t D (ε/8) (by linarith)
              let E : ℝ := ε/8
              have Epos : 0 < E := by dsimp [E]; linarith
              have htarg := targetTaylor N D E dsupp hN hsmall
              -- for this fixed polynomial use a single higher even moment for
              -- the two tails.
              have tail0 := WignerSupport.polyTail_tendsto_zero
                  N t σ D hσ dp dr1 dr0
              have tailSmall : ∀ᶠ Q : ℕ in atTop,
                   (1 + (N:ℝ) * (|t|+1)^N * D^N) / D^(2*Q) *
                     ((catalan Q : ℝ) * σ^Q + 1) < ε/8 :=
                tail0 (Iio_mem_nhds (by linarith))
              have geN : ∀ᶠ Q : ℕ in atTop, N ≤ 2*Q := by
                filter_upwards [eventually_ge_atTop N] with Q hQ
                omega
              obtain ⟨Q, hQsmall, hQN⟩ := (tailSmall.and geN).exists
              have row := rowTaylor N Q hQN D d1 hN E hsmall
              have pc := (Metric.tendsto_nhds.1 (poly N)) (ε/4) (by linarith)
              filter_upwards [row, pc] with k hk hpk
              -- identify the target of the characteristic function as the
              -- complex integral used in the comparison estimate.
              have targetEq : MeasureTheory.charFun semicircleLaw
                    (Real.sqrt σ * t) =
                    ∫ x : ℝ, Complex.exp
                      (((((Real.sqrt σ*x)*t:ℝ):ℂ)*Complex.I))
                        ∂semicircleLaw := by
                  rw [MeasureTheory.charFun_apply]
                  congr 1
                  funext x
                  simp [mul_comm, mul_left_comm, mul_assoc]
              rw [targetEq]
              -- write the empirical mean minus the target integral as the
              -- sum of its row error, its polynomial error, and its compact
              -- target error.
              let u : ℂ := (((k+1:ℕ):ℝ))⁻¹ •
                    (∑ j : Fin (k+1),
                       Complex.exp ((((a k j * t : ℝ)) : ℂ) * Complex.I))
              let v : ℂ := (((k+1:ℕ):ℝ))⁻¹ •
                    (∑ j : Fin (k+1), WignerSupport.cpoly N t (a k j))
              let zc : ℂ := ∫ x : ℝ,
                    WignerSupport.cpoly N t (Real.sqrt σ*x)
                      ∂semicircleLaw
              let zz : ℂ := ∫ x : ℝ, Complex.exp
                      (((((Real.sqrt σ*x)*t:ℝ):ℂ)*Complex.I))
                        ∂semicircleLaw
              have uv : ‖u - v‖ ≤
                  E + (1 + (N:ℝ) * (|t|+1)^N * D^N) / D^(2*Q) *
                       ((catalan Q : ℝ) * σ^Q + 1) := by
                convert hk using 1
                -- finite sums and real smul commute with subtraction
                simp [u, v, Finset.sum_sub_distrib, smul_sub]
              have vz : dist v zc < ε/4 := by
                simpa [v, zc, dist_eq_norm] using hpk
              have zzb : ‖zz - zc‖ ≤ E := by
                have h := htarg
                -- integral of the difference equals difference of integrals;
                -- both terms are integrable (proved in `targetTaylor`).
                have cpint : Integrable (fun x : ℝ =>
                    WignerSupport.cpoly N t (Real.sqrt σ*x))
                      semicircleLaw := by
                  have ids : (fun x : ℝ => WignerSupport.cpoly N t (Real.sqrt σ*x)) =
                      (fun x : ℝ => ∑ l ∈ Finset.range N,
                        (((((t:ℝ):ℂ)*Complex.I)^l) / (l.factorial:ℕ)) *
                           ((((Real.sqrt σ*x)^l:ℝ):ℂ))) := by
                    funext x
                    exact WignerSupport.cpoly_as_sum N t _
                  rw [ids]
                  apply MeasureTheory.integrable_finset_sum (Finset.range N)
                  intro l hl
                  have rr : Integrable (fun x : ℝ => (Real.sqrt σ*x)^l)
                        semicircleLaw := by
                    simpa [mul_pow] using (semiInt l).const_mul ((Real.sqrt σ)^l)
                  exact (Complex.ofRealCLM.integrable_comp rr).const_mul _
                have exint : Integrable (fun x : ℝ => Complex.exp
                    (((((Real.sqrt σ*x)*t:ℝ):ℂ)*Complex.I)))
                      semicircleLaw := by
                  -- it has constant norm one
                  refine Integrable.mono' (integrable_const (1:ℝ)) (by fun_prop) ?_
                  filter_upwards [] with x
                  exact le_of_eq (WignerSupport.norm_exp_I t (Real.sqrt σ*x))
                rw [MeasureTheory.integral_sub exint cpint] at h
                simpa [zz, zc] using h
              have uvsmall : ‖u-v‖ < ε/4 := by
                calc
                  ‖u-v‖ ≤ E +
                    (1 + (N:ℝ) * (|t|+1)^N * D^N) / D^(2*Q) *
                       ((catalan Q : ℝ) * σ^Q + 1) := uv
                  _ < ε/4 := by dsimp [E]; linarith
              change dist u zz < ε
              calc
                dist u zz ≤ dist u v + dist v zz := dist_triangle _ _ _
                _ ≤ dist u v + (dist v zc + dist zc zz) := by
                      gcongr
                      exact dist_triangle _ _ _
                _ < ε := by
                  have A : dist u v < ε/4 := by simpa [dist_eq_norm] using uvsmall
                  have B : dist zc zz ≤ E := by
                    simpa [dist_eq_norm, norm_sub_rev] using zzb
                  dsimp [E] at B
                  linarith
            have σ0 : 0 ≤ WignerSupport.cutVariance μ X (R:ℝ) :=
              WignerSupport.cutVariance_nonneg μ X (R:ℝ)
                (_hX_meas 0 0) (_hX_int 0 0 (by omega))
                (_hX_sq_int 0 0 (by omega))
            filter_upwards [hspectral] with w hw
            let a : ∀ k : ℕ, Fin (k+1) → ℝ :=
              fun k j => (wignerMatrix_isHermitian Y (k+1) w).eigenvalues j /
                            Real.sqrt (k+1)
            have ev : ∀ m : ℕ, Tendsto
                (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹ *
                    (∑ j : Fin (k+1), (a k j)^(2*m))) atTop
                (𝓝 ((catalan m : ℝ) *
                  (WignerSupport.cutVariance μ X (R:ℝ))^m)) := by
              intro m
              exact (hw m).1
            have od : ∀ m : ℕ, Tendsto
                (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹ *
                    (∑ j : Fin (k+1), (a k j)^(2*m+1))) atTop
                (𝓝 (0:ℝ)) := by
              intro m
              exact (hw m).2
            have lim := moment_to_char
                (WignerSupport.cutVariance μ X (R:ℝ)) (q:ℝ) σ0 a ev od
            simpa [WignerSupport.eigenChar, a] using lim

        filter_upwards [htailall, hbounded] with ω hω hcutω
        -- Here the matrices `cutX R X` have genuinely bounded entries.
        -- The following identities are independent of any ordering of
        -- eigenvalues.  `hs_eigen_sub` uses the overlap of the two unitary
        -- eigenbases (a doubly stochastic matrix), rather than incorrectly
        -- subtracting corresponding, arbitrarily enumerated eigenvectors.
        have hentry (R n : ℕ) :
            WignerSupport.hsSq
                (wignerMatrix X n ω -
                  wignerMatrix (WignerSupport.cutX (R:ℝ) X) n ω) =
              ∑ i : Fin n, ∑ j : Fin n,
                (WignerSupport.tailX (R:ℝ) X
                   (min (i:ℕ) j) (max (i:ℕ) j) ω)^2 := by
            unfold WignerSupport.hsSq
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            simp only [wignerMatrix, Matrix.sub_apply]
            rw [← Complex.ofReal_sub, Complex.normSq_ofReal]
            rw [show X (min (i:ℕ) (j:ℕ)) (max (i:ℕ) (j:ℕ)) ω -
                WignerSupport.cutX (R:ℝ) X (min (i:ℕ) (j:ℕ))
                  (max (i:ℕ) (j:ℕ)) ω =
                WignerSupport.tailX (R:ℝ) X (min (i:ℕ) (j:ℕ))
                  (max (i:ℕ) (j:ℕ)) ω by
                 have := WignerSupport.add_tail_cut (R:ℝ) X
                    (min (i:ℕ) (j:ℕ)) (max (i:ℕ) (j:ℕ)) ω
                 linarith]
            ring
        have hover (R n : ℕ) :=
          WignerSupport.hs_eigen_sub
             (wignerMatrix_isHermitian X n ω)
             (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) n ω)
        have hspec (R n : ℕ) :
            (∑ i : Fin n, ∑ j : Fin n,
               WignerSupport.weight
                 (wignerMatrix_isHermitian X n ω)
                 (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) n ω)
                 i j *
                ((wignerMatrix_isHermitian X n ω).eigenvalues i -
                 (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) n ω).eigenvalues j)^2) =
             ∑ i : Fin n, ∑ j : Fin n,
                (WignerSupport.tailX (R:ℝ) X
                   (min (i:ℕ) j) (max (i:ℕ) j) ω)^2 := by
          exact (hover R n).symm.trans (hentry R n)
        have hraw (R n : ℕ) :
             (∑ i : Fin n, ∑ j : Fin n,
                WignerSupport.weight
                  (wignerMatrix_isHermitian X n ω)
                  (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) n ω)
                  i j *
                 ((wignerMatrix_isHermitian X n ω).eigenvalues i -
                  (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) n ω).eigenvalues j)^2) ≤
                2 * (∑ r ∈ Finset.range (n^2),
                     WignerSupport.upperSqSeq (WignerSupport.tailX (R:ℝ) X) r ω) := by
          rw [hspec]
          exact WignerSupport.square_sum_le_enum
             (WignerSupport.tailX (R:ℝ) X) ω n
        -- The remaining pointwise core is the bounded-cutoff moment (or
        -- resolvent) argument.  The preceding laws and overlap identity are
        -- precisely the finite-variance truncation inputs; no moment greater
        -- than two of the original entries is available.
        -- A deterministic comparison with the cutoff law.  Notice that no matching
        -- between the two eigenvalue enumerations is used here; the overlap matrix
        -- in `hs_eigen_sub` is doubly stochastic.  The small parameter version of
        -- the resulting bound is much easier to combine with finite second moments
        -- than an ordering of real eigenvalues would be.
        have hhs (R n : ℕ) :
            WignerSupport.hsSq
                (wignerMatrix X n ω -
                  wignerMatrix (WignerSupport.cutX (R:ℝ) X) n ω) ≤
              2 * (∑ r ∈ Finset.range (n^2),
                   WignerSupport.upperSqSeq
                     (WignerSupport.tailX (R:ℝ) X) r ω) := by
          calc
            WignerSupport.hsSq
                (wignerMatrix X n ω -
                  wignerMatrix (WignerSupport.cutX (R:ℝ) X) n ω) =
              (∑ i : Fin n, ∑ j : Fin n,
                WignerSupport.weight
                  (wignerMatrix_isHermitian X n ω)
                  (wignerMatrix_isHermitian
                    (WignerSupport.cutX (R:ℝ) X) n ω)
                  i j *
                   ((wignerMatrix_isHermitian X n ω).eigenvalues i -
                    (wignerMatrix_isHermitian
                      (WignerSupport.cutX (R:ℝ) X) n ω).eigenvalues j)^2) :=
                hover R n
            _ ≤ _ := hraw R n
        have hcomp (R n : ℕ) (hn : n ≠ 0) {d : ℝ} (hd : 0 < d) :
            ‖WignerSupport.eigenChar (wignerMatrix_isHermitian X n ω)
                  (q:ℝ) -
              WignerSupport.eigenChar
                (wignerMatrix_isHermitian
                  (WignerSupport.cutX (R:ℝ) X) n ω) (q:ℝ)‖ ≤
              (2 * |(q:ℝ)|) *
                ((((n:ℝ)⁻¹ * ((n:ℝ)⁻¹ *
                    (2 * (∑ r ∈ Finset.range (n^2),
                      WignerSupport.upperSqSeq
                        (WignerSupport.tailX (R:ℝ) X) r ω)))) /
                        (2*d)) + d/2) := by
          have e := WignerSupport.eigenChar_sub_le_eps (n := n) hn
            (wignerMatrix_isHermitian X n ω)
            (wignerMatrix_isHermitian
              (WignerSupport.cutX (R:ℝ) X) n ω) (q:ℝ) hd
          refine e.trans ?_
          have non : 0 ≤ (2 * |(q:ℝ)|) := by positivity
          apply mul_le_mul_of_nonneg_left ?_ non
          have den : 0 ≤ (2*d:ℝ) := by positivity
          have hinv : 0 ≤ (n:ℝ)⁻¹ := by positivity
          have main :
              (n:ℝ)⁻¹ * ((n:ℝ)⁻¹ *
                WignerSupport.hsSq
                  (wignerMatrix X n ω -
                    wignerMatrix (WignerSupport.cutX (R:ℝ) X) n ω)) ≤
              (n:ℝ)⁻¹ * ((n:ℝ)⁻¹ *
                (2 * (∑ r ∈ Finset.range (n^2),
                   WignerSupport.upperSqSeq
                     (WignerSupport.tailX (R:ℝ) X) r ω))) := by
            gcongr
            exact hhs R n
          gcongr
        -- The normalized quantity on the right really is a tail *mean* (there are
        -- `n²` entries).  Substituting `m=(k+1)²` in the enumerated strong law is
        -- a slightly delicate cofinality point; it is useful to record it here so
        -- that the remaining moment argument cannot silently use `n` in place of
        -- `n²`.
        have hsqmono : StrictMono (fun k : ℕ => (k+1)^2) := by
          apply strictMono_nat_of_lt_succ
          intro k
          calc
            (k+1)^2 < (k+1)^2 + (2*(k+1)+1) := by omega
            _ = (k+1+1)^2 := by ring
        have hnorm (R : ℕ) : Tendsto
            (fun k : ℕ =>
              (((k+1 : ℕ):ℝ)⁻¹ * (((k+1 : ℕ):ℝ)⁻¹ *
                (2 * (∑ r ∈ Finset.range ((k+1)^2),
                  WignerSupport.upperSqSeq
                    (WignerSupport.tailX (R:ℝ) X) r ω)))))
              atTop (𝓝 (2 * WignerSupport.tailMean μ X (R:ℝ))) := by
          have base := (hω R).comp hsqmono.tendsto_atTop
          have twice := Filter.Tendsto.const_mul (2:ℝ) base
          -- only the common denominator changes its spelling
          convert twice using 1
          funext k
          have kk : (0:ℝ) < ((k+1 : ℕ):ℝ) := by
            exact_mod_cast (Nat.zero_lt_succ k)
          dsimp [Function.comp_def]
          push_cast
          field_simp
          <;> ring
        have hcomplim (R : ℕ) {d ε : ℝ} (hd : 0 < d) (heps : 0 < ε) :
            ∀ᶠ k : ℕ in atTop,
              ‖WignerSupport.eigenChar
                    (wignerMatrix_isHermitian X (k+1) ω) (q:ℝ) -
                WignerSupport.eigenChar
                    (wignerMatrix_isHermitian
                      (WignerSupport.cutX (R:ℝ) X) (k+1) ω) (q:ℝ)‖ <
                (2*|(q:ℝ)|) *
                  (((2 * WignerSupport.tailMean μ X (R:ℝ)) / (2*d)) + d/2) + ε := by
          let z : ℕ → ℝ := fun k =>
              (((k+1 : ℕ):ℝ)⁻¹ * (((k+1 : ℕ):ℝ)⁻¹ *
                (2 * (∑ r ∈ Finset.range ((k+1)^2),
                  WignerSupport.upperSqSeq
                    (WignerSupport.tailX (R:ℝ) X) r ω))))
          let phi : ℝ → ℝ := fun a =>
              (2*|(q:ℝ)|) * (a/(2*d) + d/2)
          have hcphi : Continuous phi := by
            dsimp [phi]
            fun_prop
          have limz : Tendsto z atTop
              (𝓝 (2 * WignerSupport.tailMean μ X (R:ℝ))) := by
            simpa [z] using (hnorm R)
          have limphi : Tendsto (fun k => phi (z k)) atTop
              (𝓝 (phi (2 * WignerSupport.tailMean μ X (R:ℝ)))) :=
            (hcphi.tendsto _).comp limz
          have ev := limphi.eventually
              (eventually_lt_nhds (show
                phi (2 * WignerSupport.tailMean μ X (R:ℝ)) <
                    phi (2 * WignerSupport.tailMean μ X (R:ℝ)) + ε by linarith))
          filter_upwards [ev] with k hk
          have ck := hcomp R (k+1) (by omega) hd
          have cz : z k =
                (((((k+1):ℕ):ℝ)⁻¹ * ((((k+1):ℕ):ℝ)⁻¹ *
                  (2 * (∑ r ∈ Finset.range (((k+1):ℕ)^2),
                    WignerSupport.upperSqSeq
                      (WignerSupport.tailX (R:ℝ) X) r ω))))) := rfl
          have cle : ‖WignerSupport.eigenChar
                    (wignerMatrix_isHermitian X (k+1) ω) (q:ℝ) -
                WignerSupport.eigenChar
                    (wignerMatrix_isHermitian
                      (WignerSupport.cutX (R:ℝ) X) (k+1) ω) (q:ℝ)‖ ≤
                    phi (z k) := by
              simpa [phi, z] using ck
          exact lt_of_le_of_lt cle (by simpa [phi] using hk)
        -- What remains is now solely the bounded-entry moment (or resolvent)
        -- theorem.  `hcomplim` shows that the hard cutoff changes any fixed
        -- characteristic value by at most
        -- `2|q| (2 tailMean R /(2d)+d/2)` in the limit.  The strong law used in
        -- that assertion is valid with only second moments, and `htailzero`
        -- lets `R→∞` afterwards.  Thus the missing step can and should be proved
        -- for truly bounded iid entries; it cannot be an assumption about how
        -- mathlib orders Hermitian eigenvalues.
        -- The elementary two-limits argument can now be completed.  It is
        -- important to let the small perturbation parameter tend to zero
        -- *after* the tail mean.  Choosing
        --   sqrt(2 tail) + 1/(R+1)
        -- as the parameter avoids any division by zero.
        let A : ℝ := 2 * |(q:ℝ)|
        let dd : ℕ → ℝ := fun R =>
          Real.sqrt (2 * WignerSupport.tailMean μ X (R:ℝ)) +
             1 / ((R:ℝ) + 1)
        let ee : ℕ → ℝ := fun R =>
          A * (Real.sqrt (2 * WignerSupport.tailMean μ X (R:ℝ)) +
             (1 / ((R:ℝ) + 1))/2) +
          A * (|WignerSupport.cutMean μ X (R:ℝ)| +
             (1 / ((R:ℝ) + 1))/2)
        have tail_nonneg (R : ℕ) :
            0 ≤ WignerSupport.tailMean μ X (R:ℝ) := by
          unfold WignerSupport.tailMean
          exact MeasureTheory.integral_nonneg_of_ae
            (ae_of_all _ (fun a => sq_nonneg _))
        have ddpos (R : ℕ) : 0 < dd R := by
          dsimp [dd]
          have ar : 0 < (1 / ((R:ℝ)+1)) := by positivity
          have sr : 0 ≤ Real.sqrt (2 * WignerSupport.tailMean μ X (R:ℝ)) :=
            Real.sqrt_nonneg _
          linarith
        -- A real inequality, used to replace the denominator in the
        -- perturbation estimate by a continuous error sequence.
        have frac_bound (R : ℕ) :
            ((2 * WignerSupport.tailMean μ X (R:ℝ)) / (2 * dd R) +
                 dd R / 2) ≤
              Real.sqrt (2 * WignerSupport.tailMean μ X (R:ℝ)) +
                (1 / ((R:ℝ) + 1))/2 := by
          let s₀ : ℝ := Real.sqrt
              (2 * WignerSupport.tailMean μ X (R:ℝ))
          let a₀ : ℝ := 1 / ((R:ℝ) + 1)
          let u₀ : ℝ := 2 * WignerSupport.tailMean μ X (R:ℝ)
          have hu : 0 ≤ u₀ := by
            dsimp [u₀]
            have := tail_nonneg R
            linarith
          have hs : 0 ≤ s₀ := by dsimp [s₀]; positivity
          have ha : 0 ≤ a₀ := by dsimp [a₀]; positivity
          have heq : s₀^2 = u₀ := by
            dsimp [s₀]
            exact Real.sq_sqrt hu
          have ddesc : dd R = s₀ + a₀ := by
            rfl
          have hdiv : u₀ / dd R ≤ s₀ := by
            apply (div_le_iff₀ (ddpos R)).2
            rw [← heq]
            rw [ddesc]
            nlinarith
          rw [ddesc]
          change u₀ / (2 * (s₀ + a₀)) + (s₀+a₀)/2 ≤ s₀ + a₀/2
          have hh : u₀ / (2 * (s₀+a₀)) = (u₀ / (s₀+a₀)) / 2 := by
            have hn : s₀ + a₀ ≠ 0 := by
              have hp : 0 < s₀ + a₀ := by
                rw [← ddesc]
                exact ddpos R
              exact ne_of_gt hp
            field_simp
          rw [hh]
          -- the only estimate is `s²/(s+a) ≤ s`.
          rw [ddesc] at hdiv
          linarith
        have ha0 : 0 ≤ A := by dsimp [A]; positivity
        -- Removing the centering is another deterministic comparison.  Its
        -- Hilbert--Schmidt square is exactly `n² b²`; using the same AM--GM
        -- bound keeps the argument independent of how eigenvalues are
        -- enumerated.
        have dbpos (R : ℕ) :
            0 < |WignerSupport.cutMean μ X (R:ℝ)| + 1/((R:ℝ)+1) := by
          have hp : 0 < (1/((R:ℝ)+1)) := by positivity
          have hb : 0 ≤ |WignerSupport.cutMean μ X (R:ℝ)| := abs_nonneg _
          linarith
        have hcenterSq (R n : ℕ) :
            WignerSupport.hsSq
              (wignerMatrix (WignerSupport.cutX (R:ℝ) X) n ω -
               wignerMatrix (WignerSupport.centeredCut μ (R:ℝ) X) n ω) =
              (n:ℝ)^2 * (WignerSupport.cutMean μ X (R:ℝ))^2 := by
          classical
          unfold WignerSupport.hsSq
          -- every real entry of this matrix is the same constant
          simp only [wignerMatrix, Matrix.sub_apply]
          simp only [WignerSupport.centeredCut]
          simp_rw [← Complex.ofReal_sub]
          simp_rw [sub_sub_cancel]
          simp_rw [Complex.normSq_ofReal]
          simp
          ring
        have eclose (R : ℕ) {η : ℝ} (hη : 0 < η) :
            ∀ᶠ k : ℕ in atTop,
              ‖WignerSupport.eigenChar
                    (wignerMatrix_isHermitian X (k+1) ω) (q:ℝ) -
                WignerSupport.eigenChar
                  (wignerMatrix_isHermitian
                    (WignerSupport.centeredCut μ (R:ℝ) X) (k+1) ω) (q:ℝ)‖
                  < ee R + η := by
          let b : ℝ := WignerSupport.cutMean μ X (R:ℝ)
          let a : ℝ := 1/((R:ℝ)+1)
          let db : ℝ := |b| + a
          have ad : 0 < a := by dsimp [a]; positivity
          have dp : 0 < db := by
            dsimp [db]
            have := abs_nonneg b
            linarith
          have bfrac : b^2/(2*db) + db/2 ≤ |b| + a/2 := by
            have beq : |b|^2 = b^2 := sq_abs b
            have small : b^2 / db ≤ |b| := by
              apply (div_le_iff₀ dp).2
              dsimp [db]
              nlinarith [abs_nonneg b]
            have hh : b^2 / (2*db) = (b^2/db)/2 := by
              have hn : db ≠ 0 := ne_of_gt dp
              field_simp
            rw [hh]
            dsimp [db] at *
            linarith
          have ev := hcomplim R (ddpos R) (by linarith : 0 < η/2)
          filter_upwards [ev] with k hk
          let n : ℕ := k+1
          have hn : n ≠ 0 := by dsimp [n]; omega
          have hkreal : (n:ℝ) ≠ 0 := by exact_mod_cast hn
          have hc := WignerSupport.eigenChar_sub_le_eps (n := n) hn
            (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) n ω)
            (wignerMatrix_isHermitian (WignerSupport.centeredCut μ (R:ℝ) X) n ω)
            (q:ℝ) dp
          have normeq :
              (n:ℝ)⁻¹ * ((n:ℝ)⁻¹ *
                WignerSupport.hsSq
                  (wignerMatrix (WignerSupport.cutX (R:ℝ) X) n ω -
                   wignerMatrix (WignerSupport.centeredCut μ (R:ℝ) X) n ω)) = b^2 := by
            rw [hcenterSq]
            dsimp [b]
            field_simp
            <;> ring
          have cutbd :
              ‖WignerSupport.eigenChar
                 (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) n ω) (q:ℝ) -
                WignerSupport.eigenChar
                 (wignerMatrix_isHermitian (WignerSupport.centeredCut μ (R:ℝ) X) n ω) (q:ℝ)‖
                 ≤ A * (|b| + a/2) := by
            have cev :
              ‖WignerSupport.eigenChar
                 (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) n ω) (q:ℝ) -
                WignerSupport.eigenChar
                 (wignerMatrix_isHermitian (WignerSupport.centeredCut μ (R:ℝ) X) n ω) (q:ℝ)‖
                 ≤ A * (b^2/(2*db)+db/2) := by
                simpa [A, normeq] using hc
            exact cev.trans (mul_le_mul_of_nonneg_left bfrac ha0)
          have tailbd :
              A * (((2 * WignerSupport.tailMean μ X (R:ℝ)) /
                       (2 * dd R)) + dd R/2)
                  ≤ A * (Real.sqrt (2 * WignerSupport.tailMean μ X (R:ℝ)) +
                       (1 / ((R:ℝ)+1))/2) :=
            mul_le_mul_of_nonneg_left (frac_bound R) ha0
          calc
            ‖WignerSupport.eigenChar
                    (wignerMatrix_isHermitian X (k+1) ω) (q:ℝ) -
                WignerSupport.eigenChar
                  (wignerMatrix_isHermitian
                    (WignerSupport.centeredCut μ (R:ℝ) X) (k+1) ω) (q:ℝ)‖ =
              ‖(WignerSupport.eigenChar
                    (wignerMatrix_isHermitian X (k+1) ω) (q:ℝ) -
                  WignerSupport.eigenChar
                    (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) (k+1) ω) (q:ℝ)) +
                (WignerSupport.eigenChar
                    (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) (k+1) ω) (q:ℝ) -
                  WignerSupport.eigenChar
                    (wignerMatrix_isHermitian (WignerSupport.centeredCut μ (R:ℝ) X) (k+1) ω) (q:ℝ))‖ := by congr 1 <;> ring
            _ ≤ ‖WignerSupport.eigenChar
                    (wignerMatrix_isHermitian X (k+1) ω) (q:ℝ) -
                  WignerSupport.eigenChar
                    (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) (k+1) ω) (q:ℝ)‖ +
                ‖WignerSupport.eigenChar
                    (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) (k+1) ω) (q:ℝ) -
                  WignerSupport.eigenChar
                    (wignerMatrix_isHermitian (WignerSupport.centeredCut μ (R:ℝ) X) (k+1) ω) (q:ℝ)‖ := norm_add_le _ _
            _ < ee R + η := by
                 change _ <
                  A * (Real.sqrt (2 * WignerSupport.tailMean μ X (R:ℝ)) +
                         (1 / ((R:ℝ)+1))/2) +
                  A * (|WignerSupport.cutMean μ X (R:ℝ)| +
                         (1 / ((R:ℝ)+1))/2) + η
                 have Hk :
                    ‖WignerSupport.eigenChar
                    (wignerMatrix_isHermitian X (k+1) ω) (q:ℝ) -
                  WignerSupport.eigenChar
                    (wignerMatrix_isHermitian (WignerSupport.cutX (R:ℝ) X) (k+1) ω) (q:ℝ)‖ <
                       A * (((2 * WignerSupport.tailMean μ X (R:ℝ)) /
                           (2 * dd R)) + dd R/2) + η/2 := by
                       exact hk
                 dsimp [b, a] at cutbd
                 change _ ≤ _ at cutbd
                 linarith
        have hsqrt : Tendsto
            (fun R : ℕ => Real.sqrt
                 (2 * WignerSupport.tailMean μ X (R:ℝ)))
             atTop (𝓝 (0:ℝ)) := by
          have ht : Tendsto
              (fun R : ℕ => 2 * WignerSupport.tailMean μ X (R:ℝ))
              atTop (𝓝 (0:ℝ)) := by
            simpa using
              (Filter.Tendsto.const_mul (2:ℝ) htailzero)
          simpa only [Function.comp_def, Real.sqrt_zero] using
            ((Real.continuous_sqrt.tendsto (0:ℝ)).comp ht)
        have hinv : Tendsto (fun R : ℕ => 1 / ((R:ℝ)+1))
              atTop (𝓝 (0:ℝ)) := by
          simpa using
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        have hee : Tendsto ee atTop (𝓝 (0:ℝ)) := by
          have addlim : Tendsto
              (fun R : ℕ =>
                Real.sqrt (2 * WignerSupport.tailMean μ X (R:ℝ)) +
                   (1 / ((R:ℝ)+1))/2)
                  atTop (𝓝 (0:ℝ)) := by
            convert hsqrt.add (hinv.div_const (2:ℝ)) using 1
            <;> simp
          have cm : Tendsto
              (fun R : ℕ => WignerSupport.cutMean μ X (R:ℝ))
              atTop (𝓝 (0:ℝ)) := by
            have hc := WignerSupport.cutMean_tendsto μ X
               (_hX_meas 0 0) (_hX_int 0 0 (by omega))
            simpa [_hX_mean 0 0 (by omega)] using hc
          have ab : Tendsto
              (fun R : ℕ => |WignerSupport.cutMean μ X (R:ℝ)|)
              atTop (𝓝 (0:ℝ)) := by
            simpa using cm.abs
          have abadd : Tendsto
              (fun R : ℕ => |WignerSupport.cutMean μ X (R:ℝ)| +
                   (1 / ((R:ℝ)+1))/2)
               atTop (𝓝 (0:ℝ)) := by
            convert ab.add (hinv.div_const (2:ℝ)) using 1
            <;> simp
          dsimp [ee]
          have tot := (Filter.Tendsto.const_mul A addlim).add
              (Filter.Tendsto.const_mul A abadd)
          convert tot using 1
          <;> simp only [zero_add, mul_zero]
        let zlim : ℕ → ℂ := fun R =>
            MeasureTheory.charFun semicircleLaw
              (Real.sqrt (WignerSupport.cutVariance μ X (R:ℝ)) * (q:ℝ))
        have vlim : Tendsto
             (fun R : ℕ => WignerSupport.cutVariance μ X (R:ℝ))
             atTop (𝓝 (1:ℝ)) := by
          have hh := WignerSupport.cutVariance_tendsto μ X
            (_hX_meas 0 0) (_hX_int 0 0 (by omega))
            (_hX_sq_int 0 0 (by omega))
          simpa [_hX_var 0 0 (by omega), _hX_mean 0 0 (by omega)] using hh
        have ztend : Tendsto zlim atTop
              (𝓝 (MeasureTheory.charFun semicircleLaw (q:ℝ))) := by
          have sr : Tendsto
              (fun R : ℕ => Real.sqrt
                (WignerSupport.cutVariance μ X (R:ℝ)))
                atTop (𝓝 (1:ℝ)) := by
            simpa only [Function.comp_def, Real.sqrt_one] using
              ((Real.continuous_sqrt.tendsto (1:ℝ)).comp vlim)
          have arg : Tendsto
              (fun R : ℕ =>
                Real.sqrt (WignerSupport.cutVariance μ X (R:ℝ)) * (q:ℝ))
              atTop (𝓝 (q:ℝ)) := by
            simpa using sr.mul_const (q:ℝ)
          exact (MeasureTheory.continuous_charFun.tendsto _).comp arg
        have fin : Tendsto
             (fun k : ℕ =>
                WignerSupport.eigenChar
                  (wignerMatrix_isHermitian X (k+1) ω) (q:ℝ))
             atTop (𝓝 (MeasureTheory.charFun semicircleLaw (q:ℝ))) := by
          apply WignerSupport.tendsto_of_approx_complex
            (fun k : ℕ => WignerSupport.eigenChar
              (wignerMatrix_isHermitian X (k+1) ω) (q:ℝ))
            (fun R k : ℕ => WignerSupport.eigenChar
              (wignerMatrix_isHermitian
                 (WignerSupport.centeredCut μ (R:ℝ) X) (k+1) ω) (q:ℝ))
            zlim (MeasureTheory.charFun semicircleLaw (q:ℝ)) ee
          · intro R
            exact hcutω R
          · exact ztend
          · exact hee
          · intro R η hη
            exact eclose R hη
        change P ω q
        simpa [P, WignerSupport.eigenChar] using fin
      have hrat_non :
          ∀ᵐ ω ∂μ, ∀ q : ℚ, q ≠ 0 →
            Tendsto
              (fun k : ℕ =>
                ((k+1 : ℕ) : ℝ)⁻¹ •
                  (∑ j : Fin (k+1),
                    Complex.exp
                      (((((wignerMatrix_isHermitian X (k+1) ω).eigenvalues j /
                            Real.sqrt (k+1)) * (q:ℝ) : ℝ) : ℂ) * Complex.I)))
              atTop (𝓝 (MeasureTheory.charFun (semicircleLaw) (q:ℝ))) := by
        change ∀ᵐ ω ∂μ, ∀ q : ℚ, q ≠ 0 → P ω q
        rw [MeasureTheory.ae_all_iff]
        intro q
        by_cases h : q = 0
        · subst q
          filter_upwards [] with ω
          exact fun absurd => False.elim (absurd rfl)
        · filter_upwards [hfixed q h] with ω hω
          intro hne
          exact hω
      have hrat :
          ∀ᵐ ω ∂μ, ∀ q : ℚ,
            Tendsto
              (fun k : ℕ =>
                ((k+1 : ℕ) : ℝ)⁻¹ •
                  (∑ j : Fin (k+1),
                    Complex.exp
                      (((((wignerMatrix_isHermitian X (k+1) ω).eigenvalues j /
                            Real.sqrt (k+1)) * (q:ℝ) : ℝ) : ℂ) * Complex.I)))
              atTop (𝓝 (MeasureTheory.charFun (semicircleLaw) (q:ℝ))) := by
        filter_upwards [hrat_non] with ω hω
        intro q
        by_cases h : q = 0
        · subst q
          simp
          convert (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 (1 : ℂ))) using 1
          funext k
          have hk : ((k:ℝ)+1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
          field_simp
        · exact hω q h
      have hsll := WignerSupport.upperSqSeq_strongLaw μ X _hX_indep _hX_iid _hX_sq_int _hX_var
      filter_upwards [hrat, hsll] with ω hq hs
      -- square traces of all sizes are bounded using the enumerated strong law
      rcases WignerSupport.square_average_bdd X ω hs with ⟨C, hC⟩
      have hmom : ∀ n : ℕ,
          ((n:ℝ)⁻¹ * ∑ j : Fin n,
            (((wignerMatrix_isHermitian X n ω).eigenvalues j /
              Real.sqrt n)^2)) ≤ C := by
        intro n
        have htrace := WignerSupport.real_wigner_sq X
          (fun m a => wignerMatrix_isHermitian X m a) n ω
        have hc := hC n
        by_cases hn : n = 0
        · subst n; simpa using hc
        have rn : (0:ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
        have root : (Real.sqrt (n:ℝ))^2 = (n:ℝ) := Real.sq_sqrt (le_of_lt rn)
        have heq :
            (∑ j : Fin n, (((wignerMatrix_isHermitian X n ω).eigenvalues j /
              Real.sqrt n)^2)) =
              (n:ℝ)⁻¹ * (∑ j : Fin n,
                ((wignerMatrix_isHermitian X n ω).eigenvalues j)^2) := by
          -- common denominator in the finite sum
          calc
            (∑ j : Fin n, (((wignerMatrix_isHermitian X n ω).eigenvalues j /
                Real.sqrt n)^2)) =
                ∑ j : Fin n, (n:ℝ)⁻¹ *
                    ((wignerMatrix_isHermitian X n ω).eigenvalues j)^2 := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [div_pow]
                      rw [root]
                      simp [div_eq_inv_mul]
            _ = _ := by rw [← Finset.mul_sum]
        rw [heq]
        have hh : (∑ j : Fin n,
                ((wignerMatrix_isHermitian X n ω).eigenvalues j)^2) =
              (∑ i : Fin n, ∑ j : Fin n,
                (X (min (i:ℕ) j) (max (i:ℕ) j) ω)^2) := by
          convert htrace using 1 <;>
            congr
        rw [hh]
        exact hc
      -- a first moment bound supplies a deterministic (pathwise) Lipschitz constant
      have habs : ∀ n : ℕ, n ≠ 0 →
          (n:ℝ)⁻¹ * ∑ j : Fin n,
            |(wignerMatrix_isHermitian X n ω).eigenvalues j / Real.sqrt n|
            ≤ C + 1 := by
        intro n hn
        exact WignerSupport.mean_abs_le_of_mean_sq hn _ C (hmom n)
      let F : ℕ → ℝ → ℂ := fun k t =>
          ((k+1 : ℕ) : ℝ)⁻¹ •
            (∑ j : Fin (k+1),
              Complex.exp
                (((((wignerMatrix_isHermitian X (k+1) ω).eigenvalues j /
                    Real.sqrt (k+1)) * t : ℝ) : ℂ) * Complex.I))
      have hCnon : 0 ≤ C + 1 := by
        have hm := hmom 1
        have : (0:ℝ) ≤ (1:ℝ)⁻¹ * ∑ j : Fin 1,
            (((wignerMatrix_isHermitian X 1 ω).eigenvalues j /
              Real.sqrt (1:ℕ))^2) := by positivity
        linarith
      have hLip : ∀ k s t, ‖F k s - F k t‖ ≤ (2*(C+1)) * |s-t| := by
        intro k s t
        have base := WignerSupport.finiteChar_lipschitz
          (v := fun j : Fin (k+1) =>
            (wignerMatrix_isHermitian X (k+1) ω).eigenvalues j /
              Real.sqrt (k+1)) s t
        change ‖F k s - F k t‖ ≤ _
        change ‖WignerSupport.finiteChar _ s - WignerSupport.finiteChar _ t‖ ≤ _
        calc
          _ ≤ ((((k+1:ℕ):ℝ)⁻¹ * ∑ j : Fin (k+1),
                |(wignerMatrix_isHermitian X (k+1) ω).eigenvalues j /
                    Real.sqrt (k+1)|) * (2 * |s-t|)) := base
          _ ≤ (C+1) * (2 * |s-t|) := by
              gcongr
              simpa [Nat.cast_add, Nat.cast_one] using (habs (k+1) (by omega))
          _ = (2*(C+1)) * |s-t| := by ring
      have hAll := WignerSupport.tendsto_of_rat_of_lipschitz F
        (MeasureTheory.charFun (semicircleLaw))
        (MeasureTheory.continuous_charFun)
        (2*(C+1)) (by positivity : 0 ≤ (2:ℝ)*(C+1)) hLip (by
          intro q
          exact hq q)
      intro t ht
      exact hAll t
    filter_upwards [hnz] with ω hω
    intro t
    by_cases ht : t = 0
    · subst t
      -- every exponential in the sum is one
      simp
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 (1 : ℂ))) using 1
      funext k
      have hk : ( (k : ℝ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
      field_simp
    · exact hω t ht
  have hchar :
      ∀ᵐ ω ∂μ, ∀ t : ℝ,
        Tendsto
          (fun k : ℕ =>
            MeasureTheory.charFun
              (wignerEmpiricalProbability X ω k : Measure ℝ) t)
          atTop
          (𝓝 (MeasureTheory.charFun (semicircleLaw) t)) := by
    filter_upwards [hexponential] with ω hω
    intro t
    simpa only [wignerEmpiricalProbability_charFun] using hω t
  have hweak :
      ∀ᵐ ω ∂μ,
        Tendsto (wignerEmpiricalProbability X ω)
          atTop (𝓝 ν₀) := by
    filter_upwards [hchar] with ω hω
    apply MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun
      (μ₀ := ν₀) (μ := wignerEmpiricalProbability X ω)
    intro t
    simpa [ν₀] using hω t
  have hcore :
      ∀ᵐ ω ∂μ,
        ∀ (f : ℝ → ℝ), Continuous f → (∃ M, ∀ x, ‖f x‖ ≤ M) →
          Tendsto
            (fun n : ℕ =>
              (n : ℝ)⁻¹ *
                ∑ j : Fin n,
                  f ((wignerMatrix_isHermitian X n ω).eigenvalues j /
                      Real.sqrt n))
            atTop (𝓝 (∫ x, f x ∂semicircleLaw)) := by
    filter_upwards [hweak] with ω hω
    intro f hf hfbound
    rcases hfbound with ⟨M, hM⟩
    let g : BoundedContinuousFunction ℝ ℝ :=
      { toFun := f
        continuous_toFun := hf
        map_bounded' := by
          refine ⟨M+M, ?_⟩
          intro x y
          rw [Real.dist_eq]
          calc
            |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
            _ = ‖f x‖ + ‖f y‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
            _ ≤ M + M := add_le_add (hM x) (hM y) }
    have hi := (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hω) g
    -- Interpret this as the sequence starting at matrix size `1`.
    have hshift : Tendsto
        (fun k : ℕ =>
          ∫ x, f x ∂
            (empiricalSpectralMeasureHerm
              (wignerMatrix_isHermitian X (k+1) ω)).map
                (fun x : ℝ => x / Real.sqrt (k+1)))
        atTop (𝓝 (∫ x, f x ∂semicircleLaw)) := by
      simpa [wignerEmpiricalProbability_apply, g, ν₀]
        using hi
    -- Inserting the zero-size empirical measure changes no `atTop` limit.
    have hall : Tendsto
        (fun n : ℕ =>
          ∫ x, f x ∂
            (empiricalSpectralMeasureHerm
              (wignerMatrix_isHermitian X n ω)).map
                (fun x : ℝ => x / Real.sqrt n))
        atTop (𝓝 (∫ x, f x ∂semicircleLaw)) := by
      -- the library lemma drops any fixed finite prefix of a sequence
      apply (Filter.tendsto_add_atTop_iff_nat 1).1
      simpa [Nat.add_comm] using hshift
    have hseq :
        (fun n : ℕ => ∫ x, f x ∂
          (empiricalSpectralMeasureHerm
            (wignerMatrix_isHermitian X n ω)).map
              (fun x : ℝ => x / Real.sqrt n)) =
        (fun n : ℕ =>
          (n : ℝ)⁻¹ * ∑ j : Fin n,
            f ((wignerMatrix_isHermitian X n ω).eigenvalues j /
              Real.sqrt n)) := by
      funext n
      exact empiricalSpectralMeasureHerm_integral_map
        (wignerMatrix_isHermitian X n ω)
        (fun x : ℝ => x / Real.sqrt n) (by fun_prop) f hf
    rw [hseq] at hall
    exact hall
  filter_upwards [hcore] with ω hω
  intro f hf hfb
  -- equality of the two sequences, pointwise for each matrix size
  have hseq :
      (fun n : ℕ => ∫ x, f x ∂
        (empiricalSpectralMeasureHerm
          (wignerMatrix_isHermitian X n ω)).map
            (fun x : ℝ => x / Real.sqrt n)) =
      (fun n : ℕ =>
        (n : ℝ)⁻¹ * ∑ j : Fin n,
          f ((wignerMatrix_isHermitian X n ω).eigenvalues j /
            Real.sqrt n)) := by
    funext n
    exact empiricalSpectralMeasureHerm_integral_map
      (wignerMatrix_isHermitian X n ω)
      (fun x : ℝ => x / Real.sqrt n)
      (by fun_prop) f hf
  rw [hseq]
  exact hω f hf hfb
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
