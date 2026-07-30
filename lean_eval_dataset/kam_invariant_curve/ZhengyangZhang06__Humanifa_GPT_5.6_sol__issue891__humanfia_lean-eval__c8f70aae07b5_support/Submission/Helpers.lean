import ChallengeDeps

open LeanEval.Dynamics
open scoped ContDiff

namespace Submission.Helpers

/-- The quantitative Diophantine condition rules out rational rotation numbers. -/
theorem isDiophantine_irrational {α : ℝ} (hα : IsDiophantine α) : Irrational α := by
  rw [irrational_iff_ne_rational]
  rintro p q hq hpq
  obtain ⟨C, hC, hbound⟩ := hα
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hq_sq : 0 < (q : ℝ) ^ 2 := sq_pos_of_ne_zero hq'
  have hpos : 0 < C / (q : ℝ) ^ 2 := div_pos hC hq_sq
  have hle := hbound p q hq
  rw [hpq, sub_self, abs_zero] at hle
  exact (not_lt_of_ge hle) hpos

/-- In particular, no nonzero integer multiple of a Diophantine number is an integer. -/
theorem isDiophantine_int_mul_ne_int {α : ℝ} (hα : IsDiophantine α)
    (n : ℤ) (hn : n ≠ 0) (m : ℤ) : (n : ℝ) * α ≠ m := by
  intro h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hrat : α = (m : ℝ) / (n : ℝ) :=
    (eq_div_iff hn').2 (by simpa [mul_comm] using h)
  exact ((irrational_iff_ne_rational α).mp (isDiophantine_irrational hα) m n hn) hrat

/-- A denominator-free form of the Diophantine estimate, suited to Fourier modes. -/
theorem isDiophantine_mul_sub_bound {α : ℝ} (hα : IsDiophantine α) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℤ, n ≠ 0 →
      C / |(n : ℝ)| ≤ |(n : ℝ) * α - (m : ℝ)| := by
  obtain ⟨C, hC, hbound⟩ := hα
  refine ⟨C, hC, ?_⟩
  intro m n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have habs_ne : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hn'
  calc
    C / |(n : ℝ)| = |(n : ℝ)| * (C / (n : ℝ) ^ 2) := by
      field_simp [habs_ne, hn']
      rw [sq_abs]
    _ ≤ |(n : ℝ)| * |α - (m : ℝ) / (n : ℝ)| :=
      mul_le_mul_of_nonneg_left (hbound m n hn) (abs_nonneg _)
    _ = |(n : ℝ) * (α - (m : ℝ) / (n : ℝ))| := by rw [abs_mul]
    _ = |(n : ℝ) * α - (m : ℝ)| := by
      congr 1
      field_simp [hn']

/-- The nonzero Fourier modes of the discrete Laplacian at a Diophantine rotation
have nonvanishing symbols. -/
theorem isDiophantine_cos_symbol_ne_zero {α : ℝ} (hα : IsDiophantine α)
    (n : ℤ) (hn : n ≠ 0) :
    2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2 ≠ 0 := by
  have hcos : Real.cos (2 * Real.pi * ((n : ℝ) * α)) ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).mp h
    have htwo_pi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    have heq : (2 * Real.pi) * ((n : ℝ) * α) = (2 * Real.pi) * (m : ℝ) := by
      calc
        (2 * Real.pi) * ((n : ℝ) * α) = 2 * Real.pi * ((n : ℝ) * α) := by ring
        _ = (m : ℝ) * (2 * Real.pi) := hm.symm
        _ = (2 * Real.pi) * (m : ℝ) := by ring
    exact isDiophantine_int_mul_ne_int hα n hn m (mul_left_cancel₀ htwo_pi heq)
  intro hzero
  apply hcos
  linarith

/-- Quantitative small-divisor estimate for the discrete-Laplacian Fourier symbol. -/
theorem isDiophantine_cos_symbol_bound {α : ℝ} (hα : IsDiophantine α) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ, n ≠ 0 →
      (C / |(n : ℝ)|) ^ 2 ≤
        |2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2| := by
  obtain ⟨C, hC, hbound⟩ := isDiophantine_mul_sub_bound hα
  refine ⟨C, hC, ?_⟩
  intro n hn
  let x : ℝ := (n : ℝ) * α
  let k : ℤ := round x
  let δ : ℝ := x - (k : ℝ)
  have hδ_lower : C / |(n : ℝ)| ≤ |δ| := by
    simpa [x, k, δ] using hbound k n hn
  have hδ_upper : |δ| ≤ (1 : ℝ) / 2 := by
    simpa [δ, k] using abs_sub_round x
  have hπδ_upper : |Real.pi * δ| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left hδ_upper Real.pi_pos.le).trans_eq (by ring)
  have hsin : 2 * |δ| ≤ |Real.sin (Real.pi * δ)| := by
    have h := Real.mul_abs_le_abs_sin hπδ_upper
    rw [abs_mul, abs_of_pos Real.pi_pos] at h
    convert h using 1
    all_goals field_simp [Real.pi_ne_zero]
  have hδ_sq : (2 * |δ|) ^ 2 ≤ |Real.sin (Real.pi * δ)| ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin 2
  have hC_sq : (C / |(n : ℝ)|) ^ 2 ≤ |δ| ^ 2 :=
    pow_le_pow_left₀ (by positivity) hδ_lower 2
  have hcos :
      Real.cos (2 * Real.pi * ((n : ℝ) * α)) =
        Real.cos (2 * Real.pi * δ) := by
    calc
      Real.cos (2 * Real.pi * ((n : ℝ) * α)) =
          Real.cos (2 * Real.pi * x - (k : ℝ) * (2 * Real.pi)) := by
            symm
            simpa only using Real.cos_sub_int_mul_two_pi (2 * Real.pi * x) k
      _ = Real.cos (2 * Real.pi * δ) := by
        congr 1
        simp only [δ, x]
        ring
  have hsymbol :
      |2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2| =
        4 * |Real.sin (Real.pi * δ)| ^ 2 := by
    rw [hcos]
    have htrig : Real.sin (Real.pi * δ) ^ 2 =
        1 / 2 - Real.cos (2 * Real.pi * δ) / 2 := by
      convert Real.sin_sq_eq_half_sub (Real.pi * δ) using 1
      all_goals ring_nf
    have hnonpos : 2 * Real.cos (2 * Real.pi * δ) - 2 ≤ 0 := by
      linarith [Real.cos_le_one (2 * Real.pi * δ)]
    rw [abs_of_nonpos hnonpos]
    rw [sq_abs]
    nlinarith
  rw [hsymbol]
  calc
    (C / |(n : ℝ)|) ^ 2 ≤ |δ| ^ 2 := hC_sq
    _ ≤ 4 * |Real.sin (Real.pi * δ)| ^ 2 := by
      nlinarith [sq_nonneg (|δ|), sq_nonneg (|Real.sin (Real.pi * δ)|)]

/-- The second difference along the rotation by `α`. -/
def discreteLaplacian (α : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  u (t + α) - 2 * u t + u (t - α)

/-- Cosine modes diagonalize the second-difference operator. -/
theorem discreteLaplacian_cos (α : ℝ) (n : ℤ) (t : ℝ) :
    discreteLaplacian α (fun x => Real.cos (2 * Real.pi * (n : ℝ) * x)) t =
      (2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2) *
        Real.cos (2 * Real.pi * (n : ℝ) * t) := by
  simp only [discreteLaplacian]
  rw [show 2 * Real.pi * (n : ℝ) * (t + α) =
        2 * Real.pi * (n : ℝ) * t + 2 * Real.pi * ((n : ℝ) * α) by ring]
  rw [show 2 * Real.pi * (n : ℝ) * (t - α) =
        2 * Real.pi * (n : ℝ) * t - 2 * Real.pi * ((n : ℝ) * α) by ring]
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- Sine modes diagonalize the second-difference operator. -/
theorem discreteLaplacian_sin (α : ℝ) (n : ℤ) (t : ℝ) :
    discreteLaplacian α (fun x => Real.sin (2 * Real.pi * (n : ℝ) * x)) t =
      (2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2) *
        Real.sin (2 * Real.pi * (n : ℝ) * t) := by
  simp only [discreteLaplacian]
  rw [show 2 * Real.pi * (n : ℝ) * (t + α) =
        2 * Real.pi * (n : ℝ) * t + 2 * Real.pi * ((n : ℝ) * α) by ring]
  rw [show 2 * Real.pi * (n : ℝ) * (t - α) =
        2 * Real.pi * (n : ℝ) * t - 2 * Real.pi * ((n : ℝ) * α) by ring]
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- Every nonconstant real Fourier mode has an explicit cohomological solution. -/
theorem discreteLaplacian_mode_solution {α : ℝ} (hα : IsDiophantine α)
    (a b : ℝ) (n : ℤ) (hn : n ≠ 0) :
    let symbol := 2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2
    let u := fun t : ℝ => symbol⁻¹ *
      (a * Real.cos (2 * Real.pi * (n : ℝ) * t) +
        b * Real.sin (2 * Real.pi * (n : ℝ) * t))
    ∀ t, discreteLaplacian α u t =
      a * Real.cos (2 * Real.pi * (n : ℝ) * t) +
        b * Real.sin (2 * Real.pi * (n : ℝ) * t) := by
  dsimp only
  intro t
  rw [show discreteLaplacian α
      (fun x => (2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2)⁻¹ *
        (a * Real.cos (2 * Real.pi * (n : ℝ) * x) +
          b * Real.sin (2 * Real.pi * (n : ℝ) * x))) t =
      (2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2)⁻¹ *
        (a * discreteLaplacian α
            (fun x => Real.cos (2 * Real.pi * (n : ℝ) * x)) t +
          b * discreteLaplacian α
            (fun x => Real.sin (2 * Real.pi * (n : ℝ) * x)) t) by
      simp only [discreteLaplacian]
      ring]
  rw [discreteLaplacian_cos, discreteLaplacian_sin]
  let symbol := 2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2
  have hsymbol : symbol ≠ 0 := isDiophantine_cos_symbol_ne_zero hα n hn
  change symbol⁻¹ *
      (a * (symbol * Real.cos (2 * Real.pi * (n : ℝ) * t)) +
        b * (symbol * Real.sin (2 * Real.pi * (n : ℝ) * t))) = _
  calc
    _ = symbol⁻¹ * symbol *
        (a * Real.cos (2 * Real.pi * (n : ℝ) * t) +
          b * Real.sin (2 * Real.pi * (n : ℝ) * t)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hsymbol, one_mul]

theorem discreteLaplacian_add (α : ℝ) (u v : ℝ → ℝ) (t : ℝ) :
    discreteLaplacian α (fun x => u x + v x) t =
      discreteLaplacian α u t + discreteLaplacian α v t := by
  simp only [discreteLaplacian]
  ring

theorem discreteLaplacian_periodic (α : ℝ) {u : ℝ → ℝ}
    (hu : Function.Periodic u 1) :
    Function.Periodic (discreteLaplacian α u) 1 := by
  intro t
  simp only [discreteLaplacian]
  rw [show t + 1 + α = (t + α) + 1 by ring, hu (t + α), hu t]
  rw [show t + 1 - α = (t - α) + 1 by ring, hu (t - α)]

theorem discreteLaplacian_finset_sum (α : ℝ) (S : Finset ℤ)
    (u : ℤ → ℝ → ℝ) (t : ℝ) :
    discreteLaplacian α (fun x => ∑ n ∈ S, u n x) t =
      ∑ n ∈ S, discreteLaplacian α (u n) t := by
  induction S using Finset.induction_on with
  | empty => simp [discreteLaplacian]
  | @insert n S hn ih =>
      simp only [Finset.sum_insert hn]
      rw [discreteLaplacian_add, ih]

/-- A finite real Fourier series with no separately stored zero mode. -/
noncomputable def trigPolynomial (S : Finset ℤ) (a b : ℤ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ S, (a n * Real.cos (2 * Real.pi * (n : ℝ) * t) +
    b n * Real.sin (2 * Real.pi * (n : ℝ) * t))

/-- Fourier division solves the cohomological equation for every finite collection
of nonzero modes. -/
noncomputable def solveTrigPolynomial
    (α : ℝ) (S : Finset ℤ) (a b : ℤ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ S,
    (2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2)⁻¹ *
      (a n * Real.cos (2 * Real.pi * (n : ℝ) * t) +
        b n * Real.sin (2 * Real.pi * (n : ℝ) * t))

theorem discreteLaplacian_solveTrigPolynomial {α : ℝ}
    (hα : IsDiophantine α) (S : Finset ℤ) (hS : ∀ n ∈ S, n ≠ 0)
    (a b : ℤ → ℝ) (t : ℝ) :
    discreteLaplacian α (solveTrigPolynomial α S a b) t =
      trigPolynomial S a b t := by
  change discreteLaplacian α
      (fun x => ∑ n ∈ S,
        (2 * Real.cos (2 * Real.pi * ((n : ℝ) * α)) - 2)⁻¹ *
          (a n * Real.cos (2 * Real.pi * (n : ℝ) * x) +
            b n * Real.sin (2 * Real.pi * (n : ℝ) * x))) t =
    ∑ n ∈ S, (a n * Real.cos (2 * Real.pi * (n : ℝ) * t) +
      b n * Real.sin (2 * Real.pi * (n : ℝ) * t))
  rw [discreteLaplacian_finset_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact discreteLaplacian_mode_solution hα (a n) (b n) n (hS n hn) t

/-- A periodic correction with Lipschitz factor strictly below one preserves
the strict increase of the identity lift. -/
theorem strictMono_id_add_of_lipschitz {u : ℝ → ℝ} {K : NNReal}
    (hK : (K : ℝ) < 1) (hu : LipschitzWith K u) :
    StrictMono (fun t => t + u t) := by
  intro x y hxy
  have hdist := hu.dist_le_mul x y
  simp only [Real.dist_eq] at hdist
  have hxy_abs : |x - y| = y - x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hxy.le)]
    ring
  rw [hxy_abs] at hdist
  have hK_nonneg : 0 ≤ (K : ℝ) := K.coe_nonneg
  have hgap : (K : ℝ) * (y - x) < y - x := by
    nlinarith
  have hudiff : u x - u y ≤ |u x - u y| := le_abs_self _
  linarith

/-- The analytic regularity assumed by the challenge supplies smoothness of
every finite order. -/
theorem analyticOnNhd_contDiff_top {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) : ContDiff ℝ ∞ f :=
  hf.contDiff

/-- Translation commutes with iterated differentiation, so all derivatives
inherit the period of the original function. -/
theorem periodic_iteratedDeriv {f : ℝ → ℝ} {p : ℝ}
    (hf : Function.Periodic f p) (n : ℕ) :
    Function.Periodic (iteratedDeriv n f) p := by
  have hfun : (fun x => f (x + p)) = f := funext hf
  have hder := congrArg (iteratedDeriv n) hfun
  rw [iteratedDeriv_comp_add_const] at hder
  exact funext_iff.mp hder

/-- One integration-by-parts step for Fourier coefficients of a smooth real
periodic function, written after embedding its values into `ℂ`. -/
theorem fourierCoeffOn_iteratedDeriv_succ {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1)
    (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun x => Complex.ofReal (iteratedDeriv k f x)) n =
      1 / (-2 * Real.pi * Complex.I * n) *
        (-fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
          (fun x => Complex.ofReal (iteratedDeriv (k + 1) f x)) n) := by
  have hdiff : ∀ x : ℝ,
      HasDerivAt (fun y => Complex.ofReal (iteratedDeriv k f y))
        (Complex.ofReal (iteratedDeriv (k + 1) f x)) x := by
    intro x
    have hx := (hf.differentiable_iteratedDeriv k
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) x).hasDerivAt.ofReal_comp
    simpa only [iteratedDeriv_succ] using hx
  have hcont : Continuous
      (fun x => Complex.ofReal (iteratedDeriv (k + 1) f x)) :=
    Complex.continuous_ofReal.comp (hf.continuous_iteratedDeriv (k + 1)
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl (k + 1)).le)
  have hformula := fourierCoeffOn_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (f := fun x => Complex.ofReal (iteratedDeriv k f x))
    (f' := fun x => Complex.ofReal (iteratedDeriv (k + 1) f x))
    (by norm_num) hn (fun x _ => hdiff x) (hcont.intervalIntegrable 0 1)
  have hboundary : iteratedDeriv k f 1 = iteratedDeriv k f 0 := by
    simpa using periodic_iteratedDeriv hper k 0
  simpa [hboundary] using hformula

/-- The scalar introduced by one integration-by-parts step at mode `n`. -/
noncomputable def fourierDerivativeDivisor (n : ℤ) : ℂ :=
  1 / (-2 * Real.pi * Complex.I * n) * (-1)

theorem norm_fourierDerivativeDivisor (n : ℤ) :
    ‖fourierDerivativeDivisor n‖ = 1 / (2 * Real.pi * |(n : ℝ)|) := by
  simp [fourierDerivativeDivisor, abs_of_pos Real.pi_pos]

theorem fourierCoeffOn_iteratedDeriv_step {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1)
    (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun x => Complex.ofReal (iteratedDeriv k f x)) n =
      fourierDerivativeDivisor n *
        fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
          (fun x => Complex.ofReal (iteratedDeriv (k + 1) f x)) n := by
  rw [fourierCoeffOn_iteratedDeriv_succ hf hper k n hn]
  simp only [fourierDerivativeDivisor]
  ring

/-- Repeating integration by parts gives arbitrary polynomial decay of the
Fourier coefficients of a smooth periodic function. -/
theorem fourierCoeffOn_iteratedDeriv_iterate {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1)
    (m : ℕ) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun x => Complex.ofReal (f x)) n =
      fourierDerivativeDivisor n ^ m *
        fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
          (fun x => Complex.ofReal (iteratedDeriv m f x)) n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [ih, fourierCoeffOn_iteratedDeriv_step hf hper m n hn, pow_succ]
      ring

/-- Continuity on one compact period gives a mode-independent bound for all
Fourier coefficients. -/
theorem exists_fourierCoeffOn_norm_bound {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℤ,
      ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
        (fun x => Complex.ofReal (f x)) n‖ ≤ B := by
  have hnorm : ContinuousOn (fun x : ℝ => ‖f x‖) (Set.Icc 0 1) :=
    hf.norm.continuousOn
  obtain ⟨B, hB⟩ := bddAbove_def.mp (isCompact_Icc.bddAbove_image hnorm)
  have hf_zero_le : ‖f 0‖ ≤ B := hB _ ⟨0, by simp, rfl⟩
  have hB_nonneg : 0 ≤ B := (norm_nonneg (f 0)).trans hf_zero_le
  refine ⟨B, hB_nonneg, ?_⟩
  intro n
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div, inv_one, one_smul]
  calc
    _ ≤ B * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
        rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul, Complex.norm_real]
        apply hB _
        refine ⟨x, ?_, rfl⟩
        norm_num at hx ⊢
        exact ⟨hx.1.le, hx.2⟩)
    _ = B := by norm_num

/-- Assemble the invariant curve from a small periodic correction. This isolates
the nonlinear existence estimate from the elementary endpoint properties. -/
theorem invariant_curve_of_correction (α c : ℝ) (f u : ℝ → ℝ) (K : NNReal)
    (hu_smooth : ContDiff ℝ ∞ u) (hu_periodic : Function.Periodic u 1)
    (hu_lipschitz : LipschitzWith K u) (hK : (K : ℝ) < 1)
    (hu_equation : ∀ t, discreteLaplacian α u t = c * f (t + u t)) :
    ∃ q : ℝ → ℝ,
      ContDiff ℝ ∞ q ∧ StrictMono q ∧
      Function.Periodic (fun t => q t - t) 1 ∧
      ∀ t : ℝ, q (t + α) - 2 * q t + q (t - α) = c * f (q t) := by
  let q := fun t : ℝ => t + u t
  refine ⟨q, contDiff_id.add hu_smooth,
    strictMono_id_add_of_lipschitz hK hu_lipschitz, ?_, ?_⟩
  · intro t
    simpa [q] using hu_periodic t
  · intro t
    calc
      q (t + α) - 2 * q t + q (t - α) = discreteLaplacian α u t := by
        simp only [q, discreteLaplacian]
        ring
      _ = c * f (t + u t) := hu_equation t
      _ = c * f (q t) := rfl

/-- At zero coupling, the identity lift is the invariant curve. -/
theorem zero_coupling_solution (α : ℝ) (f : ℝ → ℝ) :
    ∃ q : ℝ → ℝ,
      ContDiff ℝ ∞ q ∧ StrictMono q ∧
      Function.Periodic (fun t => q t - t) 1 ∧
      ∀ t : ℝ, q (t + α) - 2 * q t + q (t - α) = 0 * f (q t) := by
  refine ⟨id, contDiff_id, strictMono_id, ?_, ?_⟩
  · intro t
    simp
  · intro t
    simp [id]
    ring

end Submission.Helpers
