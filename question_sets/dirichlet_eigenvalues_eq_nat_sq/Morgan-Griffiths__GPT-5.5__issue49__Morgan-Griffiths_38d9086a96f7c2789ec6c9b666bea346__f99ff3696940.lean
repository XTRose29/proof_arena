/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: dirichlet_eigenvalues_eq_nat_sq
user: Morgan-Griffiths
model: GPT-5.5
submission_repo: Morgan-Griffiths/38d9086a96f7c2789ec6c9b666bea346
submission_ref: f99ff369694089eaa380b08a98ca9d931446a5fe
issue_number: 49
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Submission

open scoped Real

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-- On a real closed interval, a function whose derivative is zero everywhere is constant. -/
lemma const_on_Icc_of_hasDerivAt_zero
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f 0 x) :
    ∀ x ∈ Set.Icc a b, f x = f a := by
  intro x hx
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, le_of_lt hab⟩
  have hdiff : DifferentiableOn ℝ f (Set.Icc a b) := fun z hz =>
    (hf z hz).differentiableAt.differentiableWithinAt
  have hfd : ∀ z ∈ Set.Icc a b, fderivWithin ℝ f (Set.Icc a b) z = 0 := by
    intro z hz
    have huz : UniqueDiffWithinAt ℝ (Set.Icc a b) z :=
      (uniqueDiffOn_Icc hab z hz)
    have hzder : HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) (Set.Icc a b) z := by
      simpa [ContinuousLinearMap.toSpanSingleton_zero] using
        (hf z hz).hasFDerivAt.hasFDerivWithinAt
    exact hzder.fderivWithin huz
  exact (convex_Icc a b).is_const_of_fderivWithin_eq_zero hdiff hfd hx ha

/-- If `λ=0`, a Dirichlet solution of `y'' = -λ y` is zero on `[0,π]`. -/
lemma zero_lambda_solution_eq_zero_on_Icc
    {y : ℝ → ℝ} {J : Set ℝ}
    (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy' : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hy'' : ∀ x ∈ J, HasDerivAt (deriv y) 0 x)
    (hy0 : y 0 = 0) (hypi : y Real.pi = 0) :
    ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  let c : ℝ := deriv y 0
  have hderiv_const : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, deriv y x = c := by
    intro x hx
    exact const_on_Icc_of_hasDerivAt_zero hpi (fun z hz => hy'' z (hsub hz)) x hx
  let L : ℝ → ℝ := fun x => y x - c * x
  have hL_const : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, L x = L 0 := by
    apply const_on_Icc_of_hasDerivAt_zero hpi
    intro x hx
    have hyx : HasDerivAt y (deriv y x) x := hy' x (hsub hx)
    have hcx : HasDerivAt (fun t : ℝ => c * t) c x := by
      simpa using ((hasDerivAt_id x).const_mul c)
    have hsubder := hyx.sub hcx
    have hc_eq : deriv y x - c = 0 := by rw [hderiv_const x hx, sub_self]
    simpa [L, hc_eq] using hsubder
  have hL_zero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = c * x := by
    intro x hx
    have h : y x - c * x = 0 := by
      simpa [L, hy0] using hL_const x hx
    exact sub_eq_zero.mp h
  have hpi_mem : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt hpi, le_rfl⟩
  have hc : c = 0 := by
    have hmul : c * Real.pi = 0 := by
      have h := hL_zero Real.pi hpi_mem
      rw [hypi] at h
      exact h.symm
    exact (mul_eq_zero.mp hmul).resolve_right Real.pi_ne_zero
  intro x hx
  simpa [hc] using hL_zero x hx

/-- The first trigonometric Wronskian has zero derivative along a solution. -/
lemma trig_W_hasDerivAt_zero {y : ℝ → ℝ} {a lam x : ℝ}
    (ha2 : a ^ 2 = lam)
    (hyx : HasDerivAt y (deriv y x) x)
    (hy2x : HasDerivAt (deriv y) (-(lam * y x)) x) :
    HasDerivAt
      (fun t : ℝ => a * y t * Real.cos (a * t) - deriv y t * Real.sin (a * t))
      0 x := by
  have hlin : HasDerivAt (fun t : ℝ => a * t) a x := by
    simpa using ((hasDerivAt_id x).const_mul a)
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (a * t)) (-Real.sin (a * x) * a) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_cos (a * x)).comp x hlin
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (a * t)) (Real.cos (a * x) * a) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sin (a * x)).comp x hlin
  have hterm1 := (hyx.const_mul a).mul hcos
  have hterm2 := hy2x.mul hsin
  have h := hterm1.sub hterm2
  convert h using 1
  ring_nf
  rw [← ha2]
  ring

/-- The second trigonometric Wronskian has zero derivative along a solution. -/
lemma trig_V_hasDerivAt_zero {y : ℝ → ℝ} {a lam x : ℝ}
    (ha2 : a ^ 2 = lam)
    (hyx : HasDerivAt y (deriv y x) x)
    (hy2x : HasDerivAt (deriv y) (-(lam * y x)) x) :
    HasDerivAt
      (fun t : ℝ => a * y t * Real.sin (a * t) + deriv y t * Real.cos (a * t))
      0 x := by
  have hlin : HasDerivAt (fun t : ℝ => a * t) a x := by
    simpa using ((hasDerivAt_id x).const_mul a)
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (a * t)) (-Real.sin (a * x) * a) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_cos (a * x)).comp x hlin
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (a * t)) (Real.cos (a * x) * a) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sin (a * x)).comp x hlin
  have hterm1 := (hyx.const_mul a).mul hsin
  have hterm2 := hy2x.mul hcos
  have h := hterm1.add hterm2
  convert h using 1
  ring_nf
  rw [← ha2]
  ring

/-- The exponentially weighted decreasing mode is constant when `λ<0`. -/
lemma exp_minus_hasDerivAt_zero {y : ℝ → ℝ} {mu lam x : ℝ}
    (hmu2 : mu ^ 2 = -lam)
    (hyx : HasDerivAt y (deriv y x) x)
    (hy2x : HasDerivAt (deriv y) (-(lam * y x)) x) :
    HasDerivAt (fun t : ℝ => Real.exp (mu * t) * (deriv y t - mu * y t)) 0 x := by
  have hlin : HasDerivAt (fun t : ℝ => mu * t) mu x := by
    simpa using ((hasDerivAt_id x).const_mul mu)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (mu * t)) (Real.exp (mu * x) * mu) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp (mu * x)).comp x hlin
  have hmu_y : HasDerivAt (fun t : ℝ => mu * y t) (mu * deriv y x) x := hyx.const_mul mu
  have hP : HasDerivAt (fun t : ℝ => deriv y t - mu * y t) (-(lam * y x) - mu * deriv y x) x := by
    simpa using hy2x.sub hmu_y
  have h := hexp.mul hP
  convert h using 1
  ring_nf
  rw [hmu2]
  ring

/-- The exponentially weighted increasing mode is constant when `λ<0`. -/
lemma exp_plus_hasDerivAt_zero {y : ℝ → ℝ} {mu lam x : ℝ}
    (hmu2 : mu ^ 2 = -lam)
    (hyx : HasDerivAt y (deriv y x) x)
    (hy2x : HasDerivAt (deriv y) (-(lam * y x)) x) :
    HasDerivAt (fun t : ℝ => Real.exp (-(mu * t)) * (deriv y t + mu * y t)) 0 x := by
  have hlin : HasDerivAt (fun t : ℝ => -(mu * t)) (-mu) x := by
    have h : HasDerivAt (fun t : ℝ => mu * t) mu x := by
      simpa using ((hasDerivAt_id x).const_mul mu)
    simpa using h.neg
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(mu * t))) (Real.exp (-(mu * x)) * (-mu)) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp (-(mu * x))).comp x hlin
  have hmu_y : HasDerivAt (fun t : ℝ => mu * y t) (mu * deriv y x) x := hyx.const_mul mu
  have hR : HasDerivAt (fun t : ℝ => deriv y t + mu * y t) (-(lam * y x) + mu * deriv y x) x := by
    simpa using hy2x.add hmu_y
  have h := hexp.mul hR
  convert h using 1
  ring_nf
  rw [hmu2]
  ring

/-- There is no nonzero Dirichlet solution for a negative parameter. -/
lemma negative_lambda_no_nonzero_solution
    {lam : ℝ} {y : ℝ → ℝ} {J : Set ℝ}
    (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy' : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hy'' : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hy0 : y 0 = 0) (hypi : y Real.pi = 0)
    (hnonzero : ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0)
    (hlam_neg : lam < 0) : False := by
  let mu : ℝ := Real.sqrt (-lam)
  have hneg_pos : 0 < -lam := neg_pos.mpr hlam_neg
  have hmu_pos : 0 < mu := Real.sqrt_pos_of_pos hneg_pos
  have hmu2 : mu ^ 2 = -lam := Real.sq_sqrt (le_of_lt hneg_pos)
  let Q : ℝ → ℝ := fun t => Real.exp (mu * t) * (deriv y t - mu * y t)
  let S : ℝ → ℝ := fun t => Real.exp (-(mu * t)) * (deriv y t + mu * y t)
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_mem : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt hpi_pos, le_rfl⟩
  have hQ_const : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, Q x = Q 0 := by
    apply const_on_Icc_of_hasDerivAt_zero hpi_pos
    intro x hx
    exact exp_minus_hasDerivAt_zero hmu2 (hy' x (hsub hx)) (hy'' x (hsub hx))
  have hS_const : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, S x = S 0 := by
    apply const_on_Icc_of_hasDerivAt_zero hpi_pos
    intro x hx
    exact exp_plus_hasDerivAt_zero hmu2 (hy' x (hsub hx)) (hy'' x (hsub hx))
  have hq_eq : Real.exp (mu * Real.pi) * deriv y Real.pi = deriv y 0 := by
    have h := hQ_const Real.pi hpi_mem
    simpa [Q, hy0, hypi] using h
  have hs_eq : Real.exp (-(mu * Real.pi)) * deriv y Real.pi = deriv y 0 := by
    have h := hS_const Real.pi hpi_mem
    simpa [S, hy0, hypi] using h
  have hexp_diff_ne : Real.exp (mu * Real.pi) - Real.exp (-(mu * Real.pi)) ≠ 0 := by
    have harg : -(mu * Real.pi) < mu * Real.pi := by
      have : 0 < mu * Real.pi := mul_pos hmu_pos Real.pi_pos
      linarith
    have hlt : Real.exp (-(mu * Real.pi)) < Real.exp (mu * Real.pi) := Real.exp_lt_exp.mpr harg
    exact ne_of_gt (sub_pos.mpr hlt)
  have hdy_pi : deriv y Real.pi = 0 := by
    have hmul : (Real.exp (mu * Real.pi) - Real.exp (-(mu * Real.pi))) * deriv y Real.pi = 0 := by
      nlinarith [hq_eq, hs_eq]
    exact (mul_eq_zero.mp hmul).resolve_left hexp_diff_ne
  have hdy0 : deriv y 0 = 0 := by
    rw [hdy_pi, mul_zero] at hq_eq
    exact hq_eq.symm
  have hQ_zero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, Q x = 0 := by
    intro x hx
    have h := hQ_const x hx
    rw [h]
    simp [Q, hy0, hdy0]
  have hS_zero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, S x = 0 := by
    intro x hx
    have h := hS_const x hx
    rw [h]
    simp [S, hy0, hdy0]
  have hy_zero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, y x = 0 := by
    intro x hx
    have hP : deriv y x - mu * y x = 0 := by
      have h := hQ_zero x hx
      exact (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero (mu * x))
    have hR : deriv y x + mu * y x = 0 := by
      have h := hS_zero x hx
      exact (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero (-(mu * x)))
    nlinarith [hP, hR, hmu_pos]
  rcases hnonzero with ⟨x0, hx0, hx0ne⟩
  exact hx0ne (hy_zero x0 ⟨le_of_lt hx0.1, le_of_lt hx0.2⟩)

/-- A positive parameter admitting a nonzero Dirichlet solution is a square of a positive natural. -/
lemma positive_lambda_nat_square_of_solution
    {lam : ℝ} {y : ℝ → ℝ} {J : Set ℝ}
    (hsub : Set.Icc (0 : ℝ) Real.pi ⊆ J)
    (hy' : ∀ x ∈ J, HasDerivAt y (deriv y x) x)
    (hy'' : ∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x)
    (hy0 : y 0 = 0) (hypi : y Real.pi = 0)
    (hnonzero : ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0)
    (hlam_pos : 0 < lam) :
    ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 := by
  let a : ℝ := Real.sqrt lam
  have ha_pos : 0 < a := Real.sqrt_pos_of_pos hlam_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have ha2 : a ^ 2 = lam := Real.sq_sqrt (le_of_lt hlam_pos)
  let W : ℝ → ℝ := fun t => a * y t * Real.cos (a * t) - deriv y t * Real.sin (a * t)
  let V : ℝ → ℝ := fun t => a * y t * Real.sin (a * t) + deriv y t * Real.cos (a * t)
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_mem : Real.pi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt hpi_pos, le_rfl⟩
  have hW_const : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, W x = W 0 := by
    apply const_on_Icc_of_hasDerivAt_zero hpi_pos
    intro x hx
    exact trig_W_hasDerivAt_zero ha2 (hy' x (hsub hx)) (hy'' x (hsub hx))
  have hW_zero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, W x = 0 := by
    intro x hx
    have := hW_const x hx
    simpa [W, hy0] using this
  have hV_const : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, V x = V 0 := by
    apply const_on_Icc_of_hasDerivAt_zero hpi_pos
    intro x hx
    exact trig_V_hasDerivAt_zero ha2 (hy' x (hsub hx)) (hy'' x (hsub hx))
  have hsin_eq : Real.sin (a * Real.pi) = 0 := by
    by_contra hsin_ne
    have hdy_pi : deriv y Real.pi = 0 := by
      have hWp := hW_zero Real.pi hpi_mem
      have hor : deriv y Real.pi = 0 ∨ Real.sin (a * Real.pi) = 0 := by
        simpa [W, hypi] using hWp
      exact hor.resolve_right hsin_ne
    have hV_pi_zero : V Real.pi = 0 := by
      simp [V, hypi, hdy_pi]
    have hV0_zero : V 0 = 0 := by
      have hvp := hV_const Real.pi hpi_mem
      rw [hV_pi_zero] at hvp
      exact hvp.symm
    have hV_zero : ∀ x ∈ Set.Icc (0 : ℝ) Real.pi, V x = 0 := by
      intro x hx
      rw [hV_const x hx, hV0_zero]
    rcases hnonzero with ⟨x0, hx0Ioo, hx0ne⟩
    have hx0Icc : x0 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_of_lt hx0Ioo.1, le_of_lt hx0Ioo.2⟩
    have hident : W x0 * Real.cos (a * x0) + V x0 * Real.sin (a * x0) = a * y x0 := by
      simp [W, V]
      ring_nf
      rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one]
    have hay0 : a * y x0 = 0 := by
      rw [hW_zero x0 hx0Icc, hV_zero x0 hx0Icc] at hident
      simpa using hident.symm
    have hyx0 : y x0 = 0 := (mul_eq_zero.mp hay0).resolve_left ha_ne
    exact hx0ne hyx0
  rcases Real.sin_eq_zero_iff.mp hsin_eq with ⟨k, hk⟩
  have hk_real : (k : ℝ) = a := mul_right_cancel₀ Real.pi_ne_zero hk
  have hk_pos_int : 0 < k := by
    rw [← Int.cast_pos (R := ℝ)]
    simpa [hk_real] using ha_pos
  let n : ℕ := k.toNat
  have hn_int : (n : ℤ) = k := Int.toNat_of_nonneg (le_of_lt hk_pos_int)
  have hn_real : (n : ℝ) = a := by
    have hcast : ((n : ℤ) : ℝ) = (k : ℝ) := by rw [hn_int]
    simpa [Int.cast_natCast, hk_real] using hcast
  have hn_pos : 0 < n := by
    have : (0 : ℤ) < (n : ℤ) := by simpa [hn_int] using hk_pos_int
    exact_mod_cast this
  refine ⟨n, hn_pos, ?_⟩
  rw [← ha2, ← hn_real]

/-- Derivative of `sin (c x)`. -/
lemma sin_scaled_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (c * t)) (c * Real.cos (c * x)) x := by
  have hlin : HasDerivAt (fun t : ℝ => c * t) c x := by
    simpa using ((hasDerivAt_id x).const_mul c)
  simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (c * x)).comp x hlin

/-- Derivative of `c * cos (c x)`. -/
lemma cos_scaled_const_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun t : ℝ => c * Real.cos (c * t)) (-(c ^ 2 * Real.sin (c * x))) x := by
  have hlin : HasDerivAt (fun t : ℝ => c * t) c x := by
    simpa using ((hasDerivAt_id x).const_mul c)
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (c * t)) (-Real.sin (c * x) * c) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_cos (c * x)).comp x hlin
  convert hcos.const_mul c using 1
  ring

/-- For every positive natural `n`, `sin (n x)` is a nonzero Dirichlet solution for `λ=n²`. -/
lemma exists_solution_of_nat_square {lam : ℝ}
    {n : ℕ} (hn : 0 < n) (hlam : lam = (n : ℝ) ^ 2) :
    ∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0 := by
  let c : ℝ := n
  let y : ℝ → ℝ := fun x => Real.sin (c * x)
  refine ⟨y, Set.univ, isOpen_univ, by intro x hx; trivial, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := sin_scaled_hasDerivAt c x
    have hd : deriv y x = c * Real.cos (c * x) := h.deriv
    simpa [y, hd] using h
  · have hderiv_y : deriv y = fun x : ℝ => c * Real.cos (c * x) := by
      funext x
      exact (sin_scaled_hasDerivAt c x).deriv
    intro x hx
    have h := cos_scaled_const_hasDerivAt c x
    rw [hderiv_y]
    convert h using 1
    simp [y, hlam, c]
  · simp [y]
  · simp [y, c, Real.sin_nat_mul_pi]
  · let x0 : ℝ := Real.pi / (2 * c)
    have hc_pos : 0 < c := by dsimp [c]; exact_mod_cast hn
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    have hden_pos : 0 < 2 * c := mul_pos (by norm_num) hc_pos
    have hx0_pos : 0 < x0 := by
      dsimp [x0]
      exact div_pos Real.pi_pos hden_pos
    have hden_gt_one : 1 < 2 * c := by
      have hc_ge_one : 1 ≤ c := by
        have hn_one : 1 ≤ n := Nat.succ_le_iff.mpr hn
        dsimp [c]
        exact_mod_cast hn_one
      nlinarith
    have hx0_lt : x0 < Real.pi := by
      dsimp [x0]
      rw [div_lt_iff₀ hden_pos]
      nlinarith [Real.pi_pos, hden_gt_one]
    refine ⟨x0, ⟨hx0_pos, hx0_lt⟩, ?_⟩
    have harg : c * x0 = Real.pi / 2 := by
      dsimp [x0]
      field_simp [hc_ne]
    simp [y, harg, Real.sin_pi_div_two]
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/
theorem dirichlet_eigenvalues_eq_nat_sq (lam : ℝ) :
    (∃ (y : ℝ → ℝ) (J : Set ℝ),
        IsOpen J ∧ Set.Icc (0 : ℝ) Real.pi ⊆ J ∧
        (∀ x ∈ J, HasDerivAt y (deriv y x) x) ∧
        (∀ x ∈ J, HasDerivAt (deriv y) (-(lam * y x)) x) ∧
        y 0 = 0 ∧ y Real.pi = 0 ∧
        ∃ x ∈ Set.Ioo (0 : ℝ) Real.pi, y x ≠ 0) ↔
      ∃ n : ℕ, 0 < n ∧ lam = (n : ℝ) ^ 2 :=
/-ResultProofBegin-/by
  constructor
  · intro h
    rcases h with ⟨y, J, hJopen, hsub, hy', hy'', hy0, hypi, hnonzero⟩
    rcases lt_trichotomy lam 0 with hlam_neg | hlam_zero | hlam_pos
    · exact False.elim <|
        negative_lambda_no_nonzero_solution hsub hy' hy'' hy0 hypi hnonzero hlam_neg
    · have hy''0 : ∀ x ∈ J, HasDerivAt (deriv y) 0 x := by
        intro x hx
        simpa [hlam_zero] using hy'' x hx
      have hy_zero := zero_lambda_solution_eq_zero_on_Icc hsub hy' hy''0 hy0 hypi
      rcases hnonzero with ⟨x0, hx0, hx0ne⟩
      exact False.elim (hx0ne (hy_zero x0 ⟨le_of_lt hx0.1, le_of_lt hx0.2⟩))
    · exact positive_lambda_nat_square_of_solution hsub hy' hy'' hy0 hypi hnonzero hlam_pos
  · intro h
    rcases h with ⟨n, hn, hlam⟩
    exact exists_solution_of_nat_square hn hlam
/-ResultProofEnd-/
/-ResultEnd-/
end Submission