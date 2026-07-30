import Submission.Landau
import Submission.Growth
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

open Metric Set Filter

namespace Submission.ZeroGrowth

private lemma exists_entire_log_normalized {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hzero : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 = 0 ∧
      ∀ z, Complex.exp (g z) = f z / f 0 := by
  have hfderiv : Differentiable ℂ (deriv f) :=
    fun z => ((hf.differentiableOn.deriv isOpen_univ) z (Set.mem_univ z)).differentiableAt
      (by simp)
  have hlog : Differentiable ℂ (fun z => deriv f z / f z) :=
    hfderiv.div hf hzero
  obtain ⟨g, hg0, hg⟩ := hlog.isExactOn_univ.with_val_at 0 0
  have hgdiff : Differentiable ℂ g := fun z => (hg z (Set.mem_univ z)).differentiableAt
  refine ⟨g, hgdiff, hg0, ?_⟩
  have hquotdiff : Differentiable ℂ (fun z => Complex.exp (g z) / f z) :=
    hgdiff.cexp.div hf hzero
  have hquotderiv : ∀ z, deriv (fun w => Complex.exp (g w) / f w) z = 0 := by
    intro z
    have hge : HasDerivAt (fun w => Complex.exp (g w))
        (Complex.exp (g z) * (deriv f z / f z)) z :=
      (Complex.hasDerivAt_exp (g z)).comp z (hg z (Set.mem_univ z))
    have hq := (hge.div (hf z).hasDerivAt (hzero z)).deriv
    change deriv ((fun w => Complex.exp (g w)) / f) z = 0
    rw [hq]
    field_simp [hzero z]
    ring
  intro z
  have hconst := is_const_of_deriv_eq_zero hquotdiff hquotderiv z 0
  rw [hg0, Complex.exp_zero] at hconst
  rw [div_eq_iff (hzero z)] at hconst
  calc
    Complex.exp (g z) = (1 / f 0) * f z := hconst
    _ = f z / f 0 := by ring

private lemma iteratedDeriv_two_eq_zero_of_re_le_sqrt_growth {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) {A : ℝ} (hA : 0 ≤ A)
    (hre : ∀ z, (g z).re ≤ A * (1 + ‖z‖ * Real.sqrt ‖z‖)) (c : ℂ) :
    iteratedDeriv 2 g c = 0 := by
  apply norm_eq_zero.mp
  by_contra hd
  have hdpos : 0 < ‖iteratedDeriv 2 g c‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
  let B : ℝ := ‖g c‖
  let K : ℝ := 8 * (10 * A + 3 * B + 2)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max 1 (‖c‖ + 1)) (K / ‖iteratedDeriv 2 g c‖))
  have hN1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNc : ‖c‖ + 1 < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right 1 (‖c‖ + 1)) (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNK : K / ‖iteratedDeriv 2 g c‖ < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right (max 1 (‖c‖ + 1)) _) hN
  let R : ℝ := (N : ℝ) ^ 2
  let M : ℝ := A * (1 + 4 * R * Real.sqrt R) + 1
  let h : ℂ → ℂ := fun z => g (c + z)
  have hNpos : 0 < (N : ℝ) := by linarith
  have hRpos : 0 < R := by positivity
  have hcR : ‖c‖ < R := by
    dsimp [R]
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hhdiff : Differentiable ℂ h := by
    dsimp [h]
    fun_prop
  have hmaps : Set.MapsTo h (Metric.ball 0 R) {z : ℂ | z.re ≤ M} := by
    intro z hz
    have hzR : ‖z‖ < R := by simpa [Metric.mem_ball, Complex.dist_eq] using hz
    have hcz : ‖c + z‖ ≤ 2 * R := by
      calc
        ‖c + z‖ ≤ ‖c‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 2 * R := by linarith
    have hsqrtR : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
    have hsqrtR_sq : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hRpos.le
    have hsqrtcz : Real.sqrt ‖c + z‖ ≤ 2 * Real.sqrt R := by
      have hsqrt_le : Real.sqrt ‖c + z‖ ≤ Real.sqrt (2 * R) :=
        Real.sqrt_le_sqrt hcz
      have hsqrt2R_nonneg : 0 ≤ Real.sqrt (2 * R) := Real.sqrt_nonneg _
      have hsqrt2R_sq : (Real.sqrt (2 * R)) ^ 2 = 2 * R :=
        Real.sq_sqrt (by positivity)
      nlinarith [sq_nonneg (Real.sqrt (2 * R) - 2 * Real.sqrt R)]
    have hprod : ‖c + z‖ * Real.sqrt ‖c + z‖ ≤ 4 * R * Real.sqrt R := by
      nlinarith [norm_nonneg (c + z), Real.sqrt_nonneg ‖c + z‖]
    change (g (c + z)).re ≤ M
    have hgrowth := hre (c + z)
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left hprod hA]
  have hsphere : ∀ z ∈ Metric.sphere 0 (R / 2), ‖h z‖ ≤ 2 * M + 3 * B := by
    intro z hz
    have hzNorm : ‖z‖ = R / 2 := by
      simpa [Metric.mem_sphere, Complex.dist_eq] using hz
    have hzBall : z ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero, hzNorm]
      linarith
    have hbc := Complex.borelCaratheodory hMpos hhdiff.differentiableOn hmaps hRpos hzBall
    rw [hzNorm] at hbc
    have hh0 : ‖h 0‖ = B := by simp [h, B]
    rw [hh0] at hbc
    convert hbc using 1
    field_simp
    ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := h) 2 (half_pos hRpos) hhdiff.diffContOnCl hsphere
  have hiter : iteratedDeriv 2 h 0 = iteratedDeriv 2 g c := by
    have hshift := congrFun (iteratedDeriv_comp_const_add (n := 2) (f := g) (s := c)) 0
    simpa [h] using hshift
  rw [hiter] at hcauchy
  have hbound : ‖iteratedDeriv 2 g c‖ ≤ 8 * (2 * M + 3 * B) / R ^ 2 := by
    convert hcauchy using 1
    norm_num
    field_simp
    ring
  have hsqrtR_eq : Real.sqrt R = (N : ℝ) := by
    dsimp [R]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hNpos]
  have hMbound : M ≤ (5 * A + 1) * (N : ℝ) ^ 3 := by
    dsimp [M]
    rw [hsqrtR_eq]
    dsimp [R]
    have hN3 : 1 ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N : ℝ) - 1)]
    nlinarith [mul_nonneg hA (zero_le_one.trans hN3)]
  have hfinal : ‖iteratedDeriv 2 g c‖ ≤ K / (N : ℝ) := by
    calc
      ‖iteratedDeriv 2 g c‖ ≤ 8 * (2 * M + 3 * B) / R ^ 2 := hbound
      _ ≤ K / (N : ℝ) := by
        dsimp [K, R]
        have hN4pos : 0 < (N : ℝ) ^ 4 := by positivity
        rw [show ((N : ℝ) ^ 2) ^ 2 = (N : ℝ) ^ 4 by ring]
        change 8 * (2 * M + 3 * B) / (N : ℝ) ^ 4 ≤
          8 * (10 * A + 3 * B + 2) / (N : ℝ)
        apply (le_div_iff₀ hNpos).2
        rw [div_mul_eq_mul_div, div_le_iff₀ hN4pos]
        have hB : 0 ≤ B := norm_nonneg _
        have hN3 : 1 ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N : ℝ) - 1)]
        nlinarith [mul_le_mul_of_nonneg_right hMbound hNpos.le,
          mul_le_mul_of_nonneg_left hN3 hB]
  have hKnonneg : 0 ≤ K := by
    dsimp [K, B]
    positivity
  have hlt : K / (N : ℝ) < ‖iteratedDeriv 2 g c‖ := by
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hdpos] at hNK
    nlinarith
  exact (not_lt_of_ge hfinal) hlt

private lemma affine_of_re_le_sqrt_growth {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) {A : ℝ} (hA : 0 ≤ A)
    (hre : ∀ z, (g z).re ≤ A * (1 + ‖z‖ * Real.sqrt ‖z‖)) :
    ∃ a b : ℂ, ∀ z, g z = a * z + b := by
  have hsecond : ∀ c, iteratedDeriv 2 g c = 0 :=
    iteratedDeriv_two_eq_zero_of_re_le_sqrt_growth hg hA hre
  have hgderiv : Differentiable ℂ (deriv g) :=
    fun z => ((hg.differentiableOn.deriv isOpen_univ) z (Set.mem_univ z)).differentiableAt
      (by simp)
  have hderiv_zero : ∀ z, deriv (deriv g) z = 0 := by
    intro z
    simpa [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ] using hsecond z
  have hderiv_const : ∀ z, deriv g z = deriv g 0 := fun z =>
    is_const_of_deriv_eq_zero hgderiv hderiv_zero z 0
  let a := deriv g 0
  let q : ℂ → ℂ := fun z => g z - a * z
  have hqdiff : Differentiable ℂ q := by
    dsimp [q]
    fun_prop
  have hqderiv : ∀ z, deriv q z = 0 := by
    intro z
    have hq := ((hg z).hasDerivAt.sub ((hasDerivAt_id z).const_mul a)).deriv
    have hfun : (g - fun y => a * id y) = fun w => g w - a * w := by rfl
    rw [hfun] at hq
    have hq' : deriv (fun w => g w - a * w) z = deriv g z - a := by
      simpa using hq
    change deriv (fun w => g w - a * w) z = 0
    rw [hq']
    simp [a, hderiv_const z]
  refine ⟨a, g 0, fun z => ?_⟩
  have hconst := is_const_of_deriv_eq_zero hqdiff hqderiv z 0
  calc
    g z = (g z - a * z) + a * z := by ring
    _ = g 0 + a * z := by rw [show g z - a * z = g 0 by simpa [q] using hconst]
    _ = a * z + g 0 := by ring

theorem eq_exp_affine_of_sqrt_growth {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hzero : ∀ z, f z ≠ 0) {A : ℝ} (hA : 0 ≤ A)
    (hgrowth : ∀ z, ‖f z‖ ≤ Real.exp (A * (1 + ‖z‖ * Real.sqrt ‖z‖))) :
    ∃ a b : ℂ, ∀ z, f z = Complex.exp (a * z + b) := by
  obtain ⟨g, hg, hg0, hexp⟩ := exists_entire_log_normalized hf hzero
  let D : ℝ := ‖(f 0)⁻¹‖
  have hD : 0 ≤ D := norm_nonneg _
  have hre : ∀ z, (g z).re ≤ (A + D) * (1 + ‖z‖ * Real.sqrt ‖z‖) := by
    intro z
    have hnormexp : Real.exp (g z).re = ‖f z / f 0‖ := by
      rw [← Complex.norm_exp, hexp]
    have hDexp : D ≤ Real.exp D := by
      exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp D)
    have hnorm : ‖f z / f 0‖ ≤
        Real.exp (A * (1 + ‖z‖ * Real.sqrt ‖z‖) + D) := by
      rw [norm_div, div_eq_mul_inv, ← norm_inv, Real.exp_add]
      exact mul_le_mul (hgrowth z) hDexp (norm_nonneg _) (Real.exp_nonneg _)
    have hre' : (g z).re ≤ A * (1 + ‖z‖ * Real.sqrt ‖z‖) + D := by
      rw [← Real.exp_le_exp, hnormexp]
      exact hnorm
    have hx : 0 ≤ ‖z‖ * Real.sqrt ‖z‖ :=
      mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [mul_nonneg hD hx]
  obtain ⟨a, b, hab⟩ := affine_of_re_le_sqrt_growth hg (add_nonneg hA hD) hre
  refine ⟨a, b + Complex.log (f 0), fun z => ?_⟩
  have hmul : Complex.exp (g z) * f 0 = f z := by
    rw [hexp, div_mul_cancel₀ _ (hzero 0)]
  calc
    f z = Complex.exp (g z) * f 0 := hmul.symm
    _ = Complex.exp (a * z + b) * Complex.exp (Complex.log (f 0)) := by
      rw [hab, Complex.exp_log (hzero 0)]
    _ = Complex.exp (a * z + (b + Complex.log (f 0))) := by
      rw [← Complex.exp_add]
      congr 1
      ring

end Submission.ZeroGrowth

namespace Submission.ZeroExistence

open MeasureTheory

private lemma norm_Gamma_le_real_Gamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  calc
    ‖∫ t : ℝ in Set.Ioi 0, ((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ ≤
        ∫ t : ℝ in Set.Ioi 0, ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * t ^ (z.re - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change ‖((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ (z - 1)‖ =
        Real.exp (-t) * t ^ (z.re - 1)
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _),
        Complex.norm_cpow_eq_rpow_re_of_pos ht]
      simp

private lemma real_Gamma_le_exp_eight_mul_sqrt {x : ℝ} (hx : 2 ≤ x) :
    Real.Gamma x ≤ Real.exp (8 * x * Real.sqrt x) := by
  let n := Nat.ceil x
  have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
  have hnlt : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hn2 : 2 ≤ (n : ℝ) := hx.trans hxn
  have hnpos : 0 < n := by exact_mod_cast (zero_lt_two.trans_le hn2)
  have hgamma : Real.Gamma x ≤ Real.Gamma n :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (by simpa) (by simpa using hn2) hxn
  have hgammaNat : Real.Gamma n = ((n - 1).factorial : ℝ) := by
    calc
      Real.Gamma n = Real.Gamma ((n - 1 : ℕ) + 1) := by
        congr 1
        norm_cast
        omega
      _ = ((n - 1).factorial : ℝ) := Real.Gamma_nat_eq_factorial (n - 1)
  have hfac : ((n - 1).factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast ((Nat.factorial_le (Nat.sub_le n 1)).trans n.factorial_le_pow)
  have hnlog : Real.log n ≤ 2 * Real.sqrt n := by
    have h := Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    convert h using 1
    ring
  have hpowexp : (n : ℝ) ^ n ≤ Real.exp (2 * n * Real.sqrt n) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by exact_mod_cast hnpos)]
    rw [Real.exp_le_exp]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity)
      (sub_nonneg.mpr hnlog)]
  have hnx : (n : ℝ) ≤ 2 * x := by linarith
  have hsqrtn : Real.sqrt n ≤ 2 * Real.sqrt x := by
    have hsqrt_le : Real.sqrt n ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt hnx
    have hsqrtx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    have hsqrtx_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
    have hsqrt2x : 0 ≤ Real.sqrt (2 * x) := Real.sqrt_nonneg _
    have hsqrt2x_sq : (Real.sqrt (2 * x)) ^ 2 = 2 * x := Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (Real.sqrt (2 * x) - 2 * Real.sqrt x)]
  calc
    Real.Gamma x ≤ Real.Gamma n := hgamma
    _ = ((n - 1).factorial : ℝ) := hgammaNat
    _ ≤ (n : ℝ) ^ n := hfac
    _ ≤ Real.exp (2 * n * Real.sqrt n) := hpowexp
    _ ≤ Real.exp (8 * x * Real.sqrt x) := by
      rw [Real.exp_le_exp]
      have hprod := mul_le_mul hnx hsqrtn (Real.sqrt_nonneg n)
        (show 0 ≤ 2 * x by positivity)
      nlinarith

lemma chiFour_rootNumber_eq_one :
    DirichletCharacter.rootNumber Submission.Helpers.chiFour = 1 := by
  have hsum :
      gaussSum Submission.Helpers.chiFour (ZMod.stdAddChar (N := 4)) = 2 * Complex.I := by
    rw [gaussSum, ← (ZMod.finEquiv 4).toEquiv.sum_comp]
    have hfin (j : Fin 4) : (ZMod.finEquiv 4) j = (j.val : ZMod 4) := by
      apply ZMod.val_injective
      change j.val = j.val % 4
      exact (Nat.mod_eq_of_lt j.isLt).symm
    have hfun :
        (fun j : Fin 4 => Submission.Helpers.chiFour ((ZMod.finEquiv 4).toEquiv j) *
          ZMod.stdAddChar ((ZMod.finEquiv 4).toEquiv j)) =
        fun j : Fin 4 => Submission.Helpers.chiFour (j.val : ZMod 4) *
          ZMod.stdAddChar (j.val : ZMod 4) := by
      funext j
      rw [show (ZMod.finEquiv 4).toEquiv j = (j.val : ZMod 4) by exact hfin j]
    rw [hfun]
    have hstd1 : ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
      rw [show (1 : ZMod 4) = ((1 : ℤ) : ZMod 4) by rfl, ZMod.stdAddChar_coe]
      norm_num
      rw [show 2 * (Real.pi : ℂ) * Complex.I / 4 =
        (Real.pi : ℂ) / 2 * Complex.I by ring]
      exact Complex.exp_pi_div_two_mul_I
    have hstd3 : ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
      rw [show (3 : ZMod 4) = ((3 : ℤ) : ZMod 4) by rfl, ZMod.stdAddChar_coe]
      calc
        Complex.exp (2 * Real.pi * Complex.I * (3 : ℤ) / 4) =
            Complex.exp (-Real.pi / 2 * Complex.I + 2 * Real.pi * Complex.I) := by
          congr 1
          norm_num
          ring
        _ = -Complex.I := by
          rw [Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I,
            Complex.exp_two_pi_mul_I, mul_one]
    norm_num [ZMod.finEquiv, RingEquiv.refl_apply, Submission.Helpers.chiFour, ZMod.χ₄,
      ZMod.stdAddChar_coe, Fin.sum_univ_succ, Complex.exp_mul_I, hstd1, hstd3]
    ring
  rw [DirichletCharacter.rootNumber]
  rw [if_neg Submission.Helpers.chiFour_odd.not_even]
  rw [hsum]
  rw [show ((4 : ℕ) : ℂ) = (2 : ℂ) ^ 2 by norm_num]
  rw [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by ring]
  rw [Complex.sq_cpow_two_inv (by norm_num)]
  norm_num

noncomputable def chiFourXi (s : ℂ) : ℂ :=
  (4 : ℂ) ^ (s / 2) *
    DirichletCharacter.completedLFunction Submission.Helpers.chiFour s

lemma differentiable_chiFourXi : Differentiable ℂ chiFourXi := by
  letI : NeZero (4 : ℂ) := ⟨by norm_num⟩
  apply Differentiable.mul
  · exact (differentiable_const_cpow_of_neZero (4 : ℂ)).comp (by fun_prop)
  · exact DirichletCharacter.differentiable_completedLFunction
      Submission.Helpers.chiFour_ne_one

lemma chiFourXi_one_sub (s : ℂ) : chiFourXi (1 - s) = chiFourXi s := by
  rw [chiFourXi, Submission.Helpers.chiFour_completedLFunction_one_sub,
    chiFour_rootNumber_eq_one, mul_one]
  rw [← mul_assoc, ← Complex.cpow_add _ _ (by norm_num : (4 : ℂ) ≠ 0)]
  congr 1
  ring_nf

private lemma chiFour_LSeries_term_even (k m : ℕ) :
    LSeries.term (Submission.Helpers.chiFour ·) (k : ℂ) (2 * m) = 0 := by
  rw [LSeries.term_def]
  split
  · rfl
  · rw [Submission.Analytic.chiFour_apply_nat, ZMod.χ₄_nat_eq_if_mod_four]
    norm_num

private lemma chiFour_LSeries_term_odd (k m : ℕ) :
    LSeries.term (Submission.Helpers.chiFour ·) (k : ℂ) (2 * m + 1) =
      (((-1 : ℝ) ^ m / (2 * m + 1 : ℝ) ^ k : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero (by omega), Submission.Analytic.chiFour_apply_nat,
    ZMod.χ₄_eq_neg_one_pow (by omega : (2 * m + 1) % 2 = 1)]
  rw [show (2 * m + 1) / 2 = m by omega, Complex.cpow_natCast]
  push_cast
  norm_cast

private lemma chiFour_LFunction_nat_eq_alternating (k : ℕ) (hk : 2 ≤ k) :
    DirichletCharacter.LFunction Submission.Helpers.chiFour (k : ℂ) =
      ((∑' m : ℕ, (-1 : ℝ) ^ m / (2 * m + 1 : ℝ) ^ k : ℝ) : ℂ) := by
  have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re
    Submission.Helpers.chiFour (s := (k : ℂ)) (by simp; omega)
  let f : ℕ → ℂ := LSeries.term (Submission.Helpers.chiFour ·) (k : ℂ)
  have hinj : Function.Injective (fun m : ℕ => (2 * m + 1 : ℕ)) := by
    intro m n h
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel h)
  have he : HasSum (fun m => f (2 * m)) 0 := by
    simp [f, chiFour_LSeries_term_even]
  have hoSum : Summable (fun m => f (2 * m + 1)) := by
    exact hsum.comp_injective hinj
  have ho : HasSum (fun m => f (2 * m + 1))
      ((∑' m : ℕ, (-1 : ℝ) ^ m / (2 * m + 1 : ℝ) ^ k : ℝ) : ℂ) := by
    let r : ℕ → ℝ := fun m => (-1 : ℝ) ^ m / (2 * m + 1 : ℝ) ^ k
    have hbase := (Real.summable_one_div_nat_pow.mpr (one_lt_two.trans_le hk)).comp_injective hinj
    have hpossum : Summable (fun m : ℕ => 1 / (2 * m + 1 : ℝ) ^ k) := by
      exact hbase.congr fun m => by
        simp
    have hrsum : Summable r := by
      simpa [r, div_eq_mul_inv] using hpossum.alternating
    have hseq : (fun m => f (2 * m + 1)) = fun m => (r m : ℂ) := by
      funext m
      exact chiFour_LSeries_term_odd k m
    rw [hseq]
    exact Complex.hasSum_ofReal.mpr hrsum.hasSum
  have hall := he.even_add_odd ho
  rw [DirichletCharacter.LFunction_eq_LSeries Submission.Helpers.chiFour (by simp; omega),
    LSeries]
  simpa [f] using hall.tsum_eq

private lemma chiFour_LFunction_nat_re_lower (k : ℕ) (hk : 2 ≤ k) :
    (1 / 2 : ℝ) ≤
      (DirichletCharacter.LFunction Submission.Helpers.chiFour (k : ℂ)).re := by
  let u : ℕ → ℝ := fun m => 1 / (2 * m + 1 : ℝ) ^ k
  have hinj : Function.Injective (fun m : ℕ => (2 * m + 1 : ℕ)) := by
    intro m n h
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel h)
  have hbase := (Real.summable_one_div_nat_pow.mpr (one_lt_two.trans_le hk)).comp_injective hinj
  have husum : Summable u := by
    exact hbase.congr fun m => by simp [u]
  have huanti : Antitone u := by
    intro m n hmn
    dsimp [u]
    gcongr
  have hlower := huanti.alternating_series_le_tendsto
    husum.tendsto_alternating_series_tsum 1
  have hlower' : 1 - 1 / (3 : ℝ) ^ k ≤
      ∑' m : ℕ, (-1 : ℝ) ^ m / (2 * m + 1 : ℝ) ^ k := by
    have hfinite :
        ∑ x ∈ Finset.range 2, (-1 : ℝ) ^ x * u x = 1 - 1 / (3 : ℝ) ^ k := by
      norm_num [u, Finset.sum_range_succ, div_eq_mul_inv]
      ring
    rw [hfinite] at hlower
    simpa [u, div_eq_mul_inv] using hlower
  have hpow : (9 : ℝ) ≤ (3 : ℝ) ^ k := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 3) hk
  have hfrac : 1 / (3 : ℝ) ^ k ≤ 1 / 9 := by
    exact one_div_le_one_div_of_le (by positivity) hpow
  rw [chiFour_LFunction_nat_eq_alternating k hk]
  simp only [Complex.ofReal_re]
  linarith

private lemma four_cpow_odd_half (n : ℕ) :
    (4 : ℂ) ^ (((2 * n + 1 : ℕ) : ℂ) / 2) = 2 * (4 : ℂ) ^ n := by
  have hsqrt : (4 : ℂ) ^ (1 / 2 : ℂ) = 2 := by
    rw [show (4 : ℂ) = (2 : ℂ) ^ 2 by norm_num]
    rw [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by ring]
    exact Complex.sq_cpow_two_inv (by norm_num)
  rw [show (((2 * n + 1 : ℕ) : ℂ) / 2) = (n : ℂ) + 1 / 2 by
    push_cast
    ring]
  rw [Complex.cpow_add _ _ (by norm_num), Complex.cpow_natCast, hsqrt]
  ring

private lemma norm_chiFour_gammaFactor_odd_nat (n : ℕ) :
    ‖DirichletCharacter.gammaFactor Submission.Helpers.chiFour ((2 * n + 1 : ℕ) : ℂ)‖ =
      n.factorial / Real.pi ^ (n + 1) := by
  rw [Submission.Helpers.chiFour_odd.gammaFactor_def, Complex.Gammaℝ_def]
  have harg : ((((2 * n + 1 : ℕ) : ℂ) + 1) / 2) = ((n + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  have hexp : (-(((2 * n + 1 : ℕ) : ℂ) + 1)) / 2 = -((n + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [harg, hexp, show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by norm_cast,
    Complex.Gamma_nat_eq_factorial]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
    Complex.norm_natCast]
  rw [Real.rpow_neg (by positivity)]
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
  field_simp

lemma norm_chiFourXi_odd_nat_lower (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) / 4 ≤ ‖chiFourXi ((2 * n + 1 : ℕ) : ℂ)‖ := by
  let s : ℂ := ((2 * n + 1 : ℕ) : ℂ)
  have hsRe : 2 ≤ s.re := by
    dsimp [s]
    norm_num
    exact_mod_cast (show 2 ≤ 2 * n + 1 by omega)
  have hgammaNe : DirichletCharacter.gammaFactor Submission.Helpers.chiFour s ≠ 0 := by
    rw [Submission.Helpers.chiFour_odd.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp [s]; positivity)
  have hrelation := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    Submission.Helpers.chiFour s (Or.inr (by norm_num : (4 : ℕ) ≠ 1))
  have hcompleted :
      DirichletCharacter.completedLFunction Submission.Helpers.chiFour s =
        DirichletCharacter.gammaFactor Submission.Helpers.chiFour s *
          DirichletCharacter.LFunction Submission.Helpers.chiFour s := by
    rw [eq_div_iff hgammaNe] at hrelation
    rw [← hrelation]
    ring
  have hLlower := chiFour_LFunction_nat_re_lower (2 * n + 1) (by omega)
  have hLnorm : (1 / 2 : ℝ) ≤
      ‖DirichletCharacter.LFunction Submission.Helpers.chiFour s‖ := by
    exact hLlower.trans (Complex.re_le_norm _)
  have hfourNorm : ‖(4 : ℂ) ^ (s / 2)‖ = 2 * (4 : ℝ) ^ n := by
    dsimp [s]
    rw [four_cpow_odd_half]
    norm_num [norm_pow]
  have hgammaNorm :
      ‖DirichletCharacter.gammaFactor Submission.Helpers.chiFour s‖ =
        n.factorial / Real.pi ^ (n + 1) := by
    simpa [s] using norm_chiFour_gammaFactor_odd_nat n
  have hpiPow : Real.pi ^ (n + 1) ≤ (4 : ℝ) ^ (n + 1) := by
    exact pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le (n + 1)
  have hgammaLower :
      (n.factorial : ℝ) / (4 : ℝ) ^ (n + 1) ≤
        n.factorial / Real.pi ^ (n + 1) := by
    gcongr
  rw [chiFourXi, hcompleted, norm_mul, norm_mul, hfourNorm, hgammaNorm]
  calc
    (n.factorial : ℝ) / 4 =
        (2 * (4 : ℝ) ^ n) *
          ((n.factorial : ℝ) / (4 : ℝ) ^ (n + 1)) * (1 / 2) := by
      field_simp
      ring
    _ ≤ (2 * (4 : ℝ) ^ n) *
        ((n.factorial : ℝ) / Real.pi ^ (n + 1)) *
          ‖DirichletCharacter.LFunction Submission.Helpers.chiFour s‖ := by
      have hscale : 0 ≤ 2 * (4 : ℝ) ^ n := by positivity
      have hupper : 0 ≤
          (2 * (4 : ℝ) ^ n) * ((n.factorial : ℝ) / Real.pi ^ (n + 1)) := by
        positivity
      simpa only [mul_assoc] using
        (mul_le_mul (mul_le_mul_of_nonneg_left hgammaLower hscale) hLnorm
          (by norm_num : (0 : ℝ) ≤ 1 / 2) hupper)
    _ = (2 * (4 : ℝ) ^ n) *
        ((n.factorial : ℝ) / Real.pi ^ (n + 1) *
          ‖DirichletCharacter.LFunction Submission.Helpers.chiFour s‖) := by
      ring

noncomputable def chiFourLNormBound : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (Submission.Helpers.chiFour ·) (2 : ℂ) n‖

private lemma chiFourLNormBound_nonneg : 0 ≤ chiFourLNormBound :=
  tsum_nonneg fun _ => norm_nonneg _

private lemma norm_chiFour_LFunction_le_LNormBound {s : ℂ} (hs : 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction Submission.Helpers.chiFour s‖ ≤ chiFourLNormBound := by
  have hsOne : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  have hsumS := DirichletCharacter.LSeriesSummable_of_one_lt_re
    Submission.Helpers.chiFour hsOne
  have hsumTwo := DirichletCharacter.LSeriesSummable_of_one_lt_re
    Submission.Helpers.chiFour (s := (2 : ℂ)) (by norm_num)
  rw [DirichletCharacter.LFunction_eq_LSeries Submission.Helpers.chiFour hsOne, LSeries]
  exact (norm_tsum_le_tsum_norm hsumS.norm).trans
    (hsumS.norm.tsum_mono hsumTwo.norm fun n =>
      LSeries.norm_term_le_of_re_le_re (Submission.Helpers.chiFour ·) hs n)

private lemma norm_chiFour_gammaFactor_le_exp {s : ℂ} (hs : 3 ≤ s.re) :
    ‖DirichletCharacter.gammaFactor Submission.Helpers.chiFour s‖ ≤
      Real.exp (8 * s.re * Real.sqrt s.re) := by
  rw [Submission.Helpers.chiFour_odd.gammaFactor_def, Complex.Gammaℝ_def, norm_mul]
  let x : ℝ := (s.re + 1) / 2
  have hx : 2 ≤ x := by dsimp [x]; linarith
  have hxpos : 0 < x := zero_lt_two.trans_le hx
  have hpi : ‖(Real.pi : ℂ) ^ (-(s + 1) / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hpiOne : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    apply Real.rpow_le_one_of_one_le_of_nonpos hpiOne
    have hre : (-(s + 1) / 2).re = -(s.re + 1) / 2 := by
      simp
    rw [hre]
    linarith
  have hgamma : ‖Complex.Gamma ((s + 1) / 2)‖ ≤ Real.Gamma x := by
    simpa [x] using
      (norm_Gamma_le_real_Gamma (z := (s + 1) / 2) (by simp; linarith))
  have hgammaExp : Real.Gamma x ≤ Real.exp (8 * x * Real.sqrt x) :=
    real_Gamma_le_exp_eight_mul_sqrt hx
  have hxle : x ≤ s.re := by dsimp [x]; linarith
  have hsnonneg : 0 ≤ s.re := by linarith
  have hsqrt : Real.sqrt x ≤ Real.sqrt s.re := Real.sqrt_le_sqrt hxle
  have hprod : x * Real.sqrt x ≤ s.re * Real.sqrt s.re :=
    mul_le_mul hxle hsqrt (Real.sqrt_nonneg _) hsnonneg
  calc
    ‖(Real.pi : ℂ) ^ (-(s + 1) / 2)‖ * ‖Complex.Gamma ((s + 1) / 2)‖ ≤
        1 * Real.Gamma x :=
      mul_le_mul hpi hgamma (norm_nonneg _) (by positivity)
    _ ≤ Real.exp (8 * x * Real.sqrt x) := by simpa using hgammaExp
    _ ≤ Real.exp (8 * s.re * Real.sqrt s.re) := by
      exact Real.exp_le_exp.mpr
        (by simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 8)))

noncomputable def chiFourXiRightGrowthConstant : ℝ :=
  16 * Submission.Growth.chiFourCompletedStripBound (1 / 2) 3 +
    chiFourLNormBound + 10

private lemma chiFourXiRightGrowthConstant_nonneg :
    0 ≤ chiFourXiRightGrowthConstant := by
  unfold chiFourXiRightGrowthConstant
  have hstrip := Submission.Growth.chiFourCompletedStripBound_nonneg (1 / 2) 3
  nlinarith [chiFourLNormBound_nonneg]

private lemma norm_four_cpow_half_le_sixteen {s : ℂ} (hs : s.re ≤ 3) :
    ‖(4 : ℂ) ^ (s / 2)‖ ≤ 16 := by
  change ‖((4 : ℝ) : ℂ) ^ (s / 2)‖ ≤ 16
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hexp : (s / 2).re ≤ (2 : ℝ) := by simp; linarith
  calc
    (4 : ℝ) ^ (s / 2).re ≤ (4 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 16 := by norm_num

private lemma norm_four_cpow_half_le_exp {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(4 : ℂ) ^ (s / 2)‖ ≤ Real.exp (2 * s.re) := by
  change ‖((4 : ℝ) : ℂ) ^ (s / 2)‖ ≤ Real.exp (2 * s.re)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 4),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h ⊢
    exact h
  have hhalf : (s / 2).re = s.re / 2 := by simp
  rw [hhalf]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hlog)]

private lemma norm_chiFourXi_right_growth {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖chiFourXi s‖ ≤ Real.exp
      (chiFourXiRightGrowthConstant * (1 + ‖s‖ * Real.sqrt ‖s‖)) := by
  let B := chiFourXiRightGrowthConstant
  have hB : 0 ≤ B := chiFourXiRightGrowthConstant_nonneg
  have hnorm : 0 ≤ ‖s‖ * Real.sqrt ‖s‖ := by positivity
  by_cases hs3 : s.re ≤ 3
  · have hcompleted := Submission.Growth.norm_chiFour_completedLFunction_le_stripBound
      (s := s) hs hs3
    have hpow := norm_four_cpow_half_le_sixteen hs3
    have hxi : ‖chiFourXi s‖ ≤
        16 * Submission.Growth.chiFourCompletedStripBound (1 / 2) 3 := by
      rw [chiFourXi, norm_mul]
      exact mul_le_mul hpow hcompleted (norm_nonneg _) (by norm_num)
    have hconst :
        16 * Submission.Growth.chiFourCompletedStripBound (1 / 2) 3 ≤ B := by
      dsimp [B, chiFourXiRightGrowthConstant]
      nlinarith [chiFourLNormBound_nonneg]
    have hBexp : B ≤ Real.exp B :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp B)
    have hexpMono : Real.exp B ≤ Real.exp (B * (1 + ‖s‖ * Real.sqrt ‖s‖)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hB hnorm]
    exact hxi.trans (hconst.trans (hBexp.trans hexpMono))
  · have hs3' : 3 ≤ s.re := le_of_not_ge hs3
    have hs2 : 2 ≤ s.re := by linarith
    have hsnonneg : 0 ≤ s.re := by linarith
    have hgammaNe :
        DirichletCharacter.gammaFactor Submission.Helpers.chiFour s ≠ 0 := by
      rw [Submission.Helpers.chiFour_odd.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    have hrelation := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
      Submission.Helpers.chiFour s (Or.inr (by norm_num : (4 : ℕ) ≠ 1))
    have hcompleted :
        DirichletCharacter.completedLFunction Submission.Helpers.chiFour s =
          DirichletCharacter.gammaFactor Submission.Helpers.chiFour s *
            DirichletCharacter.LFunction Submission.Helpers.chiFour s := by
      rw [eq_div_iff hgammaNe] at hrelation
      rw [← hrelation]
      ring
    have hpow := norm_four_cpow_half_le_exp hsnonneg
    have hgamma := norm_chiFour_gammaFactor_le_exp hs3'
    have hL := norm_chiFour_LFunction_le_LNormBound hs2
    have hLexp : chiFourLNormBound ≤ Real.exp chiFourLNormBound :=
      (le_add_of_nonneg_right zero_le_one).trans
        (Real.add_one_le_exp chiFourLNormBound)
    have hxi : ‖chiFourXi s‖ ≤
        Real.exp (2 * s.re) * Real.exp (8 * s.re * Real.sqrt s.re) *
          Real.exp chiFourLNormBound := by
      rw [chiFourXi, hcompleted, norm_mul, norm_mul]
      rw [← mul_assoc]
      exact mul_le_mul (mul_le_mul hpow hgamma (norm_nonneg _) (Real.exp_nonneg _))
        (hL.trans hLexp) (norm_nonneg _) (by positivity)
    have hsqrtOne : 1 ≤ Real.sqrt s.re := by
      have hsqrtSq := Real.sq_sqrt hsnonneg
      nlinarith [Real.sqrt_nonneg s.re]
    have hreSelf : s.re ≤ s.re * Real.sqrt s.re := by
      nlinarith
    have hreNorm : s.re ≤ ‖s‖ :=
      (le_abs_self s.re).trans (Complex.abs_re_le_norm s)
    have hsqrtNorm : Real.sqrt s.re ≤ Real.sqrt ‖s‖ := Real.sqrt_le_sqrt hreNorm
    have hprodNorm : s.re * Real.sqrt s.re ≤ ‖s‖ * Real.sqrt ‖s‖ :=
      mul_le_mul hreNorm hsqrtNorm (Real.sqrt_nonneg _) (norm_nonneg _)
    have hexponent :
        2 * s.re + 8 * s.re * Real.sqrt s.re + chiFourLNormBound ≤
          B * (1 + ‖s‖ * Real.sqrt ‖s‖) := by
      have hstrip : 0 ≤
          16 * Submission.Growth.chiFourCompletedStripBound (1 / 2) 3 := by
        exact mul_nonneg (by norm_num)
          (Submission.Growth.chiFourCompletedStripBound_nonneg (1 / 2) 3)
      dsimp [B, chiFourXiRightGrowthConstant]
      nlinarith [mul_nonneg chiFourLNormBound_nonneg hnorm,
        mul_nonneg hstrip hnorm, hreSelf, hprodNorm]
    calc
      ‖chiFourXi s‖ ≤ Real.exp (2 * s.re) *
          Real.exp (8 * s.re * Real.sqrt s.re) * Real.exp chiFourLNormBound := hxi
      _ = Real.exp
          (2 * s.re + 8 * s.re * Real.sqrt s.re + chiFourLNormBound) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (B * (1 + ‖s‖ * Real.sqrt ‖s‖)) :=
        Real.exp_le_exp.mpr hexponent

private lemma one_add_mul_sqrt_one_add_le (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) * Real.sqrt (1 + r) ≤ 3 * (1 + r * Real.sqrt r) := by
  let x := Real.sqrt r
  have hx : 0 ≤ x := Real.sqrt_nonneg r
  have hxSq : x ^ 2 = r := by simpa [x] using Real.sq_sqrt hr
  have hsqrtShift : Real.sqrt (1 + r) ≤ 1 + x := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 + x)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hmul : (1 + r) * Real.sqrt (1 + r) ≤ (1 + r) * (1 + x) :=
    mul_le_mul_of_nonneg_left hsqrtShift (by linarith)
  apply hmul.trans
  by_cases hxOne : x ≤ 1
  · have hrOne : r ≤ 1 := by nlinarith
    nlinarith [mul_nonneg hr hx]
  · have hxOne' : 1 ≤ x := le_of_not_ge hxOne
    have hxCube : x ≤ r * x := by nlinarith
    have hrCube : r ≤ r * x := by nlinarith
    nlinarith [mul_nonneg hr hx]

noncomputable def chiFourXiGrowthConstant : ℝ :=
  4 * chiFourXiRightGrowthConstant

private lemma chiFourXiGrowthConstant_nonneg : 0 ≤ chiFourXiGrowthConstant :=
  mul_nonneg (by norm_num) chiFourXiRightGrowthConstant_nonneg

lemma norm_chiFourXi_growth (s : ℂ) :
    ‖chiFourXi s‖ ≤ Real.exp
      (chiFourXiGrowthConstant * (1 + ‖s‖ * Real.sqrt ‖s‖)) := by
  let B := chiFourXiRightGrowthConstant
  have hB : 0 ≤ B := chiFourXiRightGrowthConstant_nonneg
  have hsprod : 0 ≤ ‖s‖ * Real.sqrt ‖s‖ := by positivity
  by_cases hsRight : (1 / 2 : ℝ) ≤ s.re
  · have hright := norm_chiFourXi_right_growth hsRight
    apply hright.trans
    apply Real.exp_le_exp.mpr
    dsimp [chiFourXiGrowthConstant, B]
    nlinarith [mul_nonneg chiFourXiRightGrowthConstant_nonneg hsprod]
  · let w : ℂ := 1 - s
    have hwRight : (1 / 2 : ℝ) ≤ w.re := by
      dsimp [w]
      simp
      linarith
    have hright := norm_chiFourXi_right_growth hwRight
    have hwnorm : ‖w‖ ≤ 1 + ‖s‖ := by
      dsimp [w]
      simpa using norm_sub_le (1 : ℂ) s
    have hwsqrt : Real.sqrt ‖w‖ ≤ Real.sqrt (1 + ‖s‖) :=
      Real.sqrt_le_sqrt hwnorm
    have hwprod : ‖w‖ * Real.sqrt ‖w‖ ≤
        (1 + ‖s‖) * Real.sqrt (1 + ‖s‖) :=
      mul_le_mul hwnorm hwsqrt (Real.sqrt_nonneg _) (by positivity)
    have hshift := one_add_mul_sqrt_one_add_le ‖s‖ (norm_nonneg s)
    have hinside : 1 + ‖w‖ * Real.sqrt ‖w‖ ≤
        4 * (1 + ‖s‖ * Real.sqrt ‖s‖) := by
      nlinarith [hwprod.trans hshift]
    rw [← chiFourXi_one_sub s]
    apply hright.trans
    apply Real.exp_le_exp.mpr
    dsimp [chiFourXiGrowthConstant, B]
    nlinarith [mul_nonneg hB
      (show 0 ≤ 4 * (1 + ‖s‖ * Real.sqrt ‖s‖) -
        (1 + ‖w‖ * Real.sqrt ‖w‖) by linarith)]

theorem exists_chiFourXi_zero : ∃ s : ℂ, chiFourXi s = 0 := by
  by_contra hzero
  push Not at hzero
  obtain ⟨a, b, hab⟩ := Submission.ZeroGrowth.eq_exp_affine_of_sqrt_growth
    differentiable_chiFourXi hzero chiFourXiGrowthConstant_nonneg norm_chiFourXi_growth
  have hsymZero := chiFourXi_one_sub (0 : ℂ)
  rw [hab, hab] at hsymZero
  have hnormZero := congrArg norm hsymZero
  simp only [Complex.norm_exp] at hnormZero
  have haRe : a.re = 0 := by
    have hre := Real.exp_injective hnormZero
    norm_num [Complex.mul_re] at hre
    linarith
  have hsymI := chiFourXi_one_sub Complex.I
  rw [hab, hab] at hsymI
  have hnormI := congrArg norm hsymI
  simp only [Complex.norm_exp] at hnormI
  have haIm : a.im = 0 := by
    have hre := Real.exp_injective hnormI
    norm_num [Complex.mul_re] at hre
    rw [haRe] at hre
    linarith
  have ha : a = 0 := Complex.ext haRe haIm
  have hconst (s : ℂ) : chiFourXi s = Complex.exp b := by
    rw [hab, ha]
    simp
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (4 * ‖Complex.exp b‖))
  have hnOne : 1 ≤ n := by
    have : (1 : ℝ) < n := (le_max_left 1 (4 * ‖Complex.exp b‖)).trans_lt hn
    exact_mod_cast this.le
  have hnNorm : 4 * ‖Complex.exp b‖ < (n : ℝ) :=
    (le_max_right 1 (4 * ‖Complex.exp b‖)).trans_lt hn
  have hnFac : (n : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast n.self_le_factorial
  have hlower := norm_chiFourXi_odd_nat_lower n hnOne
  rw [hconst] at hlower
  have hstrict : ‖Complex.exp b‖ < (n.factorial : ℝ) / 4 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    simpa [mul_comm] using hnNorm.trans_le hnFac
  linarith

private theorem exists_entire_factor_at
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnotzero : ∃ z, f z ≠ 0)
    {a : ℂ} (ha : f a = 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ g : ℂ → ℂ,
      Differentiable ℂ g ∧ g a ≠ 0 ∧ ∀ z, f z = (z - a) ^ m * g z := by
  let q : ℂ → ℂ := fun z => f (a + z)
  have hq : Differentiable ℂ q := by
    dsimp [q]
    fun_prop
  have hq0 : q 0 = 0 := by simpa [q] using ha
  have hqnotzero : ∃ z, q z ≠ 0 := by
    obtain ⟨z, hz⟩ := hnotzero
    refine ⟨z - a, ?_⟩
    simpa [q] using hz
  have horderTop : analyticOrderAt q 0 ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hqzero : q = 0 :=
      ((Complex.analyticOnNhd_univ_iff_differentiable).2 hq).eq_of_eventuallyEq
        analyticOnNhd_const htop
    obtain ⟨z, hz⟩ := hqnotzero
    exact hz (by rw [hqzero]; rfl)
  let m := analyticOrderNatAt q 0
  have hmCast : (m : ℕ∞) = analyticOrderAt q 0 :=
    Nat.cast_analyticOrderNatAt horderTop
  have hmpos : 0 < m := by
    have horderNe : analyticOrderAt q 0 ≠ 0 :=
      (hq.analyticAt 0).analyticOrderAt_ne_zero.mpr hq0
    apply Nat.pos_of_ne_zero
    intro hm
    apply horderNe
    rw [← hmCast, hm]
    simp
  obtain ⟨F, hF0, hformula⟩ := (hq.analyticAt 0).exists_eq_sum_add_pow_mul m
  have hderiv : ∀ i < m, iteratedDeriv i q 0 = 0 := by
    rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hq.analyticAt 0)]
    rw [← hmCast]
  have hfactor (z : ℂ) : q z = z ^ m * F z := by
    rw [hformula]
    have hsum :
        ∑ i ∈ Finset.range m, (z ^ i / i.factorial) • iteratedDeriv i q 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hderiv i (Finset.mem_range.mp hi)]
      simp
    rw [hsum, zero_add]
    rfl
  have hF : Differentiable ℂ F := by
    intro z
    by_cases hz : z = 0
    · subst z
      exact hF0.differentiableAt
    · have hevent : F =ᶠ[nhds z] fun y => q y / y ^ m := by
        filter_upwards [eventually_ne_nhds hz] with y hy
        rw [hfactor y]
        exact (mul_div_cancel_left₀ (F y) (pow_ne_zero m hy)).symm
      apply hevent.differentiableAt_iff.mpr
      exact (hq z).div (differentiableAt_id.pow m) (pow_ne_zero m hz)
  have hFne : F 0 ≠ 0 := by
    intro hFzero
    have hForderNe : analyticOrderAt F 0 ≠ 0 :=
      hF0.analyticOrderAt_ne_zero.mpr hFzero
    have hfun : q = (fun z => z ^ m) * F := by
      funext z
      exact hfactor z
    have horderMul := analyticOrderAt_mul
      (z₀ := (0 : ℂ)) (f := fun z : ℂ => z ^ m) (g := F)
      (by fun_prop) hF0
    have hidPow : analyticOrderAt (fun z : ℂ => z ^ m) 0 = m := by
      have hpowequal : (fun z : ℂ => z ^ m) = (id : ℂ → ℂ) ^ m := rfl
      rw [hpowequal]
      rw [analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
      simp
    rw [← hfun, hidPow, ← hmCast] at horderMul
    have heq : (0 : ℕ∞) + m = analyticOrderAt F 0 + m := by
      simpa [add_comm] using horderMul
    have hzero := ENat.add_left_injective_of_ne_top (ENat.coe_ne_top m) heq
    exact hForderNe hzero.symm
  let g : ℂ → ℂ := fun z => F (z - a)
  refine ⟨m, hmpos, g, ?_, ?_, ?_⟩
  · dsimp [g]
    fun_prop
  · simpa [g] using hFne
  · intro z
    have hz := hfactor (z - a)
    dsimp [q] at hz
    simpa [g] using hz

private def zeroFactorProduct (zeros : List (ℂ × ℕ)) (z : ℂ) : ℂ :=
  (zeros.map fun am => (z - am.1) ^ am.2).prod

private theorem factor_zeros_subset_finset
    (Z : Finset ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnotzero : ∃ z, f z ≠ 0) (hzeros : ∀ z, f z = 0 → z ∈ Z) :
    ∃ zeros : List (ℂ × ℕ), ∃ g : ℂ → ℂ,
      Differentiable ℂ g ∧ (∀ z, g z ≠ 0) ∧
        ∀ z, f z = zeroFactorProduct zeros z * g z := by
  classical
  induction Z using Finset.induction_on generalizing f with
  | empty =>
      refine ⟨[], f, hf, ?_, ?_⟩
      · intro z hz
        have : z ∈ (∅ : Finset ℂ) := hzeros z hz
        simp at this
      · intro z
        simp [zeroFactorProduct]
  | @insert a Z ha ih =>
      by_cases hfa : f a = 0
      · obtain ⟨m, hm, g, hg, hga, hfactor⟩ :=
          exists_entire_factor_at hf hnotzero hfa
        have hgnotzero : ∃ z, g z ≠ 0 := ⟨a, hga⟩
        have hgzeros : ∀ z, g z = 0 → z ∈ Z := by
          intro z hgz
          have hfz : f z = 0 := by rw [hfactor z, hgz, mul_zero]
          have hz := hzeros z hfz
          rw [Finset.mem_insert] at hz
          rcases hz with rfl | hz
          · exact (hga hgz).elim
          · exact hz
        obtain ⟨zeros, h, hh, hhnz, hhfactor⟩ := ih hg hgnotzero hgzeros
        refine ⟨(a, m) :: zeros, h, hh, hhnz, ?_⟩
        intro z
        rw [hfactor z, hhfactor z]
        simp only [zeroFactorProduct, List.map_cons, List.prod_cons]
        ring
      · have hzeros' : ∀ z, f z = 0 → z ∈ Z := by
          intro z hz
          have hzmem := hzeros z hz
          rw [Finset.mem_insert] at hzmem
          exact hzmem.resolve_left fun hza => hfa (hza ▸ hz)
        exact ih hf hnotzero hzeros'

private noncomputable def zeroFactorRadius (zeros : List (ℂ × ℕ)) : ℝ :=
  1 + (zeros.map fun am => ‖am.1‖).sum

private lemma zeroFactorRadius_pos (zeros : List (ℂ × ℕ)) :
    0 < zeroFactorRadius zeros := by
  unfold zeroFactorRadius
  have : 0 ≤ (zeros.map fun am => ‖am.1‖).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨am, _ham, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  linarith

private lemma one_le_norm_zeroFactorProduct (zeros : List (ℂ × ℕ)) {z : ℂ}
    (hz : zeroFactorRadius zeros ≤ ‖z‖) :
    1 ≤ ‖zeroFactorProduct zeros z‖ := by
  induction zeros with
  | nil => simp [zeroFactorProduct]
  | cons am zeros ih =>
      have hsum : 0 ≤ (zeros.map fun bm => ‖bm.1‖).sum := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨bm, _hbm, rfl⟩ := List.mem_map.mp hx
        exact norm_nonneg _
      have hhead : 1 ≤ ‖z - am.1‖ := by
        have hdiff := norm_sub_norm_le z am.1
        unfold zeroFactorRadius at hz
        simp only [List.map_cons, List.sum_cons] at hz
        linarith
      have htailRadius : zeroFactorRadius zeros ≤ ‖z‖ := by
        unfold zeroFactorRadius at hz ⊢
        simp only [List.map_cons, List.sum_cons] at hz
        nlinarith [norm_nonneg am.1]
      have hheadPow : 1 ≤ ‖z - am.1‖ ^ am.2 := one_le_pow₀ hhead
      have htail := ih htailRadius
      have htail' : 1 ≤ ‖(zeros.map fun bm => (z - bm.1) ^ bm.2).prod‖ := by
        simpa [zeroFactorProduct] using htail
      rw [zeroFactorProduct, List.map_cons, List.prod_cons, norm_mul, norm_pow]
      simpa using mul_le_mul hheadPow htail' zero_le_one (zero_le_one.trans hheadPow)

private theorem factor_growth_bound
    {f g : ℂ → ℂ} {zeros : List (ℂ × ℕ)}
    (hg : Differentiable ℂ g)
    (hfactor : ∀ z, f z = zeroFactorProduct zeros z * g z)
    {A : ℝ} (hA : 0 ≤ A)
    (hfGrowth : ∀ z, ‖f z‖ ≤ Real.exp (A * (1 + ‖z‖ * Real.sqrt ‖z‖))) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ z, ‖g z‖ ≤ Real.exp (B * (1 + ‖z‖ * Real.sqrt ‖z‖)) := by
  let R := zeroFactorRadius zeros
  have hR : 0 < R := zeroFactorRadius_pos zeros
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have hnonempty : (Metric.closedBall (0 : ℂ) R).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hR.le⟩
  have hcontinuous : ContinuousOn (fun z => ‖g z‖) (Metric.closedBall (0 : ℂ) R) :=
    hg.continuous.norm.continuousOn
  obtain ⟨zmax, hzmax, hmax⟩ := hcompact.exists_isMaxOn hnonempty hcontinuous
  let C := ‖g zmax‖
  have hC : 0 ≤ C := norm_nonneg _
  let B := A + C
  have hB : 0 ≤ B := add_nonneg hA hC
  refine ⟨B, hB, ?_⟩
  intro z
  have hprod : 0 ≤ ‖z‖ * Real.sqrt ‖z‖ := by positivity
  by_cases hz : ‖z‖ ≤ R
  · have hzball : z ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall]
      simpa [dist_comm] using hz
    have hgC : ‖g z‖ ≤ C := hmax hzball
    have hCexp : C ≤ Real.exp C :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp C)
    apply hgC.trans (hCexp.trans ?_)
    apply Real.exp_le_exp.mpr
    dsimp [B]
    nlinarith [mul_nonneg hA hprod, mul_nonneg hC hprod]
  · have hzR : R ≤ ‖z‖ := le_of_not_ge hz
    have hP := one_le_norm_zeroFactorProduct zeros hzR
    have hgf : ‖g z‖ ≤ ‖f z‖ := by
      rw [hfactor z, norm_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) hP
    apply hgf.trans ((hfGrowth z).trans ?_)
    apply Real.exp_le_exp.mpr
    dsimp [B]
    nlinarith [mul_nonneg hC (show 0 ≤ 1 + ‖z‖ * Real.sqrt ‖z‖ by positivity)]

private noncomputable def zeroFactorExponent : List (ℂ × ℕ) → ℂ → ℝ
  | [], _ => 0
  | am :: zeros, z =>
      (am.2 : ℝ) * (‖z‖ + ‖am.1‖) + zeroFactorExponent zeros z

private lemma norm_zeroFactorProduct_le_exp (zeros : List (ℂ × ℕ)) (z : ℂ) :
    ‖zeroFactorProduct zeros z‖ ≤ Real.exp (zeroFactorExponent zeros z) := by
  induction zeros with
  | nil => simp [zeroFactorProduct, zeroFactorExponent]
  | cons am zeros ih =>
      let x : ℝ := ‖z‖ + ‖am.1‖
      have hx : 0 ≤ x := by dsimp [x]; positivity
      have hsub : ‖z - am.1‖ ≤ x := by
        dsimp [x]
        exact norm_sub_le z am.1
      have hxexp : x ≤ Real.exp x :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp x)
      have hbase : ‖z - am.1‖ ≤ Real.exp x := hsub.trans hxexp
      have hpow : ‖z - am.1‖ ^ am.2 ≤ (Real.exp x) ^ am.2 := by
        gcongr
      simp only [zeroFactorProduct, List.map_cons, List.prod_cons, norm_mul, norm_pow,
        zeroFactorExponent]
      rw [Real.exp_add, Real.exp_nat_mul]
      exact mul_le_mul hpow ih (norm_nonneg _) (by positivity)

private noncomputable def zeroFactorLinearRate : List (ℂ × ℕ) → ℝ
  | [] => 0
  | am :: zeros => 2 * (am.2 : ℝ) + zeroFactorLinearRate zeros

private noncomputable def zeroFactorLinearOffset : List (ℂ × ℕ) → ℝ
  | [] => 0
  | am :: zeros =>
      (am.2 : ℝ) * (1 + ‖am.1‖) + zeroFactorLinearOffset zeros

private lemma zeroFactorExponent_odd_nat (zeros : List (ℂ × ℕ)) (n : ℕ) :
    zeroFactorExponent zeros ((2 * n + 1 : ℕ) : ℂ) =
      zeroFactorLinearRate zeros * n + zeroFactorLinearOffset zeros := by
  induction zeros with
  | nil => simp [zeroFactorExponent, zeroFactorLinearRate, zeroFactorLinearOffset]
  | cons am zeros ih =>
      rw [zeroFactorExponent, zeroFactorLinearRate, zeroFactorLinearOffset, ih]
      rw [Complex.norm_natCast]
      push_cast
      ring

private lemma norm_exp_affine_odd_nat_le (a b : ℂ) (n : ℕ) :
    ‖Complex.exp (a * ((2 * n + 1 : ℕ) : ℂ) + b)‖ ≤
      Real.exp (2 * ‖a‖ * n + (‖a‖ + ‖b‖)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (a * ((2 * n + 1 : ℕ) : ℂ) + b).re ≤
      ‖a * ((2 * n + 1 : ℕ) : ℂ) + b‖ := Complex.re_le_norm _
  have hnorm : ‖a * ((2 * n + 1 : ℕ) : ℂ) + b‖ ≤
      ‖a‖ * (2 * n + 1 : ℝ) + ‖b‖ := by
    calc
      ‖a * ((2 * n + 1 : ℕ) : ℂ) + b‖ ≤
          ‖a * ((2 * n + 1 : ℕ) : ℂ)‖ + ‖b‖ := norm_add_le _ _
      _ = ‖a‖ * (2 * n + 1 : ℝ) + ‖b‖ := by
        rw [norm_mul, Complex.norm_natCast]
        push_cast
        rfl
  calc
    (a * ((2 * n + 1 : ℕ) : ℂ) + b).re ≤
        ‖a‖ * (2 * n + 1 : ℝ) + ‖b‖ := hre.trans hnorm
    _ = 2 * ‖a‖ * n + (‖a‖ + ‖b‖) := by
      ring

private lemma chiFourXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    chiFourXi s ≠ 0 := by
  have hpow : (4 : ℂ) ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hgamma : DirichletCharacter.gammaFactor Submission.Helpers.chiFour s ≠ 0 := by
    rw [Submission.Helpers.chiFour_odd.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hL := Submission.Helpers.chiFour_LFunction_ne_zero_of_one_le_re hs
  have hrelation := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    Submission.Helpers.chiFour s (Or.inr (by norm_num : (4 : ℕ) ≠ 1))
  have hcompleted :
      DirichletCharacter.completedLFunction Submission.Helpers.chiFour s =
        DirichletCharacter.gammaFactor Submission.Helpers.chiFour s *
          DirichletCharacter.LFunction Submission.Helpers.chiFour s := by
    rw [eq_div_iff hgamma] at hrelation
    rw [← hrelation]
    ring
  rw [chiFourXi, hcompleted]
  exact mul_ne_zero hpow (mul_ne_zero hgamma hL)

private lemma chiFourXi_zero_implies_LFunction_zero {s : ℂ} (hs : chiFourXi s = 0) :
    DirichletCharacter.LFunction Submission.Helpers.chiFour s = 0 := by
  have hpow : (4 : ℂ) ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hcompleted :
      DirichletCharacter.completedLFunction Submission.Helpers.chiFour s = 0 := by
    rw [chiFourXi, mul_eq_zero] at hs
    exact hs.resolve_left hpow
  rw [Submission.Analytic.chiFour_LFunction_eq_completed_mul_invGammaFactor]
  change DirichletCharacter.completedLFunction Submission.Helpers.chiFour s *
      (DirichletCharacter.gammaFactor Submission.Helpers.chiFour s)⁻¹ = 0
  rw [hcompleted, zero_mul]

private lemma chiFourXi_not_identically_zero : ∃ s : ℂ, chiFourXi s ≠ 0 := by
  refine ⟨(3 : ℂ), ?_⟩
  intro hzero
  have hlower := norm_chiFourXi_odd_nat_lower 1 (by norm_num)
  norm_num at hlower
  rw [hzero, norm_zero] at hlower
  linarith

theorem exists_chiFourXi_nonreal_zero :
    ∃ s : ℂ, chiFourXi s = 0 ∧ s.im ≠ 0 := by
  by_contra hnonreal
  push Not at hnonreal
  let K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Set.Icc (0 : ℝ) 1
  have hKcompact : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hzeroK : ∀ s : ℂ, chiFourXi s = 0 → s ∈ K := by
    intro s hs
    have hsim : s.im = 0 := hnonreal s hs
    have hslt : s.re < 1 := by
      by_contra hsge
      exact chiFourXi_ne_zero_of_one_le_re (le_of_not_gt hsge) hs
    have hspos : 0 < s.re := by
      by_contra hsnonpos
      have hw : 1 ≤ (1 - s).re := by simp; linarith
      have hwne := chiFourXi_ne_zero_of_one_le_re hw
      apply hwne
      rw [chiFourXi_one_sub, hs]
    refine ⟨s.re, ⟨hspos.le, hslt.le⟩, ?_⟩
    apply Complex.ext
    · simp
    · simpa using hsim.symm
  have hfinite : {s : ℂ | chiFourXi s = 0}.Finite := by
    apply (Submission.Analytic.chiFourZeroSet_inter_compact_finite hKcompact).subset
    intro s hs
    exact ⟨hzeroK s hs, chiFourXi_zero_implies_LFunction_zero hs⟩
  let Z : Finset ℂ := hfinite.toFinset
  have hzeros : ∀ s : ℂ, chiFourXi s = 0 → s ∈ Z := by
    intro s hs
    simpa [Z] using hfinite.mem_toFinset.mpr hs
  obtain ⟨zeros, g, hg, hgnz, hfactor⟩ := factor_zeros_subset_finset Z
    differentiable_chiFourXi chiFourXi_not_identically_zero hzeros
  obtain ⟨B, hB, hgrowth⟩ := factor_growth_bound hg hfactor
    chiFourXiGrowthConstant_nonneg norm_chiFourXi_growth
  obtain ⟨a, b, hab⟩ := Submission.ZeroGrowth.eq_exp_affine_of_sqrt_growth
    hg hgnz hB hgrowth
  let rate := zeroFactorLinearRate zeros + 2 * ‖a‖
  let offset := zeroFactorLinearOffset zeros + (‖a‖ + ‖b‖)
  have hupper (n : ℕ) :
      ‖chiFourXi ((2 * n + 1 : ℕ) : ℂ)‖ ≤ Real.exp (rate * n + offset) := by
    let s : ℂ := ((2 * n + 1 : ℕ) : ℂ)
    have hp := norm_zeroFactorProduct_le_exp zeros s
    have haff := norm_exp_affine_odd_nat_le a b n
    rw [hfactor s, hab, norm_mul]
    calc
      ‖zeroFactorProduct zeros s‖ * ‖Complex.exp (a * s + b)‖ ≤
          Real.exp (zeroFactorExponent zeros s) *
            Real.exp (2 * ‖a‖ * n + (‖a‖ + ‖b‖)) :=
        mul_le_mul hp haff (norm_nonneg _) (by positivity)
      _ = Real.exp (rate * n + offset) := by
        rw [← Real.exp_add]
        dsimp [s, rate, offset]
        rw [zeroFactorExponent_odd_nat]
        congr 1
        ring
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
  have hexpOffset : Real.exp offset ≤ (A : ℝ) := hA.le
  have hexpRate : Real.exp rate ≤ (C : ℝ) := hC.le
  have hexpUpper : Real.exp (rate * n + offset) ≤ (A : ℝ) * C ^ n := by
    rw [Real.exp_add, mul_comm rate (n : ℝ), Real.exp_nat_mul]
    rw [mul_comm (Real.exp rate ^ n) (Real.exp offset)]
    exact mul_le_mul hexpOffset (pow_le_pow_left₀ (Real.exp_nonneg _) hexpRate n)
      (by positivity) (by positivity)
  have hlower := norm_chiFourXi_odd_nat_lower n hnOne
  have hu := hupper n
  have hACstrict : (A : ℝ) * C ^ n < (n.factorial : ℝ) / 4 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfac
  have hstrict : ‖chiFourXi ((2 * n + 1 : ℕ) : ℂ)‖ <
      (n.factorial : ℝ) / 4 :=
    hu.trans_lt (hexpUpper.trans_lt hACstrict)
  exact (not_lt_of_ge hlower) hstrict

theorem chiFourXi_zeroSet_infinite :
    {s : ℂ | chiFourXi s = 0}.Infinite := by
  intro hfinite
  let Z : Finset ℂ := hfinite.toFinset
  have hzeros : ∀ s : ℂ, chiFourXi s = 0 → s ∈ Z := by
    intro s hs
    simpa [Z] using hfinite.mem_toFinset.mpr hs
  obtain ⟨zeros, g, hg, hgnz, hfactor⟩ := factor_zeros_subset_finset Z
    differentiable_chiFourXi chiFourXi_not_identically_zero hzeros
  obtain ⟨B, hB, hgrowth⟩ := factor_growth_bound hg hfactor
    chiFourXiGrowthConstant_nonneg norm_chiFourXi_growth
  obtain ⟨a, b, hab⟩ := Submission.ZeroGrowth.eq_exp_affine_of_sqrt_growth
    hg hgnz hB hgrowth
  let rate := zeroFactorLinearRate zeros + 2 * ‖a‖
  let offset := zeroFactorLinearOffset zeros + (‖a‖ + ‖b‖)
  have hupper (n : ℕ) :
      ‖chiFourXi ((2 * n + 1 : ℕ) : ℂ)‖ ≤ Real.exp (rate * n + offset) := by
    let s : ℂ := ((2 * n + 1 : ℕ) : ℂ)
    have hp := norm_zeroFactorProduct_le_exp zeros s
    have haff := norm_exp_affine_odd_nat_le a b n
    rw [hfactor s, hab, norm_mul]
    calc
      ‖zeroFactorProduct zeros s‖ * ‖Complex.exp (a * s + b)‖ ≤
          Real.exp (zeroFactorExponent zeros s) *
            Real.exp (2 * ‖a‖ * n + (‖a‖ + ‖b‖)) :=
        mul_le_mul hp haff (norm_nonneg _) (by positivity)
      _ = Real.exp (rate * n + offset) := by
        rw [← Real.exp_add]
        dsimp [s, rate, offset]
        rw [zeroFactorExponent_odd_nat]
        congr 1
        ring
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
  have hexpOffset : Real.exp offset ≤ (A : ℝ) := hA.le
  have hexpRate : Real.exp rate ≤ (C : ℝ) := hC.le
  have hexpUpper : Real.exp (rate * n + offset) ≤ (A : ℝ) * C ^ n := by
    rw [Real.exp_add, mul_comm rate (n : ℝ), Real.exp_nat_mul]
    rw [mul_comm (Real.exp rate ^ n) (Real.exp offset)]
    exact mul_le_mul hexpOffset (pow_le_pow_left₀ (Real.exp_nonneg _) hexpRate n)
      (by positivity) (by positivity)
  have hlower := norm_chiFourXi_odd_nat_lower n hnOne
  have hu := hupper n
  have hACstrict : (A : ℝ) * C ^ n < (n.factorial : ℝ) / 4 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfac
  have hstrict : ‖chiFourXi ((2 * n + 1 : ℕ) : ℂ)‖ <
      (n.factorial : ℝ) / 4 :=
    hu.trans_lt (hexpUpper.trans_lt hACstrict)
  exact (not_lt_of_ge hlower) hstrict

lemma chiFourXi_zero_mem_nontrivial {s : ℂ} (hs : chiFourXi s = 0) :
    s ∈ Submission.Analytic.chiFourNontrivialZeroSet := by
  have hslt : s.re < 1 := by
    by_contra hsge
    exact chiFourXi_ne_zero_of_one_le_re (le_of_not_gt hsge) hs
  have hspos : 0 < s.re := by
    by_contra hsnonpos
    have hw : 1 ≤ (1 - s).re := by simp; linarith
    have hwne := chiFourXi_ne_zero_of_one_le_re hw
    apply hwne
    rw [chiFourXi_one_sub, hs]
  exact ⟨hspos, hslt, chiFourXi_zero_implies_LFunction_zero hs⟩

theorem chiFourXi_nonrealZeroSet_infinite :
    {s : ℂ | chiFourXi s = 0 ∧ s.im ≠ 0}.Infinite := by
  have hreal : {s : ℂ | chiFourXi s = 0 ∧ s.im = 0}.Finite := by
    apply (Submission.Analytic.chiFourNontrivialZeroRectangle_finite 0).subset
    rintro s ⟨hs, hsim⟩
    refine ⟨chiFourXi_zero_mem_nontrivial hs, ?_⟩
    simp [hsim]
  by_contra hnonreal
  rw [Set.not_infinite] at hnonreal
  have hall : {s : ℂ | chiFourXi s = 0}.Finite :=
    (hreal.union hnonreal).subset fun s hs => by
      by_cases hsim : s.im = 0
      · exact Or.inl ⟨hs, hsim⟩
      · exact Or.inr ⟨hs, hsim⟩
  exact chiFourXi_zeroSet_infinite hall

theorem exists_chiFourXi_nonreal_zero_above (T : ℝ) :
    ∃ s : ℂ, chiFourXi s = 0 ∧ s.im ≠ 0 ∧ T < |s.im| := by
  let Z := Submission.Analytic.chiFourNontrivialZerosInRectangle |T|
  obtain ⟨s, hs, hsnot⟩ := chiFourXi_nonrealZeroSet_infinite.exists_notMem_finset Z
  refine ⟨s, hs.1, hs.2, ?_⟩
  have hsnontrivial := chiFourXi_zero_mem_nontrivial hs.1
  have habs : |T| < |s.im| := by
    by_contra hle
    apply hsnot
    rw [Submission.Analytic.mem_chiFourNontrivialZerosInRectangle]
    exact ⟨hsnontrivial, le_of_not_gt hle⟩
  exact (le_abs_self T).trans_lt habs

theorem exists_chiFour_nontrivial_zero_right_above (T : ℝ) :
    ∃ rho : ℂ, rho ∈ Submission.Analytic.chiFourNontrivialZeroSet ∧
      (1 / 2 : ℝ) ≤ rho.re ∧ T < |rho.im| := by
  obtain ⟨s, hs, hsim, hsheight⟩ := exists_chiFourXi_nonreal_zero_above T
  have hsnontrivial := chiFourXi_zero_mem_nontrivial hs
  by_cases hre : (1 / 2 : ℝ) ≤ s.re
  · exact ⟨s, hsnontrivial, hre, hsheight⟩
  · refine ⟨1 - s, ?_, ?_, ?_⟩
    · exact Submission.Analytic.chiFourNontrivialZeroSet_one_sub hsnontrivial
    · simp
      linarith
    · simpa using hsheight

end Submission.ZeroExistence
