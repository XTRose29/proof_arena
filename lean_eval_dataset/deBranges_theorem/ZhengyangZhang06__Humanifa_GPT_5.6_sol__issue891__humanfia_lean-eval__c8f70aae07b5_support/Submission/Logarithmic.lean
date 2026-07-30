import Mathlib
import Submission.Helpers

open Metric

namespace Submission

lemma exists_normalized_log_dslope {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (h : NormalizedUnivalentOn f R) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball 0 R) ∧ L 0 = 0 ∧
      ∀ z ∈ ball 0 R, Complex.exp (L z) = dslope f 0 z := by
  rcases h with ⟨hf, hinj, h0, h1⟩
  let q : ℂ → ℂ := dslope f 0
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hq : DifferentiableOn ℂ q (ball 0 R) := by
    exact (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hzero)).2 hf
  have hq_ne : ∀ z ∈ ball (0 : ℂ) R, q z ≠ 0 := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · simp [q, dslope_same, h1]
    · have hfz : f z ≠ f 0 := fun heq => hz0 (hinj hz hzero heq)
      change dslope f 0 z ≠ 0
      rw [dslope_of_ne f hz0]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hz0)) (sub_ne_zero.mpr hfz)
  have hlogDeriv : DifferentiableOn ℂ (logDeriv q) (ball 0 R) := by
    exact (hq.deriv isOpen_ball).div hq hq_ne
  rcases hlogDeriv.isExactOn_ball.with_val_at 0 0 with ⟨L, hL0, hL⟩
  have hLdiff : DifferentiableOn ℂ L (ball 0 R) := fun z hz =>
    (hL z hz).differentiableAt.differentiableWithinAt
  refine ⟨L, hLdiff, hL0, ?_⟩
  let u : ℂ → ℂ := (fun z => Complex.exp (-L z)) * q
  have hudiff : DifferentiableOn ℂ u (ball 0 R) := by
    intro z hz
    change DifferentiableWithinAt ℂ ((fun z => Complex.exp (-L z)) * q) (ball 0 R) z
    exact ((hL z hz).differentiableAt.neg.cexp.mul
      (hq.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt
  have hu_deriv : ∀ z ∈ ball (0 : ℂ) R, deriv u z = 0 := by
    intro z hz
    have hqz : q z ≠ 0 := hq_ne z hz
    have hq_at : HasDerivAt q (deriv q z) z :=
      (hq.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hu := (hL z hz).neg.cexp.mul hq_at
    have hderiv :
        Complex.exp ((-L) z) * -logDeriv q z * q z +
            Complex.exp ((-L) z) * deriv q z = 0 := by
      rw [logDeriv_apply]
      field_simp [hqz]
      ring
    rw [hderiv] at hu
    change deriv ((fun z => Complex.exp (-L z)) * q) z = 0
    exact hu.deriv
  have hu_const (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : u z = u 0 :=
    isOpen_ball.is_const_of_deriv_eq_zero isPreconnected_ball hudiff
      (fun w hw => hu_deriv w hw) hz hzero
  intro z hz
  have huz : u z = 1 := by
    rw [hu_const z hz]
    simp [u, hL0, q, dslope_same, h1]
  calc
    Complex.exp (L z) = Complex.exp (L z) * 1 := by simp
    _ = Complex.exp (L z) * u z := by rw [huz]
    _ = q z := by
      change Complex.exp (L z) * (Complex.exp (-L z) * q z) = q z
      rw [← mul_assoc, ← Complex.exp_add]
      simp
    _ = dslope f 0 z := rfl

lemma eqOn_mul_exp_of_normalized_log {f L : ℂ → ℂ} {R : ℝ} (h0 : f 0 = 0)
    (hL : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z) :
    Set.EqOn f (fun z => z * Complex.exp (L z)) (ball 0 R) := by
  intro z hz
  calc
    f z = z * dslope f 0 z := by
      simpa only [sub_zero, h0, sub_zero, smul_eq_mul] using (sub_smul_dslope f 0 z).symm
    _ = z * Complex.exp (L z) := by rw [hL z hz]

lemma eqOn_normalized_logs {L M : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hM : DifferentiableOn ℂ M (ball 0 R))
    (hL0 : L 0 = 0) (hM0 : M 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = Complex.exp (M z)) :
    Set.EqOn L M (ball 0 R) := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hderiv : Set.EqOn (deriv L) (deriv M) (ball 0 R) := by
    intro z hz
    have hdiffL : DifferentiableAt ℂ L z := hL.differentiableAt (isOpen_ball.mem_nhds hz)
    have hdiffM : DifferentiableAt ℂ M z := hM.differentiableAt (isOpen_ball.mem_nhds hz)
    have heq := (show Set.EqOn (fun w => Complex.exp (L w))
      (fun w => Complex.exp (M w)) (ball 0 R) from hexp).deriv isOpen_ball hz
    rw [hdiffL.hasDerivAt.cexp.deriv, hdiffM.hasDerivAt.cexp.deriv, hexp z hz] at heq
    exact mul_left_cancel₀ (Complex.exp_ne_zero (M z)) heq
  exact isOpen_ball.eqOn_of_deriv_eq isPreconnected_ball hL hM hderiv hzero
    (hL0.trans hM0.symm)

noncomputable def logarithmicCoeff (L : ℂ → ℂ) (n : ℕ) : ℂ :=
  taylorCoeff L n / 2

lemma hasSum_logarithmicCoeff {L : ℂ → ℂ} {R : ℝ}
    (hL : DifferentiableOn ℂ L (ball 0 R)) {z : ℂ} (hz : z ∈ ball 0 R) :
    HasSum (fun n : ℕ => 2 * logarithmicCoeff L n * z ^ n) (L z) := by
  simpa [logarithmicCoeff, taylorCoeff, smul_eq_mul, sub_zero, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using Complex.hasSum_taylorSeries_on_ball hL hz

@[simp]
lemma logarithmicCoeff_zero {L : ℂ → ℂ} (hL0 : L 0 = 0) :
    logarithmicCoeff L 0 = 0 := by
  simp [logarithmicCoeff, hL0]


lemma taylorCoeff_dslope {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (n : ℕ) :
    taylorCoeff (dslope f 0) n = taylorCoeff f (n + 1) := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hfAt : AnalyticAt ℂ f 0 := hf.analyticAt (isOpen_ball.mem_nhds hzero)
  have hq : DifferentiableOn ℂ (dslope f 0) (ball 0 R) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hzero)).2 hf
  have hqAt : AnalyticAt ℂ (dslope f 0) 0 := hq.analyticAt (isOpen_ball.mem_nhds hzero)
  have hpf := hfAt.hasFPowerSeriesAt
  have hpq := hqAt.hasFPowerSeriesAt
  have heq := (hpf.has_fpower_series_dslope_fslope).eq_formalMultilinearSeries hpq
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  simpa [taylorCoeff] using hc.symm

lemma taylorCoeff_deriv (f : ℂ → ℂ) (n : ℕ) :
    taylorCoeff (deriv f) n = (n + 1 : ℕ) * taylorCoeff f (n + 1) := by
  rw [taylorCoeff, taylorCoeff, ← iteratedDeriv_succ']
  rw [Nat.factorial_succ]
  push_cast
  field_simp

lemma taylorCoeff_mul {f g : ℂ → ℂ} {n : ℕ}
    (hf : ContDiffAt ℂ n f 0) (hg : ContDiffAt ℂ n g 0) :
    taylorCoeff (f * g) n =
      ∑ i ∈ Finset.range (n + 1), taylorCoeff f i * taylorCoeff g (n - i) := by
  rw [taylorCoeff, iteratedDeriv_mul hf hg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hfac : (n.choose i : ℂ) / n.factorial =
      1 / i.factorial / (n - i).factorial := by
    field_simp [Nat.factorial_ne_zero]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  rw [taylorCoeff, taylorCoeff]
  calc
    (n.choose i * iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0) / n.factorial =
        ((n.choose i : ℂ) / n.factorial) * iteratedDeriv i f 0 *
          iteratedDeriv (n - i) g 0 := by ring
    _ = (1 / i.factorial / (n - i).factorial) * iteratedDeriv i f 0 *
          iteratedDeriv (n - i) g 0 := by rw [hfac]
    _ = (iteratedDeriv i f 0 / i.factorial) *
          (iteratedDeriv (n - i) g 0 / (n - i).factorial) := by ring

lemma taylorCoeff_log_recurrence {q L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hq : DifferentiableOn ℂ q (ball 0 R)) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hderiv : Set.EqOn (deriv q) (q * deriv L) (ball 0 R)) (n : ℕ) :
    (n + 1 : ℕ) * taylorCoeff q (n + 1) =
      ∑ i ∈ Finset.range (n + 1),
        taylorCoeff q i * ((n - i + 1 : ℕ) * taylorCoeff L (n - i + 1)) := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hiter := hderiv.iteratedDeriv_of_isOpen isOpen_ball n hzero
  have hcoef : taylorCoeff (deriv q) n = taylorCoeff (q * deriv L) n := by
    simpa only [taylorCoeff] using congrArg (fun z : ℂ => z / n.factorial) hiter
  have hqCont : ContDiffAt ℂ n q 0 :=
    (hq.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hzero)
  have hLd : DifferentiableOn ℂ (deriv L) (ball 0 R) := hL.deriv isOpen_ball
  have hLdCont : ContDiffAt ℂ n (deriv L) 0 :=
    (hLd.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hzero)
  rw [taylorCoeff_deriv, taylorCoeff_mul hqCont hLdCont] at hcoef
  simpa only [taylorCoeff_deriv] using hcoef

lemma deriv_dslope_eq_mul_deriv_log {f L : ℂ → ℂ} {R : ℝ}
    (hL : DifferentiableOn ℂ L (ball 0 R))
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z) :
    Set.EqOn (deriv (dslope f 0)) ((dslope f 0) * deriv L) (ball 0 R) := by
  intro z hz
  have hdiffL : DifferentiableAt ℂ L z := hL.differentiableAt (isOpen_ball.mem_nhds hz)
  have heq := (show Set.EqOn (fun w => Complex.exp (L w)) (dslope f 0) (ball 0 R)
    from hexp).deriv isOpen_ball hz
  rw [hdiffL.hasDerivAt.cexp.deriv] at heq
  simpa only [Pi.mul_apply, hexp z hz] using heq.symm

lemma normalized_log_recurrence {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z) (n : ℕ) :
    (n + 1 : ℕ) * taylorCoeff f (n + 2) =
      ∑ i ∈ Finset.range (n + 1),
        taylorCoeff f (i + 1) *
          ((n - i + 1 : ℕ) * (2 * logarithmicCoeff L (n - i + 1))) := by
  have hq : DifferentiableOn ℂ (dslope f 0) (ball 0 R) :=
    (Complex.differentiableOn_dslope
      (isOpen_ball.mem_nhds (mem_ball_self hR))).2 hf
  have hrec := taylorCoeff_log_recurrence hR hq hL
    (deriv_dslope_eq_mul_deriv_log hL hexp) n
  have hscale (k : ℕ) : 2 * logarithmicCoeff L k = taylorCoeff L k := by
    rw [logarithmicCoeff]
    field_simp
  simpa [taylorCoeff_dslope hR hf, hscale, Nat.add_assoc] using hrec


end Submission
