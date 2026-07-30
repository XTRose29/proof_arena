import Mathlib
import Submission.Logarithmic

open Metric

namespace Submission

noncomputable def halfExp (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (L z / (2 : ℂ))

lemma differentiableOn_halfExp {L : ℂ → ℂ} {R : ℝ}
    (hL : DifferentiableOn ℂ L (ball 0 R)) :
    DifferentiableOn ℂ (halfExp L) (ball 0 R) := by
  intro z hz
  change DifferentiableWithinAt ℂ (fun w : ℂ => Complex.exp (L w / (2 : ℂ)))
    (ball 0 R) z
  exact ((hL z hz).div_const (2 : ℂ)).cexp

lemma halfExp_mul_self (L : ℂ → ℂ) (z : ℂ) :
    halfExp L z * halfExp L z = Complex.exp (L z) := by
  rw [halfExp, ← Complex.exp_add]
  congr 1
  ring

lemma taylorCoeff_eq_halfExp_convolution {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z) (n : ℕ) :
    taylorCoeff f (n + 1) =
      ∑ i ∈ Finset.range (n + 1),
        taylorCoeff (halfExp L) i * taylorCoeff (halfExp L) (n - i) := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hEq : Set.EqOn (dslope f 0) ((halfExp L) * (halfExp L)) (ball 0 R) := by
    intro z hz
    calc
      dslope f 0 z = Complex.exp (L z) := (hexp z hz).symm
      _ = halfExp L z * halfExp L z := (halfExp_mul_self L z).symm
      _ = ((halfExp L) * (halfExp L)) z := rfl
  have hiter := hEq.iteratedDeriv_of_isOpen isOpen_ball n hzero
  have hcoef : taylorCoeff (dslope f 0) n =
      taylorCoeff ((halfExp L) * (halfExp L)) n := by
    simpa only [taylorCoeff] using
      congrArg (fun z : ℂ => z / n.factorial) hiter
  have hHCont : ContDiffAt ℂ n (halfExp L) 0 :=
    ((differentiableOn_halfExp hL).contDiffOn isOpen_ball).contDiffAt
      (isOpen_ball.mem_nhds hzero)
  rw [taylorCoeff_dslope hR hf, taylorCoeff_mul hHCont hHCont] at hcoef
  exact hcoef

lemma norm_sum_mul_reverse_le_sum_sq (b : ℕ → ℂ) (n : ℕ) :
    ‖∑ i ∈ Finset.range (n + 1), b i * b (n - i)‖ ≤
      ∑ i ∈ Finset.range (n + 1), ‖b i‖ ^ 2 := by
  have hreflect :
      (∑ i ∈ Finset.range (n + 1), ‖b (n - i)‖ ^ 2) =
        ∑ i ∈ Finset.range (n + 1), ‖b i‖ ^ 2 := by
    simpa using
      (Finset.sum_range_reflect (fun i => ‖b i‖ ^ 2) (n + 1))
  calc
    ‖∑ i ∈ Finset.range (n + 1), b i * b (n - i)‖ ≤
        ∑ i ∈ Finset.range (n + 1), ‖b i * b (n - i)‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (n + 1), ‖b i‖ * ‖b (n - i)‖ := by
      simp only [norm_mul]
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (‖b i‖ ^ 2 + ‖b (n - i)‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [sq_nonneg (‖b i‖ - ‖b (n - i)‖)]
    _ = ∑ i ∈ Finset.range (n + 1), ‖b i‖ ^ 2 := by
      simp_rw [add_div]
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, hreflect]
      ring

lemma taylorCoeff_norm_le_of_robertson {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z) (n : ℕ)
    (hrobertson :
      ∑ i ∈ Finset.range (n + 1), ‖taylorCoeff (halfExp L) i‖ ^ 2 ≤ n + 1) :
    ‖taylorCoeff f (n + 1)‖ ≤ n + 1 := by
  rw [taylorCoeff_eq_halfExp_convolution hR hf hL hexp n]
  exact (norm_sum_mul_reverse_le_sum_sq (fun i => taylorCoeff (halfExp L) i) n).trans
    hrobertson

lemma normalized_coeff_bound_of_robertson {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hrobertson : ∀ n : ℕ,
      ∑ i ∈ Finset.range (n + 1), ‖taylorCoeff (halfExp L) i‖ ^ 2 ≤ n + 1)
    (n : ℕ) : ‖taylorCoeff f n‖ ≤ n := by
  rcases n with _ | n
  · simp [taylorCoeff_zero hf.2.2.1]
  · simpa only [Nat.cast_add, Nat.cast_one] using
      taylorCoeff_norm_le_of_robertson hR hf.1 hL hexp n (hrobertson n)

end Submission
