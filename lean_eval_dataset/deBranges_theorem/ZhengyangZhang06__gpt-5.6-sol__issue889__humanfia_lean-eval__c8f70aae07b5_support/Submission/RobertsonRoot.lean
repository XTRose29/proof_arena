import Submission.RootTransform
import Submission.Robertson
import Submission.GrunskyInequality

open Metric

namespace Submission

lemma rootTransform_two_eq_halfExp (L : ℂ → ℂ) (z : ℂ) :
    rootTransform L 2 z = z * halfExp L (z ^ 2) := by
  rfl

lemma taylorCoeff_halfExp_power_two
    {L : ℂ → ℂ} {R S : ℝ}
    (hS : 0 < S) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hSR : S ^ 2 < R) (n : ℕ) :
    taylorCoeff (fun z => halfExp L (z ^ 2)) (2 * n) =
      taylorCoeff (halfExp L) n := by
  let H : ℂ → ℂ := fun z => (2 : ℂ) * halfExp L z
  have hH : DifferentiableOn ℂ H (ball 0 R) := by
    intro z hz
    exact (differentiableAt_const (2 : ℂ)).mul
      ((differentiableOn_halfExp hL).differentiableAt (isOpen_ball.mem_nhds hz))
      |>.differentiableWithinAt
  have hfun : (fun z => halfExp L (z ^ 2)) = rootTransformLog H 2 := by
    funext z
    simp [H, rootTransformLog]
  rw [hfun, taylorCoeff_rootTransformLog_mul hS (by norm_num) hH hSR,
    taylorCoeff_const_mul_function]
  ring

lemma taylorCoeff_halfExp_power_two_odd
    {L : ℂ → ℂ} {R S : ℝ}
    (hS : 0 < S) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hSR : S ^ 2 < R) (n : ℕ) :
    taylorCoeff (fun z => halfExp L (z ^ 2)) (2 * n + 1) = 0 := by
  let H : ℂ → ℂ := fun z => (2 : ℂ) * halfExp L z
  have hH : DifferentiableOn ℂ H (ball 0 R) := by
    intro z hz
    exact (differentiableAt_const (2 : ℂ)).mul
      ((differentiableOn_halfExp hL).differentiableAt (isOpen_ball.mem_nhds hz))
      |>.differentiableWithinAt
  have hfun : (fun z => halfExp L (z ^ 2)) = rootTransformLog H 2 := by
    funext z
    simp [H, rootTransformLog]
  rw [hfun, taylorCoeff_rootTransformLog_add_lt hS (by norm_num) hH hSR
    (by norm_num) (by norm_num)]

set_option maxHeartbeats 500000 in
lemma taylorCoeff_rootTransform_two_odd
    {L : ℂ → ℂ} {R S : ℝ}
    (hS : 0 < S) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hSR : S ^ 2 < R) (n : ℕ) :
    taylorCoeff (rootTransform L 2) (2 * n + 1) =
      taylorCoeff (halfExp L) n := by
  rw [show rootTransform L 2 = fun z => z * halfExp L (z ^ 2) by
    funext z
    exact rootTransform_two_eq_halfExp L z]
  have hcomp : DifferentiableOn ℂ (fun z => halfExp L (z ^ 2)) (ball 0 S) := by
    intro z hz
    have hzR : z ^ 2 ∈ ball (0 : ℂ) R := pow_mem_ball (by norm_num) hSR hz
    exact ((differentiableOn_halfExp hL).differentiableAt
      (isOpen_ball.mem_nhds hzR)).comp z (differentiableAt_pow 2)
      |>.differentiableWithinAt
  have hshift :
      taylorCoeff (fun z => z ^ 1 * halfExp L (z ^ 2)) (2 * n + 1) =
        taylorCoeff (fun z => halfExp L (z ^ 2)) (2 * n) := by
    simpa only [if_pos (by omega : 1 ≤ 2 * n + 1),
      show 2 * n + 1 - 1 = 2 * n by omega] using
      taylorCoeff_pow_mul hS hcomp 1 (2 * n + 1)
  calc
    taylorCoeff (fun z => z * halfExp L (z ^ 2)) (2 * n + 1) =
        taylorCoeff (fun z => z ^ 1 * halfExp L (z ^ 2)) (2 * n + 1) := by
      simp only [pow_one]
    _ = taylorCoeff (fun z => halfExp L (z ^ 2)) (2 * n) := hshift
    _ = taylorCoeff (halfExp L) n := taylorCoeff_halfExp_power_two hS hL hSR n

end Submission
