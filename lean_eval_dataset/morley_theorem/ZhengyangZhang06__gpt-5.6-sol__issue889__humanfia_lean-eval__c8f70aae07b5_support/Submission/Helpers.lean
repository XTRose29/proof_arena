import ChallengeDeps

open scoped EuclideanGeometry

namespace Submission.Helpers

/-- The trigonometric identity underlying the final cosine-rule step. -/
lemma sin_sq_add_sin_sq_sub_two_mul_of_add_eq_pi (u v θ : ℝ)
    (h : u + v + θ = Real.pi) :
    Real.sin u * Real.sin u + Real.sin v * Real.sin v -
        2 * Real.sin u * Real.sin v * Real.cos θ =
      Real.sin θ * Real.sin θ := by
  have hθ : θ = Real.pi - (u + v) := by linarith
  have hcu : Real.cos u ^ 2 = 1 - Real.sin u ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hcv : Real.cos v ^ 2 = 1 - Real.sin v ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq v]
  rw [hθ, Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_add, Real.cos_add]
  ring_nf
  rw [hcu, hcv]
  ring

/-- A form of the triple-angle identity adapted to thirds of a triangle. -/
lemma sin_three_mul_factor (x : ℝ) :
    Real.sin (3 * x) =
      4 * Real.sin x * Real.sin (Real.pi / 3 - x) *
        Real.sin (Real.pi / 3 + x) := by
  have hcx : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hcπ : Real.cos (Real.pi / 3) ^ 2 =
      1 - Real.sin (Real.pi / 3) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 3)]
  have hprod :
      Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 + x) =
        Real.sin (Real.pi / 3) ^ 2 - Real.sin x ^ 2 := by
    rw [Real.sin_sub, Real.sin_add]
    calc
      (Real.sin (Real.pi / 3) * Real.cos x -
            Real.cos (Real.pi / 3) * Real.sin x) *
          (Real.sin (Real.pi / 3) * Real.cos x +
            Real.cos (Real.pi / 3) * Real.sin x) =
          Real.sin (Real.pi / 3) ^ 2 * Real.cos x ^ 2 -
            Real.cos (Real.pi / 3) ^ 2 * Real.sin x ^ 2 := by ring
      _ = Real.sin (Real.pi / 3) ^ 2 - Real.sin x ^ 2 := by
        rw [hcx, hcπ]
        ring
  rw [Real.sin_three_mul]
  calc
    3 * Real.sin x - 4 * Real.sin x ^ 3 =
        4 * Real.sin x *
          (Real.sin (Real.pi / 3 - x) * Real.sin (Real.pi / 3 + x)) := by
      rw [hprod, Real.sq_sin_pi_div_three]
      ring
    _ = 4 * Real.sin x * Real.sin (Real.pi / 3 - x) *
        Real.sin (Real.pi / 3 + x) := by ring

/-- Cancel the sine-law denominator after applying `sin_three_mul_factor`. -/
lemma solve_sine_law (a b c K d : ℝ) (hsum : a + b + c = Real.pi / 3)
    (hsin : Real.sin (a + b) ≠ 0)
    (h : Real.sin (a + b) * d = Real.sin a * (K * Real.sin (3 * c))) :
    d = (4 * K * Real.sin a * Real.sin c) *
      Real.sin (Real.pi / 3 + c) := by
  have hab : Real.pi / 3 - c = a + b := by linarith
  apply mul_left_cancel₀ hsin
  calc
    Real.sin (a + b) * d =
        Real.sin a * (K * Real.sin (3 * c)) := h
    _ = Real.sin (a + b) *
        ((4 * K * Real.sin a * Real.sin c) *
          Real.sin (Real.pi / 3 + c)) := by
      rw [sin_three_mul_factor, hab]
      ring

/-- The cosine rule for two radial lengths in the form used by Morley's theorem. -/
lemma dist_eq_scaled_sin {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (O X Y : P) (t u v θ : ℝ)
    (hX : dist O X = t * Real.sin u)
    (hY : dist O Y = t * Real.sin v)
    (hangle : ∠ X O Y = θ) (hsum : u + v + θ = Real.pi)
    (ht : 0 ≤ t) (hθ : 0 ≤ Real.sin θ) :
    dist X Y = t * Real.sin θ := by
  have htrig := sin_sq_add_sin_sq_sub_two_mul_of_add_eq_pi u v θ hsum
  have hcos := EuclideanGeometry.law_cos X O Y
  rw [dist_comm X O, dist_comm Y O, hX, hY, hangle] at hcos
  have hsq :
      dist X Y * dist X Y =
        (t * Real.sin θ) * (t * Real.sin θ) := by
    calc
      dist X Y * dist X Y =
          (t * Real.sin u) * (t * Real.sin u) +
            (t * Real.sin v) * (t * Real.sin v) -
              2 * (t * Real.sin u) * (t * Real.sin v) * Real.cos θ := hcos
      _ = t * t *
          (Real.sin u * Real.sin u + Real.sin v * Real.sin v -
            2 * Real.sin u * Real.sin v * Real.cos θ) := by ring
      _ = t * t * (Real.sin θ * Real.sin θ) := by rw [htrig]
      _ = (t * Real.sin θ) * (t * Real.sin θ) := by ring
  nlinarith [(dist_nonneg : 0 ≤ dist X Y), mul_nonneg ht hθ]

end Submission.Helpers
