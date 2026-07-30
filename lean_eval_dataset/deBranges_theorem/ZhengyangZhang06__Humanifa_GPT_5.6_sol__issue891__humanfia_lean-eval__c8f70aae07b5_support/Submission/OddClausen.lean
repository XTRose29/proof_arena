import Submission.ClausenGeneric

namespace Submission

open Nat PowerSeries

lemma eulerDeriv_sub_series (f g : ℝ⟦X⟧) :
    eulerDeriv (f - g) = eulerDeriv f - eulerDeriv g := by
  apply PowerSeries.ext
  intro n
  simp [coeff_eulerDeriv]
  ring

lemma eulerDeriv_one_sub_X :
    eulerDeriv ((1 : ℝ⟦X⟧) - PowerSeries.X) = -PowerSeries.X := by
  have hone : (1 : ℝ⟦X⟧) = PowerSeries.C 1 :=
    (map_one (PowerSeries.C : ℝ →+* ℝ⟦X⟧)).symm
  rw [hone, eulerDeriv_sub_series, eulerDeriv_C, eulerDeriv_X, zero_sub]

@[simp]
lemma eulerDeriv_natCast (n : ℕ) : eulerDeriv (n : ℝ⟦X⟧) = 0 := by
  rw [← map_natCast (PowerSeries.C : ℝ →+* ℝ⟦X⟧) n, eulerDeriv_C]

@[simp]
lemma eulerDeriv_one_series : eulerDeriv (1 : ℝ⟦X⟧) = 0 := by
  have hone : (1 : ℝ⟦X⟧) = PowerSeries.C 1 :=
    (map_one (PowerSeries.C : ℝ →+* ℝ⟦X⟧)).symm
  rw [hone, eulerDeriv_C]

@[simp]
lemma eulerDeriv_two_series : eulerDeriv (2 : ℝ⟦X⟧) = 0 := by
  have htwo : (2 : ℝ⟦X⟧) = PowerSeries.C 2 :=
    (map_ofNat (PowerSeries.C : ℝ →+* ℝ⟦X⟧) 2).symm
  rw [htwo, eulerDeriv_C]

noncomputable def gaussRecOddSquareSeries (a b c : ℝ) : ℝ⟦X⟧ :=
  (1 - PowerSeries.X) * gaussRecSquareSeries a b c

lemma eulerDeriv_gaussRecOddSquare (a b c : ℝ) :
    eulerDeriv (gaussRecOddSquareSeries a b c) =
      (1 - PowerSeries.X) * eulerDeriv (gaussRecSquareSeries a b c) -
        PowerSeries.X * gaussRecSquareSeries a b c := by
  rw [gaussRecOddSquareSeries, eulerDeriv_mul, eulerDeriv_one_sub_X]
  ring

lemma eulerDeriv_two_gaussRecOddSquare (a b c : ℝ) :
    eulerDeriv (eulerDeriv (gaussRecOddSquareSeries a b c)) =
      (1 - PowerSeries.X) *
          eulerDeriv (eulerDeriv (gaussRecSquareSeries a b c)) -
        2 * PowerSeries.X * eulerDeriv (gaussRecSquareSeries a b c) -
        PowerSeries.X * gaussRecSquareSeries a b c := by
  rw [eulerDeriv_gaussRecOddSquare]
  simp only [eulerDeriv_sub_series, eulerDeriv_mul, eulerDeriv_X,
    eulerDeriv_one_series]
  ring

lemma eulerDeriv_three_gaussRecOddSquare (a b c : ℝ) :
    eulerDeriv (eulerDeriv (eulerDeriv (gaussRecOddSquareSeries a b c))) =
      (1 - PowerSeries.X) *
          eulerDeriv (eulerDeriv (eulerDeriv (gaussRecSquareSeries a b c))) -
        3 * PowerSeries.X *
          eulerDeriv (eulerDeriv (gaussRecSquareSeries a b c)) -
        3 * PowerSeries.X * eulerDeriv (gaussRecSquareSeries a b c) -
        PowerSeries.X * gaussRecSquareSeries a b c := by
  rw [eulerDeriv_two_gaussRecOddSquare]
  simp only [eulerDeriv_sub_series, eulerDeriv_mul, eulerDeriv_X,
    eulerDeriv_one_series, eulerDeriv_two_series]
  ring

lemma oddClausen_algebra {T : Type*} [CommRing T]
    (a b c x f p q r : T) :
    let s := a + b
    let y := f ^ 2
    let y1 := 2 * f * p
    let y2 := 2 * p ^ 2 + 2 * f * q
    let y3 := 6 * p * q + 2 * f * r
    let h := (1 - x) * y
    let h1 := (1 - x) * y1 - x * y
    let h2 := (1 - x) * y2 - 2 * x * y1 - x * y
    let h3 := (1 - x) * y3 - 3 * x * y2 - 3 * x * y1 - x * y
    let g2 := q + (c - 1) * p - x * (q + s * p + a * b * f)
    let g3 := r + (c - 1) * q -
      x * (r + (s + 1) * q + (a * b + s) * p + a * b * f)
    let residual := 2 * c - 2 * s + 1
    let e0 :=
      -(1 + (5 * c - 2 * s - 2) + (4 * c - 2 * s - 1) * (c - 1) +
          4 * (c - a) * (c - b) * (2 * c - s)) +
        2 * (a * b) * (1 + (4 * c - 2 * s - 1))
    let e1 :=
      1 + (6 * c - 3 * s) +
          (2 * (2 * c - s) ^ 2 + 4 * (c - a) * (c - b)) +
          4 * (c - a) * (c - b) * (2 * c - s) -
        2 * (a * b) * (1 + (6 * c - 4 * s + 2))
    h3 + (2 * ((c - a) + (c - b)) + c - 2) * h2 +
        ((2 * ((c - a) + (c - b)) - 1) * (c - 1)) * h1 -
      x * (h3 + 3 * ((c - a) + (c - b)) * h2 +
        (2 * ((c - a) + (c - b)) ^ 2 + 4 * (c - a) * (c - b)) * h1 +
        4 * (c - a) * (c - b) * ((c - a) + (c - b)) * h) =
      2 * f * (1 - x) * g3 +
        (6 * (1 - x) * p +
          2 * ((4 * c - 2 * s - 1) - x * (6 * c - 4 * s + 2)) * f) * g2 +
        2 * residual * (1 - x) * (1 - 3 * x) * p ^ 2 +
        2 * residual *
          (x * (-5 * c + 2 * s - 2) + x ^ 2 * (6 * c - 3 * s + 3)) * f * p +
        e0 * x * f ^ 2 + e1 * x ^ 2 * f ^ 2 := by
  dsimp
  ring

lemma gaussRecOddSquareSeries_ode {a b c : ℝ}
    (hc : c = a + b - 1 / 2)
    (hden : ∀ n : ℕ, c + n ≠ 0) :
    eulerDeriv (eulerDeriv (eulerDeriv (gaussRecOddSquareSeries a b c))) +
        PowerSeries.C (2 * ((c - a) + (c - b)) + c - 2) *
          eulerDeriv (eulerDeriv (gaussRecOddSquareSeries a b c)) +
        PowerSeries.C ((2 * ((c - a) + (c - b)) - 1) * (c - 1)) *
          eulerDeriv (gaussRecOddSquareSeries a b c) =
      PowerSeries.X *
        (eulerDeriv (eulerDeriv (eulerDeriv (gaussRecOddSquareSeries a b c))) +
          PowerSeries.C (3 * ((c - a) + (c - b))) *
            eulerDeriv (eulerDeriv (gaussRecOddSquareSeries a b c)) +
          PowerSeries.C
              (2 * ((c - a) + (c - b)) ^ 2 + 4 * (c - a) * (c - b)) *
            eulerDeriv (gaussRecOddSquareSeries a b c) +
          PowerSeries.C
              (4 * (c - a) * (c - b) * ((c - a) + (c - b))) *
            gaussRecOddSquareSeries a b c) := by
  have h2 := gaussRecSeries_ode (a := a) (b := b) (c := c) hden
  have h3 := gaussRecSeries_ode_deriv (a := a) (b := b) (c := c) hden
  let R : ℝ := 2 * c - 2 * (a + b) + 1
  let E0 : ℝ :=
    -(1 + (5 * c - 2 * (a + b) - 2) +
        (4 * c - 2 * (a + b) - 1) * (c - 1) +
        4 * (c - a) * (c - b) * (2 * c - (a + b))) +
      2 * (a * b) * (1 + (4 * c - 2 * (a + b) - 1))
  let E1 : ℝ :=
    1 + (6 * c - 3 * (a + b)) +
        (2 * (2 * c - (a + b)) ^ 2 + 4 * (c - a) * (c - b)) +
        4 * (c - a) * (c - b) * (2 * c - (a + b)) -
      2 * (a * b) * (1 + (6 * c - 4 * (a + b) + 2))
  apply sub_eq_zero.mp
  calc
    _ =
        2 * gaussRecSeries a b c * (1 - PowerSeries.X) *
          (eulerDeriv
                (eulerDeriv
                  (eulerDeriv (gaussRecSeries a b c))) +
            PowerSeries.C (c - 1) *
              eulerDeriv (eulerDeriv (gaussRecSeries a b c)) -
            PowerSeries.X *
              (eulerDeriv
                  (eulerDeriv
                    (eulerDeriv (gaussRecSeries a b c))) +
                PowerSeries.C (a + b + 1) *
                  eulerDeriv (eulerDeriv (gaussRecSeries a b c)) +
                PowerSeries.C (a * b + a + b) *
                  eulerDeriv (gaussRecSeries a b c) +
                PowerSeries.C (a * b) * gaussRecSeries a b c)) +
        (6 * (1 - PowerSeries.X) *
              eulerDeriv (gaussRecSeries a b c) +
            2 *
              (PowerSeries.C (4 * c - 2 * (a + b) - 1) -
                PowerSeries.X *
                  PowerSeries.C (6 * c - 4 * (a + b) + 2)) *
              gaussRecSeries a b c) *
          (eulerDeriv (eulerDeriv (gaussRecSeries a b c)) +
            PowerSeries.C (c - 1) * eulerDeriv (gaussRecSeries a b c) -
            PowerSeries.X *
              (eulerDeriv (eulerDeriv (gaussRecSeries a b c)) +
                PowerSeries.C (a + b) *
                  eulerDeriv (gaussRecSeries a b c) +
                PowerSeries.C (a * b) * gaussRecSeries a b c)) +
        2 * PowerSeries.C R * (1 - PowerSeries.X) *
          (1 - 3 * PowerSeries.X) *
          eulerDeriv (gaussRecSeries a b c) ^ 2 +
        2 * PowerSeries.C R *
          (PowerSeries.X * PowerSeries.C (-5 * c + 2 * (a + b) - 2) +
            PowerSeries.X ^ 2 * PowerSeries.C (6 * c - 3 * (a + b) + 3)) *
          gaussRecSeries a b c * eulerDeriv (gaussRecSeries a b c) +
        PowerSeries.C E0 * PowerSeries.X * gaussRecSeries a b c ^ 2 +
        PowerSeries.C E1 * PowerSeries.X ^ 2 * gaussRecSeries a b c ^ 2 := by
      rw [eulerDeriv_three_gaussRecOddSquare,
        eulerDeriv_two_gaussRecOddSquare, eulerDeriv_gaussRecOddSquare,
        gaussRecOddSquareSeries, eulerDeriv_three_gaussRecSquare,
        eulerDeriv_two_gaussRecSquare, eulerDeriv_gaussRecSquare,
        gaussRecSquareSeries]
      dsimp only [R, E0, E1]
      simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_one, map_ofNat]
      ring
    _ = 0 := by
      have hR : R = 0 := by
        dsimp only [R]
        rw [hc]
        ring
      have hE0 : E0 = 0 := by
        dsimp only [E0]
        rw [hc]
        ring
      have hE1 : E1 = 0 := by
        dsimp only [E1]
        rw [hc]
        ring
      rw [sub_eq_zero.mpr h2, sub_eq_zero.mpr h3, hR, hE0, hE1]
      simp only [map_zero, zero_mul, mul_zero, add_zero]

theorem gaussRecOddSquareSeries_eq_clausenRecSeries {a b c : ℝ}
    (hc : c = a + b - 1 / 2)
    (hgauss : ∀ n : ℕ, c + n ≠ 0)
    (hclausen : ∀ n : ℕ, 2 * ((c - a) + (c - b)) + n ≠ 0) :
    gaussRecOddSquareSeries a b c =
      clausenRecSeries (c - a) (c - b) c := by
  have hsquare := gaussRecOddSquareSeries_ode hc hgauss
  have hcore := clausenRecSeries_ode
    (a := c - a) (b := c - b) (c := c)
    (fun n => ⟨hclausen n, hgauss n⟩)
  ext n
  induction n with
  | zero =>
      simp [gaussRecOddSquareSeries, gaussRecSquareSeries, gaussRecSeries,
        gaussRecCoeff, clausenRecSeries, clausenRecCoeff, PowerSeries.coeff_mul]
  | succ n ih =>
      have hs := congrArg (PowerSeries.coeff (n + 1)) hsquare
      have hc' := congrArg (PowerSeries.coeff (n + 1)) hcore
      simp only [coeff_add_series, coeff_eulerDeriv, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul] at hs hc'
      have hd :
          ((((n + 1 : ℕ) : ℝ) *
            (2 * ((c - a) + (c - b)) + n) * (c + n))) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by positivity) (hclausen n)) (hgauss n)
      apply mul_left_cancel₀ hd
      push_cast at hs hc' ⊢
      rw [ih] at hs
      linear_combination hs - hc'

end Submission
