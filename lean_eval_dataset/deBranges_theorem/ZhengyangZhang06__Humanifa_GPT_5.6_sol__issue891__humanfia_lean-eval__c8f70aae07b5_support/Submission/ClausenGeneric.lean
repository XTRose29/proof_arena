import Mathlib
import Mathlib.RingTheory.PowerSeries.Derivative

namespace Submission

open Nat PowerSeries

noncomputable def eulerDeriv (f : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  PowerSeries.X * PowerSeries.derivative ℝ f

lemma coeff_eulerDeriv (f : ℝ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (eulerDeriv f) = (n : ℝ) * PowerSeries.coeff n f := by
  cases n with
  | zero => simp [eulerDeriv, PowerSeries.coeff_zero_X_mul]
  | succ n =>
      rw [eulerDeriv, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      push_cast
      ring

lemma coeff_add_series (f g : ℝ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (f + g) = PowerSeries.coeff n f + PowerSeries.coeff n g :=
  map_add (PowerSeries.coeff n) f g

@[simp]
lemma constantCoeff_eulerDeriv (f : ℝ⟦X⟧) :
    PowerSeries.constantCoeff (eulerDeriv f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [coeff_eulerDeriv]

lemma eulerDeriv_add (f g : ℝ⟦X⟧) :
    eulerDeriv (f + g) = eulerDeriv f + eulerDeriv g := by
  simp [eulerDeriv, mul_add]

lemma eulerDeriv_mul (f g : ℝ⟦X⟧) :
    eulerDeriv (f * g) = eulerDeriv f * g + f * eulerDeriv g := by
  simp only [eulerDeriv, Derivation.leibniz, smul_eq_mul]
  ring

lemma eulerDeriv_X : eulerDeriv (PowerSeries.X : ℝ⟦X⟧) = PowerSeries.X := by
  simp [eulerDeriv]

@[simp]
lemma eulerDeriv_C (r : ℝ) : eulerDeriv (PowerSeries.C r) = 0 := by
  simp [eulerDeriv]

noncomputable def gaussRecCoeff (a b c : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      gaussRecCoeff a b c n * (a + n) * (b + n) /
        (((n + 1 : ℕ) : ℝ) * (c + n))

lemma gaussRecCoeff_succ {a b c : ℝ} {n : ℕ}
    (hc : c + n ≠ 0) :
    (((n + 1 : ℕ) : ℝ) * (c + n)) * gaussRecCoeff a b c (n + 1) =
      (a + n) * (b + n) * gaussRecCoeff a b c n := by
  rw [gaussRecCoeff]
  field_simp [hc]

noncomputable def gaussRecSeries (a b c : ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk (gaussRecCoeff a b c)

lemma gaussRecCoeff_neg_nat_add_succ (d q : ℕ) (b c : ℝ) :
    gaussRecCoeff (-(d : ℝ)) b c (d + 1 + q) = 0 := by
  induction q with
  | zero =>
      rw [show d + 1 + 0 = d + 1 by omega, gaussRecCoeff]
      push_cast
      ring
  | succ q ih =>
      rw [show d + 1 + (q + 1) = (d + 1 + q) + 1 by omega,
        gaussRecCoeff, ih]
      simp

lemma gaussRecCoeff_neg_nat_eq_zero {d n : ℕ} (b c : ℝ) (h : d < n) :
    gaussRecCoeff (-(d : ℝ)) b c n = 0 := by
  have hn : n = d + 1 + (n - (d + 1)) := by omega
  rw [hn, gaussRecCoeff_neg_nat_add_succ]

@[simp]
lemma coeff_gaussRecSeries (a b c : ℝ) (n : ℕ) :
    PowerSeries.coeff n (gaussRecSeries a b c) = gaussRecCoeff a b c n := by
  simp [gaussRecSeries]

lemma gaussRecSeries_ode {a b c : ℝ}
    (hden : ∀ n : ℕ, c + n ≠ 0) :
    eulerDeriv (eulerDeriv (gaussRecSeries a b c)) +
        PowerSeries.C (c - 1) * eulerDeriv (gaussRecSeries a b c) =
      PowerSeries.X *
        (eulerDeriv (eulerDeriv (gaussRecSeries a b c)) +
          PowerSeries.C (a + b) * eulerDeriv (gaussRecSeries a b c) +
          PowerSeries.C (a * b) * gaussRecSeries a b c) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [coeff_add_series, coeff_eulerDeriv, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, coeff_gaussRecSeries]
    have hrec := gaussRecCoeff_succ (a := a) (b := b) (c := c) (n := n) (hden n)
    push_cast at hrec ⊢
    linear_combination hrec

lemma gaussRecSeries_ode_deriv {a b c : ℝ}
    (hden : ∀ n : ℕ, c + n ≠ 0) :
    eulerDeriv (eulerDeriv (eulerDeriv (gaussRecSeries a b c))) +
        PowerSeries.C (c - 1) *
          eulerDeriv (eulerDeriv (gaussRecSeries a b c)) =
      PowerSeries.X *
        (eulerDeriv (eulerDeriv (eulerDeriv (gaussRecSeries a b c))) +
          PowerSeries.C (a + b + 1) *
            eulerDeriv (eulerDeriv (gaussRecSeries a b c)) +
          PowerSeries.C (a * b + a + b) *
            eulerDeriv (gaussRecSeries a b c) +
          PowerSeries.C (a * b) * gaussRecSeries a b c) := by
  have h := congrArg eulerDeriv
    (gaussRecSeries_ode (a := a) (b := b) (c := c) hden)
  simp only [eulerDeriv_add, eulerDeriv_mul, eulerDeriv_X, eulerDeriv_C,
    zero_mul, zero_add] at h
  convert h using 1
  all_goals simp only [map_add, map_mul, map_one]
  all_goals ring

noncomputable def gaussRecSquareSeries (a b c : ℝ) : ℝ⟦X⟧ :=
  gaussRecSeries a b c * gaussRecSeries a b c

lemma eulerDeriv_gaussRecSquare (a b c : ℝ) :
    eulerDeriv (gaussRecSquareSeries a b c) =
      2 * gaussRecSeries a b c * eulerDeriv (gaussRecSeries a b c) := by
  rw [gaussRecSquareSeries, eulerDeriv_mul]
  ring

lemma eulerDeriv_two_gaussRecSquare (a b c : ℝ) :
    eulerDeriv (eulerDeriv (gaussRecSquareSeries a b c)) =
      2 * eulerDeriv (gaussRecSeries a b c) ^ 2 +
        2 * gaussRecSeries a b c *
          eulerDeriv (eulerDeriv (gaussRecSeries a b c)) := by
  simp only [gaussRecSquareSeries, eulerDeriv_mul, eulerDeriv_add]
  ring

lemma eulerDeriv_three_gaussRecSquare (a b c : ℝ) :
    eulerDeriv (eulerDeriv (eulerDeriv (gaussRecSquareSeries a b c))) =
      6 * eulerDeriv (gaussRecSeries a b c) *
          eulerDeriv (eulerDeriv (gaussRecSeries a b c)) +
        2 * gaussRecSeries a b c *
          eulerDeriv (eulerDeriv (eulerDeriv (gaussRecSeries a b c))) := by
  simp only [gaussRecSquareSeries, eulerDeriv_mul, eulerDeriv_add]
  ring

lemma gaussRecSquareSeries_ode {a b c : ℝ}
    (hc : c = a + b + 1 / 2)
    (hden : ∀ n : ℕ, c + n ≠ 0) :
    eulerDeriv (eulerDeriv (eulerDeriv (gaussRecSquareSeries a b c))) +
        PowerSeries.C (2 * (a + b) + c - 2) *
          eulerDeriv (eulerDeriv (gaussRecSquareSeries a b c)) +
        PowerSeries.C ((2 * (a + b) - 1) * (c - 1)) *
          eulerDeriv (gaussRecSquareSeries a b c) =
      PowerSeries.X *
        (eulerDeriv (eulerDeriv (eulerDeriv (gaussRecSquareSeries a b c))) +
          PowerSeries.C (3 * (a + b)) *
            eulerDeriv (eulerDeriv (gaussRecSquareSeries a b c)) +
          PowerSeries.C (2 * (a + b) ^ 2 + 4 * a * b) *
            eulerDeriv (gaussRecSquareSeries a b c) +
          PowerSeries.C (4 * a * b * (a + b)) *
            gaussRecSquareSeries a b c) := by
  have h2 := gaussRecSeries_ode (a := a) (b := b) (c := c) hden
  have h3 := gaussRecSeries_ode_deriv (a := a) (b := b) (c := c) hden
  have hC2 : PowerSeries.C (2 : ℝ) = (2 : ℝ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℝ →+* ℝ⟦X⟧) 2
  have hC3 : PowerSeries.C (3 : ℝ) = (3 : ℝ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℝ →+* ℝ⟦X⟧) 3
  have hC4 : PowerSeries.C (4 : ℝ) = (4 : ℝ⟦X⟧) :=
    map_ofNat (PowerSeries.C : ℝ →+* ℝ⟦X⟧) 4
  apply sub_eq_zero.mp
  calc
    _ =
        2 * gaussRecSeries a b c *
            (eulerDeriv (eulerDeriv (eulerDeriv (gaussRecSeries a b c))) +
              PowerSeries.C (c - 1) *
                eulerDeriv (eulerDeriv (gaussRecSeries a b c)) -
              PowerSeries.X *
                (eulerDeriv (eulerDeriv (eulerDeriv (gaussRecSeries a b c))) +
                  PowerSeries.C (a + b + 1) *
                    eulerDeriv (eulerDeriv (gaussRecSeries a b c)) +
                  PowerSeries.C (a * b + a + b) *
                    eulerDeriv (gaussRecSeries a b c) +
                  PowerSeries.C (a * b) * gaussRecSeries a b c)) +
          2 *
            (PowerSeries.C (2 * (a + b) - 1) * gaussRecSeries a b c +
              3 * eulerDeriv (gaussRecSeries a b c)) *
            (eulerDeriv (eulerDeriv (gaussRecSeries a b c)) +
              PowerSeries.C (c - 1) * eulerDeriv (gaussRecSeries a b c) -
              PowerSeries.X *
                (eulerDeriv (eulerDeriv (gaussRecSeries a b c)) +
                  PowerSeries.C (a + b) * eulerDeriv (gaussRecSeries a b c) +
                  PowerSeries.C (a * b) * gaussRecSeries a b c)) +
          2 * eulerDeriv (gaussRecSeries a b c) ^ 2 *
            PowerSeries.C (2 * (a + b) - 2 * c + 1) := by
      rw [eulerDeriv_three_gaussRecSquare, eulerDeriv_two_gaussRecSquare,
        eulerDeriv_gaussRecSquare, gaussRecSquareSeries]
      simp only [map_add, map_sub, map_mul, map_pow, map_one]
      rw [hC2, hC3, hC4]
      ring
    _ = 0 := by
      have hzero : 2 * (a + b) - 2 * c + 1 = 0 := by linarith
      rw [sub_eq_zero.mpr h2, sub_eq_zero.mpr h3]
      simp [hzero]

noncomputable def hypergeom3RecCoeff (p q r u v : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      hypergeom3RecCoeff p q r u v n * (p + n) * (q + n) * (r + n) /
        (((n + 1 : ℕ) : ℝ) * (u + n) * (v + n))

@[simp]
lemma hypergeom3RecCoeff_zero (p q r u v : ℝ) :
    hypergeom3RecCoeff p q r u v 0 = 1 := rfl

lemma hypergeom3RecCoeff_succ {p q r u v : ℝ} {n : ℕ}
    (hu : u + n ≠ 0) (hv : v + n ≠ 0) :
    (((n + 1 : ℕ) : ℝ) * (u + n) * (v + n)) *
        hypergeom3RecCoeff p q r u v (n + 1) =
      (p + n) * (q + n) * (r + n) * hypergeom3RecCoeff p q r u v n := by
  rw [hypergeom3RecCoeff]
  field_simp [hu, hv]

lemma hypergeom3RecCoeff_shift_two {p q r u v : ℝ} (n : ℕ)
    (hden : ∀ i : ℕ, u + i ≠ 0 ∧ v + i ≠ 0) :
    hypergeom3RecCoeff (p + 2) (q + 2) (r + 2) (u + 4) (v + 2) n *
        (p * (p + 1) * q * (q + 1) * r * (r + 1)) *
        (u + (n + 2)) * (u + (n + 3)) =
      hypergeom3RecCoeff p q r u v (n + 2) *
        (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * v * (v + 1) *
          u * (u + 1) * (u + 2) * (u + 3)) := by
  induction n with
  | zero =>
      have h0 := hypergeom3RecCoeff_succ (p := p) (q := q) (r := r)
        (u := u) (v := v) (n := 0) (hden 0).1 (hden 0).2
      have h1 := hypergeom3RecCoeff_succ (p := p) (q := q) (r := r)
        (u := u) (v := v) (n := 1) (hden 1).1 (hden 1).2
      norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul,
        hypergeom3RecCoeff_zero] at h0 h1 ⊢
      linear_combination
        -(u + 2) * (u + 3) * (p + 1) * (q + 1) * (r + 1) * h0 -
          (u + 2) * (u + 3) * u * v * h1
  | succ n ih =>
      have hu4 : u + 4 + (n : ℝ) ≠ 0 := by
        convert (hden (n + 4)).1 using 1
        push_cast
        ring
      have hv2 : v + 2 + (n : ℝ) ≠ 0 := by
        convert (hden (n + 2)).2 using 1
        push_cast
        ring
      have hs := hypergeom3RecCoeff_succ
        (p := p + 2) (q := q + 2) (r := r + 2)
        (u := u + 4) (v := v + 2) (n := n) hu4 hv2
      have ho := hypergeom3RecCoeff_succ
        (p := p) (q := q) (r := r) (u := u) (v := v) (n := n + 2)
        (hden (n + 2)).1 (hden (n + 2)).2
      have hM :
          (((n + 1 : ℕ) : ℝ) * (u + (n : ℝ) + 2) * (v + (n : ℝ) + 2)) ≠ 0 := by
        apply mul_ne_zero (mul_ne_zero (by positivity) ?_) ?_
        · convert (hden (n + 2)).1 using 1
          push_cast
          ring
        · convert (hden (n + 2)).2 using 1
          push_cast
          ring
      apply mul_left_cancel₀ hM
      push_cast at hs ho ih ⊢
      linear_combination
        (p * (p + 1) * q * (q + 1) * r * (r + 1)) *
            (u + (n : ℝ) + 2) * (u + (n : ℝ) + 3) * hs -
          ((n : ℝ) + 1) * ((n : ℝ) + 2) * v * (v + 1) *
            u * (u + 1) * (u + 2) * (u + 3) * ho +
          ((p + (n : ℝ) + 2) * (q + (n : ℝ) + 2) *
            (r + (n : ℝ) + 2)) * ih

noncomputable def clausenRecCoeff (a b c : ℝ) : ℕ → ℝ :=
  hypergeom3RecCoeff (2 * a) (2 * b) (a + b) (2 * (a + b)) c

@[simp]
lemma clausenRecCoeff_zero (a b c : ℝ) : clausenRecCoeff a b c 0 = 1 := rfl

lemma clausenRecCoeff_succ {a b c : ℝ} {n : ℕ}
    (hab : 2 * (a + b) + n ≠ 0) (hc : c + n ≠ 0) :
    (((n + 1 : ℕ) : ℝ) * (2 * (a + b) + n) * (c + n)) *
        clausenRecCoeff a b c (n + 1) =
      (2 * a + n) * (2 * b + n) * (a + b + n) *
        clausenRecCoeff a b c n := by
  simpa only [clausenRecCoeff] using
    hypergeom3RecCoeff_succ (p := 2 * a) (q := 2 * b) (r := a + b)
      (u := 2 * (a + b)) (v := c) hab hc

lemma clausenRecCoeff_shift_two {a b c : ℝ} (n : ℕ)
    (hden : ∀ q : ℕ, 2 * (a + b) + q ≠ 0 ∧ c + q ≠ 0) :
    clausenRecCoeff (a + 1) (b + 1) (c + 2) n *
        ((2 * a) * (2 * a + 1) * (2 * b) * (2 * b + 1) *
          (a + b) * (a + b + 1)) *
        (2 * (a + b) + (n + 2)) * (2 * (a + b) + (n + 3)) =
      clausenRecCoeff a b c (n + 2) *
        (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * c * (c + 1) *
          (2 * (a + b)) * (2 * (a + b) + 1) *
          (2 * (a + b) + 2) * (2 * (a + b) + 3)) := by
  simp only [clausenRecCoeff]
  have h := hypergeom3RecCoeff_shift_two (p := 2 * a) (q := 2 * b) (r := a + b)
    (u := 2 * (a + b)) (v := c) n hden
  ring_nf at h ⊢
  exact h

noncomputable def clausenRecSeries (a b c : ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk (clausenRecCoeff a b c)

@[simp]
lemma coeff_clausenRecSeries (a b c : ℝ) (n : ℕ) :
    PowerSeries.coeff n (clausenRecSeries a b c) = clausenRecCoeff a b c n := by
  simp [clausenRecSeries]

lemma clausenRecSeries_ode {a b c : ℝ}
    (hden : ∀ n : ℕ, 2 * (a + b) + n ≠ 0 ∧ c + n ≠ 0) :
    eulerDeriv (eulerDeriv (eulerDeriv (clausenRecSeries a b c))) +
        PowerSeries.C (2 * (a + b) + c - 2) *
          eulerDeriv (eulerDeriv (clausenRecSeries a b c)) +
        PowerSeries.C ((2 * (a + b) - 1) * (c - 1)) *
          eulerDeriv (clausenRecSeries a b c) =
      PowerSeries.X *
        (eulerDeriv (eulerDeriv (eulerDeriv (clausenRecSeries a b c))) +
          PowerSeries.C (3 * (a + b)) *
            eulerDeriv (eulerDeriv (clausenRecSeries a b c)) +
          PowerSeries.C (2 * (a + b) ^ 2 + 4 * a * b) *
            eulerDeriv (clausenRecSeries a b c) +
          PowerSeries.C (4 * a * b * (a + b)) *
            clausenRecSeries a b c) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp only [coeff_add_series, coeff_eulerDeriv, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, coeff_clausenRecSeries]
    have hrec := clausenRecCoeff_succ (a := a) (b := b) (c := c) (n := n)
      (hden n).1 (hden n).2
    push_cast at hrec ⊢
    linear_combination hrec

theorem gaussRecSquareSeries_eq_clausenRecSeries {a b c : ℝ}
    (hc : c = a + b + 1 / 2)
    (hgauss : ∀ n : ℕ, c + n ≠ 0)
    (hclausen : ∀ n : ℕ, 2 * (a + b) + n ≠ 0) :
    gaussRecSquareSeries a b c = clausenRecSeries a b c := by
  have hsquare := gaussRecSquareSeries_ode hc hgauss
  have hcore := clausenRecSeries_ode (fun n => ⟨hclausen n, hgauss n⟩)
  ext n
  induction n with
  | zero =>
      simp [gaussRecSquareSeries, gaussRecSeries, gaussRecCoeff,
        clausenRecSeries, clausenRecCoeff, PowerSeries.coeff_mul]
  | succ n ih =>
      have hs := congrArg (PowerSeries.coeff (n + 1)) hsquare
      have hc' := congrArg (PowerSeries.coeff (n + 1)) hcore
      simp only [coeff_add_series, coeff_eulerDeriv, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul] at hs hc'
      have hd :
          ((((n + 1 : ℕ) : ℝ) * (2 * (a + b) + n) * (c + n))) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by positivity) (hclausen n)) (hgauss n)
      apply mul_left_cancel₀ hd
      push_cast at hs hc' ⊢
      rw [ih] at hs
      linear_combination hs - hc'

end Submission
