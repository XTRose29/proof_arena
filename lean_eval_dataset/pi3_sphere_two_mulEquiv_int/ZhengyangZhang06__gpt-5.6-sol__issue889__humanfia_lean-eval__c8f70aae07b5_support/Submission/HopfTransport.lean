import Submission.Helpers

open scoped ComplexConjugate unitInterval

noncomputable section

namespace Submission.HopfTransport

open Submission.Helpers

/-- The complex number `a + bi` associated with two real coordinates. -/
def plus (a b : ℝ) : ℂ :=
  (a : ℂ) + (b : ℂ) * Complex.I

/-- The complex conjugate `a - bi`. -/
def minus (a b : ℝ) : ℂ :=
  (a : ℂ) - (b : ℂ) * Complex.I

lemma plus_mul_minus (a b : ℝ) :
    plus a b * minus a b = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [plus, minus, pow_two, Complex.mul_re, Complex.mul_im]
  · simp [plus, minus, pow_two, Complex.mul_re, Complex.mul_im]
    ring

lemma minus_mul_plus (a b : ℝ) :
    minus a b * plus a b = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, plus_mul_minus]

@[simp]
lemma conj_minus (a b : ℝ) :
    conj (minus a b) = plus a b := by
  apply Complex.ext <;> simp [plus, minus]

lemma normSq_minus (a b : ℝ) :
    Complex.normSq (minus a b) = a ^ 2 + b ^ 2 := by
  simp [minus, Complex.normSq_apply]
  ring

/-- First coordinate of the unnormalized short Hopf transport. -/
def first (a b c : ℝ) (u v : ℂ) : ℂ :=
  ((1 + c : ℝ) : ℂ) * u +
    plus a b * v

/-- Second coordinate of the unnormalized short Hopf transport. -/
def second (a b c : ℝ) (u v : ℂ) : ℂ :=
  minus a b * u +
    ((1 - c : ℝ) : ℂ) * v

lemma continuous_first {A : Type*} [TopologicalSpace A]
    {a b c : A → ℝ} {u v : A → ℂ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x => first (a x) (b x) (c x) (u x) (v x) := by
  unfold first plus
  exact
    ((Complex.continuous_ofReal.comp (continuous_const.add hc)).mul hu).add
      (((Complex.continuous_ofReal.comp ha).add
        ((Complex.continuous_ofReal.comp hb).mul continuous_const)).mul hv)

lemma continuous_second {A : Type*} [TopologicalSpace A]
    {a b c : A → ℝ} {u v : A → ℂ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x => second (a x) (b x) (c x) (u x) (v x) := by
  unfold second minus
  exact
    (((Complex.continuous_ofReal.comp ha).sub
        ((Complex.continuous_ofReal.comp hb).mul continuous_const)).mul hu).add
      ((Complex.continuous_ofReal.comp (continuous_const.sub hc)).mul hv)

lemma first_relation {a b c : ℝ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 1)
    (u v : ℂ) :
    ((1 - c : ℝ) : ℂ) * first a b c u v =
      plus a b * second a b c u v := by
  have hcoeff :
      ((1 - c : ℝ) : ℂ) * ((1 + c : ℝ) : ℂ) =
        ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
    norm_cast
    nlinarith
  calc
    ((1 - c : ℝ) : ℂ) * first a b c u v =
        (((1 - c : ℝ) : ℂ) * ((1 + c : ℝ) : ℂ)) * u +
          (((1 - c : ℝ) : ℂ) * plus a b) * v := by
      simp only [first]
      ring
    _ = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) * u +
          (((1 - c : ℝ) : ℂ) * plus a b) * v := by
      rw [hcoeff]
    _ = plus a b * second a b c u v := by
      rw [← plus_mul_minus]
      simp only [second]
      ring

lemma second_relation {a b c : ℝ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 1)
    (u v : ℂ) :
    minus a b * first a b c u v =
      ((1 + c : ℝ) : ℂ) * second a b c u v := by
  have hcoeff :
      ((1 - c : ℝ) : ℂ) * ((1 + c : ℝ) : ℂ) =
        ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
    norm_cast
    nlinarith
  calc
    minus a b * first a b c u v =
        (((1 + c : ℝ) : ℂ) * minus a b) * u +
          (minus a b * plus a b) * v := by
      simp only [first]
      ring
    _ = (((1 + c : ℝ) : ℂ) * minus a b) * u +
          ((a ^ 2 + b ^ 2 : ℝ) : ℂ) * v := by
      rw [minus_mul_plus]
    _ = ((1 + c : ℝ) : ℂ) * second a b c u v := by
      rw [← hcoeff]
      simp only [second]
      ring

/-- The two eigenspace relations determine the three Hopf coordinates. -/
lemma coordinates_of_relations {a b c : ℝ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 1)
    (w₀ w₁ : ℂ)
    (hfirst :
      ((1 - c : ℝ) : ℂ) * w₀ = plus a b * w₁)
    (hsecond :
      minus a b * w₀ = ((1 + c : ℝ) : ℂ) * w₁) :
    2 * (w₀ * conj w₁).re =
        (Complex.normSq w₀ + Complex.normSq w₁) * a ∧
      2 * (w₀ * conj w₁).im =
        (Complex.normSq w₀ + Complex.normSq w₁) * b ∧
      Complex.normSq w₀ - Complex.normSq w₁ =
        (Complex.normSq w₀ + Complex.normSq w₁) * c := by
  by_cases hc : c = -1
  · have ha : a = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    have hw₀ : w₀ = 0 := by
      have hzero : (2 : ℂ) * w₀ = 0 := by
        simpa [hc, ha, hb, plus] using hfirst
      exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    subst w₀
    simp [ha, hb, hc, Complex.normSq_apply]
  · have hc_lower : -1 ≤ c := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    have hc_strict : -1 < c :=
      lt_of_le_of_ne hc_lower (Ne.symm hc)
    have hd_pos : 0 < 1 + c := by
      linarith
    have hd : 1 + c ≠ 0 := ne_of_gt hd_pos
    have hdC : ((1 + c : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hd
    have hab : a ^ 2 + b ^ 2 = (1 - c) * (1 + c) := by
      nlinarith
    have hnorm := congrArg Complex.normSq hsecond
    rw [Complex.normSq_mul, normSq_minus, Complex.normSq_mul,
      Complex.normSq_ofReal, hab] at hnorm
    have hbalance :
        (1 - c) * Complex.normSq w₀ =
          (1 + c) * Complex.normSq w₁ := by
      apply mul_left_cancel₀ hd
      calc
        (1 + c) * ((1 - c) * Complex.normSq w₀) =
            ((1 - c) * (1 + c)) * Complex.normSq w₀ := by ring
        _ = ((1 + c) * (1 + c)) * Complex.normSq w₁ := hnorm
        _ = (1 + c) * ((1 + c) * Complex.normSq w₁) := by ring
    have hsum :
        (Complex.normSq w₀ + Complex.normSq w₁) * (1 + c) =
          2 * Complex.normSq w₀ := by
      calc
        (Complex.normSq w₀ + Complex.normSq w₁) * (1 + c) =
            (1 + c) * Complex.normSq w₀ +
              (1 + c) * Complex.normSq w₁ := by ring
        _ = (1 + c) * Complex.normSq w₀ +
              (1 - c) * Complex.normSq w₀ := by rw [← hbalance]
        _ = 2 * Complex.normSq w₀ := by ring
    have hconj :
        plus a b * conj w₀ =
          ((1 + c : ℝ) : ℂ) * conj w₁ := by
      simpa using congrArg conj hsecond
    have hcrossD :
        ((1 + c : ℝ) : ℂ) * (w₀ * conj w₁) =
          plus a b * (Complex.normSq w₀ : ℂ) := by
      calc
        ((1 + c : ℝ) : ℂ) * (w₀ * conj w₁) =
            w₀ * (((1 + c : ℝ) : ℂ) * conj w₁) := by ring
        _ = w₀ * (plus a b * conj w₀) := by rw [← hconj]
        _ = plus a b * (w₀ * conj w₀) := by ring
        _ = plus a b * (Complex.normSq w₀ : ℂ) := by
          rw [Complex.mul_conj]
    have hcross :
        (2 : ℂ) * (w₀ * conj w₁) =
          plus a b *
            ((Complex.normSq w₀ + Complex.normSq w₁ : ℝ) : ℂ) := by
      apply mul_left_cancel₀ hdC
      calc
        ((1 + c : ℝ) : ℂ) * ((2 : ℂ) * (w₀ * conj w₁)) =
            (2 : ℂ) *
              (((1 + c : ℝ) : ℂ) * (w₀ * conj w₁)) := by ring
        _ = (2 : ℂ) *
              (plus a b * (Complex.normSq w₀ : ℂ)) := by rw [hcrossD]
        _ = plus a b * ((2 * Complex.normSq w₀ : ℝ) : ℂ) := by
          push_cast
          ring
        _ = plus a b *
              (((Complex.normSq w₀ + Complex.normSq w₁) *
                (1 + c) : ℝ) : ℂ) := by rw [hsum]
        _ = ((1 + c : ℝ) : ℂ) *
              (plus a b *
                ((Complex.normSq w₀ + Complex.normSq w₁ : ℝ) : ℂ)) := by
          push_cast
          ring
    have hdiff :
        Complex.normSq w₀ - Complex.normSq w₁ =
          (Complex.normSq w₀ + Complex.normSq w₁) * c := by
      apply mul_left_cancel₀ hd
      calc
        (1 + c) * (Complex.normSq w₀ - Complex.normSq w₁) =
            (1 + c) * Complex.normSq w₀ -
              (1 + c) * Complex.normSq w₁ := by ring
        _ = (1 + c) * Complex.normSq w₀ -
              (1 - c) * Complex.normSq w₀ := by rw [← hbalance]
        _ = c * (2 * Complex.normSq w₀) := by ring
        _ = c *
              ((Complex.normSq w₀ + Complex.normSq w₁) * (1 + c)) := by
          rw [hsum]
        _ = (1 + c) *
              ((Complex.normSq w₀ + Complex.normSq w₁) * c) := by ring
    refine ⟨?_, ?_, hdiff⟩
    · have hre := congrArg Complex.re hcross
      simpa [plus, mul_comm] using hre
    · have him := congrArg Complex.im hcross
      simpa [plus, mul_comm] using him

lemma first_hopf (u v : ℂ) :
    first
        (2 * (u * conj v).re)
        (2 * (u * conj v).im)
        (Complex.normSq u - Complex.normSq v) u v =
      (1 + ((Complex.normSq u + Complex.normSq v : ℝ) : ℂ)) * u := by
  apply Complex.ext <;>
    simp [first, plus, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im] <;>
    ring

lemma second_hopf (u v : ℂ) :
    second
        (2 * (u * conj v).re)
        (2 * (u * conj v).im)
        (Complex.normSq u - Complex.normSq v) u v =
      (1 + ((Complex.normSq u + Complex.normSq v : ℝ) : ℂ)) * v := by
  apply Complex.ext <;>
    simp [second, minus, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im] <;>
    ring

lemma first_second_normSq (a b c : ℝ) (u v : ℂ) :
    Complex.normSq (first a b c u v) +
        Complex.normSq (second a b c u v) =
      (1 + (a ^ 2 + b ^ 2 + c ^ 2)) *
          (Complex.normSq u + Complex.normSq v) +
        2 * (2 * (u * conj v).re * a +
          2 * (u * conj v).im * b +
          (Complex.normSq u - Complex.normSq v) * c) := by
  simp [first, second, plus, minus, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

/-- The unnormalized spinor obtained by projecting `z` to the positive
eigenspace associated with `y`.  It is nonzero exactly when `y` is not
antipodal to `hopfMap z`. -/
def raw (z : SphereThree) (y : SphereTwo) :
    EuclideanSpace ℂ (Fin 2) :=
  !₂[
    first (y.1 0) (y.1 1) (y.1 2) (z.1 0) (z.1 1),
    second (y.1 0) (y.1 1) (y.1 2) (z.1 0) (z.1 1)]

lemma continuous_raw :
    Continuous fun p : SphereThree × SphereTwo => raw p.1 p.2 := by
  unfold raw
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp ?_
  apply continuous_pi
  intro i
  fin_cases i
  · apply continuous_first <;> fun_prop
  · apply continuous_second <;> fun_prop

lemma raw_self (z : SphereThree) :
    raw z (hopfMap z) =
      (z : EuclideanSpace ℂ (Fin 2)) + z := by
  have hz := sphereThree_normSq_add z
  have hzC :
      ((Complex.normSq (z.1 0) + Complex.normSq (z.1 1) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hz
  ext i
  fin_cases i
  · calc
      raw z (hopfMap z) 0 =
          (1 + ((Complex.normSq (z.1 0) +
              Complex.normSq (z.1 1) : ℝ) : ℂ)) * z.1 0 := by
            simpa [raw, hopfMap, hopfMapRaw, Matrix.cons_val_two] using
              first_hopf (z.1 0) (z.1 1)
      _ = (z + z : EuclideanSpace ℂ (Fin 2)) 0 := by
        rw [hzC]
        rw [PiLp.add_apply]
        ring
  · calc
      raw z (hopfMap z) 1 =
          (1 + ((Complex.normSq (z.1 0) +
              Complex.normSq (z.1 1) : ℝ) : ℂ)) * z.1 1 := by
            simpa [raw, hopfMap, hopfMapRaw, Matrix.cons_val_two] using
              second_hopf (z.1 0) (z.1 1)
      _ = (z + z : EuclideanSpace ℂ (Fin 2)) 1 := by
        rw [hzC]
        rw [PiLp.add_apply]
        ring

/-- The squared norm of the raw transported spinor. -/
lemma raw_normSq (z : SphereThree) (y : SphereTwo) :
    Complex.normSq (raw z y 0) + Complex.normSq (raw z y 1) =
      2 * (1 +
        (hopfMap z).1 0 * y.1 0 +
        (hopfMap z).1 1 * y.1 1 +
        (hopfMap z).1 2 * y.1 2) := by
  have hz := sphereThree_normSq_add z
  have hy := sphereTwo_sq_add y
  calc
    Complex.normSq (raw z y 0) + Complex.normSq (raw z y 1) =
        (1 + (y.1 0 ^ 2 + y.1 1 ^ 2 + y.1 2 ^ 2)) *
            (Complex.normSq (z.1 0) + Complex.normSq (z.1 1)) +
          2 * ((hopfMap z).1 0 * y.1 0 +
            (hopfMap z).1 1 * y.1 1 +
            (hopfMap z).1 2 * y.1 2) := by
      simpa [raw, hopfMap, hopfMapRaw, Matrix.cons_val_two] using
        first_second_normSq (y.1 0) (y.1 1) (y.1 2)
          (z.1 0) (z.1 1)
    _ = 2 * (1 +
        (hopfMap z).1 0 * y.1 0 +
        (hopfMap z).1 1 * y.1 1 +
        (hopfMap z).1 2 * y.1 2) := by
      rw [hy, hz]
      ring

/-- The raw spinor has Hopf coordinates equal to the target coordinates,
scaled by its squared norm. -/
lemma raw_coordinates (z : SphereThree) (y : SphereTwo) :
    2 * (raw z y 0 * conj (raw z y 1)).re =
        (Complex.normSq (raw z y 0) + Complex.normSq (raw z y 1)) *
          y.1 0 ∧
      2 * (raw z y 0 * conj (raw z y 1)).im =
        (Complex.normSq (raw z y 0) + Complex.normSq (raw z y 1)) *
          y.1 1 ∧
      Complex.normSq (raw z y 0) - Complex.normSq (raw z y 1) =
        (Complex.normSq (raw z y 0) + Complex.normSq (raw z y 1)) *
          y.1 2 := by
  apply coordinates_of_relations (sphereTwo_sq_add y)
  · simpa [raw] using
      first_relation (sphereTwo_sq_add y) (z.1 0) (z.1 1)
  · simpa [raw] using
      second_relation (sphereTwo_sq_add y) (z.1 0) (z.1 1)

/-- Polynomial form of the projection law for the unnormalized transport. -/
lemma hopfMapRaw_raw (z : SphereThree) (y : SphereTwo) :
    hopfMapRaw (raw z y) =
      (Complex.normSq (raw z y 0) + Complex.normSq (raw z y 1)) •
        (y : EuclideanSpace ℝ (Fin 3)) := by
  have h := raw_coordinates z y
  ext i
  fin_cases i
  · simpa [hopfMapRaw] using h.1
  · simpa [hopfMapRaw] using h.2.1
  · simpa [hopfMapRaw, Matrix.cons_val_two] using h.2.2

end Submission.HopfTransport
