import Submission.Helpers

open Set
open scoped Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- Data supplied by a bounded analytic capacity function.  Its first
Laurent coefficient is nonzero, its restriction to `K` is in the closed
polynomial algebra, and the first two Laurent terms have a cubic
remainder.  The additional linear far-field bound is used to obtain the
same cubic estimate for the square of the function.

The intended construction takes a bounded injective holomorphic map on
the complement of a local continuum and pulls it back through inversion.
This structure separates that geometric construction from the elementary
two-moment algebra below. -/
structure BoundedLaurentCapacity
    (K : Set ℂ) [CompactSpace K] (a : ℂ) (R : ℝ) where
  u : (polynomialFunctions K).topologicalClosure
  c₁ : ℂ
  c₂ : ℂ
  c₁_ne_zero : c₁ ≠ 0
  L : ℝ
  B : ℝ
  L_nonneg : 0 ≤ L
  B_nonneg : 0 ≤ B
  norm_le_one : ∀ z : K, ‖(u : C(K, ℂ)) z‖ ≤ 1
  norm_le_inv :
    ∀ z : K, R ≤ dist a (z : ℂ) →
      ‖(u : C(K, ℂ)) z‖ ≤ L * (dist a (z : ℂ))⁻¹
  norm_sub_laurent_le :
    ∀ z : K, R ≤ dist a (z : ℂ) →
      ‖(u : C(K, ℂ)) z -
          ((a - (z : ℂ))⁻¹ * c₁ +
            (a - (z : ℂ))⁻¹ ^ 2 * c₂)‖ ≤
        B * (dist a (z : ℂ))⁻¹ ^ 3

/-- The coefficient of the bounded capacity function needed to match the
zeroth moment. -/
def boundedMomentFirstCoefficient
    {K : Set ℂ} [CompactSpace K] {a : ℂ} {R : ℝ}
    (d : BoundedLaurentCapacity K a R) (m₀ : ℂ) : ℂ :=
  m₀ / d.c₁

/-- The coefficient of the square of the bounded capacity function needed
to match the first moment after the zeroth moment has been matched. -/
def boundedMomentSecondCoefficient
    {K : Set ℂ} [CompactSpace K] {a : ℂ} {R : ℝ}
    (d : BoundedLaurentCapacity K a R) (m₀ m₁ : ℂ) : ℂ :=
  (-m₁ - boundedMomentFirstCoefficient d m₀ * d.c₂) /
    d.c₁ ^ 2

/-- The bounded closed-algebra replacement for a two-moment Laurent
model. -/
def boundedMomentReplacement
    {K : Set ℂ} [CompactSpace K] {a : ℂ} {R : ℝ}
    (d : BoundedLaurentCapacity K a R) (m₀ m₁ : ℂ) :
    (polynomialFunctions K).topologicalClosure :=
  boundedMomentFirstCoefficient d m₀ • d.u +
    boundedMomentSecondCoefficient d m₀ m₁ • d.u ^ 2

theorem boundedMoment_coefficients_match
    {K : Set ℂ} [CompactSpace K] {a : ℂ} {R : ℝ}
    (d : BoundedLaurentCapacity K a R) (m₀ m₁ : ℂ) :
    boundedMomentFirstCoefficient d m₀ * d.c₁ = m₀ ∧
      boundedMomentFirstCoefficient d m₀ * d.c₂ +
          boundedMomentSecondCoefficient d m₀ m₁ * d.c₁ ^ 2 =
        -m₁ := by
  constructor
  · exact div_mul_cancel₀ m₀ d.c₁_ne_zero
  · dsimp only [boundedMomentSecondCoefficient]
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 d.c₁_ne_zero)]
    ring

/-- Squaring a bounded capacity function preserves a cubic Laurent
remainder after the square of its leading term is removed. -/
theorem norm_sq_sub_laurentSquare_le
    {K : Set ℂ} [CompactSpace K] {a : ℂ} {R : ℝ}
    (d : BoundedLaurentCapacity K a R)
    (hR : 0 < R) (z : K) (hz : R ≤ dist a (z : ℂ)) :
    ‖(d.u : C(K, ℂ)) z ^ 2 -
        (a - (z : ℂ))⁻¹ ^ 2 * d.c₁ ^ 2‖ ≤
      (d.B * R⁻¹ + ‖d.c₂‖) * (d.L + ‖d.c₁‖) *
        (dist a (z : ℂ))⁻¹ ^ 3 := by
  let s : ℂ := (a - (z : ℂ))⁻¹
  let D : ℝ := dist a (z : ℂ)
  have hD : 0 < D :=
    hR.trans_le hz
  have hs : ‖s‖ = D⁻¹ := by
    dsimp only [s, D]
    rw [norm_inv, ← dist_eq_norm]
  have hRinv : D⁻¹ ≤ R⁻¹ :=
    (inv_le_inv₀ hD hR).2 hz
  have hlinear :
      ‖(d.u : C(K, ℂ)) z + s * d.c₁‖ ≤
        (d.L + ‖d.c₁‖) * D⁻¹ := by
    calc
      ‖(d.u : C(K, ℂ)) z + s * d.c₁‖
          ≤ ‖(d.u : C(K, ℂ)) z‖ + ‖s * d.c₁‖ :=
        norm_add_le _ _
      _ ≤ d.L * D⁻¹ + D⁻¹ * ‖d.c₁‖ := by
        exact add_le_add (d.norm_le_inv z hz)
          (by rw [norm_mul, hs])
      _ = (d.L + ‖d.c₁‖) * D⁻¹ := by ring
  have hquadratic :
      ‖(d.u : C(K, ℂ)) z - s * d.c₁‖ ≤
        (d.B * R⁻¹ + ‖d.c₂‖) * D⁻¹ ^ 2 := by
    calc
      ‖(d.u : C(K, ℂ)) z - s * d.c₁‖ =
          ‖((d.u : C(K, ℂ)) z -
              (s * d.c₁ + s ^ 2 * d.c₂)) +
            s ^ 2 * d.c₂‖ := by
        congr 1
        ring
      _ ≤
          ‖(d.u : C(K, ℂ)) z -
              (s * d.c₁ + s ^ 2 * d.c₂)‖ +
            ‖s ^ 2 * d.c₂‖ :=
        norm_add_le _ _
      _ ≤ d.B * D⁻¹ ^ 3 + D⁻¹ ^ 2 * ‖d.c₂‖ := by
        exact add_le_add (d.norm_sub_laurent_le z hz)
          (by rw [norm_mul, norm_pow, hs])
      _ ≤ (d.B * R⁻¹) * D⁻¹ ^ 2 +
            D⁻¹ ^ 2 * ‖d.c₂‖ := by
        apply add_le_add
        · calc
            d.B * D⁻¹ ^ 3 =
                (d.B * D⁻¹) * D⁻¹ ^ 2 := by ring
            _ ≤ (d.B * R⁻¹) * D⁻¹ ^ 2 := by
              apply mul_le_mul_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left hRinv d.B_nonneg
              · positivity
        · exact le_rfl
      _ = (d.B * R⁻¹ + ‖d.c₂‖) * D⁻¹ ^ 2 := by
        ring
  calc
    ‖(d.u : C(K, ℂ)) z ^ 2 - s ^ 2 * d.c₁ ^ 2‖ =
        ‖((d.u : C(K, ℂ)) z - s * d.c₁) *
          ((d.u : C(K, ℂ)) z + s * d.c₁)‖ := by
      congr 1
      ring
    _ =
        ‖(d.u : C(K, ℂ)) z - s * d.c₁‖ *
          ‖(d.u : C(K, ℂ)) z + s * d.c₁‖ := by
      rw [norm_mul]
    _ ≤
        ((d.B * R⁻¹ + ‖d.c₂‖) * D⁻¹ ^ 2) *
          ((d.L + ‖d.c₁‖) * D⁻¹) := by
      exact mul_le_mul hquadratic hlinear (norm_nonneg _)
        (mul_nonneg
          (add_nonneg
            (mul_nonneg d.B_nonneg (inv_nonneg.mpr hR.le))
            (norm_nonneg d.c₂))
          (sq_nonneg D⁻¹))
    _ =
        (d.B * R⁻¹ + ‖d.c₂‖) * (d.L + ‖d.c₁‖) *
          D⁻¹ ^ 3 := by
      ring

/-- The bounded replacement has a global norm controlled only by its two
scalar matching coefficients. -/
theorem norm_boundedMomentReplacement_le
    {K : Set ℂ} [CompactSpace K] {a : ℂ} {R : ℝ}
    (d : BoundedLaurentCapacity K a R) (m₀ m₁ : ℂ)
    (z : K) :
    ‖(boundedMomentReplacement d m₀ m₁ : C(K, ℂ)) z‖ ≤
      ‖boundedMomentFirstCoefficient d m₀‖ +
        ‖boundedMomentSecondCoefficient d m₀ m₁‖ := by
  change
    ‖boundedMomentFirstCoefficient d m₀ *
          (d.u : C(K, ℂ)) z +
        boundedMomentSecondCoefficient d m₀ m₁ *
          (d.u : C(K, ℂ)) z ^ 2‖ ≤ _
  calc
    _ ≤
        ‖boundedMomentFirstCoefficient d m₀‖ *
            ‖(d.u : C(K, ℂ)) z‖ +
          ‖boundedMomentSecondCoefficient d m₀ m₁‖ *
            ‖(d.u : C(K, ℂ)) z ^ 2‖ := by
      have h :=
        norm_add_le
          (boundedMomentFirstCoefficient d m₀ *
            (d.u : C(K, ℂ)) z)
          (boundedMomentSecondCoefficient d m₀ m₁ *
            (d.u : C(K, ℂ)) z ^ 2)
      rw [norm_mul, norm_mul] at h
      exact h
    _ ≤
        ‖boundedMomentFirstCoefficient d m₀‖ * 1 +
          ‖boundedMomentSecondCoefficient d m₀ m₁‖ * 1 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (d.norm_le_one z)
          (norm_nonneg _)
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [norm_pow]
        nlinarith [d.norm_le_one z, norm_nonneg ((d.u : C(K, ℂ)) z)]
    _ = _ := by ring

/-- Far from the local continuum, the bounded replacement agrees with the
prescribed zeroth/first-moment Laurent model up to cubic order. -/
theorem norm_boundedMomentReplacement_sub_moments_far_le
    {K : Set ℂ} [CompactSpace K] {a : ℂ} {R : ℝ}
    (d : BoundedLaurentCapacity K a R)
    (hR : 0 < R) (m₀ m₁ : ℂ)
    (z : K) (hz : R ≤ dist a (z : ℂ)) :
    ‖(boundedMomentReplacement d m₀ m₁ : C(K, ℂ)) z -
        ((a - (z : ℂ))⁻¹ * m₀ -
          (a - (z : ℂ))⁻¹ ^ 2 * m₁)‖ ≤
      (‖boundedMomentFirstCoefficient d m₀‖ * d.B +
          ‖boundedMomentSecondCoefficient d m₀ m₁‖ *
            ((d.B * R⁻¹ + ‖d.c₂‖) *
              (d.L + ‖d.c₁‖))) *
        (dist a (z : ℂ))⁻¹ ^ 3 := by
  let s : ℂ := (a - (z : ℂ))⁻¹
  let α : ℂ := boundedMomentFirstCoefficient d m₀
  let β : ℂ := boundedMomentSecondCoefficient d m₀ m₁
  have hcoeff := boundedMoment_coefficients_match d m₀ m₁
  change
    α * d.c₁ = m₀ ∧
      α * d.c₂ + β * d.c₁ ^ 2 = -m₁ at hcoeff
  have hsquare :=
    norm_sq_sub_laurentSquare_le d hR z hz
  change
    ‖α * (d.u : C(K, ℂ)) z +
          β * (d.u : C(K, ℂ)) z ^ 2 -
        (s * m₀ - s ^ 2 * m₁)‖ ≤ _
  have hsplit :
      α * (d.u : C(K, ℂ)) z +
            β * (d.u : C(K, ℂ)) z ^ 2 -
          (s * m₀ - s ^ 2 * m₁) =
        α * ((d.u : C(K, ℂ)) z -
          (s * d.c₁ + s ^ 2 * d.c₂)) +
        β * ((d.u : C(K, ℂ)) z ^ 2 -
          s ^ 2 * d.c₁ ^ 2) := by
    have hm₀ : m₀ = α * d.c₁ :=
      hcoeff.1.symm
    have hm₁ :
        m₁ = -(α * d.c₂ + β * d.c₁ ^ 2) := by
      calc
        m₁ = -(-m₁) := by ring
        _ = -(α * d.c₂ + β * d.c₁ ^ 2) :=
          congrArg Neg.neg hcoeff.2.symm
    rw [hm₀, hm₁]
    ring
  rw [hsplit]
  calc
    ‖α * ((d.u : C(K, ℂ)) z -
          (s * d.c₁ + s ^ 2 * d.c₂)) +
        β * ((d.u : C(K, ℂ)) z ^ 2 -
          s ^ 2 * d.c₁ ^ 2)‖
        ≤
          ‖α‖ *
              ‖(d.u : C(K, ℂ)) z -
                (s * d.c₁ + s ^ 2 * d.c₂)‖ +
          ‖β‖ *
              ‖(d.u : C(K, ℂ)) z ^ 2 -
                s ^ 2 * d.c₁ ^ 2‖ := by
      have h :=
        norm_add_le
          (α * ((d.u : C(K, ℂ)) z -
            (s * d.c₁ + s ^ 2 * d.c₂)))
          (β * ((d.u : C(K, ℂ)) z ^ 2 -
            s ^ 2 * d.c₁ ^ 2))
      rw [norm_mul, norm_mul] at h
      exact h
    _ ≤
        ‖α‖ *
            (d.B * (dist a (z : ℂ))⁻¹ ^ 3) +
          ‖β‖ *
            (((d.B * R⁻¹ + ‖d.c₂‖) *
                (d.L + ‖d.c₁‖)) *
              (dist a (z : ℂ))⁻¹ ^ 3) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (d.norm_sub_laurent_le z hz) (norm_nonneg α))
        (mul_le_mul_of_nonneg_left hsquare (norm_nonneg β))
    _ =
        (‖α‖ * d.B +
            ‖β‖ *
              ((d.B * R⁻¹ + ‖d.c₂‖) *
                (d.L + ‖d.c₁‖))) *
          (dist a (z : ℂ))⁻¹ ^ 3 := by
      ring

end Submission.Helpers
