import Submission.ScaleControlledCapacity

open Set
open scoped Polynomial Topology

noncomputable section

namespace Submission.Helpers

def scaleReplacementGlobalConstant (c₂ : ℂ) : ℝ :=
  2550 + 2000000 * ‖c₂‖

def scaleCapacityRadius (ρ : ℝ) : ℝ :=
  max 7 (4 * ρ⁻¹)

def scaleCapacityLinearConstant
    (c₂ : ℂ) (B ρ : ℝ) : ℝ :=
  B * ρ ^ 2 + ‖(1 / 100 : ℂ)‖ + ρ * ‖c₂‖

def scaleReplacementFarAux
    (c₂ : ℂ) (B ρ : ℝ) : ℝ :=
  (64 * B + 16 * ‖c₂‖) *
    (4 * scaleCapacityLinearConstant c₂ B ρ + 1)

def scaleReplacementFarConstant
    (c₂ : ℂ) (B ρ : ℝ) : ℝ :=
  scaleReplacementGlobalConstant c₂ *
    (64 * B + scaleReplacementFarAux c₂ B ρ)

theorem scaleReplacementGlobalConstant_nonneg (c₂ : ℂ) :
    0 ≤ scaleReplacementGlobalConstant c₂ := by
  dsimp only [scaleReplacementGlobalConstant]
  positivity

theorem scaleCapacityRadius_pos (ρ : ℝ) :
    0 < scaleCapacityRadius ρ := by
  exact (by norm_num : (0 : ℝ) < 7).trans_le
    (le_max_left _ _)

theorem scaleCapacityLinearConstant_nonneg
    (c₂ : ℂ) {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ) :
    0 ≤ scaleCapacityLinearConstant c₂ B ρ := by
  dsimp only [scaleCapacityLinearConstant]
  positivity

theorem scaleReplacementFarAux_nonneg
    (c₂ : ℂ) {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ) :
    0 ≤ scaleReplacementFarAux c₂ B ρ := by
  dsimp only [scaleReplacementFarAux]
  exact
    mul_nonneg
      (add_nonneg (mul_nonneg (by norm_num) hB)
        (mul_nonneg (by norm_num) (norm_nonneg c₂)))
      (add_nonneg
        (mul_nonneg (by norm_num)
          (scaleCapacityLinearConstant_nonneg c₂ hB hρ))
        zero_le_one)

theorem scaleReplacementFarConstant_nonneg
    (c₂ : ℂ) {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ) :
    0 ≤ scaleReplacementFarConstant c₂ B ρ := by
  dsimp only [scaleReplacementFarConstant]
  exact mul_nonneg (scaleReplacementGlobalConstant_nonneg c₂)
    (add_nonneg (mul_nonneg (by norm_num) hB)
      (scaleReplacementFarAux_nonneg c₂ hB hρ))

/-- The matching coefficients of a scale-controlled capacity have the
natural inverse moment scales. -/
theorem norm_boundedMoment_coefficients_scale_le
    {K : Set ℂ} [CompactSpace K]
    {q a : ℂ} {r R : ℝ} (hr : 0 < r)
    (c₂ : ℂ) (d : BoundedLaurentCapacity K a R)
    (hδlow : 2 * r < ‖q - a‖)
    (hδhigh : ‖q - a‖ < 4 * r)
    (hc₁ : d.c₁ = (q - a) * (1 / 100))
    (hc₂ : d.c₂ = (q - a) ^ 2 * c₂)
    (m₀ m₁ : ℂ) :
    ‖boundedMomentFirstCoefficient d m₀‖ +
        ‖boundedMomentSecondCoefficient d m₀ m₁‖ ≤
      scaleReplacementGlobalConstant c₂ *
        (r⁻¹ * ‖m₀‖ + r⁻¹ ^ 2 * ‖m₁‖) := by
  have hδpos : 0 < ‖q - a‖ :=
    (by positivity : 0 < 2 * r).trans hδlow
  have hc₁norm :
      ‖d.c₁‖ = ‖q - a‖ / 100 := by
    rw [hc₁, norm_mul]
    norm_num
    ring
  have hc₁pos : 0 < ‖d.c₁‖ := by
    rw [hc₁norm]
    positivity
  have hc₁lower :
      r / 50 ≤ ‖d.c₁‖ := by
    rw [hc₁norm]
    linarith
  have hc₁inv :
      ‖d.c₁‖⁻¹ ≤ 50 * r⁻¹ := by
    have h :=
      (inv_le_inv₀ hc₁pos
        (by positivity : 0 < r / 50)).2 hc₁lower
    calc
      ‖d.c₁‖⁻¹ ≤ (r / 50)⁻¹ := h
      _ = 50 * r⁻¹ := by
        field_simp [hr.ne']
  have hα :
      ‖boundedMomentFirstCoefficient d m₀‖ ≤
        50 * (r⁻¹ * ‖m₀‖) := by
    rw [boundedMomentFirstCoefficient, norm_div,
      div_eq_mul_inv]
    calc
      ‖m₀‖ * ‖d.c₁‖⁻¹ ≤
          ‖m₀‖ * (50 * r⁻¹) :=
        mul_le_mul_of_nonneg_left hc₁inv (norm_nonneg m₀)
      _ = 50 * (r⁻¹ * ‖m₀‖) := by ring
  have hc₂norm :
      ‖d.c₂‖ ≤ 16 * ‖c₂‖ * r ^ 2 := by
    rw [hc₂, norm_mul, norm_pow]
    have hpow :
        ‖q - a‖ ^ 2 ≤ (4 * r) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        hδhigh.le 2
    calc
      ‖q - a‖ ^ 2 * ‖c₂‖ ≤
          (4 * r) ^ 2 * ‖c₂‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg c₂)
      _ = 16 * ‖c₂‖ * r ^ 2 := by ring
  have hc₁sqInv :
      (‖d.c₁‖ ^ 2)⁻¹ ≤ 2500 * r⁻¹ ^ 2 := by
    calc
      (‖d.c₁‖ ^ 2)⁻¹ = ‖d.c₁‖⁻¹ ^ 2 := by
        rw [inv_pow]
      _ ≤ (50 * r⁻¹) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
          hc₁inv 2
      _ = 2500 * r⁻¹ ^ 2 := by ring
  have hαc₂ :
      ‖boundedMomentFirstCoefficient d m₀‖ * ‖d.c₂‖ ≤
        (50 * (r⁻¹ * ‖m₀‖)) *
          (16 * ‖c₂‖ * r ^ 2) := by
    exact
      mul_le_mul hα hc₂norm (norm_nonneg _)
        (by positivity)
  have hβ :
      ‖boundedMomentSecondCoefficient d m₀ m₁‖ ≤
        2000000 * ‖c₂‖ * (r⁻¹ * ‖m₀‖) +
          2500 * (r⁻¹ ^ 2 * ‖m₁‖) := by
    rw [boundedMomentSecondCoefficient, norm_div,
      norm_pow, div_eq_mul_inv]
    calc
      ‖-m₁ -
          boundedMomentFirstCoefficient d m₀ * d.c₂‖ *
            (‖d.c₁‖ ^ 2)⁻¹
          ≤
            (‖m₁‖ +
              ‖boundedMomentFirstCoefficient d m₀‖ *
                ‖d.c₂‖) *
              (‖d.c₁‖ ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          ‖-m₁ -
              boundedMomentFirstCoefficient d m₀ * d.c₂‖
              ≤ ‖-m₁‖ +
                  ‖boundedMomentFirstCoefficient d m₀ * d.c₂‖ :=
            norm_sub_le _ _
          _ = ‖m₁‖ +
                ‖boundedMomentFirstCoefficient d m₀‖ *
                  ‖d.c₂‖ := by
            rw [norm_neg, norm_mul]
      _ ≤
            (‖m₁‖ +
              (50 * (r⁻¹ * ‖m₀‖)) *
                (16 * ‖c₂‖ * r ^ 2)) *
              (2500 * r⁻¹ ^ 2) := by
        exact
          mul_le_mul
            (add_le_add le_rfl hαc₂)
            hc₁sqInv (by positivity) (by positivity)
      _ =
          2000000 * ‖c₂‖ * (r⁻¹ * ‖m₀‖) +
            2500 * (r⁻¹ ^ 2 * ‖m₁‖) := by
        field_simp [hr.ne']
        ring
  calc
    ‖boundedMomentFirstCoefficient d m₀‖ +
          ‖boundedMomentSecondCoefficient d m₀ m₁‖
        ≤
          50 * (r⁻¹ * ‖m₀‖) +
            (2000000 * ‖c₂‖ *
                (r⁻¹ * ‖m₀‖) +
              2500 * (r⁻¹ ^ 2 * ‖m₁‖)) :=
      add_le_add hα hβ
    _ ≤
        scaleReplacementGlobalConstant c₂ *
          (r⁻¹ * ‖m₀‖ + r⁻¹ ^ 2 * ‖m₁‖) := by
      calc
        50 * (r⁻¹ * ‖m₀‖) +
              (2000000 * ‖c₂‖ *
                  (r⁻¹ * ‖m₀‖) +
                2500 * (r⁻¹ ^ 2 * ‖m₁‖))
            ≤
              50 * (r⁻¹ * ‖m₀‖) +
                (2000000 * ‖c₂‖ *
                    (r⁻¹ * ‖m₀‖) +
                  2500 * (r⁻¹ ^ 2 * ‖m₁‖)) +
                (2500 * (r⁻¹ * ‖m₀‖) +
                  (50 + 2000000 * ‖c₂‖) *
                    (r⁻¹ ^ 2 * ‖m₁‖)) :=
          le_add_of_nonneg_right (by positivity)
        _ =
            scaleReplacementGlobalConstant c₂ *
              (r⁻¹ * ‖m₀‖ + r⁻¹ ^ 2 * ‖m₁‖) := by
          dsimp only [scaleReplacementGlobalConstant]
          ring

/-- Global norm bound for the scale-controlled two-moment replacement. -/
theorem norm_boundedMomentReplacement_scale_le
    {K : Set ℂ} [CompactSpace K]
    {q a : ℂ} {r R : ℝ} (hr : 0 < r)
    (c₂ : ℂ) (d : BoundedLaurentCapacity K a R)
    (hδlow : 2 * r < ‖q - a‖)
    (hδhigh : ‖q - a‖ < 4 * r)
    (hc₁ : d.c₁ = (q - a) * (1 / 100))
    (hc₂ : d.c₂ = (q - a) ^ 2 * c₂)
    (m₀ m₁ : ℂ) (z : K) :
    ‖(boundedMomentReplacement d m₀ m₁ : C(K, ℂ)) z‖ ≤
      scaleReplacementGlobalConstant c₂ *
        (r⁻¹ * ‖m₀‖ + r⁻¹ ^ 2 * ‖m₁‖) := by
  exact
    (norm_boundedMomentReplacement_le d m₀ m₁ z).trans
      (norm_boundedMoment_coefficients_scale_le
        hr c₂ d hδlow hδhigh hc₁ hc₂ m₀ m₁)

/-- The cubic Laurent coefficient of a scale-controlled replacement has
the natural `r² m₀ + r m₁` scale. -/
theorem boundedMomentReplacement_farCoefficient_scale_le
    {K : Set ℂ} [CompactSpace K]
    {q a : ℂ} {r R : ℝ} (hr : 0 < r)
    (c₂ : ℂ) (B ρ : ℝ) (hB : 0 ≤ B) (_hρ : 0 < ρ)
    (d : BoundedLaurentCapacity K a R)
    (hδlow : 2 * r < ‖q - a‖)
    (hδhigh : ‖q - a‖ < 4 * r)
    (hR : R = scaleCapacityRadius ρ * r)
    (hc₁ : d.c₁ = (q - a) * (1 / 100))
    (hc₂ : d.c₂ = (q - a) ^ 2 * c₂)
    (hL :
      d.L =
        4 * scaleCapacityLinearConstant c₂ B ρ * r)
    (hB₃ : d.B = 64 * B * r ^ 3)
    (m₀ m₁ : ℂ) :
    ‖boundedMomentFirstCoefficient d m₀‖ * d.B +
        ‖boundedMomentSecondCoefficient d m₀ m₁‖ *
          ((d.B * R⁻¹ + ‖d.c₂‖) *
            (d.L + ‖d.c₁‖)) ≤
      scaleReplacementFarConstant c₂ B ρ *
        (r ^ 2 * ‖m₀‖ + r * ‖m₁‖) := by
  let α : ℝ :=
    ‖boundedMomentFirstCoefficient d m₀‖
  let β : ℝ :=
    ‖boundedMomentSecondCoefficient d m₀ m₁‖
  let P : ℝ :=
    (d.B * R⁻¹ + ‖d.c₂‖) *
      (d.L + ‖d.c₁‖)
  have hRpos : 0 < R := by
    rw [hR]
    exact mul_pos (scaleCapacityRadius_pos ρ) hr
  have hRlower : r ≤ R := by
    rw [hR]
    apply le_mul_of_one_le_left hr.le
    exact
      (by norm_num : (1 : ℝ) ≤ 7).trans
        (le_max_left _ _)
  have hRinv : R⁻¹ ≤ r⁻¹ :=
    (inv_le_inv₀ hRpos hr).2 hRlower
  have hδpos : 0 < ‖q - a‖ :=
    (by positivity : 0 < 2 * r).trans hδlow
  have hc₁norm :
      ‖d.c₁‖ = ‖q - a‖ / 100 := by
    rw [hc₁, norm_mul]
    norm_num
    ring
  have hc₁upper : ‖d.c₁‖ ≤ r := by
    rw [hc₁norm]
    linarith
  have hc₂norm :
      ‖d.c₂‖ ≤ 16 * ‖c₂‖ * r ^ 2 := by
    rw [hc₂, norm_mul, norm_pow]
    have hpow :
        ‖q - a‖ ^ 2 ≤ (4 * r) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        hδhigh.le 2
    calc
      ‖q - a‖ ^ 2 * ‖c₂‖ ≤
          (4 * r) ^ 2 * ‖c₂‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg c₂)
      _ = 16 * ‖c₂‖ * r ^ 2 := by ring
  have hBterm :
      d.B * R⁻¹ ≤ 64 * B * r ^ 2 := by
    rw [hB₃]
    calc
      64 * B * r ^ 3 * R⁻¹ ≤
          64 * B * r ^ 3 * r⁻¹ :=
        mul_le_mul_of_nonneg_left hRinv (by positivity)
      _ = 64 * B * r ^ 2 := by
        field_simp [hr.ne']
  have hfirst :
      d.B * R⁻¹ + ‖d.c₂‖ ≤
        (64 * B + 16 * ‖c₂‖) * r ^ 2 := by
    calc
      d.B * R⁻¹ + ‖d.c₂‖ ≤
          64 * B * r ^ 2 +
            16 * ‖c₂‖ * r ^ 2 :=
        add_le_add hBterm hc₂norm
      _ = (64 * B + 16 * ‖c₂‖) * r ^ 2 := by
        ring
  have hsecond :
      d.L + ‖d.c₁‖ ≤
        (4 * scaleCapacityLinearConstant c₂ B ρ + 1) * r := by
    rw [hL]
    calc
      4 * scaleCapacityLinearConstant c₂ B ρ * r +
            ‖d.c₁‖
          ≤
          4 * scaleCapacityLinearConstant c₂ B ρ * r + r :=
        add_le_add le_rfl hc₁upper
      _ =
          (4 * scaleCapacityLinearConstant c₂ B ρ + 1) * r := by
        ring
  have hP :
      P ≤ scaleReplacementFarAux c₂ B ρ * r ^ 3 := by
    dsimp only [P]
    calc
      (d.B * R⁻¹ + ‖d.c₂‖) *
            (d.L + ‖d.c₁‖)
          ≤
          ((64 * B + 16 * ‖c₂‖) * r ^ 2) *
            ((4 * scaleCapacityLinearConstant c₂ B ρ + 1) * r) := by
        exact
          mul_le_mul hfirst hsecond
            (add_nonneg
              d.L_nonneg (norm_nonneg d.c₁))
            (mul_nonneg
              (add_nonneg
                (mul_nonneg (by positivity) hB)
                (mul_nonneg (by norm_num) (norm_nonneg c₂)))
              (sq_nonneg r))
      _ = scaleReplacementFarAux c₂ B ρ * r ^ 3 := by
        dsimp only [scaleReplacementFarAux]
        ring
  have hBbound :
      d.B ≤ 64 * B * r ^ 3 := by
    exact hB₃.le
  have hPnonneg : 0 ≤ P := by
    dsimp only [P]
    exact
      mul_nonneg
        (add_nonneg
          (mul_nonneg d.B_nonneg (inv_nonneg.mpr hRpos.le))
          (norm_nonneg d.c₂))
        (add_nonneg d.L_nonneg (norm_nonneg d.c₁))
  have hsum :
      α + β ≤
        scaleReplacementGlobalConstant c₂ *
          (r⁻¹ * ‖m₀‖ + r⁻¹ ^ 2 * ‖m₁‖) := by
    exact
      norm_boundedMoment_coefficients_scale_le
        hr c₂ d hδlow hδhigh hc₁ hc₂ m₀ m₁
  have hBP :
      d.B + P ≤
        (64 * B + scaleReplacementFarAux c₂ B ρ) *
          r ^ 3 := by
    calc
      d.B + P ≤
          64 * B * r ^ 3 +
            scaleReplacementFarAux c₂ B ρ * r ^ 3 :=
        add_le_add hBbound hP
      _ =
          (64 * B + scaleReplacementFarAux c₂ B ρ) *
            r ^ 3 := by
        ring
  change α * d.B + β * P ≤ _
  calc
    α * d.B + β * P ≤
        α * (d.B + P) + β * (d.B + P) := by
      apply add_le_add
      · exact
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right hPnonneg)
            (by positivity)
      · exact
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left d.B_nonneg)
            (by positivity)
    _ = (α + β) * (d.B + P) := by ring
    _ ≤
        (scaleReplacementGlobalConstant c₂ *
            (r⁻¹ * ‖m₀‖ + r⁻¹ ^ 2 * ‖m₁‖)) *
          ((64 * B + scaleReplacementFarAux c₂ B ρ) *
            r ^ 3) := by
      exact
        mul_le_mul hsum hBP
          (add_nonneg d.B_nonneg hPnonneg)
          (mul_nonneg
            (scaleReplacementGlobalConstant_nonneg c₂)
            (add_nonneg
              (mul_nonneg (inv_nonneg.mpr hr.le)
                (norm_nonneg m₀))
              (mul_nonneg
                (sq_nonneg r⁻¹) (norm_nonneg m₁))))
    _ =
        scaleReplacementFarConstant c₂ B ρ *
          (r ^ 2 * ‖m₀‖ + r * ‖m₁‖) := by
      dsimp only [scaleReplacementFarConstant]
      field_simp [hr.ne']

/-- Far from its pole, a scale-controlled bounded replacement differs from
the prescribed two-moment model by a uniform cubic kernel tail. -/
theorem norm_boundedMomentReplacement_sub_moments_scale_far_le
    {K : Set ℂ} [CompactSpace K]
    {q a : ℂ} {r R : ℝ} (hr : 0 < r)
    (c₂ : ℂ) (B ρ : ℝ) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (d : BoundedLaurentCapacity K a R)
    (hδlow : 2 * r < ‖q - a‖)
    (hδhigh : ‖q - a‖ < 4 * r)
    (hR : R = scaleCapacityRadius ρ * r)
    (hc₁ : d.c₁ = (q - a) * (1 / 100))
    (hc₂ : d.c₂ = (q - a) ^ 2 * c₂)
    (hL :
      d.L =
        4 * scaleCapacityLinearConstant c₂ B ρ * r)
    (hB₃ : d.B = 64 * B * r ^ 3)
    (m₀ m₁ : ℂ) (z : K)
    (hz : scaleCapacityRadius ρ * r ≤
      dist a (z : ℂ)) :
    ‖(boundedMomentReplacement d m₀ m₁ : C(K, ℂ)) z -
        ((a - (z : ℂ))⁻¹ * m₀ -
          (a - (z : ℂ))⁻¹ ^ 2 * m₁)‖ ≤
      scaleReplacementFarConstant c₂ B ρ *
        (r ^ 2 * ‖m₀‖ + r * ‖m₁‖) *
          (dist a (z : ℂ))⁻¹ ^ 3 := by
  have hRpos : 0 < R := by
    rw [hR]
    exact mul_pos (scaleCapacityRadius_pos ρ) hr
  have hzR : R ≤ dist a (z : ℂ) := by
    rwa [hR]
  exact
    (norm_boundedMomentReplacement_sub_moments_far_le
      d hRpos m₀ m₁ z hzR).trans
      (mul_le_mul_of_nonneg_right
        (boundedMomentReplacement_farCoefficient_scale_le
          hr c₂ B ρ hB hρ d hδlow hδhigh hR
            hc₁ hc₂ hL hB₃ m₀ m₁)
        (by positivity))

end Submission.Helpers
