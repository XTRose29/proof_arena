import Submission.FineLoewner

open Filter Function Metric Set

namespace Submission

noncomputable def seriesMulCoeff (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), a j * b (n - j)

noncomputable def seriesPowCoeff (a : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => seriesMulCoeff a (seriesPowCoeff a k) n

noncomputable def seriesUnitCoeff : ℕ → ℂ :=
  fun n ↦ if n = 1 then 1 else 0

lemma seriesPowCoeff_unit (k n : ℕ) :
    seriesPowCoeff seriesUnitCoeff k n = if n = k then 1 else 0 := by
  induction k generalizing n with
  | zero => simp [seriesPowCoeff]
  | succ k ih =>
      rw [seriesPowCoeff, seriesMulCoeff]
      simp_rw [ih]
      by_cases hnk : n = k + 1
      · subst n
        rw [Finset.sum_eq_single 1]
        · simp [seriesUnitCoeff]
        · intro j hj hj1
          simp [seriesUnitCoeff, hj1]
        · exact fun hnot ↦ (hnot (by simp)).elim
      · rw [Finset.sum_eq_zero]
        · simp [hnk]
        · intro j hj
          by_cases hj1 : j = 1
          · subst j
            have hnpos : 0 < n := by
              have := Finset.mem_range.mp hj
              omega
            have hne : n - 1 ≠ k := by omega
            simp [seriesUnitCoeff, hne]
          · simp [seriesUnitCoeff, hj1]

lemma seriesMulCoeff_unit_left (a : ℕ → ℂ) (n : ℕ) :
    seriesMulCoeff seriesUnitCoeff a n =
      if 0 < n then a (n - 1) else 0 := by
  unfold seriesMulCoeff
  by_cases hn : 0 < n
  · rw [Finset.sum_eq_single 1]
    · simp [seriesUnitCoeff, hn]
    · intro j hj hj1
      simp [seriesUnitCoeff, hj1]
    · exact fun hnot ↦ (hnot (by simp [hn])).elim
  · have hn0 : n = 0 := by omega
    subst n
    simp [seriesUnitCoeff]

lemma seriesMulCoeff_single_right (a : ℕ → ℂ) (k n : ℕ) :
    seriesMulCoeff a (fun d ↦ if d = k then 1 else 0) n =
      if k ≤ n then a (n - k) else 0 := by
  unfold seriesMulCoeff
  by_cases hkn : k ≤ n
  · rw [Finset.sum_eq_single (n - k)]
    · have heq : n - (n - k) = k := by omega
      rw [if_pos hkn]
      simp [heq]
    · intro j hj hjne
      have hjn : j ≤ n := by
        have := Finset.mem_range.mp hj
        omega
      have hne : n - j ≠ k := by omega
      simp [hne]
    · exact fun hnot ↦ (hnot (Finset.mem_range.mpr (by omega))).elim
  · rw [Finset.sum_eq_zero]
    · simp [hkn]
    · intro j hj
      have hne : n - j ≠ k := by
        have := Finset.mem_range.mp hj
        omega
      simp [hne]

noncomputable def canonicalTransitionCoeff
    (r omega : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => r
  | n + 2 => (1 - r ^ 2) * (-r) ^ n * omega ^ (n + 1)

noncomputable def canonicalTransitionSlopeCoeff
    (r omega : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 => -(1 + r) * (-r) ^ n * omega ^ (n + 1)

lemma canonicalTransitionCoeff_one (omega : ℂ) (n : ℕ) :
    canonicalTransitionCoeff 1 omega n = seriesUnitCoeff n := by
  rcases n with (_ | _ | n) <;>
    simp [canonicalTransitionCoeff, seriesUnitCoeff]

lemma canonicalTransitionCoeff_sub_one (r omega : ℂ) (n : ℕ) :
    canonicalTransitionCoeff r omega n - seriesUnitCoeff n =
      (r - 1) * canonicalTransitionSlopeCoeff r omega n := by
  rcases n with (_ | _ | n)
  · simp [canonicalTransitionCoeff, canonicalTransitionSlopeCoeff,
      seriesUnitCoeff]
  · simp [canonicalTransitionCoeff, canonicalTransitionSlopeCoeff,
      seriesUnitCoeff]
  · simp [canonicalTransitionCoeff, canonicalTransitionSlopeCoeff,
      seriesUnitCoeff]
    ring

lemma canonicalTransitionSlopeCoeff_one (omega : ℂ) (n : ℕ) :
    canonicalTransitionSlopeCoeff 1 omega n =
      if n = 0 then 0 else if n = 1 then 1 else
        2 * (-omega) ^ (n - 1) := by
  rcases n with (_ | _ | n)
  · simp [canonicalTransitionSlopeCoeff]
  · simp [canonicalTransitionSlopeCoeff]
  · simp [canonicalTransitionSlopeCoeff]
    ring

noncomputable def seriesPowSlopeCoeff (q qSlope : ℕ → ℂ) :
    ℕ → ℕ → ℂ
  | 0, _ => 0
  | k + 1, n =>
      seriesMulCoeff qSlope (seriesPowCoeff q k) n +
        seriesMulCoeff seriesUnitCoeff (seriesPowSlopeCoeff q qSlope k) n

lemma seriesPowCoeff_sub_unit_eq_mul_slope
    {q qSlope : ℕ → ℂ} {a : ℂ}
    (hq : ∀ n, q n - seriesUnitCoeff n = a * qSlope n) :
    ∀ k n, seriesPowCoeff q k n - seriesPowCoeff seriesUnitCoeff k n =
      a * seriesPowSlopeCoeff q qSlope k n := by
  intro k
  induction k with
  | zero =>
      intro n
      simp [seriesPowCoeff, seriesPowSlopeCoeff]
  | succ k ih =>
      intro n
      simp only [seriesPowCoeff, seriesPowSlopeCoeff, seriesMulCoeff]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hqj : q j = seriesUnitCoeff j + a * qSlope j := by
        linear_combination hq j
      have hpow : seriesPowCoeff q k (n - j) =
          seriesPowCoeff seriesUnitCoeff k (n - j) +
            a * seriesPowSlopeCoeff q qSlope k (n - j) := by
        linear_combination ih (n - j)
      rw [hqj, hpow]
      ring

lemma seriesPowSlopeCoeff_one (qSlope : ℕ → ℂ) (k n : ℕ) :
    seriesPowSlopeCoeff seriesUnitCoeff qSlope k n =
      if k = 0 then 0 else if k ≤ n + 1 then
        (k : ℂ) * qSlope (n - (k - 1)) else 0 := by
  induction k generalizing n with
  | zero => simp [seriesPowSlopeCoeff]
  | succ k ih =>
      rw [seriesPowSlopeCoeff]
      have hpow : seriesPowCoeff seriesUnitCoeff k =
          fun d ↦ if d = k then 1 else 0 := by
        funext d
        exact seriesPowCoeff_unit k d
      have hslope : seriesPowSlopeCoeff seriesUnitCoeff qSlope k =
          fun d ↦ if k = 0 then 0 else if k ≤ d + 1 then
            (k : ℂ) * qSlope (d - (k - 1)) else 0 := by
        funext d
        exact ih d
      rw [hpow, hslope, seriesMulCoeff_single_right,
        seriesMulCoeff_unit_left]
      by_cases hkn : k + 1 ≤ n + 1
      · have hkn' : k ≤ n := by omega
        by_cases hk0 : k = 0
        · subst k
          simp
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          have hnpos : 0 < n := lt_of_lt_of_le hkpos hkn'
          have hcond : k ≤ n - 1 + 1 := by omega
          have hsub : n - 1 - (k - 1) = n - k := by omega
          simp only [Nat.succ_ne_zero, if_false, hkn, if_true, hkn', hnpos,
            hk0, hcond, hsub]
          push_cast
          ring
      · have hnk : n < k := by omega
        have hk0 : k ≠ 0 := by omega
        by_cases hn : 0 < n
        · have hkn' : ¬k ≤ n := by omega
          have hcond : ¬k ≤ n - 1 + 1 := by omega
          simp [hkn, hkn', hk0, hn, hcond]
        · have hn0 : n = 0 := by omega
          subst n
          simp [hkn, hk0]

noncomputable def inversePowerSum (r : ℂ) (m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range m, r⁻¹ ^ (j + 1)

noncomputable def forwardPowerSum (r : ℂ) (m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range m, r ^ j

lemma inverse_sub_forward_pow_eq (r : ℂ) (hr : r ≠ 0) (m : ℕ) :
    r⁻¹ ^ m - r ^ m =
      (r - 1) * (-(inversePowerSum r m + forwardPowerSum r m)) := by
  induction m with
  | zero => simp [inversePowerSum, forwardPowerSum]
  | succ m ih =>
      rw [inversePowerSum, forwardPowerSum, Finset.sum_range_succ,
        Finset.sum_range_succ, pow_succ, pow_succ]
      rw [inversePowerSum, forwardPowerSum] at ih
      calc
        r⁻¹ ^ m * r⁻¹ - r ^ m * r =
            (r⁻¹ ^ m - r ^ m) +
              (r - 1) * (-(r⁻¹ ^ (m + 1) + r ^ m)) := by
          have hcancel : r * r⁻¹ ^ (m + 1) = r⁻¹ ^ m := by
            rw [pow_succ]
            calc
              r * (r⁻¹ ^ m * r⁻¹) = r⁻¹ ^ m * (r * r⁻¹) := by ring
              _ = r⁻¹ ^ m := by rw [mul_inv_cancel₀ hr, mul_one]
          linear_combination hcancel
        _ = _ := by rw [ih]; ring

noncomputable def canonicalLogFactorCoeff
    (r omega : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 =>
      (-1 : ℂ) ^ (n + 2) * omega ^ (n + 1) *
        (r⁻¹ ^ (n + 1) - r ^ (n + 1)) /
          (2 * ((n + 1 : ℕ) : ℂ))

noncomputable def canonicalLogFactorSlope
    (r omega : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 =>
      (-1 : ℂ) ^ (n + 2) * omega ^ (n + 1) *
        (-(inversePowerSum r (n + 1) + forwardPowerSum r (n + 1))) /
          (2 * ((n + 1 : ℕ) : ℂ))

lemma canonicalLogFactorCoeff_eq_mul_slope
    (r omega : ℂ) (hr : r ≠ 0) (n : ℕ) :
    canonicalLogFactorCoeff r omega n =
      (r - 1) * canonicalLogFactorSlope r omega n := by
  rcases n with _ | n
  · simp [canonicalLogFactorCoeff, canonicalLogFactorSlope]
  · simp only [canonicalLogFactorCoeff, canonicalLogFactorSlope]
    rw [inverse_sub_forward_pow_eq r hr]
    ring

lemma canonicalLogFactorCoeff_one (omega : ℂ) (n : ℕ) :
    canonicalLogFactorCoeff 1 omega n = 0 := by
  rcases n with _ | n <;> simp [canonicalLogFactorCoeff]

lemma canonicalLogFactorSlope_one (omega : ℂ) (n : ℕ) :
    canonicalLogFactorSlope 1 omega n =
      if n = 0 then 0 else (-omega) ^ n := by
  rcases n with _ | n
  · simp [canonicalLogFactorSlope]
  · simp only [canonicalLogFactorSlope, if_false, Nat.succ_ne_zero,
      inversePowerSum, forwardPowerSum, inv_one, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
    ring

noncomputable def canonicalLoewnerCoeff
    (c : ℕ → ℂ) (r omega : ℂ) (n : ℕ) : ℂ :=
  (∑ k ∈ Finset.range (n + 1),
      c k * seriesPowCoeff (canonicalTransitionCoeff r omega) k n) +
    canonicalLogFactorCoeff r omega n

noncomputable def canonicalLoewnerSlope
    (c : ℕ → ℂ) (r omega : ℂ) (n : ℕ) : ℂ :=
  (∑ k ∈ Finset.range (n + 1),
      c k * seriesPowSlopeCoeff
        (canonicalTransitionCoeff r omega)
        (canonicalTransitionSlopeCoeff r omega) k n) +
    canonicalLogFactorSlope r omega n

lemma canonicalLoewnerCoeff_one (c : ℕ → ℂ) (omega : ℂ) (n : ℕ) :
    canonicalLoewnerCoeff c 1 omega n = c n := by
  unfold canonicalLoewnerCoeff
  rw [canonicalLogFactorCoeff_one]
  simp only [add_zero]
  have htransition : canonicalTransitionCoeff 1 omega = seriesUnitCoeff := by
    funext d
    exact canonicalTransitionCoeff_one omega d
  rw [htransition, Finset.sum_eq_single n]
  · rw [seriesPowCoeff_unit]
    simp
  · intro k hk hkn
    rw [seriesPowCoeff_unit]
    simp [Ne.symm hkn]
  · exact fun hnot ↦ (hnot (by simp)).elim

lemma canonicalLoewnerCoeff_sub_eq_mul_slope
    (c : ℕ → ℂ) (r omega : ℂ) (hr : r ≠ 0) (n : ℕ) :
    canonicalLoewnerCoeff c r omega n - c n =
      (r - 1) * canonicalLoewnerSlope c r omega n := by
  have hpow (k : ℕ) := seriesPowCoeff_sub_unit_eq_mul_slope
    (a := r - 1) (canonicalTransitionCoeff_sub_one r omega) k n
  have htransition : canonicalTransitionCoeff 1 omega = seriesUnitCoeff := by
    funext d
    exact canonicalTransitionCoeff_one omega d
  rw [← canonicalLoewnerCoeff_one c omega n]
  unfold canonicalLoewnerCoeff canonicalLoewnerSlope
  rw [canonicalLogFactorCoeff_eq_mul_slope r omega hr]
  simp only [canonicalLogFactorCoeff_one, add_zero]
  rw [htransition]
  calc
    (∑ k ∈ Finset.range (n + 1),
          c k * seriesPowCoeff (canonicalTransitionCoeff r omega) k n) +
          (r - 1) * canonicalLogFactorSlope r omega n -
        ∑ k ∈ Finset.range (n + 1),
          c k * seriesPowCoeff seriesUnitCoeff k n =
        ((∑ k ∈ Finset.range (n + 1),
            c k * seriesPowCoeff (canonicalTransitionCoeff r omega) k n) -
          ∑ k ∈ Finset.range (n + 1),
            c k * seriesPowCoeff seriesUnitCoeff k n) +
          (r - 1) * canonicalLogFactorSlope r omega n := by ring
    _ = (r - 1) *
          (∑ k ∈ Finset.range (n + 1),
            c k * seriesPowSlopeCoeff
              (canonicalTransitionCoeff r omega)
              (canonicalTransitionSlopeCoeff r omega) k n) +
          (r - 1) * canonicalLogFactorSlope r omega n := by
      congr 1
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hpow' :
          seriesPowCoeff (canonicalTransitionCoeff r omega) k n =
            seriesPowCoeff seriesUnitCoeff k n +
              (r - 1) * seriesPowSlopeCoeff
                (canonicalTransitionCoeff r omega)
                (canonicalTransitionSlopeCoeff r omega) k n := by
        linear_combination hpow k
      rw [hpow']
      ring
    _ = (r - 1) *
        ((∑ k ∈ Finset.range (n + 1),
          c k * seriesPowSlopeCoeff
            (canonicalTransitionCoeff r omega)
            (canonicalTransitionSlopeCoeff r omega) k n) +
          canonicalLogFactorSlope r omega n) := by ring

lemma sum_seriesPowSlopeCoeff_one
    (c qSlope : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range (n + 1),
      c k * seriesPowSlopeCoeff seriesUnitCoeff qSlope k n) =
      ((n : ℕ) : ℂ) * c n * qSlope 1 +
        ∑ j ∈ Finset.range (n - 1),
          ((j + 1 : ℕ) : ℂ) * c (j + 1) * qSlope (n - j) := by
  rcases n with _ | m
  · omega
  · rw [Finset.sum_range_succ]
    have hprefix :
        (∑ k ∈ Finset.range (m + 1),
          c k * seriesPowSlopeCoeff seriesUnitCoeff qSlope k (m + 1)) =
          ∑ j ∈ Finset.range m,
            ((j + 1 : ℕ) : ℂ) * c (j + 1) * qSlope (m + 1 - j) := by
      rw [Finset.sum_range_succ']
      simp only [seriesPowSlopeCoeff_one, if_true, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hle : j + 1 ≤ m + 1 + 1 := by omega
      simp only [Nat.succ_ne_zero, if_false, hle, if_true]
      rw [show m + 1 - (j + 1 - 1) = m + 1 - j by omega]
      ring
    rw [hprefix, seriesPowSlopeCoeff_one]
    simp only [Nat.succ_ne_zero, if_false, Nat.le_add_right, if_true,
      Nat.add_sub_cancel]
    rw [show m + 1 - m = 1 by omega]
    ring

lemma canonicalLoewnerSlope_one
    (c : ℕ → ℂ) {omega : ℂ} (homega : omega ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    canonicalLoewnerSlope c 1 omega n =
      drivenLoewnerVelocity c (-omega) n := by
  unfold canonicalLoewnerSlope
  have htransition : canonicalTransitionCoeff 1 omega = seriesUnitCoeff := by
    funext d
    exact canonicalTransitionCoeff_one omega d
  have hslope : canonicalTransitionSlopeCoeff 1 omega =
      fun d ↦ if d = 0 then 0 else if d = 1 then 1 else
        2 * (-omega) ^ (d - 1) := by
    funext d
    exact canonicalTransitionSlopeCoeff_one omega d
  rw [htransition, hslope, sum_seriesPowSlopeCoeff_one c _ hn,
    canonicalLogFactorSlope_one]
  rw [if_neg hn.ne']
  rcases n with _ | m
  · omega
  · rw [drivenLoewnerVelocity_succ (neg_ne_zero.mpr homega) m]
    simp only [Nat.succ_ne_zero, if_false, if_true, Nat.add_sub_cancel]
    have hsum :
        (∑ j ∈ Finset.range m,
          ((j + 1 : ℕ) : ℂ) * c (j + 1) *
            (if m + 1 - j = 0 then 0 else if m + 1 - j = 1 then 1
              else 2 * (-omega) ^ (m + 1 - j - 1))) =
          2 * ∑ j ∈ Finset.range m,
            ((j + 1 : ℕ) : ℂ) * c (j + 1) * (-omega) ^ (m - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hd0 : m + 1 - j ≠ 0 := by omega
      have hd1 : m + 1 - j ≠ 1 := by omega
      simp only [hd0, hd1, if_false]
      rw [show m + 1 - j - 1 = m - j by omega]
      ring
    rw [hsum]
    ring

end Submission
