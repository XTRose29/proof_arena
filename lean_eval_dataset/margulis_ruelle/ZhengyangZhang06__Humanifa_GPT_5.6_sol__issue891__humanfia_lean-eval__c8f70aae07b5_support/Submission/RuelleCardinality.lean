import Submission.RuelleSingularCover

namespace Submission.Helpers

open LeanEval.Dynamics
open scoped Real

lemma card_singularIndexRange_real_le
    (A : EucPlane →L[ℝ] EucPlane) (i : Fin 2) :
    ((singularIndexRange A i).card : ℝ) ≤
      7 * max 1 (singularImageSize A i) := by
  let s := singularImageSize A i
  let z : ℤ := ⌈2 * s⌉
  have hs : 0 ≤ s := norm_nonneg _
  have hz : 0 ≤ z := by
    exact Int.ceil_nonneg (mul_nonneg (by norm_num) hs)
  have hceil : (z : ℝ) < 2 * s + 1 := by
    simpa [z] using Int.ceil_lt_add_one (2 * s)
  have hcard :
      ((singularIndexRange A i).card : ℝ) = 2 * (z : ℝ) + 1 := by
    rw [singularIndexRange, Int.card_Icc]
    change (((z + 1 - -z).toNat : ℕ) : ℝ) = 2 * (z : ℝ) + 1
    have hcast : ((z + 1 - -z).toNat : ℤ) = 2 * z + 1 := by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ z + 1 - -z)]
      ring
    exact_mod_cast hcast
  rw [hcard]
  by_cases hsone : s ≤ 1
  · rw [max_eq_left hsone]
    linarith
  · rw [max_eq_right (le_of_not_ge hsone)]
    nlinarith

lemma card_singularIndexBox_real_le
    (A : EucPlane →L[ℝ] EucPlane) :
    ((singularIndexBox A).card : ℝ) ≤
      49 * max 1 (singularImageSize A 0) *
        max 1 (singularImageSize A 1) := by
  rw [singularIndexBox, Finset.product_eq_sprod, Finset.card_product]
  push_cast
  calc
    ((singularIndexRange A 0).card : ℝ) *
        ((singularIndexRange A 1).card : ℝ) ≤
        (7 * max 1 (singularImageSize A 0)) *
          (7 * max 1 (singularImageSize A 1)) := by
      gcongr
      · exact card_singularIndexRange_real_le A 0
      · exact card_singularIndexRange_real_le A 1
    _ = 49 * max 1 (singularImageSize A 0) *
        max 1 (singularImageSize A 1) := by ring

lemma card_singularTargetIndexCover_real_le
    (c : EucPlane) (A : EucPlane →L[ℝ] EucPlane) (r : ℝ) :
    ((singularTargetIndexCover c A r).card : ℝ) ≤
      3969 * max 1 (singularImageSize A 0) *
        max 1 (singularImageSize A 1) := by
  have hcover : ((singularTargetIndexCover c A r).card : ℝ) ≤
      81 * ((singularIndexBox A).card : ℝ) := by
    exact_mod_cast card_singularTargetIndexCover_le c A r
  calc
    ((singularTargetIndexCover c A r).card : ℝ) ≤
        81 * ((singularIndexBox A).card : ℝ) := hcover
    _ ≤ 81 * (49 * max 1 (singularImageSize A 0) *
        max 1 (singularImageSize A 1)) := by
      gcongr
      exact card_singularIndexBox_real_le A
    _ = 3969 * max 1 (singularImageSize A 0) *
        max 1 (singularImageSize A 1) := by ring

noncomputable def singularTargetCardBound
    (c : EucPlane) (A : EucPlane →L[ℝ] EucPlane) (r : ℝ) : ℕ :=
  max 1 (singularTargetIndexCover c A r).card

lemma singularTargetCardBound_pos
    (c : EucPlane) (A : EucPlane →L[ℝ] EucPlane) (r : ℝ) :
    0 < singularTargetCardBound c A r := by
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

lemma card_singularTargetIndexCover_le_bound
    (c : EucPlane) (A : EucPlane →L[ℝ] EucPlane) (r : ℝ) :
    (singularTargetIndexCover c A r).card ≤
      singularTargetCardBound c A r := by
  exact Nat.le_max_right _ _

lemma singularTargetCardBound_real_le
    (c : EucPlane) (A : EucPlane →L[ℝ] EucPlane) (r : ℝ) :
    (singularTargetCardBound c A r : ℝ) ≤
      3969 * max 1 (singularImageSize A 0) *
        max 1 (singularImageSize A 1) := by
  let R := 3969 * max 1 (singularImageSize A 0) *
    max 1 (singularImageSize A 1)
  have hRone : 1 ≤ R := by
    dsimp [R]
    have h0 : 1 ≤ max 1 (singularImageSize A 0) := le_max_left _ _
    have h1 : 1 ≤ max 1 (singularImageSize A 1) := le_max_left _ _
    nlinarith
  have hRcard : ((singularTargetIndexCover c A r).card : ℝ) ≤ R := by
    exact card_singularTargetIndexCover_real_le c A r
  simpa [singularTargetCardBound, R, Nat.cast_max] using
    (max_le hRone hRcard)

lemma log_singularTargetCardBound_le
    (c : EucPlane) (A : EucPlane →L[ℝ] EucPlane) (r : ℝ) :
    Real.log (singularTargetCardBound c A r) ≤
      Real.log 3969 + Real.posLog (singularImageSize A 0) +
        Real.posLog (singularImageSize A 1) := by
  have hNpos : (0 : ℝ) < singularTargetCardBound c A r := by
    exact_mod_cast singularTargetCardBound_pos c A r
  have h0pos : 0 < max 1 (singularImageSize A 0) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h1pos : 0 < max 1 (singularImageSize A 1) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  calc
    Real.log (singularTargetCardBound c A r) ≤
        Real.log (3969 * max 1 (singularImageSize A 0) *
          max 1 (singularImageSize A 1)) :=
      Real.log_le_log hNpos (singularTargetCardBound_real_le c A r)
    _ = Real.log 3969 + Real.log (max 1 (singularImageSize A 0)) +
        Real.log (max 1 (singularImageSize A 1)) := by
      rw [Real.log_mul (mul_ne_zero (by norm_num) h0pos.ne') h1pos.ne',
        Real.log_mul (by norm_num : (3969 : ℝ) ≠ 0) h0pos.ne']
    _ = Real.log 3969 + Real.posLog (singularImageSize A 0) +
        Real.posLog (singularImageSize A 1) := by
      have hs0 : 0 ≤ singularImageSize A 0 := norm_nonneg _
      have hs1 : 0 ≤ singularImageSize A 1 := norm_nonneg _
      rw [← Real.posLog_eq_log_max_one hs0,
        ← Real.posLog_eq_log_max_one hs1]

end Submission.Helpers
