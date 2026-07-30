import Submission.RuelleGrid
import Submission.DerivativeDistortion
import Submission.PlaneSingularGeometry

namespace Submission.Helpers

open LeanEval.Dynamics

noncomputable def singularImageSize
    (A : EucPlane →L[ℝ] EucPlane) (i : Fin 2) : ℝ :=
  ‖A (planeSingularBasis A i)‖

noncomputable def singularImageDirection
    (A : EucPlane →L[ℝ] EucPlane) (i : Fin 2) : EucPlane :=
  (singularImageSize A i)⁻¹ • A (planeSingularBasis A i)

lemma singularImageSize_pos
    (A : EucPlane →L[ℝ] EucPlane) (hA : A.IsInvertible) (i : Fin 2) :
    0 < singularImageSize A i := by
  apply norm_pos_iff.mpr
  intro hzero
  have hbzero : planeSingularBasis A i = 0 := by
    apply hA.injective
    simpa using hzero
  have hbnorm := planeSingularBasis_norm A i
  rw [hbzero, norm_zero] at hbnorm
  norm_num at hbnorm

lemma norm_singularImageDirection
    (A : EucPlane →L[ℝ] EucPlane) (hA : A.IsInvertible) (i : Fin 2) :
    ‖singularImageDirection A i‖ = 1 := by
  have hs := singularImageSize_pos A hA i
  rw [singularImageDirection, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hs]
  exact inv_mul_cancel₀ hs.ne'

noncomputable def singularRoundIndex
    (A : EucPlane →L[ℝ] EucPlane) (r : ℝ) (v : EucPlane) : ℤ × ℤ :=
  (⌊((planeSingularBasis A).repr v).ofLp 0 *
      singularImageSize A 0 / r⌋,
   ⌊((planeSingularBasis A).repr v).ofLp 1 *
      singularImageSize A 1 / r⌋)

noncomputable def singularIndexRange
    (A : EucPlane →L[ℝ] EucPlane) (i : Fin 2) : Finset ℤ :=
  Finset.Icc (-⌈2 * singularImageSize A i⌉)
    ⌈2 * singularImageSize A i⌉

noncomputable def singularIndexBox
    (A : EucPlane →L[ℝ] EucPlane) : Finset (ℤ × ℤ) :=
  (singularIndexRange A 0).product (singularIndexRange A 1)

lemma abs_singular_repr_le_norm
    (A : EucPlane →L[ℝ] EucPlane) (v : EucPlane) (i : Fin 2) :
    |((planeSingularBasis A).repr v).ofLp i| ≤ ‖v‖ := by
  calc
    |((planeSingularBasis A).repr v).ofLp i| =
        ‖((planeSingularBasis A).repr v).ofLp i‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ‖(planeSingularBasis A).repr v‖ :=
      PiLp.norm_apply_le _ i
    _ = ‖v‖ := (planeSingularBasis A).repr.norm_map v

lemma singularRoundIndex_mem
    (A : EucPlane →L[ℝ] EucPlane) {r : ℝ} (hr : 0 < r)
    {v : EucPlane} (hv : ‖v‖ < 2 * r) :
    singularRoundIndex A r v ∈ singularIndexBox A := by
  rw [singularIndexBox, Finset.product_eq_sprod, Finset.mem_product]
  simp only [singularRoundIndex]
  constructor
  · rw [singularIndexRange, Finset.mem_Icc]
    let a := ((planeSingularBasis A).repr v).ofLp 0
    let s := singularImageSize A 0
    have ha : |a| < 2 * r :=
      (abs_singular_repr_le_norm A v 0).trans_lt hv
    have hs : 0 ≤ s := norm_nonneg _
    have ht_lower : -(2 * s) ≤ a * s / r := by
      have ha_lower : -(2 * r) < a := (abs_lt.mp ha).1
      have : -(2 * r) * s ≤ a * s :=
        mul_le_mul_of_nonneg_right ha_lower.le hs
      have hr' : 0 < r := hr
      rw [div_eq_mul_inv]
      have hinv : 0 < r⁻¹ := inv_pos.mpr hr'
      calc
        -(2 * s) = (-(2 * r) * s) * r⁻¹ := by
          field_simp [hr.ne']
        _ ≤ (a * s) * r⁻¹ := mul_le_mul_of_nonneg_right this hinv.le
        _ ≤ a * s / r := by rw [div_eq_mul_inv]
    have ht_upper : a * s / r ≤ 2 * s := by
      have ha_upper : a < 2 * r := (abs_lt.mp ha).2
      have : a * s ≤ (2 * r) * s :=
        mul_le_mul_of_nonneg_right ha_upper.le hs
      have hinv : 0 < r⁻¹ := inv_pos.mpr hr
      calc
        a * s / r = (a * s) * r⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ ((2 * r) * s) * r⁻¹ :=
          mul_le_mul_of_nonneg_right this hinv.le
        _ = 2 * s := by
          field_simp [hr.ne']
    constructor
    · rw [Int.le_floor]
      have hceil : (2 * s : ℝ) ≤ (⌈2 * s⌉ : ℤ) := Int.le_ceil _
      push_cast at hceil ⊢
      linarith
    · have hceil : (2 * s : ℝ) ≤ (⌈2 * s⌉ : ℤ) := Int.le_ceil _
      rw [← Int.lt_add_one_iff, Int.floor_lt]
      push_cast at hceil ⊢
      linarith
  · rw [singularIndexRange, Finset.mem_Icc]
    let a := ((planeSingularBasis A).repr v).ofLp 1
    let s := singularImageSize A 1
    have ha : |a| < 2 * r :=
      (abs_singular_repr_le_norm A v 1).trans_lt hv
    have hs : 0 ≤ s := norm_nonneg _
    have ht_lower : -(2 * s) ≤ a * s / r := by
      have ha_lower : -(2 * r) < a := (abs_lt.mp ha).1
      have hmul : -(2 * r) * s ≤ a * s :=
        mul_le_mul_of_nonneg_right ha_lower.le hs
      have hinv : 0 < r⁻¹ := inv_pos.mpr hr
      calc
        -(2 * s) = (-(2 * r) * s) * r⁻¹ := by
          field_simp [hr.ne']
        _ ≤ (a * s) * r⁻¹ :=
          mul_le_mul_of_nonneg_right hmul hinv.le
        _ = a * s / r := by rw [div_eq_mul_inv]
    have ht_upper : a * s / r ≤ 2 * s := by
      have ha_upper : a < 2 * r := (abs_lt.mp ha).2
      have hmul : a * s ≤ (2 * r) * s :=
        mul_le_mul_of_nonneg_right ha_upper.le hs
      have hinv : 0 < r⁻¹ := inv_pos.mpr hr
      calc
        a * s / r = (a * s) * r⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ ((2 * r) * s) * r⁻¹ :=
          mul_le_mul_of_nonneg_right hmul hinv.le
        _ = 2 * s := by
          field_simp [hr.ne']
    constructor
    · rw [Int.le_floor]
      have hceil : (2 * s : ℝ) ≤ (⌈2 * s⌉ : ℤ) := Int.le_ceil _
      push_cast at hceil ⊢
      linarith
    · have hceil : (2 * s : ℝ) ≤ (⌈2 * s⌉ : ℤ) := Int.le_ceil _
      rw [← Int.lt_add_one_iff, Int.floor_lt]
      push_cast at hceil ⊢
      linarith

noncomputable def singularApproximationCenter
    (c : EucPlane) (A : EucPlane →L[ℝ] EucPlane) (r : ℝ)
    (k : ℤ × ℤ) : EucPlane :=
  c +
    (r * (k.1 : ℝ)) • singularImageDirection A 0 +
    (r * (k.2 : ℝ)) • singularImageDirection A 1

lemma norm_linear_sub_singularApproximationCenter_lt
    (A : EucPlane →L[ℝ] EucPlane) (hA : A.IsInvertible)
    {r : ℝ} (hr : 0 < r) (v : EucPlane) :
    ‖A v -
      ((r * ((singularRoundIndex A r v).1 : ℝ)) •
          singularImageDirection A 0 +
       (r * ((singularRoundIndex A r v).2 : ℝ)) •
          singularImageDirection A 1)‖ < 2 * r := by
  let b := planeSingularBasis A
  let a0 := (b.repr v).ofLp 0
  let a1 := (b.repr v).ofLp 1
  let s0 := singularImageSize A 0
  let s1 := singularImageSize A 1
  let k0 : ℤ := ⌊a0 * s0 / r⌋
  let k1 : ℤ := ⌊a1 * s1 / r⌋
  have hs0 := singularImageSize_pos A hA 0
  have hs1 := singularImageSize_pos A hA 1
  have hk0low : (k0 : ℝ) ≤ a0 * s0 / r := Int.floor_le _
  have hk0high : a0 * s0 / r < (k0 : ℝ) + 1 := by
    simp [k0]
  have hk1low : (k1 : ℝ) ≤ a1 * s1 / r := Int.floor_le _
  have hk1high : a1 * s1 / r < (k1 : ℝ) + 1 := by
    simp [k1]
  have herr0 : |a0 * s0 - r * (k0 : ℝ)| < r := by
    rw [abs_lt]
    constructor
    · have hquot : (k0 : ℝ) * r ≤ a0 * s0 :=
        (le_div_iff₀ hr).mp hk0low
      have h : r * (k0 : ℝ) ≤ a0 * s0 := by
        simpa [mul_comm] using hquot
      linarith
    · have h : (a0 * s0 - r * (k0 : ℝ)) / r < 1 := by
        rw [sub_div, mul_div_cancel_left₀ _ hr.ne']
        linarith
      simpa using (div_lt_iff₀ hr).mp h
  have herr1 : |a1 * s1 - r * (k1 : ℝ)| < r := by
    rw [abs_lt]
    constructor
    · have hquot : (k1 : ℝ) * r ≤ a1 * s1 :=
        (le_div_iff₀ hr).mp hk1low
      have h : r * (k1 : ℝ) ≤ a1 * s1 := by
        simpa [mul_comm] using hquot
      linarith
    · have h : (a1 * s1 - r * (k1 : ℝ)) / r < 1 := by
        rw [sub_div, mul_div_cancel_left₀ _ hr.ne']
        linarith
      simpa using (div_lt_iff₀ hr).mp h
  have hdecomp : A v =
      a0 • A (b 0) + a1 • A (b 1) := by
    have hvdecomp : v = a0 • b 0 + a1 • b 1 := by
      simpa [Fin.sum_univ_two, a0, a1] using (b.sum_repr v).symm
    calc
      A v = A (a0 • b 0 + a1 • b 1) := congrArg A hvdecomp
      _ = a0 • A (b 0) + a1 • A (b 1) := by
        rw [map_add, map_smul, map_smul]
  have hdir0 : A (b 0) = s0 • singularImageDirection A 0 := by
    rw [singularImageDirection, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  have hdir1 : A (b 1) = s1 • singularImageDirection A 1 := by
    rw [singularImageDirection, smul_smul, mul_inv_cancel₀ hs1.ne', one_smul]
  have heq :
      A v -
        ((r * (k0 : ℝ)) • singularImageDirection A 0 +
         (r * (k1 : ℝ)) • singularImageDirection A 1) =
      (a0 * s0 - r * (k0 : ℝ)) • singularImageDirection A 0 +
        (a1 * s1 - r * (k1 : ℝ)) • singularImageDirection A 1 := by
    rw [hdecomp, hdir0, hdir1]
    simp only [smul_smul]
    module
  rw [show singularRoundIndex A r v = (k0, k1) by rfl, heq]
  calc
    ‖(a0 * s0 - r * (k0 : ℝ)) • singularImageDirection A 0 +
        (a1 * s1 - r * (k1 : ℝ)) • singularImageDirection A 1‖ ≤
        ‖(a0 * s0 - r * (k0 : ℝ)) • singularImageDirection A 0‖ +
          ‖(a1 * s1 - r * (k1 : ℝ)) • singularImageDirection A 1‖ :=
      norm_add_le _ _
    _ = |a0 * s0 - r * (k0 : ℝ)| +
          |a1 * s1 - r * (k1 : ℝ)| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        norm_singularImageDirection A hA,
        norm_singularImageDirection A hA]
      ring
    _ < 2 * r := by linarith

noncomputable def nearbySquareGridIndices
    (r : ℝ) (c : EucPlane) (L : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc ((squareGridIndex r c).1 - L)
      ((squareGridIndex r c).1 + L)).product
    (Finset.Icc ((squareGridIndex r c).2 - L)
      ((squareGridIndex r c).2 + L))

lemma squareGridIndex_mem_nearby_of_norm_sub_lt
    {r : ℝ} (hr : 0 < r) {x c : EucPlane}
    (hxc : ‖x - c‖ < 3 * r) :
    squareGridIndex r x ∈ nearbySquareGridIndices r c 4 := by
  rw [nearbySquareGridIndices, Finset.product_eq_sprod,
    Finset.mem_product]
  simp only [squareGridIndex]
  have hcoord (i : Fin 2) : |x.ofLp i - c.ofLp i| < 3 * r := by
    calc
      |x.ofLp i - c.ofLp i| = ‖(x - c).ofLp i‖ := by
        rw [PiLp.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖x - c‖ := PiLp.norm_apply_le _ i
      _ < 3 * r := hxc
  constructor
  · rw [Finset.mem_Icc]
    have h := hcoord 0
    have hclow : ((⌊c.ofLp 0 / r⌋ : ℤ) : ℝ) ≤ c.ofLp 0 / r :=
      Int.floor_le _
    have hchigh : c.ofLp 0 / r <
        ((⌊c.ofLp 0 / r⌋ : ℤ) : ℝ) + 1 := by
      exact Int.lt_floor_add_one _
    constructor
    · rw [Int.le_floor]
      push_cast
      rw [abs_lt] at h
      have hscaled : -3 < (x.ofLp 0 - c.ofLp 0) / r := by
        apply (lt_div_iff₀ hr).2
        linarith
      rw [sub_div] at hscaled
      linarith
    · rw [← Int.lt_add_one_iff, Int.floor_lt]
      push_cast
      rw [abs_lt] at h
      have hscaled : (x.ofLp 0 - c.ofLp 0) / r < 3 := by
        apply (div_lt_iff₀ hr).2
        linarith
      rw [sub_div] at hscaled
      linarith
  · rw [Finset.mem_Icc]
    have h := hcoord 1
    have hclow : ((⌊c.ofLp 1 / r⌋ : ℤ) : ℝ) ≤ c.ofLp 1 / r :=
      Int.floor_le _
    have hchigh : c.ofLp 1 / r <
        ((⌊c.ofLp 1 / r⌋ : ℤ) : ℝ) + 1 := by
      exact Int.lt_floor_add_one _
    constructor
    · rw [Int.le_floor]
      push_cast
      rw [abs_lt] at h
      have hscaled : -3 < (x.ofLp 1 - c.ofLp 1) / r := by
        apply (lt_div_iff₀ hr).2
        linarith
      rw [sub_div] at hscaled
      linarith
    · rw [← Int.lt_add_one_iff, Int.floor_lt]
      push_cast
      rw [abs_lt] at h
      have hscaled : (x.ofLp 1 - c.ofLp 1) / r < 3 := by
        apply (div_lt_iff₀ hr).2
        linarith
      rw [sub_div] at hscaled
      linarith

lemma card_nearbySquareGridIndices_four
    (r : ℝ) (c : EucPlane) :
    (nearbySquareGridIndices r c 4).card = 81 := by
  have hcard (z : ℤ) : (Finset.Icc (z - 4) (z + 4)).card = 9 := by
    rw [Int.card_Icc]
    have heq : z + 4 + 1 - (z - 4) = 9 := by ring
    rw [heq]
    decide
  rw [nearbySquareGridIndices, Finset.product_eq_sprod,
    Finset.card_product, hcard, hcard]

noncomputable def singularTargetIndexCover
    (c : EucPlane) (A : EucPlane →L[ℝ] EucPlane) (r : ℝ) :
    Finset (ℤ × ℤ) :=
  (singularIndexBox A).biUnion fun k =>
    nearbySquareGridIndices r (singularApproximationCenter c A r k) 4

lemma card_singularTargetIndexCover_le
    (c : EucPlane) (A : EucPlane →L[ℝ] EucPlane) (r : ℝ) :
    (singularTargetIndexCover c A r).card ≤
      81 * (singularIndexBox A).card := by
  calc
    (singularTargetIndexCover c A r).card ≤
        ∑ k ∈ singularIndexBox A,
          (nearbySquareGridIndices r
            (singularApproximationCenter c A r k) 4).card := by
      exact Finset.card_biUnion_le
    _ = 81 * (singularIndexBox A).card := by
      simp [card_nearbySquareGridIndices_four, Nat.mul_comm]

lemma squareGridIndex_image_mem_singularTargetIndexCover
    (S : EucPlane → EucPlane) (hS_smooth : ContDiff ℝ 2 S)
    {C : Set EucPlane} (hC_convex : Convex ℝ C)
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hB : ∀ z ∈ C, ∀ w ∈ C,
      ‖fderiv ℝ S z - fderiv ℝ S w‖ ≤ B * dist z w)
    {r : ℝ} (hr : 0 < r) (hsmall : 4 * B * r ≤ 1)
    {x y : EucPlane} (hx : x ∈ C) (hy : y ∈ C)
    (hcell : squareGridIndex r x = squareGridIndex r y)
    (hA : (fderiv ℝ S x).IsInvertible) :
    squareGridIndex r (S y) ∈
      singularTargetIndexCover (S x) (fderiv ℝ S x) r := by
  let A := fderiv ℝ S x
  let v := y - x
  let k := singularRoundIndex A r v
  have hv : ‖v‖ < 2 * r :=
    norm_sub_lt_two_mul_of_squareGridIndex_eq hr hcell.symm
  have hk : k ∈ singularIndexBox A :=
    singularRoundIndex_mem A hr hv
  have hlinear :=
    norm_linear_sub_singularApproximationCenter_lt A hA hr v
  have hremainder := norm_image_sub_linearization_le
    S hS_smooth hC_convex hB_nonneg hB hx hy
  have hremainder' : ‖S y - S x - A v‖ ≤ r := by
    calc
      ‖S y - S x - A v‖ ≤ B * ‖y - x‖ ^ 2 := by
        simpa [A, v] using hremainder
      _ ≤ B * (2 * r) ^ 2 := by
        gcongr
      _ ≤ r := by
        have hr0 := hr
        nlinarith
  have hclose :
      ‖S y - singularApproximationCenter (S x) A r k‖ < 3 * r := by
    have heq :
        S y - singularApproximationCenter (S x) A r k =
          (S y - S x - A v) +
            (A v -
              ((r * (k.1 : ℝ)) • singularImageDirection A 0 +
               (r * (k.2 : ℝ)) • singularImageDirection A 1)) := by
      simp only [singularApproximationCenter]
      abel
    rw [heq]
    calc
      ‖(S y - S x - A v) +
          (A v -
            ((r * (k.1 : ℝ)) • singularImageDirection A 0 +
             (r * (k.2 : ℝ)) • singularImageDirection A 1))‖ ≤
          ‖S y - S x - A v‖ +
            ‖A v -
              ((r * (k.1 : ℝ)) • singularImageDirection A 0 +
               (r * (k.2 : ℝ)) • singularImageDirection A 1)‖ :=
        norm_add_le _ _
      _ < r + 2 * r := add_lt_add_of_le_of_lt hremainder' hlinear
      _ = 3 * r := by ring
  rw [singularTargetIndexCover, Finset.mem_biUnion]
  exact ⟨k, hk,
    squareGridIndex_mem_nearby_of_norm_sub_lt hr hclose⟩

end Submission.Helpers
