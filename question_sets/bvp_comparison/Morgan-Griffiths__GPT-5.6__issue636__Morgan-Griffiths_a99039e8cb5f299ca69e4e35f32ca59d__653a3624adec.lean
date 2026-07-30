import Mathlib
namespace Submission

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem bvp_comparison (J : Set ℝ) (hJ_open : IsOpen J) (hJ_sub : Set.Icc (0 : ℝ) 1 ⊆ J)
    (u v : ℝ → ℝ)
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x)
    (hu' : ∀ x ∈ J, HasDerivAt (deriv u) (deriv (deriv u) x) x)
    (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hv' : ∀ x ∈ J, HasDerivAt (deriv v) (deriv (deriv v) x) x)
    (hineq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x ≤ -deriv (deriv v) x)
    (hu0 : u 0 ≤ v 0) (hu1 : u 1 ≤ v 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, u x ≤ v x :=
/-ResultProofBegin-/by
  classical
  have hD : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc _ _
  have hcont : ContinuousOn (u - v) (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    have hxJ : x ∈ J := hJ_sub hx
    exact ((hu x hxJ).continuousAt.sub (hv x hxJ).continuousAt).continuousWithinAt
  have hfirst : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt (u - v) ((deriv u - deriv v) x) (interior (Set.Icc (0 : ℝ) 1)) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
    have hxJ : x ∈ J := hJ_sub hxIcc
    exact ( (hu x hxJ).sub (hv x hxJ)).hasDerivWithinAt
  have hsecond : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt (deriv u - deriv v)
        ((deriv (deriv u) - deriv (deriv v)) x)
        (interior (Set.Icc (0 : ℝ) 1)) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
    have hxJ : x ∈ J := hJ_sub hxIcc
    exact ((hu' x hxJ).sub (hv' x hxJ)).hasDerivWithinAt
  have hnon : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1),
      0 ≤ (deriv (deriv u) - deriv (deriv v)) x := by
    intro x hx
    have hxoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hx
    have h := hineq x hxoo
    change 0 ≤ deriv (deriv u) x - deriv (deriv v) x
    linarith
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (u - v) :=
    convexOn_of_hasDerivWithinAt2_nonneg hD hcont hfirst hsecond hnon
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hmain : ∀ ⦃p⦄, p ∈ Set.Icc (0:ℝ) 1 →
        ∀ ⦃q⦄, q ∈ Set.Icc (0:ℝ) 1 →
        ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
          (u - v) (a • p + b • q) ≤ a • (u - v) p + b • (u - v) q :=
    hconv.2
  have hchord := @hmain (0:ℝ) hzero (1:ℝ) hone (1 - x) x
      (by linarith) (by linarith) (by ring)
  -- simplify the convex inequality for this chord
  have hs : (u - v) x ≤ (1 - x) * (u - v) 0 + x * (u - v) 1 := by
    simpa [smul_eq_mul] using hchord
  have h0 : (u - v) 0 ≤ 0 := by
    change u 0 - v 0 ≤ 0
    linarith
  have h1 : (u - v) 1 ≤ 0 := by
    change u 1 - v 1 ≤ 0
    linarith
  have hrhs : (1 - x) * (u - v) 0 + x * (u - v) 1 ≤ 0 := by
    have ha : (1 - x) * (u - v) 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) h0
    have hb : x * (u - v) 1 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hx0 h1
    linarith
  have hle : (u - v) x ≤ 0 := le_trans hs hrhs
  change u x - v x ≤ 0 at hle
  linarith/-ResultProofEnd-/
/-ResultEnd-/

end Submission
