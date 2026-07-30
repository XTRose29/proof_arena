import Submission.Scalar

namespace LeanEval.Analysis

noncomputable section

/-- In complex dimension at least three, the quadratic equation on orthogonal pairs
extends to all pairs. The auxiliary unit vector is orthogonal to both arguments; a
scalar multiple of it cancels their inner product, and the remaining terms cancel by
orthogonal and collinear instances of the equation. -/
lemma FrameFunction.homogeneousValue_parallelogram_of_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (hdim : 3 ≤ Module.finrank ℂ H)
    (horth : ∀ x y : H, inner ℂ x y = 0 →
      f.homogeneousValue (x + y) + f.homogeneousValue (x - y) =
        2 * f.homogeneousValue x + 2 * f.homogeneousValue y) :
    ∀ x y : H,
      f.homogeneousValue (x + y) + f.homogeneousValue (x - y) =
        2 * f.homogeneousValue x + 2 * f.homogeneousValue y := by
  intro x y
  obtain ⟨z, hz, hxz, hyz⟩ := exists_unit_orthogonal_pair hdim x y
  let c : ℂ := -inner ℂ x y
  have hzy : inner ℂ z y = 0 := inner_eq_zero_symm.mp hyz
  have hzz : inner ℂ z z = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hz]
    norm_num
  have huvPlus : inner ℂ (x + z) (y + c • z) = 0 := by
    simp only [inner_add_left, inner_add_right, inner_smul_right, hxz,
      hzy, hzz, mul_one, zero_add, add_zero]
    simp [c]
  have huvMinus : inner ℂ (x - z) (y - c • z) = 0 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_right, hxz,
      hzy, hzz, sub_zero, zero_sub]
    simp [c]
  have hxyPlus : inner ℂ (x + y) ((1 + c) • z) = 0 := by
    simp [hxz, hyz]
  have hxyMinus : inner ℂ (x - y) ((1 - c) • z) = 0 := by
    simp [hxz, hyz]
  have hxc : inner ℂ x z = 0 := hxz
  have hyc : inner ℂ y (c • z) = 0 := by
    simp [hyz]
  have h₁ := horth (x + z) (y + c • z) huvPlus
  have h₂ := horth (x - z) (y - c • z) huvMinus
  have h₃ := horth (x + y) ((1 + c) • z) hxyPlus
  have h₄ := horth (x - y) ((1 - c) • z) hxyMinus
  have h₅ := horth x z hxc
  have h₆ := horth y (c • z) hyc
  have hcol := f.homogeneousValue_parallelogram_smul c z
  rw [show x + z + (y + c • z) = (x + y) + (1 + c) • z by module,
    show x + z - (y + c • z) = (x - y) + (1 - c) • z by module] at h₁
  rw [show x - z + (y - c • z) = (x + y) - (1 + c) • z by module,
    show x - z - (y - c • z) = (x - y) - (1 - c) • z by module] at h₂
  rw [show z + c • z = (1 + c) • z by module,
    show z - c • z = (1 - c) • z by module] at hcol
  linarith

/-- It is enough for the finite-dimensional Gleason conclusion to prove the
quadratic equation only on orthogonal pairs. -/
lemma existsUnique_density_of_orthogonal_parallelogram
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (hdim : 3 ≤ Module.finrank ℂ H)
    (horth : ∀ x y : H, inner ℂ x y = 0 →
      f.homogeneousValue (x + y) + f.homogeneousValue (x - y) =
        2 * f.homogeneousValue x + 2 * f.homogeneousValue y) :
    ∃! T : H →L[ℂ] H,
      T.IsPositive ∧
      reTr T = 1 ∧
      ∀ P : H →L[ℂ] H, IsOrthProj P → f.μ P = reTr (T * P) := by
  apply existsUnique_density_of_parallelogram f
  exact f.homogeneousValue_parallelogram_of_orthogonal hdim horth

end

end LeanEval.Analysis
