import Mathlib

open scoped MatrixOrder Matrix

namespace Submission

theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  let P : ℕ → Matrix n n ℝ := fun k ↦ A.map fun x ↦ x ^ k
  have hP : ∀ k, (P k).PosSemidef := by
    intro k
    induction k with
    | zero =>
        let u : n → ℝ := fun _ ↦ 1
        have hP0 : P 0 = Matrix.vecMulVec u (star u) := by
          ext i j
          simp [P, u, Matrix.vecMulVec]
        rw [hP0]
        exact Matrix.posSemidef_vecMulVec_self_star u
    | succ k hk =>
        have hPsucc : P (k + 1) = P k ⊙ A := by
          ext i j
          simp [P, pow_succ, Matrix.hadamard_apply]
        rw [hPsucc]
        exact hk.hadamard hA
  let f : ℕ → Matrix n n ℝ := fun k ↦ (k.factorial : ℝ)⁻¹ • P k
  have hf : ∀ k, (f k).PosSemidef := fun k ↦
    (hP k).smul (inv_nonneg.mpr (Nat.cast_nonneg k.factorial))
  have hentry (i j : n) :
      HasSum (fun k ↦ f k i j) (Real.exp (A i j)) := by
    simpa [f, P, div_eq_mul_inv, mul_comm, Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (A i j)
  refine ⟨?_, ?_⟩
  · apply hA.isHermitian.map Real.exp
    intro x
    simp
  · intro x
    simp only [Finsupp.sum, Matrix.map_apply]
    have hquad :
        HasSum
          (fun k ↦ x.support.sum fun i ↦
            x.support.sum fun j ↦ star (x i) * f k i j * x j)
          (x.support.sum fun i ↦
            x.support.sum fun j ↦ star (x i) * Real.exp (A i j) * x j) := by
      apply hasSum_sum
      intro i _
      apply hasSum_sum
      intro j _
      exact ((hentry i j).mul_left (star (x i))).mul_right (x j)
    rw [← hquad.tsum_eq]
    exact tsum_nonneg fun k ↦ by
      simpa only [Finsupp.sum] using (hf k).2 x

end Submission
