import Mathlib
import Submission.Helpers

open scoped MatrixOrder Matrix

namespace Submission

/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/


theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  classical
  let P : ℕ → Matrix n n ℝ := fun k => A.map (fun x => x ^ k)
  have hP : ∀ k : ℕ, (P k).PosSemidef := by
    intro k
    induction k with
    | zero =>
      have hJ :
          (Matrix.vecMulVec (fun _ : n => (1 : ℝ)) (fun _ : n => (1 : ℝ))).PosSemidef := by
        simpa using
          (Matrix.posSemidef_vecMulVec_self_star (R := ℝ)
            (n := n) (fun _ : n => (1 : ℝ)))
      have heq :
          P 0 = Matrix.vecMulVec (fun _ : n => (1 : ℝ)) (fun _ : n => (1 : ℝ)) := by
        ext i j
        simp [P, Matrix.vecMulVec]
      rw [heq]
      exact hJ
    | succ k hk =>
      have heq : P (k+1) = (P k) ⊙ A := by
        ext i j
        simp [P, pow_succ]
      rw [heq]
      exact hk.hadamard hA
  let T : ℕ → Matrix n n ℝ := fun k => ((k.factorial : ℝ)⁻¹) • P k
  have hT : ∀ k : ℕ, (T k).PosSemidef := by
    intro k
    dsimp [T]
    exact (hP k).smul (inv_nonneg.mpr (Nat.cast_nonneg _))
  let S : ℕ → Matrix n n ℝ := fun N => ∑ k ∈ Finset.range N, T k
  have hS : ∀ N : ℕ, (S N).PosSemidef := by
    intro N
    dsimp [S]
    exact Matrix.posSemidef_sum (Finset.range N) (by
      intro i hi
      exact hT i)
  have hentry (i j : n) :
      Filter.Tendsto (fun N : ℕ => S N i j) Filter.atTop (nhds (Real.exp (A i j))) := by
    have hh : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (A i j) ^ k)
        (Real.exp (A i j)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (A i j)
    simpa [S, T, P, Matrix.sum_apply, smul_eq_mul] using hh.tendsto_sum_nat
  have hHerm : (A.map Real.exp).IsHermitian := by
    exact hA.isHermitian.map Real.exp (by
      intro x
      simp)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm ?_
  intro x
  have ht :
      Filter.Tendsto (fun N : ℕ => (star x) ⬝ᵥ (S N *ᵥ x))
        Filter.atTop (nhds ((star x) ⬝ᵥ ((A.map Real.exp) *ᵥ x))) := by
    have hinner (i : n) :
        Filter.Tendsto (fun N : ℕ => ∑ j : n, S N i j * x j)
          Filter.atTop (nhds (∑ j : n, Real.exp (A i j) * x j)) := by
      simpa using
        (tendsto_finset_sum (f := fun j (N : ℕ) => S N i j * x j)
          (a := fun j => Real.exp (A i j) * x j) Finset.univ (by
            intro j hj
            exact (hentry i j).mul_const (x j)))
    have houter :
        Filter.Tendsto
          (fun N : ℕ => ∑ i : n, (star x) i * (∑ j : n, S N i j * x j))
          Filter.atTop
          (nhds (∑ i : n, (star x) i * (∑ j : n, Real.exp (A i j) * x j))) := by
      simpa using
        (tendsto_finset_sum
          (f := fun i (N : ℕ) => (star x) i * (∑ j : n, S N i j * x j))
          (a := fun i => (star x) i * (∑ j : n, Real.exp (A i j) * x j))
          Finset.univ (by
            intro i hi
            exact tendsto_const_nhds.mul (hinner i)))
    simpa [dotProduct, Matrix.mulVec] using houter
  exact ge_of_tendsto ht (Filter.Eventually.of_forall (fun N =>
    (hS N).dotProduct_mulVec_nonneg x))


end Submission
