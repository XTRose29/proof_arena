import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Submission.Helpers

open scoped MatrixOrder Matrix

namespace Submission

/-- Each Hadamard power `A.map (·^k)` of a PSD matrix is PSD. -/
private lemma posSemidef_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (k : ℕ) :
    (A.map (· ^ k)).PosSemidef := by
  induction k with
  | zero =>
    have hone : A.map (fun a : ℝ => a ^ (0 : ℕ)) = Matrix.vecMulVec (1 : n → ℝ) 1 := by
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [hone]
    have h := Matrix.posSemidef_vecMulVec_self_star (1 : n → ℝ)
    simpa using h
  | succ k ih =>
    have heq : A.map (fun a : ℝ => a ^ (k + 1)) = (A.map (· ^ k)) ⊙ A := by
      ext i j
      simp [Matrix.hadamard_apply, pow_succ]
    rw [heq]
    exact ih.hadamard hA

theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  have hSemi : Function.Semiconj Real.exp (star : ℝ → ℝ) star := fun _ => rfl
  have hHerm : (A.map Real.exp).IsHermitian := hA.isHermitian.map Real.exp hSemi
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm, fun x => ?_⟩
  -- For each (i,j), x_i_star * exp(A_ij) * x_j has the series
  -- ∑' k, x_i_star * A_ij^k * x_j / k!.
  have hHasSum_ij : ∀ i j : n,
      HasSum (fun k : ℕ => star (x i) * ((A i j) ^ k / (k.factorial : ℝ)) * x j)
        (star (x i) * Real.exp (A i j) * x j) := by
    intro i j
    have h : HasSum (fun n : ℕ => (A i j) ^ n / (n.factorial : ℝ)) (Real.exp (A i j)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (A i j)
    exact (h.mul_left (star (x i))).mul_right (x j)
  -- Sum over (i, j) ∈ univ × univ.
  have hHasSum_total :
      HasSum (fun k : ℕ => ∑ i, ∑ j, star (x i) * ((A i j) ^ k / (k.factorial : ℝ)) * x j)
        (∑ i, ∑ j, star (x i) * Real.exp (A i j) * x j) := by
    refine hasSum_sum (fun i _ => ?_)
    refine hasSum_sum (fun j _ => ?_)
    exact hHasSum_ij i j
  -- Identify the target: dot product expansion.
  have hTarget : ∑ i, ∑ j, star (x i) * Real.exp (A i j) * x j =
      star x ⬝ᵥ ((A.map Real.exp) *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- Identify each summand.
  have hTerm : ∀ k : ℕ,
      ∑ i, ∑ j, star (x i) * ((A i j) ^ k / (k.factorial : ℝ)) * x j =
        (k.factorial : ℝ)⁻¹ * (star x ⬝ᵥ ((A.map (· ^ k)) *ᵥ x)) := by
    intro k
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum,
               div_eq_mul_inv]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- Combine to get the HasSum we want.
  have hHasSum_final :
      HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * (star x ⬝ᵥ ((A.map (· ^ k)) *ᵥ x)))
        (star x ⬝ᵥ ((A.map Real.exp) *ᵥ x)) := by
    rw [← hTarget]
    convert hHasSum_total using 1
    funext k
    exact (hTerm k).symm
  -- Each summand is nonneg.
  refine hHasSum_final.nonneg fun k => ?_
  have hk : 0 ≤ (k.factorial : ℝ)⁻¹ := by positivity
  have hpsd := (posSemidef_pow hA k).dotProduct_mulVec_nonneg x
  exact mul_nonneg hk hpsd

end Submission
