import Mathlib
import Mathlib.Analysis.Normed.Algebra.Exponential

open scoped Matrix MatrixOrder
open Matrix

namespace Submission

/-- Matrix is a type synonym for `n → m → α`. If the unifier has already treated 
    the type as a function, `unfold Matrix` will fail to find the literal token. 
    We use `tendsto_pi_nhds` which naturally operates on function types. -/
lemma hasSum_matrix {ι n m α : Type*} [Fintype n] [Fintype m] [TopologicalSpace α]
    [AddCommMonoid α] {f : ι → Matrix n m α} {M : Matrix n m α} :
    HasSum f M ↔ ∀ i j, HasSum (fun k => f k i j) (M i j) := by
  unfold HasSum
  refine Iff.trans tendsto_pi_nhds ?_
  apply forall_congr'; intro i
  refine Iff.trans tendsto_pi_nhds ?_
  apply forall_congr'; intro j
  apply Iff.of_eq
  congr! 1
  ext s
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change f a i j + (∑ b ∈ s, f b) i j = f a i j + ∑ x ∈ s, f x i j
    rw [ih]

lemma isClosed_posSemidef {n : Type*} [Fintype n] : IsClosed {A : Matrix n n ℝ | A.PosSemidef} := by
  have h_eq : {A : Matrix n n ℝ | A.PosSemidef} = 
    {A | IsHermitian A} ∩ ⋂ (x : n →₀ ℝ), {A | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj} := by
    ext A
    simp only [PosSemidef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [h_eq]
  apply IsClosed.inter
  · -- IsHermitian is closed
    apply isClosed_eq
    · apply continuous_pi; intro i
      apply continuous_pi; intro j
      have h : (fun (A : Matrix n n ℝ) => Aᴴ i j) = fun A => star (A j i) := rfl
      rw [h]
      -- star is continuous
      exact continuous_star.comp ((continuous_apply i).comp (continuous_apply j))
    · exact continuous_id
  · -- Quadratic form is closed
    apply isClosed_iInter; intro x
    apply isClosed_le continuous_const
    simp_rw [Finsupp.sum]
    apply continuous_finset_sum; intro i _
    apply continuous_finset_sum; intro j _
    -- Goal is Continuous (fun A => star (x i) * A i j * x j)
    -- This evaluates as (star (x i) * A i j) * x j
    apply Continuous.mul
    · apply Continuous.mul continuous_const
      exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const

theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  let Ak (k : ℕ) : Matrix n n ℝ := A.map (· ^ k)
  let f (k : ℕ) : Matrix n n ℝ := (1 / k.factorial : ℝ) • Ak k
  
  -- Ak k is PSD
  have hAk (k : ℕ) : (Ak k).PosSemidef := by
    induction k with
    | zero =>
      unfold PosSemidef
      constructor
      · ext i j
        simp [Ak, conjTranspose, transpose, Matrix.of_apply]
      · intro x
        simp_rw [Finsupp.sum, Ak, Matrix.map_apply, pow_zero]
        simp [star]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, ← sq]
        exact sq_nonneg _    | succ k ih =>
      have h_Ak_succ : Ak (k + 1) = Ak k ⊙ A := by
        ext i j
        simp [Ak, pow_succ]
      rw [h_Ak_succ]
      exact ih.hadamard hA

  -- Partial sums are PSD
  have h_sum_psd (N : ℕ) : ((Finset.range N).sum f).PosSemidef := by
    rw [← nonneg_iff_posSemidef]
    apply Finset.sum_nonneg
    intro k _
    apply smul_nonneg
    · apply one_div_nonneg.mpr
      exact Nat.cast_nonneg _
    · exact (hAk k).nonneg

  -- Series converges to A.map Real.exp
  have h_hasSum : HasSum f (A.map Real.exp) := by
    apply hasSum_matrix.mpr
    intro i j
    simp [f, Ak]
    -- Real.exp Taylor series
    let h_exp := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (A i j)
    simp [NormedSpace.expSeries, smul_eq_mul] at h_exp
    rw [Real.exp_eq_exp_ℝ]
    exact h_exp


  -- Limit of PSD is PSD
  exact isClosed_posSemidef.mem_of_tendsto h_hasSum.tendsto_sum_nat (Filter.Eventually.of_forall h_sum_psd)

end Submission