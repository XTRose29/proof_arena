/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: posSemidef_map_exp
user: sqrt-of-2
model: Aristotle (Harmonic)
submission_repo: sqrt-of-2/931556b393de1dc23de63d1c5aefc109
submission_ref: 6fb74c6f721c1824f764bfefcd7de649de5f04ac
issue_number: 226
-/
import Mathlib

open scoped MatrixOrder Matrix
open Matrix Finset

namespace Submission

-- Schur product theorem: Hadamard (entrywise) product of PSD matrices is PSD
lemma posSemidef_hadamard {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.of fun i j => A i j * B i j).PosSemidef :=
  (hA.kronecker hB).submatrix (fun i => (i, i))

-- Entrywise k-th power of a PSD matrix is PSD
lemma posSemidef_entrywise_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (k : ℕ) :
    (A.map (· ^ k)).PosSemidef := by
  induction k with
  | zero =>
    have h1 : A.map (· ^ 0) = Matrix.of fun (_ _ : n) => (1 : ℝ) := by
      ext i j; simp [Matrix.map, Matrix.of_apply]
    rw [h1]
    have h2 : (Matrix.of fun (_ _ : n) => (1 : ℝ)) = vecMulVec (1 : n → ℝ) (star (1 : n → ℝ)) := by
      ext i j; simp [vecMulVec, Matrix.of_apply]
    rw [h2]
    exact posSemidef_vecMulVec_self_star 1
  | succ k ih =>
    have h : A.map (· ^ (k + 1)) = Matrix.of fun i j => A i j * (A.map (· ^ k)) i j := by
      ext i j; simp [Matrix.map, pow_succ, mul_comm, Matrix.of_apply]
    rw [h]
    exact posSemidef_hadamard hA ih

/-
Quadratic form of entrywise k-th power scaled by 1/k! is nonneg
-/
lemma quadform_pow_div_factorial_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (x : n → ℝ) (k : ℕ) :
    0 ≤ ∑ i, ∑ j, x i * ((A i j) ^ k / ↑k.factorial) * x j := by
  -- Start by using the fact that the quadratic form is a sum of products
  have quad_form_eq : ∑ i, ∑ j, x i * (A i j ^ k / (k.factorial : ℝ)) * x j = ∑ i, ∑ j, (A i j ^ k * (x i * x j)) / (k.factorial : ℝ) := by
    exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by ring;
  -- Use the fact that the quadratic form $x^T A^k x$ is nonnegative for any positive semidefinite matrix $A$ and any vector $x$.
  have h_quad_form_nonneg : ∀ x : n → ℝ, 0 ≤ ∑ i, ∑ j, (A i j ^ k * (x i * x j)) := by
    have := posSemidef_entrywise_pow hA k;
    have := this.2;
    intro x; specialize this ( Finsupp.equivFunOnFinite.symm x ) ; simp_all +decide [ Finsupp.sum_fintype, mul_assoc, mul_comm, mul_left_comm ] ;
  exact quad_form_eq.symm ▸ by simpa only [ ← Finset.sum_div _ _ _ ] using div_nonneg ( h_quad_form_nonneg x ) ( Nat.cast_nonneg _ ) ;

/-
The quadratic form of exp equals a convergent series
-/
lemma quadform_exp_eq_tsum {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (x : n → ℝ) :
    dotProduct (star x) ((A.map Real.exp).mulVec x) =
    ∑' k, ∑ i, ∑ j, x i * ((A i j) ^ k / ↑k.factorial) * x j := by
  have h_quadForm_exp : dotProduct x (Matrix.mulVec (Matrix.map A Real.exp) x) = ∑' k : ℕ, ∑ i, ∑ j, (x i * ((A i j) ^ k / (k : ℕ).factorial) * x j) := by
    have h_summable : ∀ i j, Summable (fun k : ℕ => (x i * ((A i j) ^ k / (k : ℕ).factorial) * x j)) := by
      exact fun i j => Summable.mul_right _ ( Summable.mul_left _ ( Real.summable_pow_div_factorial _ ) )
    have h_summable : Summable (fun k : ℕ => ∑ i, ∑ j, (x i * ((A i j) ^ k / (k : ℕ).factorial) * x j)) := by
      exact summable_sum fun i _ => summable_sum fun j _ => h_summable i j;
    have h_summable : ∑' k : ℕ, ∑ i, ∑ j, (x i * ((A i j) ^ k / (k : ℕ).factorial) * x j) = ∑ i, ∑ j, ∑' k : ℕ, (x i * ((A i j) ^ k / (k : ℕ).factorial) * x j) := by
      have h_summable : ∀ N : ℕ, ∑ k ∈ Finset.range N, ∑ i, ∑ j, (x i * ((A i j) ^ k / (k : ℕ).factorial) * x j) = ∑ i, ∑ j, ∑ k ∈ Finset.range N, (x i * ((A i j) ^ k / (k : ℕ).factorial) * x j) := by
        exact fun N => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
      have h_summable : Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, ∑ i, ∑ j, (x i * ((A i j) ^ k / (k : ℕ).factorial) * x j)) Filter.atTop (nhds (∑' k : ℕ, ∑ i, ∑ j, (x i * ((A i j) ^ k / (k : ℕ).factorial) * x j))) := by
        exact Summable.hasSum ‹_› |> HasSum.tendsto_sum_nat;
      exact tendsto_nhds_unique h_summable ( by simpa only [ * ] using tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => Summable.hasSum ( by solve_by_elim ) |> HasSum.tendsto_sum_nat );
    simp_all +decide [ dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, tsum_mul_left, tsum_mul_right ];
    simp +decide [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ];
  exact h_quadForm_exp

theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  constructor;
  · simp_all +decide [ Matrix.IsHermitian, ← Matrix.ext_iff ];
    exact fun i j => hA.1.apply j i ▸ rfl;
  · intro x
    have h_sum : 0 ≤ ∑ i, ∑ j, x i * (Real.exp (A i j)) * x j := by
      convert quadform_exp_eq_tsum ( x := x ) ▸ tsum_nonneg fun k => quadform_pow_div_factorial_nonneg hA x k using 1;
      simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
    simpa [ Finsupp.sum_fintype, mul_assoc, mul_comm, mul_left_comm ] using h_sum

end Submission
