/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: posSemidef_map_exp
user: Morgan-Griffiths
model: GPT-5.5
submission_repo: Morgan-Griffiths/c71279c880cb7d2fc2bf0cd90fca4bb8
submission_ref: c8c99fc3f82132045106510b592d4111d4b31e0b
issue_number: 37
-/
import Mathlib

namespace Submission

open scoped MatrixOrder Matrix

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
open scoped BigOperators

/-- The all-ones matrix is positive semidefinite: it is `B * Bᴴ` for the one-column
matrix `B` whose entries are all `1`. -/
lemma allOnes_posSemidef {n : Type*} [Fintype n] [DecidableEq n] :
    (Matrix.of (fun (_ : n) (_ : n) => (1 : ℝ))).PosSemidef := by
  let B : Matrix n (Fin 1) ℝ := fun _ _ => 1
  have hB := Matrix.posSemidef_self_mul_conjTranspose B
  convert hB using 1
  ext i j
  simp [B, Matrix.mul_apply]

/-- Entrywise powers of a positive semidefinite real matrix are positive semidefinite.
The induction step is the Schur product theorem. -/
lemma map_pow_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    ∀ k : ℕ, (A.map (fun x => x ^ k)).PosSemidef := by
  intro k
  induction k with
  | zero =>
      simpa using allOnes_posSemidef (n := n)
  | succ k ih =>
      have h := ih.hadamard hA
      simpa [Matrix.hadamard, pow_succ] using h

/-- The `N`th partial sum of the entrywise exponential power series. -/
noncomputable def expPartial {n : Type*} (A : Matrix n n ℝ) (N : ℕ) : Matrix n n ℝ :=
  ∑ k ∈ Finset.range N, ((1 / (Nat.factorial k : ℝ)) • A.map (fun x => x ^ k))

/-- Each partial sum of the entrywise exponential series is positive semidefinite. -/
lemma expPartial_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (N : ℕ) :
    (expPartial A N).PosSemidef := by
  classical
  unfold expPartial
  apply Matrix.posSemidef_sum
  intro k hk
  exact (map_pow_posSemidef hA k).smul (by positivity)

/-- Entrywise formula for the partial sums, matching Mathlib's exponential-series theorem. -/
lemma expPartial_apply {n : Type*} (A : Matrix n n ℝ) (N : ℕ) (i j : n) :
    expPartial A N i j = ∑ k ∈ Finset.range N, (A i j) ^ k / (Nat.factorial k : ℝ) := by
  simp [expPartial, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, div_eq_mul_inv,
    mul_comm]

/-- The partial sums converge entrywise, hence in the product topology on matrices, to the
entrywise exponential matrix. -/
lemma expPartial_tendsto {n : Type*} (A : Matrix n n ℝ) :
    Filter.Tendsto (fun N => expPartial A N) Filter.atTop (nhds (A.map Real.exp)) := by
  unfold Matrix
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  have h := (NormedSpace.expSeries_div_hasSum_exp (A i j)).tendsto_sum_nat
  simpa [expPartial_apply, Real.exp_eq_exp_ℝ] using h
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/
theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef :=
/-ResultProofBegin-/
by
  have hHerm : (A.map Real.exp).IsHermitian := by
    exact hA.isHermitian.map Real.exp (by intro x; simp)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm ?_
  intro x
  let q : Matrix n n ℝ → ℝ := fun M => star x ⬝ᵥ M.mulVec x
  have hcont : Continuous q := by
    unfold q
    fun_prop
  have htend : Filter.Tendsto (fun N => q (expPartial A N)) Filter.atTop
      (nhds (q (A.map Real.exp))) := by
    exact (hcont.tendsto (A.map Real.exp)).comp (expPartial_tendsto A)
  have hmem : q (A.map Real.exp) ∈ Set.Ici (0 : ℝ) := by
    exact isClosed_Ici.mem_of_tendsto htend
      (Filter.Eventually.of_forall fun N =>
        (expPartial_posSemidef hA N).dotProduct_mulVec_nonneg x)
  simpa [q] using hmem
/-ResultProofEnd-/
/-ResultEnd-/
end Submission

