/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: posSemidef_map_exp
user: sqrt-of-2
model: GPT-5.5
submission_repo: sqrt-of-2/88b7e9060dec6431cca92cf56a408df3
submission_ref: 115fadf6e81b5de783af32becb958bb8a6d96dd7
issue_number: 151
-/
import Mathlib

open scoped MatrixOrder Matrix
open Matrix Filter Topology

namespace Submission

noncomputable def hadPow {n : Type*} (A : Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => fun _ _ => 1
  | k + 1 => hadPow A k ⊙ A

lemma hadPow_apply {n : Type*} (A : Matrix n n ℝ) (k : ℕ) (i j : n) :
    hadPow A k i j = A i j ^ k := by
  induction k with
  | zero =>
      simp [hadPow]
  | succ k ih =>
      simp [hadPow, ih, pow_succ, Matrix.hadamard_apply, mul_comm]

lemma hadPow_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (k : ℕ) :
    (hadPow A k).PosSemidef := by
  induction k with
  | zero =>
      classical
      let B : Matrix Unit n ℝ := fun _ _ => 1
      have hB : Matrix.PosSemidef (Bᴴ * B) := Matrix.posSemidef_conjTranspose_mul_self B
      convert hB using 1
      ext i j
      simp [hadPow, B, Matrix.mul_apply]
  | succ k ih =>
      simpa [hadPow] using ih.hadamard hA

noncomputable def expPartialSum {n : Type*} (A : Matrix n n ℝ) (N : ℕ) : Matrix n n ℝ :=
  (Finset.range N).sum fun k => (1 / (Nat.factorial k : ℝ)) • hadPow A k

lemma expPartialSum_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (N : ℕ) :
    (expPartialSum A N).PosSemidef := by
  classical
  induction N with
  | zero =>
      simp [expPartialSum, Matrix.PosSemidef.zero]
  | succ N ih =>
      rw [expPartialSum, Finset.sum_range_succ]
      exact ih.add ((hadPow_posSemidef hA N).smul (by positivity))

lemma expPartialSum_apply {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (N : ℕ) (i j : n) :
    expPartialSum A N i j =
      (Finset.range N).sum fun k => (A i j) ^ k / (Nat.factorial k : ℝ) := by
  change
    (((Finset.range N).sum fun k => (1 / (Nat.factorial k : ℝ)) • hadPow A k) :
        n → n → ℝ) i j =
      (Finset.range N).sum fun k => (A i j) ^ k / (Nat.factorial k : ℝ)
  rw [Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Matrix.smul_apply, hadPow_apply]
  ring

lemma expPartialSum_tendsto_entry {n : Type*} [Fintype n] (A : Matrix n n ℝ) (i j : n) :
    Tendsto (fun N => expPartialSum A N i j) atTop (𝓝 (Real.exp (A i j))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (A i j)).tendsto_sum_nat
  rw [Real.exp_eq_exp_ℝ]
  convert h using 1
  ext N
  exact expPartialSum_apply A N i j

lemma expPartialSum_tendsto_quadratic {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (x : n → ℝ) :
    Tendsto (fun N => star x ⬝ᵥ expPartialSum A N *ᵥ x) atTop
      (𝓝 (star x ⬝ᵥ A.map Real.exp *ᵥ x)) := by
  classical
  simp_rw [dotProduct, mulVec]
  apply tendsto_finset_sum
  intro i _hi
  apply Tendsto.const_mul
  apply tendsto_finset_sum
  intro j _hj
  simpa [Matrix.map_apply] using
    (expPartialSum_tendsto_entry A i j).mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => x j) atTop (𝓝 (x j)))

lemma continuous_quadratic_form {n : Type*} [Fintype n] [DecidableEq n] (x : n → ℝ) :
    Continuous fun M : Matrix n n ℝ => star x ⬝ᵥ M *ᵥ x := by
  classical
  simp_rw [dotProduct, mulVec]
  exact continuous_finset_sum Finset.univ fun i _hi =>
    continuous_const.mul <| continuous_finset_sum Finset.univ fun j _hj =>
      (show Continuous (fun M : Matrix n n ℝ => M i j) by
        change Continuous fun M : n → n → ℝ => M i j
        exact (continuous_apply j).comp (continuous_apply i)).mul continuous_const

theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simp [Matrix.map_apply]
    have h := hA.1.apply j i
    simpa using h.symm
  · have hlim :
        Tendsto (fun N => star x ⬝ᵥ expPartialSum A N *ᵥ x) atTop
          (𝓝 (star x ⬝ᵥ A.map Real.exp *ᵥ x)) :=
      expPartialSum_tendsto_quadratic A x
    exact isClosed_Ici.mem_of_tendsto hlim <|
      Filter.Eventually.of_forall fun N =>
        expPartialSum_posSemidef hA N |>.dotProduct_mulVec_nonneg x

end Submission
