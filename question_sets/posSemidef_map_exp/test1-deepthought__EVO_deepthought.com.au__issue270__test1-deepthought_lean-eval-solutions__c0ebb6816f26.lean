import Mathlib
open scoped MatrixOrder Matrix
open Real Filter Topology BigOperators
open Complex

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Submission

lemma all_ones_posSemidef {n : Type*} [Fintype n] : 
    (Matrix.of fun i j : n => (1 : ℝ)).PosSemidef := by
  let v : Matrix Unit n ℝ := Matrix.of fun (_ : Unit) (j : n) => (1 : ℝ)
  have hJ : (Matrix.of fun i j : n => (1 : ℝ)) = vᴴ * v := by
    ext i j; simp [v, Matrix.mul_apply]
  rw [hJ]
  exact Matrix.posSemidef_conjTranspose_mul_self v

lemma hadamard_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊙ B).PosSemidef := by
  let diag : n → n × n := fun i => (i, i)
  have hkronecker : (A.kronecker B).PosSemidef := hA.kronecker hB
  have hsub : ((A.kronecker B).submatrix diag diag).PosSemidef := hkronecker.submatrix diag
  have heq : A ⊙ B = (A.kronecker B).submatrix diag diag := by
    ext i j; simp [Matrix.hadamard_apply, Matrix.submatrix_apply, diag]
  rw [heq]
  exact hsub

noncomputable def hadamard_pow {n : Type*} (A : Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => Matrix.of fun _ _ => (1 : ℝ)
  | k+1 => hadamard_pow A k ⊙ A

lemma hadamard_pow_apply {n : Type*} (A : Matrix n n ℝ) (k : ℕ) (i j : n) : 
    (hadamard_pow A k) i j = (A i j) ^ k := by
  induction' k with k ih generalizing i j
  · simp [hadamard_pow]
  · simp [hadamard_pow, Matrix.hadamard_apply, ih, pow_succ]

lemma hadamard_pow_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (k : ℕ) : (hadamard_pow A k).PosSemidef := by
  induction' k with k ih
  · exact all_ones_posSemidef
  · dsimp [hadamard_pow]
    exact hadamard_posSemidef ih hA

noncomputable def expPartialSum {n : Type*} (A : Matrix n n ℝ) (N : ℕ) : Matrix n n ℝ :=
  ∑ k ∈ Finset.range (N+1), ((1 : ℝ) / (Nat.factorial k : ℝ)) • (hadamard_pow A k)

lemma expPartialSum_apply {n : Type*} (A : Matrix n n ℝ) (N : ℕ) (i j : n) : 
    (expPartialSum A N) i j = ∑ k ∈ Finset.range (N+1), ((A i j) ^ k) / (Nat.factorial k : ℝ) := by
  calc
    (expPartialSum A N) i j = (∑ k ∈ Finset.range (N+1), ((1 : ℝ) / (Nat.factorial k : ℝ)) • (hadamard_pow A k)) i j := rfl
    _ = ∑ k ∈ Finset.range (N+1), (((1 : ℝ) / (Nat.factorial k : ℝ)) • (hadamard_pow A k)) i j := by
      rw [Matrix.sum_apply]
    _ = ∑ k ∈ Finset.range (N+1), ((1 : ℝ) / (Nat.factorial k : ℝ)) * (hadamard_pow A k) i j := by
      simp [Matrix.smul_apply, smul_eq_mul]
    _ = ∑ k ∈ Finset.range (N+1), ((1 : ℝ) / (Nat.factorial k : ℝ)) * ((A i j) ^ k) := by
      simp [hadamard_pow_apply]
    _ = ∑ k ∈ Finset.range (N+1), ((A i j) ^ k) / (Nat.factorial k : ℝ) := by
      simp [div_eq_mul_inv, mul_comm]

lemma expPartialSum_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (N : ℕ) : (expPartialSum A N).PosSemidef := by
  induction' N with N ih
  · have : expPartialSum A 0 = ((1 : ℝ) / (Nat.factorial 0 : ℝ)) • (hadamard_pow A 0) := by
      unfold expPartialSum; simp
    rw [this]
    have hJ : hadamard_pow A 0 = Matrix.of fun _ _ : n => (1 : ℝ) := rfl
    rw [hJ]
    have hpos : (0 : ℝ) ≤ (1 : ℝ) / (Nat.factorial 0 : ℝ) := by norm_num
    exact all_ones_posSemidef.smul hpos
  · rw [expPartialSum, Finset.sum_range_succ, ← expPartialSum]
    have hsum : (expPartialSum A N).PosSemidef := ih
    have hterm : (((1 : ℝ) / (Nat.factorial (N+1) : ℝ)) • (hadamard_pow A (N+1))).PosSemidef := by
      have hp : (hadamard_pow A (N+1)).PosSemidef := hadamard_pow_posSemidef hA (N+1)
      have hpos : (0 : ℝ) ≤ (1 : ℝ) / (Nat.factorial (N+1) : ℝ) := by
        refine div_nonneg (by norm_num) (by positivity)
      exact hp.smul hpos
    exact hsum.add hterm

lemma ofReal_pow_re (x : ℝ) (k : ℕ) : ((x : ℂ) ^ k).re = x ^ k := by
  induction' k with k ih
  · simp
  · simp [pow_succ, ih, mul_comm]

lemma tendsto_exp_series (x : ℝ) : Tendsto (λ N : ℕ => ∑ k ∈ Finset.range (N+1), x ^ k / (Nat.factorial k : ℝ)) 
    atTop (𝓝 (Real.exp x)) := by
  have h_tendsto_cpx : Tendsto (λ n : ℕ => (Complex.exp' (x : ℂ)) n) atTop (𝓝 (Complex.exp (x : ℂ))) := by
    simpa [Complex.exp_def] using (Complex.exp' (x : ℂ)).tendsto_limit
  have h_tendsto_succ : Tendsto (λ n : ℕ => (Complex.exp' (x : ℂ)) (n+1)) atTop (𝓝 (Complex.exp (x : ℂ))) :=
    h_tendsto_cpx.comp (tendsto_add_atTop_nat 1)
  have h_re_tendsto : Tendsto (λ n : ℕ => ((Complex.exp' (x : ℂ)) (n+1) : ℂ).re) atTop (𝓝 ((Complex.exp (x : ℂ)).re)) := by
    exact continuous_re.tendsto _ |>.comp h_tendsto_succ
  have h_re_sum : ∀ n : ℕ, ((Complex.exp' (x : ℂ)) (n+1) : ℂ).re = (∑ k ∈ Finset.range (n+1), x ^ k / (Nat.factorial k : ℝ)) := by
    intro n
    calc
      ((Complex.exp' (x : ℂ)) (n+1) : ℂ).re = ((∑ k ∈ Finset.range (n+1), (x : ℂ) ^ k / (Nat.factorial k : ℂ)) : ℂ).re := by
        rfl
      _ = ∑ k ∈ Finset.range (n+1), ((x : ℂ) ^ k / (Nat.factorial k : ℂ)).re := by simp
      _ = ∑ k ∈ Finset.range (n+1), x ^ k / (Nat.factorial k : ℝ) := by
        simp [ofReal_pow_re]
  simp_rw [h_re_sum] at h_re_tendsto
  have h_real_exp : Real.exp x = (Complex.exp (x : ℂ)).re := by
    calc
      Real.exp x = ((Real.exp x : ℂ) : ℂ).re := (Complex.ofReal_re (Real.exp x)).symm
      _ = (Complex.exp (x : ℂ)).re := by rw [Complex.ofReal_exp x]
  simpa [h_real_exp] using h_re_tendsto

lemma posSemidef_of_entrywise_limit {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} {S : ℕ → Matrix n n ℝ}
    (hS_PSD : ∀ N, (S N).PosSemidef)
    (hlim : ∀ i j, Tendsto (λ N => (S N) i j) atTop (𝓝 (M i j))) : M.PosSemidef := by
  have hM_herm : M.IsHermitian := by
    ext i j
    have h1 : Tendsto (λ N => (S N) i j) atTop (𝓝 (M i j)) := hlim i j
    have h2 : Tendsto (λ N => (S N) j i) atTop (𝓝 (M j i)) := hlim j i
    have heq : ∀ N, (S N) i j = (S N) j i := by
      intro N
      have hS_herm : (S N).IsHermitian := (hS_PSD N).1
      have h_eq := congrArg (fun (A : Matrix n n ℝ) => A i j) hS_herm
      simpa [Matrix.conjTranspose_apply] using h_eq.symm
    have hM_eq : M j i = M i j := by
      apply tendsto_nhds_unique h2
      simpa [heq] using h1
    simpa [Matrix.conjTranspose_apply] using hM_eq
  refine ⟨hM_herm, ?_⟩
  intro x
  let s := x.support
  have h_form : x.sum (fun i xi => x.sum (fun j xj => xi * M i j * xj)) = 
      ∑ i ∈ s, ∑ j ∈ s, x i * M i j * x j := by
    simp [Finsupp.sum, s]
  have h_form_S : ∀ N, x.sum (fun i xi => x.sum (fun j xj => xi * (S N) i j * xj)) = 
      ∑ i ∈ s, ∑ j ∈ s, x i * (S N) i j * x j := by
    intro N; simp [Finsupp.sum, s]
  have h_nonneg : ∀ N, 0 ≤ ∑ i ∈ s, ∑ j ∈ s, x i * (S N) i j * x j := by
    intro N
    rw [← h_form_S N]
    have hPSD := hS_PSD N
    have hpos := hPSD.2 x
    simpa [star] using hpos
  have h_sum_lim : Tendsto (λ N => ∑ i ∈ s, ∑ j ∈ s, x i * (S N) i j * x j) atTop 
      (𝓝 (∑ i ∈ s, ∑ j ∈ s, x i * M i j * x j)) := by
    apply tendsto_finset_sum s
    intro i hi
    apply tendsto_finset_sum s
    intro j hj
    have hconv : Tendsto (λ N => (S N) i j) atTop (𝓝 (M i j)) := hlim i j
    have h_const_mul : Tendsto (λ N : ℕ => x i * (S N) i j * x j) atTop (𝓝 (x i * M i j * x j)) := by
      refine ((tendsto_const_nhds : Tendsto (λ _ : ℕ => x i) atTop _).mul hconv).mul ?_
      exact tendsto_const_nhds
    simpa [mul_assoc] using h_const_mul
  have h_nonneg_lim : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, x i * M i j * x j := by
    apply ge_of_tendsto h_sum_lim
    rw [Filter.eventually_atTop]
    refine ⟨0, λ n hn => h_nonneg n⟩
  calc
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, x i * M i j * x j := h_nonneg_lim
    _ = x.sum (fun i xi => x.sum (fun j xj => xi * M i j * xj)) := by symm; exact h_form
    _ = x.sum (fun i xi => x.sum (fun j xj => star xi * M i j * xj)) := by simp [star]

theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : (A.map Real.exp).PosSemidef := by
  let S := λ N => expPartialSum A N
  have hS_PSD : ∀ N, (S N).PosSemidef := expPartialSum_posSemidef hA
  have hlim : ∀ i j, Tendsto (λ N => (S N) i j) atTop (𝓝 ((A.map Real.exp) i j)) := by
    intro i j
    have h_entry : (A.map Real.exp) i j = Real.exp (A i j) := by simp
    rw [h_entry]
    have h_S_entry : ∀ N, (S N) i j = ∑ k ∈ Finset.range (N+1), ((A i j) ^ k) / (Nat.factorial k : ℝ) := by
      intro N; simp [S, expPartialSum_apply]
    simp_rw [h_S_entry]
    exact tendsto_exp_series (A i j)
  exact posSemidef_of_entrywise_limit hS_PSD hlim

end Submission