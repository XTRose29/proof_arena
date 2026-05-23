/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: posSemidef_map_exp
user: kim-em
model: Aristotle (Harmonic)
submission_repo: kim-em/e6dd59ee0fcb958f116764a20bf374d3
submission_ref: e950873aef479ab789df674fa8d5a21097f24092
issue_number: 71
-/
import Mathlib

open scoped MatrixOrder Matrix

namespace Submission

theorem posSemidef_map_exp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  -- By the properties of the exponential function and the Schur product theorem, we know that if $A$ is positive semidefinite, then $e^A$ is also positive semidefinite.
  have h_exp_posSemidef : ∀ (k : ℕ), (Matrix.map A (fun x => x ^ k)).PosSemidef := by
    intro k;
    have h_exp_posSemidef : ∀ (k : ℕ), (Matrix.map A (fun x => x ^ k)).PosSemidef := by
      intro k
      have h_schur : ∀ (B C : Matrix n n ℝ), B.PosSemidef → C.PosSemidef → (B.hadamard C).PosSemidef := by
        intro B C hB hC;
        obtain ⟨ D, rfl ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg;
        obtain ⟨ E, rfl ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hC.nonneg;
        have h_schur : ∀ (x : n → ℝ), 0 ≤ ∑ i, ∑ j, x i * x j * (∑ k, D k i * D k j) * (∑ l, E l i * E l j) := by
          intro x
          have h_schur : ∑ i, ∑ j, x i * x j * (∑ k, D k i * D k j) * (∑ l, E l i * E l j) = ∑ k, ∑ l, (∑ i, x i * D k i * E l i) ^ 2 := by
            simp +decide only [Finset.mul_sum _ _ _, mul_comm, mul_left_comm, pow_two];
            simp +decide only [← Finset.sum_product'];
            apply Finset.sum_bij (fun x _ => (x.2.2.2, x.2.2.1, x.1, x.2.1));
            · simp +decide;
            · grind;
            · simp +decide;
            · simp +decide;
          exact h_schur.symm ▸ Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _;
        constructor;
        · ext i j; simp +decide [ Matrix.mul_apply, mul_comm ] ;
        · simp_all +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finsupp.sum_fintype ]
      induction' k with k ih;
      · simp +decide [ Matrix.PosSemidef ];
        simp +decide [ Matrix.IsHermitian, Finsupp.sum_fintype ];
        exact ⟨ by ext; simp +decide, fun x => by simpa only [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] using mul_self_nonneg _ ⟩;
      · convert h_schur _ _ ih hA using 1;
    exact h_exp_posSemidef k;
  -- By the properties of the exponential function and the Schur product theorem, we know that if $A$ is positive semidefinite, then $\sum_{k=0}^{\infty} \frac{A^k}{k!}$ is also positive semidefinite.
  have h_sum_posSemidef : ∀ (N : ℕ), (Matrix.map A (fun x => ∑ k ∈ Finset.range (N + 1), x ^ k / Nat.factorial k)).PosSemidef := by
    intro N
    have h_sum_posSemidef : ∀ (k : ℕ), (Matrix.map A (fun x => x ^ k / Nat.factorial k)).PosSemidef := by
      intro k
      have h_sum_posSemidef : (Matrix.map A (fun x => x ^ k)).PosSemidef := h_exp_posSemidef k
      have h_div_posSemidef : (Matrix.map A (fun x => x ^ k / Nat.factorial k)).PosSemidef := by
        convert h_sum_posSemidef.smul ( show ( 0 : ℝ ) ≤ 1 / ( k.factorial : ℝ ) by positivity ) using 1 ; ext i j ; simp +decide [ div_eq_inv_mul ]
      exact h_div_posSemidef;
    induction' N with N ih;
    · simpa using h_sum_posSemidef 0;
    · convert ih.add ( h_sum_posSemidef ( N + 1 ) ) using 1 ; ext i j ; simp +decide [ Finset.sum_range_succ ];
  -- By the properties of the exponential function and the Schur product theorem, we know that if $A$ is positive semidefinite, then $\lim_{N \to \infty} \sum_{k=0}^{N} \frac{A^k}{k!}$ is also positive semidefinite.
  have h_lim_posSemidef : Filter.Tendsto (fun N => Matrix.map A (fun x => ∑ k ∈ Finset.range (N + 1), x ^ k / Nat.factorial k)) Filter.atTop (nhds (Matrix.map A Real.exp)) := by
    refine' tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => _;
    simpa [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ] using Real.summable_pow_div_factorial ( A i j ) |> Summable.hasSum |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1;
  refine' ⟨ _, fun x => _ ⟩;
  · ext i j; simp +decide;
    exact hA.1.apply _ _ ▸ rfl;
  · have h_lim_posSemidef : Filter.Tendsto (fun N => x.sum (fun i xi => x.sum (fun j xj => star xi * (A.map (fun x => ∑ k ∈ Finset.range (N + 1), x ^ k / Nat.factorial k)) i j * xj))) Filter.atTop (nhds (x.sum (fun i xi => x.sum (fun j xj => star xi * (A.map Real.exp) i j * xj)))) := by
      exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => Filter.Tendsto.mul ( Filter.Tendsto.mul tendsto_const_nhds ( tendsto_pi_nhds.mp ( tendsto_pi_nhds.mp h_lim_posSemidef i ) j ) ) tendsto_const_nhds;
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_lim_posSemidef fun N => by simpa [ Matrix.mulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using h_sum_posSemidef N |>.2 x;

end Submission