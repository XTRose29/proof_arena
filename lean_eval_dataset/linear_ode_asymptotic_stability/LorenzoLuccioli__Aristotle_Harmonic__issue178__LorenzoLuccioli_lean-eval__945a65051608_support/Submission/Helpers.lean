import Mathlib
import Submission.ExpDecay

open scoped Matrix
open NormedSpace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace Submission

/-! ### Helper: mulVec as a continuous linear map (in the matrix argument) -/

noncomputable def matMulVecCLM (n : ℕ) (v : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.mulVec v
      map_add' := fun M N => by simp [Matrix.add_mulVec]
      map_smul' := fun r M => by simp [Matrix.smul_mulVec] }

@[simp] lemma matMulVecCLM_apply (n : ℕ) (v : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    matMulVecCLM n v M = M.mulVec v := rfl

/-! ### Lemma 1: Matrix exponential solution satisfies the ODE -/

lemma exp_mulVec_hasDerivAt (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => (exp (s • A)).mulVec v)
      (A.mulVec ((exp (t • A)).mulVec v)) t := by
  have h1 : HasDerivAt (fun s => exp (s • A)) (exp (t • A) * A) t :=
    hasDerivAt_exp_smul_const A t
  have h2 := (matMulVecCLM n v).hasFDerivAt.comp_hasDerivAt t h1
  simp only [Function.comp_def, matMulVecCLM_apply] at h2
  convert h2 using 1
  rw [Matrix.mulVec_mulVec, ((Commute.refl A).smul_right t).exp_right.eq]

/-! ### Lemma 2: ODE uniqueness for linear systems -/

lemma linear_ode_eq_exp (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ → Fin n → ℝ)
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t)
    (t : ℝ) (ht : 1 ≤ t) :
    x t = (exp ((t - 1) • A)).mulVec (x 1) := by
  revert t;
  -- Define $g(s) = \exp((s-1)A)x(1)$ and show it satisfies the same ODE as $x$.
  set g : ℝ → Fin n → ℝ := fun s => (exp ((s - 1) • A)).mulVec (x 1)
  have hg : ∀ s > 0, HasDerivAt g (A.mulVec (g s)) s := by
    intro s hs;
    convert HasFDerivAt.hasDerivAt ( HasFDerivAt.comp s ( show HasFDerivAt ( fun t => ( exp ( t • A ) |> Matrix.mulVec ) ( x 1 ) ) _ _ from ( exp_mulVec_hasDerivAt n A ( x 1 ) _ |> HasDerivAt.hasFDerivAt ) ) ( HasFDerivAt.sub ( hasFDerivAt_id s ) ( hasFDerivAt_const _ _ ) ) ) using 1;
    aesop;
  -- Apply ODE_solution_unique_of_mem_Icc_right with $a = 1$, $b = T$, $f = x$, $g = g$, and $v(t, y) = A.mulVec(y)$.
  have h_unique : ∀ T > 1, x 1 = g 1 → ∀ t ∈ Set.Icc 1 T, x t = g t := by
    intros T hT hx1 t ht;
    have h_unique : ∀ t ∈ Set.Icc 1 T, x t = g t := by
      have h_cont : ContinuousOn x (Set.Icc 1 T) ∧ ContinuousOn g (Set.Icc 1 T) := by
        exact ⟨ continuousOn_of_forall_continuousAt fun t ht => HasDerivAt.continuousAt ( hx t <| by linarith [ ht.1 ] ), continuousOn_of_forall_continuousAt fun t ht => HasDerivAt.continuousAt ( hg t <| by linarith [ ht.1 ] ) ⟩
      have h_deriv : ∀ t ∈ Set.Ico 1 T, HasDerivWithinAt x (A.mulVec (x t)) (Set.Ici t) t ∧ HasDerivWithinAt g (A.mulVec (g t)) (Set.Ici t) t := by
        exact fun t ht => ⟨ HasDerivAt.hasDerivWithinAt ( hx t ( by linarith [ ht.1 ] ) ), HasDerivAt.hasDerivWithinAt ( hg t ( by linarith [ ht.1 ] ) ) ⟩
      have h_unique : Set.EqOn x g (Set.Icc 1 T) := by
        have h_lip : ∀ t ∈ Set.Ico 1 T, LipschitzOnWith (⟨‖(A.mulVecLin).toContinuousLinearMap‖₊, by
          positivity⟩ : NNReal) (fun y => A.mulVec y) (Set.univ : Set (Fin n → ℝ)) := by
          intro t ht;
          convert ( ContinuousLinearMap.lipschitz ( LinearMap.toContinuousLinearMap A.mulVecLin ) ) using 1;
          exact lipschitzOnWith_univ
        apply ODE_solution_unique_of_mem_Icc_right;
        any_goals tauto;
        · exact fun t ht => h_deriv t ht |>.1;
        · exact fun t ht => h_deriv t ht |>.2;
      exact h_unique;
    exact h_unique t ht;
  simp +zetaDelta at *;
  exact fun t ht => h_unique ( t + 1 ) ( by linarith ) t ht ( by linarith )

/-! ### Lemma 3: Exponential decay for Hurwitz matrices -/

lemma exp_mulVec_tendsto_zero (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    (v : Fin n → ℝ) :
    Filter.Tendsto (fun t : ℝ => (exp (t • A)).mulVec v) Filter.atTop (nhds 0) := by
  -- Reduce to complex case
  have h_complex := exp_mulVec_tendsto_zero_complex (A.map Complex.ofReal) hA (fun i => (v i : ℂ))
  -- Norm equality: ‖real‖ = ‖complex embedding‖
  have h_norm : ∀ t : ℝ, ‖(exp (t • A)).mulVec v‖ =
      ‖(exp ((↑t : ℂ) • A.map Complex.ofReal)).mulVec (fun i => (↑(v i) : ℂ))‖ := by
    intro t
    simp only [Pi.norm_def, NNReal.coe_inj, Matrix.mulVec, dotProduct]
    apply Finset.sup_congr rfl; intro i _
    suffices h : (∑ j, (exp ((↑t : ℂ) • A.map Complex.ofReal)) i j * (↑(v j) : ℂ)) =
        ↑(∑ j, (exp (t • A)) i j * v j) by
      rw [h, Complex.nnnorm_real]
    rw [Complex.ofReal_sum]; congr 1; ext j; push_cast; congr 1
    have hcont : Continuous ((algebraMap ℝ ℂ).mapMatrix :
        Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℂ) :=
      continuous_id.matrix_map Complex.continuous_ofReal
    have h_exp := map_exp (algebraMap ℝ ℂ).mapMatrix hcont (t • A)
    simp only [RingHom.mapMatrix_apply] at h_exp
    have h2 : (exp (t • A)).map (algebraMap ℝ ℂ) = exp ((↑t : ℂ) • A.map Complex.ofReal) := by
      rw [h_exp]; congr 1; ext i' j'; simp [Matrix.map_apply, Complex.ofReal_mul]
    have h3 := congr_fun (congr_fun h2 i) j
    simp [Matrix.map_apply] at h3
    exact h3.symm
  -- Conclude: ‖f(t)‖ → 0 iff f(t) → 0
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h2 := h_complex.norm
  simp only [norm_zero] at h2
  exact h2.congr (fun t => (h_norm t).symm)

end Submission