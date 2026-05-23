import Mathlib

/-!
# Trace infrastructure for the Wedderburn-based column orthogonality proof
-/

set_option maxHeartbeats 25600000

open scoped Classical
noncomputable section

namespace Submission.PeterWeylTrace

/-! ## Trace of left multiplication on matrix algebras -/

def leftMulLM (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  (Algebra.lmul ℂ (Matrix (Fin d) (Fin d) ℂ)) A

lemma trace_leftMul_matrix (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.trace ℂ _ (leftMulLM d A) = d * Matrix.trace A := by
  convert LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin d) (Fin d))
      ((Algebra.lmul ℂ (Matrix (Fin d) (Fin d) ℂ)) A) using 1
  have h_diag : ∀ i j : Fin d,
      (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin d) (Fin d))
        (Matrix.stdBasis ℂ (Fin d) (Fin d))
        ((Algebra.lmul ℂ (Matrix (Fin d) (Fin d) ℂ)) A)) (i, j) (i, j) = A i i := by
    intro i j; erw [LinearMap.toMatrix_apply]; simp +decide [Matrix.mul_apply, Matrix.stdBasis]
    rw [Finset.sum_eq_single i] <;> aesop
  simp_all +decide [Matrix.trace, Finset.mul_sum _ _ _]
  erw [Finset.sum_product]; simp +decide [← Finset.mul_sum _ _ _, ← Finset.sum_mul]

lemma trace_lmul_matrix (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.trace ℂ _ ((Algebra.lmul ℂ (Matrix (Fin d) (Fin d) ℂ)) A) =
    (d : ℂ) * Matrix.trace A :=
  trace_leftMul_matrix d A

/-! ## Trace preserved by algebra isomorphism -/

lemma trace_lmul_algEquiv {A B : Type*}
    [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    [Module.Free ℂ A] [Module.Finite ℂ A]
    [Module.Free ℂ B] [Module.Finite ℂ B]
    (e : A ≃ₐ[ℂ] B) (a : A) :
    LinearMap.trace ℂ A ((Algebra.lmul ℂ A) a) =
    LinearMap.trace ℂ B ((Algebra.lmul ℂ B) (e a)) := by
  convert (LinearMap.trace_conj' _ _)
  swap
  exact e.symm.toLinearEquiv
  ext; simp +decide [Algebra.lmul, e.symm_apply_apply]

/-! ## Trace of group element on MonoidAlgebra -/

lemma trace_lmul_single_eq_zero (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (g : G) (hg : g ≠ 1) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
      ((Algebra.lmul ℂ (MonoidAlgebra ℂ G)) (MonoidAlgebra.single g 1)) = 0 := by
  have h_diag_zero : ∀ h : G,
      (Algebra.lmul ℂ (MonoidAlgebra ℂ G) (MonoidAlgebra.single g 1))
        (MonoidAlgebra.single h 1) = MonoidAlgebra.single (g * h) 1 := by
    simp +decide [Algebra.lmul]
  convert LinearMap.trace_eq_matrix_trace ℂ (Finsupp.basisSingleOne) _
  all_goals try infer_instance
  refine' Eq.symm (Finset.sum_eq_zero fun h _ => _)
  simp +decide [LinearMap.toMatrix_apply]
  convert congr_arg (fun x : MonoidAlgebra ℂ G => x h) (h_diag_zero h) using 1
  rw [MonoidAlgebra.single_apply]; aesop

/-! ## Trace on product of matrix algebras

We prove this for the specific case of matrix algebras to avoid module instance diamonds.
-/

lemma trace_lmul_pi_matrix {n : ℕ} (d : Fin n → ℕ)
    (a : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    LinearMap.trace ℂ _ ((Algebra.lmul ℂ (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) a) =
    ∑ i, LinearMap.trace ℂ _ ((Algebra.lmul ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)) (a i)) := by
  -- The left multiplication on a product of matrix algebras acts componentwise: $(a * b) i = a i * b i$.
  have h_lmul : (Algebra.lmul ℂ ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ)) a = (LinearMap.pi (fun i => (Algebra.lmul ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)) (a i) ∘ₗ LinearMap.proj i)) := by
    ext; simp +decide [ Algebra.smul_def ] ;
  rw [ h_lmul ];
  have h_trace_block_diag : ∀ (f : (i : Fin n) → Module.End ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ)), LinearMap.trace ℂ ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ) (LinearMap.pi (fun i => f i ∘ₗ LinearMap.proj i)) = ∑ i, LinearMap.trace ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) (f i) := by
    intro f;
    -- By definition of the trace, we can write
    have h_trace_def : ∀ (g : Module.End ℂ ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ)), LinearMap.trace ℂ ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) ℂ) g = ∑ i, ∑ j, (LinearMap.toMatrix (Pi.basis (fun i => Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i)))) (Pi.basis (fun i => Matrix.stdBasis ℂ (Fin (d i)) (Fin (d i)))) g) (⟨i, j⟩ : (i : Fin n) × (Fin (d i) × Fin (d i))) (⟨i, j⟩ : (i : Fin n) × (Fin (d i) × Fin (d i))) := by
      intro g;
      convert LinearMap.trace_eq_matrix_trace ℂ ( Pi.basis fun i => Matrix.stdBasis ℂ ( Fin ( d i ) ) ( Fin ( d i ) ) ) g using 1;
      simp +decide [ Matrix.trace ];
      rw [Fintype.sum_sigma];
    rw [ h_trace_def ];
    refine' Finset.sum_congr rfl fun i _ => _;
    rw [ LinearMap.trace_eq_matrix_trace ℂ ( Matrix.stdBasis ℂ ( Fin ( d i ) ) ( Fin ( d i ) ) ) ];
    simp +decide [ LinearMap.toMatrix_apply, Matrix.trace ];
  exact h_trace_block_diag _

/-! ## The Wedderburn column identity -/

/-- For g ≠ 1, ∑ d_i * Matrix.trace(π_i(g)) = 0 via the Wedderburn decomposition. -/
lemma wedderburn_column_identity (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (g : G) (hg : g ≠ 1)
    (n : ℕ) (d : Fin n → ℕ) (_hd : ∀ i, NeZero (d i))
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∑ i, (d i : ℂ) * Matrix.trace ((e (MonoidAlgebra.single g 1)) i) = 0 := by
  have h1 := trace_lmul_single_eq_zero G g hg
  rw [trace_lmul_algEquiv e] at h1
  rw [trace_lmul_pi_matrix] at h1
  simp_rw [trace_lmul_matrix] at h1
  exact h1

end Submission.PeterWeylTrace