import Mathlib
import Submission.PerronCore

namespace Submission.Helpers

open scoped NNReal
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonneg eigenvector of a nonneg irreducible matrix must be positive. -/
lemma nonneg_eigenvec_is_pos {A : Matrix n n ℝ}
    (hA_irr : A.IsIrreducible)
    {rho : ℝ} {v : n → ℝ} (hv_nn : ∀ i, 0 ≤ v i) (hv_nz : v ≠ 0)
    (hAv : A.mulVec v = rho • v) (hrho : 0 ≤ rho) :
    ∀ i, 0 < v i := by
  have h_zero_mul : ∀ i, v i = 0 → ∀ j, A i j > 0 → v j = 0 := by
    intro i hi j hj; replace hAv := congr_fun hAv i; simp_all +decide [ Matrix.mulVec, dotProduct ]
    rw [ Finset.sum_eq_zero_iff_of_nonneg ] at hAv
    · simpa [ hj.ne' ] using hAv j ( Finset.mem_univ j )
    · intro k hk; by_cases hk' : A i k ≥ 0 <;> simp_all +decide [ mul_nonneg_iff ]
      grind +splitIndPred
  have h_zero_pow : ∀ i, v i = 0 → ∀ k > 0, ∀ j, 0 < (A^k) i j → v j = 0 := by
    intro i hi k hk j hj
    induction' k with k ih generalizing i j
    · contradiction
    · contrapose! hj
      rw [ pow_succ', Matrix.mul_apply ]
      refine' Finset.sum_nonpos fun x hx => _
      by_cases hk0 : k = 0
      · simp_all +decide [ Matrix.one_apply ]
        split_ifs <;> simp_all +decide [ funext_iff ]
        exact le_of_not_gt fun h => hj <| h_zero_mul i hi j h
      · by_cases hAx : A i x > 0
        · exact mul_nonpos_of_nonneg_of_nonpos ( le_of_lt hAx )
            ( le_of_not_gt fun h => hj <| ih x ( h_zero_mul i hi x hAx )
              ( Nat.pos_of_ne_zero hk0 ) j h )
        · exact mul_nonpos_of_nonpos_of_nonneg ( le_of_not_gt hAx )
            (pow_apply_nonneg (fun i j => hA_irr.1 i j) k x j)
  have h_irred : ∀ i j, ∃ k > 0, 0 < (A^k) i j := by
    exact (Matrix.isIrreducible_iff_exists_pow_pos hA_irr.1).mp hA_irr
  contrapose! hv_nz
  exact funext fun j => by
    obtain ⟨ i, hi ⟩ := hv_nz
    obtain ⟨ k, hk₀, hk ⟩ := h_irred i j
    exact h_zero_pow i ( le_antisymm hi ( hv_nn i ) ) k hk₀ j hk

/-
|mu| ≤ rho for any real eigenvalue mu when there's a positive
    eigenvector with eigenvalue rho for a nonneg matrix.
-/
lemma abs_eigenvalue_le {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {rho : ℝ} {v : n → ℝ} (hv : ∀ i, 0 < v i)
    (hAv : A.mulVec v = rho • v)
    {mu : ℝ} {w : n → ℝ} (hw : w ≠ 0)
    (hAw : A.mulVec w = mu • w) :
    |mu| ≤ rho := by
  -- Choose i₀ maximizing |w i| / v i over all i.
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ∀ i, abs (w i) / v i ≤ abs (w i₀) / v i₀ := by
    simpa using Finset.exists_max_image Finset.univ ( fun i => |w i| / v i ) ⟨ Classical.choose ( Function.ne_iff.mp hw ), Finset.mem_univ _ ⟩;
  -- Then for all j: |w j| ≤ (|w i₀| / v i₀) * v j (from the maximality).
  have h_bound : ∀ j, abs (w j) ≤ (abs (w i₀) / v i₀) * v j := by
    exact fun j => by rw [ ← div_le_iff₀ ( hv j ) ] ; exact hi₀ j;
  -- Then |mu| * |w i₀| = |mu * w i₀| = |(Aw)_{i₀}| = |∑_j A_{i₀,j} * w_j| ≤ ∑_j A_{i₀,j} * |w_j| ≤ ∑_j A_{i₀,j} * (|w i₀| / v i₀) * v j = (|w i₀| / v i₀) * ∑_j A_{i₀,j} * v j = (|w i₀| / v i₀) * rho * v i₀ = rho * |w i₀|.
  have h_sum : abs mu * abs (w i₀) ≤ (∑ j, A i₀ j * abs (w j)) := by
    have h_sum : abs (mu * w i₀) ≤ ∑ j, A i₀ j * abs (w j) := by
      have h_abs_mu_le_rho : abs (mu * w i₀) = abs (∑ j, A i₀ j * w j) := by
        exact congr_arg _ ( by simpa [ Matrix.mulVec, dotProduct ] using congr_fun hAw i₀ |> Eq.symm );
      exact h_abs_mu_le_rho.symm ▸ le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun j _ => by rw [ abs_mul, abs_of_nonneg ( hA i₀ j ) ] );
    rwa [ abs_mul ] at h_sum;
  -- Since $\sum_j A_{i₀,j} * v j = \rho * v i₀$, we can substitute this into the inequality.
  have h_subst : ∑ j, A i₀ j * abs (w j) ≤ (abs (w i₀) / v i₀) * (rho * v i₀) := by
    have h_subst : ∑ j, A i₀ j * abs (w j) ≤ (abs (w i₀) / v i₀) * (∑ j, A i₀ j * v j) := by
      simpa only [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm ] using Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ( h_bound j ) ( hA i₀ j );
    replace hAv := congr_fun hAv i₀; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
  by_cases hi₀ : w i₀ = 0 <;> simp_all +decide [ ne_of_gt, division_def ];
  · exact False.elim ( hw ( funext h_bound ) );
  · nlinarith [ abs_pos.mpr hi₀, hv i₀, mul_inv_cancel_left₀ ( ne_of_gt ( hv i₀ ) ) ( |w i₀| * rho ) ]

/-
The eigenvalue from the Perron eigenvector is nonneg for nonneg matrices.
-/
lemma perron_eigenvalue_nonneg [Nonempty n] {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j)
    {rho : ℝ} {v : n → ℝ} (hv_pos : ∀ i, 0 < v i)
    (hAv : A.mulVec v = rho • v) :
    0 ≤ rho := by
  have h := congr_fun hAv ( Classical.arbitrary n ) ; simp_all +decide [ Matrix.mulVec, dotProduct ];
  nlinarith [ hv_pos ( Classical.arbitrary n ), show 0 ≤ ∑ x, A ( Classical.arbitrary n ) x * v x from Finset.sum_nonneg fun _ _ => mul_nonneg ( hA _ _ ) ( le_of_lt ( hv_pos _ ) ) ]

/-
An eigenvalue of a matrix is in its spectrum.
-/
lemma eigenvalue_mem_spectrum [Nonempty n]
    (A : Matrix n n ℝ) (mu : ℝ) (v : n → ℝ) (hv : v ≠ 0)
    (hAv : A.mulVec v = mu • v) :
    mu ∈ spectrum ℝ A := by
  contrapose! hv;
  simp_all +decide [ spectrum.notMem_iff ];
  -- Since $A - \mu I$ is invertible, we have $(A - \mu I)v = 0$ implies $v = 0$.
  have h_inv : (A - mu • 1).mulVec v = 0 := by
    simp_all +decide [ Matrix.sub_mulVec, Matrix.smul_eq_diagonal_mul ];
  have h_inv : Invertible (A - mu • 1) := by
    convert hv.neg.invertible using 1 ; ext i j ; simp +decide [ Algebra.algebraMap_eq_smul_one ];
  simpa using congr_arg ( fun x => h_inv.1.mulVec x ) ‹ ( A - mu • 1 ) *ᵥ v = 0 ›

/-
For nonneg matrix, if ρ has a positive eigenvector and dominates all real eigenvalues,
    then ρ equals the spectral radius.
-/
lemma perron_root_eq_spectralRadius [Nonempty n]
    (A : Matrix n n ℝ)
    (hA : ∀ i j, 0 ≤ A i j)
    {rho : ℝ} {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i)
    (hAv : A.mulVec v = rho • v)
    (hrho_nn : 0 ≤ rho)
    (hdom : ∀ mu : ℝ, mu ∈ spectrum ℝ A → ‖mu‖₊ ≤ ‖rho‖₊) :
    (spectralRadius ℝ A).toReal = rho := by
  have h_eq : rho ∈ spectrum ℝ A := by
    apply eigenvalue_mem_spectrum;
    exacts [ ne_of_apply_ne ( fun x => x ( Classical.arbitrary n ) ) ( ne_of_gt ( hv_pos _ ) ), hAv ];
  have h_eq : spectralRadius ℝ A = ‖rho‖₊ := by
    refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ _ <;> norm_num;
    · exact ⟨ _, ⟨ rho, rfl ⟩ ⟩;
    · exact hdom;
    · exact fun w hw => ⟨ rho, by simpa [ h_eq ] using hw ⟩;
  aesop

/-
From spectrum membership, extract an eigenvector.
-/
lemma eigenvector_from_spectrum [Nonempty n]
    (A : Matrix n n ℝ) (mu : ℝ)
    (hmu : mu ∈ spectrum ℝ A) :
    ∃ w : n → ℝ, w ≠ 0 ∧ A.mulVec w = mu • w := by
  -- By definition of the spectrum, there exists a non-zero vector $w$ such that $(A - \mu I)w = 0$.
  have h_spectrum : ∃ w : n → ℝ, w ≠ 0 ∧ (A - Matrix.diagonal (fun _ => mu)).mulVec w = 0 := by
    have h_spectrum : Matrix.det (A - Matrix.diagonal (fun _ => mu)) = 0 := by
      have h_not_unit : ¬ IsUnit (A - Matrix.diagonal (fun _ => mu)) := by
        exact fun h => hmu <| by simpa [ neg_sub ] using h.neg;
      exact not_not.mp fun h => h_not_unit <| Matrix.isUnit_iff_isUnit_det _ |>.2 <| isUnit_iff_ne_zero.2 h
    generalize_proofs at *;
    convert Matrix.exists_mulVec_eq_zero_iff.mpr h_spectrum
  generalize_proofs at *; (
  simp_all +decide [ sub_eq_iff_eq_add, Matrix.sub_mulVec ])

/-
For Subsingleton n, perron_frobenius_core is trivial.
-/
lemma perron_frobenius_subsingleton [Nonempty n] [Subsingleton n]
    (A : Matrix n n ℝ) (hA : A.IsIrreducible) :
    ∃ (rho : ℝ) (v : n → ℝ),
      0 ≤ rho ∧ (∀ i, 0 ≤ v i) ∧ v ≠ 0 ∧ A.mulVec v = rho • v := by
  refine' ⟨ A ( Classical.arbitrary _ ) ( Classical.arbitrary _ ), fun _ => 1, _, _, _, _ ⟩ <;> norm_num;
  · convert hA.1 _ _;
  · exact fun h => by simpa using congr_fun h ( Classical.arbitrary n ) ;
  · ext i; simp +decide [ Matrix.mulVec, dotProduct ];
    rw [ Finset.sum_eq_single ( Classical.arbitrary n ) ] <;> simp +decide [ Subsingleton.elim i ( Classical.arbitrary n ) ];
    exact fun j hj => False.elim <| hj <| Subsingleton.elim _ _

/-- For Nontrivial n, use the Perron-Frobenius argument. -/
lemma perron_frobenius_nontrivial [Nonempty n] [Nontrivial n]
    (A : Matrix n n ℝ) (hA : A.IsIrreducible) :
    ∃ (rho : ℝ) (v : n → ℝ),
      0 ≤ rho ∧ (∀ i, 0 ≤ v i) ∧ v ≠ 0 ∧ A.mulVec v = rho • v := by
  exact Submission.PerronCore.perron_frobenius_nontrivial_core A hA

/-- Core Perron-Frobenius: existence of nonneg eigenvalue with nonneg eigenvector
    for a nonneg irreducible matrix. -/
lemma perron_frobenius_core [Nonempty n] (A : Matrix n n ℝ) (hA : A.IsIrreducible) :
    ∃ (rho : ℝ) (v : n → ℝ),
      0 ≤ rho ∧ (∀ i, 0 ≤ v i) ∧ v ≠ 0 ∧ A.mulVec v = rho • v := by
  by_cases hsub : Subsingleton n
  · exact perron_frobenius_subsingleton A hA
  · haveI : Nontrivial n := not_subsingleton_iff_nontrivial.mp hsub
    exact perron_frobenius_nontrivial A hA

end Submission.Helpers