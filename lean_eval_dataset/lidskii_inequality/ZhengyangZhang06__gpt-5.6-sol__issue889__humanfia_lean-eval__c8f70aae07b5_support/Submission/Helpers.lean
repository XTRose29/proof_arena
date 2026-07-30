import Mathlib

namespace Submission.Helpers

open scoped InnerProductSpace

open Module

private lemma finrank_basis_flag {K E : Type*} [DivisionRing K] [AddCommGroup E]
    [Module K E] {N : ℕ} (b : Basis (Fin N) K E) (k : Fin (N + 1)) :
    finrank K (b.flag k) = k := by
  classical
  rw [Module.Basis.flag]
  have hr : b '' {i | i.castSucc < k} =
      Set.range (fun i : {i : Fin N // i.castSucc < k} ↦ b i) := by
    ext x
    simp
  rw [hr, finrank_span_eq_card]
  · let e : {i : Fin N // i.castSucc < k} ≃ Fin k :=
      { toFun := fun i ↦ ⟨i, i.2⟩
        invFun := fun i ↦
          ⟨⟨i, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩, i.isLt⟩
        left_inv := by intro i; simp
        right_inv := by intro i; simp }
    simpa using Fintype.card_congr e
  · exact b.linearIndependent.comp _ Subtype.val_injective

private lemma re_inner_apply_eq_sum {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} {T : E →ₗ[K] E} (hT : T.IsSymmetric) (hn : finrank K E = N) (x : E) :
    RCLike.re ⟪x, T x⟫_K =
      ∑ j, hT.eigenvalues hn j * ‖(hT.eigenvectorBasis hn).repr x j‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map x (T x), PiLp.inner_apply, map_sum]
  apply Fintype.sum_congr
  intro j
  rw [hT.eigenvectorBasis_apply_self_apply]
  rw [RCLike.inner_apply, mul_assoc, RCLike.mul_conj]
  simp

private lemma eigenvalue_mul_norm_sq_le_of_mem_flag {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} {T : E →ₗ[K] E} (hT : T.IsSymmetric) (hn : finrank K E = N)
    (i : Fin N) (x : E)
    (hx : x ∈ (hT.eigenvectorBasis hn).toBasis.flag i.succ) :
    hT.eigenvalues hn i * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T x⟫_K := by
  let b := hT.eigenvectorBasis hn
  calc
    hT.eigenvalues hn i * ‖x‖ ^ 2 =
        ∑ j, hT.eigenvalues hn i * ‖b.repr x j‖ ^ 2 := by
      rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    _ ≤ ∑ j, hT.eigenvalues hn j * ‖b.repr x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hji : j ≤ i
      · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hji) (sq_nonneg _)
      · have hij : i.succ ≤ j.castSucc := by
          change i.val + 1 ≤ j.val
          omega
        have hz' : b.toBasis.repr x j = 0 := b.toBasis.flag_le_ker_coord hij hx
        have hz : b.repr x j = 0 := by
          simpa only [OrthonormalBasis.coe_toBasis_repr_apply] using hz'
        simp [hz]
    _ = RCLike.re ⟪x, T x⟫_K := (re_inner_apply_eq_sum hT hn x).symm

private lemma re_inner_apply_le_eigenvalue_mul_norm_sq_of_mem_orthogonal_flag
    {K E : Type*} [RCLike K] [NormedAddCommGroup E] [InnerProductSpace K E]
    [FiniteDimensional K E] {N : ℕ} {T : E →ₗ[K] E} (hT : T.IsSymmetric)
    (hn : finrank K E = N) (i : Fin N) (x : E)
    (hx : x ∈ ((hT.eigenvectorBasis hn).toBasis.flag i.castSucc)ᗮ) :
    RCLike.re ⟪x, T x⟫_K ≤ hT.eigenvalues hn i * ‖x‖ ^ 2 := by
  let b := hT.eigenvectorBasis hn
  calc
    RCLike.re ⟪x, T x⟫_K =
        ∑ j, hT.eigenvalues hn j * ‖b.repr x j‖ ^ 2 := re_inner_apply_eq_sum hT hn x
    _ ≤ ∑ j, hT.eigenvalues hn i * ‖b.repr x j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i ≤ j
      · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hij) (sq_nonneg _)
      · have hjmem : b j ∈ b.toBasis.flag i.castSucc :=
          b.toBasis.self_mem_flag (by
            change j.val < i.val
            omega)
        have hzinner : ⟪b j, x⟫_K = 0 :=
          Submodule.inner_right_of_mem_orthogonal hjmem hx
        have hz : b.repr x j = 0 := by
          simpa only [OrthonormalBasis.repr_apply_apply] using hzinner
        simp [hz]
    _ = hT.eigenvalues hn i * ‖x‖ ^ 2 := by
      rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, b.repr.norm_map]

lemma eigenvalues_mono_of_re_inner_le {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} {S T : E →ₗ[K] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : finrank K E = N)
    (hST : ∀ x, RCLike.re ⟪x, S x⟫_K ≤ RCLike.re ⟪x, T x⟫_K) :
    hS.eigenvalues hn ≤ hT.eigenvalues hn := by
  intro i
  let P : Submodule K E := (hS.eigenvectorBasis hn).toBasis.flag i.succ
  let Q : Submodule K E := ((hT.eigenvectorBasis hn).toBasis.flag i.castSucc)ᗮ
  have hdimP : finrank K P = i.val + 1 := by
    simpa [P] using finrank_basis_flag (hS.eigenvectorBasis hn).toBasis i.succ
  have hdimPrefix :
      finrank K ((hT.eigenvectorBasis hn).toBasis.flag i.castSucc) = i.val := by
    simpa using finrank_basis_flag (hT.eigenvectorBasis hn).toBasis i.castSucc
  have hdimQ : finrank K Q = N - i.val := by
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [hdimPrefix, hn]
    omega
  let PQsup : Submodule K E := P ⊔ Q
  let PQinf : Submodule K E := P ⊓ Q
  have hdimSup : finrank K PQsup ≤ N := by
    rw [← hn]
    exact Submodule.finrank_le _
  have hdim : finrank K PQsup + finrank K PQinf = finrank K P + finrank K Q := by
    simpa [PQsup, PQinf] using Submodule.finrank_sup_add_finrank_inf_eq P Q
  have hdimInf : 0 < finrank K PQinf := by
    omega
  letI : Nontrivial PQinf := Module.nontrivial_of_finrank_pos hdimInf
  obtain ⟨x, hx⟩ := exists_ne (0 : PQinf)
  have hx0 : (x : E) ≠ 0 := by
    exact_mod_cast hx
  have hxnorm : 0 < ‖(x : E)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  have hlow := eigenvalue_mul_norm_sq_le_of_mem_flag hS hn i (x : E) x.2.1
  have hupp :=
    re_inner_apply_le_eigenvalue_mul_norm_sq_of_mem_orthogonal_flag hT hn i (x : E) x.2.2
  have hmiddle := hST (x : E)
  nlinarith

private lemma eigenvalues_eq_of_apply_orthonormalBasis {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} {T : E →ₗ[K] E} (hT : T.IsSymmetric) (hn : finrank K E = N)
    (b : OrthonormalBasis (Fin N) K E) (e : Fin N → ℝ) (he : Antitone e)
    (happly : ∀ i, T (b i) = (e i : K) • b i) :
    hT.eigenvalues hn = e := by
  have hmatrix : T.toMatrix b.toBasis b.toBasis =
      Matrix.diagonal (RCLike.ofReal ∘ e) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply, happly, RCLike.real_smul_eq_coe_mul]
    · simp [LinearMap.toMatrix_apply, happly, hij]
  have hchar : T.charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (e i : K)) := by
    rw [← T.charpoly_toMatrix b.toBasis, hmatrix, Matrix.charpoly_diagonal]
    simp
  have hroots : T.charpoly.roots =
      Multiset.map (RCLike.ofReal ∘ e) Finset.univ.val := by
    rw [hchar, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  rw [← List.ofFn_inj, ← hT.sort_roots_charpoly_eq_eigenvalues hn, hroots]
  simp_rw [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Function.comp_def,
    RCLike.ofReal_re, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using he.sortedGE_ofFn

lemma eigenvalues_add_real_smul_id {K E : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [FiniteDimensional K E]
    {N : ℕ} {T : E →ₗ[K] E} (hT : T.IsSymmetric) (hn : finrank K E = N) (c : ℝ)
    (hadd : (T + (c : K) • LinearMap.id).IsSymmetric) :
    hadd.eigenvalues hn = fun i ↦ hT.eigenvalues hn i + c := by
  apply eigenvalues_eq_of_apply_orthonormalBasis hadd hn (hT.eigenvectorBasis hn)
    (fun i ↦ hT.eigenvalues hn i + c)
  · exact (hT.eigenvalues_antitone hn).add_const c
  · intro i
    simp [hT.apply_eigenvectorBasis, add_smul]

end Submission.Helpers
