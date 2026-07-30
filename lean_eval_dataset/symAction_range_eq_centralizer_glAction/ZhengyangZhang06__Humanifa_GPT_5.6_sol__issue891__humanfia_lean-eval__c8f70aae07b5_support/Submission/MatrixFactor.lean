import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.GroupTheory.Perm.Fin

namespace Submission.MatrixFactor

open Matrix

private theorem diagonal_mul_permMatrix_mulVec
    {R : Type*} [CommRing R] {n : ℕ} (D : Fin n → R)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → R) (i : Fin n) :
    ((Matrix.diagonal D * σ.permMatrix R) *ᵥ v) i = D i * v (σ i) := by
  rw [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec, Matrix.mulVec_diagonal]
  rfl

private theorem diagonal_mul_permMatrix_pow_mulVec
    {R : Type*} [CommRing R] {n : ℕ} (D : Fin n → R)
    (σ : Equiv.Perm (Fin n)) (m : ℕ) (v : Fin n → R) (i : Fin n) :
    (((Matrix.diagonal D * σ.permMatrix R) ^ m) *ᵥ v) i =
      (∏ r ∈ Finset.range m, D ((σ ^ r) i)) * v ((σ ^ m) i) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, ih,
        diagonal_mul_permMatrix_mulVec]
      simp only [Equiv.Perm.coe_pow, Function.iterate_succ_apply']
      rw [Finset.prod_range_succ, mul_assoc]

private theorem exists_finRotate_pow_eq {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    ∃ r < n, ((finRotate n) ^ r) i = j := by
  rcases n with _ | n
  · simp at hn
  rcases n with _ | n
  · exact ⟨0, by simp, Fin.ext (by omega)⟩
  · let σ := finRotate (n + 2)
    have hcycle : σ.IsCycle := isCycle_finRotate
    have hcycleOn :
        σ.IsCycleOn (↑(Finset.univ : Finset (Fin (n + 2))) : Set (Fin (n + 2))) := by
      refine ⟨σ.bijOn (by simp), fun x _ y _ ↦ hcycle.sameCycle ?_ ?_⟩
      · exact Equiv.Perm.mem_support.mp <| by
          rw [support_finRotate]
          exact Finset.mem_univ x
      · exact Equiv.Perm.mem_support.mp <| by
          rw [support_finRotate]
          exact Finset.mem_univ y
    obtain ⟨r, hr, hij⟩ :=
      hcycleOn.exists_pow_eq (s := (Finset.univ : Finset (Fin (n + 2))))
        (Finset.mem_univ i) (Finset.mem_univ j)
    have hr' : r < n + 2 := by
      simpa only [Finset.card_univ, Fintype.card_fin] using hr
    exact ⟨r, hr', by simpa only [σ] using hij⟩

/-- A weighted cyclic shift with at least one zero weight is nilpotent. -/
theorem isNilpotent_diagonal_mul_finRotate
    {R : Type*} [CommRing R] {n : ℕ} (D : Fin n → R)
    (i₀ : Fin n) (hi₀ : D i₀ = 0) :
    IsNilpotent
      (Matrix.diagonal D * (finRotate n).permMatrix R) := by
  refine ⟨n, ?_⟩
  apply Matrix.mulVec_injective
  funext v i
  rw [diagonal_mul_permMatrix_pow_mulVec]
  obtain ⟨r, hr, hir⟩ :=
    exists_finRotate_pow_eq (Nat.zero_lt_of_lt i.isLt) i i₀
  have hzero :
      (∏ q ∈ Finset.range n, D (((finRotate n) ^ q) i)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hr)
    simpa only [hir] using hi₀
  simp [hzero]

theorem isUnit_permMatrix
    {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsUnit (σ.permMatrix R) := by
  refine ⟨⟨σ.permMatrix R, (σ⁻¹).permMatrix R, ?_, ?_⟩, rfl⟩
  · rw [← Matrix.permMatrix_mul]
    simp
  · rw [← Matrix.permMatrix_mul]
    simp

theorem diagonal_eq_nilpotent_mul_unit
    {R : Type*} [Field R] {n : ℕ} (D : Fin n → R)
    (hD : ¬IsUnit (Matrix.diagonal D)) :
    ∃ N U : Matrix (Fin n) (Fin n) R,
      IsNilpotent N ∧ IsUnit U ∧ Matrix.diagonal D = N * U := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det] at hD
  simp only [Matrix.det_diagonal, isUnit_iff_ne_zero] at hD
  have hprod : ∏ i, D i = 0 := not_ne_iff.mp hD
  obtain ⟨i₀, _, hi₀⟩ := Finset.prod_eq_zero_iff.mp hprod
  let σ := finRotate n
  refine ⟨Matrix.diagonal D * σ.permMatrix R, (σ⁻¹).permMatrix R,
    isNilpotent_diagonal_mul_finRotate D i₀ hi₀, isUnit_permMatrix σ⁻¹, ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.permMatrix_mul]
  simp [σ]

end Submission.MatrixFactor
