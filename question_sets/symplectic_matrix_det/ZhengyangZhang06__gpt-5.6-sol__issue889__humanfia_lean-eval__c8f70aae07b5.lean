import Mathlib
import Submission.Helpers

open Matrix Module

namespace Submission

theorem symplectic_matrix_det {l R : Type*} [DecidableEq l] [Fintype l] [CommRing R]
    {A : Matrix (l ⊕ l) (l ⊕ l) R} (hA : A ∈ Matrix.symplecticGroup l R) :
    A.det = 1 := by
  classical
  let n := Fintype.card l
  let e : Fin n ≃ l := (Fintype.equivFin l).symm
  let q : Fin (2 * n) ≃ l ⊕ l := Helpers.sympIndexEquiv e
  let B : (l ⊕ l → R) →ₗ[R] (l ⊕ l → R) →ₗ[R] R :=
    Helpers.sympBilinear
  let F : (l ⊕ l → R) [⋀^Fin (2 * n)]→ₗ[R] R :=
    Helpers.pfForm B Helpers.sympBilinear_self n
  let b : Basis (Fin (2 * n)) R (l ⊕ l → R) :=
    (Pi.basisFun R (l ⊕ l)).reindex q.symm
  let rows : Fin (2 * n) → (l ⊕ l → R) := fun i ↦ A (q i)
  have hFb : F b = (-1 : R) ^ n := by
    have hb :
        (b : Fin (2 * n) → (l ⊕ l → R)) =
          fun i ↦ Pi.single (Helpers.sympIndex e i) 1 := by
      funext i
      simp [b, q, Pi.basisFun_apply, Basis.reindex_apply]
    rw [hb]
    exact Helpers.pfForm_sympBasis (R := R) n e e.injective
  rw [SymplecticGroup.mem_iff] at hA
  have hpair (i j : Fin (2 * n)) : B (rows i) (rows j) = B (b i) (b j) := by
    rw [show B (rows i) (rows j) = (A * Matrix.J l R * Aᵀ) (q i) (q j) by
      simpa [B, rows] using Helpers.sympBilinear_rows A (q i) (q j)]
    rw [hA]
    simp [B, b, q, Pi.basisFun_apply, Basis.reindex_apply]
  have hpres : F rows = F b :=
    Helpers.pfForm_congr_pairings B Helpers.sympBilinear_self n hpair
  have hbdet : b.det rows = A.det := by
    calc
      b.det rows = (Pi.basisFun R (l ⊕ l)).det (fun i ↦ A i) := by
        have hrows : rows = (fun i ↦ A i) ∘ q := by
          funext i j
          rfl
        rw [hrows]
        exact Module.Basis.det_reindex_symm (Pi.basisFun R (l ⊕ l))
          (fun i ↦ A i) q
      _ = A.det := by
        rw [Pi.basisFun_det_apply]
        congr 1
  have hscale : F rows = F b * b.det rows := by
    simpa [smul_eq_mul] using
      AlternatingMap.congr_fun (F.eq_smul_basis_det b) rows
  have hmul : (-1 : R) ^ n * A.det = (-1 : R) ^ n := by
    calc
      (-1 : R) ^ n * A.det = F b * b.det rows := by rw [hFb, hbdet]
      _ = F rows := hscale.symm
      _ = F b := hpres
      _ = (-1 : R) ^ n := hFb
  exact (isUnit_neg_one.pow n).mul_left_cancel (by simpa only [mul_one] using hmul)

end Submission
