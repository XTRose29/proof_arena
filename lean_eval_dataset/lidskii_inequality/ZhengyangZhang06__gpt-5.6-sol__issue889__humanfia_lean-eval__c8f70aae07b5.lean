import Mathlib
import Submission.SpectralPath

open Matrix

namespace Submission

theorem lidskii_inequality {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {p : ℝ} (_hp : 1 ≤ p) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ^ p ≤
      ∑ j, |(hB.sub hA).eigenvalues₀ j| ^ p := by
  let hC : (B - A).IsHermitian := hB.sub hA
  let hTA : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let hTC : (B - A).toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hC
  let hTB : B.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hmat : A + (B - A) = B := by
    ext i j
    simp
  have hlin : A.toEuclideanLin + (B - A).toEuclideanLin = B.toEuclideanLin := by
    rw [← map_add, hmat]
  have heigB :
      (hTA.add hTC).eigenvalues finrank_euclideanSpace =
        hTB.eigenvalues finrank_euclideanSpace :=
    SpectralPath.eigenvalues_eq_of_eq (hTA.add hTC) hTB
      finrank_euclideanSpace hlin
  have h := SpectralPath.sum_abs_eigenvalues_add_sub_le
    hTA hTC finrank_euclideanSpace _hp
  rw [heigB] at h
  simpa only [Matrix.IsHermitian.eigenvalues₀, abs_sub_comm] using h

end Submission
