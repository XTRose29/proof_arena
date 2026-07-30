import Mathlib

namespace Submission.Monodromy

def trefoil : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, -1; 1, 1]

def trefoilInv : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; -1, 0]

@[simp] theorem trefoil_mul_trefoilInv : trefoil * trefoilInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [trefoil, trefoilInv, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem trefoilInv_mul_trefoil : trefoilInv * trefoil = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [trefoil, trefoilInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem no_det_one_conjugacy (P : Matrix (Fin 2) (Fin 2) ℤ)
    (hconj : P * trefoil = trefoilInv * P) (hdet : P.det = 1) : False := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hconj
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hconj
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hconj
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hconj
  norm_num [trefoil, trefoilInv, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at hdet
  rw [h00, h10] at hdet
  have hnonneg : 0 ≤
      P 0 0 ^ 2 + P 0 0 * P 1 0 + P 1 0 ^ 2 := by
    nlinarith [sq_nonneg (2 * P 0 0 + P 1 0), sq_nonneg (P 1 0)]
  nlinarith

end Submission.Monodromy
