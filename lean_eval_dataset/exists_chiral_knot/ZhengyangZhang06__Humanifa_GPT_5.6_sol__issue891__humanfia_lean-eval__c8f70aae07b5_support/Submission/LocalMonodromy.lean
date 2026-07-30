import Submission.Milnor

namespace Submission.LocalMonodromy

noncomputable section

def rotation (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c, -s; s, c]

def inverseRotation (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c, s; -s, c]

theorem intertwiner_entries (P : Matrix (Fin 2) (Fin 2) ℝ) (c s : ℝ)
    (hs : s ≠ 0)
    (hintertwine : P * inverseRotation c s = rotation c s * P) :
    P 0 1 = P 1 0 ∧ P 1 1 = -P 0 0 := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hintertwine
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hintertwine
  norm_num [rotation, inverseRotation, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  constructor
  · apply (mul_left_cancel₀ hs)
    linarith
  · apply (mul_left_cancel₀ hs)
    linarith

theorem det_intertwiner (P : Matrix (Fin 2) (Fin 2) ℝ) (c s : ℝ)
    (hs : s ≠ 0)
    (hintertwine : P * inverseRotation c s = rotation c s * P) :
    P.det = -(P 0 0 ^ 2 + P 0 1 ^ 2) := by
  obtain ⟨h01, h11⟩ := intertwiner_entries P c s hs hintertwine
  rw [Matrix.det_fin_two, h01, h11]
  ring

theorem det_intertwiner_nonpos (P : Matrix (Fin 2) (Fin 2) ℝ) (c s : ℝ)
    (hs : s ≠ 0)
    (hintertwine : P * inverseRotation c s = rotation c s * P) :
    P.det ≤ 0 := by
  rw [det_intertwiner P c s hs hintertwine]
  exact neg_nonpos.mpr (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem no_orientation_preserving_intertwiner
    (P : Matrix (Fin 2) (Fin 2) ℝ) (c s : ℝ)
    (hs : s ≠ 0)
    (hintertwine : P * inverseRotation c s = rotation c s * P)
    (hdet : 0 < P.det) : False := by
  exact (not_lt_of_ge (det_intertwiner_nonpos P c s hs hintertwine)) hdet

def fixedPointPlus : Milnor.Fiber :=
  ⟨⟨(1, 0), by simp [Complex.normSq_apply]⟩, by
    norm_num [Milnor.polynomial]⟩

def fixedPointMinus : Milnor.Fiber :=
  ⟨⟨(-1, 0), by simp [Complex.normSq_apply]⟩, by
    norm_num [Milnor.polynomial]⟩

def monodromySq (q : Milnor.Fiber) : Milnor.Fiber :=
  Milnor.fiberMonodromy (Milnor.fiberMonodromy q)

def squareWMultiplier : ℂ :=
  Complex.exp ((((4 * Real.pi / 3 : ℝ) : ℂ)) * Complex.I)

theorem monodromySq_z (q : Milnor.Fiber) :
    (monodromySq q).1.1.1 = q.1.1.1 := by
  change Milnor.rotate 3 (Real.pi / 3)
      (Milnor.rotate 3 (Real.pi / 3) q.1.1.1) = q.1.1.1
  rw [Milnor.rotate_add]
  unfold Milnor.rotate
  have harg :
      (((((3 : ℕ) : ℝ) * (Real.pi / 3 + Real.pi / 3) : ℝ) : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  rw [Complex.exp_two_pi_mul_I, one_mul]

theorem monodromySq_w (q : Milnor.Fiber) :
    (monodromySq q).1.1.2 = squareWMultiplier * q.1.1.2 := by
  change Milnor.rotate 2 (Real.pi / 3)
      (Milnor.rotate 2 (Real.pi / 3) q.1.1.2) = squareWMultiplier * q.1.1.2
  rw [Milnor.rotate_add]
  unfold Milnor.rotate squareWMultiplier
  have harg :
      (((((2 : ℕ) : ℝ) * (Real.pi / 3 + Real.pi / 3) : ℝ) : ℂ) * Complex.I) =
        ((4 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]

@[simp] theorem monodromySq_fixedPointPlus :
    monodromySq fixedPointPlus = fixedPointPlus := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact monodromySq_z fixedPointPlus
  · rw [monodromySq_w]
    simp [fixedPointPlus]

@[simp] theorem monodromySq_fixedPointMinus :
    monodromySq fixedPointMinus = fixedPointMinus := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact monodromySq_z fixedPointMinus
  · rw [monodromySq_w]
    simp [fixedPointMinus]

theorem squareWMultiplier_re : squareWMultiplier.re = -(1 / 2 : ℝ) := by
  rw [squareWMultiplier, Complex.exp_ofReal_mul_I_re]
  rw [show (4 * Real.pi / 3 : ℝ) = Real.pi + Real.pi / 3 by ring]
  simp [Real.cos_add, Real.cos_pi_div_three]

theorem squareWMultiplier_im :
    squareWMultiplier.im = -(Real.sqrt 3 / 2) := by
  rw [squareWMultiplier, Complex.exp_ofReal_mul_I_im]
  rw [show (4 * Real.pi / 3 : ℝ) = Real.pi + Real.pi / 3 by ring]
  simp [Real.sin_add, Real.sin_pi_div_three]

theorem squareWMultiplier_im_ne_zero : squareWMultiplier.im ≠ 0 := by
  rw [squareWMultiplier_im]
  exact neg_ne_zero.mpr
    (div_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num))) (by norm_num))

end

end Submission.LocalMonodromy
