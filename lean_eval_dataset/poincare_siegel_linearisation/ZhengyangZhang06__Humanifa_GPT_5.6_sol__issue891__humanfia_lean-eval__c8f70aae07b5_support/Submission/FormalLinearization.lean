import Submission.Helpers

open Finset
open FormalMultilinearSeries

namespace Submission

/-- Multiplication by `lam`, regarded as a continuous complex-linear map. -/
noncomputable def rotationCLM (lam : ℂ) : ℂ →L[ℂ] ℂ :=
  lam • ContinuousLinearMap.id ℂ ℂ

@[simp]
theorem rotationCLM_apply (lam z : ℂ) : rotationCLM lam z = lam * z := by
  simp [rotationCLM]

/-- Coefficients of the normalized formal solution of Schröder's equation.
The coefficient in degree `n + 2` only uses coefficients in lower degrees. -/
noncomputable def linearizationCoeff (a : ℕ → ℂ) (lam : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      let q : ℕ → ℂ :=
        fun k => if k < n + 2 then linearizationCoeff a lam k else 0
      (lam ^ (n + 2) - lam)⁻¹ *
        ∑ c ∈ ({c : Composition (n + 2) | 1 < c.length}.toFinset),
          a c.length * ∏ i, q (c.blocksFun i)

@[simp]
theorem linearizationCoeff_zero (a : ℕ → ℂ) (lam : ℂ) :
    linearizationCoeff a lam 0 = 0 := by
  rw [linearizationCoeff]

@[simp]
theorem linearizationCoeff_one (a : ℕ → ℂ) (lam : ℂ) :
    linearizationCoeff a lam 1 = 1 := by
  rw [linearizationCoeff]

private theorem nonlinear_blocks_lt
    {n : ℕ} (c : Composition (n + 2)) (hc : 1 < c.length) :
    ∀ i, c.blocksFun i < n + 2 := by
  simp [← Composition.ne_single_iff (by omega : 0 < n + 2),
    Composition.eq_single_iff_length, ne_of_gt hc]

theorem linearizationCoeff_of_two_le
    (a : ℕ → ℂ) (lam : ℂ) (n : ℕ) :
    linearizationCoeff a lam (n + 2) =
      (lam ^ (n + 2) - lam)⁻¹ *
        ∑ c ∈ ({c : Composition (n + 2) | 1 < c.length}.toFinset),
          a c.length * ∏ i, linearizationCoeff a lam (c.blocksFun i) := by
  rw [linearizationCoeff]
  congr 1
  apply sum_congr rfl
  intro c hc
  simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hc
  simp [nonlinear_blocks_lt c hc]

/-- The one-dimensional formal multilinear series with the recursively
constructed linearizing coefficients. -/
noncomputable def linearizationFMS
    (a : ℕ → ℂ) (lam : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (linearizationCoeff a lam)

@[simp]
theorem linearizationFMS_coeff
    (a : ℕ → ℂ) (lam : ℂ) (n : ℕ) :
    (linearizationFMS a lam).coeff n = linearizationCoeff a lam n := by
  simp [linearizationFMS]

private theorem applyComposition_one
    (a : ℕ → ℂ) (lam : ℂ) {n : ℕ} (c : Composition n) :
    (linearizationFMS a lam).applyComposition c (fun _ => 1) =
      fun i => linearizationCoeff a lam (c.blocksFun i) := by
  funext i
  simp [FormalMultilinearSeries.applyComposition, linearizationFMS]

private theorem comp_rotation_coeff
    (a : ℕ → ℂ) (lam : ℂ) (n : ℕ) :
    ((linearizationFMS a lam).compContinuousLinearMap
      (rotationCLM lam)).coeff n =
        lam ^ n * linearizationCoeff a lam n := by
  rw [FormalMultilinearSeries.coeff]
  rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
  have hfun :
      rotationCLM lam ∘ (1 : Fin n → ℂ) = fun _ => lam := by
    funext _
    simp
  rw [hfun, linearizationFMS,
    FormalMultilinearSeries.ofScalars_apply_eq]
  simp [smul_eq_mul, mul_comm]

/-- The recursive scalar series solves Schröder's equation formally. -/
theorem comp_linearizationFMS
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (lam : ℂ)
    (hp0 : p.coeff 0 = 0)
    (hp1 : p.coeff 1 = lam)
    (hnonresonant : ∀ n : ℕ, 2 ≤ n → lam ^ n ≠ lam) :
    p.comp (linearizationFMS p.coeff lam) =
      (linearizationFMS p.coeff lam).compContinuousLinearMap
        (rotationCLM lam) := by
  let U := linearizationFMS p.coeff lam
  funext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq (p.comp U) n,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq
      (U.compContinuousLinearMap (rotationCLM lam)) n]
  congr 1
  match n with
  | 0 =>
      rw [comp_rotation_coeff]
      change (p.comp U) 0 (fun _ => 1) =
        lam ^ 0 * linearizationCoeff p.coeff lam 0
      rw [FormalMultilinearSeries.comp_coeff_zero']
      simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
        hp0, smul_zero, pow_zero,
        linearizationCoeff_zero, mul_zero]
  | 1 =>
      rw [comp_rotation_coeff]
      change (p.comp U) 1 (fun _ => 1) =
        lam ^ 1 * linearizationCoeff p.coeff lam 1
      rw [FormalMultilinearSeries.comp_coeff_one]
      simp [FormalMultilinearSeries.apply_eq_prod_smul_coeff, hp1, U]
  | n + 2 =>
      have hdenom : lam ^ (n + 2) - lam ≠ 0 :=
        sub_ne_zero.mpr (hnonresonant (n + 2) (by omega))
      rw [comp_rotation_coeff]
      change (p.comp U) (n + 2) (fun _ => 1) =
        lam ^ (n + 2) * linearizationCoeff p.coeff lam (n + 2)
      rw [FormalMultilinearSeries.comp_rightInv_aux1 (by omega)
        p U (fun _ => 1)]
      simp only [applyComposition_one,
        FormalMultilinearSeries.apply_eq_prod_smul_coeff,
        Finset.prod_const_one, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, pow_one, one_mul, hp1, U, smul_eq_mul,
        linearizationFMS_coeff]
      let S : ℂ :=
        ∑ c ∈ ({c : Composition (n + 2) | 1 < c.length}.toFinset),
          (∏ i, linearizationCoeff p.coeff lam (c.blocksFun i)) *
            p.coeff c.length
      change S + linearizationCoeff p.coeff lam (n + 2) * lam =
        lam ^ (n + 2) * linearizationCoeff p.coeff lam (n + 2)
      rw [linearizationCoeff_of_two_le]
      have hsum :
          (∑ c ∈ ({c : Composition (n + 2) | 1 < c.length}.toFinset),
            p.coeff c.length *
              ∏ i, linearizationCoeff p.coeff lam (c.blocksFun i)) = S := by
        dsimp [S]
        apply Finset.sum_congr rfl
        intro c _
        ring
      rw [hsum]
      change S + ((lam ^ (n + 2) - lam)⁻¹ * S) * lam =
        lam ^ (n + 2) * ((lam ^ (n + 2) - lam)⁻¹ * S)
      have hcancel :
          (lam ^ (n + 2) - lam) *
              ((lam ^ (n + 2) - lam)⁻¹ * S) = S := by
        rw [← mul_assoc, mul_inv_cancel₀ hdenom, one_mul]
      calc
        S + ((lam ^ (n + 2) - lam)⁻¹ * S) * lam =
            lam * ((lam ^ (n + 2) - lam)⁻¹ * S) +
              (lam ^ (n + 2) - lam) *
                ((lam ^ (n + 2) - lam)⁻¹ * S) := by
              rw [hcancel]
              ring
        _ = lam ^ (n + 2) *
              ((lam ^ (n + 2) - lam)⁻¹ * S) := by ring

end Submission
