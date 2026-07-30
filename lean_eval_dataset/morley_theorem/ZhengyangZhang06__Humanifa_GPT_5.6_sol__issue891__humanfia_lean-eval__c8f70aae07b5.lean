import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry.Morley
open scoped EuclideanGeometry

namespace Submission

theorem morley_theorem (A B C P Q R : Plane)
    (h : IsMorleyConfiguration A B C P Q R) :
    IsEquilateralTriple P Q R := by
  rcases h with
    ⟨hncol, _, _, _, ha₀, ha₁, ha₂, ha₃, hb₀, hb₁, hb₂, hb₃,
      hc₀, hc₁, hc₂, hc₃⟩
  let α : ℝ := ∠ P A B
  let β : ℝ := ∠ Q B C
  let γ : ℝ := ∠ R C A

  have hα : 0 < α := by
    dsimp [α]
    linarith
  have hβ : 0 < β := by
    dsimp [β]
    linarith
  have hγ : 0 < γ := by
    dsimp [γ]
    linarith
  have hA : 3 * α = ∠ C A B := by simpa [α] using ha₃
  have hB : 3 * β = ∠ A B C := by simpa [β] using hb₃
  have hC : 3 * γ = ∠ B C A := by simpa [γ] using hc₃

  have hAB : A ≠ B := ne₁₂_of_not_collinear hncol
  have hBC : B ≠ C := ne₂₃_of_not_collinear hncol
  have hAC : A ≠ C := ne₁₃_of_not_collinear hncol
  have houterAngles :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi C hAB.symm
  have hsum : α + β + γ = Real.pi / 3 := by
    rw [← hA, ← hB, ← hC] at houterAngles
    linarith

  have hsinα : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have hsinβ : 0 < Real.sin β :=
    Real.sin_pos_of_pos_of_lt_pi hβ (by linarith [Real.pi_pos])
  have hsinγ : 0 < Real.sin γ :=
    Real.sin_pos_of_pos_of_lt_pi hγ (by linarith [Real.pi_pos])
  have hsinαβ : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsinβγ : 0 < Real.sin (β + γ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsinαγ : 0 < Real.sin (α + γ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin3γ : 0 < Real.sin (3 * γ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

  let K : ℝ := dist A B / Real.sin (3 * γ)
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (dist_pos.mpr hAB) hsin3γ
  have hABK : dist A B = K * Real.sin (3 * γ) := by
    dsimp [K]
    rw [div_mul_cancel₀ _ hsin3γ.ne']

  have houterBC := EuclideanGeometry.law_sin A C B
  rw [EuclideanGeometry.angle_comm A C B, ← hC,
    EuclideanGeometry.angle_comm B A C, ← hA, dist_comm C B,
    dist_comm B A, hABK] at houterBC
  have hBCK : dist B C = K * Real.sin (3 * α) := by
    apply mul_left_cancel₀ hsin3γ.ne'
    calc
      Real.sin (3 * γ) * dist B C =
          Real.sin (3 * α) * (K * Real.sin (3 * γ)) := houterBC
      _ = Real.sin (3 * γ) * (K * Real.sin (3 * α)) := by ring

  have houterCA := EuclideanGeometry.law_sin B C A
  rw [← hC, ← hB, dist_comm C A, hABK] at houterCA
  have hCAK : dist A C = K * Real.sin (3 * β) := by
    apply mul_left_cancel₀ hsin3γ.ne'
    calc
      Real.sin (3 * γ) * dist A C =
          Real.sin (3 * β) * (K * Real.sin (3 * γ)) := houterCA
      _ = Real.sin (3 * γ) * (K * Real.sin (3 * β)) := by ring

  have hPAB : ∠ P A B = α := rfl
  have hQBC : ∠ Q B C = β := rfl
  have hRCA : ∠ R C A = γ := rfl
  have hABP : ∠ A B P = β := hb₁.trans (hb₂.trans hQBC)
  have hPBQ : ∠ P B Q = β := hb₂.trans hQBC
  have hBCQ : ∠ B C Q = γ := hc₁.trans (hc₂.trans hRCA)
  have hQCR : ∠ Q C R = γ := hc₂.trans hRCA
  have hCAR : ∠ C A R = α := ha₁.trans (ha₂.trans hPAB)
  have hRAP : ∠ R A P = α := ha₂.trans hPAB

  have hsumABP :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi P hAB.symm
  have hBPA : ∠ B P A = Real.pi - (α + β) := by
    rw [hABP, hPAB] at hsumABP
    linarith
  have hsumBCQ :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi Q hBC.symm
  have hCQB : ∠ C Q B = Real.pi - (β + γ) := by
    rw [hBCQ, hQBC] at hsumBCQ
    linarith
  have hsumACR :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi R hAC.symm
  have hCRA : ∠ C R A = Real.pi - (α + γ) := by
    rw [EuclideanGeometry.angle_comm A C R, hRCA,
      EuclideanGeometry.angle_comm R A C, hCAR] at hsumACR
    linarith

  have lawBP := EuclideanGeometry.law_sin A P B
  rw [EuclideanGeometry.angle_comm A P B, hBPA, Real.sin_pi_sub,
    EuclideanGeometry.angle_comm B A P, hPAB, dist_comm P B,
    dist_comm B A, hABK] at lawBP
  have hBP := Helpers.solve_sine_law α β γ K (dist B P)
    hsum hsinαβ.ne' lawBP

  have lawBQ := EuclideanGeometry.law_sin C Q B
  rw [hCQB, Real.sin_pi_sub, hBCQ, dist_comm Q B, hBCK] at lawBQ
  have hBQ := Helpers.solve_sine_law γ β α K (dist B Q)
    (by linarith) (by simpa [add_comm] using hsinβγ.ne')
    (by simpa [add_comm] using lawBQ)

  have lawCQ := EuclideanGeometry.law_sin B Q C
  rw [EuclideanGeometry.angle_comm B Q C, hCQB, Real.sin_pi_sub,
    EuclideanGeometry.angle_comm C B Q, hQBC, dist_comm Q C,
    dist_comm C B, hBCK] at lawCQ
  have hCQ := Helpers.solve_sine_law β γ α K (dist C Q)
    (by linarith) hsinβγ.ne' lawCQ

  have lawCR := EuclideanGeometry.law_sin A R C
  rw [EuclideanGeometry.angle_comm A R C, hCRA, Real.sin_pi_sub,
    hCAR, dist_comm R C, dist_comm C A, hCAK] at lawCR
  have hCR := Helpers.solve_sine_law α γ β K (dist C R)
    (by linarith) hsinαγ.ne' lawCR

  have lawAR := EuclideanGeometry.law_sin C R A
  rw [hCRA, Real.sin_pi_sub, EuclideanGeometry.angle_comm A C R,
    hRCA, dist_comm R A, hCAK] at lawAR
  have hAR := Helpers.solve_sine_law γ α β K (dist A R)
    (by linarith) (by simpa [add_comm] using hsinαγ.ne')
    (by simpa [add_comm] using lawAR)

  have lawAP := EuclideanGeometry.law_sin B P A
  rw [hBPA, Real.sin_pi_sub, hABP, dist_comm P A, hABK] at lawAP
  have hAP := Helpers.solve_sine_law β α γ K (dist A P)
    (by linarith) (by simpa [add_comm] using hsinαβ.ne')
    (by simpa [add_comm] using lawAP)

  have hPQ := Helpers.dist_eq_scaled_sin B P Q
    (4 * K * Real.sin α * Real.sin γ)
    (Real.pi / 3 + γ) (Real.pi / 3 + α) β hBP
    (by
      calc
        dist B Q =
            (4 * K * Real.sin γ * Real.sin α) *
              Real.sin (Real.pi / 3 + α) := hBQ
        _ = (4 * K * Real.sin α * Real.sin γ) *
            Real.sin (Real.pi / 3 + α) := by ring)
    hPBQ
    (by linarith) (by positivity) hsinβ.le

  have hQR := Helpers.dist_eq_scaled_sin C Q R
    (4 * K * Real.sin α * Real.sin β)
    (Real.pi / 3 + α) (Real.pi / 3 + β) γ
    (by
      calc
        dist C Q =
            (4 * K * Real.sin β * Real.sin α) *
              Real.sin (Real.pi / 3 + α) := hCQ
        _ = (4 * K * Real.sin α * Real.sin β) *
            Real.sin (Real.pi / 3 + α) := by ring)
    hCR hQCR
    (by linarith) (by positivity) hsinγ.le

  have hRP := Helpers.dist_eq_scaled_sin A R P
    (4 * K * Real.sin β * Real.sin γ)
    (Real.pi / 3 + β) (Real.pi / 3 + γ) α
    (by
      calc
        dist A R =
            (4 * K * Real.sin γ * Real.sin β) *
              Real.sin (Real.pi / 3 + β) := hAR
        _ = (4 * K * Real.sin β * Real.sin γ) *
            Real.sin (Real.pi / 3 + β) := by ring)
    hAP hRAP
    (by linarith) (by positivity) hsinα.le

  have hPQcommon :
      dist P Q = 4 * K * Real.sin α * Real.sin β * Real.sin γ := by
    calc
      dist P Q =
          (4 * K * Real.sin α * Real.sin γ) * Real.sin β := hPQ
      _ = 4 * K * Real.sin α * Real.sin β * Real.sin γ := by ring
  have hQRcommon :
      dist Q R = 4 * K * Real.sin α * Real.sin β * Real.sin γ := hQR
  have hRPcommon :
      dist R P = 4 * K * Real.sin α * Real.sin β * Real.sin γ := by
    calc
      dist R P =
          (4 * K * Real.sin β * Real.sin γ) * Real.sin α := hRP
      _ = 4 * K * Real.sin α * Real.sin β * Real.sin γ := by ring
  exact ⟨hPQcommon.trans hQRcommon.symm, hQRcommon.trans hRPcommon.symm⟩

end Submission
