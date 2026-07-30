import Submission.MomentRegularization

open Set
open scoped Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- The localized near/far regularizer can be chosen linearly in its two
moments.  Besides its small near-field value and its cubic far-field error,
the resulting two-dimensional family has one finite global operator bound.

The global bound is deliberately qualitative.  Its role is to control the
compact annulus between the near and far regimes, while the two displayed
small bounds retain the scale-explicit information used away from that
annulus. -/
theorem exists_linear_centeredBall_resolventMoment_regularization_near_far
    (K : Set ℂ) [CompactSpace K]
    (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (a : ℂ) (ha : a ∉ K) (x : ℂ) (R A : ℝ) (hA : 0 < A)
    (hnearDist :
      ∀ z ∈ K, dist x z ≤ R → dist a z ≤ A)
    (eNear eFar : ℝ) (heNear : 0 < eNear) (heFar : 0 < eFar) :
    ∃ (P₀ P₁ : ℂ[X])
        (u₀ u₁ : (polynomialFunctions K).topologicalClosure)
        (B : ℝ),
      0 ≤ B ∧
      ∀ m₀ m₁ : ℂ,
        let P : ℂ[X] := m₀ • P₀ + m₁ • P₁
        let u : (polynomialFunctions K).topologicalClosure :=
          m₀ • u₀ + m₁ • u₁
        (∀ z : K,
          (u : C(K, ℂ)) z =
            (a - (z : ℂ))⁻¹ * m₀ -
              (a - (z : ℂ))⁻¹ ^ 2 * m₁ +
            (a - (z : ℂ))⁻¹ ^ 3 *
              P.eval (a - (z : ℂ))⁻¹) ∧
        (∀ z : K, dist x (z : ℂ) ≤ R →
          ‖(u : C(K, ℂ)) z‖ ≤
            (‖m₀‖ + ‖m₁‖) * eNear) ∧
        (∀ z : K, 2 * A ≤ dist a (z : ℂ) →
          ‖(a - (z : ℂ))⁻¹ ^ 3 *
              P.eval (a - (z : ℂ))⁻¹‖ ≤
            (‖m₀‖ + ‖m₁‖) * eFar *
              (dist a (z : ℂ))⁻¹ ^ 3) ∧
        ∀ z : K,
          ‖(u : C(K, ℂ)) z‖ ≤
            (‖m₀‖ + ‖m₁‖) * B := by
  obtain ⟨P₀, u₀, hu₀, hnear₀, hfar₀⟩ :=
    exists_centeredBall_resolventMoment_regularization_near_far
      K hK hKc a ha x R A hA hnearDist
      1 0 eNear eFar heNear heFar
  obtain ⟨P₁, u₁, hu₁, hnear₁, hfar₁⟩ :=
    exists_centeredBall_resolventMoment_regularization_near_far
      K hK hKc a ha x R A hA hnearDist
      0 1 eNear eFar heNear heFar
  let B : ℝ :=
    max ‖(u₀ : C(K, ℂ))‖ ‖(u₁ : C(K, ℂ))‖
  have hB : 0 ≤ B := by
    exact (norm_nonneg (u₀ : C(K, ℂ))).trans
      (le_max_left _ _)
  refine ⟨P₀, P₁, u₀, u₁, B, hB, ?_⟩
  intro m₀ m₁
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    change
      m₀ * (u₀ : C(K, ℂ)) z +
          m₁ * (u₁ : C(K, ℂ)) z =
        (a - (z : ℂ))⁻¹ * m₀ -
          (a - (z : ℂ))⁻¹ ^ 2 * m₁ +
        (a - (z : ℂ))⁻¹ ^ 3 *
          (m₀ • P₀ + m₁ • P₁).eval
            (a - (z : ℂ))⁻¹
    simp only [Polynomial.eval_add, Polynomial.eval_smul,
      smul_eq_mul]
    rw [hu₀ z, hu₁ z]
    ring
  · intro z hz
    change
      ‖m₀ * (u₀ : C(K, ℂ)) z +
          m₁ * (u₁ : C(K, ℂ)) z‖ ≤
        (‖m₀‖ + ‖m₁‖) * eNear
    calc
      ‖m₀ * (u₀ : C(K, ℂ)) z +
          m₁ * (u₁ : C(K, ℂ)) z‖
          ≤ ‖m₀‖ * ‖(u₀ : C(K, ℂ)) z‖ +
              ‖m₁‖ * ‖(u₁ : C(K, ℂ)) z‖ := by
        simpa only [norm_mul] using
          norm_add_le
            (m₀ * (u₀ : C(K, ℂ)) z)
            (m₁ * (u₁ : C(K, ℂ)) z)
      _ ≤ ‖m₀‖ * eNear + ‖m₁‖ * eNear := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (hnear₀ z hz).le (norm_nonneg m₀))
          (mul_le_mul_of_nonneg_left
            (hnear₁ z hz).le (norm_nonneg m₁))
      _ = (‖m₀‖ + ‖m₁‖) * eNear := by ring
  · intro z hz
    let ζ : ℂ := (a - (z : ℂ))⁻¹
    have hsplit :
        ζ ^ 3 *
            (m₀ * P₀.eval ζ + m₁ * P₁.eval ζ) =
          m₀ * (ζ ^ 3 * P₀.eval ζ) +
            m₁ * (ζ ^ 3 * P₁.eval ζ) := by
      ring
    change
      ‖ζ ^ 3 *
          (m₀ • P₀ + m₁ • P₁).eval ζ‖ ≤
        (‖m₀‖ + ‖m₁‖) * eFar *
          (dist a (z : ℂ))⁻¹ ^ 3
    simp only [Polynomial.eval_add, Polynomial.eval_smul,
      smul_eq_mul]
    rw [hsplit]
    calc
      ‖m₀ * (ζ ^ 3 * P₀.eval ζ) +
          m₁ * (ζ ^ 3 * P₁.eval ζ)‖
          ≤ ‖m₀ * (ζ ^ 3 * P₀.eval ζ)‖ +
              ‖m₁ * (ζ ^ 3 * P₁.eval ζ)‖ :=
        norm_add_le _ _
      _ = ‖m₀‖ * ‖ζ ^ 3 * P₀.eval ζ‖ +
              ‖m₁‖ * ‖ζ ^ 3 * P₁.eval ζ‖ := by
        simp only [norm_mul]
      _ ≤
          ‖m₀‖ *
              (eFar * (dist a (z : ℂ))⁻¹ ^ 3) +
            ‖m₁‖ *
              (eFar * (dist a (z : ℂ))⁻¹ ^ 3) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (hfar₀ z hz).le (norm_nonneg m₀))
          (mul_le_mul_of_nonneg_left
            (hfar₁ z hz).le (norm_nonneg m₁))
      _ = (‖m₀‖ + ‖m₁‖) * eFar *
          (dist a (z : ℂ))⁻¹ ^ 3 := by ring
  · intro z
    change
      ‖m₀ * (u₀ : C(K, ℂ)) z +
          m₁ * (u₁ : C(K, ℂ)) z‖ ≤
        (‖m₀‖ + ‖m₁‖) * B
    calc
      ‖m₀ * (u₀ : C(K, ℂ)) z +
          m₁ * (u₁ : C(K, ℂ)) z‖
          ≤ ‖m₀‖ * ‖(u₀ : C(K, ℂ)) z‖ +
              ‖m₁‖ * ‖(u₁ : C(K, ℂ)) z‖ := by
        simpa only [norm_mul] using
          norm_add_le
            (m₀ * (u₀ : C(K, ℂ)) z)
            (m₁ * (u₁ : C(K, ℂ)) z)
      _ ≤ ‖m₀‖ * B + ‖m₁‖ * B := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (norm_nonneg m₀)
          exact ((u₀ : C(K, ℂ)).norm_coe_le_norm z).trans
            (le_max_left _ _)
        · apply mul_le_mul_of_nonneg_left _ (norm_nonneg m₁)
          exact ((u₁ : C(K, ℂ)).norm_coe_le_norm z).trans
            (le_max_right _ _)
      _ = (‖m₀‖ + ‖m₁‖) * B := by ring

end Submission.Helpers
