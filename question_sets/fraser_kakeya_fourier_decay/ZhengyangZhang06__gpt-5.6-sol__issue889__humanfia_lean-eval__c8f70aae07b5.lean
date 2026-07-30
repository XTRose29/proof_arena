import ChallengeDeps
import Submission.Helpers

open LeanEval.Combinatorics.FraserKakeyaProblem
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

namespace Submission

open Helpers

theorem fraser_kakeya_fourier_decay_and_sharp {d : ℕ} (_hd : 2 ≤ d) {K : Set (Space F d)} (_hK : IsKakeya K)
    (χ : AddChar F ℂ) (_hχ : χ ≠ 1) :
    (∃ μ : Space F d → ℝ, IsProbabilityMeasureOn K μ ∧
      ∀ ξ : Space F d, ξ ≠ 0 →
        ‖fourier χ μ ξ‖ ≤ (Fintype.card F : ℝ)⁻¹) ∧
    (∀ κ : ℝ, 0 < κ → κ < 1 →
      ∃ Q : ℕ, ∀ (F' : Type*) [Field F'] [Fintype F'] [DecidableEq F'],
        Q ≤ Fintype.card F' →
          ∃ K' : Set (Space F' d), IsKakeya K' ∧
            ∀ μ : Space F' d → ℝ, IsProbabilityMeasureOn K' μ →
              ∃ ξ : Space F' d, ξ ≠ 0 ∧
                κ * (Fintype.card F' : ℝ)⁻¹ ≤
                  ‖fourier (AddChar.FiniteField.primitiveChar_to_Complex F') μ ξ‖) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le _hd
  constructor
  · refine ⟨incidenceMeasure _hK, incidenceMeasure_isProbability _hK, ?_⟩
    intro ξ hξ
    exact incidence_fourier_bound _hK χ (AddChar.IsPrimitive.of_ne_one _hχ) hξ
  · intro κ hκ hκone
    obtain ⟨Q, hQ⟩ := exists_sharpness_threshold hκ hκone
    refine ⟨Q, ?_⟩
    intro F' _ _ _ hcard
    refine ⟨liftedPlanarSet (F := F') (n := n), liftedPlanar_isKakeya, ?_⟩
    exact sharpness_lifted hκ (hQ F' hcard)

end Submission
