import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry.PascalPappus
open Matrix

namespace Submission

theorem pascal (M : Matrix (Fin 3) (Fin 3) ℝ) (hMsymm : M.IsSymm) (hMdet : M.det ≠ 0)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Fin 3 → ℝ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hb₃ : b₃ ≠ 0)
    (hdist : [a₁, a₂, a₃, b₁, b₂, b₃].Pairwise (fun v w => ¬ SamePoint v w))
    (hA₁ : OnConic M a₁) (hA₂ : OnConic M a₂) (hA₃ : OnConic M a₃)
    (hB₁ : OnConic M b₁) (hB₂ : OnConic M b₂) (hB₃ : OnConic M b₃) :
    Collinear3 (meet a₁ b₂ a₂ b₁) (meet a₁ b₃ a₃ b₁) (meet a₂ b₃ a₃ b₂) := by
  open Helpers in
    have htail₁ := List.pairwise_cons.mp hdist
    have htail₂ := List.pairwise_cons.mp htail₁.2
    have htail₃ := List.pairwise_cons.mp htail₂.2
    have ha₁a₂ : ¬ SamePoint a₁ a₂ := htail₁.1 a₂ (by simp)
    have ha₁a₃ : ¬ SamePoint a₁ a₃ := htail₁.1 a₃ (by simp)
    have ha₂a₃ : ¬ SamePoint a₂ a₃ := htail₂.1 a₃ (by simp)
    have ha₁b₁ : ¬ SamePoint a₁ b₁ := htail₁.1 b₁ (by simp)
    have ha₁b₂ : ¬ SamePoint a₁ b₂ := htail₁.1 b₂ (by simp)
    have ha₁b₃ : ¬ SamePoint a₁ b₃ := htail₁.1 b₃ (by simp)
    have ha₂b₁ : ¬ SamePoint a₂ b₁ := htail₂.1 b₁ (by simp)
    have ha₂b₂ : ¬ SamePoint a₂ b₂ := htail₂.1 b₂ (by simp)
    have ha₂b₃ : ¬ SamePoint a₂ b₃ := htail₂.1 b₃ (by simp)
    have ha₃b₁ : ¬ SamePoint a₃ b₁ := htail₃.1 b₁ (by simp)
    have ha₃b₂ : ¬ SamePoint a₃ b₂ := htail₃.1 b₂ (by simp)
    have ha₃b₃ : ¬ SamePoint a₃ b₃ := htail₃.1 b₃ (by simp)

    let D := a₁ ⬝ᵥ (a₂ ⨯₃ a₃)
    let x₁ := b₁ ⬝ᵥ (a₂ ⨯₃ a₃)
    let y₁ := a₁ ⬝ᵥ (b₁ ⨯₃ a₃)
    let z₁ := a₁ ⬝ᵥ (a₂ ⨯₃ b₁)
    let x₂ := b₂ ⬝ᵥ (a₂ ⨯₃ a₃)
    let y₂ := a₁ ⬝ᵥ (b₂ ⨯₃ a₃)
    let z₂ := a₁ ⬝ᵥ (a₂ ⨯₃ b₂)
    let x₃ := b₃ ⬝ᵥ (a₂ ⨯₃ a₃)
    let y₃ := a₁ ⬝ᵥ (b₃ ⨯₃ a₃)
    let z₃ := a₁ ⬝ᵥ (a₂ ⨯₃ b₃)

    have hD : D ≠ 0 :=
      triple_product_ne_zero M hMsymm hMdet
        ha₁ ha₂ ha₃ ha₁a₂ ha₁a₃ ha₂a₃ hA₁ hA₂ hA₃
    have hx₁ : x₁ ≠ 0 :=
      triple_product_ne_zero M hMsymm hMdet
        hb₁ ha₂ ha₃ (not_samePoint_symm ha₂b₁) (not_samePoint_symm ha₃b₁)
        ha₂a₃ hB₁ hA₂ hA₃
    have hy₁ : y₁ ≠ 0 :=
      triple_product_ne_zero M hMsymm hMdet
        ha₁ hb₁ ha₃ ha₁b₁ ha₁a₃ (not_samePoint_symm ha₃b₁)
        hA₁ hB₁ hA₃
    have hz₁ : z₁ ≠ 0 :=
      triple_product_ne_zero M hMsymm hMdet
        ha₁ ha₂ hb₁ ha₁a₂ ha₁b₁ ha₂b₁ hA₁ hA₂ hB₁
    have hx₂ : x₂ ≠ 0 :=
      triple_product_ne_zero M hMsymm hMdet
        hb₂ ha₂ ha₃ (not_samePoint_symm ha₂b₂) (not_samePoint_symm ha₃b₂)
        ha₂a₃ hB₂ hA₂ hA₃
    have hy₂ : y₂ ≠ 0 :=
      triple_product_ne_zero M hMsymm hMdet
        ha₁ hb₂ ha₃ ha₁b₂ ha₁a₃ (not_samePoint_symm ha₃b₂)
        hA₁ hB₂ hA₃
    have hz₂ : z₂ ≠ 0 :=
      triple_product_ne_zero M hMsymm hMdet
        ha₁ ha₂ hb₂ ha₁a₂ ha₁b₂ ha₂b₂ hA₁ hA₂ hB₂
    have hx₃ : x₃ ≠ 0 :=
      triple_product_ne_zero M hMsymm hMdet
        hb₃ ha₂ ha₃ (not_samePoint_symm ha₂b₃) (not_samePoint_symm ha₃b₃)
        ha₂a₃ hB₃ hA₂ hA₃
    have hy₃ : y₃ ≠ 0 :=
      triple_product_ne_zero M hMsymm hMdet
        ha₁ hb₃ ha₃ ha₁b₃ ha₁a₃ (not_samePoint_symm ha₃b₃)
        hA₁ hB₃ hA₃
    have hz₃ : z₃ ≠ 0 :=
      triple_product_ne_zero M hMsymm hMdet
        ha₁ ha₂ hb₃ ha₁a₂ ha₁b₃ ha₂b₃ hA₁ hA₂ hB₃

    have hrep₁ :
        D • b₁ = combine a₁ a₂ a₃ x₁ y₁ z₁ :=
      cramer a₁ a₂ a₃ b₁
    have hrep₂ :
        D • b₂ = combine a₁ a₂ a₃ x₂ y₂ z₂ :=
      cramer a₁ a₂ a₃ b₂
    have hrep₃ :
        D • b₃ = combine a₁ a₂ a₃ x₃ y₃ z₃ :=
      cramer a₁ a₂ a₃ b₃

    let A := a₂ ⬝ᵥ (M *ᵥ a₃)
    let B := a₁ ⬝ᵥ (M *ᵥ a₃)
    let C := a₁ ⬝ᵥ (M *ᵥ a₂)
    have hA : A ≠ 0 :=
      pairing_ne_zero M hMsymm hMdet ha₂ ha₃ ha₂a₃ hA₂ hA₃
    have hq₁ : A * y₁ * z₁ + B * z₁ * x₁ + C * x₁ * y₁ = 0 :=
      coordinate_conic M hMsymm a₁ a₂ a₃ b₁ D x₁ y₁ z₁
        hA₁ hA₂ hA₃ hB₁ hrep₁
    have hq₂ : A * y₂ * z₂ + B * z₂ * x₂ + C * x₂ * y₂ = 0 :=
      coordinate_conic M hMsymm a₁ a₂ a₃ b₂ D x₂ y₂ z₂
        hA₁ hA₂ hA₃ hB₂ hrep₂
    have hq₃ : A * y₃ * z₃ + B * z₃ * x₃ + C * x₃ * y₃ = 0 :=
      coordinate_conic M hMsymm a₁ a₂ a₃ b₃ D x₃ y₃ z₃
        hA₁ hA₂ hA₃ hB₃ hrep₃
    have hpoly :=
      pascalPolynomial_eq_zero A B C
        x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ hA
        hx₁ hy₁ hz₁ hx₂ hy₂ hz₂ hx₃ hy₃ hz₃ hq₁ hq₂ hq₃
    have hscaled :=
      collinear_combinations_of_pascalPolynomial a₁ a₂ a₃
        x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ hpoly
    rw [← hrep₁, ← hrep₂, ← hrep₃] at hscaled
    exact collinear_of_scaled_second_points D hD a₁ a₂ a₃ b₁ b₂ b₃ hscaled

end Submission
