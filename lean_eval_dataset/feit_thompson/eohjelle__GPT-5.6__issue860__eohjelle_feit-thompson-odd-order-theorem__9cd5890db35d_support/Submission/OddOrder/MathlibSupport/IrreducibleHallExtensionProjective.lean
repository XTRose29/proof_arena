import Mathlib.LinearAlgebra.Determinant
import Submission.OddOrder.MathlibSupport.IrreducibleHallExtensionCocycle

/-!
# Correcting projective linear lifts in coprime degree

This is the linear-algebra half of the invariant Hall-character extension
argument.  A projective family of lifts whose degree is coprime to the order
of the quotient can be rescaled to a genuine linear representation.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {Q : Type u} {k : Type v} {V : Type w}

section Determinant

variable [Field k] [AddCommGroup V] [Module k V]

/-- Scaling a linear equivalence by a unit scales its determinant by the
unit to the dimension. -/
theorem linearEquiv_det_units_smul (c : kˣ) (f : V ≃ₗ[k] V) :
    LinearEquiv.det (c • f) = c ^ Module.finrank k V * LinearEquiv.det f := by
  apply Units.ext
  simp only [LinearEquiv.coe_det, LinearEquiv.toLinearMap_smul,
    LinearMap.det_smul, Units.val_mul, Units.val_pow_eq_pow_val]

end Determinant

section Correction

variable [Group Q] [Fintype Q]
variable [Field k] [AddCommGroup V] [Module k V]

/-- A projective family of invertible linear maps with a scalar factor set
can be rescaled to a homomorphism when the dimension is coprime to the order
of the indexing group. -/
theorem exists_linearEquivHom_of_projective_of_coprime
    (L : Q → V ≃ₗ[k] V) (alpha : Q → Q → kˣ)
    (halpha : IsScalarFactorSet alpha)
    (hL : ∀ a b, L a * L b = alpha a b • L (a * b))
    (hcop : Nat.Coprime (Module.finrank k V) (Fintype.card Q)) :
    ∃ rho : Q →* V ≃ₗ[k] V, ∀ a, ∃ c : kˣ, rho a = c • L a := by
  let delta : Q → kˣ := fun a ↦ LinearEquiv.det (L a)
  have hdelta (a b : Q) :
      alpha a b ^ Module.finrank k V =
        delta a * delta b * (delta (a * b))⁻¹ := by
    have hdet := congrArg LinearEquiv.det (hL a b)
    rw [map_mul, linearEquiv_det_units_smul] at hdet
    dsimp only [delta]
    calc
      alpha a b ^ Module.finrank k V =
          (alpha a b ^ Module.finrank k V * LinearEquiv.det (L (a * b))) *
            (LinearEquiv.det (L (a * b)))⁻¹ := by group
      _ = (LinearEquiv.det (L a) * LinearEquiv.det (L b)) *
            (LinearEquiv.det (L (a * b)))⁻¹ := by rw [← hdet]
  obtain ⟨beta, hbeta⟩ := scalarFactorSet_isCoboundary_of_pow_of_coprime
    alpha halpha (Module.finrank k V) hcop delta hdelta
  let R : Q → V ≃ₗ[k] V := fun a ↦ (beta a)⁻¹ • L a
  have hRmul (a b : Q) : R (a * b) = R a * R b := by
    dsimp only [R]
    have hc : (beta (a * b))⁻¹ =
        (beta b)⁻¹ * (beta a)⁻¹ * alpha a b := by
      rw [hbeta]
      group
    ext x
    have hx := congrArg (fun f : V ≃ₗ[k] V ↦ f x) (hL a b)
    simp only [LinearEquiv.mul_apply, LinearEquiv.smul_apply] at hx
    simp only [LinearEquiv.mul_apply, LinearEquiv.smul_apply, map_smul]
    rw [hx]
    simpa only [smul_smul, Units.val_mul, mul_assoc] using
      congrArg (fun c : kˣ ↦ (c : k) • L (a * b) x) hc
  have hRone : R 1 = 1 := by
    apply mul_left_cancel (a := R 1)
    rw [← hRmul]
    simp
  let rho : Q →* V ≃ₗ[k] V :=
    { toFun := R
      map_one' := hRone
      map_mul' := hRmul }
  refine ⟨rho, fun a ↦ ⟨(beta a)⁻¹, rfl⟩⟩

end Correction

end Submission.OddOrder.MathlibSupport
