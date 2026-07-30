import Submission.OddOrder.PF.Section02.DadeBasicProperties
import Submission.OddOrder.PF.Section01.ClassFunctionRingHom

/-!
# Compatibility of the Dade map with coefficient automorphisms

The Dade map is defined by copying values on its support and extending by
zero, so it commutes with pointwise application of a ring endomorphism.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

variable {Γ : Type u} [Group Γ]

/-- The Dade map commutes with pointwise application of a ring
endomorphism. -/
theorem Dade_aut
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k]
    (ddA : DadeHypothesis G L A) (σ : k →+* k)
    (alpha : ClassFunction L k) :
    Dade ddA (ClassFunction.mapRingHom σ alpha) =
      ClassFunction.mapRingHom σ (Dade ddA alpha) := by
  apply ClassFunction.ext
  intro x
  by_cases hx : (x : Γ) ∈ Dade_support ddA
  · rcases hx with ⟨a, ha, hxa⟩
    rw [DadeE ddA (ClassFunction.mapRingHom σ alpha) ha x hxa,
      ClassFunction.mapRingHom_apply,
      ClassFunction.mapRingHom_apply,
      DadeE ddA alpha ha x hxa]
  · rw [Dade_eq_zero_of_not_mem ddA
        (ClassFunction.mapRingHom σ alpha) x hx,
      ClassFunction.mapRingHom_apply,
      Dade_eq_zero_of_not_mem ddA alpha x hx,
      σ.map_zero]

/-- The Dade map commutes with the star involution on coefficient values. -/
theorem Dade_conjC
    [Finite Γ] {G L : Subgroup Γ} {A : Set Γ}
    {k : Type v} [Field k] [StarRing k]
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L k) :
    Dade ddA (ClassFunction.mapRingHom (starRingEnd k) alpha) =
      ClassFunction.mapRingHom (starRingEnd k) (Dade ddA alpha) :=
  Dade_aut ddA (starRingEnd k) alpha

end

end Submission.OddOrder.PF
