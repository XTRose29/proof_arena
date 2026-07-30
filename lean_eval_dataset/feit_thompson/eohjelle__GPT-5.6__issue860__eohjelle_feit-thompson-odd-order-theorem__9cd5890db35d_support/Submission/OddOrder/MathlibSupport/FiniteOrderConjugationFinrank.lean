import Submission.OddOrder.MathlibSupport.FiniteOrderPrimitiveRootEigenspaces
import Submission.OddOrder.MathlibSupport.PrimitiveRootConjugationFinrank

/-!
Conjugation eigenspace dimensions for finite-order operators.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- The inverse-conjugation eigenspace dimensions of a finite-order
operator are the cyclic autocorrelations of its eigenspace dimensions. -/
theorem finrank_linearEquivConjugation_primitiveRoot_of_pow_eq_one
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [IsAlgClosed k]
    [FiniteDimensional k V] (f : V ≃ₗ[k] V)
    (hpow : f.toLinearMap ^ h = 1) (m : ZMod h) :
    Module.finrank k
      (Module.End.eigenspace (linearEquivConjugation f)
        (primitiveRootUnitWeight homega m : k)) =
      ∑ i : ZMod h,
        Module.finrank k
            (Module.End.eigenspace f.toLinearMap
              (primitiveRootUnitWeight homega i : k)) *
          Module.finrank k
            (Module.End.eigenspace f.toLinearMap
              (primitiveRootUnitWeight homega (i + m) : k)) :=
  finrank_linearEquivConjugation_primitiveRoot homega f
    (iSup_primitiveRootUnitWeight_eigenspace_eq_top
      homega f.toLinearMap hpow) m

/-- Correlation-form restatement of
`finrank_linearEquivConjugation_primitiveRoot_of_pow_eq_one`. -/
theorem finrank_linearEquivConjugation_eq_cyclicRankCorrelation_of_pow_eq_one
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [IsAlgClosed k]
    [FiniteDimensional k V] (f : V ≃ₗ[k] V)
    (hpow : f.toLinearMap ^ h = 1) (m : ZMod h) :
    Module.finrank k
      (Module.End.eigenspace (linearEquivConjugation f)
        (primitiveRootUnitWeight homega m : k)) =
      cyclicRankCorrelation
        (fun i : ZMod h =>
          Module.finrank k
            (Module.End.eigenspace f.toLinearMap
              (primitiveRootUnitWeight homega i : k))) m :=
  finrank_linearEquivConjugation_primitiveRoot_of_pow_eq_one
    homega f hpow m

end Submission.OddOrder.MathlibSupport
