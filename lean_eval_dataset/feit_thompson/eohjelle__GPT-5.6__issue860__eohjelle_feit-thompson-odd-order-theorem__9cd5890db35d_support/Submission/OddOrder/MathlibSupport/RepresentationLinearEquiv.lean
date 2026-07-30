import Submission.OddOrder.MathlibSupport.CyclicGeneratorEigenspace
import Submission.OddOrder.MathlibSupport.EigenbasisConjugationMatrix
import Submission.OddOrder.MathlibSupport.RepresentationLinearEquivBasic

/-!
Linear equivalences and inverse conjugation from represented group elements.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The linear map underlying a represented element satisfies every
power relation satisfied by that element. -/
theorem representationLinearEquiv_pow_eq_one
    (rho : Representation k G V) (g : G) (h : Nat)
    (hpow : g ^ h = 1) :
    (representationLinearEquiv rho g).toLinearMap ^ h = 1 := by
  change (rho g) ^ h = 1
  rw [← map_pow, hpow, map_one]

/-- Generic inverse conjugation by `rho g` is the endomorphism
conjugation representation evaluated at `g⁻¹`. -/
theorem linearEquivConjugation_representationLinearEquiv
    (rho : Representation k G V) (g : G) :
    linearEquivConjugation (representationLinearEquiv rho g) =
      endomorphismConjugationRepresentation rho g⁻¹ := by
  ext T x
  simp [linearEquivConjugation, representationLinearEquiv,
    endomorphismConjugationRepresentation,
    endomorphismConjugationLinearMap, Module.End.mul_apply]

/-- The inverse of a cyclic generator generates the same group. -/
theorem forall_mem_zpowers_inv_of_forall_mem_zpowers
    (z : G) (hz : ∀ g : G, g ∈ Subgroup.zpowers z) :
    ∀ g : G, g ∈ Subgroup.zpowers z⁻¹ := by
  intro g
  simpa [Subgroup.zpowers_inv] using hz g

/-- For an irreducible representation, inverse conjugation by a cyclic
generator has a one-dimensional eigenvalue-one eigenspace. -/
theorem finrank_linearEquivConjugation_eigenspace_one_of_cyclic_irreducible
    [IsAlgClosed k] [FiniteDimensional k V]
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (z : G) (hz : ∀ g : G, g ∈ Subgroup.zpowers z) :
    Module.finrank k
      (Module.End.eigenspace
        (linearEquivConjugation (representationLinearEquiv rho z)) 1) = 1 := by
  rw [linearEquivConjugation_representationLinearEquiv]
  exact finrank_endomorphismConjugation_eigenspace_one_of_forall_mem_zpowers
    rho z⁻¹ (forall_mem_zpowers_inv_of_forall_mem_zpowers z hz)

end Submission.OddOrder.MathlibSupport
