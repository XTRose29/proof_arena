import Mathlib.Algebra.Ring.Commute
import Submission.OddOrder.MathlibSupport.SubrepresentationBurnsideExtension

/-!
Centralizing a represented subgroup algebra from centralizing its group
generators.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A basis group element of a subgroup algebra acts through the ambient
representation as that subgroup element. -/
@[simp]
theorem subgroupAlgebraEnd_of
    (rho : Representation k G V) (H : Subgroup G) (h : H) :
    subgroupAlgebraEnd rho H (MonoidAlgebra.of k H h) = rho (h : G) := by
  ext v
  simp [subgroupAlgebraEnd, subgroupAlgebraMap, MonoidAlgebra.of]

/-- Commutation with every represented subgroup element extends linearly to
commutation with the whole subgroup algebra. -/
theorem commute_subgroupAlgebraEnd_of_commute
    (rho : Representation k G V) (H : Subgroup G)
    (T : Module.End k V)
    (hT : ∀ h : H, Commute T (rho (h : G)))
    (a : k[H]) :
    Commute T (subgroupAlgebraEnd rho H a) := by
  induction a using MonoidAlgebra.induction_on with
  | hM h =>
      rw [subgroupAlgebraEnd_of]
      exact hT h
  | hadd a b ha hb =>
      rw [map_add]
      exact ha.add_right hb
  | hsmul c a ha =>
      rw [map_smul]
      exact ha.smul_right c

end Submission.OddOrder.MathlibSupport
