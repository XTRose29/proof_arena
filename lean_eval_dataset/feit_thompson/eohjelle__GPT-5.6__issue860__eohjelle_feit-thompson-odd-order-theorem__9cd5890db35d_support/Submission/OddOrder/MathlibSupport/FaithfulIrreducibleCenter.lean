import Mathlib.RingTheory.IntegralDomain
import Submission.OddOrder.MathlibSupport.FiniteSchurField
import Submission.OddOrder.MathlibSupport.IrreducibleCenterCharacter

/-!
Cyclicity of the center detected by a finite faithful irreducible
representation.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V] [Finite V]

/-- A finite group with a faithful irreducible representation has cyclic
center.  Schur's lemma and Little Wedderburn make the endomorphism ring a
field, and the central action embeds the center into that field. -/
theorem center_isCyclic_of_faithful_irreducible
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho) :
    IsCyclic (Subgroup.center G) := by
  let E := Module.End k[G] rho.asModule
  letI : Field E := finiteSchurField rho
  let f : Subgroup.center G →* E :=
    (Units.coeHom E).comp (schurCenterCharacter rho)
  have hf : Function.Injective f :=
    Units.val_injective.comp
      (schurCenterCharacter_injective_of_injective rho hrho)
  exact isCyclic_of_injective_ringHom f hf

end Submission.OddOrder.MathlibSupport
