import Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleDegree
import Submission.OddOrder.MathlibSupport.ExtraspecialNormalRestrictionIrreducible

/-!
The degree consequence of extraspecial normal-restriction irreducibility.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {A : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [Group A] [Finite A]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {p n : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- Under the cyclic full-inertia hypotheses, a faithful irreducible ambient
representation has the extraspecial degree `p ^ n`. -/
theorem finrank_eq_of_normal_quotient_isCyclic
    {P : Subgroup A} [P.Normal] [IsCyclic (A ⧸ P)]
    (hP : IsExtraspecial P) (hpP : IsPGroup p P)
    (hcard : Nat.card P = p ^ (2 * n + 1))
    (rho : Representation k A V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho)
    (U : Subrepresentation (rho.comp P.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    (hfaithful : Function.Injective U.toRepresentation)
    (hcentral : Subgroup.centralizer (centerWithin P : Set A) = ⊤) :
    Module.finrank k V = p ^ n := by
  let rhoP : Representation k P V := rho.comp P.subtype
  letI : Representation.IsIrreducible rhoP :=
    hP.normalRestriction_irreducible_of_quotient_isCyclic
      hpP hcard rho U hfaithful hcentral
  have hrhoP : Function.Injective rhoP :=
    hrho.comp P.subtype_injective
  exact hP.faithful_irreducible_finrank_eq hpP hcard rhoP hrhoP

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
