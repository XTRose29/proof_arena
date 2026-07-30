import Submission.OddOrder.MathlibSupport.ExtraspecialCharacterInertia
import Submission.OddOrder.MathlibSupport.NormalRestrictionCyclicIrreducible

/-!
Irreducibility of restriction to a normal extraspecial subgroup under the
full-inertia hypotheses used in Bender-Glauberman Theorem 2.5.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {A : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [Group A] [Finite A]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {p n : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- A faithful simple constituent of a normal extraspecial subgroup is the
whole restricted representation when the quotient is cyclic and the ambient
group centralizes the extraspecial center. -/
theorem normalRestriction_irreducible_of_quotient_isCyclic
    {P : Subgroup A} [P.Normal] [IsCyclic (A ⧸ P)]
    (hP : IsExtraspecial P) (hpP : IsPGroup p P)
    (hcard : Nat.card P = p ^ (2 * n + 1))
    (rho : Representation k A V) [Representation.IsIrreducible rho]
    (U : Subrepresentation (rho.comp P.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    (hfaithful : Function.Injective U.toRepresentation)
    (hcentral : Subgroup.centralizer (centerWithin P : Set A) = ⊤) :
    Representation.IsIrreducible (rho.comp P.subtype) := by
  have hinertia : normalConstituentCharacterStabilizer rho P U = ⊤ :=
    hP.normalConstituentCharacterStabilizer_eq_top
      hpP hcard rho U hfaithful hcentral
  have hequiv (g : A) :
      Nonempty (Representation.Equiv U.toRepresentation
        (conjugateNormalSubrepresentation rho P g U).toRepresentation) := by
    apply (mem_normalConstituentCharacterStabilizer_iff_nonempty_equiv_translate
      rho P U g).mp
    rw [hinertia]
    exact Subgroup.mem_top g
  exact _root_.Submission.OddOrder.MathlibSupport.normalRestriction_irreducible_of_quotient_isCyclic
    rho P U hequiv

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
