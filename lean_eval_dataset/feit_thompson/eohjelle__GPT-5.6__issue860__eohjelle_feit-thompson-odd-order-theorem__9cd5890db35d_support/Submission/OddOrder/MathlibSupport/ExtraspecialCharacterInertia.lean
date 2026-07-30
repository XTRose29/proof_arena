import Submission.OddOrder.MathlibSupport.ExtraspecialConjugationRigidity
import Submission.OddOrder.MathlibSupport.NormalConstituentCharacterStabilizer

/-!
Faithful simple constituents of normal extraspecial subgroups have full
character inertia when the ambient group centralizes the extraspecial center.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {A : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [Group A] [Finite A] {P : Subgroup A} [P.Normal]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {p n : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- Extraspecial rigidity makes the character inertia group of a faithful
simple constituent equal to the whole ambient group. -/
theorem normalConstituentCharacterStabilizer_eq_top
    (hP : IsExtraspecial P) (hpP : IsPGroup p P)
    (hcard : Nat.card P = p ^ (2 * n + 1))
    (rho : Representation k A V)
    (U : Subrepresentation (rho.comp P.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    (hfaithful : Function.Injective U.toRepresentation)
    (hcentral : Subgroup.centralizer (centerWithin P : Set A) = ⊤) :
    normalConstituentCharacterStabilizer rho P U = ⊤ := by
  apply top_unique
  intro g _
  rw [mem_normalConstituentCharacterStabilizer_iff_nonempty_equiv_twist]
  have hg : g⁻¹ ∈ Subgroup.centralizer (centerWithin P : Set A) := by
    rw [hcentral]
    exact Subgroup.mem_top _
  have he := hP.nonempty_equiv_comp_conjNormal_of_mem_centralizer_centerWithin
    hpP hcard U.toRepresentation hfaithful hg
  have hconj : MulAut.conjNormal (H := P) g⁻¹ =
      (MulAut.conjNormal (H := P) g).symm := by
    ext x
    simp
  simpa [hconj] using he

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
