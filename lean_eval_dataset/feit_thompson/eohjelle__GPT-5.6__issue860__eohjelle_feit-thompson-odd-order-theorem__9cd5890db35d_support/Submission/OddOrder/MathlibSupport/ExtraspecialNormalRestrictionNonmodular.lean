import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleRigidityNonmodular
import Submission.OddOrder.MathlibSupport.NormalConstituentTwistEquiv
import Submission.OddOrder.MathlibSupport.NormalRestrictionCyclicIrreducible

/-!
The extraspecial normal-restriction theorem in arbitrary nonmodular
characteristic.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {A : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k]
variable [Group A] [Finite A]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {p : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- Ambient conjugation fixing the extraspecial center preserves a faithful
irreducible representation in nonmodular characteristic. -/
theorem nonempty_equiv_comp_conjNormal_of_mem_centralizer_centerWithin_of_card_ne_zero
    {P : Subgroup A} [P.Normal]
    (hP : IsExtraspecial P) (hpP : IsPGroup p P)
    (rho : Representation k P V) [Representation.IsIrreducible rho]
    [Nontrivial V]
    (hcard : (Nat.card P : k) ≠ 0)
    (hrho : Function.Injective rho) {g : A}
    (hg : g ∈ Subgroup.centralizer (centerWithin P : Set A)) :
    letI : Representation.IsIrreducible
        (rho.comp (MulAut.conjNormal g).toMonoidHom :
          Representation k P V) :=
      representation_irreducible_comp_mulAut rho (MulAut.conjNormal g)
    Nonempty (rho.Equiv
      (rho.comp (MulAut.conjNormal g).toMonoidHom :
        Representation k P V)) := by
  apply hP.nonempty_equiv_comp_mulAut_of_fixed_center_of_card_ne_zero
    hpP rho hcard hrho (MulAut.conjNormal g)
  intro z
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have hz : (z : A) ∈ centerWithin P := by
    rw [← map_center_eq_centerWithin P]
    exact ⟨z, z.property, rfl⟩
  have hcomm := hg (z : A) hz
  rw [hcomm.symm]
  group

/-- A faithful simple constituent of a normal extraspecial subgroup is the
whole restricted representation when the quotient is cyclic, without a
characteristic-zero assumption. -/
theorem normalRestriction_irreducible_of_quotient_isCyclic_of_card_ne_zero
    {P : Subgroup A} [P.Normal] [IsCyclic (A ⧸ P)]
    (hP : IsExtraspecial P) (hpP : IsPGroup p P)
    (hcard : (Nat.card P : k) ≠ 0)
    (rho : Representation k A V) [Representation.IsIrreducible rho]
    (U : Subrepresentation (rho.comp P.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    (hfaithful : Function.Injective U.toRepresentation)
    (hcentral : Subgroup.centralizer (centerWithin P : Set A) = ⊤) :
    Representation.IsIrreducible (rho.comp P.subtype) := by
  letI : IsSimpleModule k[P] U.toRepresentation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp inferInstance
  letI : Nontrivial U.toRepresentation.asModule :=
    IsSimpleModule.nontrivial k[P] U.toRepresentation.asModule
  letI : Nontrivial U.toSubmodule :=
    Function.Injective.nontrivial
      U.toRepresentation.asModuleEquiv.injective
  apply _root_.Submission.OddOrder.MathlibSupport.normalRestriction_irreducible_of_quotient_isCyclic
    rho P U
  intro g
  have hg : g⁻¹ ∈ Subgroup.centralizer (centerWithin P : Set A) := by
    rw [hcentral]
    exact Subgroup.mem_top _
  have he :=
    hP.nonempty_equiv_comp_conjNormal_of_mem_centralizer_centerWithin_of_card_ne_zero
      hpP U.toRepresentation hcard hfaithful hg
  have hconj : MulAut.conjNormal (H := P) g⁻¹ =
      (MulAut.conjNormal (H := P) g).symm := by
    ext x
    simp
  rw [hconj] at he
  obtain ⟨e⟩ := he
  exact ⟨e.trans (normalConstituentTwistEquiv rho P g U)⟩

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
