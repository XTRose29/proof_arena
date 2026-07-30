import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.ExtraspecialAutomorphismRigidity

/-!
Rigidity of extraspecial irreducible representations under ambient
conjugation.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {A : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [Group A] {P : Subgroup A} [P.Normal] [Finite P]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {p n : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- If an ambient element centralizes the internal center of a normal
extraspecial subgroup, every faithful irreducible representation of that
subgroup is equivalent to its conjugate twist. -/
theorem nonempty_equiv_comp_conjNormal_of_mem_centralizer_centerWithin
    (hP : IsExtraspecial P) (hpP : IsPGroup p P)
    (hcard : Nat.card P = p ^ (2 * n + 1))
    (rho : Representation k P V) [Representation.IsIrreducible rho]
    (hrho : Function.Injective rho) {g : A}
    (hg : g ∈ Subgroup.centralizer (centerWithin P : Set A)) :
    letI : Representation.IsIrreducible
        (rho.comp (MulAut.conjNormal g).toMonoidHom : Representation k P V) :=
      representation_irreducible_comp_mulAut rho (MulAut.conjNormal g)
    Nonempty (rho.Equiv
      (rho.comp (MulAut.conjNormal g).toMonoidHom : Representation k P V)) := by
  apply hP.nonempty_equiv_comp_mulAut_of_fixed_center hpP hcard rho hrho
    (MulAut.conjNormal g)
  intro z
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have hz : (z : A) ∈ centerWithin P := by
    rw [← map_center_eq_centerWithin P]
    exact ⟨z, z.property, rfl⟩
  have hcomm := hg (z : A) hz
  rw [hcomm.symm]
  group

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
