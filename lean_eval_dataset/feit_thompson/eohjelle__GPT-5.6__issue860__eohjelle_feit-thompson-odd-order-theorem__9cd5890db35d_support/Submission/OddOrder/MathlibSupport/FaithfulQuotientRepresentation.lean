import Mathlib.RepresentationTheory.Invariants

/-!
Factoring a representation through its kernel.

This packages the `kquo_repr`/`kquo_mx_faithful` step used in the final part
of `BGappendixAB.odd_p_stable`.
-/

namespace Submission.OddOrder.MathlibSupport

variable {k G V : Type*} [Semiring k] [Group G]
variable [AddCommMonoid V] [Module k V]

instance representationCompKerIsTrivial (rho : Representation k G V) :
    Representation.IsTrivial (rho.comp rho.ker.subtype) where
  out g := by
    change rho (g : G) = 1
    exact g.2

/-- The representation induced on the quotient by the original kernel. -/
def quotientKerRepresentation (rho : Representation k G V) :
    Representation k (G ⧸ rho.ker) V :=
  Representation.ofQuotient rho rho.ker

@[simp]
theorem quotientKerRepresentation_mk_apply
    (rho : Representation k G V) (g : G) (v : V) :
    quotientKerRepresentation rho (g : G ⧸ rho.ker) v = rho g v :=
  rfl

/-- Quotienting by the kernel makes a representation faithful. -/
theorem quotientKerRepresentation_injective
    (rho : Representation k G V) :
    Function.Injective (quotientKerRepresentation rho) := by
  intro a b hab
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective rho.ker a
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective rho.ker b
  apply QuotientGroup.eq.mpr
  rw [MonoidHom.mem_ker]
  calc
    rho (g⁻¹ * h) = rho g⁻¹ * rho h := map_mul rho _ _
    _ = rho g⁻¹ * rho g := by
      rw [show rho h = rho g by
        apply LinearMap.ext
        intro v
        exact (LinearMap.congr_fun hab v).symm]
    _ = rho (g⁻¹ * g) := (map_mul rho _ _).symm
    _ = 1 := by simp

theorem quotientKerRepresentation_ker_eq_bot
    (rho : Representation k G V) :
    (quotientKerRepresentation rho).ker = ⊥ :=
  MonoidHom.ker_eq_bot _ (quotientKerRepresentation_injective rho)

/-- A zero fixed space for a subgroup remains zero for its image in the
faithful kernel quotient. -/
theorem quotientKerRepresentation_map_invariants_eq_bot
    {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (R : Subgroup G)
    (hfix : Representation.invariants
      (rho.comp R.subtype : Representation k R V) = ⊥) :
    Representation.invariants
      ((quotientKerRepresentation rho).comp
        (R.map (QuotientGroup.mk' rho.ker)).subtype :
        Representation k (R.map (QuotientGroup.mk' rho.ker)) V) = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  have hvR : v ∈ Representation.invariants
      (rho.comp R.subtype : Representation k R V) := by
    rw [Representation.mem_invariants]
    intro r
    let rq : R.map (QuotientGroup.mk' rho.ker) :=
      ⟨QuotientGroup.mk' rho.ker (r : G), ⟨r, r.property, rfl⟩⟩
    have hvr := (Representation.mem_invariants _ _).mp hv rq
    exact hvr
  rw [hfix] at hvR
  exact hvR

end Submission.OddOrder.MathlibSupport
