import Submission.OddOrder.MathlibSupport.IrreducibleCommutantScalar
import Submission.OddOrder.MathlibSupport.NormalConstituentCyclicCentralizer
import Submission.OddOrder.MathlibSupport.NormalConstituentSubspaceStabilizer

/-!
The cyclic-quotient irreducibility step in Clifford theory.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- If an irreducible ambient representation has a simple constituent of its
restriction to a normal subgroup whose every ambient translate is equivalent
to it, then a cyclic quotient forces the restricted representation itself to
be irreducible. This is the mathlib-facing form of `mx_irr_prime_index`. -/
theorem normalRestriction_irreducible_of_quotient_isCyclic
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)]
    (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    (hequiv : ∀ z : G, Nonempty (Representation.Equiv U.toRepresentation
      (conjugateNormalSubrepresentation rho N z U).toRepresentation)) :
    Representation.IsIrreducible (rho.comp N.subtype) := by
  classical
  letI := Fintype.ofFinite G
  have hU : U ≠ ⊥ :=
    ((irreducible_toRepresentation_iff_isAtom _ U).mp inferInstance).1
  obtain ⟨x, hgen⟩ :=
    exists_zpowers_sup_eq_top_of_quotient_isCyclic N
  obtain ⟨e⟩ := hequiv x
  obtain ⟨a, b, ha, hba⟩ :=
    exists_subgroupAlgebra_correction_pair rho N U hU hequiv x e
  have hN := correctedTranslate_commutes_normal
    rho N U hU hequiv x e a ha
  have hG := correctedTranslate_commutes_all_of_zpowers_sup_eq_top
    rho N x a b hba hN hgen
  obtain ⟨c, hscalar⟩ :=
    exists_eq_smul_one_of_commute_irreducible rho
      (rho x * subgroupAlgebraEnd rho N a) hG
  have hab :
      subgroupAlgebraEnd rho N a * subgroupAlgebraEnd rho N b = 1 :=
    mul_eq_one_symm hba
  have hx_factor :
      rho x = (c • (1 : Module.End k V)) *
        subgroupAlgebraEnd rho N b := by
    calc
      rho x =
          (rho x * subgroupAlgebraEnd rho N a) *
            subgroupAlgebraEnd rho N b := by
        rw [mul_assoc, hab, mul_one]
      _ = (c • (1 : Module.End k V)) *
          subgroupAlgebraEnd rho N b := by rw [hscalar]
  have hx_le : conjugateNormalSubrepresentation rho N x U ≤ U := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hv
    let uu : U.toSubmodule := ⟨u, hu⟩
    have hBu : subgroupAlgebraEnd rho N b u ∈ U := by
      rw [subgroupAlgebraEnd_apply_subrepresentation rho N U b uu]
      exact (U.toRepresentation.asAlgebraHom b uu).property
    rw [hx_factor]
    change c • subgroupAlgebraEnd rho N b u ∈ U
    exact U.toSubmodule.smul_mem c hBu
  have hx_eq : conjugateNormalSubrepresentation rho N x U = U := by
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.eq_of_le_of_finrank_eq hx_le
    exact finrank_conjugateNormalSubrepresentation rho N x U
  have hx_stabilizer :
      x ∈ normalConstituentSubspaceStabilizer rho N U := by
    rw [mem_normalConstituentSubspaceStabilizer_iff]
    exact hx_eq
  have hstabilizer_top :
      normalConstituentSubspaceStabilizer rho N U = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le (Subgroup.zpowers_le.mpr hx_stabilizer)
      (normal_le_normalConstituentSubspaceStabilizer rho N U)
  have htranslate (g : G) :
      conjugateNormalSubrepresentation rho N g U = U := by
    rw [← mem_normalConstituentSubspaceStabilizer_iff]
    rw [hstabilizer_top]
    exact Subgroup.mem_top g
  have hUtop : U = ⊤ := by
    apply le_antisymm le_top
    rw [← normalConstituentOrbitSup_eq_top rho N U hU]
    rw [normalConstituentOrbitSup]
    apply Finset.sup_le
    intro g _
    rw [htranslate g]
  apply isSimpleOrder_iff_isAtom_top.mpr
  rw [← hUtop]
  exact (irreducible_toRepresentation_iff_isAtom _ U).mp inferInstance

end Submission.OddOrder.MathlibSupport
