import Submission.OddOrder.MathlibSupport.IrreducibleCommutantScalar

/-!
# Scalar action above a central quotient subgroup

If a subgroup is central modulo the kernel of an irreducible
representation, every one of its elements acts by a scalar.  This is the
Schur-lemma step in Peterfalvi 1.8.
-/

namespace Submission.OddOrder.MathlibSupport

noncomputable section

universe u v w

variable {T : Type u} {k : Type v} {V : Type w}
  [Group T] [Field k] [IsAlgClosed k]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A subgroup central in the quotient by a representation kernel acts by
scalars in an irreducible representation. -/
theorem subgroup_acts_scalar_of_map_le_quotient_center
    (K D : Subgroup T) [K.Normal]
    (rho : Representation k T V) [rho.IsIrreducible]
    (hKker : K ≤ rho.ker)
    (hcenter : D.map (QuotientGroup.mk' K) ≤
      Subgroup.center (T ⧸ K)) :
    ∀ d : D, ∃ c : k,
      rho (d : T) = c • (1 : Module.End k V) := by
  intro d
  apply exists_eq_smul_one_of_commute_irreducible rho
  intro t
  have hqd : QuotientGroup.mk' K (d : T) ∈
      D.map (QuotientGroup.mk' K) := by
    exact ⟨d, d.property, rfl⟩
  have hq : QuotientGroup.mk' K ((d : T) * t) =
      QuotientGroup.mk' K (t * (d : T)) := by
    simp only [map_mul]
    exact (Subgroup.mem_center_iff.mp (hcenter hqd)
      (QuotientGroup.mk' K t)).symm
  have hz : (d : T) * t * (t * (d : T))⁻¹ ∈ K :=
    by simpa only [div_eq_mul_inv] using
      (QuotientGroup.eq_iff_div_mem.mp hq)
  have hzker : rho ((d : T) * t * (t * (d : T))⁻¹) = 1 :=
    MonoidHom.mem_ker.mp (hKker hz)
  have hcomm : rho ((d : T) * t) = rho (t * (d : T)) := by
    calc
      rho ((d : T) * t) =
          rho (((d : T) * t * (t * (d : T))⁻¹) *
            (t * (d : T))) := by
        congr 1
        group
      _ = rho ((d : T) * t * (t * (d : T))⁻¹) *
          rho (t * (d : T)) := by rw [map_mul]
      _ = rho (t * (d : T)) := by rw [hzker, one_mul]
  change rho (d : T) * rho t = rho t * rho (d : T)
  simpa only [map_mul] using hcomm

end

end Submission.OddOrder.MathlibSupport
