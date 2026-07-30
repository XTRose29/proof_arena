import Submission.OddOrder.MathlibSupport.NormalConstituentCorrectionPair

/-!
Correcting ambient translation so that it centralizes the normal subgroup
action.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V]

/-- If a subgroup-algebra correction makes `rho x` agree with an intertwiner
on one constituent, the corrected ambient endomorphism commutes with the
normal subgroup on the whole irreducible representation. -/
theorem correctedTranslate_commutes_normal
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (hU : U ≠ ⊥)
    (hequiv : ∀ z : G, Nonempty (Representation.Equiv U.toRepresentation
      (conjugateNormalSubrepresentation rho N z U).toRepresentation))
    (x : G)
    (e : Representation.Equiv U.toRepresentation
      (conjugateNormalSubrepresentation rho N x U).toRepresentation)
    (a : k[N])
    (ha : ∀ u : U.toSubmodule,
      (e u : V) = rho x (subgroupAlgebraEnd rho N a u)) :
    ∀ y : N, Commute
      (rho x * subgroupAlgebraEnd rho N a) (rho (y : G)) := by
  intro y
  let yx : N := (MulAut.conjNormal x).symm y
  have hof (z : N) :
      subgroupAlgebraEnd rho N (MonoidAlgebra.of k N z) = rho (z : G) := by
    ext v
    simp [subgroupAlgebraEnd, subgroupAlgebraMap, MonoidAlgebra.of]
  have hrestrict (u : U.toSubmodule) :
      subgroupAlgebraEnd rho N
          (a * MonoidAlgebra.of k N y) u =
        subgroupAlgebraEnd rho N
          (MonoidAlgebra.of k N yx * a) u := by
    simp only [map_mul, Module.End.mul_apply]
    rw [hof y, hof yx]
    change subgroupAlgebraEnd rho N a (rho (y : G) u) =
      rho (yx : G) (subgroupAlgebraEnd rho N a u)
    have he := congrArg Subtype.val
      (Representation.IntertwiningMap.isIntertwining
        U.toRepresentation
        (conjugateNormalSubrepresentation rho N x U).toRepresentation
        e.toIntertwiningMap y u)
    change (e (U.toRepresentation y u) : V) =
      rho (y : G) (e u : V) at he
    rw [ha (U.toRepresentation y u), ha u] at he
    change rho x (subgroupAlgebraEnd rho N a (rho (y : G) u)) =
      rho (y : G) (rho x (subgroupAlgebraEnd rho N a u)) at he
    calc
      subgroupAlgebraEnd rho N a (rho (y : G) u) =
          rho x⁻¹ (rho x (subgroupAlgebraEnd rho N a (rho (y : G) u))) := by
            simp
      _ = rho x⁻¹ (rho (y : G) (rho x (subgroupAlgebraEnd rho N a u))) :=
        congrArg (rho x⁻¹) he
      _ = rho (yx : G) (subgroupAlgebraEnd rho N a u) := by
        have hconj : x⁻¹ * (y : G) * x = (yx : G) := by
          simp [yx]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply]
        rw [← rho.map_mul, ← rho.map_mul, hconj]
  have halgebra := subgroupAlgebraEnd_eq_of_restrict_eq
    rho N U hU hequiv
    (a * MonoidAlgebra.of k N y)
    (MonoidAlgebra.of k N yx * a) hrestrict
  have hend :
      subgroupAlgebraEnd rho N a * rho (y : G) =
        rho (yx : G) * subgroupAlgebraEnd rho N a := by
    rw [map_mul, map_mul, hof y, hof yx] at halgebra
    exact halgebra
  rw [Commute]
  calc
    (rho x * subgroupAlgebraEnd rho N a) * rho (y : G) =
        rho x * (subgroupAlgebraEnd rho N a * rho (y : G)) := mul_assoc _ _ _
    _ = rho x * (rho (yx : G) * subgroupAlgebraEnd rho N a) := by rw [hend]
    _ = (rho x * rho (yx : G)) * subgroupAlgebraEnd rho N a :=
      (mul_assoc _ _ _).symm
    _ = (rho (y : G) * rho x) * subgroupAlgebraEnd rho N a := by
      congr 1
      have hcomm : x * (yx : G) = (y : G) * x := by
        simp only [yx, MulAut.conjNormal_symm_apply]
        group
      rw [← rho.map_mul, ← rho.map_mul, hcomm]
    _ = rho (y : G) * (rho x * subgroupAlgebraEnd rho N a) := mul_assoc _ _ _

/-- Existence form of `correctedTranslate_commutes_normal`, obtained by
Burnside density on the simple constituent. -/
theorem exists_correctedTranslate_commutes_normal
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (hU : U ≠ ⊥)
    [Representation.IsIrreducible U.toRepresentation]
    [FiniteDimensional k U.toSubmodule] [IsAlgClosed k]
    (hequiv : ∀ z : G, Nonempty (Representation.Equiv U.toRepresentation
      (conjugateNormalSubrepresentation rho N z U).toRepresentation))
    (x : G)
    (e : Representation.Equiv U.toRepresentation
      (conjugateNormalSubrepresentation rho N x U).toRepresentation) :
    ∃ a : k[N],
      (∀ u : U.toSubmodule,
        (e u : V) = rho x (subgroupAlgebraEnd rho N a u)) ∧
      ∀ y : N, Commute
        (rho x * subgroupAlgebraEnd rho N a) (rho (y : G)) := by
  obtain ⟨a, b, ha, _⟩ :=
    exists_subgroupAlgebra_correction_pair rho N U hU hequiv x e
  exact ⟨a, ha, correctedTranslate_commutes_normal
    rho N U hU hequiv x e a ha⟩

end Submission.OddOrder.MathlibSupport
