import Mathlib.Data.Finset.Lattice.Fold
import Submission.OddOrder.MathlibSupport.NormalRestrictionConstituents

/-!
The orbit span of a constituent of the restriction to a finite normal
subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]

/-- The sum of all ambient translates of a subrepresentation of the
restriction to a normal subgroup. -/
noncomputable def normalConstituentOrbitSup
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) :
    Subrepresentation (rho.comp N.subtype) := by
  letI := Fintype.ofFinite G
  exact Finset.univ.sup (fun g ↦ conjugateNormalSubrepresentation rho N g U)

/-- Every translate occurs in the orbit supremum. -/
theorem conjugateNormalSubrepresentation_le_orbitSup
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (g : G) :
    conjugateNormalSubrepresentation rho N g U ≤
      normalConstituentOrbitSup rho N U := by
  classical
  letI := Fintype.ofFinite G
  exact Finset.le_sup (f := fun h ↦ conjugateNormalSubrepresentation rho N h U)
    (Finset.mem_univ g)

/-- Translating the complete constituent orbit only permutes its summands. -/
theorem conjugateNormalSubrepresentation_orbitSup
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (g : G) :
    conjugateNormalSubrepresentation rho N g
        (normalConstituentOrbitSup rho N U) =
      normalConstituentOrbitSup rho N U := by
  classical
  letI := Fintype.ofFinite G
  have hforward (a : G) :
      conjugateNormalSubrepresentation rho N a
          (normalConstituentOrbitSup rho N U) ≤
        normalConstituentOrbitSup rho N U := by
    let e := conjugateNormalSubrepresentationOrderIso rho N a
    change e (normalConstituentOrbitSup rho N U) ≤ _
    rw [normalConstituentOrbitSup, map_finset_sup]
    apply Finset.sup_le
    intro h _
    change conjugateNormalSubrepresentation rho N a
        (conjugateNormalSubrepresentation rho N h U) ≤ _
    rw [← conjugateNormalSubrepresentation_mul]
    exact conjugateNormalSubrepresentation_le_orbitSup rho N U (a * h)
  apply le_antisymm (hforward g)
  have hmap := conjugateNormalSubrepresentation_mono rho N g (hforward g⁻¹)
  simpa [← conjugateNormalSubrepresentation_mul] using hmap

/-- The orbit supremum is invariant under the whole ambient representation,
so it defines an ambient subrepresentation. -/
noncomputable def normalConstituentOrbitSubrepresentation
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) : Subrepresentation rho where
  toSubmodule := (normalConstituentOrbitSup rho N U).toSubmodule
  apply_mem_toSubmodule g v hv := by
    have hmem : rho g v ∈ conjugateNormalSubrepresentation rho N g
        (normalConstituentOrbitSup rho N U) := ⟨v, hv, rfl⟩
    rwa [conjugateNormalSubrepresentation_orbitSup] at hmem

/-- In an irreducible ambient representation, the orbit of every nonzero
normal-restriction subrepresentation spans the whole space. -/
theorem normalConstituentOrbitSubrepresentation_eq_top
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible rho] (hU : U ≠ ⊥) :
    normalConstituentOrbitSubrepresentation rho N U = ⊤ := by
  rcases eq_bot_or_eq_top (normalConstituentOrbitSubrepresentation rho N U) with hbot | htop
  · exfalso
    apply hU
    apply le_antisymm
    · intro v hv
      have hv1 : v ∈ conjugateNormalSubrepresentation rho N 1 U := by simpa
      have hv' := conjugateNormalSubrepresentation_le_orbitSup rho N U 1 hv1
      change v ∈ normalConstituentOrbitSubrepresentation rho N U at hv'
      rw [hbot] at hv'
      exact hv'
    · exact bot_le
  · exact htop

/-- Equivalently, the orbit supremum is the top subrepresentation of the
normal restriction. -/
theorem normalConstituentOrbitSup_eq_top
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible rho] (hU : U ≠ ⊥) :
    normalConstituentOrbitSup rho N U = ⊤ := by
  apply SetLike.ext
  intro v
  change v ∈ normalConstituentOrbitSubrepresentation rho N U ↔ _
  rw [normalConstituentOrbitSubrepresentation_eq_top rho N U hU]
  rfl

end Submission.OddOrder.MathlibSupport
