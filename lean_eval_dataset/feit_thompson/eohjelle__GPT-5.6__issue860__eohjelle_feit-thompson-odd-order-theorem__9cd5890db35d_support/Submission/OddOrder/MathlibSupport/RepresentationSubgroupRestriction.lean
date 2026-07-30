import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
Representation, invariant-space, and commutator bridges for subgroup
restriction.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {G : Type u} [Group G]
variable {k : Type v} [Field k]
variable {V : Type w} [AddCommGroup V] [Module k V]

noncomputable section

/-- A zero fixed space remains zero when the acting subgroup is viewed as a
subgroup of an intermediate subgroup. -/
theorem invariants_comp_subgroupOf_eq_bot
    (rho : _root_.Representation k G V)
    {J R : Subgroup G} (hRJ : R ≤ J)
    (hfix : _root_.Representation.invariants
      (rho.comp R.subtype : _root_.Representation k R V) = ⊥) :
    _root_.Representation.invariants
      ((rho.comp J.subtype).comp (R.subgroupOf J).subtype :
        _root_.Representation k (R.subgroupOf J) V) = ⊥ := by
  apply le_antisymm
  · intro v hv
    have hvR : v ∈ _root_.Representation.invariants
        (rho.comp R.subtype : _root_.Representation k R V) := by
      intro r
      let rJ : J := ⟨r, hRJ r.property⟩
      let rRJ : R.subgroupOf J := ⟨rJ, r.property⟩
      have hvr := hv rRJ
      change rho (r : G) v = v
      exact hvr
    rw [hfix] at hvR
    exact hvR
  · exact bot_le

/-- Kernel membership for a representation restricted to a subgroup. -/
theorem mem_ker_comp_subtype_iff
    (rho : _root_.Representation k G V) (J : Subgroup G) (j : J) :
    j ∈ (rho.comp J.subtype : _root_.Representation k J V).ker ↔
      (j : G) ∈ rho.ker :=
  Iff.rfl

/-- Mapping mixed commutators from an intermediate subgroup recovers the
ambient mixed commutator. -/
theorem map_subgroupOf_commutator {J H R : Subgroup G}
    (hHJ : H ≤ J) (hRJ : R ≤ J) :
    ⁅R.subgroupOf J, H.subgroupOf J⁆.map J.subtype = ⁅R, H⁆ := by
  rw [Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hRJ,
    Subgroup.map_subgroupOf_eq_of_le hHJ]

/-- A commutator-kernel bound proved after restricting to an intermediate
subgroup lifts back to the ambient representation. -/
theorem commutator_le_ker_of_subgroupOf
    (rho : _root_.Representation k G V)
    {J H R : Subgroup G} (hHJ : H ≤ J) (hRJ : R ≤ J)
    (hlocal : ⁅R.subgroupOf J, H.subgroupOf J⁆ ≤
      (rho.comp J.subtype : _root_.Representation k J V).ker) :
    ⁅R, H⁆ ≤ rho.ker := by
  intro g hg
  rw [← map_subgroupOf_commutator hHJ hRJ] at hg
  rcases hg with ⟨j, hj, rfl⟩
  exact (mem_ker_comp_subtype_iff rho J j).mp (hlocal hj)

end

end Submission.OddOrder.MathlibSupport
