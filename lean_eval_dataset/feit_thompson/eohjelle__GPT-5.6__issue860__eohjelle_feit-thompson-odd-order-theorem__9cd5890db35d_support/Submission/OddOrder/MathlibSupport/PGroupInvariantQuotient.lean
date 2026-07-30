import Mathlib.LinearAlgebra.Dimension.RankNullity
import Submission.OddOrder.MathlibSupport.PGroupInvariantVector

/-!
The quotient by the common fixed subspace of a two-dimensional modular
representation of a finite `p`-group.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

omit [Finite G] [FiniteDimensional F V] in
/-- The common fixed subspace of a representation is stable under the
representation. -/
theorem invariants_le_comap (rho : Representation F G V) (g : G) :
    rho.invariants ≤ rho.invariants.comap (rho g) := by
  intro x hx
  change rho g x ∈ rho.invariants
  rw [hx g]
  exact hx

/-- The representation induced on the quotient by the common fixed
subspace. -/
noncomputable def quotientByInvariants
    (rho : Representation F G V) :
    Representation F G (V ⧸ rho.invariants) :=
  rho.quotient rho.invariants (invariants_le_comap rho)

/-- In characteristic `p`, a finite `p`-group acts trivially on the quotient
by its common fixed subspace when the ambient space has dimension at most
two. -/
theorem quotientByInvariants_isTrivial
    {p : ℕ} [CharP F p] [Fact p.Prime]
    (rho : Representation F G V) (hG : IsPGroup p G)
    (hdim : Module.finrank F V ≤ 2) :
    (quotientByInvariants rho).IsTrivial := by
  classical
  let U := rho.invariants
  let tau : Representation F G (V ⧸ U) := quotientByInvariants rho
  change tau.IsTrivial
  by_cases hV : Nontrivial V
  · letI : Nontrivial V := hV
    have hU : U ≠ ⊥ := invariants_ne_bot_of_isPGroup_charP rho hG
    have hUdim : 1 ≤ Module.finrank F U :=
      Submodule.one_le_finrank_iff.mpr hU
    have hquotdim : Module.finrank F (V ⧸ U) ≤ 1 := by
      have hsum := U.finrank_quotient_add_finrank
      omega
    by_cases hquot : Nontrivial (V ⧸ U)
    · letI : Nontrivial (V ⧸ U) := hquot
      have htau : tau.invariants ≠ ⊥ :=
        invariants_ne_bot_of_isPGroup_charP tau hG
      have hinvDim : 1 ≤ Module.finrank F tau.invariants :=
        Submodule.one_le_finrank_iff.mpr htau
      have hquotPos : 1 ≤ Module.finrank F (V ⧸ U) :=
        Module.finrank_pos
      have hquotOne : Module.finrank F (V ⧸ U) = 1 := by omega
      have hinvTop : tau.invariants = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        have hinvLe := tau.invariants.finrank_le
        omega
      exact ⟨fun g ↦ LinearMap.ext fun (x : V ⧸ U) ↦ by
        have hx : x ∈ tau.invariants := by rw [hinvTop]; exact Submodule.mem_top
        exact hx g⟩
    · haveI : Subsingleton (V ⧸ U) :=
        not_nontrivial_iff_subsingleton.mp hquot
      exact ⟨fun _ ↦ LinearMap.ext fun x ↦ Subsingleton.elim _ _⟩
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    haveI : Subsingleton (V ⧸ U) := inferInstance
    exact ⟨fun _ ↦ LinearMap.ext fun x ↦ Subsingleton.elim _ _⟩

end Submission.OddOrder.MathlibSupport
