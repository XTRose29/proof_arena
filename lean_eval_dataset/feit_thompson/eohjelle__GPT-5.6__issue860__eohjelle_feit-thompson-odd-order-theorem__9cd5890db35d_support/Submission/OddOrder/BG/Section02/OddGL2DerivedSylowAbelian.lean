import Submission.OddOrder.BG.Section02.OddGL2DerivedSylowContainment
import Submission.OddOrder.MathlibSupport.PGroupRepresentationAbelian

/-!
The Lean form of
`BGsection2.charf_GL2_der_subS_abelian_Sylow`
(Bender--Glauberman Theorem 2.6(b)).
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- In prime characteristic `p`, the commutator of a finite odd-order group
faithfully represented in dimension two lies in an abelian Sylow
`p`-subgroup. -/
theorem exists_abelian_sylow_commutator_le_of_odd_faithful_finrank_two
    {p : ℕ} [CharP F p] [Fact p.Prime]
    (rho : Representation F G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank F V = 2) (hodd : Odd (Nat.card G)) :
    ∃ P : Sylow p G,
      _root_.commutator G ≤ (P : Subgroup G) ∧ IsMulCommutative P := by
  obtain ⟨P, hcommP⟩ :=
    exists_sylow_commutator_le_of_odd_faithful_finrank_two
      rho hrho hdim hodd
  let sigma : Representation F P V := rho.comp (P : Subgroup G).subtype
  have hsigma : Function.Injective sigma := by
    intro x y hxy
    apply Subtype.ext
    apply hrho
    simpa [sigma] using hxy
  refine ⟨P, hcommP, ?_⟩
  exact isMulCommutative_of_faithful_isPGroup_charP_finrank_le_two
    sigma hsigma P.isPGroup' hdim.le

end Submission.OddOrder.BG.Section02
