import Submission.OddOrder.BG.AppendixAB.QuadraticElement

/-!
Conjugation invariance of Appendix A quadratic p-elements.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] {p : ℕ}

/-- Conjugating by an element of `N_G(E)` preserves the quadratic p-element
predicate on `E`. -/
theorem IsQuadraticPElement.conj_of_mem_normalizer {E : Subgroup G} {x g : G}
    (hx : IsQuadraticPElement p E x)
    (hg : g ∈ Subgroup.normalizer (E : Set G)) :
    IsQuadraticPElement p E (g * x * g⁻¹) := by
  let e : MulAut G := MulAut.conj g
  have hE : E.map e = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hcyclic : (Subgroup.zpowers x).map e =
      Subgroup.zpowers (e x) := MonoidHom.map_zpowers e.toMonoidHom x
  have hcommutator : (⁅E, Subgroup.zpowers x⁆ : Subgroup G).map e =
      ⁅E, Subgroup.zpowers (e x)⁆ := by
    rw [Subgroup.map_commutator, hE, hcyclic]
  change IsQuadraticPElement p E (e x)
  refine ⟨hx.1.map e.toMonoidHom, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : e.symm y ∈ ⁅E, Subgroup.zpowers x⁆ := by
    rw [← hcommutator] at hy
    exact Subgroup.mem_map_equiv.mp hy
  have hxy := Subgroup.mem_centralizer_iff.mp hx.2 (e.symm y) hy'
  have hmapped := congrArg e hxy
  simpa using hmapped

end Submission.OddOrder.BG.AppendixAB
