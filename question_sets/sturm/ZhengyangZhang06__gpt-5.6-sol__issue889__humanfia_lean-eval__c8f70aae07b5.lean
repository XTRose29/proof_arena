import ChallengeDeps
import Submission.Helpers

open LeanEval.Algebra
open Polynomial
open scoped Classical

namespace Submission

theorem sturm (p : ℝ[X]) (hp : Squarefree p) {a b : ℝ} (hab : a < b)
    (_ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    ((p.roots.toFinset).filter (fun x => a < x ∧ x < b)).card =
      sigma p a - sigma p b := by
  have hroots :
      Helpers.rootsIoc p a b =
        p.roots.toFinset.filter (fun x => a < x ∧ x < b) := by
    ext x
    constructor
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨hx'.1, hx'.2.1, lt_of_le_of_ne hx'.2.2 ?_⟩
      intro hxb
      apply hb
      have hxroot := Polynomial.isRoot_of_mem_roots
        (Multiset.mem_toFinset.mp hx'.1)
      simpa [Polynomial.IsRoot, hxb] using hxroot
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hx'.1, hx'.2.1, hx'.2.2.le⟩
  have hcount := Helpers.sigma_eq_add_card_rootsIoc hp hab
  rw [hroots] at hcount
  omega

end Submission
