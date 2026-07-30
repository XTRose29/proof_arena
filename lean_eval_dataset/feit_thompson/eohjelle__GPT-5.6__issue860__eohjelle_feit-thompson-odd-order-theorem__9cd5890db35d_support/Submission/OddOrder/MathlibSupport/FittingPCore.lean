import Submission.OddOrder.MathlibSupport.FittingSelfCentralizing

/-!
The p-core form of the solvable Fitting self-centralizer theorem.

When the `p'`-core is trivial, the Fitting core is the `p`-core.  The
self-centralizer theorem therefore makes the centralizer of the `p`-core a
`p`-group.  This is the constrained-group input used by Appendix B.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot [IsSolvable G]
    (hprimeCore : pPrimeCore p G = ⊥) :
    Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G := by
  rw [← fittingCore_eq_pCore_of_pPrimeCore_eq_bot p hprimeCore]
  exact centralizer_fittingCore_le

theorem centralizer_pCore_isPGroup_of_pPrimeCore_eq_bot [IsSolvable G]
    (hprimeCore : pPrimeCore p G = ⊥) :
    IsPGroup p (Subgroup.centralizer (pCore p G : Set G)) :=
  (pCore_isPGroup (p := p) (G := G)).to_le
    (centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hprimeCore)

end Submission.OddOrder.MathlibSupport
