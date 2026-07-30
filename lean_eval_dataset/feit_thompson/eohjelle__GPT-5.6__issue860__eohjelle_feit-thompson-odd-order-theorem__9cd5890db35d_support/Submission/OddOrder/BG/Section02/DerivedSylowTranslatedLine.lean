import Submission.OddOrder.BG.Section02.DerivedSylowLineSeparation
import Submission.OddOrder.MathlibSupport.DistinctEigenlines
import Submission.OddOrder.MathlibSupport.NormalInvariantSubspaceTranslate

/-!
Ambient translates of derived-Sylow invariant lines in
`BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped MonoidAlgebra

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- Every ambient translate of a one-dimensional derived-Sylow invariant
subspace is contained in one of the two distinct eigenlines. This is the
subspace form of `nAx` in the source proof. -/
theorem derivedSylow_translatedLine_le_left_or_right
    {q : ℕ} (rho : Representation F G V) (Q : Sylow q G)
    (hN : (derivedSylowPart Q).Normal)
    (m n r : Submodule F[derivedSylowPart Q]
      (derivedSylowRepresentation rho Q).asModule)
    (hmn : IsCompl m n) (x : derivedSylowPart Q) (a b : F)
    (hma : invariantLineAction (derivedSylowRepresentation rho Q) m x =
      a • LinearMap.id)
    (hna : invariantLineAction (derivedSylowRepresentation rho Q) n x =
      b • LinearMap.id)
    (hab : a ≠ b)
    (hrdim : Module.finrank F (r.restrictScalars F) = 1)
    (y : G) :
    translateRestrictedInvariantSubspace rho (derivedSylowPart Q) r y ≤
        m.restrictScalars F ∨
      translateRestrictedInvariantSubspace rho (derivedSylowPart Q) r y ≤
        n.restrictScalars F := by
  let f := asModuleGroupAction
    (subgroupRepresentation rho (derivedSylowPart Q)) x
  have hmnF : IsCompl (m.restrictScalars F) (n.restrictScalars F) :=
    (Submodule.isCompl_restrictScalars_iff F).mpr hmn
  have hm : ∀ u ∈ m.restrictScalars F, f u ∈ m.restrictScalars F := by
    intro u hu
    exact m.smul_mem (MonoidAlgebra.of F (derivedSylowPart Q) x) hu
  have hn : ∀ u ∈ n.restrictScalars F, f u ∈ n.restrictScalars F := by
    intro u hu
    exact n.smul_mem (MonoidAlgebra.of F (derivedSylowPart Q) x) hu
  have hfm : f.restrict hm =
      invariantLineAction (derivedSylowRepresentation rho Q) m x := by
    ext u
    rfl
  have hfn : f.restrict hn =
      invariantLineAction (derivedSylowRepresentation rho Q) n x := by
    ext u
    rfl
  have hrinv := translateRestrictedInvariantSubspace_le_comap
    rho (derivedSylowPart Q) hN r y x
  have hrank : Module.finrank F
      (translateRestrictedInvariantSubspace rho (derivedSylowPart Q) r y) = 1 :=
    (finrank_translateRestrictedInvariantSubspace
      rho (derivedSylowPart Q) r y).trans hrdim
  exact invariantLine_le_left_or_right_of_complementary_scalar_actions
    (m.restrictScalars F) (n.restrictScalars F) hmnF f hm hn a b
    (hfm.trans hma) (hfn.trans hna) hab
    (translateRestrictedInvariantSubspace rho (derivedSylowPart Q) r y)
    hrinv hrank

end Submission.OddOrder.BG.Section02
