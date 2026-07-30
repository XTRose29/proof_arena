import Submission.CoverSymmetry
import Submission.Monodromy

namespace Submission.PageObstruction

noncomputable section

open CoverSymmetry

def monodromyMap : C(Milnor.Fiber, Milnor.Fiber) :=
  Milnor.fiberMonodromyHomeomorph

def monodromyInvMap : C(Milnor.Fiber, Milnor.Fiber) :=
  Milnor.fiberMonodromyHomeomorph.symm

theorem fiberMap_relation
    {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot}
    (P : PhaseReversing S) :
    (fiberContinuousMapAt P (2 * Real.pi)).comp monodromyInvMap =
      monodromyMap.comp (fiberContinuousMapAt P 0) := by
  ext x
  change fiberEquivAt P (2 * Real.pi) (Milnor.fiberMonodromy.symm x) =
    Milnor.fiberMonodromy (fiberEquivAt P 0 x)
  simpa only [zero_add] using fiberEquivAt_add_two_pi P 0 x

structure OrientedPageAction where
  action : C(Milnor.Fiber, Milnor.Fiber) → Matrix (Fin 2) (Fin 2) ℤ
  map_comp : ∀ f g, action (g.comp f) = action g * action f
  homotopy_invariant : ∀ {f g}, f.Homotopy g → action f = action g
  monodromy_action : action monodromyMap = Monodromy.trefoilInv
  monodromy_inv_action : action monodromyInvMap = Monodromy.trefoil
  phase_reversing_det :
    ∀ {S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot} (P : PhaseReversing S),
      (action (fiberContinuousMapAt P 0)).det = 1

theorem no_phaseReversing (A : OrientedPageAction)
    (S : Symmetry.NegativeSymmetry AlgebraicTrefoil.knot) :
    ¬ PhaseReversing S := by
  intro P
  have hrelation := congrArg A.action (fiberMap_relation P)
  rw [A.map_comp, A.map_comp, A.monodromy_inv_action, A.monodromy_action] at hrelation
  have hhomotopy := A.homotopy_invariant (fiberHomotopyZeroTwoPi P)
  rw [← hhomotopy] at hrelation
  exact Monodromy.no_det_one_conjugacy
    (A.action (fiberContinuousMapAt P 0)) hrelation (A.phase_reversing_det P)

end

end Submission.PageObstruction
