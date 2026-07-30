import Submission.FiberAction
import Submission.HomeomorphismDegree

open scoped unitInterval

namespace Submission.RadialPageObstruction

noncomputable section

abbrev Complement := RadialPhase.Complement

def onProductMap (h : Complement ≃ₜ Complement) :
    C(RadialMilnor.Fiber × ℝ, RadialMilnor.Fiber × ℝ) :=
  ⟨fun x => RadialCyclicCover.toFiber
      (HomeomorphismDegree.coverAction h (RadialCyclicCover.fromFiber x)),
    RadialCyclicCover.toFiber_continuous.comp
      (HomeomorphismDegree.coverAction_continuous h |>.comp
        RadialCyclicCover.fromFiber_continuous)⟩

theorem onProductMap_deck (h : Complement ≃ₜ Complement)
    (hdegree : DeckDegree.degree (HomeomorphismDegree.inducedCircleMap h) = -1)
    (x : RadialMilnor.Fiber × ℝ) :
    onProductMap h (DeckDegree.deckProduct x) =
      (RadialMilnor.fiberMonodromy (onProductMap h x).1,
        (onProductMap h x).2 - 2 * Real.pi) := by
  change RadialCyclicCover.toFiber
      (HomeomorphismDegree.coverAction h
        (RadialCyclicCover.fromFiber (DeckDegree.deckProduct x))) = _
  rw [DeckDegree.fromFiber_deckProduct,
    HomeomorphismDegree.coverAction_deck, hdegree,
    HomeomorphismDegree.deckPow_neg_one,
    RadialCyclicCover.toFiber_deck_symm]
  rfl

def fiberMapAt (h : Complement ≃ₜ Complement) (s : ℝ) :
    C(RadialMilnor.Fiber, RadialMilnor.Fiber) :=
  ⟨fun q => (onProductMap h (q, s)).1,
    continuous_fst.comp
      ((onProductMap h).continuous.comp
        (continuous_id.prodMk continuous_const))⟩

theorem fiberMapAt_continuous (h : Complement ≃ₜ Complement) :
    Continuous (fun x : ℝ × RadialMilnor.Fiber => fiberMapAt h x.1 x.2) := by
  exact continuous_fst.comp
    ((onProductMap h).continuous.comp (continuous_snd.prodMk continuous_fst))

def fiberHomotopyZeroTwoPi (h : Complement ≃ₜ Complement) :
    (fiberMapAt h 0).Homotopy (fiberMapAt h (2 * Real.pi)) :=
  ContinuousMap.Homotopy.mk
    ⟨fun x : unitInterval × RadialMilnor.Fiber =>
        fiberMapAt h (2 * Real.pi * (x.1 : ℝ)) x.2, by
      have htime : Continuous
          (fun x : unitInterval × RadialMilnor.Fiber =>
            2 * Real.pi * (x.1 : ℝ)) := by
        fun_prop
      have hpair : Continuous
          (fun x : unitInterval × RadialMilnor.Fiber =>
            (2 * Real.pi * (x.1 : ℝ), x.2)) :=
        htime.prodMk continuous_snd
      have hcomp := (fiberMapAt_continuous h).comp hpair
      simpa only [Function.comp_def] using hcomp⟩
    (by
      intro q
      change fiberMapAt h (2 * Real.pi * ((0 : unitInterval) : ℝ)) q =
        fiberMapAt h 0 q
      rw [show 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 by norm_num])
    (by
      intro q
      change fiberMapAt h (2 * Real.pi * ((1 : unitInterval) : ℝ)) q =
        fiberMapAt h (2 * Real.pi) q
      rw [show 2 * Real.pi * ((1 : unitInterval) : ℝ) =
        2 * Real.pi by norm_num])

theorem fiberMap_relation (h : Complement ≃ₜ Complement)
    (hdegree : DeckDegree.degree (HomeomorphismDegree.inducedCircleMap h) = -1) :
    (fiberMapAt h (2 * Real.pi)).comp FiberAction.monodromyInvMap =
      FiberAction.monodromyMap.comp (fiberMapAt h 0) := by
  ext q
  change fiberMapAt h (2 * Real.pi)
      (RadialMilnor.fiberMonodromy.symm q) =
    RadialMilnor.fiberMonodromy (fiberMapAt h 0 q)
  have hdeck := congrArg Prod.fst (onProductMap_deck h hdegree (q, 0))
  simpa [DeckDegree.deckProduct, fiberMapAt] using hdeck

theorem action_relation (h : Complement ≃ₜ Complement)
    (hdegree : DeckDegree.degree (HomeomorphismDegree.inducedCircleMap h) = -1) :
    FiberAction.action (fiberMapAt h 0) * Monodromy.trefoil =
      Monodromy.trefoilInv * FiberAction.action (fiberMapAt h 0) := by
  have hrelation := congrArg FiberAction.action (fiberMap_relation h hdegree)
  rw [FiberAction.action_comp, FiberAction.action_comp,
    FiberAction.action_monodromy_inv, FiberAction.action_monodromy] at hrelation
  have hhomotopy := FiberAction.action_homotopy_invariant
    (fiberHomotopyZeroTwoPi h)
  rw [← hhomotopy] at hrelation
  exact hrelation

theorem false_of_action_det_one (h : Complement ≃ₜ Complement)
    (hdegree : DeckDegree.degree (HomeomorphismDegree.inducedCircleMap h) = -1)
    (hdet : (FiberAction.action (fiberMapAt h 0)).det = 1) : False :=
  Monodromy.no_det_one_conjugacy
    (FiberAction.action (fiberMapAt h 0)) (action_relation h hdegree) hdet

end

end Submission.RadialPageObstruction
