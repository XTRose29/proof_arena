import Submission.RadialConnected

namespace Submission.DeckDegree

noncomputable section

abbrev Complement := RadialPhase.Complement

def baseFiber : RadialMilnor.Fiber :=
  RadialSpine.spineInclusion
    (CoreDeformation.coreInclusion RadialConnected.coreBase)

def basePoint : RadialMilnor.Fiber × ℝ := (baseFiber, 0)

def deckProduct : C(RadialMilnor.Fiber × ℝ,
    RadialMilnor.Fiber × ℝ) :=
  ⟨fun x => (RadialMilnor.fiberMonodromy.symm x.1,
      x.2 + 2 * Real.pi),
    (RadialMilnor.fiberMonodromyHomeomorph.symm.continuous.comp
      continuous_fst).prodMk (continuous_snd.add continuous_const)⟩

theorem fromFiber_deckProduct (x : RadialMilnor.Fiber × ℝ) :
    RadialCyclicCover.fromFiber (deckProduct x) =
      RadialCyclicCover.deck (RadialCyclicCover.fromFiber x) := by
  apply RadialCyclicCover.fiberCoverEquiv.symm.injective
  change RadialCyclicCover.toFiber
      (RadialCyclicCover.fromFiber (deckProduct x)) =
    RadialCyclicCover.toFiber
      (RadialCyclicCover.deck (RadialCyclicCover.fromFiber x))
  rw [RadialCyclicCover.toFiber_fromFiber,
    RadialCyclicCover.toFiber_deck,
    RadialCyclicCover.toFiber_fromFiber]
  rfl

theorem productMap_deckProduct (u : C(Complement, Circle))
    (x : RadialMilnor.Fiber × ℝ) :
    ComplementLift.productMap u (deckProduct x) =
      ComplementLift.productMap u x := by
  change u (RadialCyclicCover.fromFiber (deckProduct x)).1.1 =
    u (RadialCyclicCover.fromFiber x).1.1
  rw [fromFiber_deckProduct]
  rfl

theorem exp_productLift_deckProduct (u : C(Complement, Circle))
    (x : RadialMilnor.Fiber × ℝ) :
    Circle.exp (ComplementLift.productLift u (deckProduct x)) =
      Circle.exp (ComplementLift.productLift u x) := by
  rw [ComplementLift.exp_productLift, ComplementLift.exp_productLift,
    productMap_deckProduct]

def degree (u : C(Complement, Circle)) : ℤ :=
  Classical.choose (Circle.exp_eq_exp.mp
    (exp_productLift_deckProduct u basePoint))

theorem degree_spec (u : C(Complement, Circle)) :
    ComplementLift.productLift u (deckProduct basePoint) =
      ComplementLift.productLift u basePoint + degree u * (2 * Real.pi) :=
  Classical.choose_spec (Circle.exp_eq_exp.mp
    (exp_productLift_deckProduct u basePoint))

def deckLift (u : C(Complement, Circle)) :
    C(RadialMilnor.Fiber × ℝ, ℝ) :=
  (ComplementLift.productLift u).comp deckProduct

def shiftedLift (u : C(Complement, Circle)) :
    C(RadialMilnor.Fiber × ℝ, ℝ) :=
  ⟨fun x => ComplementLift.productLift u x + degree u * (2 * Real.pi),
    (ComplementLift.productLift u).continuous.add continuous_const⟩

theorem exp_shiftedLift (u : C(Complement, Circle))
    (x : RadialMilnor.Fiber × ℝ) :
    Circle.exp (shiftedLift u x) =
      Circle.exp (ComplementLift.productLift u x) := by
  apply Circle.exp_eq_exp.mpr
  exact ⟨degree u, rfl⟩

theorem deckLift_eq_shiftedLift (u : C(Complement, Circle)) :
    deckLift u = shiftedLift u := by
  have hfun : (deckLift u : RadialMilnor.Fiber × ℝ → ℝ) =
      (shiftedLift u : RadialMilnor.Fiber × ℝ → ℝ) :=
    Circle.isCoveringMap_exp.eq_of_comp_eq
      (deckLift u).continuous (shiftedLift u).continuous
      (by
        funext x
        exact (exp_productLift_deckProduct u x).trans
          (exp_shiftedLift u x).symm)
      basePoint (degree_spec u)
  ext x
  exact congrFun hfun x

theorem productLift_deckProduct (u : C(Complement, Circle))
    (x : RadialMilnor.Fiber × ℝ) :
    ComplementLift.productLift u (deckProduct x) =
      ComplementLift.productLift u x + degree u * (2 * Real.pi) := by
  exact DFunLike.congr_fun (deckLift_eq_shiftedLift u) x

theorem coverLift_deck (u : C(Complement, Circle))
    (x : RadialCyclicCover.Cover) :
    ComplementLift.coverLift u (RadialCyclicCover.deck x) =
      ComplementLift.coverLift u x + degree u * (2 * Real.pi) := by
  change ComplementLift.productLift u
      (RadialCyclicCover.toFiber (RadialCyclicCover.deck x)) =
    ComplementLift.productLift u (RadialCyclicCover.toFiber x) +
      degree u * (2 * Real.pi)
  rw [RadialCyclicCover.toFiber_deck]
  exact productLift_deckProduct u (RadialCyclicCover.toFiber x)

end

end Submission.DeckDegree
