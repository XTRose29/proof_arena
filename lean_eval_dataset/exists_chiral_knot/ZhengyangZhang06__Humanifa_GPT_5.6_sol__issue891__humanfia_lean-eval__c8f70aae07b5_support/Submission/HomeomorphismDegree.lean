import Submission.PhaseDegree

namespace Submission.HomeomorphismDegree

noncomputable section

abbrev Complement := RadialPhase.Complement
abbrev Cover := RadialCyclicCover.Cover

instance coverPreconnectedSpace : PreconnectedSpace Cover := by
  constructor
  rw [← RadialCyclicCover.fiberCoverEquiv.surjective.range_eq]
  rw [← Set.image_univ]
  exact isPreconnected_univ.image RadialCyclicCover.fromFiber
    RadialCyclicCover.fromFiber_continuous.continuousOn

def inducedCircleMap (h : Complement ≃ₜ Complement) : C(Complement, Circle) :=
  PhaseDegree.phaseMap.comp ⟨h, h.continuous⟩

def deckPow (n : ℤ) (x : Cover) : Cover :=
  ⟨(x.1.1, x.1.2 + (n : ℝ) * (2 * Real.pi)), by
    rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
    exact x.2⟩

@[simp] theorem deckPow_zero (x : Cover) : deckPow 0 x = x := by
  apply Subtype.ext
  apply Prod.ext <;> simp [deckPow]

theorem deckPow_add_one (n : ℤ) (x : Cover) :
    deckPow (n + 1) x = RadialCyclicCover.deck (deckPow n x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change x.1.2 + ((n + 1 : ℤ) : ℝ) * (2 * Real.pi) =
      x.1.2 + (n : ℝ) * (2 * Real.pi) + 2 * Real.pi
    push_cast
    ring

theorem deckPow_sub_one (n : ℤ) (x : Cover) :
    deckPow (n - 1) x = RadialCyclicCover.deck.symm (deckPow n x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change x.1.2 + ((n - 1 : ℤ) : ℝ) * (2 * Real.pi) =
      x.1.2 + (n : ℝ) * (2 * Real.pi) - 2 * Real.pi
    push_cast
    ring

theorem deckPow_neg_one (x : Cover) :
    deckPow (-1) x = RadialCyclicCover.deck.symm x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change x.1.2 + ((-1 : ℤ) : ℝ) * (2 * Real.pi) =
      x.1.2 - 2 * Real.pi
    push_cast
    ring

theorem coverLift_deck_symm (u : C(Complement, Circle)) (x : Cover) :
    ComplementLift.coverLift u (RadialCyclicCover.deck.symm x) =
      ComplementLift.coverLift u x - DeckDegree.degree u * (2 * Real.pi) := by
  have h := DeckDegree.coverLift_deck u (RadialCyclicCover.deck.symm x)
  rw [Equiv.apply_symm_apply] at h
  linarith

theorem coverLift_deckPow (u : C(Complement, Circle)) (n : ℤ) (x : Cover) :
    ComplementLift.coverLift u (deckPow n x) =
      ComplementLift.coverLift u x +
        (DeckDegree.degree u * n : ℤ) * (2 * Real.pi) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [deckPow_add_one, DeckDegree.coverLift_deck, ih]
      push_cast
      ring
  | pred n ih =>
      rw [deckPow_sub_one, coverLift_deck_symm, ih]
      push_cast
      ring

def coverAction (h : Complement ≃ₜ Complement) (x : Cover) : Cover :=
  ⟨(h x.1.1, ComplementLift.coverLift (inducedCircleMap h) x), by
    exact (ComplementLift.exp_coverLift (inducedCircleMap h) x).symm⟩

theorem coverAction_continuous (h : Complement ≃ₜ Complement) :
    Continuous (coverAction h) := by
  apply Continuous.subtype_mk
  exact (h.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (ComplementLift.coverLift (inducedCircleMap h)).continuous

def coverActionMap (h : Complement ≃ₜ Complement) : C(Cover, Cover) :=
  ⟨coverAction h, coverAction_continuous h⟩

@[simp] theorem coverAction_base (h : Complement ≃ₜ Complement) (x : Cover) :
    (coverAction h x).1.1 = h x.1.1 :=
  rfl

@[simp] theorem coverAction_height (h : Complement ≃ₜ Complement) (x : Cover) :
    (coverAction h x).1.2 = ComplementLift.coverLift (inducedCircleMap h) x :=
  rfl

theorem coverAction_deck (h : Complement ≃ₜ Complement) (x : Cover) :
    coverAction h (RadialCyclicCover.deck x) =
      deckPow (DeckDegree.degree (inducedCircleMap h)) (coverAction h x) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact DeckDegree.coverLift_deck (inducedCircleMap h) x

def compositionHeight (h : Complement ≃ₜ Complement) : C(Cover, ℝ) :=
  (ComplementLift.coverLift (inducedCircleMap h.symm)).comp (coverActionMap h)

theorem exp_compositionHeight (h : Complement ≃ₜ Complement) (x : Cover) :
    Circle.exp (compositionHeight h x) = Circle.exp x.1.2 := by
  rw [compositionHeight, ContinuousMap.comp_apply,
    ComplementLift.exp_coverLift]
  change RadialPhase.phase (h.symm (h x.1.1)) = Circle.exp x.1.2
  rw [Homeomorph.symm_apply_apply]
  exact x.2

def coverBase : Cover :=
  RadialCyclicCover.fromFiber DeckDegree.basePoint

def compositionOffset (h : Complement ≃ₜ Complement) : ℝ :=
  compositionHeight h coverBase - coverBase.1.2

theorem exp_compositionOffset (h : Complement ≃ₜ Complement) :
    Circle.exp (compositionOffset h) = 1 := by
  rw [compositionOffset, Circle.exp_sub, exp_compositionHeight]
  exact div_self' _

def shiftedHeight (h : Complement ≃ₜ Complement) : C(Cover, ℝ) :=
  ⟨fun x => x.1.2 + compositionOffset h,
    (continuous_snd.comp continuous_subtype_val).add continuous_const⟩

theorem exp_shiftedHeight (h : Complement ≃ₜ Complement) (x : Cover) :
    Circle.exp (shiftedHeight h x) = Circle.exp x.1.2 := by
  change Circle.exp (x.1.2 + compositionOffset h) = Circle.exp x.1.2
  rw [Circle.exp_add, exp_compositionOffset, mul_one]

theorem compositionHeight_eq_shiftedHeight (h : Complement ≃ₜ Complement) :
    compositionHeight h = shiftedHeight h := by
  have hfun : (compositionHeight h : Cover → ℝ) =
      (shiftedHeight h : Cover → ℝ) :=
    Circle.isCoveringMap_exp.eq_of_comp_eq
      (compositionHeight h).continuous (shiftedHeight h).continuous
      (by
        funext x
        exact (exp_compositionHeight h x).trans (exp_shiftedHeight h x).symm)
      coverBase (by
        change compositionHeight h coverBase =
          coverBase.1.2 + compositionOffset h
        rw [compositionOffset]
        ring)
  ext x
  exact congrFun hfun x

theorem compositionHeight_deck (h : Complement ≃ₜ Complement) (x : Cover) :
    compositionHeight h (RadialCyclicCover.deck x) =
      compositionHeight h x + 2 * Real.pi := by
  rw [compositionHeight_eq_shiftedHeight]
  change x.1.2 + 2 * Real.pi + compositionOffset h =
    x.1.2 + compositionOffset h + 2 * Real.pi
  ring

theorem degrees_mul_eq_one (h : Complement ≃ₜ Complement) :
    DeckDegree.degree (inducedCircleMap h.symm) *
      DeckDegree.degree (inducedCircleMap h) = 1 := by
  let n := DeckDegree.degree (inducedCircleMap h)
  let m := DeckDegree.degree (inducedCircleMap h.symm)
  have hdeck := compositionHeight_deck h coverBase
  change ComplementLift.coverLift (inducedCircleMap h.symm)
      (coverAction h (RadialCyclicCover.deck coverBase)) =
    ComplementLift.coverLift (inducedCircleMap h.symm)
        (coverAction h coverBase) + 2 * Real.pi at hdeck
  rw [coverAction_deck, coverLift_deckPow] at hdeck
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcast : ((m * n : ℤ) : ℝ) = 1 := by
    apply mul_right_cancel₀ htwoPi
    dsimp [m, n]
    linarith
  exact_mod_cast hcast

theorem degree_eq_one_or_neg_one (h : Complement ≃ₜ Complement) :
    DeckDegree.degree (inducedCircleMap h) = 1 ∨
      DeckDegree.degree (inducedCircleMap h) = -1 := by
  have hmul := degrees_mul_eq_one h
  have hmul' : DeckDegree.degree (inducedCircleMap h) *
      DeckDegree.degree (inducedCircleMap h.symm) = 1 := by
    rw [mul_comm]
    exact hmul
  exact Int.eq_one_or_neg_one_of_mul_eq_one hmul'

end

end Submission.HomeomorphismDegree
