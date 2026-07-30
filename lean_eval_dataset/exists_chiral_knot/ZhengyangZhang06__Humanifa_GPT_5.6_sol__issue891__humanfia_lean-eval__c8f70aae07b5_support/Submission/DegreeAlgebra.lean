import Submission.CircleMapAlgebra
import Submission.HomeomorphismDegree

namespace Submission.DegreeAlgebra

noncomputable section

abbrev Complement := RadialPhase.Complement

def sumLift (u v : C(Complement, Circle)) :
    C(RadialMilnor.Fiber × ℝ, ℝ) :=
  ⟨fun x => ComplementLift.productLift u x + ComplementLift.productLift v x,
    (ComplementLift.productLift u).continuous.add
      (ComplementLift.productLift v).continuous⟩

def sumOffset (u v : C(Complement, Circle)) : ℝ :=
  ComplementLift.productLift (CircleMapAlgebra.mapMul u v) DeckDegree.basePoint -
    sumLift u v DeckDegree.basePoint

def shiftedSumLift (u v : C(Complement, Circle)) :
    C(RadialMilnor.Fiber × ℝ, ℝ) :=
  ⟨fun x => sumLift u v x + sumOffset u v,
    (sumLift u v).continuous.add continuous_const⟩

theorem exp_sumOffset (u v : C(Complement, Circle)) :
    Circle.exp (sumOffset u v) = 1 := by
  rw [sumOffset, Circle.exp_sub, ComplementLift.exp_productLift]
  change (u (RadialCyclicCover.fromFiber DeckDegree.basePoint).1.1 *
      v (RadialCyclicCover.fromFiber DeckDegree.basePoint).1.1) /
    Circle.exp (ComplementLift.productLift u DeckDegree.basePoint +
      ComplementLift.productLift v DeckDegree.basePoint) = 1
  rw [Circle.exp_add, ComplementLift.exp_productLift,
    ComplementLift.exp_productLift]
  exact div_self' _

theorem exp_shiftedSumLift (u v : C(Complement, Circle))
    (x : RadialMilnor.Fiber × ℝ) :
    Circle.exp (shiftedSumLift u v x) =
      Circle.exp
        (ComplementLift.productLift (CircleMapAlgebra.mapMul u v) x) := by
  change Circle.exp (sumLift u v x + sumOffset u v) = _
  rw [Circle.exp_add, exp_sumOffset, mul_one]
  change Circle.exp
      (ComplementLift.productLift u x + ComplementLift.productLift v x) = _
  rw [Circle.exp_add, ComplementLift.exp_productLift,
    ComplementLift.exp_productLift, ComplementLift.exp_productLift]
  rfl

theorem productLift_mapMul_eq_shiftedSumLift (u v : C(Complement, Circle)) :
    ComplementLift.productLift (CircleMapAlgebra.mapMul u v) =
      shiftedSumLift u v := by
  have hfun :
      (ComplementLift.productLift (CircleMapAlgebra.mapMul u v) :
          RadialMilnor.Fiber × ℝ → ℝ) =
        (shiftedSumLift u v : RadialMilnor.Fiber × ℝ → ℝ) :=
    Circle.isCoveringMap_exp.eq_of_comp_eq
      (ComplementLift.productLift
        (CircleMapAlgebra.mapMul u v)).continuous
      (shiftedSumLift u v).continuous
      (by
        funext x
        exact (exp_shiftedSumLift u v x).symm)
      DeckDegree.basePoint (by
        change ComplementLift.productLift
            (CircleMapAlgebra.mapMul u v) DeckDegree.basePoint =
          sumLift u v DeckDegree.basePoint + sumOffset u v
        rw [sumOffset]
        ring)
  ext x
  exact congrFun hfun x

theorem degree_mapMul (u v : C(Complement, Circle)) :
    DeckDegree.degree (CircleMapAlgebra.mapMul u v) =
      DeckDegree.degree u + DeckDegree.degree v := by
  have hdeck := DeckDegree.productLift_deckProduct
    (CircleMapAlgebra.mapMul u v) DeckDegree.basePoint
  rw [productLift_mapMul_eq_shiftedSumLift] at hdeck
  change sumLift u v (DeckDegree.deckProduct DeckDegree.basePoint) +
      sumOffset u v =
    sumLift u v DeckDegree.basePoint + sumOffset u v +
      DeckDegree.degree (CircleMapAlgebra.mapMul u v) *
        (2 * Real.pi) at hdeck
  change (ComplementLift.productLift u
      (DeckDegree.deckProduct DeckDegree.basePoint) +
      ComplementLift.productLift v
        (DeckDegree.deckProduct DeckDegree.basePoint)) + sumOffset u v =
    (ComplementLift.productLift u DeckDegree.basePoint +
      ComplementLift.productLift v DeckDegree.basePoint) + sumOffset u v +
      DeckDegree.degree (CircleMapAlgebra.mapMul u v) *
        (2 * Real.pi) at hdeck
  rw [DeckDegree.productLift_deckProduct,
    DeckDegree.productLift_deckProduct] at hdeck
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcast :
      (DeckDegree.degree (CircleMapAlgebra.mapMul u v) : ℝ) =
        (DeckDegree.degree u + DeckDegree.degree v : ℤ) := by
    apply mul_right_cancel₀ htwoPi
    push_cast
    linarith
  exact_mod_cast hcast

def negLift (u : C(Complement, Circle)) :
    C(RadialMilnor.Fiber × ℝ, ℝ) :=
  ⟨fun x => -ComplementLift.productLift u x,
    (ComplementLift.productLift u).continuous.neg⟩

def negOffset (u : C(Complement, Circle)) : ℝ :=
  ComplementLift.productLift (CircleMapAlgebra.mapInv u) DeckDegree.basePoint -
    negLift u DeckDegree.basePoint

def shiftedNegLift (u : C(Complement, Circle)) :
    C(RadialMilnor.Fiber × ℝ, ℝ) :=
  ⟨fun x => negLift u x + negOffset u,
    (negLift u).continuous.add continuous_const⟩

theorem exp_negOffset (u : C(Complement, Circle)) :
    Circle.exp (negOffset u) = 1 := by
  rw [negOffset, Circle.exp_sub, ComplementLift.exp_productLift]
  change (u (RadialCyclicCover.fromFiber DeckDegree.basePoint).1.1)⁻¹ /
    Circle.exp (-ComplementLift.productLift u DeckDegree.basePoint) = 1
  rw [Circle.exp_neg, ComplementLift.exp_productLift]
  exact div_self' _

theorem exp_shiftedNegLift (u : C(Complement, Circle))
    (x : RadialMilnor.Fiber × ℝ) :
    Circle.exp (shiftedNegLift u x) =
      Circle.exp (ComplementLift.productLift (CircleMapAlgebra.mapInv u) x) := by
  change Circle.exp (negLift u x + negOffset u) = _
  rw [Circle.exp_add, exp_negOffset, mul_one]
  change Circle.exp (-ComplementLift.productLift u x) = _
  rw [Circle.exp_neg, ComplementLift.exp_productLift,
    ComplementLift.exp_productLift]
  rfl

theorem productLift_mapInv_eq_shiftedNegLift (u : C(Complement, Circle)) :
    ComplementLift.productLift (CircleMapAlgebra.mapInv u) = shiftedNegLift u := by
  have hfun :
      (ComplementLift.productLift (CircleMapAlgebra.mapInv u) :
          RadialMilnor.Fiber × ℝ → ℝ) =
        (shiftedNegLift u : RadialMilnor.Fiber × ℝ → ℝ) :=
    Circle.isCoveringMap_exp.eq_of_comp_eq
      (ComplementLift.productLift (CircleMapAlgebra.mapInv u)).continuous
      (shiftedNegLift u).continuous
      (by
        funext x
        exact (exp_shiftedNegLift u x).symm)
      DeckDegree.basePoint (by
        change ComplementLift.productLift
            (CircleMapAlgebra.mapInv u) DeckDegree.basePoint =
          negLift u DeckDegree.basePoint + negOffset u
        rw [negOffset]
        ring)
  ext x
  exact congrFun hfun x

theorem degree_mapInv (u : C(Complement, Circle)) :
    DeckDegree.degree (CircleMapAlgebra.mapInv u) = -DeckDegree.degree u := by
  have hdeck := DeckDegree.productLift_deckProduct
    (CircleMapAlgebra.mapInv u) DeckDegree.basePoint
  rw [productLift_mapInv_eq_shiftedNegLift] at hdeck
  change negLift u (DeckDegree.deckProduct DeckDegree.basePoint) + negOffset u =
    negLift u DeckDegree.basePoint + negOffset u +
      DeckDegree.degree (CircleMapAlgebra.mapInv u) *
        (2 * Real.pi) at hdeck
  change -ComplementLift.productLift u
      (DeckDegree.deckProduct DeckDegree.basePoint) + negOffset u =
    -ComplementLift.productLift u DeckDegree.basePoint + negOffset u +
      DeckDegree.degree (CircleMapAlgebra.mapInv u) *
        (2 * Real.pi) at hdeck
  rw [DeckDegree.productLift_deckProduct] at hdeck
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcast : (DeckDegree.degree (CircleMapAlgebra.mapInv u) : ℝ) =
      (-DeckDegree.degree u : ℤ) := by
    apply mul_right_cancel₀ htwoPi
    push_cast
    linarith
  exact_mod_cast hcast

def globalCoverLift (G : C(Complement, ℝ)) :
    C(HomeomorphismDegree.Cover, ℝ) :=
  G.comp ⟨fun x => x.1.1,
    continuous_fst.comp continuous_subtype_val⟩

def globalLiftOffset (u : C(Complement, Circle)) (G : C(Complement, ℝ)) : ℝ :=
  ComplementLift.coverLift u HomeomorphismDegree.coverBase -
    globalCoverLift G HomeomorphismDegree.coverBase

def shiftedGlobalCoverLift (u : C(Complement, Circle)) (G : C(Complement, ℝ)) :
    C(HomeomorphismDegree.Cover, ℝ) :=
  ⟨fun x => globalCoverLift G x + globalLiftOffset u G,
    (globalCoverLift G).continuous.add continuous_const⟩

theorem exp_globalLiftOffset (u : C(Complement, Circle))
    (G : C(Complement, ℝ)) (hexp : ∀ q, Circle.exp (G q) = u q) :
    Circle.exp (globalLiftOffset u G) = 1 := by
  rw [globalLiftOffset, Circle.exp_sub, ComplementLift.exp_coverLift]
  change u HomeomorphismDegree.coverBase.1.1 /
    Circle.exp (G HomeomorphismDegree.coverBase.1.1) = 1
  rw [hexp]
  exact div_self' _

theorem exp_shiftedGlobalCoverLift (u : C(Complement, Circle))
    (G : C(Complement, ℝ)) (hexp : ∀ q, Circle.exp (G q) = u q)
    (x : HomeomorphismDegree.Cover) :
    Circle.exp (shiftedGlobalCoverLift u G x) =
      Circle.exp (ComplementLift.coverLift u x) := by
  change Circle.exp (globalCoverLift G x + globalLiftOffset u G) = _
  rw [Circle.exp_add, exp_globalLiftOffset u G hexp, mul_one,
    ComplementLift.exp_coverLift]
  exact hexp x.1.1

theorem coverLift_eq_shiftedGlobalCoverLift (u : C(Complement, Circle))
    (G : C(Complement, ℝ)) (hexp : ∀ q, Circle.exp (G q) = u q) :
    ComplementLift.coverLift u = shiftedGlobalCoverLift u G := by
  have hfun : (ComplementLift.coverLift u : HomeomorphismDegree.Cover → ℝ) =
      (shiftedGlobalCoverLift u G : HomeomorphismDegree.Cover → ℝ) :=
    Circle.isCoveringMap_exp.eq_of_comp_eq
      (ComplementLift.coverLift u).continuous
      (shiftedGlobalCoverLift u G).continuous
      (by
        funext x
        exact (exp_shiftedGlobalCoverLift u G hexp x).symm)
      HomeomorphismDegree.coverBase (by
        change ComplementLift.coverLift u HomeomorphismDegree.coverBase =
          globalCoverLift G HomeomorphismDegree.coverBase +
            globalLiftOffset u G
        rw [globalLiftOffset]
        ring)
  ext x
  exact congrFun hfun x

theorem degree_eq_zero_of_global_lift (u : C(Complement, Circle))
    (G : C(Complement, ℝ)) (hexp : ∀ q, Circle.exp (G q) = u q) :
    DeckDegree.degree u = 0 := by
  have hdeck := DeckDegree.coverLift_deck u HomeomorphismDegree.coverBase
  rw [coverLift_eq_shiftedGlobalCoverLift u G hexp] at hdeck
  change globalCoverLift G (RadialCyclicCover.deck HomeomorphismDegree.coverBase) +
      globalLiftOffset u G =
    globalCoverLift G HomeomorphismDegree.coverBase + globalLiftOffset u G +
      DeckDegree.degree u * (2 * Real.pi) at hdeck
  have hinvariant :
      globalCoverLift G (RadialCyclicCover.deck HomeomorphismDegree.coverBase) =
        globalCoverLift G HomeomorphismDegree.coverBase := rfl
  rw [hinvariant] at hdeck
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcast : (DeckDegree.degree u : ℝ) = 0 := by
    apply mul_right_cancel₀ htwoPi
    linarith
  exact_mod_cast hcast

def composedLift (u : C(Complement, Circle)) (h : Complement ≃ₜ Complement) :
    C(HomeomorphismDegree.Cover, ℝ) :=
  (ComplementLift.coverLift u).comp (HomeomorphismDegree.coverActionMap h)

def composedOffset (u : C(Complement, Circle)) (h : Complement ≃ₜ Complement) : ℝ :=
  ComplementLift.coverLift (u.comp ⟨h, h.continuous⟩)
      HomeomorphismDegree.coverBase -
    composedLift u h HomeomorphismDegree.coverBase

def shiftedComposedLift (u : C(Complement, Circle))
    (h : Complement ≃ₜ Complement) : C(HomeomorphismDegree.Cover, ℝ) :=
  ⟨fun x => composedLift u h x + composedOffset u h,
    (composedLift u h).continuous.add continuous_const⟩

theorem exp_composedLift (u : C(Complement, Circle))
    (h : Complement ≃ₜ Complement) (x : HomeomorphismDegree.Cover) :
    Circle.exp (composedLift u h x) = u (h x.1.1) := by
  rw [composedLift, ContinuousMap.comp_apply, ComplementLift.exp_coverLift]
  rfl

theorem exp_composedOffset (u : C(Complement, Circle))
    (h : Complement ≃ₜ Complement) : Circle.exp (composedOffset u h) = 1 := by
  rw [composedOffset, Circle.exp_sub, ComplementLift.exp_coverLift,
    exp_composedLift]
  exact div_self' _

theorem exp_shiftedComposedLift (u : C(Complement, Circle))
    (h : Complement ≃ₜ Complement) (x : HomeomorphismDegree.Cover) :
    Circle.exp (shiftedComposedLift u h x) =
      Circle.exp (ComplementLift.coverLift (u.comp ⟨h, h.continuous⟩) x) := by
  change Circle.exp (composedLift u h x + composedOffset u h) = _
  rw [Circle.exp_add, exp_composedOffset, mul_one,
    ComplementLift.exp_coverLift, exp_composedLift]
  rfl

theorem coverLift_comp_homeomorph_eq_shifted (u : C(Complement, Circle))
    (h : Complement ≃ₜ Complement) :
    ComplementLift.coverLift (u.comp ⟨h, h.continuous⟩) =
      shiftedComposedLift u h := by
  have hfun :
      (ComplementLift.coverLift (u.comp ⟨h, h.continuous⟩) :
          HomeomorphismDegree.Cover → ℝ) =
        (shiftedComposedLift u h : HomeomorphismDegree.Cover → ℝ) :=
    Circle.isCoveringMap_exp.eq_of_comp_eq
      (ComplementLift.coverLift (u.comp ⟨h, h.continuous⟩)).continuous
      (shiftedComposedLift u h).continuous
      (by
        funext x
        exact (exp_shiftedComposedLift u h x).symm)
      HomeomorphismDegree.coverBase (by
        change ComplementLift.coverLift (u.comp ⟨h, h.continuous⟩)
            HomeomorphismDegree.coverBase =
          composedLift u h HomeomorphismDegree.coverBase + composedOffset u h
        rw [composedOffset]
        ring)
  ext x
  exact congrFun hfun x

theorem degree_comp_homeomorph (u : C(Complement, Circle))
    (h : Complement ≃ₜ Complement) :
    DeckDegree.degree (u.comp ⟨h, h.continuous⟩) =
      DeckDegree.degree u *
        DeckDegree.degree (HomeomorphismDegree.inducedCircleMap h) := by
  let v := u.comp ⟨h, h.continuous⟩
  have hdeck := DeckDegree.coverLift_deck v HomeomorphismDegree.coverBase
  rw [coverLift_comp_homeomorph_eq_shifted] at hdeck
  change composedLift u h (RadialCyclicCover.deck HomeomorphismDegree.coverBase) +
      composedOffset u h =
    composedLift u h HomeomorphismDegree.coverBase + composedOffset u h +
      DeckDegree.degree v * (2 * Real.pi) at hdeck
  change ComplementLift.coverLift u
      (HomeomorphismDegree.coverAction h
        (RadialCyclicCover.deck HomeomorphismDegree.coverBase)) +
      composedOffset u h =
    ComplementLift.coverLift u
        (HomeomorphismDegree.coverAction h HomeomorphismDegree.coverBase) +
      composedOffset u h + DeckDegree.degree v * (2 * Real.pi) at hdeck
  rw [
    HomeomorphismDegree.coverAction_deck,
    HomeomorphismDegree.coverLift_deckPow] at hdeck
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcast : (DeckDegree.degree v : ℝ) =
      (DeckDegree.degree u *
        DeckDegree.degree (HomeomorphismDegree.inducedCircleMap h) : ℤ) := by
    apply mul_right_cancel₀ htwoPi
    push_cast at hdeck ⊢
    linarith
  exact_mod_cast hcast

end

end Submission.DegreeAlgebra
