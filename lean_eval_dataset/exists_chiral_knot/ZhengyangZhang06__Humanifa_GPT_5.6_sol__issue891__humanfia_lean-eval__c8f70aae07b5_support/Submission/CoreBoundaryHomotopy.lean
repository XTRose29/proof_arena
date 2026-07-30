import Submission.CoreBoundary
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

set_option maxHeartbeats 1000000

namespace Submission.CoreBoundary

noncomputable section

def commutatorCoverLoop {q : Core} (alpha beta : Path q q) :
    Path (baseCover q) (baseCover q) where
  toFun := liftedCover (commutator alpha beta)
  continuous_toFun := (liftedCover (commutator alpha beta)).continuous
  source' := liftedCover_zero _
  target' := liftedCover_one_of_windings_zero _
    (firstCoordinate_commutator_winding_zero alpha beta)
    (secondCoordinate_commutator_winding_zero alpha beta)

def circleExpMap : C(ℝ, Circle) :=
  ⟨Circle.exp, Circle.exp.continuous⟩

theorem firstHeight_commutatorCoverLoop_exp {q : Core}
    (alpha beta : Path q q) (t : unitInterval) :
    Circle.exp (firstHeight (commutatorCoverLoop alpha beta t)) =
      CoreCoordinates.firstCoordinate (commutator alpha beta t) :=
  (commutatorCoverLoop alpha beta t).2.1

theorem secondHeight_commutatorCoverLoop_exp {q : Core}
    (alpha beta : Path q q) (t : unitInterval) :
    Circle.exp (secondHeight (commutatorCoverLoop alpha beta t)) =
      CoreCoordinates.secondCoordinate (commutator alpha beta t) :=
  (commutatorCoverLoop alpha beta t).2.2

theorem commutatorIndex_eq_of_commutator_homotopic {q : Core}
    {alpha beta alpha' beta' : Path q q}
    (hcomm : (commutator alpha beta).Homotopic
      (commutator alpha' beta')) :
    commutatorIndex alpha beta = commutatorIndex alpha' beta' := by
  rcases hcomm with ⟨Hcore⟩
  let firstLeft := (commutatorCoverLoop alpha beta).map firstHeight.continuous
  let firstRight := (commutatorCoverLoop alpha' beta').map firstHeight.continuous
  let secondLeft := (commutatorCoverLoop alpha beta).map secondHeight.continuous
  let secondRight := (commutatorCoverLoop alpha' beta').map secondHeight.continuous
  let HfirstBase := Hcore.map CoreCoordinates.firstCoordinate
  let HsecondBase := Hcore.map CoreCoordinates.secondCoordinate
  have hfirstLeft : Circle.exp ∘ firstLeft.toContinuousMap =
      (firstCoordinateLoop (commutator alpha beta) : unitInterval → Circle) := by
    funext t
    exact firstHeight_commutatorCoverLoop_exp alpha beta t
  have hfirstRight : Circle.exp ∘ firstRight.toContinuousMap =
      (firstCoordinateLoop (commutator alpha' beta') : unitInterval → Circle) := by
    funext t
    exact firstHeight_commutatorCoverLoop_exp alpha' beta' t
  have hsecondLeft : Circle.exp ∘ secondLeft.toContinuousMap =
      (secondCoordinateLoop (commutator alpha beta) : unitInterval → Circle) := by
    funext t
    exact secondHeight_commutatorCoverLoop_exp alpha beta t
  have hsecondRight : Circle.exp ∘ secondRight.toContinuousMap =
      (secondCoordinateLoop (commutator alpha' beta') : unitInterval → Circle) := by
    funext t
    exact secondHeight_commutatorCoverLoop_exp alpha' beta' t
  let hfirstZero : ∀ t, HfirstBase (0, t) = Circle.exp (firstLeft t) :=
    fun t => (HfirstBase.apply_zero t).trans (congrFun hfirstLeft t).symm
  let hsecondZero : ∀ t, HsecondBase (0, t) = Circle.exp (secondLeft t) :=
    fun t => (HsecondBase.apply_zero t).trans (congrFun hsecondLeft t).symm
  let Hfirst : firstLeft.Homotopy firstRight :=
    Circle.isCoveringMap_exp.liftHomotopyRel HfirstBase
      ⟨0, by simp, by simp [firstLeft, firstRight, commutatorCoverLoop]⟩
      hfirstLeft hfirstRight
  let Hsecond : secondLeft.Homotopy secondRight :=
    Circle.isCoveringMap_exp.liftHomotopyRel HsecondBase
      ⟨0, by simp, by simp [secondLeft, secondRight, commutatorCoverLoop]⟩
      hsecondLeft hsecondRight
  have Hfirst_lifts (x : unitInterval × unitInterval) :
      Circle.exp (Hfirst x) = CoreCoordinates.firstCoordinate (Hcore x) := by
    change Circle.exp
        (Circle.isCoveringMap_exp.liftHomotopy HfirstBase firstLeft.toContinuousMap
          hfirstZero x) = HfirstBase x
    exact congrFun
      (Circle.isCoveringMap_exp.liftHomotopy_lifts HfirstBase
        firstLeft.toContinuousMap hfirstZero) x
  have Hsecond_lifts (x : unitInterval × unitInterval) :
      Circle.exp (Hsecond x) = CoreCoordinates.secondCoordinate (Hcore x) := by
    change Circle.exp
        (Circle.isCoveringMap_exp.liftHomotopy HsecondBase secondLeft.toContinuousMap
          hsecondZero x) = HsecondBase x
    exact congrFun
      (Circle.isCoveringMap_exp.liftHomotopy_lifts HsecondBase
        secondLeft.toContinuousMap hsecondZero) x
  let Hcover : (commutatorCoverLoop alpha beta).Homotopy
      (commutatorCoverLoop alpha' beta') :=
    { toFun := fun x =>
        ⟨(Hcore x, (Hfirst x, Hsecond x)), Hfirst_lifts x, Hsecond_lifts x⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact Hcore.continuous.prodMk
          (Hfirst.continuous.prodMk Hsecond.continuous)
      map_zero_left := by
        intro t
        apply Subtype.ext
        apply Prod.ext
        · exact Hcore.map_zero_left t
        · apply Prod.ext
          · exact Hfirst.map_zero_left t
          · exact Hsecond.map_zero_left t
      map_one_left := by
        intro t
        apply Subtype.ext
        apply Prod.ext
        · exact Hcore.map_one_left t
        · apply Prod.ext
          · exact Hfirst.map_one_left t
          · exact Hsecond.map_one_left t
      prop' := by
        intro s t ht
        apply Subtype.ext
        apply Prod.ext
        · exact Hcore.prop s t ht
        · apply Prod.ext
          · exact Hfirst.prop s t ht
          · exact Hsecond.prop s t ht }
  have Htwist := Hcover.map twistMap
  have hleft :
      (commutatorCoverLoop alpha beta).map twist_continuous =
        commutatorTwistLoop alpha beta := by
    apply Path.ext
    rfl
  have hright :
      (commutatorCoverLoop alpha' beta').map twist_continuous =
        commutatorTwistLoop alpha' beta' := by
    apply Path.ext
    rfl
  have htwist : (commutatorTwistLoop alpha beta).Homotopic
      (commutatorTwistLoop alpha' beta') :=
    ⟨Htwist.cast hleft hright⟩
  exact CircleWinding.windingReal_eq_of_homotopic htwist

def transportLoop {q q' : Core} (lambda : Path q q') (gamma : Path q' q') :
    Path q q :=
  lambda.trans (gamma.trans lambda.symm)

theorem firstCoordinateLoop_transportLoop {q q' : Core}
    (lambda : Path q q') (gamma : Path q' q') :
    firstCoordinateLoop (transportLoop lambda gamma) =
      (lambda.map CoreCoordinates.firstCoordinate.continuous).trans
        ((firstCoordinateLoop gamma).trans
          (lambda.map CoreCoordinates.firstCoordinate.continuous).symm) := by
  simp [firstCoordinateLoop, transportLoop]

theorem secondCoordinateLoop_transportLoop {q q' : Core}
    (lambda : Path q q') (gamma : Path q' q') :
    secondCoordinateLoop (transportLoop lambda gamma) =
      (lambda.map CoreCoordinates.secondCoordinate.continuous).trans
        ((secondCoordinateLoop gamma).trans
          (lambda.map CoreCoordinates.secondCoordinate.continuous).symm) := by
  simp [secondCoordinateLoop, transportLoop]

theorem firstIndex_transportLoop {q q' : Core}
    (lambda : Path q q') (gamma : Path q' q') :
    firstIndex (transportLoop lambda gamma) = firstIndex gamma := by
  apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
  rw [firstCoordinateLoop_transportLoop, ← CircleWinding.pathIncrement_loop,
    CircleWinding.pathIncrement_trans, CircleWinding.pathIncrement_trans,
    CircleWinding.pathIncrement_symm, CircleWinding.pathIncrement_loop,
    firstIndex_spec]
  ring

theorem secondIndex_transportLoop {q q' : Core}
    (lambda : Path q q') (gamma : Path q' q') :
    secondIndex (transportLoop lambda gamma) = secondIndex gamma := by
  apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
  rw [secondCoordinateLoop_transportLoop, ← CircleWinding.pathIncrement_loop,
    CircleWinding.pathIncrement_trans, CircleWinding.pathIncrement_trans,
    CircleWinding.pathIncrement_symm, CircleWinding.pathIncrement_loop,
    secondIndex_spec]
  ring

theorem commutatorIndex_transportLoop {q q' : Core}
    (lambda : Path q q') (alpha beta : Path q' q') :
    commutatorIndex (transportLoop lambda alpha) (transportLoop lambda beta) =
      commutatorIndex alpha beta := by
  rw [commutatorIndex_formula, commutatorIndex_formula,
    firstIndex_transportLoop, secondIndex_transportLoop,
    firstIndex_transportLoop, secondIndex_transportLoop]

theorem quotient_symm_trans_assoc {q q' q'' : Core}
    (alpha : Path.Homotopic.Quotient q q')
    (beta : Path.Homotopic.Quotient q' q'') :
    alpha.symm.trans (alpha.trans beta) = beta := by
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

theorem commutator_transportLoop_homotopic {q q' : Core}
    (lambda : Path q q') (alpha beta : Path q' q') :
    (transportLoop lambda (commutator alpha beta)).Homotopic
      (commutator (transportLoop lambda alpha)
        (transportLoop lambda beta)) := by
  apply Path.Homotopic.Quotient.exact
  simp [transportLoop, commutator, Path.Homotopic.Quotient.trans_assoc,
    quotient_symm_trans_assoc]

theorem commutatorIndex_eq_of_commutator_freeHomotopy
    {q q' : Core} {alpha beta : Path q q} {alpha' beta' : Path q' q'}
    (H : (commutator alpha beta : C(unitInterval, Core)).Homotopy
      (commutator alpha' beta'))
    (hloop : ∀ s : unitInterval, H (s, 1) = H (s, 0)) :
    commutatorIndex alpha beta = commutatorIndex alpha' beta' := by
  let gamma := commutator alpha beta
  let delta := commutator alpha' beta'
  let lambda : Path q q' :=
    (H.evalAt 0).cast gamma.source.symm delta.source.symm
  let lambdaEnd : Path q q' :=
    (H.evalAt 1).cast gamma.target.symm delta.target.symm
  have hside : lambdaEnd = lambda := by
    apply Path.ext
    funext s
    exact hloop s
  rcases Path.Homotopic.map_trans_evalAt H Path.id with ⟨Hsquare⟩
  let HsquareCast := Hsquare.pathCast gamma.source.symm delta.target.symm
  have hleft :
      ((Path.id.map gamma.continuous).trans (H.evalAt 1)).cast
          gamma.source.symm delta.target.symm =
        gamma.trans lambda := by
    apply Path.ext
    rw [← hside]
    rfl
  have hright :
      ((H.evalAt 0).trans (Path.id.map delta.continuous)).cast
          gamma.source.symm delta.target.symm =
        lambda.trans delta := by
    apply Path.ext
    rfl
  have hsquare : (gamma.trans lambda).Homotopic (lambda.trans delta) :=
    ⟨HsquareCast.cast hleft hright⟩
  have hquotient := Path.Homotopic.Quotient.eq.mpr hsquare
  have hquotientComp := congrArg
    (fun p => p.trans (Path.Homotopic.Quotient.mk lambda.symm)) hquotient
  have hbased : gamma.Homotopic (transportLoop lambda delta) := by
    apply Path.Homotopic.Quotient.exact
    simpa [transportLoop, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.trans_assoc] using hquotientComp
  have htransported : gamma.Homotopic
      (commutator (transportLoop lambda alpha')
        (transportLoop lambda beta')) :=
    hbased.trans (commutator_transportLoop_homotopic lambda alpha' beta')
  calc
    commutatorIndex alpha beta =
        commutatorIndex (transportLoop lambda alpha')
          (transportLoop lambda beta') :=
      commutatorIndex_eq_of_commutator_homotopic htransported
    _ = commutatorIndex alpha' beta' :=
      commutatorIndex_transportLoop lambda alpha' beta'

end

end Submission.CoreBoundary
