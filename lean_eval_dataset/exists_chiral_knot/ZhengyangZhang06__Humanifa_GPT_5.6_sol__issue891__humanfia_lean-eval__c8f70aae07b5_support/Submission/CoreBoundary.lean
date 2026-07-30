import Submission.CoreAction
import Submission.RadialConnected
import Mathlib.Topology.Piecewise

namespace Submission.CoreBoundary

noncomputable section

abbrev Core := RadialCore.Core

theorem coordinate_one_or_coordinate_one (q : Core) :
    CoreCoordinates.firstCoordinate q = 1 ∨
      CoreCoordinates.secondCoordinate q = 1 := by
  obtain ⟨i, j, u, rfl⟩ := CoreClassification.exists_edge q
  fin_cases i <;> fin_cases j <;>
    simp [CoreCoordinates.firstCoordinate, CoreCoordinates.secondCoordinate,
      CoreCoordinates.coordinate_edge]

def AbelianCover := {x : Core × (ℝ × ℝ) //
  Circle.exp x.2.1 = CoreCoordinates.firstCoordinate x.1 ∧
    Circle.exp x.2.2 = CoreCoordinates.secondCoordinate x.1}

instance : TopologicalSpace AbelianCover := by
  unfold AbelianCover
  infer_instance

def firstSet : Set AbelianCover :=
  {x | CoreCoordinates.firstCoordinate x.1.1 = 1}

def secondSet : Set AbelianCover :=
  {x | CoreCoordinates.secondCoordinate x.1.1 = 1}

theorem firstSet_isClosed : IsClosed firstSet := by
  apply isClosed_eq
  · exact CoreCoordinates.firstCoordinate.continuous.comp
      (continuous_fst.comp continuous_subtype_val)
  · exact continuous_const

theorem secondSet_isClosed : IsClosed secondSet := by
  apply isClosed_eq
  · exact CoreCoordinates.secondCoordinate.continuous.comp
      (continuous_fst.comp continuous_subtype_val)
  · exact continuous_const

theorem mem_firstSet_or_mem_secondSet (x : AbelianCover) :
    x ∈ firstSet ∨ x ∈ secondSet :=
  coordinate_one_or_coordinate_one x.1.1

def twistBranch (x : AbelianCover) : Circle :=
  Circle.exp (x.1.2.1 * x.1.2.2 / (2 * Real.pi))

theorem twistBranch_continuous : Continuous twistBranch := by
  unfold twistBranch
  fun_prop

theorem twistBranch_eq_one_of_mem_first_second (x : AbelianCover)
    (hxFirst : x ∈ firstSet) (hxSecond : x ∈ secondSet) :
    twistBranch x = 1 := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp (x.2.1.trans hxFirst)
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp (x.2.2.trans hxSecond)
  rw [twistBranch, hm, hn]
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have harg :
      ((m : ℝ) * (2 * Real.pi)) * ((n : ℝ) * (2 * Real.pi)) /
          (2 * Real.pi) =
        ((m * n : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp [htwoPi]
  rw [harg, Circle.exp_int_mul_two_pi]

def twist (x : AbelianCover) : Circle := by
  classical
  exact if x ∈ firstSet then twistBranch x else 1

theorem twist_continuous : Continuous twist := by
  classical
  unfold twist
  apply continuous_if
  · intro x hx
    have hxFirst : x ∈ firstSet :=
      firstSet_isClosed.frontier_subset hx
    have hxSecond : x ∈ secondSet := by
      have hsubset : firstSetᶜ ⊆ secondSet := by
        intro y hy
        exact (mem_firstSet_or_mem_secondSet y).resolve_left (by simpa using hy)
      have hxClosure : x ∈ closure firstSetᶜ := by
        apply frontier_subset_closure
        rwa [frontier_compl]
      exact closure_minimal hsubset secondSet_isClosed hxClosure
    exact twistBranch_eq_one_of_mem_first_second x hxFirst hxSecond
  · exact twistBranch_continuous.continuousOn
  · exact continuous_const.continuousOn

def twistMap : C(AbelianCover, Circle) :=
  ⟨twist, twist_continuous⟩

def deckShift (m n : ℤ) (x : AbelianCover) : AbelianCover :=
  ⟨(x.1.1, (x.1.2.1 + (m : ℝ) * (2 * Real.pi),
      x.1.2.2 + (n : ℝ) * (2 * Real.pi))), by
    constructor
    · rw [Circle.exp_add]
      rw [Circle.exp_int_mul_two_pi, mul_one, x.2.1]
    · rw [Circle.exp_add]
      rw [Circle.exp_int_mul_two_pi, mul_one, x.2.2]⟩

@[simp] theorem deckShift_point (m n : ℤ) (x : AbelianCover) :
    (deckShift m n x).1.1 = x.1.1 :=
  rfl

theorem twist_deckShift (m n : ℤ) (x : AbelianCover) :
    twist (deckShift m n x) =
      twist x * (CoreCoordinates.secondCoordinate x.1.1) ^ m := by
  classical
  by_cases hx : x ∈ firstSet
  · have hshift : deckShift m n x ∈ firstSet := hx
    rw [twist, if_pos hshift, twist, if_pos hx]
    obtain ⟨k, hk⟩ := Circle.exp_eq_one.mp (x.2.1.trans hx)
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have harg :
        (x.1.2.1 + (m : ℝ) * (2 * Real.pi)) *
              (x.1.2.2 + (n : ℝ) * (2 * Real.pi)) /
            (2 * Real.pi) =
          x.1.2.1 * x.1.2.2 / (2 * Real.pi) +
            (m : ℝ) * x.1.2.2 +
              ((n * k + m * n : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hk]
      push_cast
      field_simp [htwoPi]
    change Circle.exp
        ((x.1.2.1 + (m : ℝ) * (2 * Real.pi)) *
            (x.1.2.2 + (n : ℝ) * (2 * Real.pi)) / (2 * Real.pi)) =
      Circle.exp (x.1.2.1 * x.1.2.2 / (2 * Real.pi)) *
        (CoreCoordinates.secondCoordinate x.1.1) ^ m
    rw [harg, Circle.exp_add, Circle.exp_add,
      Circle.exp_int_mul_two_pi, mul_one, Circle.exp_intCast_mul, x.2.2]
  · have hshift : deckShift m n x ∉ firstSet := hx
    have hsecond : CoreCoordinates.secondCoordinate x.1.1 = 1 :=
      (mem_firstSet_or_mem_secondSet x).resolve_left hx
    rw [twist, if_neg hshift, twist, if_neg hx, hsecond]
    simp

def pathMul {x0 x1 y0 y1 : Circle} (alpha : Path x0 x1)
    (beta : Path y0 y1) : Path (x0 * y0) (x1 * y1) where
  toFun t := alpha t * beta t
  continuous_toFun := alpha.continuous.mul beta.continuous
  source' := by rw [alpha.source, beta.source]
  target' := by rw [alpha.target, beta.target]

theorem pathIncrement_pathMul {x0 x1 y0 y1 : Circle}
    (alpha : Path x0 x1) (beta : Path y0 y1) :
    CircleWinding.pathIncrement (pathMul alpha beta) =
      CircleWinding.pathIncrement alpha + CircleWinding.pathIncrement beta := by
  let candidate : C(unitInterval, ℝ) :=
    ⟨fun t => CircleWinding.liftedPath alpha t +
        CircleWinding.liftedPath beta t,
      (CircleWinding.liftedPath alpha).continuous.add
        (CircleWinding.liftedPath beta).continuous⟩
  have hlift : candidate = CircleWinding.liftedPath (pathMul alpha beta) := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      change Circle.exp
          (CircleWinding.liftedPath alpha t +
            CircleWinding.liftedPath beta t) =
        CircleWinding.normalizePath (pathMul alpha beta) t
      rw [Circle.exp_add, CircleWinding.exp_liftedPath,
        CircleWinding.exp_liftedPath]
      change (alpha t * x0⁻¹) * (beta t * y0⁻¹) =
        (alpha t * beta t) * (x0 * y0)⁻¹
      simp only [mul_inv_rev]
      ac_rfl
    · simp [candidate]
  have hend := DFunLike.congr_fun hlift 1
  simpa [candidate, CircleWinding.pathIncrement] using hend.symm

def pathZPow {x0 x1 : Circle} (alpha : Path x0 x1) (n : ℤ) :
    Path (x0 ^ n) (x1 ^ n) where
  toFun t := alpha t ^ n
  continuous_toFun := alpha.continuous.zpow n
  source' := by rw [alpha.source]
  target' := by rw [alpha.target]

theorem pathIncrement_pathZPow {x0 x1 : Circle} (alpha : Path x0 x1)
    (n : ℤ) :
    CircleWinding.pathIncrement (pathZPow alpha n) =
      (n : ℝ) * CircleWinding.pathIncrement alpha := by
  let candidate : C(unitInterval, ℝ) :=
    ⟨fun t => (n : ℝ) * CircleWinding.liftedPath alpha t,
      continuous_const.mul (CircleWinding.liftedPath alpha).continuous⟩
  have hlift : candidate = CircleWinding.liftedPath (pathZPow alpha n) := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' (γ_0 := by simp)).mpr
    constructor
    · funext t
      change Circle.exp ((n : ℝ) * CircleWinding.liftedPath alpha t) =
        CircleWinding.normalizePath (pathZPow alpha n) t
      rw [Circle.exp_intCast_mul, CircleWinding.exp_liftedPath]
      change (alpha t * x0⁻¹) ^ n = alpha t ^ n * (x0 ^ n)⁻¹
      rw [mul_zpow, inv_zpow]
    · simp [candidate]
  have hend := DFunLike.congr_fun hlift 1
  simpa [candidate, CircleWinding.pathIncrement] using hend.symm

theorem deckShift_continuous (m n : ℤ) : Continuous (deckShift m n) := by
  apply Continuous.subtype_mk
  fun_prop

def shiftPath (m n : ℤ) {x y : AbelianCover} (gamma : Path x y) :
    Path (deckShift m n x) (deckShift m n y) :=
  gamma.map (deckShift_continuous m n)

def coreProjection : C(AbelianCover, Core) :=
  ⟨fun x => x.1.1, continuous_fst.comp continuous_subtype_val⟩

def secondOnCover : C(AbelianCover, Circle) :=
  CoreCoordinates.secondCoordinate.comp coreProjection

def twistPath {x y : AbelianCover} (gamma : Path x y) :
    Path (twist x) (twist y) :=
  gamma.map twist_continuous

def secondPath {x y : AbelianCover} (gamma : Path x y) :
    Path (secondOnCover x) (secondOnCover y) :=
  gamma.map secondOnCover.continuous

theorem twistPath_shiftPath (m n : ℤ) {x y : AbelianCover}
    (gamma : Path x y) :
    twistPath (shiftPath m n gamma) =
      (pathMul (twistPath gamma) (pathZPow (secondPath gamma) m)).cast
        (twist_deckShift m n x) (twist_deckShift m n y) := by
  apply Path.ext
  funext t
  exact twist_deckShift m n (gamma t)

theorem twistIncrement_shiftPath (m n : ℤ) {x y : AbelianCover}
    (gamma : Path x y) :
    CircleWinding.pathIncrement (twistPath (shiftPath m n gamma)) =
      CircleWinding.pathIncrement (twistPath gamma) +
        (m : ℝ) * CircleWinding.pathIncrement (secondPath gamma) := by
  rw [twistPath_shiftPath, CircleWinding.pathIncrement_cast,
    pathIncrement_pathMul, pathIncrement_pathZPow]

def firstBaseLift (q : Core) : ℝ :=
  Classical.choose (Circle.exp_surjective (CoreCoordinates.firstCoordinate q))

theorem exp_firstBaseLift (q : Core) :
    Circle.exp (firstBaseLift q) = CoreCoordinates.firstCoordinate q :=
  Classical.choose_spec (Circle.exp_surjective (CoreCoordinates.firstCoordinate q))

def secondBaseLift (q : Core) : ℝ :=
  Classical.choose (Circle.exp_surjective (CoreCoordinates.secondCoordinate q))

theorem exp_secondBaseLift (q : Core) :
    Circle.exp (secondBaseLift q) = CoreCoordinates.secondCoordinate q :=
  Classical.choose_spec (Circle.exp_surjective (CoreCoordinates.secondCoordinate q))

def baseCover (q : Core) : AbelianCover :=
  ⟨(q, (firstBaseLift q, secondBaseLift q)),
    exp_firstBaseLift q, exp_secondBaseLift q⟩

def firstCoordinateLoop {q : Core} (gamma : Path q q) :
    Path (CoreCoordinates.firstCoordinate q)
      (CoreCoordinates.firstCoordinate q) :=
  gamma.map CoreCoordinates.firstCoordinate.continuous

def secondCoordinateLoop {q : Core} (gamma : Path q q) :
    Path (CoreCoordinates.secondCoordinate q)
      (CoreCoordinates.secondCoordinate q) :=
  gamma.map CoreCoordinates.secondCoordinate.continuous

def liftedCover {q : Core} (gamma : Path q q) : C(unitInterval, AbelianCover) :=
  ⟨fun t => ⟨(gamma t,
      (firstBaseLift q + CircleWinding.liftedLoop (firstCoordinateLoop gamma) t,
        secondBaseLift q + CircleWinding.liftedLoop (secondCoordinateLoop gamma) t)), by
      constructor
      · rw [Circle.exp_add, exp_firstBaseLift,
          CircleWinding.exp_liftedLoop]
        change CoreCoordinates.firstCoordinate q *
            (CoreCoordinates.firstCoordinate (gamma t) *
              (CoreCoordinates.firstCoordinate q)⁻¹) =
          CoreCoordinates.firstCoordinate (gamma t)
        simp [mul_comm]
      · rw [Circle.exp_add, exp_secondBaseLift,
          CircleWinding.exp_liftedLoop]
        change CoreCoordinates.secondCoordinate q *
            (CoreCoordinates.secondCoordinate (gamma t) *
              (CoreCoordinates.secondCoordinate q)⁻¹) =
          CoreCoordinates.secondCoordinate (gamma t)
        simp [mul_comm]⟩, by
    apply Continuous.subtype_mk
    exact gamma.continuous.prodMk
      ((continuous_const.add
          (CircleWinding.liftedLoop (firstCoordinateLoop gamma)).continuous).prodMk
        (continuous_const.add
          (CircleWinding.liftedLoop (secondCoordinateLoop gamma)).continuous))⟩

@[simp] theorem liftedCover_zero {q : Core} (gamma : Path q q) :
    liftedCover gamma 0 = baseCover q := by
  apply Subtype.ext
  simp [liftedCover, baseCover]

theorem liftedCover_one_of_windings_zero {q : Core} (gamma : Path q q)
    (hfirst : CircleWinding.windingReal (firstCoordinateLoop gamma) = 0)
    (hsecond : CircleWinding.windingReal (secondCoordinateLoop gamma) = 0) :
    liftedCover gamma 1 = baseCover q := by
  apply Subtype.ext
  apply Prod.ext
  · exact gamma.target
  · apply Prod.ext
    · change firstBaseLift q +
          CircleWinding.windingReal (firstCoordinateLoop gamma) =
        firstBaseLift q
      rw [hfirst, add_zero]
    · change secondBaseLift q +
          CircleWinding.windingReal (secondCoordinateLoop gamma) =
        secondBaseLift q
      rw [hsecond, add_zero]

def commutator {X : Type*} [TopologicalSpace X] {q : X}
    (alpha beta : Path q q) : Path q q :=
  alpha.trans (beta.trans (alpha.symm.trans beta.symm))

theorem windingReal_commutator {x : Circle} (alpha beta : Path x x) :
    CircleWinding.windingReal (commutator alpha beta) = 0 := by
  simp [commutator, CircleWinding.windingReal_trans]

theorem firstCoordinateLoop_commutator {q : Core} (alpha beta : Path q q) :
    firstCoordinateLoop (commutator alpha beta) =
      commutator (firstCoordinateLoop alpha) (firstCoordinateLoop beta) := by
  simp [firstCoordinateLoop, commutator]

theorem secondCoordinateLoop_commutator {q : Core} (alpha beta : Path q q) :
    secondCoordinateLoop (commutator alpha beta) =
      commutator (secondCoordinateLoop alpha) (secondCoordinateLoop beta) := by
  simp [secondCoordinateLoop, commutator]

theorem firstCoordinate_commutator_winding_zero {q : Core}
    (alpha beta : Path q q) :
    CircleWinding.windingReal
        (firstCoordinateLoop (commutator alpha beta)) = 0 := by
  rw [firstCoordinateLoop_commutator]
  exact windingReal_commutator _ _

theorem secondCoordinate_commutator_winding_zero {q : Core}
    (alpha beta : Path q q) :
    CircleWinding.windingReal
        (secondCoordinateLoop (commutator alpha beta)) = 0 := by
  rw [secondCoordinateLoop_commutator]
  exact windingReal_commutator _ _

def commutatorTwistLoop {q : Core} (alpha beta : Path q q) :
    Path (twist (baseCover q)) (twist (baseCover q)) where
  toFun t := twist (liftedCover (commutator alpha beta) t)
  continuous_toFun := twist_continuous.comp (liftedCover _).continuous
  source' := by rw [liftedCover_zero]
  target' := by
    rw [liftedCover_one_of_windings_zero _
      (firstCoordinate_commutator_winding_zero alpha beta)
      (secondCoordinate_commutator_winding_zero alpha beta)]

def commutatorIndex {q : Core} (alpha beta : Path q q) : ℝ :=
  CircleWinding.windingReal (commutatorTwistLoop alpha beta)

def firstIndex {q : Core} (gamma : Path q q) : ℤ :=
  CoreMapAlgebra.windingInt (firstCoordinateLoop gamma)

def secondIndex {q : Core} (gamma : Path q q) : ℤ :=
  CoreMapAlgebra.windingInt (secondCoordinateLoop gamma)

theorem firstIndex_spec {q : Core} (gamma : Path q q) :
    CircleWinding.windingReal (firstCoordinateLoop gamma) =
      firstIndex gamma * (2 * Real.pi) :=
  CoreMapAlgebra.windingReal_eq_windingInt_mul_two_pi _

theorem secondIndex_spec {q : Core} (gamma : Path q q) :
    CircleWinding.windingReal (secondCoordinateLoop gamma) =
      secondIndex gamma * (2 * Real.pi) :=
  CoreMapAlgebra.windingReal_eq_windingInt_mul_two_pi _

theorem liftedCover_one {q : Core} (gamma : Path q q) :
    liftedCover gamma 1 =
      deckShift (firstIndex gamma) (secondIndex gamma) (baseCover q) := by
  apply Subtype.ext
  apply Prod.ext
  · exact gamma.target
  · apply Prod.ext
    · change firstBaseLift q +
          CircleWinding.windingReal (firstCoordinateLoop gamma) =
        firstBaseLift q + (firstIndex gamma : ℝ) * (2 * Real.pi)
      rw [firstIndex_spec]
    · change secondBaseLift q +
          CircleWinding.windingReal (secondCoordinateLoop gamma) =
        secondBaseLift q + (secondIndex gamma : ℝ) * (2 * Real.pi)
      rw [secondIndex_spec]

def abelianLiftPath {q : Core} (gamma : Path q q) :
    Path (baseCover q)
      (deckShift (firstIndex gamma) (secondIndex gamma) (baseCover q)) where
  toFun := liftedCover gamma
  continuous_toFun := (liftedCover gamma).continuous
  source' := liftedCover_zero gamma
  target' := liftedCover_one gamma

theorem deckShift_comp (m n r s : ℤ) (x : AbelianCover) :
    deckShift m n (deckShift r s x) = deckShift (m + r) (n + s) x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change x.1.2.1 + (r : ℝ) * (2 * Real.pi) +
          (m : ℝ) * (2 * Real.pi) =
        x.1.2.1 + ((m + r : ℤ) : ℝ) * (2 * Real.pi)
      push_cast
      ring
    · change x.1.2.2 + (s : ℝ) * (2 * Real.pi) +
          (n : ℝ) * (2 * Real.pi) =
        x.1.2.2 + ((n + s : ℤ) : ℝ) * (2 * Real.pi)
      push_cast
      ring

def shiftedLiftPath (m n : ℤ) {q : Core} (gamma : Path q q) :
    Path (deckShift m n (baseCover q))
      (deckShift (m + firstIndex gamma) (n + secondIndex gamma)
        (baseCover q)) :=
  (shiftPath m n (abelianLiftPath gamma)).cast rfl
    (deckShift_comp m n (firstIndex gamma) (secondIndex gamma)
      (baseCover q)).symm

def alphaLiftAfterBeta {q : Core} (alpha beta : Path q q) :
    Path (deckShift (firstIndex beta) (secondIndex beta) (baseCover q))
      (deckShift (firstIndex alpha + firstIndex beta)
        (secondIndex alpha + secondIndex beta) (baseCover q)) :=
  (shiftedLiftPath (firstIndex beta) (secondIndex beta) alpha).cast rfl (by
    rw [add_comm (firstIndex alpha) (firstIndex beta),
      add_comm (secondIndex alpha) (secondIndex beta)])

def commutatorAbelianLift {q : Core} (alpha beta : Path q q) :
    Path (baseCover q) (baseCover q) :=
  (abelianLiftPath alpha).trans
    ((shiftedLiftPath (firstIndex alpha) (secondIndex alpha) beta).trans
      ((alphaLiftAfterBeta alpha beta).symm.trans (abelianLiftPath beta).symm))

theorem abelianLiftPath_projection {q : Core} (gamma : Path q q) :
    (abelianLiftPath gamma).map coreProjection.continuous = gamma := by
  apply Path.ext
  rfl

theorem shiftedLiftPath_projection (m n : ℤ) {q : Core}
    (gamma : Path q q) :
    (shiftedLiftPath m n gamma).map coreProjection.continuous = gamma := by
  apply Path.ext
  rfl

theorem alphaLiftAfterBeta_projection {q : Core} (alpha beta : Path q q) :
    (alphaLiftAfterBeta alpha beta).map coreProjection.continuous = alpha := by
  apply Path.ext
  rfl

theorem commutatorAbelianLift_projection {q : Core} (alpha beta : Path q q) :
    (commutatorAbelianLift alpha beta).map coreProjection.continuous =
      commutator alpha beta := by
  apply Path.ext
  funext t
  change coreProjection (commutatorAbelianLift alpha beta t) =
    commutator alpha beta t
  simp only [commutatorAbelianLift, commutator, Path.trans_apply]
  split_ifs <;> rfl

def firstHeight : C(AbelianCover, ℝ) :=
  ⟨fun x => x.1.2.1,
    continuous_fst.comp (continuous_snd.comp continuous_subtype_val)⟩

def secondHeight : C(AbelianCover, ℝ) :=
  ⟨fun x => x.1.2.2,
    continuous_snd.comp (continuous_snd.comp continuous_subtype_val)⟩

theorem abelianLift_unique {q : Core}
    (gamma : Path q q) (delta : Path (baseCover q) (baseCover q))
    (hprojection : delta.map coreProjection.continuous = gamma)
    (t : unitInterval) : delta t = liftedCover gamma t := by
  have hcore (u : unitInterval) : (delta u).1.1 = gamma u := by
    exact congrArg (fun path : Path q q => path u) hprojection
  have hfirst :
      (firstHeight.comp delta.toContinuousMap : unitInterval → ℝ) =
        (firstHeight.comp (liftedCover gamma) : unitInterval → ℝ) :=
    Circle.isCoveringMap_exp.eq_of_comp_eq
      (firstHeight.comp delta.toContinuousMap).continuous
      (firstHeight.comp (liftedCover gamma)).continuous
      (by
        funext u
        change Circle.exp (delta u).1.2.1 =
          Circle.exp (liftedCover gamma u).1.2.1
        rw [(delta u).2.1, (liftedCover gamma u).2.1, hcore u]
        rfl)
      0 (by
        change (delta 0).1.2.1 = (liftedCover gamma 0).1.2.1
        rw [delta.source, liftedCover_zero])
  have hsecond :
      (secondHeight.comp delta.toContinuousMap : unitInterval → ℝ) =
        (secondHeight.comp (liftedCover gamma) : unitInterval → ℝ) :=
    Circle.isCoveringMap_exp.eq_of_comp_eq
      (secondHeight.comp delta.toContinuousMap).continuous
      (secondHeight.comp (liftedCover gamma)).continuous
      (by
        funext u
        change Circle.exp (delta u).1.2.2 =
          Circle.exp (liftedCover gamma u).1.2.2
        rw [(delta u).2.2, (liftedCover gamma u).2.2, hcore u]
        rfl)
      0 (by
        change (delta 0).1.2.2 = (liftedCover gamma 0).1.2.2
        rw [delta.source, liftedCover_zero])
  apply Subtype.ext
  apply Prod.ext
  · exact hcore t
  · apply Prod.ext
    · exact congrFun hfirst t
    · exact congrFun hsecond t

def commutatorAbelianTwistLoop {q : Core} (alpha beta : Path q q) :
    Path (twist (baseCover q)) (twist (baseCover q)) :=
  (commutatorAbelianLift alpha beta).map twist_continuous

theorem commutatorAbelianTwistLoop_eq {q : Core} (alpha beta : Path q q) :
    commutatorAbelianTwistLoop alpha beta = commutatorTwistLoop alpha beta := by
  apply Path.ext
  funext t
  change twist (commutatorAbelianLift alpha beta t) =
    twist (liftedCover (commutator alpha beta) t)
  congr 1
  exact abelianLift_unique (commutator alpha beta)
    (commutatorAbelianLift alpha beta)
    (commutatorAbelianLift_projection alpha beta) t

def liftTwistIncrement {q : Core} (gamma : Path q q) : ℝ :=
  CircleWinding.pathIncrement
    ((abelianLiftPath gamma).map twist_continuous)

theorem secondPath_abelianLiftPath {q : Core} (gamma : Path q q) :
    CircleWinding.pathIncrement (secondPath (abelianLiftPath gamma)) =
      secondIndex gamma * (2 * Real.pi) := by
  have hpath : secondPath (abelianLiftPath gamma) =
      secondCoordinateLoop gamma := by
    apply Path.ext
    rfl
  have hincrement := congrArg
    (fun path => CircleWinding.pathIncrement path) hpath
  calc
    CircleWinding.pathIncrement (secondPath (abelianLiftPath gamma)) =
        CircleWinding.pathIncrement (secondCoordinateLoop gamma) := hincrement
    _ = CircleWinding.windingReal (secondCoordinateLoop gamma) :=
      CircleWinding.pathIncrement_loop _
    _ = secondIndex gamma * (2 * Real.pi) := secondIndex_spec gamma

theorem twistIncrement_shiftedLiftPath (m n : ℤ) {q : Core}
    (gamma : Path q q) :
    CircleWinding.pathIncrement
        ((shiftedLiftPath m n gamma).map twist_continuous) =
      liftTwistIncrement gamma +
        (m : ℝ) * (secondIndex gamma * (2 * Real.pi)) := by
  change CircleWinding.pathIncrement
      (((shiftPath m n (abelianLiftPath gamma)).cast rfl
        (deckShift_comp m n (firstIndex gamma) (secondIndex gamma)
          (baseCover q)).symm).map twist_continuous) = _
  rw [CircleWinding.pathIncrement_map_cast]
  change CircleWinding.pathIncrement
      (twistPath (shiftPath m n (abelianLiftPath gamma))) = _
  rw [twistIncrement_shiftPath, secondPath_abelianLiftPath]
  rfl

theorem twistIncrement_alphaLiftAfterBeta {q : Core}
    (alpha beta : Path q q) :
    CircleWinding.pathIncrement
        ((alphaLiftAfterBeta alpha beta).map twist_continuous) =
      liftTwistIncrement alpha +
        (firstIndex beta : ℝ) *
          (secondIndex alpha * (2 * Real.pi)) := by
  change CircleWinding.pathIncrement
      (((shiftedLiftPath (firstIndex beta) (secondIndex beta) alpha).cast
        rfl _).map twist_continuous) = _
  rw [CircleWinding.pathIncrement_map_cast,
    twistIncrement_shiftedLiftPath]

theorem twistIncrement_symm {x y : AbelianCover} (gamma : Path x y) :
    CircleWinding.pathIncrement (gamma.symm.map twist_continuous) =
      -CircleWinding.pathIncrement (gamma.map twist_continuous) := by
  rw [← Path.map_symm, CircleWinding.pathIncrement_symm]

theorem commutatorIndex_formula {q : Core} (alpha beta : Path q q) :
    commutatorIndex alpha beta =
      ((firstIndex alpha * secondIndex beta -
          firstIndex beta * secondIndex alpha : ℤ) : ℝ) *
        (2 * Real.pi) := by
  rw [commutatorIndex, ← commutatorAbelianTwistLoop_eq,
    ← CircleWinding.pathIncrement_loop]
  simp only [commutatorAbelianTwistLoop, commutatorAbelianLift,
    Path.map_trans, CircleWinding.pathIncrement_trans]
  rw [twistIncrement_shiftedLiftPath,
    twistIncrement_symm, twistIncrement_symm,
    twistIncrement_alphaLiftAfterBeta]
  change liftTwistIncrement alpha +
      (liftTwistIncrement beta +
        (firstIndex alpha : ℝ) *
          ((secondIndex beta : ℝ) * (2 * Real.pi)) +
        (-(liftTwistIncrement alpha +
          (firstIndex beta : ℝ) *
            ((secondIndex alpha : ℝ) * (2 * Real.pi))) +
          -liftTwistIncrement beta)) = _
  push_cast
  ring

def mappedFirstCycle (f : C(Core, Core)) :
    Path (f (CoreCycles.aVertex 0)) (f (CoreCycles.aVertex 0)) :=
  CoreCycles.firstCycle.map f.continuous

def mappedSecondCycle (f : C(Core, Core)) :
    Path (f (CoreCycles.aVertex 0)) (f (CoreCycles.aVertex 0)) :=
  CoreCycles.secondCycle.map f.continuous

theorem firstIndex_mappedFirstCycle (f : C(Core, Core)) :
    firstIndex (mappedFirstCycle f) = CoreAction.action f 0 0 := by
  have hpath : firstCoordinateLoop (mappedFirstCycle f) =
      CoreCycles.firstCycle.map
        (CoreCoordinates.firstCoordinate.comp f).continuous := by
    apply Path.ext
    rfl
  rw [firstIndex, hpath]
  rfl

theorem secondIndex_mappedFirstCycle (f : C(Core, Core)) :
    secondIndex (mappedFirstCycle f) = CoreAction.action f 1 0 := by
  have hpath : secondCoordinateLoop (mappedFirstCycle f) =
      CoreCycles.firstCycle.map
        (CoreCoordinates.secondCoordinate.comp f).continuous := by
    apply Path.ext
    rfl
  rw [secondIndex, hpath]
  rfl

theorem firstIndex_mappedSecondCycle (f : C(Core, Core)) :
    firstIndex (mappedSecondCycle f) = CoreAction.action f 0 1 := by
  have hpath : firstCoordinateLoop (mappedSecondCycle f) =
      CoreCycles.secondCycle.map
        (CoreCoordinates.firstCoordinate.comp f).continuous := by
    apply Path.ext
    rfl
  rw [firstIndex, hpath]
  rfl

theorem secondIndex_mappedSecondCycle (f : C(Core, Core)) :
    secondIndex (mappedSecondCycle f) = CoreAction.action f 1 1 := by
  have hpath : secondCoordinateLoop (mappedSecondCycle f) =
      CoreCycles.secondCycle.map
        (CoreCoordinates.secondCoordinate.comp f).continuous := by
    apply Path.ext
    rfl
  rw [secondIndex, hpath]
  rfl

theorem commutatorIndex_mappedCycles (f : C(Core, Core)) :
    commutatorIndex (mappedFirstCycle f) (mappedSecondCycle f) =
      (CoreAction.action f).det * (2 * Real.pi) := by
  rw [commutatorIndex_formula, firstIndex_mappedFirstCycle,
    secondIndex_mappedFirstCycle, firstIndex_mappedSecondCycle,
    secondIndex_mappedSecondCycle, Matrix.det_fin_two]

theorem commutatorIndex_standard :
    commutatorIndex CoreCycles.firstCycle CoreCycles.secondCycle =
      2 * Real.pi := by
  rw [commutatorIndex_formula]
  have hfirstFirst : firstIndex CoreCycles.firstCycle = 1 := by
    apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simp [firstCoordinateLoop]
  have hsecondFirst : secondIndex CoreCycles.firstCycle = 0 := by
    apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simp [secondCoordinateLoop]
  have hfirstSecond : firstIndex CoreCycles.secondCycle = 0 := by
    apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simp [firstCoordinateLoop]
  have hsecondSecond : secondIndex CoreCycles.secondCycle = 1 := by
    apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simp [secondCoordinateLoop]
  rw [hfirstFirst, hsecondFirst, hfirstSecond, hsecondSecond]
  norm_num

def PreservesBoundary (f : C(Core, Core)) : Prop :=
  commutatorIndex (mappedFirstCycle f) (mappedSecondCycle f) =
    commutatorIndex CoreCycles.firstCycle CoreCycles.secondCycle

theorem action_det_eq_one_of_preservesBoundary (f : C(Core, Core))
    (hboundary : PreservesBoundary f) : (CoreAction.action f).det = 1 := by
  rw [PreservesBoundary, commutatorIndex_mappedCycles,
    commutatorIndex_standard] at hboundary
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcast : ((CoreAction.action f).det : ℝ) = 1 := by
    apply mul_right_cancel₀ htwoPi
    simpa using hboundary
  exact_mod_cast hcast

end

end Submission.CoreBoundary
