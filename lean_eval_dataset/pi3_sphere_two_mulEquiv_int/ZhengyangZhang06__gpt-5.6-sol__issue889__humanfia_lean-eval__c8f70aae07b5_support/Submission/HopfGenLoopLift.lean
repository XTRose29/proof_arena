import Submission.HopfLift

open scoped unitInterval

noncomputable section

namespace Submission.HopfGenLoopLift

open Topology.Homotopy
open Submission.Helpers
open Submission.HopfLift

/-- The two coordinates left after splitting a 3-cube at coordinate zero. -/
abbrev SideIndex :=
  {j : Fin 3 // j ≠ 0}

/-- The square parametrizing the paths parallel to coordinate zero. -/
abbrev SideCube :=
  SideIndex → I

/-- Regard a based 3-loop as a compact family of paths in its zeroth
coordinate. -/
def baseFamily {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (p : SideCube × I) :
    SphereTwo :=
  q (Cube.insertAt (0 : Fin 3) (p.2, p.1))

lemma continuous_baseFamily {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    Continuous (baseFamily q) :=
  q.1.continuous.comp
    ((Cube.insertAt (0 : Fin 3)).continuous.comp
      (continuous_snd.prodMk continuous_fst))

@[simp]
lemma baseFamily_zero {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) :
    baseFamily q (a, 0) = x :=
  q.property _
    (Cube.insertAt_boundary (0 : Fin 3) (Or.inl (Or.inl rfl)))

lemma baseFamily_eq_of_side_boundary {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube)
    (ha : a ∈ Cube.boundary SideIndex) (t : I) :
    baseFamily q (a, t) = x :=
  q.property _ (Cube.insertAt_boundary (0 : Fin 3) (Or.inr ha))

@[simp]
lemma baseFamily_one {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) :
    baseFamily q (a, 1) = x :=
  q.property _
    (Cube.insertAt_boundary (0 : Fin 3) (Or.inl (Or.inr rfl)))

/-- Lift the coordinate-zero path family, starting at the chosen point of
the Hopf fiber over the loop base point. -/
def liftedFamily {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    SideCube × I → SphereThree :=
  pathFamilyLift
    (baseFamily q)
    (continuous_baseFamily q)
    (fun _ => hopfBase x)
    continuous_const
    (fun a => by simp)

lemma continuous_liftedFamily {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    Continuous (liftedFamily q) :=
  continuous_pathFamilyLift
    (baseFamily q)
    (continuous_baseFamily q)
    (fun _ => hopfBase x)
    continuous_const
    (fun a => by simp)

@[simp]
lemma hopfMap_liftedFamily {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (p : SideCube × I) :
    hopfMap (liftedFamily q p) = baseFamily q p :=
  hopfMap_pathFamilyLift
    (baseFamily q)
    (continuous_baseFamily q)
    (fun _ => hopfBase x)
    continuous_const
    (fun a => by simp)
    p

@[simp]
lemma liftedFamily_zero {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) :
    liftedFamily q (a, 0) = hopfBase x :=
  pathFamilyLift_zero
    (baseFamily q)
    (continuous_baseFamily q)
    (fun _ => hopfBase x)
    continuous_const
    (fun a => by simp)
    a

lemma liftedFamily_eq_of_side_boundary {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube)
    (ha : a ∈ Cube.boundary SideIndex) (t : I) :
    liftedFamily q (a, t) = hopfBase x := by
  apply pathFamilyLift_eq_of_path_eq
  intro s
  rw [baseFamily_eq_of_side_boundary q a ha s,
    baseFamily_zero q a]

/-- The endpoint of the lifted path, regarded as a point in the original
Hopf fiber. -/
def topFiber {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) :
    HopfFiber (hopfBase x) :=
  ⟨liftedFamily q (a, 1), by
    rw [hopfMap_liftedFamily, baseFamily_one, hopfMap_hopfBase]⟩

lemma continuous_topFiber {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    Continuous (topFiber q) :=
  ((continuous_liftedFamily q).comp
    (continuous_id.prodMk continuous_const)).subtype_mk _

/-- The phase accumulated on the top face by coordinate-zero path
lifting. -/
def topPhase {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) : Circle :=
  hopfFiberPhaseContinuous (hopfBase x) (topFiber q a)

lemma continuous_topPhase {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    Continuous (topPhase q) :=
  (continuous_hopfFiberPhaseContinuous (hopfBase x)).comp
    (continuous_topFiber q)

@[simp]
lemma hopfFiberPhaseContinuous_self (z : SphereThree) :
    hopfFiberPhaseContinuous z
        (⟨z, rfl⟩ : HopfFiber z) =
      1 := by
  have h :=
    (hopfFiberHomeomorphCircle z).apply_symm_apply (1 : Circle)
  simpa [hopfFiberHomeomorphCircle] using h

lemma topPhase_eq_one_of_boundary {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube)
    (ha : a ∈ Cube.boundary SideIndex) :
    topPhase q a = 1 := by
  rw [topPhase, show
    topFiber q a =
        (⟨hopfBase x, rfl⟩ : HopfFiber (hopfBase x)) by
      apply Subtype.ext
      exact liftedFamily_eq_of_side_boundary q a ha 1]
  exact hopfFiberPhaseContinuous_self (hopfBase x)

/-- The top-face phase as a generalized circle loop. -/
def topPhaseGenLoop {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    GenLoop SideIndex Circle (1 : Circle) :=
  ⟨⟨topPhase q, continuous_topPhase q⟩,
    topPhase_eq_one_of_boundary q⟩

/-- A fixed coordinate used to normalize the real lift of the top-face
phase. -/
def phaseLiftIndex : SideIndex :=
  ⟨1, by decide⟩

/-- The two-dimensional side-index type has two distinct coordinates. -/
instance : Nontrivial SideIndex :=
  ⟨⟨⟨1, by decide⟩, ⟨2, by decide⟩, by decide⟩⟩

/-- The normalized real lift of the top-face phase through
`Circle.exp`. -/
def topPhaseLift {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) : ℝ :=
  Submission.CircleHomotopy.circleGenLoopLift phaseLiftIndex
    (topPhaseGenLoop q) a

lemma continuous_topPhaseLift {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    Continuous (topPhaseLift q) :=
  (Submission.CircleHomotopy.circleGenLoopLift phaseLiftIndex
    (topPhaseGenLoop q)).continuous

@[simp]
lemma exp_topPhaseLift {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) :
    Circle.exp (topPhaseLift q a) = topPhase q a :=
  Submission.CircleHomotopy.circle_exp_circleGenLoopLift
    phaseLiftIndex (topPhaseGenLoop q) a

lemma topPhaseLift_eq_zero_of_boundary {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube)
    (ha : a ∈ Cube.boundary SideIndex) :
    topPhaseLift q a = 0 :=
  Submission.CircleHomotopy.circleGenLoopLift_boundary
    phaseLiftIndex (topPhaseGenLoop q) a ha

/-- Interpolate the accumulated top-face phase from one on the bottom
face to the full phase on the top face. -/
def phaseCorrection {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (p : SideCube × I) : Circle :=
  Circle.exp ((p.2 : ℝ) * topPhaseLift q p.1)

lemma continuous_phaseCorrection {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    Continuous (phaseCorrection q) := by
  unfold phaseCorrection
  exact
    Circle.exp.continuous.comp
      ((continuous_subtype_val.comp continuous_snd).mul
        ((continuous_topPhaseLift q).comp continuous_fst))

@[simp]
lemma phaseCorrection_zero {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) :
    phaseCorrection q (a, 0) = 1 := by
  simp [phaseCorrection]

@[simp]
lemma phaseCorrection_one {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) :
    phaseCorrection q (a, 1) = topPhase q a := by
  unfold phaseCorrection
  change
    Circle.exp (((1 : I) : ℝ) * topPhaseLift q a) =
      topPhase q a
  norm_num [exp_topPhaseLift]

lemma phaseCorrection_eq_one_of_boundary {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube)
    (ha : a ∈ Cube.boundary SideIndex) (t : I) :
    phaseCorrection q (a, t) = 1 := by
  rw [phaseCorrection, topPhaseLift_eq_zero_of_boundary q a ha]
  simp

/-- Remove the accumulated top-face phase from the uncorrected path
family. -/
def correctedFamily {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (p : SideCube × I) :
    SphereThree :=
  circleAct (phaseCorrection q p)⁻¹ (liftedFamily q p)

lemma continuous_correctedFamily {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    Continuous (correctedFamily q) := by
  unfold correctedFamily
  exact continuous_circleAct.comp
    ((continuous_phaseCorrection q).inv.prodMk
      (continuous_liftedFamily q))

@[simp]
lemma hopfMap_correctedFamily {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (p : SideCube × I) :
    hopfMap (correctedFamily q p) = baseFamily q p := by
  rw [correctedFamily, hopfMap_circleAct, hopfMap_liftedFamily]

@[simp]
lemma correctedFamily_zero {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) :
    correctedFamily q (a, 0) = hopfBase x := by
  rw [correctedFamily, phaseCorrection_zero, inv_one, circleAct_one,
    liftedFamily_zero]

lemma correctedFamily_eq_of_side_boundary {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube)
    (ha : a ∈ Cube.boundary SideIndex) (t : I) :
    correctedFamily q (a, t) = hopfBase x := by
  rw [correctedFamily, phaseCorrection_eq_one_of_boundary q a ha,
    inv_one, circleAct_one,
    liftedFamily_eq_of_side_boundary q a ha]

@[simp]
lemma correctedFamily_one {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (a : SideCube) :
    correctedFamily q (a, 1) = hopfBase x := by
  rw [correctedFamily, phaseCorrection_one]
  have hphase :=
    circleAct_hopfFiberPhaseContinuous (hopfBase x) (topFiber q a)
  change
    circleAct (topPhase q a) (hopfBase x) =
      liftedFamily q (a, 1) at hphase
  rw [← hphase, ← circleAct_mul]
  simp

/-- Swap the factors produced by `Cube.splitAt` into the order expected by
`liftedFamily`. -/
def splitParameters (t : Fin 3 → I) : SideCube × I :=
  ((Cube.splitAt (0 : Fin 3) t).2,
    (Cube.splitAt (0 : Fin 3) t).1)

lemma continuous_splitParameters :
    Continuous splitParameters :=
  (continuous_snd.prodMk continuous_fst).comp
    (Cube.splitAt (0 : Fin 3)).continuous

/-- The uncorrected lift written on the original 3-cube. -/
def liftedCube {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (t : Fin 3 → I) :
    SphereThree :=
  liftedFamily q (splitParameters t)

lemma continuous_liftedCube {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    Continuous (liftedCube q) :=
  (continuous_liftedFamily q).comp continuous_splitParameters

@[simp]
lemma hopfMap_liftedCube {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (t : Fin 3 → I) :
    hopfMap (liftedCube q t) = q t := by
  rw [liftedCube, hopfMap_liftedFamily]
  change
    q (Cube.insertAt (0 : Fin 3)
      (Cube.splitAt (0 : Fin 3) t)) = q t
  exact congrArg q ((Cube.splitAt (0 : Fin 3)).symm_apply_apply t)

/-- The corrected lift written on the original 3-cube. -/
def correctedCube {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (t : Fin 3 → I) :
    SphereThree :=
  correctedFamily q (splitParameters t)

lemma continuous_correctedCube {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    Continuous (correctedCube q) :=
  (continuous_correctedFamily q).comp continuous_splitParameters

@[simp]
lemma hopfMap_correctedCube {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (t : Fin 3 → I) :
    hopfMap (correctedCube q t) = q t := by
  rw [correctedCube, hopfMap_correctedFamily]
  change
    q (Cube.insertAt (0 : Fin 3)
      (Cube.splitAt (0 : Fin 3) t)) = q t
  exact congrArg q ((Cube.splitAt (0 : Fin 3)).symm_apply_apply t)

lemma correctedCube_boundary {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (t : Fin 3 → I)
    (ht : t ∈ Cube.boundary (Fin 3)) :
    correctedCube q t = hopfBase x := by
  obtain ⟨j, hj⟩ := ht
  by_cases hj0 : j = 0
  · subst j
    rcases hj with hj | hj
    · rw [correctedCube, splitParameters, show
        (Cube.splitAt (0 : Fin 3) t).1 = 0 by
          exact hj,
        correctedFamily_zero]
    · rw [correctedCube, splitParameters, show
        (Cube.splitAt (0 : Fin 3) t).1 = 1 by
          exact hj,
        correctedFamily_one]
  · apply correctedFamily_eq_of_side_boundary
    exact ⟨⟨j, hj0⟩, hj⟩

/-- A boundary-fixed lift of every based 3-loop through the Hopf map. -/
def liftedGenLoop {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) :
    GenLoop (Fin 3) SphereThree (hopfBase x) :=
  ⟨⟨correctedCube q, continuous_correctedCube q⟩,
    correctedCube_boundary q⟩

@[simp]
lemma hopfMap_liftedGenLoop {x : SphereTwo}
    (q : GenLoop (Fin 3) SphereTwo x) (t : Fin 3 → I) :
    hopfMap (liftedGenLoop q t) = q t :=
  hopfMap_correctedCube q t

/-- Every based 3-loop in the 2-sphere has a boundary-fixed lift through
the Hopf map, so the induced map on third homotopy groups is surjective. -/
theorem hopfHomotopyGroupMap_surjective (x : SphereTwo) :
    Function.Surjective (hopfHomotopyGroupMap x) := by
  intro a
  induction a using Quotient.inductionOn with
  | _ q =>
      refine ⟨Quotient.mk' (liftedGenLoop q), ?_⟩
      change
        homotopyGroupMap hopfContinuousMap (hopfMap_hopfBase x)
            (Quotient.mk' (liftedGenLoop q)) =
          Quotient.mk' q
      rw [homotopyGroupMap_mk]
      apply congrArg Quotient.mk'
      apply Subtype.ext
      apply ContinuousMap.ext
      intro t
      exact hopfMap_liftedGenLoop q t

end Submission.HopfGenLoopLift
