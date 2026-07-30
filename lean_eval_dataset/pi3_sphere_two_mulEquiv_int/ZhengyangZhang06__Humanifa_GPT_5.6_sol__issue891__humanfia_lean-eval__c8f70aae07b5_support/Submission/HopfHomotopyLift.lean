import Submission.HopfFiberPhase
import Submission.CircleHomotopy

open scoped unitInterval

noncomputable section

namespace Submission.HopfHomotopyLift

open Topology.Homotopy
open Submission.Helpers
open Submission.HopfLift
open Submission.HopfFiberPhase
open Submission.CircleHomotopy

/-- Postcompose a based 3-loop in the total space with the Hopf map. -/
abbrev mappedLoop {x : SphereTwo}
    (p : GenLoop (Fin 3) SphereThree (hopfBase x)) :
    GenLoop (Fin 3) SphereTwo x :=
  genLoopMap hopfContinuousMap (hopfMap_hopfBase x) p

/-- Reorder a relative homotopy as a family of paths parametrized by the
3-cube. -/
def baseHomotopyFamily {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (param : (Fin 3 → I) × I) : SphereTwo :=
  H (param.2, param.1)

lemma continuous_baseHomotopyFamily {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3))) :
    Continuous (baseHomotopyFamily H) :=
  H.toHomotopy.continuous.comp
    (continuous_snd.prodMk continuous_fst)

lemma baseHomotopyFamily_zero {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) :
    baseHomotopyFamily H (a, 0) = hopfMap (p a) := by
  calc
    baseHomotopyFamily H (a, 0) = H (0, a) := rfl
    _ = mappedLoop p a := H.apply_zero a
    _ = hopfMap (p a) := rfl

lemma baseHomotopyFamily_one {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) :
    baseHomotopyFamily H (a, 1) = hopfMap (q a) := by
  calc
    baseHomotopyFamily H (a, 1) = H (1, a) := rfl
    _ = mappedLoop q a := H.apply_one a
    _ = hopfMap (q a) := rfl

lemma baseHomotopyFamily_eq_of_boundary {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) (ha : a ∈ Cube.boundary (Fin 3)) (t : I) :
    baseHomotopyFamily H (a, t) = x := by
  calc
    baseHomotopyFamily H (a, t) =
        mappedLoop p a := H.eq_fst t ha
    _ = hopfMap (p a) := rfl
    _ = hopfMap (hopfBase x) :=
      congrArg hopfMap (p.property a ha)
    _ = x := hopfMap_hopfBase x

/-- Lift the projected relative homotopy from its prescribed initial
3-loop. -/
def liftedHomotopyFamily {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3))) :
    (Fin 3 → I) × I → SphereThree :=
  pathFamilyLift
    (baseHomotopyFamily H)
    (continuous_baseHomotopyFamily H)
    p
    p.1.continuous
    (fun a => (baseHomotopyFamily_zero H a).symm)

lemma continuous_liftedHomotopyFamily {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3))) :
    Continuous (liftedHomotopyFamily H) :=
  continuous_pathFamilyLift
    (baseHomotopyFamily H)
    (continuous_baseHomotopyFamily H)
    p
    p.1.continuous
    (fun a => (baseHomotopyFamily_zero H a).symm)

@[simp]
lemma hopfMap_liftedHomotopyFamily {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (param : (Fin 3 → I) × I) :
    hopfMap (liftedHomotopyFamily H param) =
      baseHomotopyFamily H param :=
  hopfMap_pathFamilyLift
    (baseHomotopyFamily H)
    (continuous_baseHomotopyFamily H)
    p
    p.1.continuous
    (fun a => (baseHomotopyFamily_zero H a).symm)
    param

@[simp]
lemma liftedHomotopyFamily_zero {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) :
    liftedHomotopyFamily H (a, 0) = p a :=
  pathFamilyLift_zero
    (baseHomotopyFamily H)
    (continuous_baseHomotopyFamily H)
    p
    p.1.continuous
    (fun a => (baseHomotopyFamily_zero H a).symm)
    a

lemma liftedHomotopyFamily_eq_of_boundary {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) (ha : a ∈ Cube.boundary (Fin 3)) (t : I) :
    liftedHomotopyFamily H (a, t) = hopfBase x := by
  calc
    liftedHomotopyFamily H (a, t) = p a := by
      apply pathFamilyLift_eq_of_path_eq
      intro s
      calc
        baseHomotopyFamily H (a, s) = x :=
          baseHomotopyFamily_eq_of_boundary H a ha s
        _ = hopfMap (p a) := by
          exact
            ((congrArg hopfMap (p.property a ha)).trans
              (hopfMap_hopfBase x)).symm
        _ = baseHomotopyFamily H (a, 0) :=
          (baseHomotopyFamily_zero H a).symm
    _ = hopfBase x := p.property a ha

lemma hopfMap_q_eq_lifted_one {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) :
    hopfMap (q a) = hopfMap (liftedHomotopyFamily H (a, 1)) := by
  rw [hopfMap_liftedHomotopyFamily,
    baseHomotopyFamily_one]

/-- The endpoint discrepancy of a lifted projected homotopy. -/
def endpointPhase {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) : Circle :=
  phase (q a) (liftedHomotopyFamily H (a, 1))
    (hopfMap_q_eq_lifted_one H a)

lemma continuous_endpointPhase {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3))) :
    Continuous (endpointPhase H) := by
  apply continuous_phase (fun a => hopfMap_q_eq_lifted_one H a)
  · exact q.1.continuous
  · exact (continuous_liftedHomotopyFamily H).comp
      (continuous_id.prodMk continuous_const)

lemma endpointPhase_eq_one_of_boundary {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) (ha : a ∈ Cube.boundary (Fin 3)) :
    endpointPhase H a = 1 := by
  unfold endpointPhase
  apply phase_eq_of_circleAct_eq
  rw [circleAct_one]
  exact (q.property a ha).trans
    (liftedHomotopyFamily_eq_of_boundary H a ha 1).symm

/-- The endpoint discrepancy as a based circle 3-loop. -/
def endpointPhaseGenLoop {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3))) :
    GenLoop (Fin 3) Circle (1 : Circle) :=
  ⟨⟨endpointPhase H, continuous_endpointPhase H⟩,
    endpointPhase_eq_one_of_boundary H⟩

/-- A real lift of the endpoint phase, normalized to vanish on the
boundary of the 3-cube. -/
def endpointPhaseLift {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3))) :
    C(Fin 3 → I, ℝ) :=
  circleGenLoopLift (0 : Fin 3) (endpointPhaseGenLoop H)

lemma circle_exp_endpointPhaseLift {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) :
    Circle.exp (endpointPhaseLift H a) = endpointPhase H a :=
  circle_exp_circleGenLoopLift
    (0 : Fin 3) (endpointPhaseGenLoop H) a

lemma endpointPhaseLift_eq_zero_of_boundary {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) (ha : a ∈ Cube.boundary (Fin 3)) :
    endpointPhaseLift H a = 0 :=
  circleGenLoopLift_boundary
    (0 : Fin 3) (endpointPhaseGenLoop H) a ha

/-- Correct the lifted homotopy by the inverse endpoint phase, introduced
linearly over the homotopy parameter. -/
def correctedHomotopyFamily {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (ta : I × (Fin 3 → I)) : SphereThree :=
  circleAct
    (Circle.exp (-((ta.1 : ℝ) * endpointPhaseLift H ta.2)))
    (liftedHomotopyFamily H (ta.2, ta.1))

lemma continuous_correctedHomotopyFamily {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3))) :
    Continuous (correctedHomotopyFamily H) := by
  unfold correctedHomotopyFamily
  exact continuous_circleAct.comp <|
    ((Circle.exp).continuous.comp
        (((continuous_subtype_val.comp continuous_fst).mul
          ((endpointPhaseLift H).continuous.comp continuous_snd)).neg)).prodMk
      ((continuous_liftedHomotopyFamily H).comp
        (continuous_snd.prodMk continuous_fst))

@[simp]
lemma correctedHomotopyFamily_zero {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) :
    correctedHomotopyFamily H (0, a) = p a := by
  simp [correctedHomotopyFamily]

@[simp]
lemma correctedHomotopyFamily_one {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (a : Fin 3 → I) :
    correctedHomotopyFamily H (1, a) = q a := by
  rw [correctedHomotopyFamily, show
    -(((1 : I) : ℝ) * endpointPhaseLift H a) =
      -(endpointPhaseLift H a) by simp,
    Circle.exp_neg, circle_exp_endpointPhaseLift]
  rw [← circleAct_phase
    (q a) (liftedHomotopyFamily H (a, 1))
    (hopfMap_q_eq_lifted_one H a)]
  unfold endpointPhase
  rw [← circleAct_mul]
  simp

lemma correctedHomotopyFamily_eq_of_boundary {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3)))
    (t : I) (a : Fin 3 → I) (ha : a ∈ Cube.boundary (Fin 3)) :
    correctedHomotopyFamily H (t, a) = hopfBase x := by
  rw [correctedHomotopyFamily,
    endpointPhaseLift_eq_zero_of_boundary H a ha,
    mul_zero, neg_zero, Circle.exp_zero, circleAct_one,
    liftedHomotopyFamily_eq_of_boundary H a ha t]

/-- A projected relative homotopy lifts to a relative homotopy of the
original based 3-loops. -/
def correctedHomotopy {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (H : ContinuousMap.HomotopyRel
      (mappedLoop p).1 (mappedLoop q).1
      (Cube.boundary (Fin 3))) :
    ContinuousMap.HomotopyRel p.1 q.1 (Cube.boundary (Fin 3)) where
  toHomotopy :=
    { toContinuousMap :=
        ⟨correctedHomotopyFamily H,
          continuous_correctedHomotopyFamily H⟩
      map_zero_left := correctedHomotopyFamily_zero H
      map_one_left := correctedHomotopyFamily_one H }
  prop' t a ha := by
    change correctedHomotopyFamily H (t, a) = p a
    exact (correctedHomotopyFamily_eq_of_boundary H t a ha).trans
      (p.property a ha).symm

lemma genLoop_homotopic_of_mapped_homotopic {x : SphereTwo}
    {p q : GenLoop (Fin 3) SphereThree (hopfBase x)}
    (hpq : GenLoop.Homotopic (mappedLoop p) (mappedLoop q)) :
    GenLoop.Homotopic p q :=
  hpq.map correctedHomotopy

/-- The Hopf map is injective on third homotopy groups. -/
theorem hopfHomotopyGroupMap_injective (x : SphereTwo) :
    Function.Injective (hopfHomotopyGroupMap x) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ p =>
      induction b using Quotient.inductionOn with
      | _ q =>
          apply Quotient.sound
          apply genLoop_homotopic_of_mapped_homotopic
          change (mappedLoop p) ≈ (mappedLoop q)
          have hbase :
              hopfContinuousMap (hopfBase x) = x :=
            hopfMap_hopfBase x
          change
            (Quotient.mk' (genLoopMap hopfContinuousMap hbase p) :
                HomotopyGroup.Pi 3 SphereTwo x) =
              Quotient.mk' (genLoopMap hopfContinuousMap hbase q) at hab
          exact Quotient.exact hab

/-- The Hopf fibration identifies the third homotopy groups of its total
and base spaces. -/
theorem hopfHomotopyGroupMap_bijective (x : SphereTwo) :
    Function.Bijective (hopfHomotopyGroupMap x) :=
  ⟨hopfHomotopyGroupMap_injective x,
    Submission.HopfGenLoopLift.hopfHomotopyGroupMap_surjective x⟩

end Submission.HopfHomotopyLift
