import Mathlib

noncomputable section

open scoped unitInterval Topology
open Topology.Homotopy
open Homeomorph

namespace Submission.CircleHomotopy

variable {N : Type*} [DecidableEq N]

lemma circleGenLoopLift_initialCondition (i : N)
    (p : GenLoop N Circle (1 : Circle))
    (a : I^{j // j ≠ i}) :
    (p.1.comp (Cube.insertAt i)) ((0 : I), a) =
      Circle.exp ((ContinuousMap.const (I^{j // j ≠ i}) (0 : ℝ)) a) := by
  change p (Cube.insertAt i ((0 : I), a)) = Circle.exp 0
  calc
    p (Cube.insertAt i ((0 : I), a)) = 1 :=
      p.property _ (Cube.insertAt_boundary i (Or.inl (Or.inl rfl)))
    _ = Circle.exp 0 := Circle.exp_zero.symm

/-- Lift a generalized loop in the circle through the exponential covering.
The lift is normalized to vanish on the face whose `i`th coordinate is zero. -/
def circleGenLoopLift (i : N) (p : GenLoop N Circle (1 : Circle)) :
    C(I^N, ℝ) :=
  (Circle.isCoveringMap_exp.liftHomotopy
      (p.1.comp (Cube.insertAt i))
      (ContinuousMap.const (I^{j // j ≠ i}) (0 : ℝ))
      (circleGenLoopLift_initialCondition i p)).comp
    (Cube.splitAt i)

lemma circle_exp_circleGenLoopLift (i : N)
    (p : GenLoop N Circle (1 : Circle)) (y : I^N) :
    Circle.exp (circleGenLoopLift i p y) = p y := by
  have h := congrFun
    (Circle.isCoveringMap_exp.liftHomotopy_lifts
      (p.1.comp (Cube.insertAt i))
      (ContinuousMap.const (I^{j // j ≠ i}) (0 : ℝ))
      (circleGenLoopLift_initialCondition i p))
    (Cube.splitAt i y)
  change
    Circle.exp
        ((Circle.isCoveringMap_exp.liftHomotopy
          (p.1.comp (Cube.insertAt i))
          (ContinuousMap.const (I^{j // j ≠ i}) (0 : ℝ))
          (circleGenLoopLift_initialCondition i p))
          (Cube.splitAt i y)) =
      p y
  exact h.trans (congrArg p ((Cube.splitAt i).symm_apply_apply y))

@[simp]
lemma circleGenLoopLift_insertAt_zero (i : N)
    (p : GenLoop N Circle (1 : Circle)) (a : I^{j // j ≠ i}) :
    circleGenLoopLift i p (Cube.insertAt i (0, a)) = 0 := by
  simpa [circleGenLoopLift] using
    Circle.isCoveringMap_exp.liftHomotopy_zero
      (p.1.comp (Cube.insertAt i))
      (ContinuousMap.const (I^{j // j ≠ i}) (0 : ℝ))
      (circleGenLoopLift_initialCondition i p) a

lemma insertAt_splitAt_snd_eq (i : N) (y : I^N) (t : I)
    (h : y i = t) :
    Cube.insertAt i (t, (Cube.splitAt i y).2) = y := by
  calc
    Cube.insertAt i (t, (Cube.splitAt i y).2) =
        Cube.insertAt i (Cube.splitAt i y) := by
      apply congrArg (Cube.insertAt i)
      apply Prod.ext
      · exact h.symm
      · rfl
    _ = y := (Cube.splitAt i).symm_apply_apply y

lemma splitAt_snd_apply (i : N) (y : I^N)
    (j : {j // j ≠ i}) :
    (Cube.splitAt i y).2 j = y j := by
  rfl

lemma circleGenLoopLift_eq_zero_of_boundary_ne (i : N)
    (p : GenLoop N Circle (1 : Circle)) (y : I^N)
    (j : N) (hji : j ≠ i) (hj : y j = 0 ∨ y j = 1) :
    circleGenLoopLift i p y = 0 := by
  let a : I^{k // k ≠ i} := (Cube.splitAt i y).2
  let q : C(I, ℝ) :=
    ⟨fun t => circleGenLoopLift i p (Cube.insertAt i (t, a)), by
      fun_prop⟩
  have ha : a ⟨j, hji⟩ = 0 ∨ a ⟨j, hji⟩ = 1 := by
    simpa [a, splitAt_snd_apply] using hj
  have hq :
      q (Cube.splitAt i y).1 = q 0 :=
    Circle.isCoveringMap_exp.const_of_comp q.continuous
      (fun t t' => by
        change
          Circle.exp
              (circleGenLoopLift i p (Cube.insertAt i (t, a))) =
            Circle.exp
              (circleGenLoopLift i p (Cube.insertAt i (t', a)))
        rw [circle_exp_circleGenLoopLift,
          circle_exp_circleGenLoopLift]
        exact
          (p.property _ (Cube.insertAt_boundary i
            (Or.inr ⟨⟨j, hji⟩, ha⟩))).trans
          (p.property _ (Cube.insertAt_boundary i
            (Or.inr ⟨⟨j, hji⟩, ha⟩))).symm)
      (Cube.splitAt i y).1 0
  change
    circleGenLoopLift i p
        (Cube.insertAt i ((Cube.splitAt i y).1, a)) =
      circleGenLoopLift i p (Cube.insertAt i (0, a)) at hq
  rw [show Cube.insertAt i ((Cube.splitAt i y).1, a) = y by
      simpa [a] using (Cube.splitAt i).symm_apply_apply y,
    circleGenLoopLift_insertAt_zero] at hq
  exact hq

lemma circleGenLoopLift_boundary [Nontrivial N] (i : N)
    (p : GenLoop N Circle (1 : Circle)) (y : I^N)
    (hy : y ∈ Cube.boundary N) :
    circleGenLoopLift i p y = 0 := by
  rcases hy with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · rw [← insertAt_splitAt_snd_eq i y 0 hj,
        circleGenLoopLift_insertAt_zero]
    · obtain ⟨k, hki⟩ := exists_ne i
      let a : I^{j // j ≠ i} := (Cube.splitAt i y).2
      let a0 : I^{j // j ≠ i} := fun _ => 0
      let q : C(I^{j // j ≠ i}, ℝ) :=
        ⟨fun b => circleGenLoopLift i p (Cube.insertAt i (1, b)), by
          fun_prop⟩
      have hq : q a = q a0 :=
        Circle.isCoveringMap_exp.const_of_comp q.continuous
          (fun b b' => by
            change
              Circle.exp
                  (circleGenLoopLift i p
                    (Cube.insertAt i (1, b))) =
                Circle.exp
                  (circleGenLoopLift i p
                    (Cube.insertAt i (1, b')))
            rw [circle_exp_circleGenLoopLift,
              circle_exp_circleGenLoopLift]
            exact
              (p.property _ (Cube.insertAt_boundary i
                (Or.inl (Or.inr rfl)))).trans
              (p.property _ (Cube.insertAt_boundary i
                (Or.inl (Or.inr rfl)))).symm)
          a a0
      have ha0 :
          circleGenLoopLift i p (Cube.insertAt i (1, a0)) = 0 := by
        apply circleGenLoopLift_eq_zero_of_boundary_ne i p _ k hki
        left
        rw [funSplitAt_symm_apply, dif_neg hki]
      change
        circleGenLoopLift i p (Cube.insertAt i (1, a)) =
          circleGenLoopLift i p (Cube.insertAt i (1, a0)) at hq
      rw [show Cube.insertAt i (1, a) = y by
          exact insertAt_splitAt_snd_eq i y 1 hj,
        ha0] at hq
      exact hq
  · exact circleGenLoopLift_eq_zero_of_boundary_ne i p y j hji hj

/-- Every generalized loop in the circle with at least two cubical
coordinates is homotopic relative to the boundary to the constant loop. -/
lemma circleGenLoop_homotopic_const [Nontrivial N] (i : N)
    (p : GenLoop N Circle (1 : Circle)) :
    GenLoop.Homotopic p GenLoop.const := by
  refine ⟨{
    toHomotopy := {
      toContinuousMap :=
        ⟨fun ty =>
          Circle.exp
            ((1 - (ty.1 : ℝ)) * circleGenLoopLift i p ty.2), by
          fun_prop⟩
      map_zero_left := ?_
      map_one_left := ?_ }
    prop' := ?_ }⟩
  · intro y
    change
      Circle.exp
          ((1 - ((0 : I) : ℝ)) * circleGenLoopLift i p y) =
        p y
    simpa using circle_exp_circleGenLoopLift i p y
  · intro y
    change
      Circle.exp
          ((1 - ((1 : I) : ℝ)) * circleGenLoopLift i p y) =
        (1 : Circle)
    simp
  · intro t y hy
    change
      Circle.exp
          ((1 - (t : ℝ)) * circleGenLoopLift i p y) =
        p y
    calc
      Circle.exp
          ((1 - (t : ℝ)) * circleGenLoopLift i p y) =
          1 := by
            rw [circleGenLoopLift_boundary i p y hy]
            simp
      _ = p y := (p.property y hy).symm

/-- Higher homotopy groups of the circle are subsingletons.  The
`Nontrivial N` hypothesis is exactly the statement that the cubical
dimension has at least two coordinates. -/
theorem circleHigherHomotopyGroup_subsingleton [Nontrivial N] :
    Subsingleton (HomotopyGroup N Circle (1 : Circle)) where
  allEq a b := by
    induction a using Quotient.inductionOn with
    | _ p =>
      induction b using Quotient.inductionOn with
      | _ q =>
        apply Quotient.sound
        exact
          (circleGenLoop_homotopic_const (Classical.arbitrary N) p).trans
            (circleGenLoop_homotopic_const
              (Classical.arbitrary N) q).symm

instance : Subsingleton (HomotopyGroup.Pi 2 Circle (1 : Circle)) :=
  circleHigherHomotopyGroup_subsingleton

instance : Subsingleton (HomotopyGroup.Pi 3 Circle (1 : Circle)) :=
  circleHigherHomotopyGroup_subsingleton

end Submission.CircleHomotopy
