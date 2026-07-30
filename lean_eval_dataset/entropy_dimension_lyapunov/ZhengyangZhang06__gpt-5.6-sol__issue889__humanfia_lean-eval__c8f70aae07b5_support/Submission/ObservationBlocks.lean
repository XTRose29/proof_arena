import Submission.FiniteObservationEntropy

namespace Submission.Helpers

open MeasureTheory

noncomputable def observationBlock
    {M I : Type*} (T : M → M) (X : M → I) (n : ℕ) (x : M) : Fin n → I :=
  fun k => X (T^[k.val] x)

lemma measurable_observationBlock
    {M I : Type*} [MeasurableSpace M] [MeasurableSpace I]
    (T : M → M) (hT : Measurable T) (X : M → I) (hX : Measurable X) (n : ℕ) :
    Measurable (observationBlock T X n) := by
  apply measurable_pi_lambda
  intro k
  exact hX.comp (hT.iterate k.val)

def finSuccLastEquiv (I : Type*) (n : ℕ) :
    (Fin (n + 1) → I) ≃ (Fin n → I) × I where
  toFun f := (fun i => f i.castSucc, f (Fin.last n))
  invFun p := Fin.lastCases p.2 p.1
  left_inv f := by
    funext i
    cases i using Fin.lastCases <;> simp
  right_inv p := by
    apply Prod.ext
    · funext i
      simp
    · simp

lemma finSuccLastEquiv_observationBlock
    {M I : Type*} (T : M → M) (X : M → I) (n : ℕ) :
    (fun x => finSuccLastEquiv I n (observationBlock T X (n + 1) x)) =
      fun x => (observationBlock T X n x, X (T^[n] x)) := by
  funext x
  apply Prod.ext
  · funext i
    rfl
  · rfl

lemma conditionalObservationEntropy_observationBlock_le
    {M I J : Type*} [MeasurableSpace M]
    [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T : M → M) (hT : MeasurePreserving T mu mu)
    (X : M → I) (hX : Measurable X)
    (Y : M → J) (hY : Measurable Y) (n : ℕ) :
    conditionalObservationEntropy mu (observationBlock T X n)
        (observationBlock T Y n) ≤
      n * conditionalObservationEntropy mu X Y := by
  induction n with
  | zero =>
      have hXfiber : observationBlock T X 0 ⁻¹'
          ({default} : Set (Fin 0 → I)) = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        exact Subsingleton.elim _ _
      have hYfiber : observationBlock T Y 0 ⁻¹'
          ({default} : Set (Fin 0 → J)) = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        exact Subsingleton.elim _ _
      simp [conditionalObservationEntropy, hXfiber, hYfiber]
  | succ n ih =>
      let eX := finSuccLastEquiv I n
      let eY := finSuccLastEquiv J n
      have hblockX := measurable_observationBlock T hT.measurable X hX (n + 1)
      have hblockY := measurable_observationBlock T hT.measurable Y hY (n + 1)
      have hequiv := conditionalObservationEntropy_equiv mu eX eY
        (observationBlock T X (n + 1)) hblockX
        (observationBlock T Y (n + 1)) hblockY
      have hsplitX :
          (fun x => eX (observationBlock T X (n + 1) x)) =
            fun x => (observationBlock T X n x, X (T^[n] x)) := by
        exact finSuccLastEquiv_observationBlock T X n
      have hsplitY :
          (fun x => eY (observationBlock T Y (n + 1) x)) =
            fun x => (observationBlock T Y n x, Y (T^[n] x)) := by
        exact finSuccLastEquiv_observationBlock T Y n
      have hpair := conditionalObservationEntropy_pair_pair_le mu
        (observationBlock T X n)
          (measurable_observationBlock T hT.measurable X hX n)
        (fun x => X (T^[n] x)) (hX.comp (hT.measurable.iterate n))
        (observationBlock T Y n)
          (measurable_observationBlock T hT.measurable Y hY n)
        (fun x => Y (T^[n] x)) (hY.comp (hT.measurable.iterate n))
      have hcoordinate := conditionalObservationEntropy_comp_measurePreserving
        mu (T^[n]) (hT.iterate n) X hX Y hY
      calc
        conditionalObservationEntropy mu (observationBlock T X (n + 1))
            (observationBlock T Y (n + 1)) =
            conditionalObservationEntropy mu
              (fun x => (observationBlock T X n x, X (T^[n] x)))
              (fun x => (observationBlock T Y n x, Y (T^[n] x))) := by
          rw [← hsplitX, ← hsplitY]
          exact hequiv.symm
        _ ≤ conditionalObservationEntropy mu (observationBlock T X n)
              (observationBlock T Y n) +
            conditionalObservationEntropy mu (fun x => X (T^[n] x))
              (fun x => Y (T^[n] x)) := hpair
        _ ≤ n * conditionalObservationEntropy mu X Y +
            conditionalObservationEntropy mu X Y := by
          exact add_le_add ih hcoordinate.le
        _ = ((n + 1 : ℕ) : ℝ) * conditionalObservationEntropy mu X Y := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

end Submission.Helpers
