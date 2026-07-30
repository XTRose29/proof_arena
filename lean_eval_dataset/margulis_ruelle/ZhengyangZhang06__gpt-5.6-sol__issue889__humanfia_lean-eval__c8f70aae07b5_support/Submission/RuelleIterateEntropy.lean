import Submission.RuelleEntropyRate

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

def flattenObservationEquiv (I : Type*) (m n : ℕ) :
    (Fin m → Fin n → I) ≃ (Fin (m * n) → I) where
  toFun f k :=
    let p := finProdFinEquiv.symm k
    f p.1 p.2
  invFun f i j := f (finProdFinEquiv (i, j))
  left_inv f := by
    funext i j
    change f (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
        (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = f i j
    rw [Equiv.symm_apply_apply]
  right_inv f := by
    funext k
    change f (finProdFinEquiv (finProdFinEquiv.symm k)) = f k
    rw [Equiv.apply_symm_apply]

lemma flattenObservationEquiv_observationBlock
    {M I : Type*} (T : M → M) (Y : M → I) (m n : ℕ) (x : M) :
    flattenObservationEquiv I m n
        (observationBlock (T^[n]) (observationBlock T Y n) m x) =
      observationBlock T Y (m * n) x := by
  funext k
  let p := finProdFinEquiv.symm k
  change Y (T^[p.2.val] ((T^[n])^[p.1.val] x)) = Y (T^[k.val] x)
  congr 1
  rw [← Function.iterate_mul]
  rw [← Function.iterate_add_apply]
  congr 2
  exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply k)

lemma observationEntropy_nested_observationBlock
    {M I : Type*} [MeasurableSpace M] [Fintype I]
    (mu : Measure M) (T : M → M) (Y : M → I) (m n : ℕ) :
    observationEntropy mu
        (observationBlock (T^[n]) (observationBlock T Y n) m) =
      partitionEntropy mu
        (iteratedJoin T (fiberPartition Y) (m * n)) := by
  calc
    observationEntropy mu
        (observationBlock (T^[n]) (observationBlock T Y n) m) =
        observationEntropy mu (fun x =>
          flattenObservationEquiv I m n
            (observationBlock (T^[n]) (observationBlock T Y n) m x)) :=
      (observationEntropy_equiv mu (flattenObservationEquiv I m n)
        (observationBlock (T^[n]) (observationBlock T Y n) m)).symm
    _ = observationEntropy mu (observationBlock T Y (m * n)) := by
      congr 1
      funext x
      exact flattenObservationEquiv_observationBlock T Y m n x
    _ = partitionEntropy mu
        (iteratedJoin T (fiberPartition Y) (m * n)) :=
      observationEntropy_observationBlock_fiberPartition mu T Y (m * n)

lemma tendsto_nat_mul_const_atTop
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun m : ℕ => m * n) atTop atTop := by
  refine tendsto_atTop.2 fun b => (eventually_ge_atTop b).mono ?_
  intro m hm
  exact hm.trans (Nat.le_mul_of_pos_right m hn)

lemma entropyW_iterate_fiberPartition_observationBlock
    {M I : Type*} [MeasurableSpace M]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (Y : M → I) (hY : Measurable Y)
    {n : ℕ} (hn : 0 < n) :
    entropyW mu (T^[n])
        (fiberPartition (observationBlock T Y n)) =
      n * entropyW mu T (fiberPartition Y) := by
  let P := fiberPartition Y
  let Q := fiberPartition (observationBlock T Y n)
  have hP : IsMeasurablePartition mu P :=
    isMeasurablePartition_fiberPartition mu Y hY
  have hblock : Measurable (observationBlock T Y n) :=
    measurable_observationBlock T hT.measurable Y hY n
  have hQ : IsMeasurablePartition mu Q :=
    isMeasurablePartition_fiberPartition mu _ hblock
  have hSlimit :=
    tendsto_partitionEntropy_iteratedJoin_div_entropyW
      mu (T^[n]) (T_inv^[n]) (hT_right.iterate n) (hT.iterate n) Q hQ
  have hSlimit' : Tendsto
      (fun m : ℕ =>
        partitionEntropy mu (iteratedJoin T P (m * n)) / m)
      atTop (nhds (entropyW mu (T^[n]) Q)) := by
    apply hSlimit.congr'
    exact Eventually.of_forall fun m => by
      apply congrArg (fun z : ℝ => z / m)
      calc
        partitionEntropy mu (iteratedJoin (T^[n]) Q m) =
            observationEntropy mu
              (observationBlock (T^[n]) (observationBlock T Y n) m) := by
          rw [observationEntropy_observationBlock_fiberPartition]
        _ = partitionEntropy mu (iteratedJoin T P (m * n)) := by
          exact observationEntropy_nested_observationBlock mu T Y m n
  have hTlimit :=
    tendsto_partitionEntropy_iteratedJoin_div_entropyW
      mu T T_inv hT_right hT P hP
  have hsub : Tendsto
      (fun m : ℕ =>
        partitionEntropy mu (iteratedJoin T P (m * n)) /
          ((m * n : ℕ) : ℝ))
      atTop (nhds (entropyW mu T P)) := by
    apply (hTlimit.comp (tendsto_nat_mul_const_atTop hn)).congr'
    exact Eventually.of_forall fun m => rfl
  have hscaled : Tendsto
      (fun m : ℕ =>
        n * (partitionEntropy mu (iteratedJoin T P (m * n)) /
          ((m * n : ℕ) : ℝ)))
      atTop (nhds (n * entropyW mu T P)) :=
    tendsto_const_nhds.mul hsub
  have hscaled' : Tendsto
      (fun m : ℕ =>
        partitionEntropy mu (iteratedJoin T P (m * n)) / m)
      atTop (nhds (n * entropyW mu T P)) := by
    apply hscaled.congr'
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Nat.cast_mul]
    field_simp [hm0, hn0]
  change entropyW mu (T^[n]) Q = n * entropyW mu T P
  exact tendsto_nhds_unique hSlimit' hscaled'

end Submission.Helpers
