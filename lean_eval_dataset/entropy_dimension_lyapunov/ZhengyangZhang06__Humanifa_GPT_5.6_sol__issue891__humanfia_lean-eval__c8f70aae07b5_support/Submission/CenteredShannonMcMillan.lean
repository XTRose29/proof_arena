import Submission.ShannonMcMillan
import Submission.HyperbolicBalance

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

lemma partitionInformation_preimagePartition
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (F : M → M) (hF : MeasurePreserving F mu mu)
    (hF_surj : Function.Surjective F)
    (P : Finset (Set M)) (hP : ∀ A ∈ P, MeasurableSet A) (x : M) :
    partitionInformation mu (preimagePartition F P) x =
      partitionInformation mu P (F x) := by
  classical
  unfold partitionInformation preimagePartition
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro A hAP
    have hmu : mu.real (F ⁻¹' A) = mu.real A := by
      change (mu (F ⁻¹' A)).toReal = (mu A).toReal
      rw [hF.measure_preimage (hP A hAP).nullMeasurableSet]
    rw [hmu]
    by_cases hx : F x ∈ A <;> simp [Set.indicator, hx]
  · exact hF_surj.preimage_injective.injOn

lemma partitionInformation_centeredJoin
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) (T T_inv : M → M)
    (hT_left : Function.LeftInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set M)) (hP : IsMeasurablePartition mu P)
    (m n : ℕ) (x : M) :
    partitionInformation mu (centeredJoin T T_inv P m n) x =
      partitionInformation mu (iteratedJoin T P (m + n)) (T_inv^[m] x) := by
  unfold centeredJoin
  exact partitionInformation_preimagePartition mu (T_inv^[m])
    (hT_inv.iterate m) (hT_left.iterate m).surjective
      (iteratedJoin T P (m + n))
      (isMeasurablePartition_iteratedJoin mu T hT P hP (m + n)).measurable x

lemma birkhoffSum_centered_eq_backward_add_forward
    {M E : Type*} [AddCommMonoid E]
    (T T_inv : M → M)
    (hT_right : Function.RightInverse T_inv T)
    (f : M → E) (m n : ℕ) (x : M) :
    birkhoffSum T f (m + n) (T_inv^[m] x) =
      birkhoffSum T_inv f m (T_inv x) + birkhoffSum T f n x := by
  rw [birkhoffSum_add]
  rw [(hT_right.iterate m) x]
  congr 1
  rw [birkhoffSum, birkhoffSum]
  calc
    (∑ j ∈ Finset.range m, f (T^[j] (T_inv^[m] x))) =
        ∑ j ∈ Finset.range m, f (T_inv^[m - j] x) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [iterate_before_inverse_cancel hT_right (Finset.mem_range.mp hj).le]
    _ = ∑ j ∈ Finset.range m, f (T_inv^[j + 1] x) := by
      rw [← Finset.sum_range_reflect (fun j => f (T_inv^[j + 1] x)) m]
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      have hjlt := Finset.mem_range.mp hj
      omega
    _ = ∑ j ∈ Finset.range m, f (T_inv^[j] (T_inv x)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← Function.iterate_succ_apply]

end Submission.Helpers
