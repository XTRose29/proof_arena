import Submission.RiemannReachable

open Function Metric Set

namespace Submission

noncomputable def NormalizedDiskEmbedding.OmittedPointStep.inverseMap
    {U : Set ℂ} {x : ℂ} {E F : NormalizedDiskEmbedding U x}
    (step : E.OmittedPointStep F) (w : ℂ) : ℂ :=
  diskMobiusInv step.a ((diskMobiusInv step.b w) ^ 2)

lemma diskMobiusInv_differentiableAt {a w : ℂ}
    (ha : a ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    DifferentiableAt ℂ (diskMobiusInv a) w := by
  have hneg : -a ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff] using ha
  have heq : diskMobiusInv a = diskMobius (-a) := by
    funext z
    simp [diskMobiusInv, diskMobius]
  rw [heq]
  exact (hasDerivAt_diskMobius hneg hw).differentiableAt

lemma NormalizedDiskEmbedding.OmittedPointStep.inverseMap_mapsTo_unitBall
    {U : Set ℂ} {x : ℂ} {E F : NormalizedDiskEmbedding U x}
    (step : E.OmittedPointStep F) :
    MapsTo step.inverseMap (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro w hw
  have hb := diskMobiusInv_mapsTo_unitBall step.b_mem hw
  have hsq : diskMobiusInv step.b w ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]
    have hb' : ‖diskMobiusInv step.b w‖ < 1 := by
      simpa [mem_ball_zero_iff] using hb
    nlinarith [norm_nonneg (diskMobiusInv step.b w)]
  exact diskMobiusInv_mapsTo_unitBall step.a_mem hsq

lemma NormalizedDiskEmbedding.OmittedPointStep.inverseMap_differentiableOn
    {U : Set ℂ} {x : ℂ} {E F : NormalizedDiskEmbedding U x}
    (step : E.OmittedPointStep F) :
    DifferentiableOn ℂ step.inverseMap (ball (0 : ℂ) 1) := by
  intro w hw
  have hb := diskMobiusInv_mapsTo_unitBall step.b_mem hw
  have hsq : diskMobiusInv step.b w ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_pow]
    have hb' : ‖diskMobiusInv step.b w‖ < 1 := by
      simpa [mem_ball_zero_iff] using hb
    nlinarith [norm_nonneg (diskMobiusInv step.b w)]
  have hinner : DifferentiableAt ℂ
      (fun z ↦ diskMobiusInv step.b z ^ 2) w :=
    (diskMobiusInv_differentiableAt step.b_mem hw).pow 2
  exact ((diskMobiusInv_differentiableAt step.a_mem hsq).comp w hinner)
    |>.differentiableWithinAt

lemma NormalizedDiskEmbedding.OmittedPointStep.q_mem_unitBall
    {U : Set ℂ} {x : ℂ} {E F : NormalizedDiskEmbedding U x}
    (step : E.OmittedPointStep F) {z : ℂ} (hz : z ∈ U) :
    step.q z ∈ ball (0 : ℂ) 1 := by
  have hsqMem : step.q z ^ 2 ∈ ball (0 : ℂ) 1 := by
    rw [step.q_sq]
    exact diskMobius_mapsTo_unitBall step.a_mem (E.mapsTo hz)
  rw [mem_ball_zero_iff] at hsqMem ⊢
  rw [norm_pow] at hsqMem
  nlinarith [norm_nonneg (step.q z)]

lemma NormalizedDiskEmbedding.OmittedPointStep.inverseMap_apply
    {U : Set ℂ} {x : ℂ} {E F : NormalizedDiskEmbedding U x}
    (step : E.OmittedPointStep F) {z : ℂ} (hz : z ∈ U) :
    step.inverseMap (F z) = E z := by
  have hq := step.q_mem_unitBall hz
  rw [step.toFun_eq]
  rw [inverseMap, diskMobiusInv_diskMobius step.b_mem hq,
    step.q_sq, diskMobiusInv_diskMobius step.a_mem (E.mapsTo hz)]

lemma NormalizedDiskEmbedding.OmittedPointStep.inverseMap_zero
    {U : Set ℂ} {x : ℂ} {E F : NormalizedDiskEmbedding U x}
    (step : E.OmittedPointStep F) : step.inverseMap 0 = 0 := by
  rw [inverseMap, diskMobiusInv_zero, step.b_sq]
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hmobius : diskMobius step.a 0 = -step.a := by
    simp [diskMobius]
  rw [← hmobius, diskMobiusInv_diskMobius step.a_mem hzero]

noncomputable def NormalizedDiskEmbedding.ReachableFrom.inverseMap
    {U : Set ℂ} {x : ℂ} {E₀ E : NormalizedDiskEmbedding U x}
    (reach : E₀.ReachableFrom E) : ℂ → ℂ := by
  induction reach with
  | refl => exact id
  | step previous step previousInverse =>
      exact previousInverse ∘ step.inverseMap

lemma NormalizedDiskEmbedding.ReachableFrom.inverseMap_apply
    {U : Set ℂ} {x : ℂ} {E₀ E : NormalizedDiskEmbedding U x}
    (reach : E₀.ReachableFrom E) {z : ℂ} (hz : z ∈ U) :
    reach.inverseMap (E z) = E₀ z := by
  induction reach with
  | refl => simp [inverseMap]
  | step previous step ih =>
      change previous.inverseMap (step.inverseMap _) = E₀ z
      rw [step.inverseMap_apply hz]
      exact ih

lemma NormalizedDiskEmbedding.ReachableFrom.inverseMap_zero
    {U : Set ℂ} {x : ℂ} {E₀ E : NormalizedDiskEmbedding U x}
    (reach : E₀.ReachableFrom E) : reach.inverseMap 0 = 0 := by
  induction reach with
  | refl => simp [inverseMap]
  | step previous step ih =>
      change previous.inverseMap (step.inverseMap 0) = 0
      rw [step.inverseMap_zero]
      exact ih

lemma NormalizedDiskEmbedding.ReachableFrom.inverseMap_mapsTo_unitBall
    {U : Set ℂ} {x : ℂ} {E₀ E : NormalizedDiskEmbedding U x}
    (reach : E₀.ReachableFrom E) :
    MapsTo reach.inverseMap (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  induction reach with
  | refl => simpa [inverseMap] using (mapsTo_id (ball (0 : ℂ) 1))
  | step previous step ih =>
      exact ih.comp step.inverseMap_mapsTo_unitBall

lemma NormalizedDiskEmbedding.ReachableFrom.inverseMap_differentiableOn
    {U : Set ℂ} {x : ℂ} {E₀ E : NormalizedDiskEmbedding U x}
    (reach : E₀.ReachableFrom E) :
    DifferentiableOn ℂ reach.inverseMap (ball (0 : ℂ) 1) := by
  induction reach with
  | refl => simpa [inverseMap] using differentiableOn_id
  | step previous step ih =>
      change DifferentiableOn ℂ (previous.inverseMap ∘ step.inverseMap) (ball 0 1)
      exact ih.comp step.inverseMap_differentiableOn
        step.inverseMap_mapsTo_unitBall

end Submission
