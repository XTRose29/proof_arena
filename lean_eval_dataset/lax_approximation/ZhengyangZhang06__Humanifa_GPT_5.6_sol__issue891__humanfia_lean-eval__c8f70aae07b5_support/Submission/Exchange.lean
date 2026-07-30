import Submission.Helpers

open LeanEval.Dynamics.LaxApproximation
open MeasureTheory Set Function
open scoped ENNReal BigOperators

namespace Submission.Helpers

/-- The piecewise-rigid cube exchange associated to a permutation of grid indices. -/
noncomputable def cubeExchangeMap (n : ℕ) (hn : 0 < n) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) (x : Torus d) : Torus d :=
  let k := gridIndex n hn x
  gridTranslate n k (σ k) x

lemma cubeExchangeMap_mem_cube (n : ℕ) (hn : 0 < n) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) (x : Torus d) :
    cubeExchangeMap n hn σ x ∈ cube n (σ (gridIndex n hn x)) := by
  exact gridTranslate_mem_cube (n := n) (k := gridIndex n hn x)
    (l := σ (gridIndex n hn x)) (mem_cube_gridIndex n hn x)

lemma gridIndex_cubeExchangeMap (n : ℕ) (hn : 0 < n) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) (x : Torus d) :
    gridIndex n hn (cubeExchangeMap n hn σ x) = σ (gridIndex n hn x) :=
  gridIndex_eq_of_mem_cube n hn (cubeExchangeMap_mem_cube n hn σ x)

lemma cubeExchangeMap_symm_apply (n : ℕ) (hn : 0 < n) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) (x : Torus d) :
    cubeExchangeMap n hn σ.symm (cubeExchangeMap n hn σ x) = x := by
  change gridTranslate n (gridIndex n hn (cubeExchangeMap n hn σ x))
    (σ.symm (gridIndex n hn (cubeExchangeMap n hn σ x)))
    (cubeExchangeMap n hn σ x) = x
  rw [gridIndex_cubeExchangeMap, σ.symm_apply_apply]
  exact gridTranslate_reverse n (gridIndex n hn x) (σ (gridIndex n hn x)) x

lemma measurable_cubeExchangeMap (n : ℕ) (hn : 0 < n) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) : Measurable (cubeExchangeMap n hn σ) := by
  apply measurable_pi_lambda
  intro i
  have hshift : Measurable (fun k : Fin d → Fin n =>
      (realGridShift n k (σ k) i : AddCircle (1 : ℝ))) := measurable_of_finite _
  exact (measurable_pi_apply i).add (hshift.comp (measurable_gridIndex n hn))

/-- The measurable equivalence underlying a grid permutation. -/
noncomputable def cubeExchangeMeasurableEquiv (n : ℕ) (hn : 0 < n) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) : Torus d ≃ᵐ Torus d where
  toFun := cubeExchangeMap n hn σ
  invFun := cubeExchangeMap n hn σ.symm
  left_inv := cubeExchangeMap_symm_apply n hn σ
  right_inv := by
    intro x
    simpa using cubeExchangeMap_symm_apply n hn σ.symm x
  measurable_toFun := measurable_cubeExchangeMap n hn σ
  measurable_invFun := measurable_cubeExchangeMap n hn σ.symm

lemma measure_cubeExchangeMap_preimage (n : ℕ) (hn : 0 < n) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) {A : Set (Torus d)} (hA : MeasurableSet A) :
    volume (cubeExchangeMap n hn σ ⁻¹' A) = volume A := by
  let f := cubeExchangeMap n hn σ
  have hpre : f ⁻¹' A = ⋃ k : Fin d → Fin n,
      cube n k ∩ gridTranslate n k (σ k) ⁻¹' A := by
    ext x
    constructor
    · intro hx
      let k := gridIndex n hn x
      refine mem_iUnion.2 ⟨k, mem_inter (mem_cube_gridIndex n hn x) ?_⟩
      exact hx
    · rw [mem_iUnion]
      rintro ⟨k, hxk, hxA⟩
      change f x ∈ A
      have hk : gridIndex n hn x = k := gridIndex_eq_of_mem_cube n hn hxk
      change gridTranslate n k (σ k) x ∈ A at hxA
      simpa only [f, cubeExchangeMap, hk] using hxA
  rw [hpre, measure_iUnion]
  · have hterm : ∀ k : Fin d → Fin n,
        volume (cube n k ∩ gridTranslate n k (σ k) ⁻¹' A) =
          volume (cube n (σ k) ∩ A) := by
      intro k
      have hset : cube n k ∩ gridTranslate n k (σ k) ⁻¹' A =
          gridTranslate n k (σ k) ⁻¹' (cube n (σ k) ∩ A) := by
        ext x
        simp only [mem_inter_iff, mem_preimage]
        rw [gridTranslate_mem_cube_iff]
      rw [hset]
      exact measure_preimage_add_right (volume : Measure (Torus d))
        (fun i => (realGridShift n k (σ k) i : AddCircle (1 : ℝ)))
        (cube n (σ k) ∩ A)
    simp_rw [hterm]
    have hreindex :
        (∑' k : Fin d → Fin n, volume (cube n (σ k) ∩ A)) =
          ∑' k : Fin d → Fin n, volume (cube n k ∩ A) := by
      simp only [tsum_fintype]
      exact Equiv.sum_comp σ (fun k : Fin d → Fin n => volume (cube n k ∩ A))
    rw [hreindex]
    have hApartition : (⋃ k : Fin d → Fin n, cube n k ∩ A) = A := by
      rw [← iUnion_inter, iUnion_cube n hn, univ_inter]
    rw [← measure_iUnion]
    · exact congrArg (fun s : Set (Torus d) => volume s) hApartition
    · intro k l hkl
      exact (pairwise_disjoint_cube n hn hkl).mono inter_subset_left inter_subset_left
    · intro k
      exact (measurableSet_cube n hn k).inter hA
  · intro k l hkl
    exact (pairwise_disjoint_cube n hn hkl).mono inter_subset_left inter_subset_left
  · intro k
    have htrans : Measurable (gridTranslate n k (σ k)) := by
      apply measurable_pi_lambda
      intro i
      exact (measurable_pi_apply i).add measurable_const
    exact (measurableSet_cube n hn k).inter (hA.preimage htrans)

lemma cubeExchangeMap_measurePreserving (n : ℕ) (hn : 0 < n) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) :
    MeasurePreserving (cubeExchangeMap n hn σ) (volume : Measure (Torus d)) volume := by
  refine ⟨measurable_cubeExchangeMap n hn σ, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_cubeExchangeMap n hn σ) hA]
  exact measure_cubeExchangeMap_preimage n hn σ hA

/-- A grid permutation, realized as a volume-preserving measurable equivalence. -/
noncomputable def cubeExchange (n : ℕ) (hn : 0 < n) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) : VolumePreservingEquiv d where
  toMeasurableEquiv := cubeExchangeMeasurableEquiv n hn σ
  measurePreserving := cubeExchangeMap_measurePreserving n hn σ

lemma cubeExchange_apply_of_mem_cube (n : ℕ) (hn : 0 < n) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n)) (k : Fin d → Fin n) (x : Torus d)
    (hx : x ∈ cube n k) (i : Fin d) :
    (cubeExchange n hn σ).toMeasurableEquiv x i = x i + cubeShift n σ k i := by
  have hk : gridIndex n hn x = k := gridIndex_eq_of_mem_cube n hn hx
  change cubeExchangeMap n hn σ x i = x i + cubeShift n σ k i
  simp only [cubeExchangeMap, hk, gridTranslate, realGridShift, cubeShift]
  congr 2
  push_cast
  norm_cast

end Submission.Helpers
