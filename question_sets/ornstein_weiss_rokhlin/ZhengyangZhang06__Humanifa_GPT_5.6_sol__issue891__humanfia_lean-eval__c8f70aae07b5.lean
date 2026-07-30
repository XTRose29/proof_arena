import ChallengeDeps
import Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory Set

namespace Submission

theorem ornstein_weiss_rokhlin {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    {d : ℕ} (_hd : 1 ≤ d) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : (Fin d → ℤ) → Ω → Ω)
    (_hid : ∀ x, T 0 x = x)
    (_hT : ∀ v, MeasurePreserving (T v) μ μ)
    (_hgrp : ∀ u v x, T (u + v) x = T u (T v x))
    (_hfree : IsFreeAction μ T)
    (N : ℕ) (_hN : 1 ≤ N) {ε : ENNReal} (_hε : 0 < ε) :
    ∃ B : Set Ω,
      MeasurableSet B ∧
      ((boxShape d N : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)).PairwiseDisjoint
        (fun v => T v '' B) ∧
      μ (⋃ v ∈ boxShape d N, T v '' B) ≥ 1 - ε := by
  by_cases hεone : 1 ≤ ε
  · refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
    · simp [Set.PairwiseDisjoint, Set.Pairwise]
    · simp [tsub_eq_zero_of_le hεone]
  have hεlt : ε < 1 := lt_of_not_ge hεone
  have he : 0 < ε.toReal :=
    ENNReal.toReal_pos _hε.ne' (ne_top_of_lt hεlt)
  obtain ⟨k, M, _hk, hM, hlarge⟩ :=
    Helpers.exists_large_packedUnion μ T _hid _hT _hgrp _hfree _hd N _hN he
  let B := Helpers.retiledBase μ T _hfree k M N
  refine ⟨B, Helpers.measurableSet_retiledBase μ T _hid _hT _hgrp _hfree k M N,
    Helpers.pairwiseDisjoint_retiledBase μ T _hid _hgrp _hfree k M N _hN, ?_⟩
  change 1 - ε ≤ μ (Helpers.tower T (boxShape d N) B)
  rw [Helpers.tower_retiledBase_eq μ T _hgrp _hfree k M N _hN]
  apply (ENNReal.toReal_le_toReal
    (ENNReal.sub_ne_top ENNReal.one_ne_top) (measure_ne_top μ _)).mp
  rw [ENNReal.toReal_sub_of_le hεlt.le ENNReal.one_ne_top]
  simpa [Measure.real] using hlarge

end Submission
