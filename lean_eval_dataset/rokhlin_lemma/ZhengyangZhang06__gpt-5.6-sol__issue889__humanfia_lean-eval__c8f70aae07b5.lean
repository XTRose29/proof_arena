import ChallengeDeps
import Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory Set

namespace Submission

theorem rokhlin_lemma {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (_hT : MeasurePreserving T μ μ) (_hap : IsAperiodic T μ)
    (n : ℕ) (_hn : 1 ≤ n) {ε : ENNReal} (_hε : 0 < ε) :
    ∃ B : Set Ω, IsRokhlinTower T B n ∧
      μ (towerUnion T B n) ≥ 1 - ε := by
  have hn : 0 < n := _hn
  let c : ENNReal := (n : ENNReal) * (n : ENNReal)
  have hc0 : c ≠ 0 := by
    simp [c, Nat.ne_of_gt hn]
  have hctop : c ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top n) (ENNReal.natCast_ne_top n)
  have hδ : 0 < ε / c := ENNReal.div_pos _hε.ne' hctop
  obtain ⟨A, hA, hμA, hsweep⟩ :=
    Submission.Helpers.exists_small_sweep _hT _hap hδ
  let B := Submission.Helpers.phase T A n (n - 1)
  refine ⟨B, Submission.Helpers.phaseTower_isRokhlin
    _hT.measurable hA hn, ?_⟩
  have hcount :=
    Submission.Helpers.one_le_nsmul_phase_last_add_error
      _hT hA hn hsweep
  have hscaled : c * μ A < ε := by
    calc
      c * μ A < c * (ε / c) :=
        ENNReal.mul_lt_mul_right hc0 hctop hμA
      _ = ε := ENNReal.mul_div_cancel hc0 hctop
  have herr : n • (n • μ A) < ε := by
    simpa only [nsmul_eq_mul, c, mul_assoc] using hscaled
  have hbase : 1 - ε ≤ n • μ B := by
    rw [tsub_le_iff_right]
    exact hcount.trans (add_le_add le_rfl herr.le)
  exact hbase.trans
    (Submission.Helpers.phaseTower_measure_ge _hT hA hn)

end Submission
