import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis
open MeasureTheory Set
open scoped BoundedContinuousFunction

namespace Submission

theorem monge_kantorovich_exists {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : Measure X) (Q : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : X × Y → ENNReal) (hc : Continuous c) :
    ∃ π ∈ Couplings P Q,
      ∀ π' ∈ Couplings P Q, kantorovichCost c π ≤ kantorovichCost c π' := by
  let P₀ : ProbabilityMeasure X := ⟨P, by infer_instance⟩
  let Q₀ : ProbabilityMeasure Y := ⟨Q, by infer_instance⟩
  let S : Set (ProbabilityMeasure (X × Y)) :=
    {π |
      π.map measurable_fst.aemeasurable = P₀ ∧
        π.map measurable_snd.aemeasurable = Q₀}

  have hS_closed : IsClosed S := by
    simpa only [S, setOf_and] using
      (isClosed_eq
        (ProbabilityMeasure.continuous_map continuous_fst)
        continuous_const).inter
      (isClosed_eq
        (ProbabilityMeasure.continuous_map continuous_snd)
        continuous_const)

  have mem_couplings_of_mem_S (π : ProbabilityMeasure (X × Y)) (hπ : π ∈ S) :
      (π : Measure (X × Y)) ∈ Couplings P Q := by
    change
      π.map measurable_fst.aemeasurable = P₀ ∧
        π.map measurable_snd.aemeasurable = Q₀ at hπ
    change
      IsProbabilityMeasure (π : Measure (X × Y)) ∧
        (π : Measure (X × Y)).fst = P ∧
          (π : Measure (X × Y)).snd = Q
    refine ⟨inferInstance, ?_, ?_⟩
    · simpa [Measure.fst, P₀] using
        congrArg ProbabilityMeasure.toMeasure hπ.1
    · simpa [Measure.snd, Q₀] using
        congrArg ProbabilityMeasure.toMeasure hπ.2

  have mem_S_of_mem_couplings (π : Measure (X × Y)) (hπ : π ∈ Couplings P Q) :
      (⟨π, hπ.1⟩ : ProbabilityMeasure (X × Y)) ∈ S := by
    change
      IsProbabilityMeasure π ∧ π.fst = P ∧ π.snd = Q at hπ
    change
      ProbabilityMeasure.map
          (⟨π, hπ.1⟩ : ProbabilityMeasure (X × Y))
          measurable_fst.aemeasurable = P₀ ∧
        ProbabilityMeasure.map
          (⟨π, hπ.1⟩ : ProbabilityMeasure (X × Y))
          measurable_snd.aemeasurable = Q₀
    constructor
    · apply ProbabilityMeasure.toMeasure_injective
      simpa [Measure.fst, P₀] using hπ.2.1
    · apply ProbabilityMeasure.toMeasure_injective
      simpa [Measure.snd, Q₀] using hπ.2.2

  have hS_nonempty : S.Nonempty := ⟨P₀.prod Q₀, by simp [S]⟩

  letI : IsFiniteMeasure P := ⟨by simp⟩
  letI : IsFiniteMeasure Q := ⟨by simp⟩

  have hCouplings_tight : IsTightMeasureSet (Couplings P Q) := by
    apply IsTightMeasureSet.prodMk
    · apply (isTightMeasureSet_singleton (μ := P)).subset
      rintro μ ⟨π, hπ, rfl⟩
      exact hπ.2.1
    · apply (isTightMeasureSet_singleton (μ := Q)).subset
      rintro μ ⟨π, hπ, rfl⟩
      exact hπ.2.2

  have hS_tight :
      IsTightMeasureSet
        {((π : ProbabilityMeasure (X × Y)) : Measure (X × Y)) | π ∈ S} := by
    apply hCouplings_tight.subset
    rintro μ ⟨π, hπ, rfl⟩
    exact mem_couplings_of_mem_S π hπ

  have hS_compact : IsCompact S := by
    rw [← hS_closed.closure_eq]
    exact isCompact_closure_of_isTightMeasureSet hS_tight

  let g (n : ℕ) : (X × Y) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun p ↦ ENNReal.truncateToReal (n : ENNReal) (c p),
        (ENNReal.continuous_truncateToReal (ENNReal.natCast_ne_top n)).comp hc⟩
      (n : ℝ)
      (fun x y ↦ by
        change
          dist
              (ENNReal.truncateToReal (n : ENNReal) (c x))
              (ENNReal.truncateToReal (n : ENNReal) (c y)) ≤
            (n : ℝ)
        simpa only [sub_zero] using
          Real.dist_le_of_mem_Icc
            ⟨ENNReal.truncateToReal_nonneg,
              by
                simpa using
                  ENNReal.truncateToReal_le
                    (ENNReal.natCast_ne_top n) (x := c x)⟩
            ⟨ENNReal.truncateToReal_nonneg,
              by
                simpa using
                  ENNReal.truncateToReal_le
                    (ENNReal.natCast_ne_top n) (x := c y)⟩)
  let f (n : ℕ) : (X × Y) →ᵇ NNReal := (g n).nnrealPart

  have hf_apply (n : ℕ) (p : X × Y) :
      (f n p : ENNReal) = min (n : ENNReal) (c p) := by
    change
      ENNReal.ofReal (ENNReal.truncateToReal (n : ENNReal) (c p)) =
        min (n : ENNReal) (c p)
    rw [ENNReal.truncateToReal, ENNReal.ofReal_toReal]
    exact
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top n)
        (min_le_left (n : ENNReal) (c p))

  have hf_mono : Monotone (fun n p ↦ (f n p : ENNReal)) := by
    intro n m hnm p
    change (f n p : ENNReal) ≤ (f m p : ENNReal)
    rw [hf_apply, hf_apply]
    gcongr

  have hc_eq_iSup (p : X × Y) :
      c p = ⨆ n : ℕ, (f n p : ENNReal) := by
    simp_rw [hf_apply]
    rw [← iSup_inf_eq, ENNReal.iSup_natCast, top_inf_eq]

  let F : ProbabilityMeasure (X × Y) → ENNReal :=
    fun π ↦ ∫⁻ p, c p ∂(π : Measure (X × Y))

  have hF_eq_iSup (π : ProbabilityMeasure (X × Y)) :
      F π = ⨆ n : ℕ, ∫⁻ p, (f n p : ENNReal) ∂(π : Measure (X × Y)) := by
    dsimp only [F]
    calc
      (∫⁻ p, c p ∂(π : Measure (X × Y))) =
          ∫⁻ p, ⨆ n : ℕ, (f n p : ENNReal) ∂(π : Measure (X × Y)) :=
        lintegral_congr hc_eq_iSup
      _ = ⨆ n : ℕ, ∫⁻ p, (f n p : ENNReal) ∂(π : Measure (X × Y)) :=
        lintegral_iSup
          (fun n ↦ (ENNReal.continuous_coe.comp (f n).continuous).measurable)
          hf_mono

  have hF_lsc : LowerSemicontinuous F := by
    rw [show
      F =
        fun π : ProbabilityMeasure (X × Y) ↦
          ⨆ n : ℕ, ∫⁻ p, (f n p : ENNReal) ∂(π : Measure (X × Y))
      by
        funext π
        exact hF_eq_iSup π]
    exact lowerSemicontinuous_iSup fun n ↦
      (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
        (f n)).lowerSemicontinuous

  obtain ⟨π, hπ, hπ_min⟩ :=
    (hF_lsc.lowerSemicontinuousOn S).exists_isMinOn hS_nonempty hS_compact
  refine ⟨(π : Measure (X × Y)), mem_couplings_of_mem_S π hπ, ?_⟩
  intro π' hπ'
  have hπ_le :
      F π ≤ F (⟨π', hπ'.1⟩ : ProbabilityMeasure (X × Y)) :=
    hπ_min (mem_S_of_mem_couplings π' hπ')
  simpa only [kantorovichCost, F, ProbabilityMeasure.coe_mk] using hπ_le

end Submission
