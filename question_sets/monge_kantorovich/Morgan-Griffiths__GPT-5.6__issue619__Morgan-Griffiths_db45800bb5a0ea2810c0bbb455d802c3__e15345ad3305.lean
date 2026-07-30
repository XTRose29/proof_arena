import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis
open MeasureTheory Set

namespace Submission

/-ResultProofDefinitionsBegin-/

open scoped ENNReal NNReal Topology BoundedContinuousFunction
open Filter Topology

-- truncations of a continuous ENNReal function as bounded NNReal functions
noncomputable def mkTruncBCF {Ω : Type*} [TopologicalSpace Ω]
    (f : Ω → ENNReal) (hf : Continuous f) (n : ℕ) : Ω →ᵇ ℝ≥0 where
  toFun := fun x => (min (f x) (n : ENNReal)).toNNReal
  continuous_toFun := by
    apply ContinuousOn.comp_continuous ENNReal.continuousOn_toNNReal (hf.min continuous_const)
    intro x
    exact (lt_of_le_of_lt (min_le_right _ _) (by exact_mod_cast (ENNReal.coe_lt_top : (n : ENNReal) < ∞))).ne
  map_bounded' := by
    refine ⟨(n : ℝ) + n + 1, ?_⟩
    intro x y
    rw [NNReal.dist_eq]
    have hx : ((min (f x) (n : ENNReal)).toNNReal : ℝ) ≤ n := by
      exact_mod_cast (ENNReal.coe_le_coe.1 (by simpa using (min_le_right (f x) (n : ENNReal))))
    have hy : ((min (f y) (n : ENNReal)).toNNReal : ℝ) ≤ n := by
      exact_mod_cast (ENNReal.coe_le_coe.1 (by simpa using (min_le_right (f y) (n : ENNReal))))
    have hx0 : 0 ≤ ((min (f x) (n : ENNReal)).toNNReal : ℝ) := NNReal.zero_le_coe
    have hy0 : 0 ≤ ((min (f y) (n : ENNReal)).toNNReal : ℝ) := NNReal.zero_le_coe
    rw [abs_sub_le_iff]
    constructor <;> linarith

lemma lsc_lintegral_continuous {Ω : Type*} [TopologicalSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    (f : Ω → ENNReal) (hf : Continuous f) :
    LowerSemicontinuous
      (fun μ : ProbabilityMeasure Ω => ∫⁻ x, f x ∂(μ : Measure Ω)) := by
  classical
  have hval (n : ℕ) (x : Ω) :
      ((mkTruncBCF f hf n x : ℝ≥0) : ENNReal) = min (f x) (n : ENNReal) := by
    change ((min (f x) (n : ENNReal)).toNNReal : ENNReal) = _
    apply ENNReal.coe_toNNReal
    exact (lt_of_le_of_lt (min_le_right _ _) (by exact_mod_cast (ENNReal.coe_lt_top : (n : ENNReal) < ∞))).ne
  have hpt (x : Ω) : (⨆ n : ℕ, ((mkTruncBCF f hf n x : ℝ≥0) : ENNReal)) = f x := by
    simp_rw [hval]
    -- supremum of truncations
    calc
      (⨆ n : ℕ, min (f x) (n : ENNReal)) =
          (⨆ n : ℕ, (n : ENNReal) ⊓ f x) := by
            congr 1; funext n; exact inf_comm _ _
      _ = ( (⨆ n : ℕ, (n : ENNReal)) ⊓ f x) := (iSup_inf_eq _ _).symm
      _ = f x := by simp [ENNReal.iSup_natCast]
  have heq (μ : ProbabilityMeasure Ω) :
      (∫⁻ x, f x ∂(μ : Measure Ω)) =
        ⨆ n : ℕ, (∫⁻ x, ((mkTruncBCF f hf n x : ℝ≥0) : ENNReal) ∂(μ : Measure Ω)) := by
    let g : ℕ → Ω → ENNReal := fun n x => ((mkTruncBCF f hf n x : ℝ≥0) : ENNReal)
    have hg (n : ℕ) : Measurable (g n) :=
      (ENNReal.continuous_coe.comp (mkTruncBCF f hf n).continuous).measurable
    have hmono : Monotone g := by
      intro a b hab x
      change ((mkTruncBCF f hf a x : ℝ≥0) : ENNReal) ≤
        ((mkTruncBCF f hf b x : ℝ≥0) : ENNReal)
      rw [hval, hval]
      exact min_le_min_left _ (by exact_mod_cast hab)
    calc
      (∫⁻ x, f x ∂(μ : Measure Ω)) =
          ∫⁻ x, ⨆ n : ℕ, g n x ∂(μ : Measure Ω) := by
            have hh : f = (fun x => ⨆ n : ℕ, g n x) := by
              funext x
              exact (hpt x).symm
            rw [hh]
      _ = ⨆ n : ℕ, (∫⁻ x, g n x ∂(μ : Measure Ω)) :=
          lintegral_iSup hg hmono

  -- supremum of continuous bounded integrals is l.s.c.
  have H := lowerSemicontinuous_iSup (δ := ENNReal)
    (α := ProbabilityMeasure Ω)
    (f := fun n (μ : ProbabilityMeasure Ω) =>
      ∫⁻ x, ((mkTruncBCF f hf n x : ℝ≥0) : ENNReal) ∂(μ : Measure Ω))
    (fun n => (ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
      (mkTruncBCF f hf n)).lowerSemicontinuous)
  have fun_eq :
      (fun μ : ProbabilityMeasure Ω => ∫⁻ x, f x ∂(μ : Measure Ω)) =
      (fun μ : ProbabilityMeasure Ω =>
        ⨆ n : ℕ, ∫⁻ x, ((mkTruncBCF f hf n x : ℝ≥0) : ENNReal) ∂(μ : Measure Ω)) :=
    funext heq
  exact fun_eq ▸ H


-- The same closed marginal constraints in the space of probability measures.
def pmCouplings {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (p : ProbabilityMeasure X) (q : ProbabilityMeasure Y) :
    Set (ProbabilityMeasure (X × Y)) :=
  {ν | ProbabilityMeasure.map ν continuous_fst.measurable.aemeasurable = p ∧
       ProbabilityMeasure.map ν continuous_snd.measurable.aemeasurable = q}

lemma isClosed_pmCouplings {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [T2Space X] [T2Space Y]
    (p : ProbabilityMeasure X) (q : ProbabilityMeasure Y) :
    IsClosed (pmCouplings p q) := by
  change IsClosed ({ν : ProbabilityMeasure (X × Y) |
    ProbabilityMeasure.map ν continuous_fst.measurable.aemeasurable = p ∧
    ProbabilityMeasure.map ν continuous_snd.measurable.aemeasurable = q})
  apply IsClosed.inter
  · exact isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const
  · exact isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const

lemma nonempty_pmCouplings {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (p : ProbabilityMeasure X) (q : ProbabilityMeasure Y) :
    (pmCouplings p q).Nonempty := by
  let ν : ProbabilityMeasure (X × Y) :=
    ⟨(p : Measure X).prod (q : Measure Y), by infer_instance⟩
  refine ⟨ν, ?_⟩
  change (ProbabilityMeasure.map ν continuous_fst.measurable.aemeasurable = p) ∧
    (ProbabilityMeasure.map ν continuous_snd.measurable.aemeasurable = q)
  constructor
  · apply ProbabilityMeasure.toMeasure_injective
    change ((p : Measure X).prod (q : Measure Y)).fst = (p : Measure X)
    exact Measure.fst_prod
  · apply ProbabilityMeasure.toMeasure_injective
    change ((p : Measure X).prod (q : Measure Y)).snd = (q : Measure Y)
    exact Measure.snd_prod

lemma tight_pmCouplings {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (p : ProbabilityMeasure X) (q : ProbabilityMeasure Y) :
    IsTightMeasureSet
      {((ν : ProbabilityMeasure (X × Y)) : Measure (X × Y)) |
         ν ∈ pmCouplings p q} := by
  -- Tight compact pieces for the two fixed marginals.
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hp := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le).1
    (isTightMeasureSet_singleton (μ := (p : Measure X)))
  have hq := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le).1
    (isTightMeasureSet_singleton (μ := (q : Measure Y)))
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  rcases hp (ε/2) hhalf with ⟨A, hA, hpa⟩
  rcases hq (ε/2) hhalf with ⟨B, hB, hqb⟩
  refine ⟨A ×ˢ B, hA.prod hB, ?_⟩
  intro μ hμ
  rcases hμ with ⟨ν, hνS, rfl⟩
  -- on this rectangle the mass is controlled by its marginals
  have hν1 : (ν : Measure (X × Y)).fst = (p : Measure X) := by
    have h := congrArg ProbabilityMeasure.toMeasure hνS.1
    exact h
  have hν2 : (ν : Measure (X × Y)).snd = (q : Measure Y) := by
    have h := congrArg ProbabilityMeasure.toMeasure hνS.2
    exact h
  have hAmeas : MeasurableSet A := hA.isClosed.measurableSet
  have hBmeas : MeasurableSet B := hB.isClosed.measurableSet
  have h1 : (ν : Measure (X × Y)) (Prod.fst ⁻¹' (Aᶜ)) ≤ ε/2 := by
    rw [← Measure.fst_apply hAmeas.compl, hν1]
    exact hpa _ (by simp)
  have h2 : (ν : Measure (X × Y)) (Prod.snd ⁻¹' (Bᶜ)) ≤ ε/2 := by
    rw [← Measure.snd_apply hBmeas.compl, hν2]
    exact hqb _ (by simp)
  calc
    (ν : Measure (X × Y)) ((A ×ˢ B)ᶜ)
        ≤ (ν : Measure (X × Y)) ((Prod.fst ⁻¹' (Aᶜ)) ∪ (Prod.snd ⁻¹' (Bᶜ))) := by
            apply measure_mono
            intro z hz
            rcases z with ⟨x,y⟩
            by_cases hx : x ∈ A
            · have hy : y ∉ B := by
                intro hy
                exact hz ⟨hx, hy⟩
              exact Or.inr hy
            · exact Or.inl hx
    _ ≤ (ν : Measure (X × Y)) (Prod.fst ⁻¹' (Aᶜ)) +
          (ν : Measure (X × Y)) (Prod.snd ⁻¹' (Bᶜ)) := measure_union_le _ _
    _ ≤ ε/2 + ε/2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε

lemma compact_pmCouplings {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (p : ProbabilityMeasure X) (q : ProbabilityMeasure Y) :
    IsCompact (pmCouplings p q) := by
  have h := isCompact_closure_of_isTightMeasureSet (tight_pmCouplings p q)
  rw [(closure_eq_iff_isClosed).2 (isClosed_pmCouplings p q)] at h
  exact h

/-ResultProofDefinitionsEnd-/


theorem monge_kantorovich_exists {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : Measure X) (Q : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : X × Y → ENNReal) (_hc : Continuous c) :
    ∃ π ∈ Couplings P Q,
      ∀ π' ∈ Couplings P Q, kantorovichCost c π ≤ kantorovichCost c π' := by
  let p : ProbabilityMeasure X := ⟨P, inferInstance⟩
  let q : ProbabilityMeasure Y := ⟨Q, inferInstance⟩
  let S : Set (ProbabilityMeasure (X × Y)) := pmCouplings p q
  let F : ProbabilityMeasure (X × Y) → ENNReal :=
    fun ν => ∫⁻ z, c z ∂(ν : Measure (X × Y))
  have hne : S.Nonempty := nonempty_pmCouplings p q
  have hcomp : IsCompact S := compact_pmCouplings p q
  have hlsc : LowerSemicontinuous F := lsc_lintegral_continuous c _hc
  obtain ⟨ν, hνS, hνmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hne hcomp
      (hlsc.lowerSemicontinuousOn S)
  refine ⟨(ν : Measure (X × Y)), ?_, ?_⟩
  · change IsProbabilityMeasure (ν : Measure (X × Y)) ∧
        (ν : Measure (X × Y)).fst = P ∧ (ν : Measure (X × Y)).snd = Q
    refine ⟨inferInstance, ?_, ?_⟩
    · have h := (show ν ∈ pmCouplings p q from hνS)
      have hm := congrArg ProbabilityMeasure.toMeasure h.1
      exact hm
    · have h := (show ν ∈ pmCouplings p q from hνS)
      have hm := congrArg ProbabilityMeasure.toMeasure h.2
      exact hm
  · intro π' hπ'
    let ν' : ProbabilityMeasure (X × Y) := ⟨π', hπ'.1⟩
    have hν'S : ν' ∈ S := by
      change ProbabilityMeasure.map ν' continuous_fst.measurable.aemeasurable = p ∧
        ProbabilityMeasure.map ν' continuous_snd.measurable.aemeasurable = q
      constructor
      · apply ProbabilityMeasure.toMeasure_injective
        exact hπ'.2.1
      · apply ProbabilityMeasure.toMeasure_injective
        exact hπ'.2.2
    have hle : F ν ≤ F ν' := hνmin hν'S
    exact hle


end Submission
