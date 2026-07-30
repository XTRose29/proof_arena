import Mathlib

open MeasureTheory Set

noncomputable section

namespace Submission.Helpers

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Scalar characterization of a probability measure on `K` having barycenter `z`. -/
def Represents (K : Set X) (z : K) (μ : ProbabilityMeasure K) : Prop :=
  ∀ L : X →L[ℝ] ℝ, ∫ y, L y.1 ∂(μ : Measure K) = L z.1

omit [CompleteSpace X] in
lemma continuous_integral_dual (K : Set X) [CompactSpace K] (L : X →L[ℝ] ℝ) :
    Continuous fun μ : ProbabilityMeasure K => ∫ y, L y.1 ∂(μ : Measure K) := by
  exact ProbabilityMeasure.continuous_integral_continuousMap
    (⟨fun y : K => L y.1, L.continuous.comp continuous_subtype_val⟩ : C(K, ℝ))

omit [CompleteSpace X] in
lemma isClosed_represents (K : Set X) [CompactSpace K] :
    IsClosed {p : K × ProbabilityMeasure K | Represents K p.1 p.2} := by
  simp only [Represents, setOf_forall]
  exact isClosed_iInter fun L => isClosed_eq
    ((continuous_integral_dual K L).comp continuous_snd)
    ((L.continuous.comp continuous_subtype_val).comp continuous_fst)

omit [CompleteSpace X] in
lemma represents_dirac (K : Set X) (z : K) :
    Represents K z ⟨Measure.dirac z, Measure.dirac.isProbabilityMeasure⟩ := by
  intro L
  simp

omit [NormedSpace ℝ X] [CompleteSpace X] in
lemma integrable_coe (K : Set X) [CompactSpace K] (μ : ProbabilityMeasure K) :
    Integrable (fun y : K => (y.1 : X)) (μ : Measure K) := by
  simpa only [integrableOn_univ] using
    ContinuousOn.integrableOn_compact (μ := (μ : Measure K)) isCompact_univ
      continuous_subtype_val.continuousOn

lemma Represents.integral_coe_eq {K : Set X} [CompactSpace K]
    {z : K} {μ : ProbabilityMeasure K} (hμ : Represents K z μ) :
    ∫ y : K, (y.1 : X) ∂(μ : Measure K) = z.1 := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro L
  calc
    L (∫ y : K, (y.1 : X) ∂(μ : Measure K)) =
        ∫ y : K, L y.1 ∂(μ : Measure K) :=
      (ContinuousLinearMap.integral_comp_comm L (integrable_coe K μ)).symm
    _ = L z.1 := hμ L

def testTerm (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (n : ℕ) (y : ↥K) : ℝ :=
  dist y (TopologicalSpace.denseSeq ↥K n) ^ 2 / 2 / 2 ^ n

def testFunction (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (y : ↥K) : ℝ :=
  ∑' n, testTerm K n y

omit [NormedSpace ℝ X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma testTerm_nonneg (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (n : ℕ) (y : ↥K) :
    0 ≤ testTerm K n y := by
  unfold testTerm
  positivity

omit [NormedSpace ℝ X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma testTerm_le_bound (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (n : ℕ) (y : ↥K) :
    testTerm K n y ≤ Metric.diam (univ : Set ↥K) ^ 2 / 2 / 2 ^ n := by
  unfold testTerm
  gcongr
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _)
    (mem_univ _)

omit [NormedSpace ℝ X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma summable_testTerm (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (y : ↥K) : Summable fun n => testTerm K n y := by
  exact Summable.of_nonneg_of_le (testTerm_nonneg K · y) (testTerm_le_bound K · y)
    (summable_geometric_two' (Metric.diam (univ : Set ↥K) ^ 2))

omit [NormedSpace ℝ X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_testFunction (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] :
    Continuous (testFunction K) := by
  apply continuous_tsum
  · intro n
    unfold testTerm
    fun_prop
  · exact summable_geometric_two' (Metric.diam (univ : Set ↥K) ^ 2)
  · intro n y
    rw [Real.norm_eq_abs, abs_of_nonneg (testTerm_nonneg K n y)]
    exact testTerm_le_bound K n y

omit [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma dist_sq_combo_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (u v q : X) :
    dist (a • u + b • v) q ^ 2 ≤ a * dist u q ^ 2 + b * dist v q ^ 2 := by
  have hvec : a • u + b • v - q = a • (u - q) + b • (v - q) := by
    calc
      a • u + b • v - q = a • u + b • v - (a + b) • q := by rw [hab, one_smul]
      _ = a • (u - q) + b • (v - q) := by module
  have hdist : dist (a • u + b • v) q ≤ a * dist u q + b * dist v q := by
    simp only [dist_eq_norm, hvec]
    calc
      ‖a • (u - q) + b • (v - q)‖ ≤ ‖a • (u - q)‖ + ‖b • (v - q)‖ :=
        norm_add_le _ _
      _ = a * ‖u - q‖ + b * ‖v - q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
  have hweighted :
      (a * dist u q + b * dist v q) ^ 2 ≤
        a * dist u q ^ 2 + b * dist v q ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (dist u q - dist v q))]
  have hsum_nonneg : 0 ≤ a * dist u q + b * dist v q :=
    add_nonneg (mul_nonneg ha dist_nonneg) (mul_nonneg hb dist_nonneg)
  have hcombo_nonneg : 0 ≤ dist (a • u + b • v) q := dist_nonneg
  have hsquare :
      dist (a • u + b • v) q ^ 2 ≤ (a * dist u q + b * dist v q) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdist)
      (add_nonneg hsum_nonneg hcombo_nonneg)]
  exact hsquare.trans hweighted

omit [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma dist_sq_combo_lt_left (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    {u v : X} (huv : u ≠ v) :
    dist (a • u + b • v) u ^ 2 < a * dist u u ^ 2 + b * dist v u ^ 2 := by
  have hvec : a • u + b • v - u = b • (v - u) := by
    calc
      a • u + b • v - u = a • u + b • v - (a + b) • u := by rw [hab, one_smul]
      _ = b • (v - u) := by module
  have hdist : dist (a • u + b • v) u = b * dist v u := by
    simp [dist_eq_norm, hvec, norm_smul, Real.norm_eq_abs, abs_of_pos hb]
  have hd : 0 < dist v u := dist_pos.mpr huv.symm
  rw [hdist, dist_self]
  nlinarith [mul_pos (mul_pos ha hb) (sq_pos_of_pos hd)]

omit [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma testTerm_combo_le (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {u v w : ↥K} (hw : w.1 = a • u.1 + b • v.1) (n : ℕ) :
    testTerm K n w ≤ a * testTerm K n u + b * testTerm K n v := by
  unfold testTerm
  have h := dist_sq_combo_le a b ha hb hab u.1 v.1
    (TopologicalSpace.denseSeq ↥K n).1
  rw [← hw] at h
  calc
    dist w (TopologicalSpace.denseSeq ↥K n) ^ 2 / 2 / 2 ^ n =
        dist w (TopologicalSpace.denseSeq ↥K n) ^ 2 / (2 * 2 ^ n) := by ring
    _ ≤ (a * dist u (TopologicalSpace.denseSeq ↥K n) ^ 2 +
          b * dist v (TopologicalSpace.denseSeq ↥K n) ^ 2) / (2 * 2 ^ n) :=
      div_le_div_of_nonneg_right (by simpa only [Subtype.dist_eq] using h) (by positivity)
    _ = a * (dist u (TopologicalSpace.denseSeq ↥K n) ^ 2 / 2 / 2 ^ n) +
        b * (dist v (TopologicalSpace.denseSeq ↥K n) ^ 2 / 2 / 2 ^ n) := by ring

omit [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_testTerm_combo_lt (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    {u v w : ↥K} (huv : u ≠ v) (hw : w.1 = a • u.1 + b • v.1) :
    ∃ n, testTerm K n w < a * testTerm K n u + b * testTerm K n v := by
  let s : Set ↥K := {q | dist w q ^ 2 < a * dist u q ^ 2 + b * dist v q ^ 2}
  have hs_open : IsOpen s := by
    apply isOpen_lt <;> fun_prop
  have hu_mem : u ∈ s := by
    change dist (w.1 : X) u.1 ^ 2 < a * dist u.1 u.1 ^ 2 + b * dist v.1 u.1 ^ 2
    rw [hw]
    exact dist_sq_combo_lt_left a b ha hb hab (Subtype.coe_injective.ne huv)
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq ↥K).exists_mem_open
    hs_open ⟨u, hu_mem⟩
  refine ⟨n, ?_⟩
  unfold testTerm
  change dist w (TopologicalSpace.denseSeq ↥K n) ^ 2 / 2 / 2 ^ n <
    a * (dist u (TopologicalSpace.denseSeq ↥K n) ^ 2 / 2 / 2 ^ n) +
      b * (dist v (TopologicalSpace.denseSeq ↥K n) ^ 2 / 2 / 2 ^ n)
  calc
    dist w (TopologicalSpace.denseSeq ↥K n) ^ 2 / 2 / 2 ^ n =
        dist w (TopologicalSpace.denseSeq ↥K n) ^ 2 / (2 * 2 ^ n) := by ring
    _ < (a * dist u (TopologicalSpace.denseSeq ↥K n) ^ 2 +
          b * dist v (TopologicalSpace.denseSeq ↥K n) ^ 2) / (2 * 2 ^ n) :=
      div_lt_div_of_pos_right hn (by positivity)
    _ = a * (dist u (TopologicalSpace.denseSeq ↥K n) ^ 2 / 2 / 2 ^ n) +
        b * (dist v (TopologicalSpace.denseSeq ↥K n) ^ 2 / 2 / 2 ^ n) := by ring

omit [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma testFunction_combo_lt (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    {u v w : ↥K} (huv : u ≠ v) (hw : w.1 = a • u.1 + b • v.1) :
    testFunction K w < a * testFunction K u + b * testFunction K v := by
  obtain ⟨n, hn⟩ := exists_testTerm_combo_lt K a b ha hb hab huv hw
  have hle (i : ℕ) : testTerm K i w ≤ a * testTerm K i u + b * testTerm K i v :=
    testTerm_combo_le K a b ha.le hb.le hab hw i
  have hsum_u := summable_testTerm K u
  have hsum_v := summable_testTerm K v
  have hsum_w := summable_testTerm K w
  have hsum_au := hsum_u.mul_left a
  have hsum_bv := hsum_v.mul_left b
  have hsum_rhs : Summable fun i => a * testTerm K i u + b * testTerm K i v :=
    hsum_au.add hsum_bv
  have hlt := hsum_w.tsum_lt_tsum hle hn hsum_rhs
  unfold testFunction at hlt ⊢
  calc
    ∑' i, testTerm K i w < ∑' i, (a * testTerm K i u + b * testTerm K i v) := hlt
    _ = a * ∑' i, testTerm K i u + b * ∑' i, testTerm K i v := by
      calc
        ∑' i, (a * testTerm K i u + b * testTerm K i v) =
            (∑' i, a * testTerm K i u) + ∑' i, b * testTerm K i v :=
          (hsum_au.hasSum.add hsum_bv.hasSum).tsum_eq
        _ = a * ∑' i, testTerm K i u + b * ∑' i, testTerm K i v := by
          rw [hsum_u.tsum_mul_left a, hsum_v.tsum_mul_left b]

def mixProbability {K : Set X} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure K) : ProbabilityMeasure K :=
  ⟨a.toNNReal • (μ : Measure K) + b.toNNReal • (ν : Measure K), by
    rw [isProbabilityMeasure_iff]
    simp only [Measure.coe_add, Pi.add_apply, Measure.coe_nnreal_smul_apply, measure_univ,
      mul_one]
    rw [← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj]
    apply NNReal.eq
    simpa [Real.coe_toNNReal a ha, Real.coe_toNNReal b hb] using hab⟩

omit [NormedSpace ℝ X] [CompleteSpace X] in
lemma integral_mixProbability {K : Set X} [CompactSpace ↥K]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure K) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : K → E} (hf : Continuous f) :
    ∫ y, f y ∂(mixProbability a b ha hb hab μ ν : Measure K) =
      a • ∫ y, f y ∂(μ : Measure K) + b • ∫ y, f y ∂(ν : Measure K) := by
  have hfμ : Integrable f (μ : Measure K) := by
    simpa only [integrableOn_univ] using
      ContinuousOn.integrableOn_compact (μ := (μ : Measure K)) isCompact_univ hf.continuousOn
  have hfν : Integrable f (ν : Measure K) := by
    simpa only [integrableOn_univ] using
      ContinuousOn.integrableOn_compact (μ := (ν : Measure K)) isCompact_univ hf.continuousOn
  change ∫ y, f y ∂(a.toNNReal • (μ : Measure K) + b.toNNReal • (ν : Measure K)) = _
  rw [integral_add_measure hfμ.smul_measure_nnreal hfν.smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Real.coe_toNNReal a ha, Real.coe_toNNReal b hb]

omit [CompleteSpace X] in
lemma Represents.mix {K : Set X} [CompactSpace ↥K]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {u v w : K} {μ ν : ProbabilityMeasure K}
    (hμ : Represents K u μ) (hν : Represents K v ν)
    (hw : w.1 = a • u.1 + b • v.1) :
    Represents K w (mixProbability a b ha hb hab μ ν) := by
  intro L
  have hi := integral_mixProbability a b ha hb hab μ ν
    (f := fun y : K => L y.1) (L.continuous.comp continuous_subtype_val)
  rw [hi, hμ L, hν L]
  simpa [map_add, map_smul] using (congrArg L hw).symm

def objective (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (μ : ProbabilityMeasure K) : ℝ :=
  ∫ y, testFunction K y ∂(μ : Measure K)

omit [NormedSpace ℝ X] [CompleteSpace X] in
lemma continuous_objective (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] :
    Continuous (objective K) := by
  exact ProbabilityMeasure.continuous_integral_continuousMap
    (⟨testFunction K, continuous_testFunction K⟩ : C(↥K, ℝ))

omit [NormedSpace ℝ X] [CompleteSpace X] in
lemma objective_mix (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (μ ν : ProbabilityMeasure K) :
    objective K (mixProbability a b ha hb hab μ ν) =
      a * objective K μ + b * objective K ν := by
  simpa [objective, smul_eq_mul] using
    integral_mixProbability a b ha hb hab μ ν (continuous_testFunction K)

def momentMap (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (p : K × ProbabilityMeasure K) : X × ℝ :=
  (p.1.1, objective K p.2)

def attainable (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] :
    Set (X × ℝ) :=
  momentMap K '' {p : K × ProbabilityMeasure K | Represents K p.1 p.2}

omit [NormedSpace ℝ X] [CompleteSpace X] in
lemma continuous_momentMap (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] :
    Continuous (momentMap K) := by
  exact (continuous_subtype_val.comp continuous_fst).prodMk
    ((continuous_objective K).comp continuous_snd)

omit [CompleteSpace X] in
lemma isCompact_attainable (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] :
    IsCompact (attainable K) := by
  exact ((isClosed_represents K).isCompact.image (continuous_momentMap K))

omit [CompleteSpace X] in
lemma mem_attainable_dirac (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] (z : K) :
    (z.1, testFunction K z) ∈ attainable K := by
  let δ : ProbabilityMeasure K := ⟨Measure.dirac z, Measure.dirac.isProbabilityMeasure⟩
  refine ⟨(z, δ), represents_dirac K z, ?_⟩
  ext
  · rfl
  · simp [momentMap, objective, δ]

omit [CompleteSpace X] in
lemma convex_attainable (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] (hK : Convex ℝ K) :
    Convex ℝ (attainable K) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a b ha hb hab
  let w : K := ⟨a • p.1.1 + b • q.1.1, hK p.1.2 q.1.2 ha hb hab⟩
  let ρ := mixProbability a b ha hb hab p.2 q.2
  refine ⟨(w, ρ), ?_, ?_⟩
  · exact hp.mix a b ha hb hab hq rfl
  · ext
    · rfl
    · simp [momentMap, ρ, objective_mix K a b ha hb hab]

omit [CompleteSpace X] [BorelSpace X] in
lemma mem_attainable_of_represents (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    {z : K} {μ : ProbabilityMeasure K} (hμ : Represents K z μ) :
    (z.1, objective K μ) ∈ attainable K := by
  exact ⟨(z, μ), hμ, rfl⟩

def representingMeasures (K : Set X) (z : K) : Set (ProbabilityMeasure K) :=
  {μ | Represents K z μ}

omit [CompleteSpace X] in
lemma isCompact_representingMeasures (K : Set X) [CompactSpace ↥K] (z : K) :
    IsCompact (representingMeasures K z) := by
  have hclosed : IsClosed (representingMeasures K z) := by
    have hcont : Continuous fun μ : ProbabilityMeasure K => (z, μ) :=
      continuous_const.prodMk continuous_id
    exact (isClosed_represents K).preimage hcont
  exact hclosed.isCompact

omit [CompleteSpace X] in
lemma nonempty_representingMeasures (K : Set X) (z : K) :
    (representingMeasures K z).Nonempty := by
  exact ⟨⟨Measure.dirac z, Measure.dirac.isProbabilityMeasure⟩, represents_dirac K z⟩

omit [CompleteSpace X] in
lemma exists_objective_maximizer (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] (z : K) :
    ∃ μ : ProbabilityMeasure K, Represents K z μ ∧
      ∀ ν : ProbabilityMeasure K, Represents K z ν → objective K ν ≤ objective K μ := by
  obtain ⟨μ, hμ, hmax⟩ := (isCompact_representingMeasures K z).exists_isMaxOn
    (nonempty_representingMeasures K z) (continuous_objective K).continuousOn
  exact ⟨μ, hμ, hmax⟩

omit [CompleteSpace X] in
lemma exists_affine_majorant (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] (hK : Convex ℝ K)
    {z : K} {μ : ProbabilityMeasure K} (hμ : Represents K z μ)
    (hmax : ∀ ν : ProbabilityMeasure K, Represents K z ν → objective K ν ≤ objective K μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : C(↥K, ℝ),
      (∀ y : K, testFunction K y < A y) ∧
      A z = objective K μ + ε ∧
      ∀ (w : K) (ν : ProbabilityMeasure K), Represents K w ν →
        ∫ y, A y ∂(ν : Measure K) = A w := by
  let p : X × ℝ := (z.1, objective K μ)
  let q : X × ℝ := (z.1, objective K μ + ε)
  have hp : p ∈ attainable K := mem_attainable_of_represents K hμ
  have hq : q ∉ attainable K := by
    rintro ⟨r, hr, hrq⟩
    have hz : r.1 = z := by
      apply Subtype.ext
      exact congrArg Prod.fst hrq
    have hobj : objective K r.2 = objective K μ + ε := congrArg Prod.snd hrq
    have hle := hmax r.2 (hz ▸ hr)
    exact (not_lt_of_ge hle) (by linarith)
  obtain ⟨L, c, hLc, hcq⟩ := geometric_hahn_banach_closed_point
    (convex_attainable K hK) (isCompact_attainable K).isClosed hq
  let β : ℝ := L (0, 1)
  have hpq : L p < L q := (hLc p hp).trans hcq
  have hq_decomp : q = p + ε • (0, 1) := by
    ext <;> simp [p, q]
  have hLq : L q = L p + ε * β := by
    rw [hq_decomp, map_add, map_smul]
    simp [β, smul_eq_mul]
  have hβ : 0 < β := by
    by_contra h
    have hβ' : β ≤ 0 := not_lt.mp h
    have hmul : ε * β ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε.le hβ'
    linarith
  let A : C(↥K, ℝ) :=
    ⟨fun y => (L q - L (y.1, 0)) / β, by fun_prop⟩
  refine ⟨A, ?_, ?_, ?_⟩
  · intro y
    have hy : (y.1, testFunction K y) ∈ attainable K := mem_attainable_dirac K y
    have hyq : L (y.1, testFunction K y) < L q := (hLc _ hy).trans hcq
    have hy_decomp : (y.1, testFunction K y) =
        (y.1, 0) + testFunction K y • (0, 1) := by
      ext <;> simp
    have hLy : L (y.1, testFunction K y) =
        L (y.1, 0) + testFunction K y * β := by
      rw [hy_decomp, map_add, map_smul]
      simp [β, smul_eq_mul]
    change testFunction K y < (L q - L (y.1, 0)) / β
    rw [lt_div_iff₀ hβ]
    linarith
  · have hp_decomp : p = (z.1, 0) + objective K μ • (0, 1) := by
      ext <;> simp [p]
    have hLp : L p = L (z.1, 0) + objective K μ * β := by
      rw [hp_decomp, map_add, map_smul]
      simp [β, smul_eq_mul]
    change (L q - L (z.1, 0)) / β = objective K μ + ε
    apply (div_eq_iff hβ.ne').2
    nlinarith
  · intro w ν hν
    let Lx : X →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ X ℝ)
    have hLx : ∫ y : K, L (y.1, 0) ∂(ν : Measure K) = L (w.1, 0) := by
      simpa [Lx, ContinuousLinearMap.inl_apply] using hν Lx
    have hconst : Integrable (fun _ : K => L q) (ν : Measure K) := integrable_const _
    have hlin : Integrable (fun y : K => L (y.1, 0)) (ν : Measure K) := by
      have hcont : Continuous (fun y : K => L (y.1, 0)) := by fun_prop
      simpa only [integrableOn_univ] using
        ContinuousOn.integrableOn_compact (μ := (ν : Measure K)) isCompact_univ
          hcont.continuousOn
    change ∫ y : K, (L q - L (y.1, 0)) / β ∂(ν : Measure K) =
      (L q - L (w.1, 0)) / β
    rw [integral_div, integral_sub hconst hlin, integral_const, hLx]
    simp

def badPairs (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] (n : ℕ) :
    Set (K × ProbabilityMeasure K) :=
  {p | Represents K p.1 p.2 ∧
    testFunction K p.1 + 1 / (n + 1 : ℝ) ≤ objective K p.2}

def badSet (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] (n : ℕ) :
    Set K :=
  Prod.fst '' badPairs K n

omit [CompleteSpace X] in
lemma isClosed_badPairs (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] (n : ℕ) :
    IsClosed (badPairs K n) := by
  apply (isClosed_represents K).inter
  exact isClosed_le
    (((continuous_testFunction K).comp continuous_fst).add continuous_const)
    ((continuous_objective K).comp continuous_snd)

omit [CompleteSpace X] in
lemma isCompact_badSet (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] (n : ℕ) :
    IsCompact (badSet K n) := by
  exact (isClosed_badPairs K n).isCompact.image continuous_fst

omit [CompleteSpace X] [BorelSpace X] in
lemma mem_badSet_iff (K : Set X) [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (n : ℕ) (y : K) :
    y ∈ badSet K n ↔ ∃ ν : ProbabilityMeasure K,
      Represents K y ν ∧ testFunction K y + 1 / (n + 1 : ℝ) ≤ objective K ν := by
  simp [badSet, badPairs]

omit [CompleteSpace X] in
lemma nonextreme_mem_iUnion_bad (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K]
    (y : K) (hy : y.1 ∉ K.extremePoints ℝ) :
    y ∈ ⋃ n, badSet K n := by
  rw [mem_extremePoints_iff_left] at hy
  simp only [y.2, true_and] at hy
  push Not at hy
  obtain ⟨u, hu, v, hv, hyseg, huy⟩ := hy
  obtain ⟨a, b, ha, hb, hab, hcombo⟩ := hyseg
  let uK : K := ⟨u, hu⟩
  let vK : K := ⟨v, hv⟩
  have huv : uK ≠ vK := by
    intro huv
    have huv' : u = v := congrArg Subtype.val huv
    have huy' : u = y.1 := by
      rw [← hcombo, huv', ← add_smul, hab, one_smul]
    exact huy huy'
  let δu : ProbabilityMeasure K := ⟨Measure.dirac uK, Measure.dirac.isProbabilityMeasure⟩
  let δv : ProbabilityMeasure K := ⟨Measure.dirac vK, Measure.dirac.isProbabilityMeasure⟩
  let ν := mixProbability a b ha.le hb.le hab δu δv
  have hν : Represents K y ν := by
    exact (represents_dirac K uK).mix a b ha.le hb.le hab (represents_dirac K vK)
      hcombo.symm
  have hstrict : testFunction K y < a * testFunction K uK + b * testFunction K vK :=
    testFunction_combo_lt K a b ha hb hab huv hcombo.symm
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hstrict)
  rw [mem_iUnion]
  refine ⟨n, (mem_badSet_iff K n y).2 ⟨ν, hν, ?_⟩⟩
  have hobj : objective K ν = a * testFunction K uK + b * testFunction K vK := by
    rw [objective_mix K a b ha.le hb.le hab]
    simp [objective, δu, δv]
  rw [hobj]
  linarith

omit [CompleteSpace X] in
lemma measure_badSet_eq_zero (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] (hK : Convex ℝ K)
    {z : K} {μ : ProbabilityMeasure K} (hμ : Represents K z μ)
    (hmax : ∀ ν : ProbabilityMeasure K, Represents K z ν → objective K ν ≤ objective K μ)
    (n : ℕ) :
    (μ : Measure K) (badSet K n) = 0 := by
  by_contra hbad
  let δ : ℝ := 1 / (n + 1 : ℝ)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let m : ℝ := ((μ : Measure K) (badSet K n)).toReal
  have hm : 0 < m := by
    exact ENNReal.toReal_pos hbad (measure_ne_top _ _)
  let ε : ℝ := δ * m / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨A, hAmajor, hAz, hAbar⟩ := exists_affine_majorant K hK hμ hmax hε
  let g : K → ℝ := fun y => (A y - testFunction K y) / δ
  have hgcont : Continuous g := by
    exact (A.continuous.sub (continuous_testFunction K)).div_const δ
  have hgint : Integrable g (μ : Measure K) := by
    simpa only [integrableOn_univ] using
      ContinuousOn.integrableOn_compact (μ := (μ : Measure K)) isCompact_univ
        hgcont.continuousOn
  have hgnonneg : ∀ y : K, 0 ≤ g y := by
    intro y
    exact div_nonneg (sub_nonneg.mpr (hAmajor y).le) hδ.le
  have hgap {y : K} (hy : y ∈ badSet K n) : δ ≤ A y - testFunction K y := by
    obtain ⟨ν, hν, hνgap⟩ := (mem_badSet_iff K n y).1 hy
    have hfint : Integrable (testFunction K) (ν : Measure K) := by
      simpa only [integrableOn_univ] using
        ContinuousOn.integrableOn_compact (μ := (ν : Measure K)) isCompact_univ
          (continuous_testFunction K).continuousOn
    have hAint : Integrable (fun t : K => A t) (ν : Measure K) := by
      simpa only [integrableOn_univ] using
        ContinuousOn.integrableOn_compact (μ := (ν : Measure K)) isCompact_univ
          A.continuous.continuousOn
    have hobj_le : objective K ν ≤ A y := by
      rw [← hAbar y ν hν]
      exact integral_mono hfint hAint fun t => (hAmajor t).le
    change testFunction K y + δ ≤ objective K ν at hνgap
    linarith
  have hmeasure := hgint.measure_le_integral (ae_of_all _ hgnonneg)
    (s := badSet K n) (fun y hy => by
      change 1 ≤ (A y - testFunction K y) / δ
      rw [le_div_iff₀ hδ]
      simpa [one_mul] using hgap hy)
  have hAμ := hAbar z μ hμ
  have hfμ : Integrable (testFunction K) (μ : Measure K) := by
    simpa only [integrableOn_univ] using
      ContinuousOn.integrableOn_compact (μ := (μ : Measure K)) isCompact_univ
        (continuous_testFunction K).continuousOn
  have hAμint : Integrable (fun t : K => A t) (μ : Measure K) := by
    simpa only [integrableOn_univ] using
      ContinuousOn.integrableOn_compact (μ := (μ : Measure K)) isCompact_univ
        A.continuous.continuousOn
  have hgIntegral : ∫ y, g y ∂(μ : Measure K) = ε / δ := by
    change ∫ y : K, (A y - testFunction K y) / δ ∂(μ : Measure K) = ε / δ
    rw [integral_div, integral_sub hAμint hfμ, hAμ]
    change (A z - objective K μ) / δ = ε / δ
    rw [hAz]
    ring
  rw [hgIntegral] at hmeasure
  have hreal := ENNReal.toReal_mono (by finiteness) hmeasure
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ ε / δ)] at hreal
  change m ≤ ε / δ at hreal
  dsimp [ε] at hreal
  field_simp [hδ.ne'] at hreal
  linarith

omit [CompleteSpace X] in
lemma measure_nonextreme_eq_zero (K : Set X) [CompactSpace ↥K]
    [TopologicalSpace.SeparableSpace ↥K] [Nonempty ↥K] (hK : Convex ℝ K)
    {z : K} {μ : ProbabilityMeasure K} (hμ : Represents K z μ)
    (hmax : ∀ ν : ProbabilityMeasure K, Represents K z ν → objective K ν ≤ objective K μ) :
    (μ : Measure K) {y : K | y.1 ∉ K.extremePoints ℝ} = 0 := by
  apply le_antisymm ?_ zero_le
  calc
    (μ : Measure K) {y : K | y.1 ∉ K.extremePoints ℝ} ≤
        (μ : Measure K) (⋃ n, badSet K n) := by
      apply measure_mono
      intro y hy
      exact nonextreme_mem_iUnion_bad K y hy
    _ = 0 := measure_iUnion_null fun n => measure_badSet_eq_zero K hK hμ hmax n

theorem exists_choquet_measure
    (K : Set X) (hK_cpt : IsCompact K) (hK_cvx : Convex ℝ K)
    {x : X} (hx : x ∈ K) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      μ (K.extremePoints ℝ)ᶜ = 0 ∧
      x = ∫ y, y ∂μ := by
  let xK : K := ⟨x, hx⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK_cpt
  letI : TopologicalSpace.SeparableSpace K := hK_cpt.isSeparable.separableSpace
  letI : Nonempty K := ⟨xK⟩
  obtain ⟨μK, hμK, hmax⟩ := exists_objective_maximizer K xK
  have hnull := measure_nonextreme_eq_zero K hK_cvx hμK hmax
  let emb : K → X := Subtype.val
  have hemb : MeasurableEmbedding emb := MeasurableEmbedding.subtype_coe hK_cpt.measurableSet
  let μ : Measure X := Measure.map emb (μK : Measure K)
  have hprob : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map hemb.measurable.aemeasurable
  refine ⟨μ, hprob, ?_, ?_⟩
  · dsimp [μ]
    rw [hemb.map_apply]
    have hset : emb ⁻¹' (K.extremePoints ℝ)ᶜ = {y : K | y.1 ∉ K.extremePoints ℝ} := by
      ext y
      simp [emb]
    rw [hset]
    exact hnull
  · have hbarK := hμK.integral_coe_eq
    have hmap := hemb.integral_map (μ := (μK : Measure K)) (fun y : X => y)
    dsimp [μ]
    exact hbarK.symm.trans hmap.symm

end Submission.Helpers
