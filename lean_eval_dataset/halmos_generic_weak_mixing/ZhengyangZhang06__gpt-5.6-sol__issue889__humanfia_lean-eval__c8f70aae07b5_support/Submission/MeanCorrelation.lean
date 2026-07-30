import Submission.Criterion
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.MeasureTheory.Function.L2Space

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology Finset Function
open scoped InnerProductSpace

namespace Submission.MeanCorrelation

noncomputable section

variable {X : Type*} [MeasurableSpace X]

abbrev RealL2 (m : Measure X) := MeasureTheory.Lp ℝ 2 m

def koopman {m : Measure X} (T : Automorphism m) :
    RealL2 m →L[ℝ] RealL2 m :=
  (Lp.compMeasurePreservingₗᵢ ℝ (T.toEquiv : X → X)
    T.measurePreserving).toContinuousLinearMap

theorem koopman_norm_le {m : Measure X} (T : Automorphism m) :
    ‖koopman T‖ ≤ 1 := by
  apply (koopman T).opNorm_le_bound (by norm_num)
  intro f
  simp [koopman]

theorem koopman_iterate_apply {m : Measure X} (T : Automorphism m)
    (k : ℕ) (f : RealL2 m) :
    ((koopman T : RealL2 m → RealL2 m)^[k]) f =
      Lp.compMeasurePreserving ((T.toEquiv : X → X)^[k])
        (T.measurePreserving.iterate k) f := by
  change ((Lp.compMeasurePreserving (E := ℝ) (p := 2)
    (T.toEquiv : X → X) T.measurePreserving)^[k]) f = _
  rw [Lp.compMeasurePreserving_iterate]

theorem inner_koopman_iterate_indicator {m : Measure X} [IsFiniteMeasure m]
    (T : Automorphism m) (k : ℕ) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ⟪((koopman T : RealL2 m → RealL2 m)^[k])
        (indicatorConstLp 2 hA (measure_ne_top m A) (1 : ℝ)),
      indicatorConstLp 2 hB (measure_ne_top m B) (1 : ℝ)⟫_ℝ =
      m.real (WeakTopology.iteratePreimage T k A ∩ B) := by
  rw [koopman_iterate_apply]
  rw [Lp.indicatorConstLp_compMeasurePreserving]
  simpa only [WeakTopology.iteratePreimage] using
    (L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
      (hA.preimage (T.measurePreserving.iterate k).measurable) hB)

def rawCorrelationAverage (m : Measure X) (T : Automorphism m)
    (A B : Set X) (n : ℕ) : ℝ :=
  (∑ k ∈ range n,
    m.real (WeakTopology.iteratePreimage T k A ∩ B)) / (n : ℝ)

theorem inner_birkhoffAverage_indicator {m : Measure X} [IsFiniteMeasure m]
    (T : Automorphism m) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    ⟪birkhoffAverage ℝ (koopman T) id n
        (indicatorConstLp 2 hA (measure_ne_top m A) (1 : ℝ)),
      indicatorConstLp 2 hB (measure_ne_top m B) (1 : ℝ)⟫_ℝ =
      rawCorrelationAverage m T A B n := by
  simp only [birkhoffAverage, birkhoffSum, id_eq, sum_inner,
    inner_smul_left, RCLike.conj_to_real]
  simp_rw [inner_koopman_iterate_indicator T _ hA hB]
  rw [rawCorrelationAverage, div_eq_inv_mul]

theorem exists_tendsto_rawCorrelationAverage (m : Measure X)
    [IsFiniteMeasure m] (T : Automorphism m) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∃ l : ℝ, Tendsto (rawCorrelationAverage m T A B) atTop (𝓝 l) := by
  let fA : RealL2 m := indicatorConstLp 2 hA (measure_ne_top m A) (1 : ℝ)
  let fB : RealL2 m := indicatorConstLp 2 hB (measure_ne_top m B) (1 : ℝ)
  let P : RealL2 m :=
    ((koopman T).eqLocus
      (1 : RealL2 m →L[ℝ] RealL2 m)).orthogonalProjectionOnto fA
  have hvec := (koopman T).tendsto_birkhoffAverage_orthogonalProjection
    (koopman_norm_le T) fA
  have hinner : Tendsto
      (fun n : ℕ ↦ ⟪birkhoffAverage ℝ (koopman T) id n fA, fB⟫_ℝ)
      atTop (𝓝 ⟪P, fB⟫_ℝ) :=
    hvec.inner (𝕜 := ℝ) (tendsto_const_nhds (x := fB))
  refine ⟨⟪P, fB⟫_ℝ, ?_⟩
  apply hinner.congr'
  filter_upwards [] with n
  exact inner_birkhoffAverage_indicator T hA hB n

def prodAutomorphism {m : Measure X} [SFinite m] (T : Automorphism m) :
    Automorphism (m.prod m) where
  toEquiv := MeasurableEquiv.prodCongr T.toEquiv T.toEquiv
  measurePreserving := T.measurePreserving.prod T.measurePreserving

@[simp]
theorem prodAutomorphism_apply {m : Measure X} [SFinite m]
    (T : Automorphism m)
    (x : X × X) :
    (prodAutomorphism T).toEquiv x = (T.toEquiv x.1, T.toEquiv x.2) :=
  rfl

theorem prodAutomorphism_iterate_apply {m : Measure X} [SFinite m]
    (T : Automorphism m) (k : ℕ) (x : X × X) :
    (((prodAutomorphism T).toEquiv : X × X → X × X)^[k]) x =
      (((T.toEquiv : X → X)^[k]) x.1,
        ((T.toEquiv : X → X)^[k]) x.2) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, prodAutomorphism_apply, ih]

theorem prod_iteratePreimage_prod {m : Measure X} [SFinite m]
    (T : Automorphism m)
    (k : ℕ) (A B : Set X) :
    WeakTopology.iteratePreimage (prodAutomorphism T) k (A ×ˢ B) =
      WeakTopology.iteratePreimage T k A ×ˢ
        WeakTopology.iteratePreimage T k B := by
  ext x
  simp only [WeakTopology.iteratePreimage, Set.mem_preimage,
    Set.mem_prod, prodAutomorphism_iterate_apply]

def rawCorrelationSquareAverage (m : Measure X) (T : Automorphism m)
    (A B : Set X) (n : ℕ) : ℝ :=
  (∑ k ∈ range n,
    (m.real (WeakTopology.iteratePreimage T k A ∩ B)) ^ 2) / (n : ℝ)

theorem rawCorrelationAverage_prod (m : Measure X) [SFinite m]
    (T : Automorphism m)
    (A B : Set X) (n : ℕ) :
    rawCorrelationAverage (m.prod m) (prodAutomorphism T)
        (A ×ˢ A) (B ×ˢ B) n =
      rawCorrelationSquareAverage m T A B n := by
  simp only [rawCorrelationAverage, rawCorrelationSquareAverage,
    prod_iteratePreimage_prod, Set.prod_inter_prod, pow_two]
  simp_rw [MeasureTheory.measureReal_prod_prod]

theorem exists_tendsto_rawCorrelationSquareAverage (m : Measure X)
    [IsFiniteMeasure m] (T : Automorphism m) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∃ l : ℝ, Tendsto (rawCorrelationSquareAverage m T A B) atTop (nhds l) := by
  obtain ⟨l, hl⟩ := exists_tendsto_rawCorrelationAverage (m.prod m)
    (prodAutomorphism T) (hA.prod hA) (hB.prod hB)
  exact ⟨l, hl.congr' (Eventually.of_forall fun n ↦
    rawCorrelationAverage_prod m T A B n)⟩

noncomputable def squareCorrelationAverage (m : Measure X)
    (T : Automorphism m) (A B : Set X) (n : ℕ) : ℝ :=
  (∑ k ∈ range n, (Criterion.correlationTerm m T A B k) ^ 2) /
    (n : ℝ)

theorem squareCorrelationAverage_eq (m : Measure X) (T : Automorphism m)
    (A B : Set X) {n : ℕ} (hn : 0 < n) :
    squareCorrelationAverage m T A B n =
      rawCorrelationSquareAverage m T A B n -
        2 * (m.real A * m.real B) * rawCorrelationAverage m T A B n +
        (m.real A * m.real B) ^ 2 := by
  rw [squareCorrelationAverage, rawCorrelationSquareAverage,
    rawCorrelationAverage]
  simp_rw [Criterion.correlationTerm, sq_abs, sub_sq]
  rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum,
    sum_const, card_range]
  field_simp [Nat.ne_of_gt hn]
  ring

theorem exists_tendsto_squareCorrelationAverage (m : Measure X)
    [IsFiniteMeasure m] (T : Automorphism m) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∃ l : ℝ, Tendsto (squareCorrelationAverage m T A B) atTop (nhds l) := by
  obtain ⟨l₁, hl₁⟩ := exists_tendsto_rawCorrelationAverage m T hA hB
  obtain ⟨l₂, hl₂⟩ := exists_tendsto_rawCorrelationSquareAverage m T hA hB
  let p := m.real A * m.real B
  refine ⟨l₂ - 2 * p * l₁ + p ^ 2, ?_⟩
  have hlim : Tendsto
      (fun n ↦ rawCorrelationSquareAverage m T A B n -
        2 * p * rawCorrelationAverage m T A B n + p ^ 2)
      atTop (nhds (l₂ - 2 * p * l₁ + p ^ 2)) :=
    (hl₂.sub ((tendsto_const_nhds.mul tendsto_const_nhds).mul hl₁)).add
      tendsto_const_nhds
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (squareCorrelationAverage_eq m T A B hn).symm

theorem continuous_squareCorrelationAverage (m : Measure X)
    [IsFiniteMeasure m] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    Continuous (fun T : Automorphism m ↦
      squareCorrelationAverage m T A B n) := by
  unfold squareCorrelationAverage
  exact (continuous_finsetSum (range n) fun k _ ↦
    (Criterion.continuous_correlationTerm m hA hB k).pow 2).div_const n

theorem isOpen_squareCorrelationAverage_lt (m : Measure X)
    [IsFiniteMeasure m] {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) (r : ℝ) :
    IsOpen {T : Automorphism m | squareCorrelationAverage m T A B n < r} :=
  isOpen_lt (continuous_squareCorrelationAverage m hA hB n) continuous_const

theorem correlationTerm_le_one (m : Measure X) [IsProbabilityMeasure m]
    (T : Automorphism m) (A B : Set X) (k : ℕ) :
    Criterion.correlationTerm m T A B k ≤ 1 := by
  unfold Criterion.correlationTerm
  have hI0 : 0 ≤ m.real (WeakTopology.iteratePreimage T k A ∩ B) :=
    measureReal_nonneg
  have hI1 : m.real (WeakTopology.iteratePreimage T k A ∩ B) ≤ 1 :=
    measureReal_le_one
  have hA0 : 0 ≤ m.real A := measureReal_nonneg
  have hA1 : m.real A ≤ 1 := measureReal_le_one
  have hB0 : 0 ≤ m.real B := measureReal_nonneg
  have hB1 : m.real B ≤ 1 := measureReal_le_one
  rw [abs_le]
  constructor <;> nlinarith

theorem correlationTerm_sq_le (m : Measure X) [IsProbabilityMeasure m]
    (T : Automorphism m) (A B : Set X) (k : ℕ) :
    (Criterion.correlationTerm m T A B k) ^ 2 ≤
      Criterion.correlationTerm m T A B k := by
  have h0 : 0 ≤ Criterion.correlationTerm m T A B k := abs_nonneg _
  have h1 := correlationTerm_le_one m T A B k
  nlinarith

theorem squareCorrelationAverage_nonneg (m : Measure X)
    (T : Automorphism m) (A B : Set X) (n : ℕ) :
    0 ≤ squareCorrelationAverage m T A B n := by
  unfold squareCorrelationAverage
  exact div_nonneg (sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg n)

theorem squareCorrelationAverage_le (m : Measure X) [IsProbabilityMeasure m]
    (T : Automorphism m) (A B : Set X) (n : ℕ) :
    squareCorrelationAverage m T A B n ≤
      Criterion.correlationAverage m T A B n := by
  unfold squareCorrelationAverage Criterion.correlationAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact sum_le_sum fun k _ ↦ correlationTerm_sq_le m T A B k

theorem correlationAverage_sq_le (m : Measure X) (T : Automorphism m)
    (A B : Set X) (n : ℕ) :
    (Criterion.correlationAverage m T A B n) ^ 2 ≤
      squareCorrelationAverage m T A B n := by
  simpa only [Criterion.correlationAverage, squareCorrelationAverage,
    card_range] using
      (sum_div_card_sq_le_sum_sq_div_card
        (s := range n) (f := fun k ↦ Criterion.correlationTerm m T A B k))

theorem tendsto_correlationAverage_iff_square (m : Measure X)
    [IsProbabilityMeasure m] (T : Automorphism m) (A B : Set X) :
    Tendsto (Criterion.correlationAverage m T A B) atTop (nhds 0) ↔
      Tendsto (squareCorrelationAverage m T A B) atTop (nhds 0) := by
  constructor
  · intro h
    exact squeeze_zero
      (fun n ↦ squareCorrelationAverage_nonneg m T A B n)
      (fun n ↦ squareCorrelationAverage_le m T A B n) h
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [] with n
      unfold Criterion.correlationAverage
      have hnonneg : 0 ≤
          (∑ k ∈ range n, Criterion.correlationTerm m T A B k) / (n : ℝ) :=
        div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (Nat.cast_nonneg n)
      exact lt_of_lt_of_le ha hnonneg
    · intro ε hε
      have hev := (tendsto_order.mp h).2 (ε ^ 2) (sq_pos_of_pos hε)
      filter_upwards [hev] with n hn
      have hsq := correlationAverage_sq_le m T A B n
      have hnonneg : 0 ≤ Criterion.correlationAverage m T A B n := by
        unfold Criterion.correlationAverage
        exact div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _)
          (Nat.cast_nonneg n)
      nlinarith

theorem tendsto_square_of_arbitrarily_late_small (m : Measure X)
    [IsProbabilityMeasure m] (T : Automorphism m) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      squareCorrelationAverage m T A B n < ε) :
    Tendsto (squareCorrelationAverage m T A B) atTop (nhds 0) := by
  obtain ⟨l, hl⟩ := exists_tendsto_squareCorrelationAverage m T hA hB
  have hl0 : 0 ≤ l := ge_of_tendsto' hl
    (fun n ↦ squareCorrelationAverage_nonneg m T A B n)
  have hl_le : l ≤ 0 := by
    by_contra hnot
    have hlpos : 0 < l := lt_of_not_ge hnot
    have hevent : ∀ᶠ n in atTop,
        l / 2 < squareCorrelationAverage m T A B n :=
      (tendsto_order.mp hl).1 (l / 2) (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    obtain ⟨n, hnN, hn⟩ := hsmall (l / 2) (by linarith) N
    exact (not_lt_of_ge (hN n hnN).le) hn
  have : l = 0 := le_antisymm hl_le hl0
  simpa [this] using hl

end

end Submission.MeanCorrelation
