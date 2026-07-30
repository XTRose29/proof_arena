import ChallengeDeps

open scoped ENNReal NNReal Topology MeasureTheory
open Set Metric MeasureTheory Filter Bornology

namespace Submission.Helpers

noncomputable section

/-- The affine similarity `x ↦ λ A x + b`, bundled as a metric dilation. -/
def affineDilation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (lam : ℝ) (hlam : 0 < lam) (A : X →ₗᵢ[ℝ] X) (b : X) : X →ᵈ X :=
  Dilation.mkOfDistEq (fun x ↦ lam • A x + b) <|
    ⟨⟨lam, hlam.le⟩, NNReal.coe_ne_zero.mp hlam.ne', fun x y ↦ by
      rw [dist_add_right, dist_smul₀, A.isometry.dist_eq]
      exact congrArg (· * dist x y) (Real.norm_of_nonneg hlam.le)⟩

@[simp]
theorem affineDilation_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (lam : ℝ) (hlam : 0 < lam) (A : X →ₗᵢ[ℝ] X) (b x : X) :
    affineDilation lam hlam A b x = lam • A x + b :=
  rfl

theorem affineDilation_dist {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (lam : ℝ) (hlam : 0 < lam) (A : X →ₗᵢ[ℝ] X) (b x y : X) :
    dist (affineDilation lam hlam A b x) (affineDilation lam hlam A b y) =
      lam * dist x y := by
  rw [affineDilation_apply, affineDilation_apply, dist_add_right, dist_smul₀,
    A.isometry.dist_eq, Real.norm_of_nonneg hlam.le]

theorem affineDilation_ratio {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Nontrivial X] (lam : ℝ) (hlam : 0 < lam) (A : X →ₗᵢ[ℝ] X) (b : X) :
    Dilation.ratio (affineDilation lam hlam A b) = ⟨lam, hlam.le⟩ := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact (Dilation.ratio_unique_of_dist_ne_zero (dist_ne_zero.mpr hxy)
    (affineDilation_dist lam hlam A b x y)).symm

theorem affineDilation_surjective {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (lam : ℝ) (hlam : 0 < lam) (A : X →ₗᵢ[ℝ] X) (b : X) :
    Function.Surjective (affineDilation lam hlam A b) := by
  have hA : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp A.injective
  intro y
  obtain ⟨x, hx⟩ := hA (lam⁻¹ • (y - b))
  refine ⟨x, ?_⟩
  rw [affineDilation_apply, hx, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul,
    sub_add_cancel]

/-- Composition of the similarities indexed by a finite word. -/
def wordMap {X I : Type*} [PseudoEMetricSpace X] (φ : I → X →ᵈ X) :
    List I → X →ᵈ X
  | [] => 1
  | i :: w => φ i * wordMap φ w

@[simp]
theorem wordMap_nil {X I : Type*} [PseudoEMetricSpace X] (φ : I → X →ᵈ X) :
    wordMap φ [] = 1 :=
  rfl

@[simp]
theorem wordMap_cons {X I : Type*} [PseudoEMetricSpace X] (φ : I → X →ᵈ X)
    (i : I) (w : List I) :
    wordMap φ (i :: w) = φ i * wordMap φ w :=
  rfl

@[simp]
theorem wordMap_append {X I : Type*} [PseudoEMetricSpace X] (φ : I → X →ᵈ X)
    (u v : List I) :
    wordMap φ (u ++ v) = wordMap φ u * wordMap φ v := by
  induction u with
  | nil => simp
  | cons i u ih => simp [ih, mul_assoc]

@[simp]
theorem wordMap_apply_nil {X I : Type*} [PseudoEMetricSpace X] (φ : I → X →ᵈ X) (x : X) :
    wordMap φ [] x = x :=
  rfl

@[simp]
theorem wordMap_apply_cons {X I : Type*} [PseudoEMetricSpace X] (φ : I → X →ᵈ X)
    (i : I) (w : List I) (x : X) :
    wordMap φ (i :: w) x = φ i (wordMap φ w x) :=
  rfl

theorem wordMap_ratio_of_ratio {X I : Type*} [MetricSpace X] [Nontrivial X]
    (φ : I → X →ᵈ X) (q : ℝ≥0) (hφ : ∀ i, Dilation.ratio (φ i) = q) (w : List I) :
    Dilation.ratio (wordMap φ w) = q ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih => simp [hφ, ih, pow_succ']

theorem wordMap_surjective {X I : Type*} [EMetricSpace X] (φ : I → X →ᵈ X)
    (hφ : ∀ i, Function.Surjective (φ i)) (w : List I) :
    Function.Surjective (wordMap φ w) := by
  induction w with
  | nil => exact Function.surjective_id
  | cons i w ih => exact (hφ i).comp ih

theorem wordMap_mapsTo {X I : Type*} [PseudoEMetricSpace X] (φ : I → X →ᵈ X)
    {G : Set X} (hφ : ∀ i, MapsTo (φ i) G G) (w : List I) :
    MapsTo (wordMap φ w) G G := by
  induction w with
  | nil => simpa using mapsTo_id G
  | cons i w ih => exact (hφ i).comp ih

theorem Dilation.image_ball_of_surjective {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (g : X →ᵈ Y) (hg : Function.Surjective g) (x : X) (r : ℝ) :
    g '' ball x r = ball (g x) (Dilation.ratio g * r) := by
  apply Subset.antisymm
  · exact (Dilation.mapsTo_ball g x r).image_subset
  · intro y hy
    obtain ⟨z, rfl⟩ := hg y
    refine ⟨z, ?_, rfl⟩
    rw [mem_ball] at hy ⊢
    rw [Dilation.dist_eq] at hy
    have hratio : (0 : ℝ) < (Dilation.ratio g : ℝ) := by
      exact_mod_cast Dilation.ratio_pos g
    nlinarith

/-- The similarity exponent associated to `n` maps of common ratio `q`. -/
def similarityExponent (q : ℝ≥0) (n : ℕ) : ℝ :=
  -Real.log n / Real.log q

theorem similarityExponent_nonneg (q : ℝ≥0) (n : ℕ) (hn : 1 ≤ n)
    (hq : 0 < q) (hq1 : q < 1) :
    0 ≤ similarityExponent q n := by
  apply div_nonneg_of_nonpos
  · exact neg_nonpos.mpr (Real.log_nonneg (by exact_mod_cast hn))
  · exact (Real.log_neg (by exact_mod_cast hq) (by exact_mod_cast hq1)).le

theorem real_rpow_similarityExponent (q : ℝ≥0) (n : ℕ) (hn : 1 ≤ n)
    (hq : 0 < q) (hq1 : q < 1) :
    (q : ℝ) ^ similarityExponent q n = (n : ℝ)⁻¹ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlogq : Real.log (q : ℝ) ≠ 0 :=
    (Real.log_neg hqR (by exact_mod_cast hq1)).ne
  rw [similarityExponent, Real.rpow_def_of_pos hqR]
  have hmul :
      Real.log (q : ℝ) * (-Real.log (n : ℝ) / Real.log (q : ℝ)) =
        -Real.log (n : ℝ) := by
    field_simp
  rw [hmul, Real.exp_neg, Real.exp_log]
  exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)

theorem nnreal_rpow_similarityExponent (q : ℝ≥0) (n : ℕ) (hn : 1 ≤ n)
    (hq : 0 < q) (hq1 : q < 1) :
    q ^ similarityExponent q n = (n : ℝ≥0)⁻¹ := by
  apply NNReal.eq
  simpa using real_rpow_similarityExponent q n hn hq hq1

theorem ennreal_rpow_similarityExponent (q : ℝ≥0) (n : ℕ) (hn : 1 ≤ n)
    (hq : 0 < q) (hq1 : q < 1) :
    (q : ℝ≥0∞) ^ similarityExponent q n = (n : ℝ≥0∞)⁻¹ := by
  rw [← ENNReal.coe_rpow_of_ne_zero hq.ne', nnreal_rpow_similarityExponent q n hn hq hq1]
  rw [ENNReal.coe_inv]
  · norm_cast
  · exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))

/-- Data for a finite family of onto similarities with a common ratio, together
with a compact invariant set and an open set satisfying the open set condition. -/
structure UniformIFS (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) where
  q : ℝ≥0
  q_pos : 0 < q
  q_lt_one : q < 1
  φ : Fin n → X →ᵈ X
  ratio_φ : ∀ i, Dilation.ratio (φ i) = q
  surjective_φ : ∀ i, Function.Surjective (φ i)
  S : Set X
  S_compact : IsCompact S
  S_nonempty : S.Nonempty
  fixed : S = ⋃ i, φ i '' S
  G : Set X
  G_open : IsOpen G
  G_nonempty : G.Nonempty
  mapsTo_G : ∀ i, MapsTo (φ i) G G
  disjoint_G : ∀ i j, i ≠ j → Disjoint (φ i '' G) (φ j '' G)

namespace UniformIFS

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {n : ℕ} (F : UniformIFS X n)

/-- A level-`k` cylinder generated by a word `w`. -/
def cylinder {k : ℕ} (w : Fin k → Fin n) (T : Set X) : Set X :=
  wordMap F.φ (List.ofFn w) '' T

@[simp]
theorem cylinder_zero (w : Fin 0 → Fin n) (T : Set X) :
    F.cylinder w T = T := by
  simp [cylinder]

theorem cylinder_cons {k : ℕ} (i : Fin n) (w : Fin k → Fin n) (T : Set X) :
    F.cylinder (Fin.cons i w) T = F.φ i '' F.cylinder w T := by
  simp [cylinder, List.ofFn_succ, image_image]

theorem map_S (i : Fin n) : MapsTo (F.φ i) F.S F.S := by
  intro x hx
  rw [F.fixed]
  exact mem_iUnion.2 ⟨i, mem_image_of_mem _ hx⟩

theorem fixed_level (k : ℕ) :
    F.S = ⋃ w : Fin k → Fin n, F.cylinder w F.S := by
  induction k with
  | zero =>
      ext x
      constructor
      · intro hx
        exact mem_iUnion.2 ⟨fun i ↦ Fin.elim0 i, by simpa using hx⟩
      · rintro hx
        rcases mem_iUnion.1 hx with ⟨w, hw⟩
        simpa using hw
  | succ k ih =>
      conv_lhs => rw [F.fixed]
      ext x
      constructor
      · rintro hx
        rcases mem_iUnion.1 hx with ⟨i, y, hy, rfl⟩
        rw [ih] at hy
        rcases mem_iUnion.1 hy with ⟨w, hw⟩
        exact mem_iUnion.2 ⟨Fin.cons i w, by
          rw [F.cylinder_cons]
          exact mem_image_of_mem (F.φ i) hw⟩
      · rintro hx
        rcases mem_iUnion.1 hx with ⟨w, hw⟩
        have hw' : F.cylinder w F.S =
            F.φ (w 0) '' F.cylinder (Fin.tail w) F.S := by
          conv_lhs => rw [← Fin.cons_self_tail w]
          exact F.cylinder_cons (w 0) (Fin.tail w) F.S
        rw [hw'] at hw
        rcases hw with ⟨y, hy, rfl⟩
        have hyS : y ∈ F.S := by
          rw [ih]
          exact mem_iUnion.2 ⟨Fin.tail w, hy⟩
        exact mem_iUnion.2 ⟨w 0, mem_image_of_mem (F.φ (w 0)) hyS⟩

theorem ratio_word [Nontrivial X] {k : ℕ} (w : Fin k → Fin n) :
    Dilation.ratio (wordMap F.φ (List.ofFn w)) = F.q ^ k := by
  simpa using wordMap_ratio_of_ratio F.φ F.q F.ratio_φ (List.ofFn w)

theorem surjective_word {k : ℕ} (w : Fin k → Fin n) :
    Function.Surjective (wordMap F.φ (List.ofFn w)) :=
  wordMap_surjective F.φ F.surjective_φ (List.ofFn w)

theorem ediam_cylinder [Nontrivial X] {k : ℕ} (w : Fin k → Fin n) (T : Set X) :
    ediam (F.cylinder w T) = (F.q : ℝ≥0∞) ^ k * ediam T := by
  rw [cylinder, Dilation.ediam_image, F.ratio_word w]
  simp

theorem compact_cylinder {k : ℕ} (w : Fin k → Fin n) :
    IsCompact (F.cylinder w F.S) :=
  F.S_compact.image (Dilation.toContinuous _)

theorem nonempty_cylinder {k : ℕ} (w : Fin k → Fin n) :
    (F.cylinder w F.S).Nonempty :=
  F.S_nonempty.image _

theorem word_mapsTo_G {k : ℕ} (w : Fin k → Fin n) :
    MapsTo (wordMap F.φ (List.ofFn w)) F.G F.G :=
  wordMap_mapsTo F.φ F.mapsTo_G (List.ofFn w)

theorem disjoint_level_G {k : ℕ} {w v : Fin k → Fin n} (hwv : w ≠ v) :
    Disjoint (F.cylinder w F.G) (F.cylinder v F.G) := by
  induction k with
  | zero => exact (hwv (Subsingleton.elim _ _)).elim
  | succ k ih =>
      have hw : F.cylinder w F.G =
          F.φ (w 0) '' F.cylinder (Fin.tail w) F.G := by
        conv_lhs => rw [← Fin.cons_self_tail w]
        exact F.cylinder_cons (w 0) (Fin.tail w) F.G
      have hv : F.cylinder v F.G =
          F.φ (v 0) '' F.cylinder (Fin.tail v) F.G := by
        conv_lhs => rw [← Fin.cons_self_tail v]
        exact F.cylinder_cons (v 0) (Fin.tail v) F.G
      rw [hw, hv]
      by_cases hhead : w 0 = v 0
      · rw [hhead]
        apply Set.disjoint_image_of_injective (Dilation.injective _)
        apply ih
        intro htail
        apply hwv
        rw [← Fin.cons_self_tail w, ← Fin.cons_self_tail v, hhead, htail]
      · refine (F.disjoint_G (w 0) (v 0) hhead).mono ?_ ?_
        · exact image_mono (F.word_mapsTo_G (Fin.tail w)).image_subset
        · exact image_mono (F.word_mapsTo_G (Fin.tail v)).image_subset

/-- The cylinder determined by the first `k` letters of an infinite word. -/
def prefixCylinder (a : ℕ → Fin n) (k : ℕ) : Set X :=
  F.cylinder (fun i : Fin k ↦ a i) F.S

theorem prefix_succ_subset (a : ℕ → Fin n) (k : ℕ) :
    F.prefixCylinder a (k + 1) ⊆ F.prefixCylinder a k := by
  rintro x ⟨s, hs, rfl⟩
  refine ⟨F.φ (a k) s, F.map_S (a k) hs, ?_⟩
  rw [List.ofFn_succ', List.concat_eq_append, wordMap_append]
  simp

theorem compact_prefix (a : ℕ → Fin n) (k : ℕ) :
    IsCompact (F.prefixCylinder a k) :=
  F.compact_cylinder _

theorem nonempty_prefix (a : ℕ → Fin n) (k : ℕ) :
    (F.prefixCylinder a k).Nonempty :=
  F.nonempty_cylinder _

theorem prefix_iInter_nonempty (a : ℕ → Fin n) :
    (⋂ k, F.prefixCylinder a k).Nonempty :=
  (F.compact_prefix a 0).nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (F.prefixCylinder a) (F.prefix_succ_subset a) (F.nonempty_prefix a)
    fun k ↦ (F.compact_prefix a k).isClosed

/-- The point coded by an infinite word, obtained from nested compact cylinders. -/
def code (a : ℕ → Fin n) : X :=
  Classical.choose (F.prefix_iInter_nonempty a)

theorem code_mem_prefix (a : ℕ → Fin n) (k : ℕ) :
    F.code a ∈ F.prefixCylinder a k :=
  Set.mem_iInter.mp (Classical.choose_spec (F.prefix_iInter_nonempty a)) k

theorem code_mem_S (a : ℕ → Fin n) : F.code a ∈ F.S := by
  simpa [prefixCylinder] using F.code_mem_prefix a 0

theorem diam_prefix [Nontrivial X] (a : ℕ → Fin n) (k : ℕ) :
    diam (F.prefixCylinder a k) = (F.q : ℝ) ^ k * diam F.S := by
  rw [prefixCylinder, cylinder, Dilation.diam_image, F.ratio_word]
  simp

theorem continuous_code [Nontrivial X] : Continuous F.code := by
  rw [Metric.continuous_iff']
  intro a ε hε
  by_cases hD : diam F.S = 0
  · filter_upwards [] with b
    have hdist := Metric.dist_le_diam_of_mem F.S_compact.isBounded
      (F.code_mem_S b) (F.code_mem_S a)
    exact (hdist.trans_eq hD).trans_lt hε
  · have hDpos : 0 < diam F.S := lt_of_le_of_ne diam_nonneg (Ne.symm hD)
    have hq1 : (F.q : ℝ) < 1 := by exact_mod_cast F.q_lt_one
    obtain ⟨k, hk⟩ :=
      exists_pow_lt_of_lt_one (div_pos hε hDpos) hq1
    let U : Set (ℕ → Fin n) :=
      (Finset.range k : Set ℕ).pi fun i ↦ {a i}
    have hU : U ∈ 𝓝 a := set_pi_mem_nhds (Finset.finite_toSet _) fun i _ ↦
      (isOpen_discrete {a i}).mem_nhds (by simp)
    filter_upwards [hU] with b hb
    have hp : (fun i : Fin k ↦ b i) = fun i : Fin k ↦ a i := by
      funext i
      simpa [U] using hb i (Finset.mem_range.mpr i.isLt)
    have hb' : F.code b ∈ F.prefixCylinder a k := by
      simpa [prefixCylinder, hp] using F.code_mem_prefix b k
    have hdist := Metric.dist_le_diam_of_mem (F.compact_prefix a k).isBounded
      hb' (F.code_mem_prefix a k)
    rw [F.diam_prefix a k] at hdist
    exact hdist.trans_lt ((lt_div_iff₀ hDpos).mp hk)

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem measurable_code [Nontrivial X] : Measurable F.code :=
  F.continuous_code.measurable

/-- Uniform measure on the alphabet of the IFS. -/
def letterMeasure (n : ℕ) : Measure (Fin n) :=
  ProbabilityTheory.uniformOn Set.univ

local instance letterMeasure_isProbabilityMeasure (n : ℕ) [Nonempty (Fin n)] :
    IsProbabilityMeasure (letterMeasure n) := by
  unfold letterMeasure
  infer_instance

/-- Bernoulli measure on infinite words. -/
def sequenceMeasure (n : ℕ) : Measure (ℕ → Fin n) :=
  Measure.infinitePi fun _ ↦ letterMeasure n

local instance sequenceMeasure_isProbabilityMeasure (n : ℕ) [Nonempty (Fin n)] :
    IsProbabilityMeasure (sequenceMeasure n) := by
  unfold sequenceMeasure
  infer_instance

/-- The self-similar probability measure obtained by pushing Bernoulli measure
through the coding map. -/
def naturalMeasure : Measure X :=
  (sequenceMeasure n).map F.code

/-- The symbolic cylinder prescribing the first `k` letters. -/
def symbolicCylinder {k : ℕ} (w : Fin k → Fin n) : Set (ℕ → Fin n) :=
  (Finset.range k : Set ℕ).pi fun j ↦
    if hj : j < k then {w ⟨j, hj⟩} else Set.univ

theorem mem_symbolicCylinder {k : ℕ} {w : Fin k → Fin n} {a : ℕ → Fin n} :
    a ∈ symbolicCylinder w ↔ ∀ i : Fin k, a i = w i := by
  constructor
  · intro ha i
    simpa [symbolicCylinder, i.isLt] using
      ha i (Finset.mem_range.mpr i.isLt)
  · intro ha j hj
    have hj' : j < k := Finset.mem_range.mp hj
    simpa [symbolicCylinder, hj'] using ha ⟨j, hj'⟩

theorem sequenceMeasure_symbolicCylinder (hn : 1 ≤ n) {k : ℕ}
    (w : Fin k → Fin n) :
    sequenceMeasure n (symbolicCylinder w) = ((n : ℝ≥0∞)⁻¹) ^ k := by
  letI : Nonempty (Fin n) :=
    Fin.pos_iff_nonempty.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [sequenceMeasure, symbolicCylinder, Measure.infinitePi_pi]
  · calc
      _ = ∏ _x ∈ Finset.range k, ((n : ℝ≥0∞)⁻¹) := by
        apply Finset.prod_congr rfl
        intro x hx
        have hxk : x < k := Finset.mem_range.mp hx
        simp [letterMeasure, ProbabilityTheory.uniformOn_univ, hxk]
      _ = ((n : ℝ≥0∞)⁻¹) ^ k := by simp
  · intro j hj
    split_ifs
    · exact MeasurableSet.singleton _
    · exact MeasurableSet.univ

/-- Level-`k` words whose geometric cylinders meet `T`. -/
def meetingWords (k : ℕ) (T : Set X) : Finset (Fin k → Fin n) := by
  classical
  exact Finset.univ.filter fun w ↦ (F.cylinder w F.S ∩ T).Nonempty

theorem code_preimage_subset_meetingWords (k : ℕ) (T : Set X) :
    F.code ⁻¹' T ⊆ ⋃ w ∈ F.meetingWords k T, symbolicCylinder w := by
  intro a ha
  let w : Fin k → Fin n := fun i ↦ a i
  have hw : w ∈ F.meetingWords k T := by
    simp only [meetingWords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨F.code a, F.code_mem_prefix a k, ha⟩
  refine Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨hw, ?_⟩⟩
  exact mem_symbolicCylinder.2 fun _ ↦ rfl

theorem sequenceMeasure_code_preimage_le (hn : 1 ≤ n) (k : ℕ) (T : Set X) :
    sequenceMeasure n (F.code ⁻¹' T) ≤
      (F.meetingWords k T).card * ((n : ℝ≥0∞)⁻¹) ^ k := by
  calc
    sequenceMeasure n (F.code ⁻¹' T) ≤
        sequenceMeasure n (⋃ w ∈ F.meetingWords k T, symbolicCylinder w) :=
      measure_mono (F.code_preimage_subset_meetingWords k T)
    _ ≤ ∑ w ∈ F.meetingWords k T, sequenceMeasure n (symbolicCylinder w) :=
      measure_biUnion_finset_le _ _
    _ = (F.meetingWords k T).card * ((n : ℝ≥0∞)⁻¹) ^ k := by
      simp [sequenceMeasure_symbolicCylinder hn, nsmul_eq_mul]

theorem naturalMeasure_apply_le [Nontrivial X] (hn : 1 ≤ n) (k : ℕ) {T : Set X}
    (hT : MeasurableSet T) :
    F.naturalMeasure T ≤
      (F.meetingWords k T).card * ((n : ℝ≥0∞)⁻¹) ^ k := by
  rw [naturalMeasure, Measure.map_apply F.measurable_code hT]
  exact F.sequenceMeasure_code_preimage_le hn k T

theorem naturalMeasure_S [Nontrivial X] (hn : 1 ≤ n) : F.naturalMeasure F.S = 1 := by
  letI : Nonempty (Fin n) :=
    Fin.pos_iff_nonempty.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [naturalMeasure, Measure.map_apply F.measurable_code F.S_compact.measurableSet]
  have hpre : F.code ⁻¹' F.S = Set.univ := by
    ext a
    simp [F.code_mem_S]
  rw [hpre, measure_univ]

/-- The open set condition gives a uniform bound on the number of level
cylinders which can meet a set of diameter at most the cylinder scale. -/
theorem exists_meetingWords_card_le [FiniteDimensional ℝ X] [Nontrivial X] :
    ∃ N : ℕ, ∀ (k : ℕ) (T : Set X), T.Nonempty → IsBounded T →
      diam T ≤ (F.q : ℝ) ^ k → (F.meetingWords k T).card ≤ N := by
  classical
  obtain ⟨a, ha⟩ := F.G_nonempty
  obtain ⟨rho, hrho, hball⟩ := (Metric.isOpen_iff.mp F.G_open) a ha
  obtain ⟨R0, hR0⟩ := F.S_compact.isBounded.subset_closedBall a
  let R : ℝ := max R0 0
  have hSR : F.S ⊆ closedBall a R :=
    hR0.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨C, _, hCfinite, hCcover⟩ :=
    (isCompact_closedBall (0 : X) (R + 1)).finite_cover_balls hrho
  let Cfin : Finset X := hCfinite.toFinset
  refine ⟨Cfin.card, fun k T hTne hTb hTdiam ↦ ?_⟩
  let qk : ℝ := (F.q : ℝ) ^ k
  have hq : (0 : ℝ) < F.q := by exact_mod_cast F.q_pos
  have hqk : 0 < qk := pow_pos hq _
  obtain ⟨u, hu⟩ := hTne
  let W := {w // w ∈ F.meetingWords k T}
  have hmeet (w : W) : (F.cylinder w.1 F.S ∩ T).Nonempty :=
    (Finset.mem_filter.mp w.2).2
  let y : W → X := fun w ↦ Classical.choose (hmeet w)
  have hy (w : W) : y w ∈ F.cylinder w.1 F.S ∩ T :=
    Classical.choose_spec (hmeet w)
  let source : W → X := fun w ↦ Classical.choose (hy w).1
  have hsource (w : W) :
      source w ∈ F.S ∧
        wordMap F.φ (List.ofFn w.1) (source w) = y w :=
    Classical.choose_spec (hy w).1
  let z : W → X := fun w ↦ wordMap F.φ (List.ofFn w.1) a
  let p : W → X := fun w ↦ qk⁻¹ • (z w - u)
  have hzy (w : W) : dist (z w) (y w) = qk * dist a (source w) := by
    change
      dist (wordMap F.φ (List.ofFn w.1) a) (y w) =
        (F.q : ℝ) ^ k * dist a (source w)
    rw [← (hsource w).2, Dilation.dist_eq, F.ratio_word]
    rfl
  have hp_closed (w : W) : p w ∈ closedBall (0 : X) (R + 1) := by
    have has : dist a (source w) ≤ R := by
      simpa [mem_closedBall, dist_comm] using hSR (hsource w).1
    have hyu : dist (y w) u ≤ diam T :=
      Metric.dist_le_diam_of_mem hTb (hy w).2 hu
    have hzu : dist (z w) u ≤ qk * (R + 1) := by
      calc
        dist (z w) u ≤ dist (z w) (y w) + dist (y w) u := dist_triangle _ _ _
        _ ≤ qk * R + qk :=
          add_le_add (by rw [hzy]; exact mul_le_mul_of_nonneg_left has hqk.le)
            (hyu.trans hTdiam)
        _ = qk * (R + 1) := by ring
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖p w‖ = qk⁻¹ * dist (z w) u := by
        change ‖qk⁻¹ • (z w - u)‖ = qk⁻¹ * dist (z w) u
        rw [norm_smul_of_nonneg (inv_nonneg.mpr hqk.le), dist_eq_norm]
      _ ≤ qk⁻¹ * (qk * (R + 1)) :=
        mul_le_mul_of_nonneg_left hzu (inv_nonneg.mpr hqk.le)
      _ = R + 1 := by field_simp
  have hpcover (w : W) : ∃ c ∈ C, p w ∈ ball c rho := by
    rcases Set.mem_iUnion.1 (hCcover (hp_closed w)) with ⟨c, hc⟩
    rcases Set.mem_iUnion.1 hc with ⟨hcC, hp⟩
    exact ⟨c, hcC, hp⟩
  let c : W → X := fun w ↦ Classical.choose (hpcover w)
  have hc (w : W) : c w ∈ C ∧ p w ∈ ball (c w) rho :=
    Classical.choose_spec (hpcover w)
  let pick : W → {x // x ∈ Cfin} := fun w ↦
    ⟨c w, by simpa [Cfin] using (hc w).1⟩
  have hsep (w v : W) (hwv : w ≠ v) :
      2 * rho ≤ dist (p w) (p v) := by
    have hwv' : w.1 ≠ v.1 := fun h ↦ hwv (Subtype.ext h)
    have hballw : ball (z w) (qk * rho) ⊆ F.cylinder w.1 F.G := by
      calc
        ball (z w) (qk * rho) =
            wordMap F.φ (List.ofFn w.1) '' ball a rho := by
          rw [Dilation.image_ball_of_surjective _ (F.surjective_word w.1)]
          simp [z, qk, F.ratio_word]
        _ ⊆ wordMap F.φ (List.ofFn w.1) '' F.G := image_mono hball
        _ = F.cylinder w.1 F.G := rfl
    have hballv : ball (z v) (qk * rho) ⊆ F.cylinder v.1 F.G := by
      calc
        ball (z v) (qk * rho) =
            wordMap F.φ (List.ofFn v.1) '' ball a rho := by
          rw [Dilation.image_ball_of_surjective _ (F.surjective_word v.1)]
          simp [z, qk, F.ratio_word]
        _ ⊆ wordMap F.φ (List.ofFn v.1) '' F.G := image_mono hball
        _ = F.cylinder v.1 F.G := rfl
    have hdisj : Disjoint (ball (z w) (qk * rho)) (ball (z v) (qk * rho)) :=
      (F.disjoint_level_G hwv').mono hballw hballv
    have hzsep : qk * rho + qk * rho ≤ dist (z w) (z v) :=
      (disjoint_ball_ball_iff (mul_pos hqk hrho) (mul_pos hqk hrho)).mp hdisj
    have hpdist : dist (p w) (p v) = qk⁻¹ * dist (z w) (z v) := by
      change
        dist (qk⁻¹ • (z w - u)) (qk⁻¹ • (z v - u)) =
          qk⁻¹ * dist (z w) (z v)
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hqk)]
      simp
    rw [hpdist]
    calc
      2 * rho = qk⁻¹ * (qk * rho + qk * rho) := by field_simp; ring
      _ ≤ qk⁻¹ * dist (z w) (z v) :=
        mul_le_mul_of_nonneg_left hzsep (inv_nonneg.mpr hqk.le)
  have hpick : Function.Injective pick := by
    intro w v hpickwv
    by_contra hwv
    have hcwv : c w = c v := congrArg Subtype.val hpickwv
    have hlt : dist (p w) (p v) < 2 * rho := by
      calc
        dist (p w) (p v) ≤ dist (p w) (c w) + dist (c w) (p v) :=
          dist_triangle _ _ _
        _ < rho + rho := by
          exact add_lt_add (hc w).2 (by simpa [hcwv, dist_comm] using (hc v).2)
        _ = 2 * rho := by ring
    exact (not_le_of_gt hlt) (hsep w v hwv)
  have hcard := Fintype.card_le_of_injective pick hpick
  simp only [W, Fintype.card_coe] at hcard
  exact hcard

/-- Frostman's power bound for the natural self-similar measure. -/
theorem exists_naturalMeasure_le_rpow [FiniteDimensional ℝ X] [Nontrivial X]
    (hn : 2 ≤ n) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ U : Set X, ediam U ≤ 1 →
        F.naturalMeasure U ≤ C * ediam U ^ similarityExponent F.q n := by
  classical
  obtain ⟨N, hN⟩ := F.exists_meetingWords_card_le
  let s := similarityExponent F.q n
  let qE : ℝ≥0∞ := F.q
  let C : ℝ≥0∞ := (N : ℝ≥0∞) * (qE⁻¹) ^ s + 1
  have hn1 : 1 ≤ n := hn.trans' (by omega)
  have hs : 0 ≤ s :=
    similarityExponent_nonneg F.q n hn1 F.q_pos F.q_lt_one
  have hqE0 : qE ≠ 0 := by simp [qE, F.q_pos.ne']
  have hqETop : qE ≠ ⊤ := by simp [qE]
  have hqs : qE ^ s = (n : ℝ≥0∞)⁻¹ := by
    simpa [qE, s] using
      ennreal_rpow_similarityExponent F.q n hn1 F.q_pos F.q_lt_one
  have hninv : (n : ℝ≥0∞)⁻¹ < 1 := by
    apply ENNReal.inv_lt_one.mpr
    exact_mod_cast hn
  have hC0 : C ≠ 0 := by simp [C]
  have hCTop : C ≠ ⊤ := by
    apply ENNReal.add_ne_top.2
    refine ⟨ENNReal.mul_ne_top (by simp) ?_, ENNReal.one_ne_top⟩
    exact ENNReal.rpow_ne_top_of_nonneg hs (ENNReal.inv_ne_top.mpr hqE0)
  refine ⟨C, hC0, hCTop, fun U hU ↦ ?_⟩
  by_cases hUne : U.Nonempty
  · let V := closure U
    have hVne : V.Nonempty := hUne.mono subset_closure
    have hEtop : ediam U ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hU
    have hVb : IsBounded V := by
      rw [Metric.isBounded_iff_ediam_ne_top, Metric.ediam_closure]
      exact hEtop
    have hmono : F.naturalMeasure U ≤ F.naturalMeasure V :=
      measure_mono subset_closure
    by_cases hE0 : ediam U = 0
    · have hzero : F.naturalMeasure U = 0 := by
        apply ENNReal.eq_zero_of_le_mul_pow (ε := (N : ℝ≥0)) hninv
        intro k
        have hcard : (F.meetingWords k V).card ≤ N := by
          apply hN k V hVne hVb
          simp [V, Metric.diam, Metric.ediam_closure, hE0]
        calc
          F.naturalMeasure U ≤ F.naturalMeasure V := hmono
          _ ≤ (F.meetingWords k V).card * ((n : ℝ≥0∞)⁻¹) ^ k :=
            F.naturalMeasure_apply_le hn1 k isClosed_closure.measurableSet
          _ ≤ N * ((n : ℝ≥0∞)⁻¹) ^ k := by
            exact mul_le_mul_left (by exact_mod_cast hcard) _
      simp [hzero, hE0]
    · have hEpos : 0 < (ediam U).toReal :=
        ENNReal.toReal_pos hE0 hEtop
      have hEle : (ediam U).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top hU
      have hqR : (0 : ℝ) < F.q := by exact_mod_cast F.q_pos
      have hqR1 : (F.q : ℝ) < 1 := by exact_mod_cast F.q_lt_one
      obtain ⟨k, hklow, hkhigh⟩ :=
        exists_nat_pow_near_of_lt_one hEpos hEle hqR hqR1
      have hVdiam : diam V ≤ (F.q : ℝ) ^ k := by
        simpa [V, Metric.diam, Metric.ediam_closure] using hkhigh
      have hcard : (F.meetingWords k V).card ≤ N :=
        hN k V hVne hVb hVdiam
      have hqstep : qE ^ (k + 1) ≤ ediam U := by
        rw [← ENNReal.toReal_le_toReal (by simp [qE]) hEtop]
        simpa [qE] using hklow.le
      have hqscale : qE ^ k ≤ qE⁻¹ * ediam U := by
        calc
          qE ^ k = qE⁻¹ * qE ^ (k + 1) := by
            rw [pow_succ]
            calc
              qE ^ k = 1 * qE ^ k := by simp
              _ = (qE⁻¹ * qE) * qE ^ k := by
                rw [ENNReal.inv_mul_cancel hqE0 hqETop]
              _ = qE⁻¹ * (qE ^ k * qE) := by ac_rfl
          _ ≤ qE⁻¹ * ediam U := mul_le_mul_right hqstep _
      have hpow :
          ((n : ℝ≥0∞)⁻¹) ^ k = (qE ^ k) ^ s := by
        rw [← hqs, ← ENNReal.rpow_natCast_mul, mul_comm,
          ENNReal.rpow_mul_natCast]
      calc
        F.naturalMeasure U ≤ F.naturalMeasure V := hmono
        _ ≤ (F.meetingWords k V).card * ((n : ℝ≥0∞)⁻¹) ^ k :=
          F.naturalMeasure_apply_le hn1 k isClosed_closure.measurableSet
        _ ≤ N * ((n : ℝ≥0∞)⁻¹) ^ k := by
          exact mul_le_mul_left (by exact_mod_cast hcard) _
        _ = N * (qE ^ k) ^ s := by rw [hpow]
        _ ≤ N * (qE⁻¹ * ediam U) ^ s := by
          exact mul_le_mul_right (ENNReal.rpow_le_rpow hqscale hs) _
        _ = ((N : ℝ≥0∞) * (qE⁻¹) ^ s) * ediam U ^ s := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hs]
          ac_rfl
        _ ≤ C * ediam U ^ s := by
          exact mul_le_mul_left (le_add_right le_rfl) _
  · have hUempty : U = ∅ := not_nonempty_iff_eq_empty.mp hUne
    simp [hUempty]

theorem hausdorffMeasure_similarityExponent_le [Nontrivial X] (hn : 1 ≤ n) :
    μH[similarityExponent F.q n] F.S ≤
      ediam F.S ^ similarityExponent F.q n := by
  let s := similarityExponent F.q n
  let r : ℕ → ℝ≥0∞ := fun k ↦ (F.q : ℝ≥0∞) ^ k * ediam F.S
  let t : (k : ℕ) → (Fin k → Fin n) → Set X :=
    fun _ w ↦ F.cylinder w F.S
  have hqE : (F.q : ℝ≥0∞) < 1 := by exact_mod_cast F.q_lt_one
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa [r] using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hqE)
      (Or.inr F.S_compact.isBounded.ediam_ne_top)
  have ht : ∀ᶠ k in atTop, ∀ w, ediam (t k w) ≤ r k := by
    filter_upwards [] with k w
    exact le_of_eq (F.ediam_cylinder w F.S)
  have hcover : ∀ᶠ k in atTop, F.S ⊆ ⋃ w, t k w := by
    filter_upwards [] with k
    exact le_of_eq (F.fixed_level k)
  refine (MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum s F.S r hr t ht hcover).trans_eq ?_
  have hs : 0 ≤ s :=
    similarityExponent_nonneg F.q n hn F.q_pos F.q_lt_one
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn))
  have hnTop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hqs :
      (F.q : ℝ≥0∞) ^ s = (n : ℝ≥0∞)⁻¹ :=
    ennreal_rpow_similarityExponent F.q n hn F.q_pos F.q_lt_one
  have hsum :
      (fun k ↦ ∑ w : Fin k → Fin n, ediam (t k w) ^ s) =
        fun _ ↦ ediam F.S ^ s := by
    funext k
    have hpow :
        (((F.q : ℝ≥0∞) ^ k) ^ s) = ((n : ℝ≥0∞)⁻¹) ^ k := by
      rw [← ENNReal.rpow_natCast_mul, mul_comm, ENNReal.rpow_mul_natCast, hqs]
    simp only [t, F.ediam_cylinder, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hs, hpow]
    rw [Nat.cast_pow, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hn0 hnTop,
      one_pow, one_mul]
  rw [hsum, liminf_const]

theorem hausdorffMeasure_similarityExponent_ne_top [Nontrivial X] (hn : 1 ≤ n) :
    μH[similarityExponent F.q n] F.S ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (F.hausdorffMeasure_similarityExponent_le hn)
  exact ENNReal.rpow_ne_top_of_nonneg
    (similarityExponent_nonneg F.q n hn F.q_pos F.q_lt_one)
    F.S_compact.isBounded.ediam_ne_top

theorem hausdorffMeasure_similarityExponent_ne_zero [FiniteDimensional ℝ X] [Nontrivial X]
    (hn : 2 ≤ n) :
    μH[similarityExponent F.q n] F.S ≠ 0 := by
  obtain ⟨C, hC0, hCTop, hC⟩ := F.exists_naturalMeasure_le_rpow hn
  have hn1 : 1 ≤ n := by omega
  let ν : Measure X := C⁻¹ • F.naturalMeasure
  have hν : ν ≤ μH[similarityExponent F.q n] := by
    apply MeasureTheory.Measure.le_hausdorffMeasure
      (similarityExponent F.q n) ν 1 zero_lt_one
    intro U hU
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    calc
      C⁻¹ * F.naturalMeasure U ≤
          C⁻¹ * (C * ediam U ^ similarityExponent F.q n) :=
        mul_le_mul_right (hC U hU) _
      _ = ediam U ^ similarityExponent F.q n := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCTop, one_mul]
  intro hzero
  have hνS : ν F.S = 0 := by
    apply nonpos_iff_eq_zero.mp
    simpa [hzero] using hν F.S
  have hνS' : ν F.S = C⁻¹ := by
    simp [ν, F.naturalMeasure_S hn1]
  rw [hνS'] at hνS
  exact (ENNReal.inv_ne_zero.mpr hCTop) hνS

theorem dimH_eq_similarityExponent [FiniteDimensional ℝ X] [Nontrivial X] (hn : 1 ≤ n) :
    dimH F.S = ENNReal.ofReal (similarityExponent F.q n) := by
  rcases hn.eq_or_lt with rfl | hn'
  · have hsingle : F.S.Subsingleton := by
      have hfixed : F.S = F.φ 0 '' F.S := by
        conv_lhs => rw [F.fixed]
        ext x
        simp only [mem_iUnion]
        constructor
        · rintro ⟨i, hi⟩
          simpa [Subsingleton.elim i 0] using hi
        · intro hx
          exact ⟨0, hx⟩
      have hdiam : diam F.S = (F.q : ℝ) * diam F.S := by
        conv_lhs => rw [hfixed, Dilation.diam_image, F.ratio_φ]
      have hq : (F.q : ℝ) < 1 := by exact_mod_cast F.q_lt_one
      have hdiam0 : diam F.S = 0 := by
        nlinarith [diam_nonneg (s := F.S)]
      intro x hx y hy
      apply dist_le_zero.mp
      simpa [hdiam0] using
        Metric.dist_le_diam_of_mem F.S_compact.isBounded hx hy
    simpa [similarityExponent] using hsingle.dimH_zero
  · have hn2 : 2 ≤ n := by omega
    let d0 : ℝ≥0 :=
      ⟨similarityExponent F.q n,
        similarityExponent_nonneg F.q n hn F.q_pos F.q_lt_one⟩
    have hzero : μH[(d0 : ℝ)] F.S ≠ 0 := by
      change μH[similarityExponent F.q n] F.S ≠ 0
      exact F.hausdorffMeasure_similarityExponent_ne_zero hn2
    have htop : μH[(d0 : ℝ)] F.S ≠ ⊤ := by
      change μH[similarityExponent F.q n] F.S ≠ ⊤
      exact F.hausdorffMeasure_similarityExponent_ne_top hn
    have hd := dimH_of_hausdorffMeasure_ne_zero_ne_top hzero htop
    rw [ENNReal.ofReal_eq_coe_nnreal
      (similarityExponent_nonneg F.q n hn F.q_pos F.q_lt_one)]
    exact hd

end UniformIFS

end

end Submission.Helpers
