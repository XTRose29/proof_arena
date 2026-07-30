import Submission.PartitionWeights

open Set Metric
open scoped Topology

namespace Submission.LipschitzWeights

open Helpers FragmentationConstruction PartitionWeights GridDeformation

variable {ι X : Type*} [MetricSpace X] [CompactSpace X]

/-- Distance to the complement of an open set, with the value `1` when
the complement is empty. -/
noncomputable def boundaryDistance (V : Set X) (x : X) : ℝ :=
  by
    classical
    exact if h : Vᶜ.Nonempty then min 1 (infDist x Vᶜ) else 1

omit [CompactSpace X] in
theorem boundaryDistance_nonneg (V : Set X) (x : X) :
    0 ≤ boundaryDistance V x := by
  classical
  rw [boundaryDistance]
  split_ifs with h
  · exact le_min zero_le_one infDist_nonneg
  · exact zero_le_one

omit [CompactSpace X] in
theorem boundaryDistance_le_one (V : Set X) (x : X) :
    boundaryDistance V x ≤ 1 := by
  classical
  rw [boundaryDistance]
  split_ifs <;> simp

omit [CompactSpace X] in
theorem lipschitz_boundaryDistance (V : Set X) :
    LipschitzWith 1 (boundaryDistance V) := by
  classical
  unfold boundaryDistance
  split_ifs with h
  · exact (lipschitz_infDist_pt Vᶜ).const_min 1
  · exact (LipschitzWith.const (α := X) 1).weaken zero_le_one

omit [CompactSpace X] in
theorem boundaryDistance_eq_zero_of_not_mem (V : Set X) {x : X}
    (hx : x ∉ V) : boundaryDistance V x = 0 := by
  classical
  rw [boundaryDistance, dif_pos ⟨x, hx⟩]
  have hxcompl : x ∈ Vᶜ := hx
  rw [infDist_zero_of_mem hxcompl]
  simp

omit [CompactSpace X] in
theorem boundaryDistance_pos_of_mem (V : Set X) (hV : IsOpen V)
    {x : X} (hx : x ∈ V) : 0 < boundaryDistance V x := by
  classical
  rw [boundaryDistance]
  split_ifs with hcomp
  · have hxcomp : x ∉ Vᶜ := fun hxC => hxC hx
    have hdist : 0 < infDist x Vᶜ :=
      (hV.isClosed_compl.notMem_iff_infDist_pos hcomp).mp hxcomp
    exact lt_min zero_lt_one hdist
  · exact zero_lt_one

structure CoverData (ι X : Type*) [MetricSpace X] [CompactSpace X] where
  U : ι → Set X
  isOpen : ∀ i, IsOpen (U i)
  rho : PartitionOfUnity ι X univ
  subordinate : rho.IsSubordinate U

variable (D : CoverData ι X)

noncomputable def m : ℕ := (activeIndices D.rho).card

noncomputable def label (j : Fin (m D)) : ι :=
  ((activeIndices D.rho).equivFin.symm j).1

theorem label_mem_activeIndices (j : Fin (m D)) :
    label D j ∈ activeIndices D.rho :=
  ((activeIndices D.rho).equivFin.symm j).2

theorem activeLabel_cover [Nonempty X] (x : X) :
    ∃ j : Fin (m D), x ∈ D.U (label D j) := by
  have hx : x ∈ ⋃ i ∈ activeIndices D.rho, D.U i := by
    rw [activeIndices_cover D.rho D.subordinate]
    exact mem_univ x
  rw [mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  rw [mem_iUnion] at hi
  obtain ⟨hiA, hxi⟩ := hi
  let a : activeIndices D.rho := ⟨i, hiA⟩
  refine ⟨(activeIndices D.rho).equivFin a, ?_⟩
  simpa [label, a] using hxi

noncomputable def distanceSum (x : X) : ℝ :=
  ∑ j : Fin (m D), boundaryDistance (D.U (label D j)) x

theorem continuous_distanceSum : Continuous (distanceSum D) := by
  unfold distanceSum
  apply continuous_finsetSum
  intro j _hj
  exact (lipschitz_boundaryDistance (D.U (label D j))).continuous

theorem distanceSum_pos [Nonempty X] (x : X) : 0 < distanceSum D x := by
  obtain ⟨j, hxj⟩ := activeLabel_cover D x
  have hjpos := boundaryDistance_pos_of_mem (D.U (label D j))
    (D.isOpen (label D j)) hxj
  exact lt_of_lt_of_le hjpos <| Finset.single_le_sum
    (fun i _hi => boundaryDistance_nonneg (D.U (label D i)) x) (Finset.mem_univ j)

theorem exists_uniform_delta [Nonempty X] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, δ ≤ distanceSum D x := by
  obtain ⟨δ, hδ, hbound⟩ := isCompact_univ.exists_forall_le'
    (continuous_distanceSum D).continuousOn
    (fun x _hx => distanceSum_pos D x)
  exact ⟨δ, hδ, fun x => hbound x (mem_univ x)⟩

noncomputable def uniformDelta [Nonempty X] (D : CoverData ι X) : ℝ :=
  Classical.choose (exists_uniform_delta D)

theorem uniformDelta_pos [Nonempty X] : 0 < uniformDelta D :=
  (Classical.choose_spec (exists_uniform_delta D)).1

theorem uniformDelta_le [Nonempty X] (x : X) :
    uniformDelta D ≤ distanceSum D x :=
  (Classical.choose_spec (exists_uniform_delta D)).2 x

theorem m_pos [Nonempty X] : 0 < m D := by
  let W := ofPartitionOfUnity D.U D.rho D.subordinate
  exact W.positive_card

noncomputable def epsilon [Nonempty X] (D : CoverData ι X) : ℝ :=
  uniformDelta D / m D

theorem epsilon_pos [Nonempty X] : 0 < epsilon D := by
  exact div_pos (uniformDelta_pos D) (by exact_mod_cast m_pos D)

noncomputable def cutoff [Nonempty X] (D : CoverData ι X)
    (j : Fin (m D)) (x : X) : ℝ :=
  min 1 (boundaryDistance (D.U (label D j)) x / epsilon D)

theorem cutoff_nonneg [Nonempty X] (j : Fin (m D)) (x : X) :
    0 ≤ cutoff D j x := by
  exact le_min zero_le_one <|
    div_nonneg (boundaryDistance_nonneg _ _) (epsilon_pos D).le

theorem cutoff_le_one [Nonempty X] (j : Fin (m D)) (x : X) :
    cutoff D j x ≤ 1 :=
  min_le_left _ _

theorem cutoff_eq_zero_of_not_mem [Nonempty X] (j : Fin (m D)) {x : X}
    (hx : x ∉ D.U (label D j)) : cutoff D j x = 0 := by
  rw [cutoff, boundaryDistance_eq_zero_of_not_mem _ hx, zero_div, min_eq_right]
  exact zero_le_one

theorem lipschitz_cutoff [Nonempty X] (j : Fin (m D)) :
    ∃ K : NNReal, LipschitzWith K (cutoff D j) := by
  let e := epsilon D
  let K : NNReal := ‖e⁻¹‖₊
  have hscaled' : LipschitzWith K fun x : X =>
      e⁻¹ * boundaryDistance (D.U (label D j)) x := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (e⁻¹ * boundaryDistance (D.U (label D j)) x)
          (e⁻¹ * boundaryDistance (D.U (label D j)) y) ≤
          ‖e⁻¹‖ * dist (boundaryDistance (D.U (label D j)) x)
            (boundaryDistance (D.U (label D j)) y) := by
        simpa only [smul_eq_mul] using dist_smul_le (e⁻¹ : ℝ)
          (boundaryDistance (D.U (label D j)) x)
          (boundaryDistance (D.U (label D j)) y)
      _ ≤ ‖e⁻¹‖ * dist x y := by
        gcongr
        simpa using (lipschitz_boundaryDistance (D.U (label D j))).dist_le_mul x y
      _ = (K : ℝ) * dist x y := rfl
  have hscaled : LipschitzWith K fun x : X =>
      boundaryDistance (D.U (label D j)) x / e := by
    simpa only [div_eq_mul_inv, mul_comm] using hscaled'
  exact ⟨K, hscaled.const_min 1⟩

theorem exists_cutoff_eq_one [Nonempty X] (x : X) :
    ∃ j : Fin (m D), cutoff D j x = 1 := by
  by_contra hnone
  have hall : ∀ j : Fin (m D),
      boundaryDistance (D.U (label D j)) x < epsilon D := by
    intro j
    have hnot : cutoff D j x ≠ 1 := by
      intro h
      exact hnone ⟨j, h⟩
    have hratio : boundaryDistance (D.U (label D j)) x / epsilon D < 1 := by
      by_contra hle
      have hone : 1 ≤ boundaryDistance (D.U (label D j)) x / epsilon D :=
        not_lt.mp hle
      exact hnot (min_eq_left hone)
    exact (div_lt_one (epsilon_pos D)).mp hratio
  have hsumlt : distanceSum D x < ∑ _j : Fin (m D), epsilon D := by
    exact Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr <|
      ⟨⟨0, m_pos D⟩⟩) fun j _hj => hall j
  have hconst : (∑ _j : Fin (m D), epsilon D) = uniformDelta D := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, epsilon]
    field_simp [show (m D : ℝ) ≠ 0 by exact_mod_cast (m_pos D).ne']
  rw [hconst] at hsumlt
  exact (not_lt_of_ge (uniformDelta_le D x)) hsumlt

/-- Extend a finite vector by zero to natural-number indices. -/
noncomputable def cutoffNat [Nonempty X] (D : CoverData ι X)
    (x : X) (a : ℕ) : ℝ :=
  if h : a < m D then cutoff D ⟨a, h⟩ x else 0

noncomputable def prefixProduct [Nonempty X] (D : CoverData ι X)
    (x : X) (a : ℕ) : ℝ :=
  ∏ i ∈ Finset.range a, (1 - cutoffNat D x i)

@[simp]
theorem prefixProduct_zero [Nonempty X] (x : X) :
    prefixProduct D x 0 = 1 := by
  simp [prefixProduct]

theorem prefixProduct_succ [Nonempty X] (x : X) (a : ℕ) :
    prefixProduct D x (a + 1) =
      prefixProduct D x a * (1 - cutoffNat D x a) := by
  simp [prefixProduct, Finset.prod_range_succ]

noncomputable def stickWeight [Nonempty X] (D : CoverData ι X)
    (x : X) (j : Fin (m D)) : ℝ :=
  cutoff D j x * prefixProduct D x j

theorem stickWeight_nonneg [Nonempty X] (x : X) (j : Fin (m D)) :
    0 ≤ stickWeight D x j := by
  apply mul_nonneg (cutoff_nonneg D j x)
  apply Finset.prod_nonneg
  intro i hi
  exact sub_nonneg.mpr <| by
    unfold cutoffNat
    split_ifs with him
    · exact cutoff_le_one D ⟨i, him⟩ x
    · exact zero_le_one

theorem stickWeight_eq_prefix_sub [Nonempty X] (x : X) (j : Fin (m D)) :
    stickWeight D x j = prefixProduct D x j - prefixProduct D x (j + 1) := by
  rw [prefixProduct_succ]
  have hcut : cutoffNat D x j = cutoff D j x := by
    simp [cutoffNat, j.isLt]
  rw [hcut]
  unfold stickWeight
  ring

theorem prefixProduct_total_eq_zero [Nonempty X] (x : X) :
    prefixProduct D x (m D) = 0 := by
  obtain ⟨j, hj⟩ := exists_cutoff_eq_one D x
  unfold prefixProduct
  apply Finset.prod_eq_zero (Finset.mem_range.mpr j.isLt)
  have hcut : cutoffNat D x j = cutoff D j x := by
    simp [cutoffNat, j.isLt]
  rw [hcut, hj, sub_self]

theorem sum_stickWeight [Nonempty X] (x : X) :
    ∑ j : Fin (m D), stickWeight D x j = 1 := by
  calc
    ∑ j : Fin (m D), stickWeight D x j =
        ∑ j ∈ Finset.range (m D),
          (prefixProduct D x j - prefixProduct D x (j + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      rw [stickWeight_eq_prefix_sub D x j]
    _ = prefixProduct D x 0 - prefixProduct D x (m D) := by
      simpa only using Finset.sum_range_sub'
        (fun a => prefixProduct D x a) (m D)
    _ = 1 := by
      rw [prefixProduct_zero, prefixProduct_total_eq_zero]
      simp

theorem stickWeight_zero_outside [Nonempty X] (j : Fin (m D)) {x : X}
    (hx : x ∉ D.U (label D j)) : stickWeight D x j = 0 := by
  rw [stickWeight, cutoff_eq_zero_of_not_mem D j hx, zero_mul]

omit [CompactSpace X] in
theorem lipschitz_mul_of_nonneg_le_one
    {f g : X → ℝ} {Kf Kg : NNReal}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    LipschitzWith (Kf + Kg) fun x => f x * g x := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  calc
    |f x * g x - f y * g y| =
        |f x * (g x - g y) + (f x - f y) * g y| := by ring_nf
    _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
      calc
        |f x * (g x - g y) + (f x - f y) * g y| ≤
            |f x * (g x - g y)| + |(f x - f y) * g y| := abs_add_le _ _
        _ = |f x| * |g x - g y| + |f x - f y| * |g y| := by
          rw [abs_mul, abs_mul]
    _ ≤ 1 * ((Kg : ℝ) * dist x y) +
        ((Kf : ℝ) * dist x y) * 1 := by
      gcongr
      · simpa [abs_of_nonneg (hf0 x)] using hf1 x
      · simpa [Real.dist_eq] using hg.dist_le_mul x y
      · simpa [Real.dist_eq] using hf.dist_le_mul x y
      · simpa [abs_of_nonneg (hg0 y)] using hg1 y
    _ = ((Kf + Kg : NNReal) : ℝ) * dist x y := by
      push_cast
      ring

omit [CompactSpace X] in
theorem exists_lipschitz_finset_prod
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → X → ℝ)
    (hlip : ∀ i ∈ s, ∃ K : NNReal, LipschitzWith K (f i))
    (h0 : ∀ i ∈ s, ∀ x, 0 ≤ f i x)
    (h1 : ∀ i ∈ s, ∀ x, f i x ≤ 1) :
    ∃ K : NNReal,
      LipschitzWith K (fun x => ∏ i ∈ s, f i x) ∧
      (∀ x, 0 ≤ ∏ i ∈ s, f i x) ∧
      (∀ x, ∏ i ∈ s, f i x ≤ 1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp [LipschitzWith.const (α := X) (1 : ℝ)],
        by simp, by simp⟩
  | @insert a s has ih =>
      obtain ⟨Ka, hKa⟩ := hlip a (Finset.mem_insert_self a s)
      obtain ⟨Ks, hKs, hKs0, hKs1⟩ := ih
        (fun i hi => hlip i (Finset.mem_insert_of_mem hi))
        (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      refine ⟨Ka + Ks, ?_, ?_, ?_⟩
      · simpa only [Finset.prod_insert has] using
          lipschitz_mul_of_nonneg_le_one hKa hKs
            (h0 a (Finset.mem_insert_self a s))
            (h1 a (Finset.mem_insert_self a s)) hKs0 hKs1
      · intro x
        rw [Finset.prod_insert has]
        exact mul_nonneg (h0 a (Finset.mem_insert_self a s) x) (hKs0 x)
      · intro x
        rw [Finset.prod_insert has]
        calc
          f a x * ∏ i ∈ s, f i x ≤ 1 * ∏ i ∈ s, f i x :=
            mul_le_mul_of_nonneg_right (h1 a (Finset.mem_insert_self a s) x) (hKs0 x)
          _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (hKs1 x) zero_le_one
          _ = 1 := one_mul 1

theorem exists_lipschitz_prefixProduct [Nonempty X] (a : ℕ) (ha : a ≤ m D) :
    ∃ K : NNReal,
      LipschitzWith K (fun x => prefixProduct D x a) ∧
      (∀ x, 0 ≤ prefixProduct D x a) ∧
      (∀ x, prefixProduct D x a ≤ 1) := by
  let factor : ℕ → X → ℝ := fun i x => 1 - cutoffNat D x i
  have hlip : ∀ i ∈ Finset.range a, ∃ K : NNReal, LipschitzWith K (factor i) := by
    intro i hi
    have him : i < m D := (Finset.mem_range.mp hi).trans_le ha
    obtain ⟨K, hK⟩ := lipschitz_cutoff D ⟨i, him⟩
    refine ⟨K, ?_⟩
    have h := (LipschitzWith.const (α := X) (1 : ℝ)).sub hK
    simpa [factor, cutoffNat, him] using h
  have h0 : ∀ i ∈ Finset.range a, ∀ x, 0 ≤ factor i x := by
    intro i hi x
    have him : i < m D := (Finset.mem_range.mp hi).trans_le ha
    simp only [factor, cutoffNat, dif_pos him]
    exact sub_nonneg.mpr (cutoff_le_one D ⟨i, him⟩ x)
  have h1 : ∀ i ∈ Finset.range a, ∀ x, factor i x ≤ 1 := by
    intro i hi x
    have him : i < m D := (Finset.mem_range.mp hi).trans_le ha
    have hnonneg := cutoff_nonneg D ⟨i, him⟩ x
    simp only [factor, cutoffNat, dif_pos him]
    linarith
  simpa only [prefixProduct, factor] using
    exists_lipschitz_finset_prod (Finset.range a) factor hlip h0 h1

theorem exists_lipschitz_stickWeight [Nonempty X] (j : Fin (m D)) :
    ∃ K : NNReal, LipschitzWith K (fun x => stickWeight D x j) := by
  obtain ⟨Kc, hKc⟩ := lipschitz_cutoff D j
  obtain ⟨Kp, hKp, hP0, hP1⟩ :=
    exists_lipschitz_prefixProduct D j j.isLt.le
  exact ⟨Kc + Kp, lipschitz_mul_of_nonneg_le_one hKc hKp
    (cutoff_nonneg D j) (cutoff_le_one D j) hP0 hP1⟩

noncomputable def stickLipConstant [Nonempty X] (j : Fin (m D)) : NNReal :=
  Classical.choose (exists_lipschitz_stickWeight D j)

theorem stickLipConstant_spec [Nonempty X] (j : Fin (m D)) :
    LipschitzWith (stickLipConstant D j) (fun x => stickWeight D x j) :=
  Classical.choose_spec (exists_lipschitz_stickWeight D j)

noncomputable def commonLipConstant [Nonempty X] : NNReal :=
  ∑ j : Fin (m D), stickLipConstant D j

theorem stickWeight_lipschitz [Nonempty X] (j : Fin (m D)) :
    LipschitzWith (commonLipConstant D) (fun x => stickWeight D x j) := by
  apply (stickLipConstant_spec D j).weaken
  exact Finset.single_le_sum (fun i _hi => by positivity)
    (Finset.mem_univ j)

noncomputable def baseWeightSystem [Nonempty X] : WeightSystem D.U (m D) where
  label := label D
  weight := stickWeight D
  continuous_weight j := (stickWeight_lipschitz D j).continuous
  nonneg := stickWeight_nonneg D
  sum_eq_one := sum_stickWeight D
  zero_outside := stickWeight_zero_outside D

noncomputable def repeatedBaseIndex [Nonempty X] {M : ℕ}
    (j : Fin (M * m D)) : Fin (m D) :=
  (finProdFinEquiv.symm j).2

@[simp]
theorem repeatedBaseIndex_pair [Nonempty X] {M : ℕ}
    (b : Fin M) (i : Fin (m D)) :
    repeatedBaseIndex D (finProdFinEquiv (b, i)) = i := by
  simp [repeatedBaseIndex]

noncomputable def repeatedWeightSystem [Nonempty X]
    (M : ℕ) (hM : 0 < M) : WeightSystem D.U (M * m D) where
  label j := label D (repeatedBaseIndex D j)
  weight x j := stickWeight D x (repeatedBaseIndex D j) / M
  continuous_weight j := by
    exact ((stickWeight_lipschitz D (repeatedBaseIndex D j)).continuous).div_const _
  nonneg x j := div_nonneg (stickWeight_nonneg D x (repeatedBaseIndex D j)) (by positivity)
  sum_eq_one x := by
    calc
      ∑ j : Fin (M * m D), stickWeight D x (repeatedBaseIndex D j) / M =
          ∑ p : Fin M × Fin (m D), stickWeight D x p.2 / M := by
        symm
        calc
          ∑ p : Fin M × Fin (m D), stickWeight D x p.2 / M =
              ∑ p : Fin M × Fin (m D),
                stickWeight D x (repeatedBaseIndex D (finProdFinEquiv p)) / M := by
            apply Finset.sum_congr rfl
            intro p _hp
            rw [repeatedBaseIndex_pair]
          _ = ∑ j : Fin (M * m D),
                stickWeight D x (repeatedBaseIndex D j) / M :=
            finProdFinEquiv.sum_comp
              (fun j : Fin (M * m D) => stickWeight D x (repeatedBaseIndex D j) / M)
      _ = ∑ b : Fin M, ∑ i : Fin (m D), stickWeight D x i / M := by
        rw [Fintype.sum_prod_type]
      _ = ∑ _b : Fin M, (1 : ℝ) / M := by
        apply Finset.sum_congr rfl
        intro b _hb
        rw [← Finset.sum_div, sum_stickWeight D x]
      _ = 1 := by
        simp [hM.ne']
  zero_outside j x hx := by
    rw [stickWeight_zero_outside D (repeatedBaseIndex D j) hx, zero_div]

noncomputable def repeatCoordinateConstant [Nonempty X]
    (M : ℕ) : NNReal := ‖((M : ℝ)⁻¹)‖₊ * commonLipConstant D

theorem repeatedWeight_lipschitz [Nonempty X]
    (M : ℕ) (hM : 0 < M) (j : Fin (M * m D)) :
    LipschitzWith (repeatCoordinateConstant D M)
      (fun x => (repeatedWeightSystem D M hM).weight x j) := by
  let i := repeatedBaseIndex D j
  let a : ℝ := (M : ℝ)⁻¹
  have hbase := stickWeight_lipschitz D i
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (stickWeight D x i / M) (stickWeight D y i / M) ≤
    (repeatCoordinateConstant D M : ℝ) * dist x y
  calc
    dist (stickWeight D x i / M) (stickWeight D y i / M) =
        dist (a * stickWeight D x i) (a * stickWeight D y i) := by
      congr 1 <;> dsimp [a] <;> field_simp
    _ ≤ ‖a‖ * dist (stickWeight D x i) (stickWeight D y i) := by
      simpa only [smul_eq_mul] using
        dist_smul_le a (stickWeight D x i) (stickWeight D y i)
    _ ≤ ‖a‖ * ((commonLipConstant D : NNReal) : ℝ) * dist x y := by
      calc
        ‖a‖ * dist (stickWeight D x i) (stickWeight D y i) ≤
            ‖a‖ * ((commonLipConstant D : NNReal) : ℝ) * dist x y := by
          rw [mul_assoc]
          gcongr
          exact hbase.dist_le_mul x y
    _ = (repeatCoordinateConstant D M : ℝ) * dist x y := by
      simp [repeatCoordinateConstant, a]

omit [CompactSpace X] in
theorem lipschitz_fintype_sum
    {α : Type*} [Fintype α] (K : NNReal) (f : α → X → ℝ)
    (hf : ∀ i, LipschitzWith K (f i)) :
    LipschitzWith ((Fintype.card α : NNReal) * K)
      (fun x => ∑ i, f i x) := by
  classical
  let s : Finset α := Finset.univ
  have hs : LipschitzWith ((s.card : NNReal) * K)
      (fun x => ∑ i ∈ s, f i x) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul] using
          (LipschitzWith.const (α := X) (0 : ℝ))
    | @insert a s has ih =>
        have h := (hf a).add ih
        simpa [Finset.sum_insert has, Finset.card_insert_of_notMem has,
          Nat.cast_add, add_mul, add_comm] using h
  simpa [s] using hs

noncomputable def blockContribution [Nonempty X]
    (M : ℕ) (hM : 0 < M) (b : Fin M) (s : ℝ) (x : X) : ℝ :=
  ∑ i : Fin (m D),
    (repeatedWeightSystem D M hM).weight x (finProdFinEquiv (b, i)) *
      ramp (M * m D) (finProdFinEquiv (b, i)) s

theorem cdf_eq_sum_blockContribution [Nonempty X]
    (M : ℕ) (hM : 0 < M) (s : ℝ) (x : X) :
    cdf ((repeatedWeightSystem D M hM).weight x) s =
      ∑ b : Fin M, blockContribution D M hM b s x := by
  unfold cdf blockContribution
  calc
    ∑ j : Fin (M * m D),
        (repeatedWeightSystem D M hM).weight x j * ramp (M * m D) j s =
        ∑ p : Fin M × Fin (m D),
          (repeatedWeightSystem D M hM).weight x (finProdFinEquiv p) *
            ramp (M * m D) (finProdFinEquiv p) s := by
      symm
      exact finProdFinEquiv.sum_comp
        (fun j : Fin (M * m D) =>
          (repeatedWeightSystem D M hM).weight x j * ramp (M * m D) j s)
    _ = ∑ b : Fin M, ∑ i : Fin (m D),
          (repeatedWeightSystem D M hM).weight x (finProdFinEquiv (b, i)) *
            ramp (M * m D) (finProdFinEquiv (b, i)) s := by
      rw [Fintype.sum_prod_type]

theorem finProdFinEquiv_lt_of_fst_lt [Nonempty X] {M : ℕ}
    {b c : Fin M} (hbc : b < c) (i j : Fin (m D)) :
    finProdFinEquiv (b, i) < finProdFinEquiv (c, j) := by
  change i.1 + m D * b.1 < j.1 + m D * c.1
  calc
    i.1 + m D * b.1 < m D + m D * b.1 :=
      Nat.add_lt_add_right i.isLt _
    _ = m D * b.1 + m D := Nat.add_comm _ _
    _ = m D * (b.1 + 1) := (Nat.mul_succ _ _).symm
    _ ≤ m D * c.1 := Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hbc)
    _ ≤ j.1 + m D * c.1 := Nat.le_add_left _ _

theorem blockContribution_eq_div_of_lt [Nonempty X]
    (M : ℕ) (hM : 0 < M) (j : Fin (M * m D)) (b : Fin M)
    (hb : b < (finProdFinEquiv.symm j).1) {s : ℝ}
    (hs : (j : ℝ) / (↑(M * m D) : ℝ) ≤ s) (x : X) :
    blockContribution D M hM b s x = 1 / (M : ℝ) := by
  unfold blockContribution
  calc
    ∑ i : Fin (m D),
        (repeatedWeightSystem D M hM).weight x (finProdFinEquiv (b, i)) *
          ramp (M * m D) (finProdFinEquiv (b, i)) s =
        ∑ i : Fin (m D),
          (repeatedWeightSystem D M hM).weight x (finProdFinEquiv (b, i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hj : finProdFinEquiv ((finProdFinEquiv.symm j).1,
          (finProdFinEquiv.symm j).2) = j := finProdFinEquiv.apply_symm_apply j
      have hcell :
          ((finProdFinEquiv ((finProdFinEquiv.symm j).1,
              (finProdFinEquiv.symm j).2) : ℝ) / (↑(M * m D) : ℝ)) ≤ s := by
        rw [hj]
        exact hs
      rw [ramp_eq_one_of_cell_lt
        (finProdFinEquiv_lt_of_fst_lt D hb i (finProdFinEquiv.symm j).2) hcell,
        mul_one]
    _ = ∑ i : Fin (m D), stickWeight D x i / M := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [repeatedWeightSystem]
    _ = 1 / (M : ℝ) := by
      rw [← Finset.sum_div, sum_stickWeight]

theorem blockContribution_eq_zero_of_gt [Nonempty X]
    (M : ℕ) (hM : 0 < M) (j : Fin (M * m D)) (b : Fin M)
    (hb : (finProdFinEquiv.symm j).1 < b) {s : ℝ}
    (hs : s ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / (↑(M * m D) : ℝ)) (x : X) :
    blockContribution D M hM b s x = 0 := by
  unfold blockContribution
  apply Finset.sum_eq_zero
  intro i _hi
  have hj : finProdFinEquiv ((finProdFinEquiv.symm j).1,
      (finProdFinEquiv.symm j).2) = j := finProdFinEquiv.apply_symm_apply j
  have hcell : s ≤
      (((finProdFinEquiv ((finProdFinEquiv.symm j).1,
          (finProdFinEquiv.symm j).2) : ℕ) + 1 : ℕ) : ℝ) /
        (↑(M * m D) : ℝ) := by
    rw [hj]
    exact hs
  rw [ramp_eq_zero_of_lt_cell
    (finProdFinEquiv_lt_of_fst_lt D hb (finProdFinEquiv.symm j).2 i) hcell,
    mul_zero]

theorem blockContribution_eq_of_ne_current [Nonempty X]
    (M : ℕ) (hM : 0 < M) (j : Fin (M * m D)) (b : Fin M)
    (hb : b ≠ (finProdFinEquiv.symm j).1) {s : ℝ}
    (hs : (j : ℝ) / (↑(M * m D) : ℝ) ≤ s ∧
      s ≤ (((j : ℕ) + 1 : ℕ) : ℝ) / (↑(M * m D) : ℝ)) (x y : X) :
    blockContribution D M hM b s x = blockContribution D M hM b s y := by
  rcases lt_or_gt_of_ne hb with hb | hb
  · rw [blockContribution_eq_div_of_lt D M hM j b hb hs.1 x,
      blockContribution_eq_div_of_lt D M hM j b hb hs.1 y]
  · rw [blockContribution_eq_zero_of_gt D M hM j b hb hs.2 x,
      blockContribution_eq_zero_of_gt D M hM j b hb hs.2 y]

omit [CompactSpace X] in
theorem lipschitz_mul_const_of_nonneg_le_one (K : NNReal) (f : X → ℝ)
    (hf : LipschitzWith K f) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    LipschitzWith K (fun x => f x * a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (f x * a) (f y * a) = dist (a • f x) (a • f y) := by
      simp only [smul_eq_mul, mul_comm]
    _ ≤ ‖a‖ * dist (f x) (f y) := dist_smul_le a (f x) (f y)
    _ ≤ 1 * ((K : ℝ) * dist x y) := by
      apply mul_le_mul
      · simpa only [Real.norm_of_nonneg ha0] using ha1
      · exact hf.dist_le_mul x y
      · exact dist_nonneg
      · exact zero_le_one
    _ = (K : ℝ) * dist x y := one_mul _

noncomputable def blockLipschitzConstant [Nonempty X]
    (M : ℕ) : NNReal := (m D : NNReal) * repeatCoordinateConstant D M

theorem blockContribution_lipschitz [Nonempty X]
    (M : ℕ) (hM : 0 < M) (b : Fin M) (s : ℝ) :
    LipschitzWith (blockLipschitzConstant D M)
      (blockContribution D M hM b s) := by
  change LipschitzWith ((m D : NNReal) * repeatCoordinateConstant D M)
    (fun x => ∑ i : Fin (m D),
      (repeatedWeightSystem D M hM).weight x (finProdFinEquiv (b, i)) *
        ramp (M * m D) (finProdFinEquiv (b, i)) s)
  simpa only [Fintype.card_fin] using lipschitz_fintype_sum (X := X) (α := Fin (m D))
    (repeatCoordinateConstant D M)
    (fun i x =>
      (repeatedWeightSystem D M hM).weight x (finProdFinEquiv (b, i)) *
        ramp (M * m D) (finProdFinEquiv (b, i)) s)
    (fun i => lipschitz_mul_const_of_nonneg_le_one
      (repeatCoordinateConstant D M)
      (fun x => (repeatedWeightSystem D M hM).weight x (finProdFinEquiv (b, i)))
      (repeatedWeight_lipschitz D M hM (finProdFinEquiv (b, i)))
      (ramp (M * m D) (finProdFinEquiv (b, i)) s)
      (ramp_nonneg _ _ _) (ramp_le_one _ _ _))

theorem repeatedCdf_lipschitz [Nonempty X]
    (M : ℕ) (hM : 0 < M) (s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) :
    LipschitzWith (blockLipschitzConstant D M)
      (fun x => cdf ((repeatedWeightSystem D M hM).weight x) s) := by
  obtain ⟨j, hj⟩ := exists_grid_index (Nat.mul_pos hM (m_pos D)) hs.1 hs.2
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [cdf_eq_sum_blockContribution D M hM s x,
    cdf_eq_sum_blockContribution D M hM s y]
  have hdiff :
      (∑ b : Fin M, blockContribution D M hM b s x) -
          ∑ b : Fin M, blockContribution D M hM b s y =
        blockContribution D M hM (finProdFinEquiv.symm j).1 s x -
          blockContribution D M hM (finProdFinEquiv.symm j).1 s y := by
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_single (finProdFinEquiv.symm j).1]
    intro b hb
    rw [blockContribution_eq_of_ne_current D M hM j b hb hj x y, sub_self]
  calc
    dist (∑ b : Fin M, blockContribution D M hM b s x)
        (∑ b : Fin M, blockContribution D M hM b s y) =
        |(∑ b : Fin M, blockContribution D M hM b s x) -
          ∑ b : Fin M, blockContribution D M hM b s y| := Real.dist_eq _ _
    _ = |blockContribution D M hM (finProdFinEquiv.symm j).1 s x -
          blockContribution D M hM (finProdFinEquiv.symm j).1 s y| :=
      congrArg abs hdiff
    _ = dist (blockContribution D M hM (finProdFinEquiv.symm j).1 s x)
        (blockContribution D M hM (finProdFinEquiv.symm j).1 s y) :=
      (Real.dist_eq _ _).symm
    _ ≤ (blockLipschitzConstant D M : ℝ) * dist x y :=
      (blockContribution_lipschitz D M hM (finProdFinEquiv.symm j).1 s).dist_le_mul x y

end Submission.LipschitzWeights
