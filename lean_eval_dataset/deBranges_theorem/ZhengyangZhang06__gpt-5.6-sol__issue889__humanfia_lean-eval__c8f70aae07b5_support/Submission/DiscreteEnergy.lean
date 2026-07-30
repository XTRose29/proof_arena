import Submission.FineStepLog

open Filter Function Metric Set

namespace Submission

abbrev LoewnerCoeffVector (N : ℕ) := Fin (N + 1) → ℂ

noncomputable def coeffVectorToSeq {N : ℕ}
    (c : LoewnerCoeffVector N) (n : ℕ) : ℂ :=
  if hn : n < N + 1 then c ⟨n, hn⟩ else 0

noncomputable def seqToCoeffVector (N : ℕ) (c : ℕ → ℂ) :
    LoewnerCoeffVector N :=
  fun n ↦ c n

@[simp]
lemma coeffVectorToSeq_apply {N : ℕ} (c : LoewnerCoeffVector N)
    (n : Fin (N + 1)) :
    coeffVectorToSeq c n = c n := by
  simp [coeffVectorToSeq, n.isLt]

@[simp]
lemma seqToCoeffVector_apply (N : ℕ) (c : ℕ → ℂ) (n : Fin (N + 1)) :
    seqToCoeffVector N c n = c n := rfl

lemma continuousAt_seriesMulCoeff
    {X : Type*} [TopologicalSpace X] {x : X}
    (a b : X → ℕ → ℂ)
    (ha : ∀ n, ContinuousAt (fun y ↦ a y n) x)
    (hb : ∀ n, ContinuousAt (fun y ↦ b y n) x) (n : ℕ) :
    ContinuousAt (fun y ↦ seriesMulCoeff (a y) (b y) n) x := by
  unfold seriesMulCoeff
  fun_prop

lemma continuousAt_finsetSum
    {X I : Type*} [TopologicalSpace X] {x : X}
    (s : Finset I) (f : X → I → ℂ)
    (hf : ∀ i ∈ s, ContinuousAt (fun y ↦ f y i) x) :
    ContinuousAt (fun y ↦ ∑ i ∈ s, f y i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : X ↦ (0 : ℂ)) x)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

lemma continuousAt_finsetSum_real
    {X I : Type*} [TopologicalSpace X] {x : X}
    (s : Finset I) (f : X → I → ℝ)
    (hf : ∀ i ∈ s, ContinuousAt (fun y ↦ f y i) x) :
    ContinuousAt (fun y ↦ ∑ i ∈ s, f y i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : X ↦ (0 : ℝ)) x)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

lemma continuousAt_seriesPowCoeff
    {X : Type*} [TopologicalSpace X] {x : X}
    (a : X → ℕ → ℂ)
    (ha : ∀ n, ContinuousAt (fun y ↦ a y n) x) :
    ∀ k n, ContinuousAt (fun y ↦ seriesPowCoeff (a y) k n) x := by
  intro k
  induction k with
  | zero =>
      intro n
      simp only [seriesPowCoeff]
      fun_prop
  | succ k ih =>
      intro n
      simp only [seriesPowCoeff]
      exact continuousAt_seriesMulCoeff a
        (fun y ↦ seriesPowCoeff (a y) k) ha (ih) n

lemma continuousAt_seriesPowSlopeCoeff
    {X : Type*} [TopologicalSpace X] {x : X}
    (a aSlope : X → ℕ → ℂ)
    (ha : ∀ n, ContinuousAt (fun y ↦ a y n) x)
    (haSlope : ∀ n, ContinuousAt (fun y ↦ aSlope y n) x) :
    ∀ k n,
      ContinuousAt
        (fun y ↦ seriesPowSlopeCoeff (a y) (aSlope y) k n) x := by
  intro k
  induction k with
  | zero =>
      intro n
      simp only [seriesPowSlopeCoeff]
      fun_prop
  | succ k ih =>
      intro n
      simp only [seriesPowSlopeCoeff]
      exact (continuousAt_seriesMulCoeff aSlope
          (fun y ↦ seriesPowCoeff (a y) k) haSlope
          (continuousAt_seriesPowCoeff a ha k) n).add
        (continuousAt_seriesMulCoeff (fun _ ↦ seriesUnitCoeff)
          (fun y ↦ seriesPowSlopeCoeff (a y) (aSlope y) k)
          (fun _ ↦ continuousAt_const) ih n)

lemma continuousAt_canonicalTransitionCoeff
    {X : Type*} [TopologicalSpace X] {x : X}
    (r omega : X → ℂ) (hr : ContinuousAt r x)
    (homega : ContinuousAt omega x) (n : ℕ) :
    ContinuousAt (fun y ↦ canonicalTransitionCoeff (r y) (omega y) n) x := by
  rcases n with (_ | _ | n) <;>
    simp only [canonicalTransitionCoeff] <;> fun_prop

lemma continuousAt_canonicalTransitionSlopeCoeff
    {X : Type*} [TopologicalSpace X] {x : X}
    (r omega : X → ℂ) (hr : ContinuousAt r x)
    (homega : ContinuousAt omega x) (n : ℕ) :
    ContinuousAt
      (fun y ↦ canonicalTransitionSlopeCoeff (r y) (omega y) n) x := by
  rcases n with (_ | _ | n) <;>
    simp only [canonicalTransitionSlopeCoeff] <;> fun_prop

lemma continuousAt_inversePowerSum
    {X : Type*} [TopologicalSpace X] {x : X}
    (r : X → ℂ) (hr : ContinuousAt r x) (hr0 : r x ≠ 0) (m : ℕ) :
    ContinuousAt (fun y ↦ inversePowerSum (r y) m) x := by
  unfold inversePowerSum
  fun_prop

lemma continuousAt_forwardPowerSum
    {X : Type*} [TopologicalSpace X] {x : X}
    (r : X → ℂ) (hr : ContinuousAt r x) (m : ℕ) :
    ContinuousAt (fun y ↦ forwardPowerSum (r y) m) x := by
  unfold forwardPowerSum
  fun_prop

lemma continuousAt_canonicalLogFactorSlope
    {X : Type*} [TopologicalSpace X] {x : X}
    (r omega : X → ℂ) (hr : ContinuousAt r x)
    (homega : ContinuousAt omega x) (hr0 : r x ≠ 0) (n : ℕ) :
    ContinuousAt
      (fun y ↦ canonicalLogFactorSlope (r y) (omega y) n) x := by
  rcases n with _ | n
  · simp only [canonicalLogFactorSlope]
    fun_prop
  · simp only [canonicalLogFactorSlope]
    exact (((continuousAt_const.pow (n + 2)).mul (homega.pow (n + 1))).mul
      ((continuousAt_inversePowerSum r hr hr0 (n + 1)).add
        (continuousAt_forwardPowerSum r hr (n + 1))).neg).div_const _

lemma continuousAt_canonicalLoewnerSlope
    {X : Type*} [TopologicalSpace X] {x : X}
    (c : X → ℕ → ℂ) (r omega : X → ℂ)
    (hc : ∀ n, ContinuousAt (fun y ↦ c y n) x)
    (hr : ContinuousAt r x) (homega : ContinuousAt omega x)
    (hr0 : r x ≠ 0) (n : ℕ) :
    ContinuousAt
      (fun y ↦ canonicalLoewnerSlope (c y) (r y) (omega y) n) x := by
  unfold canonicalLoewnerSlope
  apply ContinuousAt.add
  · apply continuousAt_finsetSum
    intro k hk
    exact (hc k).mul
      (continuousAt_seriesPowSlopeCoeff
        (fun y ↦ canonicalTransitionCoeff (r y) (omega y))
        (fun y ↦ canonicalTransitionSlopeCoeff (r y) (omega y))
        (continuousAt_canonicalTransitionCoeff r omega hr homega)
        (continuousAt_canonicalTransitionSlopeCoeff r omega hr homega) k n)
  · exact continuousAt_canonicalLogFactorSlope r omega hr homega hr0 n

noncomputable def vectorCanonicalSlope {N : ℕ}
    (r omega : ℂ) (c : LoewnerCoeffVector N) : LoewnerCoeffVector N :=
  fun n ↦ canonicalLoewnerSlope (coeffVectorToSeq c) r omega n

noncomputable def vectorCanonicalCoeff {N : ℕ}
    (r omega : ℂ) (c : LoewnerCoeffVector N) : LoewnerCoeffVector N :=
  fun n ↦ canonicalLoewnerCoeff (coeffVectorToSeq c) r omega n

noncomputable def vectorDrivenVelocity {N : ℕ}
    (omega : ℂ) (c : LoewnerCoeffVector N) : LoewnerCoeffVector N :=
  fun n ↦ drivenLoewnerVelocity (coeffVectorToSeq c) omega n

lemma continuousAt_vectorCanonicalSlope {N : ℕ}
    {r omega : ℂ} {c : LoewnerCoeffVector N} (hr0 : r ≠ 0) :
    ContinuousAt
      (fun p : ℂ × ℂ × LoewnerCoeffVector N ↦
        vectorCanonicalSlope p.1 p.2.1 p.2.2) (r, omega, c) := by
  apply (continuousAt_pi).2
  intro n
  apply continuousAt_canonicalLoewnerSlope
  · intro k
    unfold coeffVectorToSeq
    by_cases hk : k < N + 1
    · simp only [hk, dite_true]
      fun_prop
    · simp only [hk, dite_false]
      fun_prop
  · fun_prop
  · fun_prop
  · exact hr0

lemma vectorCanonicalCoeff_eq_add_slope {N : ℕ}
    (c : LoewnerCoeffVector N) (r omega : ℂ) (hr : r ≠ 0) :
    vectorCanonicalCoeff r omega c =
      c + (r - 1) • vectorCanonicalSlope r omega c := by
  funext n
  change canonicalLoewnerCoeff (coeffVectorToSeq c) r omega n =
    c n + (r - 1) * canonicalLoewnerSlope (coeffVectorToSeq c) r omega n
  rw [← coeffVectorToSeq_apply c n]
  linear_combination
    canonicalLoewnerCoeff_sub_eq_mul_slope
      (coeffVectorToSeq c) r omega hr n

@[simp]
lemma vectorCanonicalSlope_one {N : ℕ}
    (c : LoewnerCoeffVector N) {omega : ℂ} (homega : omega ≠ 0)
    (n : Fin (N + 1)) (hn : 0 < (n : ℕ)) :
    vectorCanonicalSlope 1 omega c n = vectorDrivenVelocity (-omega) c n := by
  exact canonicalLoewnerSlope_one (coeffVectorToSeq c) homega hn

noncomputable def vectorDeBrangesGap (N : ℕ) (t : ℝ)
    (c : LoewnerCoeffVector N) : ℝ :=
  deBrangesEnergy N (fun k ↦ explicitDeBrangesTau N k t)
      (coeffVectorToSeq c) -
    deBrangesWeight N (fun k ↦ explicitDeBrangesTau N k t)

noncomputable def vectorDeBrangesGapRate (N : ℕ) (t : ℝ)
    (c cDot : LoewnerCoeffVector N) : ℝ :=
  deBrangesEnergyRate N
      (fun k ↦ explicitDeBrangesTau N k t)
      (fun k ↦ explicitDeBrangesTauDot N k t)
      (coeffVectorToSeq c) (coeffVectorToSeq cDot) -
    deBrangesWeightRate N (fun k ↦ explicitDeBrangesTauDot N k t)

lemma vectorDrivenVelocity_satisfiesODE {N : ℕ}
    (c : LoewnerCoeffVector N) {omega : ℂ} (_homega : omega ≠ 0) :
    SatisfiesDrivenLoewnerLogarithmicODE N (coeffVectorToSeq c)
      (coeffVectorToSeq (vectorDrivenVelocity omega c)) omega := by
  intro k hk
  have hk' : k + 1 < N + 1 := by
    exact Nat.succ_lt_succ (Finset.mem_range.mp hk)
  rw [coeffVectorToSeq]
  simp only [hk', dite_true, vectorDrivenVelocity]
  simp [drivenLoewnerVelocity]

lemma vectorDeBrangesGapRate_driven_nonneg {N : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (c : LoewnerCoeffVector N) {omega : ℂ}
    (homega : ‖omega‖ = 1) :
    0 ≤ vectorDeBrangesGapRate N t c (vectorDrivenVelocity omega c) := by
  have hsystem := explicitDeBranges_satisfies_system N t
  have hrate := deBrangesEnergyRate_lower_bound_driven hsystem homega
    (vectorDrivenVelocity_satisfiesODE c (norm_ne_zero_iff.mp (by
      rw [homega]
      norm_num)))
    (fun k hk ↦ explicitDeBrangesTauDot_nonpos_of_gasper
      satisfiesGasperIdentities (by omega) (Finset.mem_range.mp hk) ht)
  have hweight := deBrangesSystem_boundary_eq_weightRate hsystem
  unfold vectorDeBrangesGapRate
  linarith

lemma taylorCoeff_inverseMap_norm_le_two_pow
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (n : ℕ) :
    ‖taylorCoeff reach.inverseMap n‖ ≤ (2 : ℝ) ^ n := by
  have hclosed : closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball_zero_iff]
    linarith
  have hdiff : DiffContOnCl ℂ reach.inverseMap (ball (0 : ℂ) (1 / 2 : ℝ)) :=
    reach.inverseMap_differentiableOn.diffContOnCl_ball hclosed
  have hbound : ∀ z ∈ sphere (0 : ℂ) (1 / 2 : ℝ),
      ‖reach.inverseMap z‖ ≤ 1 := by
    intro z hz
    have hzBall := hclosed (sphere_subset_closedBall hz)
    exact (mem_ball_zero_iff.mp
      (reach.inverseMap_mapsTo_unitBall hzBall)).le
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n (by norm_num : (0 : ℝ) < 1 / 2) hdiff hbound
  rw [taylorCoeff, norm_div, Complex.norm_natCast]
  have hfac : (0 : ℝ) < n.factorial := by positivity
  calc
    ‖iteratedDeriv n reach.inverseMap 0‖ / (n.factorial : ℝ) ≤
        (n.factorial * 1 / (1 / 2 : ℝ) ^ n) / n.factorial :=
      div_le_div_of_nonneg_right hcauchy hfac.le
    _ = (2 : ℝ) ^ n := by
      field_simp
      rw [← mul_pow]
      norm_num

lemma taylorCoeff_normalizedInverse_norm_le
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (n : ℕ) :
    ‖taylorCoeff reach.normalizedInverse n‖ ≤
      (2 : ℝ) ^ n / ‖deriv E₀.toFun 0‖ := by
  have hd₀ : 0 < ‖deriv E₀.toFun 0‖ := norm_pos_iff.mpr E₀.deriv_ne_zero
  have hE : ‖deriv E.toFun 0‖ ≤ 1 := E.deriv_norm_le_one
  have hInv : ‖deriv E₀.toFun 0‖ ≤ ‖deriv reach.inverseMap 0‖ := by
    rw [reach.norm_deriv_inverseMap]
    have hEpos : 0 < ‖deriv E.toFun 0‖ := norm_pos_iff.mpr E.deriv_ne_zero
    exact (le_div_iff₀ hEpos).2 (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hE hd₀.le)
  rw [show reach.normalizedInverse =
      fun z ↦ reach.inverseMap z / deriv reach.inverseMap 0 by rfl,
    taylorCoeff_div_const, norm_div]
  calc
    ‖taylorCoeff reach.inverseMap n‖ / ‖deriv reach.inverseMap 0‖ ≤
        (2 : ℝ) ^ n / ‖deriv reach.inverseMap 0‖ :=
      div_le_div_of_nonneg_right
        (taylorCoeff_inverseMap_norm_le_two_pow reach n) (norm_nonneg _)
    _ ≤ (2 : ℝ) ^ n / ‖deriv E₀.toFun 0‖ := by
      apply (div_le_div_iff_of_pos_left (by positivity)
        (lt_of_lt_of_le hd₀ hInv) hd₀).2
      exact hInv

noncomputable def normalizedTaylorBox
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    Set (ℕ → ℂ) :=
  Set.pi Set.univ fun n ↦
    closedBall 0 ((2 : ℝ) ^ n / ‖deriv E₀.toFun 0‖)

lemma isCompact_normalizedTaylorBox
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    IsCompact (normalizedTaylorBox E₀) := by
  unfold normalizedTaylorBox
  exact isCompact_univ_pi fun n ↦ isCompact_closedBall 0 _

lemma normalizedTaylorVector_mem_box
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) :
    taylorCoeff reach.normalizedInverse ∈ normalizedTaylorBox E₀ := by
  intro n hn
  rw [mem_closedBall, dist_zero_right]
  exact taylorCoeff_normalizedInverse_norm_le reach n

lemma continuousAt_formalLogarithmicCoeff
    {X : Type*} [TopologicalSpace X] {x : X}
    (a : X → ℕ → ℂ)
    (ha : ∀ n, ContinuousAt (fun y ↦ a y n) x) :
    ∀ n, ContinuousAt (fun y ↦ formalLogarithmicCoeff (a y) n) x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp only [formalLogarithmicCoeff]
          fun_prop
      | succ n =>
          simp only [formalLogarithmicCoeff]
          apply ContinuousAt.sub
          · exact (ha (n + 2)).div_const 2
          · apply ContinuousAt.div_const
            apply continuousAt_finsetSum
            intro j hj
            exact (ha (j + 2)).mul
              (continuousAt_const.mul
                ((ih (n - j) (by
                  have hjn := Finset.mem_range.mp hj
                  omega)).const_mul 2))

noncomputable def formalCoeffVector (N : ℕ)
    (a : ℕ → ℂ) : LoewnerCoeffVector N :=
  fun n ↦ formalLogarithmicCoeff a n

lemma continuous_formalCoeffVector (N : ℕ) :
    Continuous (formalCoeffVector N) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply (continuousAt_pi).2
  intro n
  apply continuousAt_formalLogarithmicCoeff
  intro k
  exact (continuous_apply k).continuousAt

noncomputable def formalCoeffBody
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) (N : ℕ) :
    Set (LoewnerCoeffVector N) :=
  formalCoeffVector N '' normalizedTaylorBox E₀

lemma isCompact_formalCoeffBody
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) (N : ℕ) :
    IsCompact (formalCoeffBody E₀ N) := by
  exact (isCompact_normalizedTaylorBox E₀).image_of_continuousOn
    (continuous_formalCoeffVector N).continuousOn

lemma formalCoeffVector_normalizedInverse_mem
    {E₀ E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (reach : E₀.ReachableFrom E) (N : ℕ) :
    seqToCoeffVector N
        (formalLogarithmicCoeff (taylorCoeff reach.normalizedInverse)) ∈
      formalCoeffBody E₀ N := by
  refine ⟨taylorCoeff reach.normalizedInverse,
    normalizedTaylorVector_mem_box reach, ?_⟩
  rfl

lemma continuous_explicitDeBrangesTau (N k : ℕ) :
    Continuous (explicitDeBrangesTau N k) := by
  unfold explicitDeBrangesTau
  fun_prop

lemma continuous_explicitDeBrangesTauDot (N k : ℕ) :
    Continuous (explicitDeBrangesTauDot N k) := by
  unfold explicitDeBrangesTauDot
  fun_prop

lemma continuousAt_coeffVectorToSeq
    {X : Type*} [TopologicalSpace X] {x : X} {N n : ℕ}
    (hn : n < N + 1) (c : X → LoewnerCoeffVector N)
    (hc : ContinuousAt c x) :
    ContinuousAt (fun y ↦ coeffVectorToSeq (c y) n) x := by
  simp only [coeffVectorToSeq, hn, dite_true]
  exact (continuous_apply ⟨n, hn⟩).continuousAt.comp hc

lemma continuousAt_vectorDeBrangesGapRate
    {X : Type*} [TopologicalSpace X] {x : X} {N : ℕ}
    (t : X → ℝ) (c cDot : X → LoewnerCoeffVector N)
    (ht : ContinuousAt t x) (hc : ContinuousAt c x)
    (hcDot : ContinuousAt cDot x) :
    ContinuousAt (fun y ↦ vectorDeBrangesGapRate N (t y) (c y) (cDot y)) x := by
  unfold vectorDeBrangesGapRate deBrangesEnergyRate deBrangesWeightRate
  apply ContinuousAt.sub
  · apply continuousAt_finsetSum_real
    intro k hk
    have hkN : k + 1 < N + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hk)
    have hcVal := continuousAt_coeffVectorToSeq hkN c hc
    have hcDotVal := continuousAt_coeffVectorToSeq hkN cDot hcDot
    have htau := (continuous_explicitDeBrangesTau N (k + 1)).continuousAt.comp ht
    have htauDot :=
      (continuous_explicitDeBrangesTauDot N (k + 1)).continuousAt.comp ht
    exact continuousAt_const.mul
      ((htauDot.mul (hcVal.norm.pow 2)).add
        ((continuousAt_const.mul htau).mul
          (Complex.continuous_re.continuousAt.comp
            (hcDotVal.mul hcVal.star))))
  · apply continuousAt_finsetSum_real
    intro k hk
    exact ((continuous_explicitDeBrangesTauDot N (k + 1)).continuousAt.comp ht).div_const _

abbrev LocalGapDatum (N : ℕ) :=
  ℝ × (ℝ × (ℝ × (LoewnerCoeffVector N × ℂ)))

def LocalGapDatum.time {N : ℕ} (p : LocalGapDatum N) : ℝ := p.1
def LocalGapDatum.mesh {N : ℕ} (p : LocalGapDatum N) : ℝ := p.2.1
def LocalGapDatum.offset {N : ℕ} (p : LocalGapDatum N) : ℝ := p.2.2.1
def LocalGapDatum.coeff {N : ℕ} (p : LocalGapDatum N) : LoewnerCoeffVector N :=
  p.2.2.2.1
def LocalGapDatum.omega {N : ℕ} (p : LocalGapDatum N) : ℂ := p.2.2.2.2

noncomputable def localCanonicalSlope {N : ℕ} (p : LocalGapDatum N) :
    LoewnerCoeffVector N :=
  vectorCanonicalSlope ((1 - p.mesh : ℝ) : ℂ) p.omega p.coeff

noncomputable def localInterpolatedCoeff {N : ℕ} (p : LocalGapDatum N) :
    LoewnerCoeffVector N :=
  p.coeff + (((p.offset - p.mesh : ℝ) : ℂ) • localCanonicalSlope p)

noncomputable def localDiscreteGapRate (N : ℕ) (p : LocalGapDatum N) : ℝ :=
  vectorDeBrangesGapRate N (p.time + p.offset)
    (localInterpolatedCoeff p) (localCanonicalSlope p)

lemma continuousAt_localCanonicalSlope {N : ℕ} {p : LocalGapDatum N}
    (hr : ((1 - p.mesh : ℝ) : ℂ) ≠ 0) :
    ContinuousAt (localCanonicalSlope (N := N)) p := by
  have hmap : ContinuousAt
      (fun q : LocalGapDatum N ↦
        (((1 - q.2.1 : ℝ) : ℂ), (q.2.2.2.2, q.2.2.2.1))) p := by
    fun_prop
  change ContinuousAt
    (fun q : LocalGapDatum N ↦
      vectorCanonicalSlope (((1 - q.2.1 : ℝ) : ℂ))
        q.2.2.2.2 q.2.2.2.1) p
  have hcont := (continuousAt_vectorCanonicalSlope (N := N)
      (r := ((1 - p.2.1 : ℝ) : ℂ)) (omega := p.2.2.2.2)
      (c := p.2.2.2.1) hr).comp (x := p) hmap
  change ContinuousAt
    (fun q : LocalGapDatum N ↦
      vectorCanonicalSlope (((1 - q.2.1 : ℝ) : ℂ))
        q.2.2.2.2 q.2.2.2.1) p at hcont
  exact hcont

lemma continuousAt_localInterpolatedCoeff {N : ℕ} {p : LocalGapDatum N}
    (hr : ((1 - p.mesh : ℝ) : ℂ) ≠ 0) :
    ContinuousAt (localInterpolatedCoeff (N := N)) p := by
  unfold localInterpolatedCoeff LocalGapDatum.coeff LocalGapDatum.offset
    LocalGapDatum.mesh
  apply (continuousAt_pi).2
  intro n
  change ContinuousAt
    (fun q : LocalGapDatum N ↦
      q.2.2.2.1 n + ((q.2.2.1 - q.2.1 : ℝ) : ℂ) *
        localCanonicalSlope q n) p
  have hc : ContinuousAt
    (fun q : LocalGapDatum N ↦ q.2.2.2.1 n) p :=
    (continuous_apply n).continuousAt.comp (x := p)
      continuous_snd.continuousAt.snd.snd.fst
  have hs : ContinuousAt
      (fun q : LocalGapDatum N ↦
        ((q.2.2.1 - q.2.1 : ℝ) : ℂ) * localCanonicalSlope q n) p := by
    exact (Complex.continuous_ofReal.continuousAt.comp (x := p)
      (continuous_snd.continuousAt.snd.fst.sub
        continuous_snd.continuousAt.fst)).mul
      ((continuous_apply n).continuousAt.comp (x := p)
        (continuousAt_localCanonicalSlope hr))
  exact hc.add hs

lemma continuousAt_localDiscreteGapRate {N : ℕ} {p : LocalGapDatum N}
    (hr : ((1 - p.mesh : ℝ) : ℂ) ≠ 0) :
    ContinuousAt (localDiscreteGapRate N) p := by
  apply continuousAt_vectorDeBrangesGapRate
  · unfold LocalGapDatum.time LocalGapDatum.offset
    fun_prop
  · exact continuousAt_localInterpolatedCoeff hr
  · exact continuousAt_localCanonicalSlope hr

lemma localDiscreteGapRate_zero_nonneg {N : ℕ}
    {t : ℝ} (ht : 0 ≤ t) (c : LoewnerCoeffVector N)
    {omega : ℂ} (homega : ‖omega‖ = 1) :
    0 ≤ localDiscreteGapRate N (t, 0, 0, c, omega) := by
  have homega0 : omega ≠ 0 := norm_ne_zero_iff.mp (by
    rw [homega]
    norm_num)
  have hslope : vectorCanonicalSlope 1 omega c =
      vectorDrivenVelocity (-omega) c := by
    funext n
    by_cases hn : (n : ℕ) = 0
    · have hnFin : n = ⟨0, Nat.zero_lt_succ N⟩ := Fin.ext hn
      subst n
      simp [vectorCanonicalSlope, vectorDrivenVelocity,
        canonicalLoewnerSlope, canonicalLogFactorSlope,
        drivenLoewnerVelocity, seriesPowSlopeCoeff]
    · exact vectorCanonicalSlope_one c homega0 n (Nat.pos_of_ne_zero hn)
  have hbase := vectorDeBrangesGapRate_driven_nonneg ht c
    (omega := -omega) (by simpa using homega)
  simpa [localDiscreteGapRate, LocalGapDatum.time, LocalGapDatum.mesh,
    LocalGapDatum.offset, LocalGapDatum.coeff, LocalGapDatum.omega,
    localInterpolatedCoeff, localCanonicalSlope, hslope] using hbase

noncomputable def localGapDomain
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N : ℕ) (T : ℝ) : Set (LocalGapDatum N) :=
  Icc 0 T ×ˢ
    (Icc 0 (1 / 2 : ℝ) ×ˢ
      (Icc 0 (1 / 2 : ℝ) ×ˢ
        (formalCoeffBody E₀ N ×ˢ sphere (0 : ℂ) 1)))

lemma isCompact_localGapDomain
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N : ℕ) (T : ℝ) :
    IsCompact (localGapDomain E₀ N T) := by
  exact isCompact_Icc.prod
    (isCompact_Icc.prod
      (isCompact_Icc.prod
        ((isCompact_formalCoeffBody E₀ N).prod
          (isCompact_sphere (0 : ℂ) 1))))

lemma continuousOn_localDiscreteGapRate
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N : ℕ) (T : ℝ) :
    ContinuousOn (localDiscreteGapRate N) (localGapDomain E₀ N T) := by
  intro p hp
  apply (continuousAt_localDiscreteGapRate ?_).continuousWithinAt
  have hmesh : p.mesh ≤ 1 / 2 := hp.2.1.2
  have hreal : 0 < 1 - p.mesh := by linarith
  exact_mod_cast hreal.ne'

lemma uniformContinuousOn_localDiscreteGapRate
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N : ℕ) (T : ℝ) :
    UniformContinuousOn (localDiscreteGapRate N) (localGapDomain E₀ N T) :=
  (isCompact_localGapDomain E₀ N T).uniformContinuousOn_of_continuous
    (continuousOn_localDiscreteGapRate E₀ N T)

lemma dist_localGapDatum_base_le {N : ℕ}
    (t h u : ℝ) (c : LoewnerCoeffVector N) (omega : ℂ)
    (hh : 0 ≤ h) (hu : 0 ≤ u) (huh : u ≤ h) :
    dist (t, h, u, c, omega) (t, 0, 0, c, omega) ≤ h := by
  simpa [Prod.dist_eq, abs_of_nonneg hh, abs_of_nonneg hu, huh] using hh

lemma exists_localDiscreteGapRate_lower_bound_delta
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N : ℕ) (T : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ (t h u : ℝ) (c : LoewnerCoeffVector N) (omega : ℂ),
      t ∈ Icc 0 T → h ∈ Icc 0 (1 / 2 : ℝ) → u ∈ Icc 0 h →
      c ∈ formalCoeffBody E₀ N → ‖omega‖ = 1 → h < delta →
      -eps < localDiscreteGapRate N (t, h, u, c, omega) := by
  rcases Metric.uniformContinuousOn_iff.mp
      (uniformContinuousOn_localDiscreteGapRate E₀ N T) eps heps with
    ⟨delta, hdelta, hclose⟩
  refine ⟨delta, hdelta, ?_⟩
  intro t h u c omega ht hh hu hc homega hhdelta
  have huHalf : u ∈ Icc 0 (1 / 2 : ℝ) := ⟨hu.1, hu.2.trans hh.2⟩
  have homegaSphere : omega ∈ sphere (0 : ℂ) 1 := by
    simpa [mem_sphere, dist_zero_right] using homega
  have hp : (t, h, u, c, omega) ∈ localGapDomain E₀ N T :=
    ⟨ht, hh, huHalf, hc, homegaSphere⟩
  have hp0 : (t, 0, 0, c, omega) ∈ localGapDomain E₀ N T := by
    refine ⟨ht, ?_, ?_, hc, homegaSphere⟩ <;> norm_num
  have hdist : dist (t, h, u, c, omega) (t, 0, 0, c, omega) < delta :=
    lt_of_le_of_lt (dist_localGapDatum_base_le t h u c omega hh.1 hu.1 hu.2)
      hhdelta
  have hrateClose := hclose _ hp _ hp0 hdist
  have hbase := localDiscreteGapRate_zero_nonneg ht.1 c homega
  rw [Real.dist_eq] at hrateClose
  have habs := abs_lt.mp hrateClose
  linarith

lemma hasDerivAt_vectorDeBrangesGap_interpolation {N : ℕ}
    (t h : ℝ) (c s : LoewnerCoeffVector N) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ vectorDeBrangesGap N (t + v)
        (c + (((v - h : ℝ) : ℂ) • s)))
      (vectorDeBrangesGapRate N (t + u)
        (c + (((u - h : ℝ) : ℂ) • s)) s) u := by
  have htau : ∀ k ∈ Finset.range N,
      HasDerivAt
        (fun v : ℝ ↦ explicitDeBrangesTau N (k + 1) (t + v))
        (explicitDeBrangesTauDot N (k + 1) (t + u)) u := by
    intro k hk
    have hderiv := (hasDerivAt_explicitDeBrangesTau N (k + 1) (t + u)).comp u
      ((hasDerivAt_id u).const_add t)
    simpa only [Function.comp_def, mul_one] using hderiv
  have hcoeff : ∀ k ∈ Finset.range N,
      HasDerivAt
        (fun v : ℝ ↦ coeffVectorToSeq
          (c + (((v - h : ℝ) : ℂ) • s)) (k + 1))
        (coeffVectorToSeq s (k + 1)) u := by
    intro k hk
    have hkN : k + 1 < N + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hk)
    have hcast : HasDerivAt (fun v : ℝ ↦ (v : ℂ)) 1 u :=
      (hasDerivAt_id u).ofReal_comp
    have hlinear := ((hcast.sub_const (h : ℂ)).mul_const
      (coeffVectorToSeq s (k + 1))).const_add
        (coeffVectorToSeq c (k + 1))
    simpa [coeffVectorToSeq, hkN] using hlinear
  have hgap := hasDerivAt_deBrangesGap
      (tau := fun k v ↦ explicitDeBrangesTau N k (t + v))
      (tauDot := fun k v ↦ explicitDeBrangesTauDot N k (t + v))
      (c := fun k v ↦ coeffVectorToSeq
        (c + (((v - h : ℝ) : ℂ) • s)) k)
      (cDot := fun k _ ↦ coeffVectorToSeq s k) htau hcoeff
  change HasDerivAt
    (fun v : ℝ ↦ vectorDeBrangesGap N (t + v)
      (c + (((v - h : ℝ) : ℂ) • s)))
    (vectorDeBrangesGapRate N (t + u)
      (c + (((u - h : ℝ) : ℂ) • s)) s) u at hgap
  exact hgap

lemma vectorCanonicalCoeff_real_step {N : ℕ}
    (c : LoewnerCoeffVector N) (h : ℝ) (omega : ℂ) (hh : h < 1) :
    vectorCanonicalCoeff (((1 - h : ℝ) : ℂ)) omega c =
      c + (((0 - h : ℝ) : ℂ) •
        vectorCanonicalSlope (((1 - h : ℝ) : ℂ)) omega c) := by
  have hrReal : 1 - h ≠ 0 := sub_ne_zero.mpr hh.ne'
  have hr : ((1 - h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrReal
  rw [vectorCanonicalCoeff_eq_add_slope c _ omega hr]
  have heq : (((1 - h : ℝ) : ℂ) - 1) = ((0 - h : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq]

lemma exists_vectorDeBrangesGap_canonical_step_delta
    (E₀ : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (N : ℕ) (T : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta > 0, ∀ (t h : ℝ) (c : LoewnerCoeffVector N) (omega : ℂ),
      t ∈ Icc 0 T → h ∈ Icc 0 (1 / 2 : ℝ) →
      c ∈ formalCoeffBody E₀ N → ‖omega‖ = 1 → h < delta →
      vectorDeBrangesGap N t
          (vectorCanonicalCoeff (((1 - h : ℝ) : ℂ)) omega c) ≤
        vectorDeBrangesGap N (t + h) c + eps * h := by
  rcases exists_localDiscreteGapRate_lower_bound_delta E₀ N T heps with
    ⟨delta, hdelta, hrate⟩
  refine ⟨delta, hdelta, ?_⟩
  intro t h c omega ht hh hc homega hhdelta
  let s := vectorCanonicalSlope (((1 - h : ℝ) : ℂ)) omega c
  let G : ℝ → ℝ := fun u ↦
    vectorDeBrangesGap N (t + u) (c + (((u - h : ℝ) : ℂ) • s))
  let Gplus : ℝ → ℝ := fun u ↦ G u + eps * u
  have hG (u : ℝ) : HasDerivAt G
      (localDiscreteGapRate N (t, h, u, c, omega)) u := by
    simpa [G, localDiscreteGapRate, localInterpolatedCoeff,
      localCanonicalSlope, LocalGapDatum.time, LocalGapDatum.mesh,
      LocalGapDatum.offset, LocalGapDatum.coeff, LocalGapDatum.omega, s] using
      hasDerivAt_vectorDeBrangesGap_interpolation t h c s u
  have hGplus (u : ℝ) : HasDerivAt Gplus
      (localDiscreteGapRate N (t, h, u, c, omega) + eps) u := by
    simpa only [Gplus] using
      (hG u).fun_add (hasDerivAt_const_mul eps)
  have hmono : MonotoneOn Gplus (Icc 0 h) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 h)
    · intro u hu
      exact (hGplus u).continuousAt.continuousWithinAt
    · intro u hu
      exact (hGplus u).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Icc 0 h := by
        have huIoo : u ∈ Ioo 0 h := by simpa only [interior_Icc] using hu
        exact ⟨huIoo.1.le, huIoo.2.le⟩
      rw [(hGplus u).deriv]
      exact le_of_lt (by
        have := hrate t h u c omega ht hh hu' hc homega hhdelta
        linarith)
  have hendpoint := hmono (show (0 : ℝ) ∈ Icc 0 h by exact ⟨le_rfl, hh.1⟩)
    (show h ∈ Icc 0 h by exact ⟨hh.1, le_rfl⟩) hh.1
  have hstep : vectorCanonicalCoeff (((1 - h : ℝ) : ℂ)) omega c =
      c + (((0 - h : ℝ) : ℂ) • s) := by
    simpa only [s] using vectorCanonicalCoeff_real_step c h omega (by linarith [hh.2])
  rw [hstep]
  simpa [Gplus, G] using hendpoint

end Submission
