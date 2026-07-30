import Submission.RiemannReachable
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Filter Function Metric Set
open scoped Topology

namespace Submission

noncomputable def NormalizedDiskEmbedding.phaseFactor
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) : ℂ :=
  (deriv E.toFun 0)⁻¹ * (‖deriv E.toFun 0‖ : ℂ)

noncomputable def NormalizedDiskEmbedding.phaseNormalize
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) (z : ℂ) : ℂ :=
  E.phaseFactor * E z

lemma NormalizedDiskEmbedding.norm_phaseFactor
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    ‖E.phaseFactor‖ = 1 := by
  have hd : 0 < ‖deriv E.toFun 0‖ := norm_pos_iff.mpr E.deriv_ne_zero
  rw [phaseFactor, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ hd.ne'

lemma NormalizedDiskEmbedding.phaseFactor_mul_deriv
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    E.phaseFactor * deriv E.toFun 0 = (‖deriv E.toFun 0‖ : ℂ) := by
  rw [phaseFactor]
  field_simp [E.deriv_ne_zero]

noncomputable def NormalizedDiskEmbedding.phaseNormalizedEmbedding
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0 where
  toFun := E.phaseNormalize
  differentiableOn := by
    exact (differentiableOn_const (c := E.phaseFactor)).mul E.differentiableOn
  mapsTo := by
    intro z hz
    rw [mem_ball_zero_iff, phaseNormalize, norm_mul, E.norm_phaseFactor, one_mul]
    simpa [mem_ball_zero_iff] using E.mapsTo hz
  injOn := by
    intro z hz w hw hzw
    apply E.injOn hz hw
    exact mul_left_cancel₀ (norm_ne_zero_iff.mp (by rw [E.norm_phaseFactor]; norm_num)) hzw
  map_base := by simp [phaseNormalize, E.map_base]
  deriv_ne_zero := by
    have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
    have hEAt := E.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hzero)
    change deriv (fun z => E.phaseFactor * E z) 0 ≠ 0
    rw [(hEAt.hasDerivAt.const_mul E.phaseFactor).deriv,
      E.phaseFactor_mul_deriv]
    exact_mod_cast norm_pos_iff.mpr E.deriv_ne_zero |>.ne'

lemma NormalizedDiskEmbedding.deriv_phaseNormalizedEmbedding
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    deriv E.phaseNormalizedEmbedding.toFun 0 = (‖deriv E.toFun 0‖ : ℂ) := by
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hEAt := E.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hzero)
  change deriv (fun z => E.phaseFactor * E z) 0 = _
  rw [(hEAt.hasDerivAt.const_mul E.phaseFactor).deriv]
  exact E.phaseFactor_mul_deriv

lemma NormalizedDiskEmbedding.deriv_norm_le_one
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0) :
    ‖deriv E.toFun 0‖ ≤ 1 := by
  apply Complex.norm_deriv_le_one_of_mapsTo_ball E.differentiableOn _ zero_lt_one
  intro z hz
  rw [E.map_base]
  exact ball_subset_closedBall (E.mapsTo hz)

lemma NormalizedDiskEmbedding.phaseNormalize_eq_id_of_deriv_norm_eq_one
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (hderiv : ‖deriv E.toFun 0‖ = 1) :
    Set.EqOn E.phaseNormalize id (ball (0 : ℂ) 1) := by
  let H := E.phaseNormalizedEmbedding
  have hmaps : MapsTo H.toFun (ball (0 : ℂ) 1) (closedBall (H 0) 1) := by
    intro z hz
    rw [H.map_base]
    exact ball_subset_closedBall (H.mapsTo hz)
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hdslope : ‖dslope H.toFun 0 0‖ = 1 := by
    rw [dslope_same, E.deriv_phaseNormalizedEmbedding, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), hderiv]
  have haffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    H.differentiableOn hmaps hzero (by simpa using hdslope)
  intro z hz
  change H z = id z
  rw [haffine hz, H.map_base, dslope_same, E.deriv_phaseNormalizedEmbedding,
    hderiv]
  simp [id_eq]

lemma NormalizedDiskEmbedding.norm_dslope_lt_one_of_deriv_norm_lt_one
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (hderiv : ‖deriv E.toFun 0‖ < 1) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖dslope E.toFun 0 z‖ < 1 := by
  have hmaps : MapsTo E.toFun (ball (0 : ℂ) 1) (closedBall (E 0) 1) := by
    intro w hw
    rw [E.map_base]
    exact ball_subset_closedBall (E.mapsTo hw)
  have hle := Complex.norm_dslope_le_div_of_mapsTo_ball E.differentiableOn hmaps hz
  simp only [one_div] at hle
  have hleOne : ‖dslope E.toFun 0 z‖ ≤ 1 := by simpa using hle
  apply lt_of_le_of_ne hleOne
  intro heq
  have heqOne : ‖dslope E.toFun 0 z‖ = 1 := heq
  have haffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    E.differentiableOn hmaps hz (by simpa using heqOne)
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hderivEq := haffine.deriv isOpen_ball hzero
  have hrhs : deriv
      (fun w : ℂ => E 0 + (w - 0) • dslope E.toFun 0 z) 0 =
        dslope E.toFun 0 z := by
    convert (hasDerivAt_id 0).sub_const 0 |>.const_smul (dslope E.toFun 0 z)
      |>.const_add (E 0) |>.deriv using 1 <;> simp [smul_eq_mul, mul_comm]
  rw [hrhs] at hderivEq
  have : ‖deriv E.toFun 0‖ = 1 := by rw [hderivEq, heqOne]
  linarith

lemma norm_diskMobiusInv_sub_one_le
    {a r : ℝ} {w : ℂ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hr1 : r < 1) (hw : ‖w‖ ≤ r) :
    ‖diskMobiusInv (a : ℂ) w - 1‖ ≤ 2 * (1 - a) / (1 - r) := by
  have haMem : (a : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ha0]
    exact ha1
  have hwMem : w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact hw.trans_lt hr1
  have hstar : starRingEnd ℂ (a : ℂ) = (a : ℂ) := by
    apply Complex.ext <;> simp
  have hden := diskMobiusInv_denominator_ne_zero haMem hwMem
  have hden' : 1 + (a : ℂ) * w ≠ 0 := by
    simpa only [hstar] using hden
  have hden'' : 1 + w * (a : ℂ) ≠ 0 := by
    simpa only [mul_comm] using hden'
  have heq :
      diskMobiusInv (a : ℂ) w - 1 =
        (((1 - a : ℝ) : ℂ) * (w - 1)) /
          (1 + starRingEnd ℂ (a : ℂ) * w) := by
    rw [diskMobiusInv, hstar]
    push_cast
    field_simp [hden', hden'']
    ring
  rw [heq, norm_div, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sub_nonneg.mpr ha1.le)]
  have hwOne : ‖w‖ ≤ 1 := hw.trans hr1.le
  have hnum : ‖w - 1‖ ≤ 2 := by
    calc
      ‖w - 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by norm_num; linarith
  have hmul : ‖starRingEnd ℂ (a : ℂ) * w‖ ≤ r := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg ha0]
    exact (mul_le_of_le_one_left (norm_nonneg w) ha1.le).trans hw
  have hdenLower : 1 - r ≤ ‖1 + starRingEnd ℂ (a : ℂ) * w‖ := by
    calc
      1 - r ≤ 1 - ‖starRingEnd ℂ (a : ℂ) * w‖ := by linarith
      _ ≤ ‖1 + starRingEnd ℂ (a : ℂ) * w‖ := by
        have h := norm_sub_norm_le (1 : ℂ) (-(starRingEnd ℂ (a : ℂ) * w))
        rw [norm_one, norm_neg, sub_neg_eq_add] at h
        exact h
  have hnumMul :
      (1 - a) * ‖w - 1‖ ≤ 2 * (1 - a) := by
    calc
      (1 - a) * ‖w - 1‖ ≤ (1 - a) * 2 :=
        mul_le_mul_of_nonneg_left hnum (sub_nonneg.mpr ha1.le)
      _ = 2 * (1 - a) := by ring
  apply div_le_div₀
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr ha1.le)
  · exact hnumMul
  · exact sub_pos.mpr hr1
  · exact hdenLower

lemma NormalizedDiskEmbedding.phaseNormalize_sub_id_norm_le
    (E : NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0)
    (hderiv : ‖deriv E.toFun 0‖ < 1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖E.phaseNormalize z - z‖ ≤
      r * (2 * (1 - ‖deriv E.toFun 0‖) / (1 - r)) := by
  let H := E.phaseNormalizedEmbedding
  let a : ℝ := ‖deriv E.toFun 0‖
  let q : ℂ → ℂ := dslope H.toFun 0
  let W : ℂ → ℂ := fun w => diskMobius (a : ℂ) (q w)
  have ha0 : 0 ≤ a := norm_nonneg _
  have ha1 : a < 1 := hderiv
  have haMem : (a : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ha0]
    exact ha1
  have hzBall : z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact hz.trans_lt hr1
  have hqDiff : DifferentiableOn ℂ q (ball (0 : ℂ) 1) := by
    exact (Complex.differentiableOn_dslope
      (isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))).2 H.differentiableOn
  have hqMem : MapsTo q (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro w hw
    rw [mem_ball_zero_iff]
    exact H.norm_dslope_lt_one_of_deriv_norm_lt_one (by
      rw [E.deriv_phaseNormalizedEmbedding, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _)]
      exact hderiv) hw
  have hWDiff : DifferentiableOn ℂ W (ball (0 : ℂ) 1) := by
    intro w hw
    have hcomp := (hasDerivAt_diskMobius haMem (hqMem hw)).comp w
      ((hqDiff w hw).differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    change DifferentiableWithinAt ℂ (diskMobius (a : ℂ) ∘ q) (ball 0 1) w
    exact hcomp.differentiableAt.differentiableWithinAt
  have hWMap : MapsTo W (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    intro w hw
    exact ball_subset_closedBall (diskMobius_mapsTo_unitBall haMem (hqMem hw))
  have hqZero : q 0 = (a : ℂ) := by
    dsimp only [q]
    rw [dslope_same, E.deriv_phaseNormalizedEmbedding]
  have hWZero : W 0 = 0 := by simp [W, hqZero, diskMobius]
  have hWNorm : ‖W z‖ ≤ r := by
    exact (Complex.norm_le_norm_of_mapsTo_ball hWDiff hWMap hWZero
      (hz.trans_lt hr1)).trans hz
  have hqEq : q z = diskMobiusInv (a : ℂ) (W z) := by
    exact (diskMobiusInv_diskMobius haMem (hqMem hzBall)).symm
  have hqBound : ‖q z - 1‖ ≤ 2 * (1 - a) / (1 - r) := by
    rw [hqEq]
    exact norm_diskMobiusInv_sub_one_le ha0 ha1 hr1 hWNorm
  rw [phaseNormalize]
  change ‖H z - z‖ ≤ _
  rw [show H z - z = z * (q z - 1) by
    dsimp only [q]
    by_cases hz0 : z = 0
    · simp [hz0, H.map_base]
    · rw [dslope_of_ne _ hz0]
      rw [slope_def_module]
      rw [H.map_base]
      simp only [sub_zero, smul_eq_mul]
      field_simp [hz0]
      ]
  rw [norm_mul]
  exact mul_le_mul hz hqBound (norm_nonneg _) hr0

lemma tendstoLocallyUniformlyOn_phaseNormalize_of_deriv_norm_tendsto_one
    {E : ℕ → NormalizedDiskEmbedding (ball (0 : ℂ) 1) 0}
    (hE : Tendsto (fun j => ‖deriv (E j).toFun 0‖) atTop (nhds 1)) :
    TendstoLocallyUniformlyOn (fun j => (E j).phaseNormalize) id atTop
      (ball (0 : ℂ) 1) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball]
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · rw [tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun j z hz => hz.elim
  obtain ⟨z₀, hz₀, hz₀max⟩ :=
    hK.exists_isMaxOn hKne continuous_norm.continuousOn
  let r := ‖z₀‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := by
    simpa only [r, mem_ball_zero_iff] using hKU hz₀
  have hKr : ∀ z ∈ K, ‖z‖ ≤ r := by
    intro z hz
    exact hz₀max hz
  let error : ℝ → ℝ := fun a => r * (2 * (1 - a) / (1 - r))
  have herrorContinuous : ContinuousAt error 1 := by
    dsimp only [error]
    fun_prop
  have herror : Tendsto (fun j => error ‖deriv (E j).toFun 0‖)
      atTop (nhds 0) := by
    have ht := herrorContinuous.tendsto.comp hE
    have hone : error 1 = 0 := by simp [error]
    rw [hone] at ht
    apply ht.congr'
    exact Eventually.of_forall fun j => by rfl
  rw [tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 herror).2 ε hε] with j hj z hz
  rw [dist_comm, dist_eq_norm, id_eq]
  by_cases heq : ‖deriv (E j).toFun 0‖ = 1
  · rw [(E j).phaseNormalize_eq_id_of_deriv_norm_eq_one heq (hKU hz)]
    simpa using hε
  · have hlt : ‖deriv (E j).toFun 0‖ < 1 :=
      lt_of_le_of_ne (E j).deriv_norm_le_one heq
    exact ((E j).phaseNormalize_sub_id_norm_le hlt hr0 hr1 (hKr z hz)).trans_lt hj

end Submission
