import ChallengeDeps
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Hausdorff
import Submission.Isodiametric

open LeanEval.Geometry
open MeasureTheory ENNReal Metric Set Filter
open scoped Topology

namespace Submission.HausdorffNormalization

noncomputable def ballConstant (d : ℕ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ d / volume (closedBall (0 : E d) 1)

noncomputable def rawScale (d : ℕ) : NNReal := (ballConstant d).toNNReal

private theorem ball_volume_pos (d : ℕ) (hd : 1 ≤ d) :
    0 < volume (closedBall (0 : E d) 1) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_lt hd)
  rw [EuclideanSpace.volume_closedBall]
  positivity

private theorem ball_volume_ne_top (d : ℕ) (hd : 1 ≤ d) :
    volume (closedBall (0 : E d) 1) ≠ ⊤ := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_lt hd)
  rw [EuclideanSpace.volume_closedBall]
  finiteness

private theorem ballConstant_pos (d : ℕ) (hd : 1 ≤ d) : 0 < ballConstant d := by
  unfold ballConstant
  exact ENNReal.div_pos (pow_ne_zero d two_ne_zero) (ball_volume_ne_top d hd)

private theorem ballConstant_ne_top (d : ℕ) (hd : 1 ≤ d) : ballConstant d ≠ ⊤ := by
  unfold ballConstant
  exact ENNReal.div_ne_top (by finiteness) (ball_volume_pos d hd).ne'

@[simp]
theorem coe_rawScale (d : ℕ) (hd : 1 ≤ d) : (rawScale d : ℝ≥0∞) = ballConstant d := by
  exact ENNReal.coe_toNNReal (ballConstant_ne_top d hd)

theorem rawScale_ne_zero (d : ℕ) (hd : 1 ≤ d) : rawScale d ≠ 0 := by
  intro h
  have : (rawScale d : ℝ≥0∞) = 0 := by simp [h]
  rw [coe_rawScale d hd] at this
  exact (ballConstant_pos d hd).ne' this

private structure FineBallCover (d : ℕ) (s : Set (E d)) (R : ℝ) (ε : ℝ≥0∞) where
  centers : Set (E d)
  radius : E d → ℝ
  centers_countable : centers.Countable
  radius_pos : ∀ x : centers, 0 < radius x
  radius_lt : ∀ x : centers, radius x < R
  covers : s ⊆ ⋃ x : centers, closedBall x (radius x)
  volume_sum_le : (∑' x : centers, volume (closedBall (x : E d) (radius x))) ≤ volume s + ε

private theorem exists_fineBallCover (d : ℕ) (s : Set (E d)) (R : ℝ) (hR : 0 < R)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) : Nonempty (FineBallCover d s R ε) := by
  let f : E d → Set ℝ := fun _ ↦ Ioo 0 R
  have hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ hδ
    refine ⟨min R δ / 2, ?_⟩
    have hmin : 0 < min R δ := lt_min hR hδ
    constructor
    · exact ⟨half_pos hmin, (half_lt_self hmin).trans_le (min_le_left _ _)⟩
    · exact ⟨half_pos hmin, (half_lt_self hmin).trans_le (min_le_right _ _)⟩
  rcases Besicovitch.exists_closedBall_covering_tsum_measure_le volume hε f s hf with
    ⟨t, r, ht_count, hts, htr, hcover, hsum⟩
  exact ⟨
    { centers := t
      radius := r
      centers_countable := ht_count
      radius_pos := fun x ↦ (htr x x.property).1
      radius_lt := fun x ↦ (htr x x.property).2
      covers := by simpa only [iUnion_subtype] using hcover
      volume_sum_le := hsum }⟩

private noncomputable def fineBallCover (d : ℕ) (s : Set (E d)) (R : ℝ) (hR : 0 < R)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) : FineBallCover d s R ε :=
  Classical.choice (exists_fineBallCover d s R hR ε hε)

private instance fineBallCover_countable (d : ℕ) (s : Set (E d)) (R : ℝ) (hR : 0 < R)
    (ε : ℝ≥0∞) (hε : ε ≠ 0) : Countable (fineBallCover d s R hR ε hε).centers :=
  (fineBallCover d s R hR ε hε).centers_countable.to_subtype

private theorem ediam_cover_ball_le {d : ℕ} {s : Set (E d)} {R : ℝ} {hR : 0 < R}
    {ε : ℝ≥0∞} {hε : ε ≠ 0} (x : (fineBallCover d s R hR ε hε).centers) :
    ediam (closedBall (x : E d) ((fineBallCover d s R hR ε hε).radius x))
      ≤ ENNReal.ofReal (2 * R) := by
  apply ediam_le_of_forall_dist_le
  intro y hy z hz
  calc
    dist y z ≤ dist y x + dist z x := dist_triangle_right _ _ _
    _ ≤ (fineBallCover d s R hR ε hε).radius x +
        (fineBallCover d s R hR ε hε).radius x :=
      add_le_add hy hz
    _ ≤ R + R := add_le_add
      ((fineBallCover d s R hR ε hε).radius_lt x).le
      ((fineBallCover d s R hR ε hε).radius_lt x).le
    _ = 2 * R := by ring

private theorem ediam_pow_le_ballConstant_mul_volume {d : ℕ} (hd : 1 ≤ d)
    {x : E d} {r : ℝ} (hr : 0 < r) :
    ediam (closedBall x r) ^ (d : ℝ) ≤ ballConstant d * volume (closedBall x r) := by
  have hed : ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) := by
    apply ediam_le_of_forall_dist_le
    intro y hy z hz
    calc
      dist y z ≤ dist y x + dist z x := dist_triangle_right _ _ _
      _ ≤ r + r := add_le_add hy hz
      _ = 2 * r := by ring
  calc
    ediam (closedBall x r) ^ (d : ℝ) ≤ ENNReal.ofReal (2 * r) ^ (d : ℝ) := by
      gcongr
    _ = ballConstant d * volume (closedBall x r) := by
      rw [ENNReal.rpow_natCast, Measure.addHaar_closedBall' volume x hr.le,
        finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_pow hr.le]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ)), ENNReal.ofReal_ofNat,
        mul_pow]
      unfold ballConstant
      rw [ENNReal.div_eq_inv_mul]
      calc
        (2 : ℝ≥0∞) ^ d * ENNReal.ofReal r ^ d =
            (volume (closedBall (0 : E d) 1))⁻¹ *
              volume (closedBall (0 : E d) 1) *
                ((2 : ℝ≥0∞) ^ d * ENNReal.ofReal r ^ d) := by
          rw [ENNReal.inv_mul_cancel (ball_volume_pos d hd).ne' (ball_volume_ne_top d hd), one_mul]
        _ = (volume (closedBall (0 : E d) 1))⁻¹ * (2 : ℝ≥0∞) ^ d *
              (ENNReal.ofReal r ^ d * volume (closedBall (0 : E d) 1)) := by
          ac_rfl

/-- Raw `d`-dimensional Hausdorff measure on Euclidean `d`-space is at most the
isodiametric normalization of volume. -/
theorem hausdorffMeasure_le_ballConstant_smul_volume (d : ℕ) (hd : 1 ≤ d)
    (s : Set (E d)) :
    μH[d] s ≤ ballConstant d * volume s := by
  classical
  by_cases hs_top : volume s = ⊤
  · rw [hs_top, mul_top (ballConstant_pos d hd).ne']
    exact le_top
  let R : ℕ → ℝ := fun k ↦ ((k + 1 : ℕ) : ℝ)⁻¹
  have hR : ∀ k, 0 < R k := fun k ↦ by positivity
  let ε : ℕ → ℝ≥0∞ := fun k ↦ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hε : ∀ k, ε k ≠ 0 := fun k ↦ by simp [ε]
  let C := fun k ↦ fineBallCover d s (R k) (hR k) (ε k) (hε k)
  let t : ∀ k, C k |>.centers → Set (E d) :=
    fun k x ↦ closedBall (x : E d) ((C k).radius x)
  have hdiam : ∀ k x, ediam (t k x) ≤ ENNReal.ofReal (2 * R k) := by
    intro k x
    exact ediam_cover_ball_le x
  have hcover : ∀ k, s ⊆ ⋃ x, t k x := fun k ↦ (C k).covers
  have hr_tendsto : Tendsto (fun k ↦ ENNReal.ofReal (2 * R k)) atTop (𝓝 0) := by
    have hR0 : Tendsto R atTop (𝓝 0) := by
      simpa [R, Nat.cast_add, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0))
    have htwo : Tendsto (fun k ↦ (2 : ℝ) * R k) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hR0 :
        Tendsto (fun k ↦ (2 : ℝ) * R k) atTop (𝓝 ((2 : ℝ) * 0)))
    simpa using ENNReal.tendsto_ofReal htwo
  refine (Measure.hausdorffMeasure_le_liminf_tsum (d : ℝ) s
    (fun k ↦ ENNReal.ofReal (2 * R k)) hr_tendsto t
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)).trans ?_
  have hcost : ∀ k, (∑' x, ediam (t k x) ^ (d : ℝ)) ≤
      ballConstant d * (volume s + ε k) := by
    intro k
    calc
      (∑' x, ediam (t k x) ^ (d : ℝ)) ≤
          ∑' x, ballConstant d * volume (t k x) := by
        exact ENNReal.tsum_le_tsum fun x ↦
          ediam_pow_le_ballConstant_mul_volume hd ((C k).radius_pos x)
      _ = ballConstant d * ∑' x, volume (t k x) := by
        rw [ENNReal.tsum_mul_left]
      _ ≤ ballConstant d * (volume s + ε k) := by
        gcongr
        exact (C k).volume_sum_le
  calc
    liminf (fun k ↦ ∑' x, ediam (t k x) ^ (d : ℝ)) atTop
        ≤ liminf (fun k ↦ ballConstant d * (volume s + ε k)) atTop :=
      liminf_le_liminf (Eventually.of_forall hcost)
    _ = ballConstant d * volume s := by
      apply Filter.Tendsto.liminf_eq
      have hε0 : Tendsto ε atTop (𝓝 0) := by
        simpa [ε] using
          (tendsto_add_atTop_iff_nat 1).mpr ENNReal.tendsto_inv_nat_nhds_zero
      have hadd : Tendsto (fun k ↦ volume s + ε k) atTop (𝓝 (volume s)) := by
        simpa using tendsto_const_nhds.add hε0
      exact ENNReal.Tendsto.const_mul hadd (Or.inr (ballConstant_ne_top d hd))

private theorem ballConstant_mul_volume_half_ball {d : ℕ} (hd : 1 ≤ d) {a : ℝ}
    (ha : 0 ≤ a) :
    ballConstant d * volume (closedBall (0 : E d) (a / 2)) = ENNReal.ofReal a ^ d := by
  rw [Measure.addHaar_closedBall' volume (0 : E d) (div_nonneg ha (by positivity)),
    finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_pow (div_nonneg ha (by positivity)),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  unfold ballConstant
  calc
    ((2 : ℝ≥0∞) ^ d / volume (closedBall (0 : E d) 1)) *
          ((ENNReal.ofReal a / 2) ^ d * volume (closedBall (0 : E d) 1)) =
        (ENNReal.ofReal a / 2) ^ d *
          (((2 : ℝ≥0∞) ^ d / volume (closedBall (0 : E d) 1)) *
            volume (closedBall (0 : E d) 1)) := by
      ac_rfl
    _ = (ENNReal.ofReal a / 2) ^ d * (2 : ℝ≥0∞) ^ d := by
      rw [ENNReal.div_mul_cancel (ball_volume_pos d hd).ne' (ball_volume_ne_top d hd)]
    _ = ENNReal.ofReal a ^ d := by
      rw [ENNReal.div_eq_inv_mul, mul_pow, ← ENNReal.inv_pow]
      calc
        ((2 : ℝ≥0∞) ^ d)⁻¹ * ENNReal.ofReal a ^ d * (2 : ℝ≥0∞) ^ d =
            (((2 : ℝ≥0∞) ^ d)⁻¹ * (2 : ℝ≥0∞) ^ d) * ENNReal.ofReal a ^ d := by
          ac_rfl
        _ = ENNReal.ofReal a ^ d := by
          rw [ENNReal.inv_mul_cancel (pow_ne_zero d two_ne_zero) (by finiteness), one_mul]

/-- The isodiametric inequality gives the converse comparison between volume and raw
Hausdorff measure. -/
theorem ballConstant_smul_volume_le_hausdorffMeasure (d : ℕ) (hd : 1 ≤ d) :
    ballConstant d • (volume : Measure (E d)) ≤ μH[d] := by
  apply Measure.le_hausdorffMeasure (d : ℝ) _ 1 zero_lt_one
  intro s hsdiam
  rw [Measure.smul_apply, smul_eq_mul]
  by_cases hs_empty : s = ∅
  · simp [hs_empty]
  have hs_nonempty : s.Nonempty := nonempty_iff_ne_empty.mpr hs_empty
  have hs_ediam : ediam s ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hsdiam
  have hs_bounded : Bornology.IsBounded s := Metric.isBounded_iff_ediam_ne_top.mpr hs_ediam
  calc
    ballConstant d * volume s ≤
        ballConstant d * volume (closedBall (0 : E d) (Metric.diam s / 2)) := by
      exact mul_le_mul le_rfl
        (Isodiametric.volume_le_closedBall_half_diam hd hs_nonempty hs_bounded)
        (by positivity) (by positivity)
    _ = ENNReal.ofReal (Metric.diam s) ^ d :=
      ballConstant_mul_volume_half_ball hd diam_nonneg
    _ = ediam s ^ (d : ℝ) := by
      rw [ENNReal.rpow_natCast, Metric.diam, ENNReal.ofReal_toReal hs_ediam]

/-- Exact normalization of raw Hausdorff measure on its model Euclidean space. -/
theorem hausdorffMeasure_eq_ballConstant_smul_volume (d : ℕ) (hd : 1 ≤ d) :
    (μH[d] : Measure (E d)) = ballConstant d • volume := by
  apply le_antisymm
  · intro s
    simpa only [Measure.smul_apply, smul_eq_mul] using
      hausdorffMeasure_le_ballConstant_smul_volume d hd s
  · exact ballConstant_smul_volume_le_hausdorffMeasure d hd

theorem hausdorffMeasure_eq_rawScale_smul_volume (d : ℕ) (hd : 1 ≤ d) :
    (μH[d] : Measure (E d)) = rawScale d • (volume : Measure (E d)) := by
  rw [hausdorffMeasure_eq_ballConstant_smul_volume d hd]
  ext s
  simp only [Measure.smul_apply, smul_eq_mul]
  change ballConstant d * volume s = (rawScale d : ℝ≥0∞) * volume s
  rw [coe_rawScale d hd]

theorem addHaarScalarFactor_eq_rawScale_inv (d : ℕ) (hd : 1 ≤ d) :
    Measure.addHaarScalarFactor (volume : Measure (E d)) μH[d] = (rawScale d)⁻¹ := by
  simp only [hausdorffMeasure_eq_rawScale_smul_volume d hd]
  have h := Measure.mul_addHaarScalarFactor_smul
    (volume : Measure (E d)) volume (rawScale_ne_zero d hd)
  apply eq_inv_of_mul_eq_one_left
  simpa only [Measure.addHaarScalarFactor_self, mul_one, mul_comm] using h

theorem euclideanHausdorffMeasure_eq_rawScale_inv_smul_hausdorffMeasure
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (d : ℕ) (hd : 1 ≤ d) :
    (μHE[d] : Measure X) = (rawScale d)⁻¹ • (μH[d] : Measure X) := by
  rw [Measure.euclideanHausdorffMeasure_def, addHaarScalarFactor_eq_rawScale_inv d hd]

/-- Sharp isodiametric estimate in the normalization used by `μHE`. -/
theorem volume_le_rawScale_inv_mul_ediam_rpow {d : ℕ} (hd : 1 ≤ d)
    {s : Set (E d)} (hs : s.Nonempty) (hs_bounded : Bornology.IsBounded s) :
    volume s ≤ (rawScale d : ℝ≥0∞)⁻¹ * ediam s ^ (d : ℝ) := by
  have hCpos := ballConstant_pos d hd
  have hCtop := ballConstant_ne_top d hd
  calc
    volume s ≤ volume (closedBall (0 : E d) (Metric.diam s / 2)) :=
      Isodiametric.volume_le_closedBall_half_diam hd hs hs_bounded
    _ = (ballConstant d)⁻¹ *
          (ballConstant d * volume (closedBall (0 : E d) (Metric.diam s / 2))) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hCpos.ne' hCtop, one_mul]
    _ = (ballConstant d)⁻¹ * ENNReal.ofReal (Metric.diam s) ^ d := by
      rw [ballConstant_mul_volume_half_ball hd diam_nonneg]
    _ = (rawScale d : ℝ≥0∞)⁻¹ * ediam s ^ (d : ℝ) := by
      rw [coe_rawScale d hd, ENNReal.rpow_natCast, Metric.diam,
        ENNReal.ofReal_toReal hs_bounded.ediam_ne_top]

end Submission.HausdorffNormalization
