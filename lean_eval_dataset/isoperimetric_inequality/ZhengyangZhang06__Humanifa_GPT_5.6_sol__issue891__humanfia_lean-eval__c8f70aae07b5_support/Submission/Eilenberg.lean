import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Submission.HausdorffNormalization

open LeanEval.Geometry
open MeasureTheory ENNReal Metric Set Filter
open scoped Topology

namespace Submission.Eilenberg

private structure FineCover (d n : ℕ) (F : Set (E n)) (ρ ε : ℝ≥0∞) where
  sets : ℕ → Set (E n)
  isCompact : ∀ i, IsCompact (sets i)
  covers : F ⊆ ⋃ i, sets i
  ediam_le : ∀ i, ediam (sets i) ≤ ρ
  rawCost_lt :
    (∑' i, ⨆ _ : (sets i).Nonempty, ediam (sets i) ^ (d : ℝ)) < μH[d] F + ε

private theorem exists_fineCover {d n : ℕ} {F : Set (E n)} {ρ ε : ℝ≥0∞}
    (hρ : 0 < ρ) (hρtop : ρ ≠ ⊤) (hε : ε ≠ 0) (hFtop : μH[d] F ≠ ⊤) :
    Nonempty (FineCover d n F ρ ε) := by
  let q : ℝ≥0∞ :=
    ⨅ (t : ℕ → Set (E n)) (_ : F ⊆ ⋃ i, t i) (_ : ∀ i, ediam (t i) ≤ ρ),
      ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (d : ℝ)
  have hq_le : q ≤ μH[d] F := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl)
  have hq_lt : q < μH[d] F + ε :=
    hq_le.trans_lt (ENNReal.lt_add_right hFtop hε)
  simp only [q, iInf_lt_iff] at hq_lt
  rcases hq_lt with ⟨t, ht_cover, ht_ediam, ht_cost⟩
  refine ⟨
    { sets := fun i ↦ closure (t i)
      isCompact := fun i ↦ ?_
      covers := ht_cover.trans (iUnion_mono fun i ↦ subset_closure)
      ediam_le := fun i ↦ by simpa only [Metric.ediam_closure] using ht_ediam i
      rawCost_lt := by
        simpa only [Metric.ediam_closure, closure_nonempty_iff] using ht_cost }⟩
  have hi_top : ediam (t i) ≠ ⊤ := ne_top_of_le_ne_top hρtop (ht_ediam i)
  exact (Metric.isBounded_iff_ediam_ne_top.mpr hi_top).isCompact_closure

private noncomputable def fineCover {d n : ℕ} (F : Set (E n)) (ρ ε : ℝ≥0∞)
    (hρ : 0 < ρ) (hρtop : ρ ≠ ⊤) (hε : ε ≠ 0) (hFtop : μH[d] F ≠ ⊤) :
    FineCover d n F ρ ε :=
  Classical.choice (exists_fineCover hρ hρtop hε hFtop)

private theorem lintegral_fiber_le_raw {d n : ℕ} (hd : 1 ≤ d) (F : Set (E n))
    (p : E n → E d) (hp : LipschitzWith 1 p) (hFtop : μH[d] F ≠ ⊤) :
    ∫⁻ y, μH[0] (F ∩ p ⁻¹' {y}) ≤
      (HausdorffNormalization.rawScale d : ℝ≥0∞)⁻¹ * μH[d] F := by
  classical
  let ρ : ℕ → ℝ≥0∞ := fun k ↦ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hρpos : ∀ k, 0 < ρ k := fun k ↦ by simp [ρ]
  have hρtop : ∀ k, ρ k ≠ ⊤ := fun k ↦ by simp [ρ]
  let ε : ℕ → ℝ≥0∞ := fun k ↦ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hεne : ∀ k, ε k ≠ 0 := fun k ↦ by simp [ε]
  let C : (k : ℕ) → FineCover d n F (ρ k) (ε k) :=
    fun k ↦ fineCover F (ρ k) (ε k) (hρpos k) (hρtop k) (hεne k) hFtop
  let g : ℕ → E d → ℝ≥0∞ := fun k y ↦
    ∑' i, (p '' (C k).sets i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y
  have hgmeas : ∀ k, Measurable (g k) := by
    intro k
    apply Measurable.tsum
    intro i
    apply Measurable.indicator measurable_const
    exact ((C k).isCompact i).image hp.continuous |>.measurableSet
  have hfiber : ∀ y, μH[0] (F ∩ p ⁻¹' {y}) ≤ liminf (fun k ↦ g k y) atTop := by
    intro y
    let I : ℕ → Type := fun k ↦ {i : ℕ // ((C k).sets i ∩ p ⁻¹' {y}).Nonempty}
    let t : ∀ k, I k → Set (E n) := fun k i ↦ (C k).sets i ∩ p ⁻¹' {y}
    have htend : Tendsto ρ atTop (nhds 0) := by
      simpa [ρ] using (tendsto_add_atTop_iff_nat 1).mpr ENNReal.tendsto_inv_nat_nhds_zero
    have hdiam : ∀ k i, ediam (t k i) ≤ ρ k := by
      intro k i
      exact (ediam_mono inter_subset_left).trans ((C k).ediam_le i)
    have hcover : ∀ k, F ∩ p ⁻¹' {y} ⊆ ⋃ i, t k i := by
      intro k x hx
      rcases mem_iUnion.mp ((C k).covers hx.1) with ⟨i, hi⟩
      apply mem_iUnion.mpr
      exact ⟨⟨i, ⟨x, hi, hx.2⟩⟩, hi, hx.2⟩
    refine (Measure.hausdorffMeasure_le_liminf_tsum 0 (F ∩ p ⁻¹' {y}) ρ htend t
      (Eventually.of_forall hdiam) (Eventually.of_forall hcover)).trans_eq ?_
    apply Filter.liminf_congr
    filter_upwards [] with k
    simp only [g, t, I, ENNReal.rpow_zero]
    calc
      (∑' _i : {i : ℕ // ((C k).sets i ∩ p ⁻¹' {y}).Nonempty}, (1 : ℝ≥0∞)) =
          ∑' i : ℕ, {i : ℕ | ((C k).sets i ∩ p ⁻¹' {y}).Nonempty}.indicator
            (fun _ ↦ (1 : ℝ≥0∞)) i :=
        tsum_subtype {i : ℕ | ((C k).sets i ∩ p ⁻¹' {y}).Nonempty}
          (fun _ ↦ (1 : ℝ≥0∞))
      _ = ∑' i : ℕ, (p '' (C k).sets i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
        apply tsum_congr
        intro i
        simp only [Set.indicator, mem_setOf_eq, mem_image]
        by_cases hi : ((C k).sets i ∩ p ⁻¹' {y}).Nonempty
        · rw [if_pos hi, if_pos]
          rcases hi with ⟨x, hx, hxy⟩
          exact ⟨x, hx, by simpa using hxy⟩
        · rw [if_neg hi, if_neg]
          rintro ⟨x, hx, hxy⟩
          exact hi ⟨x, hx, by simpa using hxy⟩
  have hgint : ∀ k, ∫⁻ y, g k y ≤
      (HausdorffNormalization.rawScale d : ℝ≥0∞)⁻¹ * (μH[d] F + ε k) := by
    intro k
    simp only [g]
    rw [lintegral_tsum]
    · calc
        (∑' i, ∫⁻ y, (p '' (C k).sets i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) =
            ∑' i, volume (p '' (C k).sets i) := by
              apply tsum_congr
              intro i
              rw [lintegral_indicator
                (((C k).isCompact i).image hp.continuous).measurableSet, setLIntegral_one]
        _ ≤ ∑' i, (HausdorffNormalization.rawScale d : ℝ≥0∞)⁻¹ *
              ⨆ _ : ((C k).sets i).Nonempty, ediam ((C k).sets i) ^ (d : ℝ) := by
            apply ENNReal.tsum_le_tsum
            intro i
            by_cases hi : ((C k).sets i).Nonempty
            · rw [ciSup_pos hi]
              have himage : (p '' (C k).sets i).Nonempty := hi.image p
              have himage_bdd : Bornology.IsBounded (p '' (C k).sets i) :=
                (((C k).isCompact i).image hp.continuous).isBounded
              refine (HausdorffNormalization.volume_le_rawScale_inv_mul_ediam_rpow hd
                himage himage_bdd).trans ?_
              gcongr
              simpa using hp.ediam_image_le ((C k).sets i)
            · letI : IsEmpty ((C k).sets i).Nonempty := ⟨hi⟩
              simp only [ciSup_of_empty]
              simp [not_nonempty_iff_eq_empty.mp hi]
        _ = (HausdorffNormalization.rawScale d : ℝ≥0∞)⁻¹ *
              ∑' i, ⨆ _ : ((C k).sets i).Nonempty, ediam ((C k).sets i) ^ (d : ℝ) := by
            rw [ENNReal.tsum_mul_left]
        _ ≤ (HausdorffNormalization.rawScale d : ℝ≥0∞)⁻¹ * (μH[d] F + ε k) := by
            gcongr
            exact (C k).rawCost_lt.le
    · intro i
      apply Measurable.aemeasurable
      apply Measurable.indicator measurable_const
      exact ((C k).isCompact i).image hp.continuous |>.measurableSet
  calc
    ∫⁻ y, μH[0] (F ∩ p ⁻¹' {y}) ≤ ∫⁻ y, liminf (fun k ↦ g k y) atTop :=
      lintegral_mono hfiber
    _ ≤ liminf (fun k ↦ ∫⁻ y, g k y) atTop := lintegral_liminf_le hgmeas
    _ ≤ liminf (fun k ↦
        (HausdorffNormalization.rawScale d : ℝ≥0∞)⁻¹ * (μH[d] F + ε k)) atTop :=
      liminf_le_liminf (Eventually.of_forall hgint)
    _ = (HausdorffNormalization.rawScale d : ℝ≥0∞)⁻¹ * μH[d] F := by
      apply Filter.Tendsto.liminf_eq
      have hε0 : Tendsto ε atTop (nhds 0) := by
        simpa [ε] using (tendsto_add_atTop_iff_nat 1).mpr ENNReal.tendsto_inv_nat_nhds_zero
      have hadd : Tendsto (fun k ↦ μH[d] F + ε k) atTop (nhds (μH[d] F)) := by
        simpa using tendsto_const_nhds.add hε0
      exact ENNReal.Tendsto.const_mul hadd (Or.inr (by
        simpa using HausdorffNormalization.rawScale_ne_zero d hd))

theorem lintegral_hausdorffMeasure_zero_fiber_le {d n : ℕ} (hd : 1 ≤ d)
    (F : Set (E n)) (p : E n → E d) (hp : LipschitzWith 1 p) :
    ∫⁻ y, μH[0] (F ∩ p ⁻¹' {y}) ≤ μHE[d] F := by
  rw [HausdorffNormalization.euclideanHausdorffMeasure_eq_rawScale_inv_smul_hausdorffMeasure
    d hd, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.coe_inv (HausdorffNormalization.rawScale_ne_zero d hd)]
  by_cases hFtop : μH[d] F = ⊤
  · simp [hFtop, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top]
  · exact lintegral_fiber_le_raw hd F p hp hFtop

end Submission.Eilenberg
