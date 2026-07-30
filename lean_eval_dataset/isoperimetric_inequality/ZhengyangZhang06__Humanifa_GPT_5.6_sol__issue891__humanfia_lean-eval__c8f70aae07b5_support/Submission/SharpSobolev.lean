import ChallengeDeps
import Submission.ParallelVolume

open LeanEval.Geometry
open MeasureTheory ENNReal Metric Set Function Filter
open scoped Topology ENNReal

namespace Submission.SharpSobolev

noncomputable section

/-- The jointly parametrized thickening of the strict superlevel sets of `f`. -/
def thickSuperlevel {n : ℕ} (f : E n → ℝ) (r : ℝ) : Set (ℝ × E n) :=
  {p | p.2 ∈ thickening r {x | p.1 < f x}}

/-- The jointly parametrized strict superlevel sets of `f`. -/
def superlevelPair {n : ℕ} (f : E n → ℝ) : Set (ℝ × E n) :=
  {p | p.1 < f p.2}

/-- The part gained when all strict superlevel sets in `(0, 1)` are thickened. -/
def superlevelLayer {n : ℕ} (f : E n → ℝ) (r : ℝ) : Set (ℝ × E n) :=
  (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (E n))) ∩
    (thickSuperlevel f r \ superlevelPair f)

theorem isOpen_thickSuperlevel {n : ℕ} {f : E n → ℝ} (_hf : Continuous f) (r : ℝ) :
    IsOpen (thickSuperlevel f r) := by
  rw [show thickSuperlevel f r = ⋃ y : E n, Iio (f y) ×ˢ ball y r by
    ext p
    simp [thickSuperlevel, mem_thickening_iff, dist_comm]]
  exact isOpen_iUnion fun y ↦ isOpen_Iio.prod (isOpen_ball : IsOpen (ball y r))

theorem isOpen_superlevelPair {n : ℕ} {f : E n → ℝ} (hf : Continuous f) :
    IsOpen (superlevelPair f) := by
  exact isOpen_lt continuous_fst (hf.comp continuous_snd)

theorem measurableSet_superlevelLayer {n : ℕ} {f : E n → ℝ}
    (hf : Continuous f) (r : ℝ) : MeasurableSet (superlevelLayer f r) := by
  exact (measurableSet_Ioo.prod MeasurableSet.univ).inter
    ((isOpen_thickSuperlevel hf r).measurableSet.diff
      (isOpen_superlevelPair hf).measurableSet)

theorem superlevelLayer_section_left {n : ℕ} (f : E n → ℝ) (r t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    Prod.mk t ⁻¹' superlevelLayer f r =
      thickening r {x | t < f x} \ {x | t < f x} := by
  ext x
  simp [superlevelLayer, thickSuperlevel, superlevelPair, ht]

theorem superlevelLayer_section_left_of_notMem {n : ℕ} (f : E n → ℝ) (r t : ℝ)
    (ht : t ∉ Ioo (0 : ℝ) 1) : Prod.mk t ⁻¹' superlevelLayer f r = ∅ := by
  ext x
  simp [superlevelLayer, ht]

private theorem rpow_inv_nat_pow {n : ℕ} (hn : 1 ≤ n) (a : ℝ≥0∞) :
    (a ^ (n : ℝ)⁻¹) ^ n = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [inv_mul_cancel₀ hnR, ENNReal.rpow_one]

private theorem rpow_inv_nat_pow_pred {n : ℕ} (hn : 1 ≤ n) (a : ℝ≥0∞) :
    (a ^ (n : ℝ)⁻¹) ^ (n - 1) = a ^ (((n : ℝ) - 1) / n) := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  rw [Nat.cast_sub hn, Nat.cast_one, div_eq_mul_inv, mul_comm]

/-- The first-order consequence of Brunn--Minkowski used on every superlevel set. -/
theorem level_increment {n : ℕ} (hn : 2 ≤ n) {S : Set (E n)}
    (hS : MeasurableSet S) {r : ℝ} (hr : 0 < r) :
    volume S + (n : ℝ≥0∞) * ENNReal.ofReal r *
        volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
        volume S ^ (((n : ℝ) - 1) / n)
      ≤ volume (thickening r S) := by
  by_cases hSne : S.Nonempty
  · have hbm := ParallelVolume.brunn_minkowski_thickening_unit_ball (by omega) hSne hS hr
    have hbm_pow :
        (volume S ^ (n : ℝ)⁻¹ +
            ENNReal.ofReal r * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹) ^ n
          ≤ volume (thickening r S) := by
      calc
        _ ≤ (volume (thickening r S) ^ (n : ℝ)⁻¹) ^ n := by gcongr
        _ = _ := rpow_inv_nat_pow (by omega) _
    have hbernoulli :
        (volume S ^ (n : ℝ)⁻¹) ^ n +
            (n : ℝ≥0∞) * (volume S ^ (n : ℝ)⁻¹) ^ (n - 1) *
              (ENNReal.ofReal r * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹)
          ≤ (volume S ^ (n : ℝ)⁻¹ +
            ENNReal.ofReal r * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹) ^ n := by
      apply pow_add_mul_le_add_pow_of_sq_nonneg <;> positivity
    rw [rpow_inv_nat_pow (by omega), rpow_inv_nat_pow_pred (by omega)] at hbernoulli
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hbernoulli.trans hbm_pow
  · have hS0 : S = ∅ := not_nonempty_iff_eq_empty.mp hSne
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn
    have halpha : 0 < ((n : ℝ) - 1) / n :=
      div_pos (sub_pos.mpr hnR) (by positivity)
    simp [hS0, ENNReal.zero_rpow_of_pos halpha]

/-- The Brunn--Minkowski increment on a superlevel set that contains a fixed plateau. -/
theorem plateau_increment_le_layer {n : ℕ} (hn : 2 ≤ n) {f : E n → ℝ}
    (hf : Continuous f) (hfcompact : HasCompactSupport f) {K : Set (E n)}
    (hK : ∀ x ∈ K, f x = 1) {r t : ℝ} (hr : 0 < r) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (n : ℝ≥0∞) * ENNReal.ofReal r *
        volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
        volume K ^ (((n : ℝ) - 1) / n) ≤
      volume (Prod.mk t ⁻¹' superlevelLayer f r) := by
  let S : Set (E n) := {x | t < f x}
  have hSopen : IsOpen S := isOpen_lt continuous_const hf
  have hS : MeasurableSet S := hSopen.measurableSet
  have hStsupport : S ⊆ tsupport f := by
    intro x hx
    apply subset_closure
    simp only [mem_support, ne_eq]
    intro hzero
    change t < f x at hx
    rw [hzero] at hx
    exact (not_lt_of_ge ht.1.le) hx
  have hSfinite : volume S ≠ ⊤ :=
    (hfcompact.isBounded.subset hStsupport).measure_lt_top.ne
  have hKS : K ⊆ S := by
    intro x hx
    change t < f x
    rw [hK x hx]
    exact ht.2
  have hinc := level_increment hn hS hr
  have hpow : volume K ^ (((n : ℝ) - 1) / n) ≤
      volume S ^ (((n : ℝ) - 1) / n) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact ENNReal.rpow_le_rpow (measure_mono hKS)
      (div_nonneg (sub_nonneg.mpr hnR) (Nat.cast_nonneg n))
  have hadd : volume S +
      (n : ℝ≥0∞) * ENNReal.ofReal r *
        volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
        volume K ^ (((n : ℝ) - 1) / n) ≤
      volume (thickening r S) := by
    calc
      _ ≤ volume S +
          (n : ℝ≥0∞) * ENNReal.ofReal r *
            volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
            volume S ^ (((n : ℝ) - 1) / n) := by gcongr
      _ ≤ _ := hinc
  have hSsub : S ⊆ thickening r S := by
    intro x hx
    exact mem_thickening_iff.mpr ⟨x, hx, by simpa using hr⟩
  have hvol : volume (thickening r S) =
      volume S + volume (thickening r S \ S) := by
    symm
    calc
      volume S + volume (thickening r S \ S) = volume (S ∪ thickening r S) :=
        measure_add_sdiff hS.nullMeasurableSet _
      _ = volume (thickening r S) := by rw [union_eq_right.mpr hSsub]
  rw [hvol] at hadd
  rw [superlevelLayer_section_left f r t ht]
  exact (ENNReal.add_le_add_iff_left hSfinite).mp hadd

/-- Integrating the preceding pointwise increment over all levels in `(0,1)`. -/
theorem plateau_increment_le_prod_volume {n : ℕ} (hn : 2 ≤ n) {f : E n → ℝ}
    (hf : Continuous f) (hfcompact : HasCompactSupport f) {K : Set (E n)}
    (hK : ∀ x ∈ K, f x = 1) {r : ℝ} (hr : 0 < r) :
    (n : ℝ≥0∞) * ENNReal.ofReal r *
        volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
        volume K ^ (((n : ℝ) - 1) / n) ≤
      ((volume : Measure ℝ).prod (volume : Measure (E n))) (superlevelLayer f r) := by
  let C : ℝ≥0∞ := (n : ℝ≥0∞) * ENNReal.ofReal r *
    volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
    volume K ^ (((n : ℝ) - 1) / n)
  have hLayer : MeasurableSet (superlevelLayer f r) :=
    measurableSet_superlevelLayer hf r
  have hsection : Measurable fun t : ℝ ↦
      volume (Prod.mk t ⁻¹' superlevelLayer f r) :=
    measurable_measure_prodMk_left hLayer
  calc
    (n : ℝ≥0∞) * ENNReal.ofReal r *
          volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
          volume K ^ (((n : ℝ) - 1) / n) =
        ∫⁻ _t in Ioo (0 : ℝ) 1, C := by
          simp [C, Real.volume_Ioo]
    _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
        volume (Prod.mk t ⁻¹' superlevelLayer f r) := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro t ht
      exact plateau_increment_le_layer hn hf hfcompact hK hr ht
    _ ≤ ∫⁻ t, volume (Prod.mk t ⁻¹' superlevelLayer f r) :=
      setLIntegral_le_lintegral _ _
    _ = ((volume : Measure ℝ).prod (volume : Measure (E n)))
        (superlevelLayer f r) := (Measure.prod_apply hLayer).symm

theorem superlevelLayer_section_right_subset {n : ℕ} {f : E n → ℝ}
    {g : E n → ℝ} {r : ℝ}
    (hslope : ∀ x y, dist x y < r → f y ≤ f x + r * g x) (x : E n) :
    (fun t : ℝ ↦ (t, x)) ⁻¹' superlevelLayer f r ⊆ Ico (f x) (f x + r * g x) := by
  intro t ht
  change ((t ∈ Ioo (0 : ℝ) 1 ∧ x ∈ (univ : Set (E n))) ∧
    (x ∈ thickening r {y | t < f y} ∧ ¬t < f x)) at ht
  rcases ht with ⟨_ht01, hthick, hnot⟩
  refine ⟨le_of_not_gt hnot, ?_⟩
  rcases mem_thickening_iff.mp hthick with ⟨y, hty, hxy⟩
  exact hty.trans_le (hslope x y hxy)

theorem volume_superlevelLayer_section_right_le {n : ℕ} {f : E n → ℝ}
    {g : E n → ℝ} {r : ℝ}
    (hslope : ∀ x y, dist x y < r → f y ≤ f x + r * g x) (x : E n) :
    volume ((fun t : ℝ ↦ (t, x)) ⁻¹' superlevelLayer f r) ≤
      ENNReal.ofReal (r * g x) := by
  calc
    volume ((fun t : ℝ ↦ (t, x)) ⁻¹' superlevelLayer f r) ≤
        volume (Ico (f x) (f x + r * g x)) :=
      measure_mono (superlevelLayer_section_right_subset hslope x)
    _ = ENNReal.ofReal (r * g x) := by simp [Real.volume_Ico]

/-- A pointwise upper slope bounds the product volume swept out by all superlevel sets. -/
theorem prod_volume_superlevelLayer_le {n : ℕ} {f : E n → ℝ}
    (hf : Continuous f) {g : E n → ℝ} (hg : Measurable g) {r : ℝ} (hr : 0 ≤ r)
    (hslope : ∀ x y, dist x y < r → f y ≤ f x + r * g x) :
    ((volume : Measure ℝ).prod (volume : Measure (E n))) (superlevelLayer f r) ≤
      ENNReal.ofReal r * ∫⁻ x, ENNReal.ofReal (g x) := by
  have hLayer : MeasurableSet (superlevelLayer f r) :=
    measurableSet_superlevelLayer hf r
  have hg' : Measurable fun x ↦ ENNReal.ofReal (g x) := ENNReal.measurable_ofReal.comp hg
  calc
    ((volume : Measure ℝ).prod (volume : Measure (E n))) (superlevelLayer f r) =
        ∫⁻ x, volume ((fun t : ℝ ↦ (t, x)) ⁻¹' superlevelLayer f r) :=
      Measure.prod_apply_symm hLayer
    _ ≤ ∫⁻ x, ENNReal.ofReal (r * g x) :=
      lintegral_mono fun x ↦ volume_superlevelLayer_section_right_le hslope x
    _ = ∫⁻ x, ENNReal.ofReal r * ENNReal.ofReal (g x) := by
      congr 1
      funext x
      rw [ENNReal.ofReal_mul hr]
    _ = ENNReal.ofReal r * ∫⁻ x, ENNReal.ofReal (g x) :=
      lintegral_const_mul _ hg'

/-- A compactly supported `C¹` function has, at a sufficiently small scale, an upper slope
whose integral differs from the integral of `‖Df‖` by an arbitrarily small constant on one
fixed bounded neighborhood of the support. -/
theorem exists_integrable_upper_slope {n : ℕ} {f : E n → ℝ}
    (hf : ContDiff ℝ 1 f) (hfcompact : HasCompactSupport f) {eta : ℝ} (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : E n → ℝ, Measurable g ∧
      (∀ x y, dist x y < r → f y ≤ f x + r * g x) ∧
      (∫⁻ x, ENNReal.ofReal (g x)) ≤
        (∫⁻ x, ‖fderiv ℝ f x‖ₑ) + ENNReal.ofReal eta *
          volume (thickening 1 (tsupport f)) := by
  classical
  have hDfcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hDfunif : UniformContinuous (fderiv ℝ f) :=
    (hfcompact.fderiv ℝ).uniformContinuous_of_continuous hDfcont
  rcases (Metric.uniformContinuous_iff.mp hDfunif) eta heta with
    ⟨delta, hdelta, hmod⟩
  let r : ℝ := min delta 1 / 2
  have hmin : 0 < min delta 1 := lt_min hdelta zero_lt_one
  have hr : 0 < r := half_pos hmin
  have hrdelta : r < delta :=
    (half_lt_self hmin).trans_le (min_le_left delta 1)
  have hrone : r < 1 :=
    (half_lt_self hmin).trans_le (min_le_right delta 1)
  let T : Set (E n) := thickening 1 (tsupport f)
  let g : E n → ℝ := fun x ↦ if x ∈ T then ‖fderiv ℝ f x‖ + eta else 0
  have hTopen : IsOpen T := Metric.isOpen_thickening
  have hg : Measurable g := by
    exact Measurable.ite hTopen.measurableSet
      (hDfcont.norm.measurable.add_const eta) measurable_const
  have hslope : ∀ x y, dist x y < r → f y ≤ f x + r * g x := by
    intro x y hxy
    by_cases hxT : x ∈ T
    · have hbound : ∀ z ∈ segment ℝ x y,
          ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ f x‖ + eta := by
        intro z hz
        have hxz : dist x z < delta := by
          calc
            dist x z ≤ dist x y := by
              simpa only [mem_closedBall, dist_comm] using
                (segment_subset_closedBall_left x y hz)
            _ < r := hxy
            _ < delta := hrdelta
        have hclose : dist (fderiv ℝ f x) (fderiv ℝ f z) < eta := hmod hxz
        have hsub : ‖fderiv ℝ f z - fderiv ℝ f x‖ < eta := by
          simpa only [dist_eq_norm, norm_sub_rev] using hclose
        calc
          ‖fderiv ℝ f z‖ =
              ‖(fderiv ℝ f z - fderiv ℝ f x) + fderiv ℝ f x‖ := by
            rw [sub_add_cancel]
          _ ≤ ‖fderiv ℝ f z - fderiv ℝ f x‖ + ‖fderiv ℝ f x‖ :=
            norm_add_le _ _
          _ ≤ ‖fderiv ℝ f x‖ + eta := by linarith
      have hmv : ‖f y - f x‖ ≤
          (‖fderiv ℝ f x‖ + eta) * ‖y - x‖ :=
        Convex.norm_image_sub_le_of_norm_fderiv_le
          (fun z _hz ↦ (hf.differentiable one_ne_zero).differentiableAt)
          hbound (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
      have hC : 0 ≤ ‖fderiv ℝ f x‖ + eta := by positivity
      have hdiff : f y - f x ≤ r * (‖fderiv ℝ f x‖ + eta) := by
        calc
          f y - f x ≤ ‖f y - f x‖ := by
            simpa only [Real.norm_eq_abs] using le_abs_self (f y - f x)
          _ ≤ (‖fderiv ℝ f x‖ + eta) * ‖y - x‖ := hmv
          _ ≤ (‖fderiv ℝ f x‖ + eta) * r := by
            gcongr
            simpa only [dist_eq_norm, norm_sub_rev] using hxy.le
          _ = r * (‖fderiv ℝ f x‖ + eta) := mul_comm _ _
      simp only [g, hxT, if_true]
      linarith
    · have hfx : f x = 0 := by
        by_contra hfx
        apply hxT
        apply mem_thickening_iff.mpr
        refine ⟨x, subset_closure ?_, by norm_num⟩
        simpa only [mem_support] using hfx
      have hfy : f y = 0 := by
        by_contra hfy
        apply hxT
        apply mem_thickening_iff.mpr
        refine ⟨y, subset_closure ?_, hxy.trans hrone⟩
        simpa only [mem_support] using hfy
      simp [g, hxT, hfx, hfy]
  have hpoint : ∀ x, ENNReal.ofReal (g x) ≤
      ‖fderiv ℝ f x‖ₑ + T.indicator (fun _ ↦ ENNReal.ofReal eta) x := by
    intro x
    by_cases hxT : x ∈ T
    · simp only [g, hxT, if_true, indicator_of_mem]
      rw [ENNReal.ofReal_add (norm_nonneg _) heta.le, ofReal_norm]
    · simp [g, hxT]
  have hnormmeas : Measurable fun x ↦ ‖fderiv ℝ f x‖ₑ := hDfcont.enorm.measurable
  refine ⟨r, hr, g, hg, hslope, ?_⟩
  calc
    (∫⁻ x, ENNReal.ofReal (g x)) ≤
        ∫⁻ x, ‖fderiv ℝ f x‖ₑ + T.indicator (fun _ ↦ ENNReal.ofReal eta) x :=
      lintegral_mono hpoint
    _ = (∫⁻ x, ‖fderiv ℝ f x‖ₑ) +
        ∫⁻ x, T.indicator (fun _ ↦ ENNReal.ofReal eta) x := by
      rw [lintegral_add_left hnormmeas]
    _ = (∫⁻ x, ‖fderiv ℝ f x‖ₑ) + ENNReal.ofReal eta * volume T := by
      rw [lintegral_indicator hTopen.measurableSet]
      simp only [lintegral_const, Measure.restrict_apply_univ]
    _ = _ := rfl

/-- Sharp `L¹` Sobolev inequality in the only form needed here: a compactly supported `C¹`
function which equals one on `K` pays at least the isoperimetric constant times
`volume K ^ ((n-1)/n)` in total gradient. -/
theorem sharp_sobolev_of_plateau {n : ℕ} (hn : 2 ≤ n) {f : E n → ℝ}
    (hf : ContDiff ℝ 1 f) (hfcompact : HasCompactSupport f) {K : Set (E n)}
    (hK : ∀ x ∈ K, f x = 1) :
    (n : ℝ≥0∞) * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
        volume K ^ (((n : ℝ) - 1) / n) ≤
      ∫⁻ x, ‖fderiv ℝ f x‖ₑ := by
  let D : ℝ≥0∞ := ∫⁻ x, ‖fderiv ℝ f x‖ₑ
  let T : Set (E n) := thickening 1 (tsupport f)
  have hTfinite : volume T ≠ ⊤ :=
    (hfcompact.isBounded.thickening : Bornology.IsBounded T).measure_lt_top.ne
  refine ENNReal.le_of_forall_pos_le_add fun eps heps hDfinite ↦ ?_
  let M : NNReal := (volume T).toNNReal
  have hM : (M : ℝ≥0∞) = volume T := ENNReal.coe_toNNReal hTfinite
  let eta : NNReal := eps / (M + 1)
  have hetaNN : 0 < eta := div_pos heps (by positivity)
  have heta : 0 < (eta : ℝ) := by exact_mod_cast hetaNN
  rcases exists_integrable_upper_slope hf hfcompact heta with
    ⟨r, hr, g, hg, hslope, hgint⟩
  have hlower := plateau_increment_le_prod_volume hn hf.continuous hfcompact hK hr
  have hupper := prod_volume_superlevelLayer_le hf.continuous hg hr.le hslope
  have hchain := hlower.trans hupper
  have hr0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  have hrtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel :
      (n : ℝ≥0∞) * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
          volume K ^ (((n : ℝ) - 1) / n) ≤
        ∫⁻ x, ENNReal.ofReal (g x) := by
    apply (ENNReal.mul_le_mul_iff_left hr0 hrtop).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hchain
  have herrNN : eta * M ≤ eps := by
    calc
      eta * M ≤ eta * (M + 1) :=
        mul_le_mul_right (le_add_of_nonneg_right zero_le_one) eta
      _ = eps := by
        dsimp only [eta]
        exact div_mul_cancel₀ eps (by positivity)
  have herr : ENNReal.ofReal (eta : ℝ) * volume T ≤ (eps : ℝ≥0∞) := by
    rw [← hM, ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_mul]
    exact_mod_cast herrNN
  calc
    (n : ℝ≥0∞) * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
          volume K ^ (((n : ℝ) - 1) / n) ≤
        ∫⁻ x, ENNReal.ofReal (g x) := hcancel
    _ ≤ D + ENNReal.ofReal (eta : ℝ) * volume T := by simpa [D, T] using hgint
    _ ≤ D + eps := by gcongr

theorem measurable_volume_superlevel {n : ℕ} (f : E n → ℝ) :
    Measurable fun t : ℝ ↦ volume {x | t < f x} := by
  apply Antitone.measurable
  intro a b hab
  exact measure_mono fun x hx ↦ hab.trans_lt hx

/-- Layer cake restricted to `(0,1)` for a nonnegative function bounded by one. -/
theorem lintegral_volume_superlevel_Ioo {n : ℕ} {f : E n → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (hf : AEStronglyMeasurable f) :
    ∫⁻ t in Ioo (0 : ℝ) 1, volume {x | t < f x} =
      ∫⁻ x, ENNReal.ofReal (f x) := by
  rw [lintegral_eq_lintegral_meas_lt volume (Eventually.of_forall hf0) hf.aemeasurable]
  let V : ℝ → ℝ≥0∞ := fun t ↦ volume {x | t < f x}
  have hV : Measurable V := measurable_volume_superlevel f
  have htail : ∫⁻ t in Ici (1 : ℝ), V t = 0 := by
    rw [setLIntegral_eq_zero_iff measurableSet_Ici hV]
    filter_upwards with t ht
    have hempty : {x | t < f x} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun h ↦ (not_lt_of_ge (hf1 x)) (ht.trans_lt h)
    simp [V, hempty]
  calc
    ∫⁻ t in Ioo (0 : ℝ) 1, V t =
        (∫⁻ t in Ioo (0 : ℝ) 1, V t) + ∫⁻ t in Ici (1 : ℝ), V t := by rw [htail, add_zero]
    _ = ∫⁻ t in Ioo (0 : ℝ) 1 ∪ Ici (1 : ℝ), V t := by
      rw [lintegral_union measurableSet_Ici]
      simp only [disjoint_left, mem_Ioo, mem_Ici]
      exact fun _ h0 h1 ↦ (not_lt_of_ge h1) h0.2
    _ = ∫⁻ t in Ioi (0 : ℝ), V t := by
      rw [Ioo_union_Ici_eq_Ioi zero_lt_one]

end

end Submission.SharpSobolev
