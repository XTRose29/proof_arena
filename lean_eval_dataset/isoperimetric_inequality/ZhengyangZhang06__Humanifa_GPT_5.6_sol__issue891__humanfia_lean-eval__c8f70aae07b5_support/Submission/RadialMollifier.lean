import ChallengeDeps
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open LeanEval.Geometry
open MeasureTheory Metric Set Function Filter
open scoped Convolution Topology ENNReal RealInnerProductSpace

namespace Submission.RadialMollifier

noncomputable section

/-- The concrete radial bump used below.  We use the explicit inner-product-space bump base,
rather than the arbitrary bump selected by the `HasContDiffBump` typeclass, because radial
monotonicity is essential in the slicing argument. -/
def raw {n : ℕ} (a b : ℝ) (x : E n) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace (E n)).toFun (b / a) (a⁻¹ • x)

theorem raw_eq_smoothTransition {n : ℕ} {a b : ℝ} (ha : 0 < a) (x : E n) :
    raw a b x = Real.smoothTransition ((b - ‖x‖) / (b - a)) := by
  simp only [raw, ContDiffBumpBase.ofInnerProductSpace, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos ha]
  congr 1
  field_simp

theorem raw_nonneg {n : ℕ} (a b : ℝ) (x : E n) : 0 ≤ raw a b x :=
  (ContDiffBumpBase.ofInnerProductSpace (E n)).mem_Icc _ _ |>.1

theorem raw_le_one {n : ℕ} (a b : ℝ) (x : E n) : raw a b x ≤ 1 :=
  (ContDiffBumpBase.ofInnerProductSpace (E n)).mem_Icc _ _ |>.2

theorem raw_eq_one_of_norm_le {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x : E n} (hx : ‖x‖ ≤ a) : raw a b x = 1 := by
  apply (ContDiffBumpBase.ofInnerProductSpace (E n)).eq_one (b / a)
  · exact (one_lt_div ha).2 hab
  simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha, ← div_eq_inv_mul,
    div_le_one ha] using hx

theorem raw_eq_zero_of_le_norm {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x : E n} (hx : b ≤ ‖x‖) : raw a b x = 0 := by
  rw [raw_eq_smoothTransition ha, Real.smoothTransition.zero_iff_nonpos]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_nonneg.mpr hab.le)

theorem support_raw {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    support (raw a b : E n → ℝ) = ball 0 b := by
  ext x
  rw [mem_support, Ne, raw_eq_smoothTransition ha, Real.smoothTransition.zero_iff_nonpos,
    not_le, mem_ball, dist_zero_right]
  simp [sub_pos.mpr hab]

theorem hasCompactSupport_raw {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    HasCompactSupport (raw a b : E n → ℝ) := by
  rw [HasCompactSupport, tsupport, support_raw ha hab,
    closure_ball (0 : E n) (ne_of_gt (ha.trans hab))]
  exact isCompact_closedBall _ _

theorem contDiff_raw {n : ℕ∞} {d : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ n (raw a b : E d → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  change ContDiffAt ℝ n
    (uncurry (ContDiffBumpBase.ofInnerProductSpace (E d)).toFun ∘
      fun x : E d ↦ (b / a, a⁻¹ • x)) x
  refine (((ContDiffBumpBase.ofInnerProductSpace (E d)).smooth.contDiffAt ?_).of_le
    (mod_cast le_top)).comp x ?_
  · exact prod_mem_nhds (Ioi_mem_nhds ((one_lt_div ha).2 hab)) univ_mem
  · fun_prop

theorem continuous_raw {d : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Continuous (raw a b : E d → ℝ) :=
  (contDiff_raw (n := 0) ha hab).continuous

theorem integrable_raw {d : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable (raw a b : E d → ℝ) :=
  (continuous_raw ha hab).integrable_of_hasCompactSupport (hasCompactSupport_raw ha hab)

/-- Total mass of the unnormalised radial bump. -/
def mass (n : ℕ) (a b : ℝ) : ℝ := ∫ x : E n, raw a b x

theorem mass_pos {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < mass n a b := by
  unfold mass
  refine (integral_pos_iff_support_of_nonneg (fun x ↦ raw_nonneg a b x)
    (integrable_raw ha hab)).2 ?_
  rw [support_raw ha hab]
  exact measure_ball_pos volume 0 (ha.trans hab)

/-- The radial bump normalised to have integral one. -/
def kernel {n : ℕ} (a b : ℝ) (x : E n) : ℝ := raw a b x / mass n a b

theorem kernel_nonneg {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (x : E n) : 0 ≤ kernel a b x :=
  div_nonneg (raw_nonneg a b x) (mass_pos ha hab).le

theorem integral_kernel {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫ x : E n, kernel a b x = 1 := by
  simp_rw [kernel, div_eq_mul_inv]
  rw [integral_mul_const]
  exact mul_inv_cancel₀ (mass_pos ha hab).ne'

theorem contDiff_kernel {m : ℕ∞} {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ m (kernel a b : E n → ℝ) := by
  exact (contDiff_raw ha hab).div_const (mass n a b)

theorem support_kernel {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    support (kernel a b : E n → ℝ) = ball 0 b := by
  change support (fun x : E n ↦ raw a b x / mass n a b) = _
  rw [support_div, support_raw ha hab, support_const (mass_pos ha hab).ne', inter_univ]

theorem hasCompactSupport_kernel {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    HasCompactSupport (kernel a b : E n → ℝ) := by
  rw [HasCompactSupport, tsupport, support_kernel ha hab,
    closure_ball (0 : E n) (ne_of_gt (ha.trans hab))]
  exact isCompact_closedBall _ _

theorem kernel_zero_of_le_norm {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x : E n} (hx : b ≤ ‖x‖) : kernel a b x = 0 := by
  rw [kernel, raw_eq_zero_of_le_norm ha hab hx, zero_div]

theorem kernel_zero_of_mem_compl_ball {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x : E n} (hx : x ∉ ball (0 : E n) b) : kernel a b x = 0 := by
  apply kernel_zero_of_le_norm ha hab
  simpa only [mem_ball, dist_zero_right, not_lt] using hx

theorem kernel_at_zero {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    kernel a b (0 : E n) = (mass n a b)⁻¹ := by
  rw [kernel, raw_eq_one_of_norm_le ha hab (by simpa using ha.le), one_div]

theorem kernel_le_peak {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (x : E n) : kernel a b x ≤ (mass n a b)⁻¹ := by
  rw [kernel, div_eq_mul_inv]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (raw_le_one a b x)
    (inv_nonneg.2 (mass_pos (n := n) ha hab).le)

theorem measure_closedBall_le_mass {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (volume (closedBall (0 : E n) a)).toReal ≤ mass n a b := by
  calc
    (volume (closedBall (0 : E n) a)).toReal =
        ∫ x in closedBall (0 : E n) a, (1 : ℝ) := by simp [measureReal_def]
    _ = ∫ x in closedBall (0 : E n) a, raw a b x := by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro x hx
      exact (raw_eq_one_of_norm_le ha hab (by simpa [mem_closedBall] using hx)).symm
    _ ≤ ∫ x : E n, raw a b x := by
      exact setIntegral_le_integral (integrable_raw ha hab)
        (Eventually.of_forall fun x ↦ raw_nonneg a b x)
    _ = mass n a b := rfl

/-- The signed integral of the derivative of a nonnegative compactly supported unimodal function
over an arbitrary measurable set is bounded by its peak.  The point is that the positive and
negative parts lie on opposite sides of the mode; their *difference*, rather than their sum, is
being estimated. -/
theorem abs_setIntegral_deriv_le_peak {h : ℝ → ℝ} {U : Set ℝ} {c : ℝ}
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h) (hU : MeasurableSet U)
    (hleft : ∀ t ≤ c, 0 ≤ deriv h t) (hright : ∀ t, c < t → deriv h t ≤ 0) :
    |∫ t in U, deriv h t| ≤ h c := by
  have hd_int : Integrable (deriv h) :=
    (hh.continuous_deriv le_rfl).integrable_of_hasCompactSupport hhc.deriv
  let L := U ∩ Iic c
  let R := U ∩ Ioi c
  have hL : MeasurableSet L := hU.inter measurableSet_Iic
  have hR : MeasurableSet R := hU.inter measurableSet_Ioi
  have hLR : Disjoint L R := by
    rw [Set.disjoint_left]
    intro t htL htR
    have hle : t ≤ c := by simpa only [mem_Iic] using htL.2
    have hlt : c < t := by simpa only [mem_Ioi] using htR.2
    exact (not_lt_of_ge hle) hlt
  have hUeq : L ∪ R = U := by
    ext t
    simp only [L, R, mem_union, mem_inter_iff, mem_Iic, mem_Ioi]
    constructor
    · tauto
    · intro ht
      exact (le_or_gt t c).elim (fun htc ↦ Or.inl ⟨ht, htc⟩) (fun htc ↦ Or.inr ⟨ht, htc⟩)
  let p := ∫ t in L, deriv h t
  let q := -∫ t in R, deriv h t
  have hp0 : 0 ≤ p := by
    exact setIntegral_nonneg hL fun t ht ↦ hleft t ht.2
  have hq0 : 0 ≤ q := by
    rw [neg_nonneg]
    exact setIntegral_nonpos hR fun t ht ↦ hright t ht.2
  have hp : p ≤ h c := by
    rw [← hhc.integral_Iic_deriv_eq hh c]
    apply setIntegral_mono_set hd_int.integrableOn
    · rw [EventuallyLE, ae_restrict_iff' measurableSet_Iic]
      exact ae_of_all _ fun t ht ↦ hleft t ht
    · exact Eventually.of_forall fun t ht ↦ ht.2
  have hq : q ≤ h c := by
    have hneg : ∫ t in R, -deriv h t ≤ ∫ t in Ioi c, -deriv h t := by
      apply setIntegral_mono_set hd_int.neg.integrableOn
      · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
        exact ae_of_all _ fun t ht ↦ neg_nonneg.mpr (hright t ht)
      · exact Eventually.of_forall fun t ht ↦ ht.2
    simp only [integral_neg] at hneg
    rw [hhc.integral_Ioi_deriv_eq hh c] at hneg
    simpa only [q, neg_neg] using hneg
  have hint : ∫ t in U, deriv h t = p - q := by
    rw [← hUeq, setIntegral_union hLR hR hd_int.integrableOn hd_int.integrableOn]
    simp only [p, q, sub_neg_eq_add]
  rw [hint, abs_le]
  constructor <;> linarith

theorem raw_antitone_norm {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x y : E n} (hxy : ‖x‖ ≤ ‖y‖) : raw a b y ≤ raw a b x := by
  rw [raw_eq_smoothTransition ha, raw_eq_smoothTransition ha]
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (sub_le_sub_left hxy b) (sub_nonneg.mpr hab.le)

theorem kernel_antitone_norm {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {x y : E n} (hxy : ‖x‖ ≤ ‖y‖) : kernel a b y ≤ kernel a b x := by
  unfold kernel
  exact div_le_div_of_nonneg_right (raw_antitone_norm ha hab hxy) (mass_pos ha hab).le

private theorem norm_add_smul_le_norm_add_smul_of_sq_le {n : ℕ} {z u : E n}
    (hzu : ⟪z, u⟫ = 0) (hu : ‖u‖ = 1) {s t : ℝ} (hst : s ^ 2 ≤ t ^ 2) :
    ‖z + s • u‖ ≤ ‖z + t • u‖ := by
  have hsorth : ⟪z, s • u⟫ = 0 := by simp [real_inner_smul_right, hzu]
  have htorth : ⟪z, t • u⟫ = 0 := by simp [real_inner_smul_right, hzu]
  have hs : ‖z + s • u‖ ^ 2 = ‖z‖ ^ 2 + s ^ 2 := by
    calc
      ‖z + s • u‖ ^ 2 = ‖z + s • u‖ * ‖z + s • u‖ := by rw [pow_two]
      _ = ‖z‖ * ‖z‖ + ‖s • u‖ * ‖s • u‖ :=
        norm_add_sq_eq_norm_sq_add_norm_sq_real hsorth
      _ = ‖z‖ ^ 2 + s ^ 2 := by simp [pow_two, norm_smul, hu]
  have ht : ‖z + t • u‖ ^ 2 = ‖z‖ ^ 2 + t ^ 2 := by
    calc
      ‖z + t • u‖ ^ 2 = ‖z + t • u‖ * ‖z + t • u‖ := by rw [pow_two]
      _ = ‖z‖ * ‖z‖ + ‖t • u‖ * ‖t • u‖ :=
        norm_add_sq_eq_norm_sq_add_norm_sq_real htorth
      _ = ‖z‖ ^ 2 + t ^ 2 := by simp [pow_two, norm_smul, hu]
  nlinarith [norm_nonneg (z + s • u), norm_nonneg (z + t • u)]

/-- A radial kernel restricted to an affine line is unimodal, with its mode at the closest point
of that line to the origin. -/
theorem kernel_line_monotone {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {z u : E n} (hzu : ⟪z, u⟫ = 0) (hu : ‖u‖ = 1) :
    MonotoneOn (fun t : ℝ ↦ kernel a b (z + t • u)) (Iic 0) := by
  intro s hs t ht hst
  apply kernel_antitone_norm ha hab
  apply norm_add_smul_le_norm_add_smul_of_sq_le hzu hu
  have hprod : 0 ≤ (s - t) * (s + t) :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hst) (by
      have hs0 : s ≤ 0 := by simpa only [mem_Iic] using hs
      have ht0 : t ≤ 0 := by simpa only [mem_Iic] using ht
      linarith)
  nlinarith

theorem kernel_line_antitone {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {z u : E n} (hzu : ⟪z, u⟫ = 0) (hu : ‖u‖ = 1) :
    AntitoneOn (fun t : ℝ ↦ kernel a b (z + t • u)) (Ici 0) := by
  intro s hs t ht hst
  apply kernel_antitone_norm ha hab
  apply norm_add_smul_le_norm_add_smul_of_sq_le hzu hu
  have hprod : 0 ≤ (t - s) * (t + s) :=
    mul_nonneg (sub_nonneg.mpr hst) (by
      have hs0 : 0 ≤ s := by simpa only [mem_Ici] using hs
      have ht0 : 0 ≤ t := by simpa only [mem_Ici] using ht
      linarith)
  nlinarith

end

end Submission.RadialMollifier
