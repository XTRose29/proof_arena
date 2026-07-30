import ChallengeDeps
import Submission.Eilenberg
import Submission.Hyperplane
import Submission.RadialMollifier

open LeanEval.Geometry
open MeasureTheory ENNReal Metric Set Function Filter
open scoped RealInnerProductSpace Topology

namespace Submission.BoundarySlice

noncomputable section

def slice {n : ℕ} (hn : 1 ≤ n) (u : E n) (hu : ‖u‖ = 1)
    (A : Set (E n)) (x : E n) (z : E (n - 1)) : Set ℝ :=
  {t | x - Hyperplane.parametrization hn u hu (z, t) ∈ A}

def localBoundary {n : ℕ} (A : Set (E n)) (x : E n) (b : ℝ) : Set (E n) :=
  {y | y ∈ ball 0 b ∧ x - y ∈ frontier A}

private theorem slice_isOpen {n : ℕ} {hn : 1 ≤ n} {u : E n} {hu : ‖u‖ = 1}
    {A : Set (E n)} (hA : IsOpen A) (x : E n) (z : E (n - 1)) :
    IsOpen (slice hn u hu A x z) := by
  have hcont : Continuous (fun t : ℝ ↦
      x - Hyperplane.parametrization hn u hu (z, t)) := by
    simp_rw [Hyperplane.parametrization_apply]
    fun_prop
  exact hA.preimage hcont

private theorem kernelLine_contDiff {n : ℕ} {hn : 1 ≤ n} {u : E n} {hu : ‖u‖ = 1}
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (z : E (n - 1)) :
    ContDiff ℝ 1 (fun t : ℝ ↦ RadialMollifier.kernel a b
      (Hyperplane.parametrization hn u hu (z, t))) := by
  simp_rw [Hyperplane.parametrization_apply]
  exact (RadialMollifier.contDiff_kernel ha hab).comp (by fun_prop)

private theorem kernelLine_hasCompactSupport {n : ℕ} {hn : 1 ≤ n}
    {u : E n} {hu : ‖u‖ = 1} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (z : E (n - 1)) : HasCompactSupport (fun t : ℝ ↦ RadialMollifier.kernel a b
      (Hyperplane.parametrization hn u hu (z, t))) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) b)
  intro t ht
  apply RadialMollifier.kernel_zero_of_le_norm ha hab
  have hbt : b ≤ ‖t‖ := by
    have hbt' : b < |t| := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero, not_le] using ht
    simpa only [Real.norm_eq_abs] using hbt'.le
  exact hbt.trans (Hyperplane.norm_snd_le_parametrization hn u hu z t)

private theorem kernelLine_deriv_zero_of_notMem_ball {n : ℕ} {hn : 1 ≤ n}
    {u : E n} {hu : ‖u‖ = 1} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (z : E (n - 1)) {t : ℝ}
    (ht : Hyperplane.parametrization hn u hu (z, t) ∉ ball (0 : E n) b) :
    deriv (fun s : ℝ ↦ RadialMollifier.kernel a b
      (Hyperplane.parametrization hn u hu (z, s))) t = 0 := by
  let h : ℝ → ℝ := fun s ↦ RadialMollifier.kernel a b
    (Hyperplane.parametrization hn u hu (z, s))
  have htzero : h t = 0 := by
    apply RadialMollifier.kernel_zero_of_mem_compl_ball ha hab ht
  have hmin : IsLocalMin h t := by
    filter_upwards with s
    rw [htzero]
    exact RadialMollifier.kernel_nonneg ha hab _
  exact hmin.deriv_eq_zero

private theorem integral_kernelLine_deriv_eq_zero {n : ℕ} {hn : 1 ≤ n}
    {u : E n} {hu : ‖u‖ = 1} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (z : E (n - 1)) :
    ∫ t : ℝ, deriv (fun s : ℝ ↦ RadialMollifier.kernel a b
      (Hyperplane.parametrization hn u hu (z, s))) t = 0 := by
  let h : ℝ → ℝ := fun t ↦ RadialMollifier.kernel a b
    (Hyperplane.parametrization hn u hu (z, t))
  have hh : ContDiff ℝ 1 h := kernelLine_contDiff ha hab z
  have hhc : HasCompactSupport h := kernelLine_hasCompactSupport ha hab z
  have hdint : Integrable (deriv h) :=
    (hh.continuous_deriv le_rfl).integrable_of_hasCompactSupport hhc.deriv
  have hunion : Iic (0 : ℝ) ∪ Ioi 0 = univ := by
    ext t
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt t 0
  calc
    ∫ t : ℝ, deriv h t = ∫ t in Iic (0 : ℝ) ∪ Ioi 0, deriv h t := by rw [hunion, setIntegral_univ]
    _ = (∫ t in Iic (0 : ℝ), deriv h t) + ∫ t in Ioi 0, deriv h t := by
      rw [setIntegral_union]
      · exact Set.disjoint_left.2 fun _ hle hgt ↦
          (not_lt_of_ge (by simpa only [mem_Iic] using hle))
            (by simpa only [mem_Ioi] using hgt)
      · exact measurableSet_Ioi
      · exact hdint.integrableOn
      · exact hdint.integrableOn
    _ = h 0 + -h 0 := by rw [hhc.integral_Iic_deriv_eq hh, hhc.integral_Ioi_deriv_eq hh]
    _ = 0 := add_neg_cancel _

private theorem integral_slice_deriv_eq_zero_of_empty_fiber {n : ℕ} {hn : 1 ≤ n}
    {u : E n} {hu : ‖u‖ = 1} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {A : Set (E n)} (hA : IsOpen A) (x : E n) (z : E (n - 1))
    (hempty : localBoundary A x b ∩
      Hyperplane.projection hn u hu ⁻¹' {z} = ∅) :
    ∫ t in slice hn u hu A x z,
        deriv (fun s : ℝ ↦ RadialMollifier.kernel a b
          (Hyperplane.parametrization hn u hu (z, s))) t = 0 := by
  let U : Set ℝ := slice hn u hu A x z
  let J : Set ℝ := {t | Hyperplane.parametrization hn u hu (z, t) ∈ ball (0 : E n) b}
  let φ : ℝ → E n := fun t ↦ x - Hyperplane.parametrization hn u hu (z, t)
  have hφ : Continuous φ := by
    simp_rw [φ, Hyperplane.parametrization_apply]
    fun_prop
  have hU : U = φ ⁻¹' A := rfl
  have hUopen : IsOpen U := slice_isOpen hA x z
  have hfrontier : frontier U ⊆ φ ⁻¹' frontier A := by
    rw [hU]
    exact hφ.frontier_preimage_subset A
  have hJconv : Convex ℝ J := by
    intro s hs t ht c d hc hd hcd
    have hcombo : Hyperplane.parametrization hn u hu (z, c • s + d • t) =
        c • Hyperplane.parametrization hn u hu (z, s) +
          d • Hyperplane.parametrization hn u hu (z, t) := by
      simp only [smul_eq_mul, Hyperplane.parametrization_apply]
      calc
        _ = (c + d) • ((Hyperplane.perpBasis hn u hu).repr.symm z : E n) +
            (c * s + d * t) • u := by rw [hcd, one_smul]
        _ = (c • ((Hyperplane.perpBasis hn u hu).repr.symm z : E n) +
              d • ((Hyperplane.perpBasis hn u hu).repr.symm z : E n)) +
            ((c * s) • u + (d * t) • u) := by rw [add_smul, add_smul]
        _ = _ := by simp only [smul_add, smul_smul]; abel
    change Hyperplane.parametrization hn u hu (z, s) ∈ ball (0 : E n) b at hs
    change Hyperplane.parametrization hn u hu (z, t) ∈ ball (0 : E n) b at ht
    change Hyperplane.parametrization hn u hu (z, c • s + d • t) ∈ ball (0 : E n) b
    rw [hcombo]
    exact (convex_ball (0 : E n) b) hs ht hc hd hcd
  have hdisj : Disjoint (frontier U) J := by
    rw [Set.disjoint_left]
    intro t htfront htJ
    have hpoint : Hyperplane.parametrization hn u hu (z, t) ∈
        localBoundary A x b ∩ Hyperplane.projection hn u hu ⁻¹' {z} := by
      refine ⟨⟨htJ, hfrontier htfront⟩, ?_⟩
      simpa only [mem_preimage, mem_singleton_iff] using
        Hyperplane.projection_parametrization hn u hu z t
    rw [hempty] at hpoint
    exact hpoint
  let V : Set J := Subtype.val ⁻¹' U
  have hclopen : IsClopen V := by
    simpa only [V] using isClopen_preimage_val hUopen hdisj
  letI : PreconnectedSpace J := Subtype.preconnectedSpace hJconv.isPreconnected
  rcases isClopen_iff.mp hclopen with hVempty | hVuniv
  · rw [← integral_indicator hUopen.measurableSet]
    apply integral_eq_zero_of_ae
    filter_upwards with t
    by_cases htU : t ∈ U
    · have htJ : t ∉ J := by
        intro htJ
        have : (⟨t, htJ⟩ : J) ∈ V := htU
        rw [hVempty] at this
        exact this
      simp only [indicator_of_mem htU]
      exact kernelLine_deriv_zero_of_notMem_ball ha hab z htJ
    · simp only [indicator_of_notMem htU, Pi.zero_apply]
  · rw [← integral_indicator hUopen.measurableSet]
    have hindicator : U.indicator (fun t ↦ deriv (fun s : ℝ ↦
        RadialMollifier.kernel a b (Hyperplane.parametrization hn u hu (z, s))) t) =
        fun t ↦ deriv (fun s : ℝ ↦
          RadialMollifier.kernel a b (Hyperplane.parametrization hn u hu (z, s))) t := by
      funext t
      by_cases htJ : t ∈ J
      · have htV : (⟨t, htJ⟩ : J) ∈ V := by rw [hVuniv]; trivial
        have htU : t ∈ U := htV
        rw [indicator_of_mem htU]
      · by_cases htU : t ∈ U
        · rw [indicator_of_mem htU]
        · rw [indicator_of_notMem htU,
            kernelLine_deriv_zero_of_notMem_ball ha hab z htJ]
    rw [hindicator, integral_kernelLine_deriv_eq_zero ha hab z]

/-- A signed derivative integral on a line is controlled by the number of local frontier points
on that line.  Empty fibers contribute exactly zero. -/
theorem enorm_integral_slice_deriv_le {n : ℕ} (hn : 2 ≤ n)
    {u : E n} (hu : ‖u‖ = 1) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {A : Set (E n)} (hA : IsOpen A) (x : E n) (z : E (n - 1)) :
    ‖∫ t in slice (by omega) u hu A x z,
        deriv (fun s : ℝ ↦ RadialMollifier.kernel a b
          (Hyperplane.parametrization (by omega) u hu (z, s))) t‖ₑ ≤
      ENNReal.ofReal (RadialMollifier.mass n a b)⁻¹ *
        μH[0] (localBoundary A x b ∩
          Hyperplane.projection (by omega) u hu ⁻¹' {z}) := by
  let U : Set ℝ := slice (by omega) u hu A x z
  let h : ℝ → ℝ := fun t ↦ RadialMollifier.kernel a b
    (Hyperplane.parametrization (by omega) u hu (z, t))
  let F : Set (E n) := localBoundary A x b ∩
    Hyperplane.projection (by omega) u hu ⁻¹' {z}
  by_cases hF : F.Nonempty
  · have hh : ContDiff ℝ 1 h := kernelLine_contDiff ha hab z
    have hhc : HasCompactSupport h := kernelLine_hasCompactSupport ha hab z
    have hUmeas : MeasurableSet U := (slice_isOpen hA x z).measurableSet
    have hinner : ⟪Hyperplane.parametrization (by omega) u hu (z, 0), u⟫ = 0 :=
      Hyperplane.parametrization_zero_inner (by omega) u hu z
    have hparam (t : ℝ) : Hyperplane.parametrization (by omega) u hu (z, t) =
        Hyperplane.parametrization (by omega) u hu (z, 0) + t • u := by
      simpa only [zero_add] using
        Hyperplane.parametrization_add_line (by omega) u hu z 0 t
    have hfun : h = fun t ↦ RadialMollifier.kernel a b
        (Hyperplane.parametrization (by omega) u hu (z, 0) + t • u) := by
      funext t
      simp only [h]
      rw [hparam]
    have hmono : MonotoneOn h (Iic 0) := by
      rw [hfun]
      exact RadialMollifier.kernel_line_monotone ha hab hinner hu
    have hanti : AntitoneOn h (Ici 0) := by
      rw [hfun]
      exact RadialMollifier.kernel_line_antitone ha hab hinner hu
    have hleft : ∀ t ≤ 0, 0 ≤ deriv h t := by
      intro t ht
      have heq : derivWithin h (Iic 0) t = deriv h t :=
        (hh.differentiable one_ne_zero t).hasDerivAt.hasDerivWithinAt.derivWithin
          (uniqueDiffOn_Iic 0 t ht)
      rw [← heq]
      exact hmono.derivWithin_nonneg
    have hright : ∀ t, 0 < t → deriv h t ≤ 0 := by
      intro t ht
      have heq : derivWithin h (Ici 0) t = deriv h t :=
        (hh.differentiable one_ne_zero t).hasDerivAt.hasDerivWithinAt.derivWithin
          (uniqueDiffOn_Ici 0 t ht.le)
      rw [← heq]
      exact hanti.derivWithin_nonpos
    have habs : |∫ t in U, deriv h t| ≤ (RadialMollifier.mass n a b)⁻¹ :=
      (RadialMollifier.abs_setIntegral_deriv_le_peak hh hhc hUmeas hleft hright).trans
        (RadialMollifier.kernel_le_peak ha hab _)
    calc
      ‖∫ t in U, deriv h t‖ₑ = ENNReal.ofReal |∫ t in U, deriv h t| := by
        simpa only [Real.norm_eq_abs] using
          (ofReal_norm (∫ t in U, deriv h t)).symm
      _ ≤ ENNReal.ofReal (RadialMollifier.mass n a b)⁻¹ := ENNReal.ofReal_le_ofReal habs
      _ = ENNReal.ofReal (RadialMollifier.mass n a b)⁻¹ * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal (RadialMollifier.mass n a b)⁻¹ * μH[0] F := by
        gcongr
        exact MeasureTheory.Measure.one_le_hausdorffMeasure_zero_of_nonempty hF
  · have hFempty : F = ∅ := not_nonempty_iff_eq_empty.mp hF
    have hzero := integral_slice_deriv_eq_zero_of_empty_fiber ha hab hA x z hFempty
    rw [hzero, enorm_zero]
    exact zero_le

end

end Submission.BoundarySlice
