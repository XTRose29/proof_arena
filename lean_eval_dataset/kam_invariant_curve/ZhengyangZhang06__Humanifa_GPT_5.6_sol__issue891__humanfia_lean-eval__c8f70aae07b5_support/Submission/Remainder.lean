import Submission.NewtonEstimates
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open LeanEval.Dynamics
open MeasureTheory
open scoped ContDiff

namespace Submission.Majorant

noncomputable section

/-- Repeated differentiation in the second coordinate of a smooth function on
the plane.  This gives a convenient jointly continuous representative for the
derivatives of all one-dimensional slices. -/
def verticalIteratedDeriv : ℕ → ((ℝ × ℝ) → ℝ) → (ℝ × ℝ) → ℝ
  | 0, H => H
  | n + 1, H => fun p =>
      fderiv ℝ (verticalIteratedDeriv n H) p (0, 1)

theorem verticalIteratedDeriv_contDiff (n : ℕ) {H : (ℝ × ℝ) → ℝ}
    (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (verticalIteratedDeriv n H) := by
  induction n with
  | zero => simpa only [verticalIteratedDeriv] using hH
  | succ n ih =>
      simp only [verticalIteratedDeriv]
      fun_prop

theorem verticalIteratedDeriv_slice (n : ℕ) {H : (ℝ × ℝ) → ℝ}
    (hH : ContDiff ℝ ∞ H) (a t : ℝ) :
    iteratedDeriv n (fun x => H (a, x)) t =
      verticalIteratedDeriv n H (a, t) := by
  induction n generalizing t with
  | zero => simp [verticalIteratedDeriv]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (fun x => H (a, x)) =
          fun x => verticalIteratedDeriv n H (a, x) := by
        funext x
        exact ih x
      rw [hfun]
      simp only [verticalIteratedDeriv]
      have hs := verticalIteratedDeriv_contDiff n hH
      have hinner : HasDerivAt (fun x : ℝ => (a, x)) (0, 1) t := by
        simpa using (hasDerivAt_const (x := t) (c := a)).prodMk
          (hasDerivAt_id t)
      exact (hs.differentiable (by simp)).differentiableAt.hasFDerivAt
        |>.comp_hasDerivAt t hinner |>.deriv

theorem verticalIteratedDeriv_hasDerivAt (n : ℕ)
    {H : (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (a t : ℝ) :
    HasDerivAt (fun x => verticalIteratedDeriv n H (a, x))
      (verticalIteratedDeriv (n + 1) H (a, t)) t := by
  simp only [verticalIteratedDeriv]
  have hs := verticalIteratedDeriv_contDiff n hH
  have hinner : HasDerivAt (fun x : ℝ => (a, x)) (0, 1) t := by
    simpa using (hasDerivAt_const (x := t) (c := a)).prodMk
      (hasDerivAt_id t)
  exact (hs.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt t hinner

/-- Integrate a smooth family over a fixed compact parameter interval. -/
def sliceIntegral (H : (ℝ × ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ a in (0 : ℝ)..1, H (a, t)

theorem hasDerivAt_integral_verticalIteratedDeriv (n : ℕ)
    {H : (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    {s : ℕ} {A R : ℝ}
    (hmajor : ∀ a ∈ Set.Icc (0 : ℝ) 1,
      Majorized s A R (fun t => H (a, t))) (t : ℝ) :
    HasDerivAt
      (fun x => ∫ a in (0 : ℝ)..1,
        verticalIteratedDeriv n H (a, x))
      (∫ a in (0 : ℝ)..1, verticalIteratedDeriv (n + 1) H (a, t)) t := by
  let C := A * weight s (n + 1) * R ^ (n + 1)
  have hcont (k : ℕ) (x : ℝ) :
      Continuous (fun a => verticalIteratedDeriv k H (a, x)) := by
    exact (verticalIteratedDeriv_contDiff k hH).continuous.comp (by fun_prop)
  have hbound (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
      ‖verticalIteratedDeriv (n + 1) H (a, x)‖ ≤ C := by
    rw [← verticalIteratedDeriv_slice (n + 1) hH a x,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hmajor a ha (n + 1) x
  have hresult := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume)
    (F := fun x a => verticalIteratedDeriv n H (a, x))
    (F' := fun x a => verticalIteratedDeriv (n + 1) H (a, x))
    (s := Set.univ) (bound := fun _ => C) (a := (0 : ℝ)) (b := 1)
    (by exact Filter.univ_mem : Set.univ ∈ nhds t)
    (by
      filter_upwards [] with x
      exact (hcont n x).aestronglyMeasurable)
    ((hcont n t).intervalIntegrable 0 1)
    ((hcont (n + 1) t).aestronglyMeasurable)
    (by
      filter_upwards [] with a ha x hx
      apply hbound a _ x
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ha
      exact ⟨ha.1.le, ha.2⟩)
    (continuous_const.intervalIntegrable 0 1)
    (by
      filter_upwards [] with a ha x hx
      exact verticalIteratedDeriv_hasDerivAt n hH a x)
  exact hresult.2

theorem iteratedDeriv_sliceIntegral (n : ℕ)
    {H : (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    {s : ℕ} {A R : ℝ}
    (hmajor : ∀ a ∈ Set.Icc (0 : ℝ) 1,
      Majorized s A R (fun t => H (a, t))) (t : ℝ) :
    iteratedDeriv n (sliceIntegral H) t =
      ∫ a in (0 : ℝ)..1, verticalIteratedDeriv n H (a, t) := by
  induction n generalizing t with
  | zero => simp [sliceIntegral, verticalIteratedDeriv]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (sliceIntegral H) =
          fun x => ∫ a in (0 : ℝ)..1,
            verticalIteratedDeriv n H (a, x) := by
        funext x
        exact ih x
      rw [hfun]
      exact (hasDerivAt_integral_verticalIteratedDeriv n hH hmajor t).deriv

theorem sliceIntegral_majorized {H : (ℝ × ℝ) → ℝ}
    (hH : ContDiff ℝ ∞ H) {s : ℕ} {A R : ℝ}
    (hmajor : ∀ a ∈ Set.Icc (0 : ℝ) 1,
      Majorized s A R (fun t => H (a, t))) :
    Majorized s A R (sliceIntegral H) := by
  intro n t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_sliceIntegral n hH hmajor t]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := A * weight s n * R ^ n)
    (f := fun a => verticalIteratedDeriv n H (a, t)) (by
      intro a ha
      rw [← verticalIteratedDeriv_slice n hH a t,
        ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      apply hmajor a _ n t
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ha
      exact ⟨ha.1.le, ha.2⟩)
  simpa only [sub_zero, abs_one, mul_one] using hint

theorem sliceIntegral_contDiff {H : (ℝ × ℝ) → ℝ}
    (hH : ContDiff ℝ ∞ H) {s : ℕ} {A R : ℝ}
    (hmajor : ∀ a ∈ Set.Icc (0 : ℝ) 1,
      Majorized s A R (fun t => H (a, t))) :
    ContDiff ℝ ∞ (sliceIntegral H) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n hn
  rw [show iteratedDeriv n (sliceIntegral H) =
      fun x => ∫ a in (0 : ℝ)..1,
        verticalIteratedDeriv n H (a, x) by
    funext x
    exact iteratedDeriv_sliceIntegral n hH hmajor x]
  intro t
  exact (hasDerivAt_integral_verticalIteratedDeriv n hH hmajor t).differentiableAt

theorem PositiveMajorized.add_const_mul {s r : ℕ} {B V S T a : ℝ}
    {g v : ℝ → ℝ} (hg : PositiveMajorized s B S g)
    (hv : Majorized r V T v) (hgs : ContDiff ℝ ∞ g)
    (hvs : ContDiff ℝ ∞ v) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (ha : |a| ≤ 1) :
    PositiveMajorized (max s r) (B + V) (max S T)
      (fun t => g t + a * v t) := by
  intro n hn t
  let p := max s r
  let M := max S T
  have hM : 0 ≤ M := hS.trans (le_max_left _ _)
  have hg' : ‖iteratedFDeriv ℝ n g t‖ ≤
      B * weight p n * M ^ n := by
    apply (hg n hn t).trans
    have hw : weight s n ≤ weight p n :=
      weight_exponent_mono (le_max_left _ _)
    have hp : S ^ n ≤ M ^ n :=
      pow_le_pow_left₀ hS (le_max_left _ _) n
    have hcore : weight s n * S ^ n ≤ weight p n * M ^ n :=
      mul_le_mul hw hp (pow_nonneg hS n) (weight_nonneg p n)
    calc
      B * weight s n * S ^ n = B * (weight s n * S ^ n) := by ring
      _ ≤ B * (weight p n * M ^ n) := mul_le_mul_of_nonneg_left hcore hB
      _ = B * weight p n * M ^ n := by ring
  have hv' : ‖iteratedFDeriv ℝ n v t‖ ≤
      V * weight p n * M ^ n := by
    apply (hv n t).trans
    have hw : weight r n ≤ weight p n :=
      weight_exponent_mono (le_max_right _ _)
    have hp : T ^ n ≤ M ^ n :=
      pow_le_pow_left₀ hT (le_max_right _ _) n
    have hcore : weight r n * T ^ n ≤ weight p n * M ^ n :=
      mul_le_mul hw hp (pow_nonneg hT n) (weight_nonneg p n)
    calc
      V * weight r n * T ^ n = V * (weight r n * T ^ n) := by ring
      _ ≤ V * (weight p n * M ^ n) := mul_le_mul_of_nonneg_left hcore hV
      _ = V * weight p n * M ^ n := by ring
  rw [show (fun t => g t + a * v t) = g + a • v by rfl,
    iteratedFDeriv_add (i := n) (f := g) (g := a • v)
      (hgs.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)))
      ((hvs.const_smul a).of_le
        (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))),
    Pi.add_apply, iteratedFDeriv_const_smul_apply
      (hvs.contDiffAt.of_le
        (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)))]
  calc
    ‖iteratedFDeriv ℝ n g t + a • iteratedFDeriv ℝ n v t‖ ≤
        ‖iteratedFDeriv ℝ n g t‖ +
          ‖a • iteratedFDeriv ℝ n v t‖ := norm_add_le _ _
    _ = ‖iteratedFDeriv ℝ n g t‖ +
          |a| * ‖iteratedFDeriv ℝ n v t‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ B * weight p n * M ^ n +
        1 * (V * weight p n * M ^ n) := by
      gcongr
    _ = (B + V) * weight p n * M ^ n := by ring

def secondDerivativeAmplitude (s : ℕ) (A R : ℝ) : ℝ :=
  (A * R * 2 ^ s) * (2 ^ (2 * s) * R) * 2 ^ s

def secondDerivativeRadius (s : ℕ) (R : ℝ) : ℝ :=
  2 ^ (2 * s) * (2 ^ (2 * s) * R)

theorem secondDerivative_majorized {s : ℕ} {A R : ℝ} {f : ℝ → ℝ}
    (hf : Majorized s A R f) :
    Majorized s (secondDerivativeAmplitude s A R)
      (secondDerivativeRadius s R) (deriv (deriv f)) := by
  exact hf.deriv.deriv

def taylorKernel (f x v : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 - p.1) * deriv (deriv f) (x p.2 + p.1 * v p.2)

def taylorIntegral (f x v : ℝ → ℝ) : ℝ → ℝ :=
  sliceIntegral (taylorKernel f x v)

def taylorRemainder (f x v : ℝ → ℝ) (t : ℝ) : ℝ :=
  v t ^ 2 * taylorIntegral f x v t

def taylorKernelExponent (sf sx sv : ℕ) : ℕ :=
  sf + max sx sv + 1

def taylorKernelRadius (sf : ℕ) (RF B V S T : ℝ) : ℝ :=
  max 1 (secondDerivativeRadius sf RF) * max 1 (B + V) * max S T

theorem taylorKernel_slice_majorized {sf sx sv : ℕ}
    {F RF B V S T : ℝ} {f x v : ℝ → ℝ}
    (hf : Majorized sf F RF f) (hx : PositiveMajorized sx B S x)
    (hv : Majorized sv V T v) (hfs : ContDiff ℝ ∞ f)
    (hxs : ContDiff ℝ ∞ x) (hvs : ContDiff ℝ ∞ v)
    (hF : 0 ≤ F) (hRF : 0 ≤ RF) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (a : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    Majorized (taylorKernelExponent sf sx sv)
      (secondDerivativeAmplitude sf F RF)
      (taylorKernelRadius sf RF B V S T)
      (fun t => taylorKernel f x v (a, t)) := by
  have hinner := hx.add_const_mul hv hxs hvs hB hV hS hT
    (show |a| ≤ 1 by rw [abs_of_nonneg ha.1]; exact ha.2)
  have hinnerSmooth : ContDiff ℝ ∞ (fun t => x t + a * v t) := by
    fun_prop
  have hf2 := secondDerivative_majorized hf
  have hf2Smooth : ContDiff ℝ ∞ (deriv (deriv f)) := by
    exact (contDiff_infty_iff_deriv.mp
      (contDiff_infty_iff_deriv.mp hfs).2).2
  have hM : 0 ≤ max S T := hS.trans (le_max_left _ _)
  have hcomp := hf2.comp_positive_sharp hinner hf2Smooth hinnerSmooth
    (by unfold secondDerivativeAmplitude; positivity)
    (by unfold secondDerivativeRadius; positivity) hM
  have hscaled := hcomp.const_mul (c := 1 - a)
    (hf2Smooth.comp hinnerSmooth)
  change Majorized (sf + max sx sv + 1)
    (secondDerivativeAmplitude sf F RF)
    (max 1 (secondDerivativeRadius sf RF) * max 1 (B + V) * max S T)
    (fun t => (1 - a) * deriv (deriv f) (x t + a * v t))
  apply hscaled.amplitude_mono _ (by positivity)
  have hone : |1 - a| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr ha.2)]
    exact sub_le_self 1 ha.1
  exact mul_le_of_le_one_left
    (by unfold secondDerivativeAmplitude; positivity) hone

theorem taylorIntegral_majorized {sf sx sv : ℕ}
    {F RF B V S T : ℝ} {f x v : ℝ → ℝ}
    (hf : Majorized sf F RF f) (hx : PositiveMajorized sx B S x)
    (hv : Majorized sv V T v) (hfs : ContDiff ℝ ∞ f)
    (hxs : ContDiff ℝ ∞ x) (hvs : ContDiff ℝ ∞ v)
    (hF : 0 ≤ F) (hRF : 0 ≤ RF) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    Majorized (taylorKernelExponent sf sx sv)
      (secondDerivativeAmplitude sf F RF)
      (taylorKernelRadius sf RF B V S T) (taylorIntegral f x v) := by
  apply sliceIntegral_majorized
  · unfold taylorKernel
    fun_prop
  · exact fun a ha => taylorKernel_slice_majorized hf hx hv hfs hxs hvs
      hF hRF hB hV hS hT a ha

theorem taylorIntegral_contDiff {sf sx sv : ℕ}
    {F RF B V S T : ℝ} {f x v : ℝ → ℝ}
    (hf : Majorized sf F RF f) (hx : PositiveMajorized sx B S x)
    (hv : Majorized sv V T v) (hfs : ContDiff ℝ ∞ f)
    (hxs : ContDiff ℝ ∞ x) (hvs : ContDiff ℝ ∞ v)
    (hF : 0 ≤ F) (hRF : 0 ≤ RF) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    ContDiff ℝ ∞ (taylorIntegral f x v) := by
  apply sliceIntegral_contDiff
  · unfold taylorKernel
    fun_prop
  · exact fun a ha => taylorKernel_slice_majorized hf hx hv hfs hxs hvs
      hF hRF hB hV hS hT a ha

def taylorRemainderExponent (sf sx sv : ℕ) : ℕ :=
  max sv (taylorKernelExponent sf sx sv)

def taylorRemainderAmplitude (sf : ℕ) (F RF V : ℝ) : ℝ :=
  V ^ 2 * secondDerivativeAmplitude sf F RF

def taylorRemainderRadius (sf : ℕ) (RF B V S T : ℝ) : ℝ :=
  4 * max (4 * T) (taylorKernelRadius sf RF B V S T)

theorem taylorRemainder_majorized {sf sx sv : ℕ}
    {F RF B V S T : ℝ} {f x v : ℝ → ℝ}
    (hf : Majorized sf F RF f) (hx : PositiveMajorized sx B S x)
    (hv : Majorized sv V T v) (hfs : ContDiff ℝ ∞ f)
    (hxs : ContDiff ℝ ∞ x) (hvs : ContDiff ℝ ∞ v)
    (hF : 0 ≤ F) (hRF : 0 ≤ RF) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    Majorized (taylorRemainderExponent sf sx sv)
      (taylorRemainderAmplitude sf F RF V)
      (taylorRemainderRadius sf RF B V S T)
      (taylorRemainder f x v) := by
  have hv2 := hv.mul hv hvs hvs hV hV hT hT
  have hint := taylorIntegral_majorized hf hx hv hfs hxs hvs
    hF hRF hB hV hS hT
  have hintSmooth := taylorIntegral_contDiff hf hx hv hfs hxs hvs
    hF hRF hB hV hS hT
  have hprod := hv2.mul hint (hvs.mul hvs) hintSmooth
    (mul_nonneg hV hV) (by unfold secondDerivativeAmplitude; positivity)
    (by positivity) (by unfold taylorKernelRadius; positivity)
  unfold taylorRemainderExponent taylorRemainderAmplitude
    taylorRemainderRadius taylorRemainder
  simpa only [pow_two, max_self] using hprod

end

end Submission.Majorant
