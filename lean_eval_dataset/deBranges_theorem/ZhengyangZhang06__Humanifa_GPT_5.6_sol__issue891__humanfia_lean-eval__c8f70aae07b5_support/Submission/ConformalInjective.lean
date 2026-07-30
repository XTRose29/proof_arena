import Mathlib

open Filter Function Metric Set
open scoped Topology

namespace Submission

lemma hasDerivAt_of_continuousAt_pow_eq
    {q u : ℂ → ℂ} {z u' : ℂ} {m : ℕ} (hm : m ≠ 0)
    (hq : ContinuousAt q z) (hpow : ∀ w, q w ^ m = u w)
    (hq0 : q z ≠ 0) (hu : HasDerivAt u u' z) :
    HasDerivAt q (u' / ((m : ℂ) * q z ^ (m - 1))) z := by
  let P : ℂ → ℂ := fun w => w ^ m
  let d : ℂ := (m : ℂ) * q z ^ (m - 1)
  have hd : d ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hm) (pow_ne_zero _ hq0)
  have hP : HasStrictDerivAt P d (q z) := by
    simpa only [P, d] using hasStrictDerivAt_pow m (q z)
  let r : ℂ → ℂ := hP.localInverse P d (q z) hd
  have hr : HasStrictDerivAt r d⁻¹ (P (q z)) := hP.to_localInverse hd
  have hleft : ∀ᶠ w in nhds (q z), r (P w) = w := hP.eventually_left_inverse hd
  have hleftEq : (fun w => r (P w)) =ᶠ[nhds (q z)] id := hleft
  have hpull := hleftEq.comp_tendsto hq
  have hqr : ∀ᶠ w in nhds z, r (u w) = q w := by
    filter_upwards [hpull] with w hw
    simpa only [Function.comp_apply, id_eq, P, hpow w] using hw
  have hpoint : P (q z) = u z := by exact hpow z
  have hcomp : HasDerivAt (r ∘ u) (d⁻¹ * u') z := by
    rw [hpoint] at hr
    exact hr.hasDerivAt.comp z hu
  have hqrEq : (fun w => r (u w)) =ᶠ[nhds z] q := hqr
  have hcongr : q =ᶠ[nhds z] r ∘ u := by
    filter_upwards [hqrEq] with w hw
    exact hw.symm
  simpa only [d, div_eq_mul_inv, mul_comm] using
    hcomp.congr_of_eventuallyEq hcongr

lemma isSimplyConnected_ball (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IsSimplyConnected (ball z r) := by
  letI : ContractibleSpace (ball z r) :=
    (convex_ball z r).contractibleSpace ⟨z, mem_ball_self hr⟩
  change SimplyConnectedSpace (ball z r)
  infer_instance

lemma deriv_ne_zero_of_injOn_of_differentiableOn
    {U : Set ℂ} (hUo : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hinj : U.InjOn f)
    {z : ℂ} (hz : z ∈ U) : deriv f z ≠ 0 := by
  intro hderiv
  let F : ℂ → ℂ := fun w => f w - f z
  have hfAnalytic : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hUo
  have hFAnalytic : AnalyticAt ℂ F z := (hfAnalytic z hz).sub analyticAt_const
  have hFzero : F z = 0 := by simp [F]
  have hFnot : ¬∀ᶠ w in nhds z, F w = 0 := by
    intro heq
    have hevent : ∀ᶠ w in nhds z, w ∈ U ∧ F w = 0 := by
      filter_upwards [hUo.mem_nhds hz, heq] with w hwU hwF
      exact ⟨hwU, hwF⟩
    change {w | w ∈ U ∧ F w = 0} ∈ nhds z at hevent
    rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hεsub⟩
    let w : ℂ := z + (ε / 2 : ℝ)
    have hwball : w ∈ ball z ε := by
      rw [mem_ball, dist_eq_norm]
      simp only [w, add_sub_cancel_left]
      change ‖((ε / 2 : ℝ) : ℂ)‖ < ε
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hw := hεsub hwball
    have hfw : f w = f z := sub_eq_zero.mp hw.2
    have hwz : w = z := hinj hw.1 hz hfw
    have : (ε / 2 : ℂ) = 0 := by simpa [w] using congrArg (fun v => v - z) hwz
    have : ε / 2 = 0 := by exact_mod_cast this
    linarith
  rcases (hFAnalytic.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hFnot) with
    ⟨m, g, hgAnalytic, hg0, hfactor⟩
  have hm0 : m ≠ 0 := by
    intro hm
    subst m
    have h := hfactor.self_of_nhds
    apply hg0
    simpa [F] using h.symm
  have hm1 : m ≠ 1 := by
    intro hm
    subst m
    have hfactorEq : F =ᶠ[nhds z] fun w => (w - z) ^ 1 * g w := by
      filter_upwards [hfactor] with w hw
      simpa only [smul_eq_mul] using hw
    have hFderiv : deriv F z = 0 := by
      have hfAt : DifferentiableAt ℂ f z :=
        (hf z hz).differentiableAt (hUo.mem_nhds hz)
      simpa only [F, (hfAt.hasDerivAt.sub_const (f z)).deriv] using hderiv
    have hrightDeriv : deriv (fun w => (w - z) ^ 1 * g w) z = g z := by
      have hgAt := hgAnalytic.differentiableAt
      simp only [pow_one]
      change deriv ((fun w => w - z) * g) z = g z
      simpa using
        (((hasDerivAt_id z).sub_const z).pow 1).mul hgAt.hasDerivAt |>.deriv
    rw [hfactorEq.deriv_eq, hrightDeriv] at hFderiv
    exact hg0 hFderiv
  have hm2 : 2 ≤ m := by omega
  have hg_ne : ∀ᶠ w in nhds z, g w ≠ 0 := by
    have hmem : ∀ᶠ w in nhds z, g w ∈ ({0}ᶜ : Set ℂ) :=
      hgAnalytic.continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds hg0)
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
  have hg_an : ∀ᶠ w in nhds z, AnalyticAt ℂ g w :=
    (isOpen_analyticAt ℂ g).mem_nhds hgAnalytic
  have hnear : ∀ᶠ w in nhds z,
      w ∈ U ∧ AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
        F w = (w - z) ^ m * g w := by
    filter_upwards [hUo.mem_nhds hz, hg_an, hg_ne, hfactor] with w hwU hwg hw0 hwf
    exact ⟨hwU, hwg, hw0, by simpa only [smul_eq_mul] using hwf⟩
  change {w | w ∈ U ∧ AnalyticAt ℂ g w ∧ g w ≠ 0 ∧
    F w = (w - z) ^ m * g w} ∈ nhds z at hnear
  rcases Metric.mem_nhds_iff.mp hnear with ⟨ρ, hρ, hρsub⟩
  have hgcont : ContinuousOn g (ball z ρ) := by
    intro w hw
    exact (hρsub hw).2.1.continuousAt.continuousWithinAt
  have hgavoid : 0 ∉ g '' ball z ρ := by
    rintro ⟨w, hw, hgw⟩
    exact (hρsub hw).2.2.1 hgw
  rcases Complex.exists_continuousOn_pow_eq
      (isSimplyConnected_ball z hρ) isOpen_ball hgcont hgavoid hm0 with
    ⟨r, hrcont, hrpow⟩
  have hr0 : ∀ w ∈ ball z ρ, r w ≠ 0 := by
    intro w hw hrw
    have h := hrpow w
    rw [hrw, zero_pow hm0] at h
    exact (hρsub hw).2.2.1 h.symm
  have hrdiff : DifferentiableOn ℂ r (ball z ρ) := by
    intro w hw
    have hroot := hasDerivAt_of_continuousAt_pow_eq hm0
      (hrcont.continuousAt (isOpen_ball.mem_nhds hw)) hrpow (hr0 w hw)
      (hρsub hw).2.1.differentiableAt.hasDerivAt
    exact hroot.differentiableAt.differentiableWithinAt
  let h : ℂ → ℂ := fun w => (w - z) * r w
  have hzball : z ∈ ball z ρ := mem_ball_self hρ
  have hrAt : DifferentiableAt ℂ r z :=
    (hrdiff z hzball).differentiableAt (isOpen_ball.mem_nhds hzball)
  have hhAt : HasDerivAt h (r z) z := by
    change HasDerivAt ((fun w => w - z) * r) (r z) z
    simpa only [Pi.mul_apply, id_eq, sub_self, zero_mul, one_mul, add_zero] using
      ((hasDerivAt_id z).sub_const z).mul hrAt.hasDerivAt
  have hhdiff : DifferentiableOn ℂ h (ball z ρ) := by
    intro w hw
    exact (differentiableWithinAt_id.sub_const z).mul (hrdiff w hw)
  have hhAnalytic : AnalyticAt ℂ h z :=
    (hhdiff.analyticOnNhd isOpen_ball) z hzball
  have hhstrict : HasStrictDerivAt h (r z) z := by
    simpa only [hhAt.deriv] using hhAnalytic.hasStrictDerivAt
  have hfactor' : ∀ w ∈ ball z ρ, F w = h w ^ m := by
    intro w hw
    calc
      F w = (w - z) ^ m * g w := (hρsub hw).2.2.2
      _ = ((w - z) * r w) ^ m := by rw [mul_pow, hrpow]
      _ = h w ^ m := rfl
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))
  have hωroot : IsPrimitiveRoot ω m := by
    exact Complex.isPrimitiveRoot_exp m hm0
  have hωpow : ω ^ m = 1 := hωroot.pow_eq_one
  have hωne : ω ≠ 1 := by
    have := hωroot.pow_ne_one_of_pos_of_lt (by norm_num : 1 ≠ 0) (by omega : 1 < m)
    simpa using this
  let l : ℂ → ℂ := hhstrict.localInverse h (r z) z (hr0 z hzball)
  have hhzero : h z = 0 := by simp [h]
  have hright : ∀ᶠ y in nhds 0, h (l y) = y := by
    simpa only [hhzero] using hhstrict.eventually_right_inverse (hr0 z hzball)
  have hlim : Tendsto l (nhds 0) (nhds z) := by
    simpa only [l, hhzero] using
      (hhstrict.hasStrictFDerivAt_equiv (hr0 z hzball)).localInverse_tendsto
  have hlball : ∀ᶠ y in nhds 0, l y ∈ ball z ρ :=
    hlim (isOpen_ball.mem_nhds hzball)
  have hrot : Tendsto (fun y : ℂ => ω * y) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun y : ℂ => ω * y) 0 := by fun_prop
    have hc' : Tendsto (fun y : ℂ => ω * y) (nhds 0) (nhds (ω * 0)) := hc
    simpa only [mul_zero] using hc'
  have hgood : ∀ᶠ y in nhds 0,
      (h (l y) = y ∧ l y ∈ ball z ρ) ∧
        (h (l (ω * y)) = ω * y ∧ l (ω * y) ∈ ball z ρ) := by
    filter_upwards [hright, hlball, hrot hright, hrot hlball] with y hy hyl hyω hyωl
    exact ⟨⟨hy, hyl⟩, hyω, hyωl⟩
  change {y | (h (l y) = y ∧ l y ∈ ball z ρ) ∧
    (h (l (ω * y)) = ω * y ∧ l (ω * y) ∈ ball z ρ)} ∈ nhds 0 at hgood
  rcases Metric.mem_nhds_iff.mp hgood with ⟨δ, hδ, hδsub⟩
  let y : ℂ := (δ / 2 : ℝ)
  have hyball : y ∈ ball (0 : ℂ) δ := by
    rw [mem_ball_zero_iff]
    dsimp only [y]
    change ‖((δ / 2 : ℝ) : ℂ)‖ < δ
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have hy := hδsub hyball
  have hy0 : y ≠ 0 := by
    dsimp only [y]
    exact_mod_cast (div_ne_zero (ne_of_gt hδ) (by norm_num : (2 : ℝ) ≠ 0))
  have hFeq : F (l y) = F (l (ω * y)) := by
    rw [hfactor' _ hy.1.2, hfactor' _ hy.2.2, hy.1.1, hy.2.1,
      mul_pow, hωpow, one_mul]
  have hfeq : f (l y) = f (l (ω * y)) := by
    simpa only [F, sub_left_inj] using hFeq
  have hleq : l y = l (ω * y) :=
    hinj (hρsub hy.1.2).1 (hρsub hy.2.2).1 hfeq
  apply hωne
  apply mul_right_cancel₀ hy0
  calc
    ω * y = h (l (ω * y)) := hy.2.1.symm
    _ = h (l y) := congrArg h hleq.symm
    _ = y := hy.1.1
    _ = 1 * y := (one_mul y).symm

end Submission
