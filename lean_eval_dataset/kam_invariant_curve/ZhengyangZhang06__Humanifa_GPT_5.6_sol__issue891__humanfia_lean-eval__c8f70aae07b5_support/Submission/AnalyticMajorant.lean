import Submission.Remainder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.IteratedFDeriv

open scoped ContDiff

namespace Submission.Majorant

noncomputable section

def localCoeffSum (p : FormalMultilinearSeries ℝ ℝ ℝ) (ρ : NNReal) : NNReal :=
  ∑' k : ℕ, ∑' z : Σ l : ℕ,
      {s : Finset (Fin (k + l)) // s.card = l},
    ‖p (k + z.1)‖₊ * ρ ^ z.1 * ρ ^ k

theorem nnnorm_changeOrigin_mul_pow_le_localCoeffSum
    (p : FormalMultilinearSeries ℝ ℝ ℝ) {ρ : NNReal}
    (hρ : 0 < ρ) (hr : ((ρ : ENNReal) + ρ) < p.radius)
    {d : ℝ} (hd : ‖d‖₊ ≤ ρ) (k : ℕ) :
    ‖p.changeOrigin d k‖₊ * ρ ^ k ≤ localCoeffSum p ρ := by
  have hdRad : (‖d‖₊ : ENNReal) < p.radius := by
    calc
      (‖d‖₊ : ENNReal) ≤ ρ := by exact_mod_cast hd
      _ < (ρ : ENNReal) + ρ := by
        exact ENNReal.lt_add_right (by simp) (by exact_mod_cast hρ.ne')
      _ < p.radius := hr
  have hs := p.changeOriginSeries_summable_aux₁ hr
  have hcoeff := p.nnnorm_changeOrigin_le k hdRad
  calc
    ‖p.changeOrigin d k‖₊ * ρ ^ k ≤
        (∑' z : Σ l : ℕ, {s : Finset (Fin (k + l)) // s.card = l},
          ‖p (k + z.1)‖₊ * ‖d‖₊ ^ z.1) * ρ ^ k :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = ∑' z : Σ l : ℕ, {s : Finset (Fin (k + l)) // s.card = l},
          (‖p (k + z.1)‖₊ * ‖d‖₊ ^ z.1) * ρ ^ k :=
      (NNReal.tsum_mul_right _ _).symm
    _ ≤ ∑' z : Σ l : ℕ, {s : Finset (Fin (k + l)) // s.card = l},
          ‖p (k + z.1)‖₊ * ρ ^ z.1 * ρ ^ k := by
      have hright : Summable (fun z : Σ l : ℕ,
          {s : Finset (Fin (k + l)) // s.card = l} =>
          ‖p (k + z.1)‖₊ * ρ ^ z.1 * ρ ^ k) :=
        (NNReal.summable_sigma.1 hs).1 k
      have hpoint : ∀ z : Σ l : ℕ,
          {s : Finset (Fin (k + l)) // s.card = l},
          (‖p (k + z.1)‖₊ * ‖d‖₊ ^ z.1) * ρ ^ k ≤
            ‖p (k + z.1)‖₊ * ρ ^ z.1 * ρ ^ k := by
        intro z
        gcongr
      have hleft : Summable (fun z : Σ l : ℕ,
          {s : Finset (Fin (k + l)) // s.card = l} =>
          (‖p (k + z.1)‖₊ * ‖d‖₊ ^ z.1) * ρ ^ k) :=
        NNReal.summable_of_le hpoint hright
      exact hleft.tsum_le_tsum hpoint hright
    _ ≤ localCoeffSum p ρ := by
      unfold localCoeffSum
      apply (NNReal.summable_sigma.1 hs).2.le_tsum k
      intro j _
      positivity

theorem nnnorm_changeOrigin_le_localCoeffSum_mul_inv
    (p : FormalMultilinearSeries ℝ ℝ ℝ) {ρ : NNReal}
    (hρ : 0 < ρ) (hr : ((ρ : ENNReal) + ρ) < p.radius)
    {d : ℝ} (hd : ‖d‖₊ ≤ ρ) (k : ℕ) :
    ‖p.changeOrigin d k‖₊ ≤ localCoeffSum p ρ * ρ⁻¹ ^ k := by
  have hk : ρ ^ k ≠ 0 := pow_ne_zero _ hρ.ne'
  calc
    ‖p.changeOrigin d k‖₊ =
        (‖p.changeOrigin d k‖₊ * ρ ^ k) * (ρ ^ k)⁻¹ := by
      rw [mul_inv_cancel_right₀ hk]
    _ ≤ localCoeffSum p ρ * (ρ ^ k)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (nnnorm_changeOrigin_mul_pow_le_localCoeffSum p hρ hr hd k) (by positivity)
    _ = localCoeffSum p ρ * ρ⁻¹ ^ k := by rw [inv_pow]

theorem local_iteratedFDeriv_bound {f : ℝ → ℝ}
    {p : FormalMultilinearSeries ℝ ℝ ℝ} {x : ℝ} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall f p x r) {ρ : NNReal}
    (hρ : 0 < ρ) (hr : ((ρ : ENNReal) + ρ) < r)
    {y : ℝ} (hy : dist y x < ρ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f y‖ ≤
      (localCoeffSum p ρ : ℝ) * weight 1 n *
        (max 1 ((ρ : ℝ)⁻¹)) ^ n := by
  let d := y - x
  have hd : ‖d‖₊ ≤ ρ := by
    change ‖d‖ ≤ (ρ : ℝ)
    simpa only [d, Real.norm_eq_abs, Real.dist_eq] using le_of_lt hy
  have hdRad : (‖d‖₊ : ENNReal) < r := by
    calc
      (‖d‖₊ : ENNReal) ≤ ρ := by exact_mod_cast hd
      _ < (ρ : ENNReal) + ρ := by
        exact ENNReal.lt_add_right (by simp) (by exact_mod_cast hρ.ne')
      _ < r := hr
  have hq := hp.changeOrigin hdRad
  have hcenter : x + d = y := by simp only [d]; ring
  rw [hcenter] at hq
  have hfac := hq.factorial_smul (1 : ℝ) n
  have hdiag : (n.factorial : ℝ) *
      p.changeOrigin d n (fun _ => (1 : ℝ)) = iteratedDeriv n f y := by
    simpa [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] using hfac
  have hevalNN : ‖p.changeOrigin d n (fun _ => (1 : ℝ))‖₊ ≤
      ‖p.changeOrigin d n‖₊ := by
    simpa using ContinuousMultilinearMap.le_opNNNorm
      (p.changeOrigin d n) (fun _ => (1 : ℝ))
  have hcoeffNN := nnnorm_changeOrigin_le_localCoeffSum_mul_inv
    p hρ (hr.trans_le hp.r_le) hd n
  have hcoeff : ‖p.changeOrigin d n (fun _ => (1 : ℝ))‖ ≤
      (localCoeffSum p ρ : ℝ) * ((ρ : ℝ)⁻¹) ^ n := by
    exact_mod_cast hevalNN.trans hcoeffNN
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← hdiag,
    norm_mul, Real.norm_natCast]
  calc
    (n.factorial : ℝ) * ‖p.changeOrigin d n (fun _ => (1 : ℝ))‖ ≤
        (n.factorial : ℝ) *
          ((localCoeffSum p ρ : ℝ) * ((ρ : ℝ)⁻¹) ^ n) := by
      exact mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
    _ ≤ weight 1 n *
          ((localCoeffSum p ρ : ℝ) * ((ρ : ℝ)⁻¹) ^ n) := by
      exact mul_le_mul_of_nonneg_right (factorial_cast_le_weight_one n)
        (mul_nonneg (NNReal.coe_nonneg _) (pow_nonneg (by positivity) n))
    _ ≤ weight 1 n *
          ((localCoeffSum p ρ : ℝ) * (max 1 ((ρ : ℝ)⁻¹)) ^ n) := by
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg 1 n)
      apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
      exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) n
    _ = (localCoeffSum p ρ : ℝ) * weight 1 n *
        (max 1 ((ρ : ℝ)⁻¹)) ^ n := by ring

theorem exists_local_iteratedFDeriv_bound {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) :
    ∃ δ A R : ℝ, 0 < δ ∧ 0 ≤ A ∧ 1 ≤ R ∧
      ∀ y : ℝ, dist y x < δ → ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n f y‖ ≤ A * weight 1 n * R ^ n := by
  rcases hf with ⟨p, r, hp⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos with ⟨a, ha0, har⟩
  have ha : 0 < a := by exact_mod_cast ha0
  let ρ : NNReal := a / 4
  have hρ : 0 < ρ := by unfold ρ; positivity
  have hρsumNN : ρ + ρ < a := by
    unfold ρ
    have ha' : (0 : NNReal) < a := ha
    nlinarith
  have hρsum : ((ρ : ENNReal) + ρ) < r := by
    calc
      (ρ : ENNReal) + ρ < a := by exact_mod_cast hρsumNN
      _ < r := har
  refine ⟨ρ, localCoeffSum p ρ, max 1 ((ρ : ℝ)⁻¹), ?_,
    NNReal.coe_nonneg _, le_max_left _ _, ?_⟩
  · exact_mod_cast hρ
  · intro y hy n
    exact local_iteratedFDeriv_bound hp hρ hρsum hy n

/-- An analytic periodic real function has one global quadratic-exponential
derivative majorant.  Compactness is used only on a single fundamental
interval; periodicity then transports every derivative bound to `ℝ`. -/
theorem exists_periodic_analytic_majorant {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ)
    (hper : Function.Periodic f 1) :
    ∃ A R : ℝ, 0 ≤ A ∧ 1 ≤ R ∧ Majorized 1 A R f := by
  have hlocal : ∀ z : Set.Icc (0 : ℝ) 1,
      ∃ δ A R : ℝ, 0 < δ ∧ 0 ≤ A ∧ 1 ≤ R ∧
        ∀ y : ℝ, dist y z.1 < δ → ∀ n : ℕ,
          ‖iteratedFDeriv ℝ n f y‖ ≤ A * weight 1 n * R ^ n := by
    intro z
    exact exists_local_iteratedFDeriv_bound (hf z.1 (Set.mem_univ _))
  choose δ A R hδ hA hR hbound using hlocal
  let U : Set.Icc (0 : ℝ) 1 → Set ℝ := fun z => Metric.ball z.1 (δ z)
  have hcover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ z, U z := by
    intro y hy
    rw [Set.mem_iUnion]
    refine ⟨⟨y, hy⟩, ?_⟩
    exact Metric.mem_ball_self (hδ ⟨y, hy⟩)
  rcases isCompact_Icc.elim_finite_subcover U
      (fun _ => Metric.isOpen_ball) hcover with ⟨S, hS⟩
  let A₀ : ℝ := ∑ z ∈ S, A z
  let R₀ : ℝ := 1 + ∑ z ∈ S, R z
  have hA₀ : 0 ≤ A₀ := by
    unfold A₀
    exact Finset.sum_nonneg fun z _ => hA z
  have hR₀ : 1 ≤ R₀ := by
    unfold R₀
    have : 0 ≤ ∑ z ∈ S, R z := by
      exact Finset.sum_nonneg fun z _ => zero_le_one.trans (hR z)
    linarith
  have hIcc (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
      ‖iteratedFDeriv ℝ n f y‖ ≤ A₀ * weight 1 n * R₀ ^ n := by
    have hyc := hS hy
    simp only [Set.mem_iUnion] at hyc
    rcases hyc with ⟨z, hzS, hyz⟩
    have hAz : A z ≤ A₀ := by
      unfold A₀
      exact Finset.single_le_sum (fun i _ => hA i) hzS
    have hRzsum : R z ≤ ∑ i ∈ S, R i :=
      Finset.single_le_sum (fun i _ => zero_le_one.trans (hR i)) hzS
    have hRz : R z ≤ R₀ := by
      unfold R₀
      linarith
    apply (hbound z y hyz n).trans
    exact mul_le_mul
      (mul_le_mul hAz (weight_exponent_mono (s := 1) (s' := 1) le_rfl)
        (weight_nonneg 1 n) hA₀)
      (pow_le_pow_left₀ (zero_le_one.trans (hR z)) hRz n)
      (pow_nonneg (zero_le_one.trans (hR z)) n)
      (mul_nonneg hA₀ (weight_nonneg 1 n))
  refine ⟨A₀, R₀, hA₀, hR₀, ?_⟩
  intro n t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hnper := Helpers.periodic_iteratedDeriv hper n
  have heq : iteratedDeriv n f (Int.fract t) = iteratedDeriv n f t := by
    have h := hnper.sub_int_mul_eq (x := t) (Int.floor t)
    have harg : t - (Int.floor t : ℝ) * 1 = Int.fract t := by
      rw [mul_one]
      rfl
    rw [harg] at h
    exact h
  rw [← heq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hIcc (Int.fract t) ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩ n

end

end Submission.Majorant
