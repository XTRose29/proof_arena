import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue

open Filter Topology Set

namespace Submission.Helpers

variable {y : ℝ → ℝ}

/-- The defect `h(t) = y(t)² (1+2t) - 1`; we will show `h ≡ 0`. -/
noncomputable def h (y : ℝ → ℝ) (t : ℝ) : ℝ :=
  (y t)^2 * (1 + 2*t) - 1

lemma h_zero (hy0 : y 0 = 1) : h y 0 = 0 := by
  simp [h, hy0]

/-- For `t > 0`, `h` has derivative `-2 (y t)² · h(t)`. -/
lemma hasDerivAt_h
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (h y) (-2 * (y t)^2 * h y t) t := by
  have hy := hy_diff t ht
  have hy2 : HasDerivAt (fun s => (y s)^2) (2 * y t * (-(y t)^3)) t := by
    have := hy.pow 2
    simpa using this
  have h1plus2t : HasDerivAt (fun s : ℝ => 1 + 2 * s) 2 t := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 t :=
      (hasDerivAt_id t).const_mul 2 |>.congr_deriv (by ring)
    simpa using h1.const_add 1
  have hprod : HasDerivAt (fun s => (y s)^2 * (1 + 2*s))
      (2 * y t * (-(y t)^3) * (1 + 2*t) + (y t)^2 * 2) t := hy2.mul h1plus2t
  have hsub : HasDerivAt (fun s => (y s)^2 * (1 + 2*s) - 1)
      (2 * y t * (-(y t)^3) * (1 + 2*t) + (y t)^2 * 2) t := hprod.sub_const 1
  convert hsub using 1
  show -2 * (y t)^2 * h y t
      = 2 * y t * (-(y t)^3) * (1 + 2*t) + (y t)^2 * 2
  simp [h]; ring

lemma y_continuousOn
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0) :
    ContinuousOn y (Ici 0) := by
  intro t ht
  have ht' : (0 : ℝ) ≤ t := ht
  rcases lt_or_eq_of_le ht' with htpos | hteq
  · exact ((hy_diff t htpos).continuousAt).continuousWithinAt
  · subst hteq; exact hy_cont

lemma h_continuousOn
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0) :
    ContinuousOn (h y) (Ici 0) := by
  have hy := y_continuousOn hy_diff hy_cont
  exact ((hy.pow 2).mul (continuousOn_const.add (continuousOn_id.const_mul _))).sub
    continuousOn_const

/-- Grönwall bound on `[a, b]` for fixed `0 < a`. -/
lemma h_gronwall_bound
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    {a b : ℝ} (ha : 0 < a) (K : ℝ)
    (hK : ∀ s ∈ Icc a b, 2 * (y s)^2 ≤ K) :
    ∀ x ∈ Icc a b, |h y x| ≤ |h y a| * Real.exp (K * (x - a)) := by
  have hcont : ContinuousOn (h y) (Icc a b) :=
    (h_continuousOn hy_diff hy_cont).mono (fun x hx => le_trans ha.le hx.1)
  have hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt (h y) (-2 * (y x)^2 * h y x) (Ici x) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    exact (hasDerivAt_h hy_diff hxpos).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico a b, ‖-2 * (y x)^2 * h y x‖ ≤ K * ‖h y x‖ + 0 := by
    intro x hx
    have hxK : 2 * (y x)^2 ≤ K := hK x ⟨hx.1, le_of_lt hx.2⟩
    have hy2_nn : 0 ≤ 2 * (y x)^2 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, add_zero]
    rw [show -2 * (y x)^2 * h y x = -(2 * (y x)^2 * h y x) by ring,
        abs_neg, abs_mul, abs_of_nonneg hy2_nn]
    exact mul_le_mul_of_nonneg_right hxK (abs_nonneg _)
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv
    (le_refl ‖h y a‖) hbound
  intro x hx
  have := hgr x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  rw [gronwallBound_ε0] at this
  exact this

/-- **Phase 1**: `h y ≡ 0` on `[0, ∞)`. -/
lemma h_eq_zero
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    (hy0 : y 0 = 1) :
    ∀ t ≥ (0 : ℝ), h y t = 0 := by
  intro t ht
  rcases lt_or_eq_of_le ht with htpos | hteq
  · have hy_cont' : ContinuousOn y (Icc 0 t) :=
      (y_continuousOn hy_diff hy_cont).mono Icc_subset_Ici_self
    have hy2_cont : ContinuousOn (fun s => (y s)^2) (Icc 0 t) := hy_cont'.pow 2
    have hcompact : IsCompact (Icc (0:ℝ) t) := isCompact_Icc
    have hne : (Icc (0:ℝ) t).Nonempty := ⟨0, ⟨le_refl _, htpos.le⟩⟩
    obtain ⟨xmax, _, hmax⟩ := hcompact.exists_isMaxOn hne hy2_cont
    set M := (y xmax)^2 with hM_def
    set K := 2 * M with hK_def
    have hK_bound : ∀ s ∈ Icc (0:ℝ) t, 2 * (y s)^2 ≤ K := by
      intro s hs
      have hsmax : (y s)^2 ≤ M := hmax hs
      simp [hK_def]; linarith
    have habs_h : ∀ ε : ℝ, 0 < ε → ε ≤ t →
        |h y t| ≤ |h y ε| * Real.exp (K * (t - ε)) := by
      intro ε hε hεt
      have hK_bound_sub : ∀ s ∈ Icc ε t, 2 * (y s)^2 ≤ K :=
        fun s hs => hK_bound s ⟨le_trans hε.le hs.1, hs.2⟩
      exact h_gronwall_bound hy_diff hy_cont hε K hK_bound_sub t ⟨hεt, le_refl _⟩
    have hε_pos : ∀ n : ℕ, (0 : ℝ) < t / (n + 2 : ℕ) := by
      intro n
      apply div_pos htpos
      exact_mod_cast Nat.succ_pos _
    have hε_le : ∀ n : ℕ, t / (n + 2 : ℕ) ≤ t := by
      intro n
      apply div_le_self htpos.le
      exact_mod_cast (by omega : 1 ≤ n + 2)
    have hε_to_zero : Tendsto (fun n : ℕ => t / (n + 2 : ℕ)) atTop (𝓝 0) := by
      have h1 := tendsto_natCast_atTop_atTop (R := ℝ)
      have h2 : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop := by
        simp only [Nat.cast_add, Nat.cast_ofNat]
        exact h1.atTop_add tendsto_const_nhds
      exact Tendsto.div_atTop (a := t) tendsto_const_nhds h2
    have hh_to_zero : Tendsto (fun n : ℕ => h y (t / (n + 2 : ℕ))) atTop (𝓝 0) := by
      have hh : Tendsto (h y) (𝓝[Ici 0] 0) (𝓝 (h y 0)) :=
        h_continuousOn hy_diff hy_cont 0 (Set.self_mem_Ici)
      rw [h_zero hy0] at hh
      have hε_in : Tendsto (fun n : ℕ => t / (n + 2 : ℕ)) atTop (𝓝[Ici (0:ℝ)] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hε_to_zero, ?_⟩
        filter_upwards with n
        exact (hε_pos n).le
      exact hh.comp hε_in
    have habs_to_zero : Tendsto (fun n : ℕ => |h y (t / (n + 2 : ℕ))|) atTop (𝓝 0) := by
      have := hh_to_zero.abs
      simpa using this
    have hexp_bdd : Tendsto
        (fun n : ℕ => Real.exp (K * (t - t / (n + 2 : ℕ)))) atTop
        (𝓝 (Real.exp (K * t))) := by
      have ht_diff : Tendsto (fun n : ℕ => t - t / (n + 2 : ℕ)) atTop (𝓝 t) := by
        have := hε_to_zero
        have : Tendsto (fun n : ℕ => t - t / (n + 2 : ℕ)) atTop (𝓝 (t - 0)) :=
          tendsto_const_nhds.sub this
        simpa using this
      have hKtx : Tendsto (fun n : ℕ => K * (t - t / (n + 2 : ℕ))) atTop (𝓝 (K * t)) :=
        ht_diff.const_mul K
      exact (Real.continuous_exp.tendsto _).comp hKtx
    have hprod_to : Tendsto
        (fun n : ℕ => |h y (t / (n + 2 : ℕ))| * Real.exp (K * (t - t / (n + 2 : ℕ))))
        atTop (𝓝 (0 * Real.exp (K * t))) := habs_to_zero.mul hexp_bdd
    rw [zero_mul] at hprod_to
    have habs_le : |h y t| ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds hprod_to
        (fun n => habs_h _ (hε_pos n) (hε_le n))
    have habs_eq : |h y t| = 0 := le_antisymm habs_le (abs_nonneg _)
    exact abs_eq_zero.mp habs_eq
  · subst hteq; exact h_zero hy0

lemma y_sq_eq
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    (hy0 : y 0 = 1) {t : ℝ} (ht : 0 ≤ t) :
    (y t)^2 = 1 / (1 + 2*t) := by
  have hH : h y t = 0 := h_eq_zero hy_diff hy_cont hy0 t ht
  have h1plus : (0 : ℝ) < 1 + 2 * t := by linarith
  have hne : (1 + 2 * t : ℝ) ≠ 0 := h1plus.ne'
  have heq : (y t)^2 * (1 + 2*t) = 1 := by
    have : (y t)^2 * (1 + 2*t) - 1 = 0 := hH
    linarith
  field_simp
  linarith

lemma y_ne_zero
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    (hy0 : y 0 = 1) {t : ℝ} (ht : 0 ≤ t) :
    y t ≠ 0 := by
  intro hzero
  have h1 : (y t)^2 = 1 / (1 + 2*t) := y_sq_eq hy_diff hy_cont hy0 ht
  rw [hzero] at h1
  have : (0 : ℝ) = 1 / (1 + 2*t) := by simpa using h1
  have h1plus : (0 : ℝ) < 1 + 2 * t := by linarith
  have hpos : (0 : ℝ) < 1 / (1 + 2*t) := div_pos one_pos h1plus
  linarith

lemma y_pos
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    (hy0 : y 0 = 1) {t : ℝ} (ht : 0 ≤ t) :
    0 < y t := by
  by_contra hle
  have hle : y t ≤ 0 := not_lt.mp hle
  have hne : y t ≠ 0 := y_ne_zero hy_diff hy_cont hy0 ht
  have hlt : y t < 0 := lt_of_le_of_ne hle hne
  have hcont : ContinuousOn y (Icc 0 t) :=
    (y_continuousOn hy_diff hy_cont).mono Icc_subset_Ici_self
  have h0_in : (0 : ℝ) ∈ Icc (y t) (y 0) := by
    rw [hy0]; exact ⟨hlt.le, by norm_num⟩
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' ht hcont h0_in
  exact y_ne_zero hy_diff hy_cont hy0 hc.1 hc0

lemma tendsto_t_div_one_plus_two_t :
    Tendsto (fun t : ℝ => t / (1 + 2*t)) atTop (𝓝 (1/2)) := by
  have hrewrite : ∀ t > (0 : ℝ), t / (1 + 2*t) = 1 / (1/t + 2) := by
    intro t ht
    field_simp
  have hinv : Tendsto (fun t : ℝ => 1/t) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [one_div] using this
  have hsum : Tendsto (fun t : ℝ => 1/t + 2) atTop (𝓝 (0 + 2)) :=
    hinv.add tendsto_const_nhds
  have hrhs : Tendsto (fun t : ℝ => 1 / (1/t + 2)) atTop (𝓝 (1 / (0 + 2))) := by
    apply Tendsto.div tendsto_const_nhds hsum
    norm_num
  have h12 : (1 / (0 + 2) : ℝ) = 1/2 := by norm_num
  rw [h12] at hrhs
  refine Tendsto.congr' ?_ hrhs
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (hrewrite t ht).symm

end Submission.Helpers
