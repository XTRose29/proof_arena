import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue

open Filter Topology Set Metric

namespace Submission.Helpers

/-- Derivative of `t ↦ (y t)⁻²` equals 2 when `y' = -y³` and `y t ≠ 0`. -/
theorem hasDerivAt_inv_sq_of_cubic {y : ℝ → ℝ} {t : ℝ}
    (hy : HasDerivAt y (-(y t) ^ 3) t) (hne : y t ≠ 0) :
    HasDerivAt (fun s => (y s) ^ (-2 : ℤ)) 2 t := by
  have heq : ((↑(-2 : ℤ) : ℝ) * (y t) ^ ((-2 : ℤ) - 1)) * (-(y t) ^ 3) = 2 := by
    have hcast : (y t) ^ (3 : ℕ) = (y t) ^ (3 : ℤ) := (zpow_natCast _ _).symm
    rw [show (-2 : ℤ) - 1 = (-3 : ℤ) by norm_num, Int.cast_neg, Int.cast_ofNat]
    calc
      ((-2 : ℝ) * (y t) ^ (-3 : ℤ)) * (-(y t) ^ 3)
          = 2 * ((y t) ^ (-3 : ℤ) * (y t) ^ (3 : ℤ)) := by
              rw [hcast]; ring
      _ = 2 * (y t) ^ ((-3 : ℤ) + 3) := by rw [← zpow_add₀ hne]
      _ = 2 := by norm_num [zpow_zero]
  have hpow := (hasDerivAt_zpow (-2 : ℤ) (y t) (Or.inl hne)).comp t hy
  exact (hpow.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).congr_deriv heq

/-- Continuity of a cubic ODE solution on `[0, ∞)`. -/
theorem continuousOn_Ici_of_cubic {y : ℝ → ℝ}
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0) :
    ContinuousOn y (Ici 0) := by
  intro t ht
  rcases eq_or_lt_of_le (show 0 ≤ t from ht) with rfl | ht0
  · exact hy_cont
  · exact (hy_diff t ht0).continuousAt.continuousWithinAt

/-- On an interval where `y ≠ 0` and the ODE holds, `y⁻²` increases at rate 2. -/
theorem inv_sq_sub_eq {y : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hy_diff : ∀ t ∈ Ioo a b, HasDerivAt y (-(y t) ^ 3) t)
    (hy_ne : ∀ t ∈ Icc a b, y t ≠ 0)
    (hy_cont : ContinuousOn y (Icc a b)) :
    (y b) ^ (-2 : ℤ) - (y a) ^ (-2 : ℤ) = 2 * (b - a) := by
  let f : ℝ → ℝ := fun s => (y s) ^ (-2 : ℤ)
  have hf_cont : ContinuousOn f (Icc a b) :=
    ContinuousOn.zpow₀ hy_cont (-2) fun t ht => Or.inl (hy_ne t ht)
  have hf_diff : ∀ t ∈ Ioo a b, HasDerivAt f 2 t := fun t ht =>
    hasDerivAt_inv_sq_of_cubic (hy_diff t ht) (hy_ne t (Ioo_subset_Icc_self ht))
  obtain ⟨c, _, hc⟩ :=
    exists_hasDerivAt_eq_slope f (fun _ => (2 : ℝ)) hab hf_cont fun t ht => hf_diff t ht
  have hba : (b - a : ℝ) ≠ 0 := sub_ne_zero.mpr hab.ne'
  have : f b - f a = 2 * (b - a) := by
    rw [eq_div_iff hba] at hc
    linarith
  exact this

/-- Energy identity under positivity only on `[0, T)`. -/
theorem inv_sq_eq_of_pos_before {y : ℝ → ℝ} {T : ℝ} (_hTpos : 0 < T)
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    (hy0 : y 0 = 1)
    (hy_pos_before : ∀ s, 0 ≤ s → s < T → 0 < y s) :
    ∀ b, 0 < b → b < T → (y b) ^ (-2 : ℤ) = 1 + 2 * b := by
  have hy_contOn : ContinuousOn y (Ici 0) := continuousOn_Ici_of_cubic hy_diff hy_cont
  intro b hb0 hbT
  have hstep : ∀ a, 0 < a → a < b →
      (y b) ^ (-2 : ℤ) - (y a) ^ (-2 : ℤ) = 2 * (b - a) := by
    intro a ha0 hab
    apply inv_sq_sub_eq hab
    · intro s hs; exact hy_diff s (lt_trans ha0 hs.1)
    · intro s hs
      have hs0 : 0 ≤ s := le_trans (le_of_lt ha0) hs.1
      have hsT : s < T := lt_of_le_of_lt hs.2 hbT
      exact (hy_pos_before s hs0 hsT).ne'
    · exact hy_contOn.mono fun s hs => le_trans (le_of_lt ha0) hs.1
  have hlim1 : Tendsto (fun a : ℝ => (y a) ^ (-2 : ℤ)) (𝓝[>] 0) (𝓝 1) := by
    have hy_lim : Tendsto y (𝓝[Ici 0] 0) (𝓝 1) := by
      simpa [hy0] using hy_cont.tendsto
    have hy_lim' : Tendsto y (𝓝[>] 0) (𝓝 1) :=
      hy_lim.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    have hpow : ContinuousAt (fun x : ℝ => x ^ (-2 : ℤ)) (1 : ℝ) :=
      continuousAt_zpow₀ (1 : ℝ) (-2 : ℤ) (Or.inl (by norm_num))
    have : Tendsto (fun a => (y a) ^ (-2 : ℤ)) (𝓝[>] 0) (𝓝 ((1 : ℝ) ^ (-2 : ℤ))) :=
      hpow.tendsto.comp hy_lim'
    convert this
    norm_num [zpow_neg, zpow_two, inv_one]
  have hlim_a' : Tendsto (fun a : ℝ => (y a) ^ (-2 : ℤ) - 2 * a) (𝓝[>] 0) (𝓝 1) := by
    have ha : Tendsto (fun a : ℝ => (2 : ℝ) * a) (𝓝[>] 0) (𝓝 0) := by
      simpa using (continuous_const_mul (2 : ℝ)).continuousAt.tendsto.comp
        (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 0)))
    convert hlim1.sub ha using 1
    ring_nf
  have heq : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      (y b) ^ (-2 : ℤ) - 2 * b = (y a) ^ (-2 : ℤ) - 2 * a := by
    filter_upwards [Ioo_mem_nhdsGT hb0] with a ha
    have := hstep a ha.1 ha.2
    linarith
  have hconst : (y b) ^ (-2 : ℤ) - 2 * b = 1 := by
    have htend : Tendsto (fun _ : ℝ => (y b) ^ (-2 : ℤ) - 2 * b) (𝓝[>] 0) (𝓝 1) :=
      Tendsto.congr' (heq.mono fun _ h => h.symm) hlim_a'
    exact tendsto_nhds_unique tendsto_const_nhds htend
  linarith

/-- Energy identity `(y t)⁻² = 1 + 2 t` for `t ≥ 0`, assuming positivity on `[0, ∞)`. -/
theorem inv_sq_eq_of_pos {y : ℝ → ℝ}
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    (hy0 : y 0 = 1)
    (hy_pos : ∀ t : ℝ, 0 ≤ t → 0 < y t) :
    ∀ t : ℝ, 0 ≤ t → (y t) ^ (-2 : ℤ) = 1 + 2 * t := by
  intro t ht
  rcases eq_or_lt_of_le ht with rfl | ht0
  · simp [hy0, zpow_neg, zpow_two, inv_one]
  exact inv_sq_eq_of_pos_before (by linarith : (0 : ℝ) < t + 1) hy_diff hy_cont hy0
    (fun s hs0 _ => hy_pos s hs0) t ht0 (by linarith)

/-- From `(y t)⁻² = 1 + 2 t` and `y t > 0`, recover `y t = 1 / √(1 + 2 t)`. -/
theorem eq_explicit_of_inv_sq {y : ℝ → ℝ} {t : ℝ}
    (hinv : (y t) ^ (-2 : ℤ) = 1 + 2 * t) (hy_pos : 0 < y t) :
    y t = (Real.sqrt (1 + 2 * t))⁻¹ := by
  have h : ((y t)⁻¹) ^ 2 = 1 + 2 * t := by
    simpa [zpow_neg, zpow_two, pow_two] using hinv
  have hsq : (y t) ^ 2 = (1 + 2 * t)⁻¹ := by
    calc
      (y t) ^ 2 = ((y t)⁻¹)⁻¹ ^ 2 := by simp
      _ = ((y t)⁻¹ ^ 2)⁻¹ := by rw [← inv_pow]
      _ = (1 + 2 * t)⁻¹ := by rw [h]
  rw [← Real.sqrt_sq (le_of_lt hy_pos), hsq, Real.sqrt_inv]

/-- Asymptotics of the explicit profile: `√t / √(1+2t) → 1/√2`. -/
theorem tendsto_explicit_asymptotic :
    Tendsto (fun t : ℝ => Real.sqrt t / Real.sqrt (1 + 2 * t)) atTop (𝓝 (1 / Real.sqrt 2)) := by
  have hform : ∀ᶠ t : ℝ in atTop,
      Real.sqrt t / Real.sqrt (1 + 2 * t) = Real.sqrt (1 / (t⁻¹ + 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h3 : 0 ≤ t := le_of_lt ht
    have hdiv : t / (1 + 2 * t) = 1 / (t⁻¹ + 2) := by
      field_simp [ht.ne']
    rw [← Real.sqrt_div h3 (1 + 2 * t), hdiv]
  refine Tendsto.congr' (EventuallyEq.symm hform) ?_
  have hlim : Tendsto (fun t : ℝ => (t⁻¹ + 2 : ℝ)) atTop (𝓝 2) := by
    convert tendsto_inv_atTop_zero.add (tendsto_const_nhds (x := (2 : ℝ))) using 1
    simp
  have hsqrt : ContinuousAt (fun x : ℝ => Real.sqrt (1 / x)) 2 := by
    refine ContinuousAt.comp Real.continuous_sqrt.continuousAt ?_
    exact ContinuousAt.div continuousAt_const continuousAt_id (by norm_num : (2 : ℝ) ≠ 0)
  have hmain : Tendsto (fun t : ℝ => Real.sqrt (1 / (t⁻¹ + 2))) atTop (𝓝 (Real.sqrt (1 / 2))) := by
    convert hsqrt.tendsto.comp hlim
    simp
  convert hmain
  rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one]

/-- A solution of the cubic ODE with `y 0 = 1` stays strictly positive on `[0, ∞)`. -/
theorem pos_of_cubic {y : ℝ → ℝ}
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0)
    (hy0 : y 0 = 1) :
    ∀ t : ℝ, 0 ≤ t → 0 < y t := by
  have hy_contOn : ContinuousOn y (Ici 0) := continuousOn_Ici_of_cubic hy_diff hy_cont
  intro t₀ ht₀
  by_contra hne
  replace hne : y t₀ ≤ 0 := le_of_not_gt hne
  have hzero_exists : ∃ T ∈ Icc (0 : ℝ) t₀, y T = 0 := by
    have hcont : ContinuousOn y (Icc 0 t₀) := hy_contOn.mono Icc_subset_Ici_self
    have hmem : (0 : ℝ) ∈ Icc (y t₀) (y 0) := by
      rw [hy0]; exact ⟨hne, by norm_num⟩
    obtain ⟨T, hT, hTy⟩ := (intermediate_value_Icc' ht₀ hcont) hmem
    exact ⟨T, hT, hTy⟩
  let Z : Set ℝ := Icc 0 t₀ ∩ y ⁻¹' {0}
  have hZ_ne : Z.Nonempty := by
    obtain ⟨T, hT, hTy⟩ := hzero_exists
    exact ⟨T, hT, by simp [hTy]⟩
  have hZ_closed : IsClosed Z :=
    (hy_contOn.mono Icc_subset_Ici_self).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_singleton
  have hZ_compact : IsCompact Z :=
    IsCompact.of_isClosed_subset isCompact_Icc hZ_closed inter_subset_left
  obtain ⟨T, hTZ, hTmin⟩ := hZ_compact.exists_isMinOn hZ_ne continuousOn_id
  have hT0 : 0 ≤ T := hTZ.1.1
  have hTt₀ : T ≤ t₀ := hTZ.1.2
  have hTy : y T = 0 := by simpa using hTZ.2
  have hTpos : 0 < T := by
    by_contra hTle
    replace hTle : T ≤ 0 := le_of_not_gt hTle
    have hTeq : T = 0 := le_antisymm hTle hT0
    rw [hTeq, hy0] at hTy
    norm_num at hTy
  have hy_pos_before : ∀ s, 0 ≤ s → s < T → 0 < y s := by
    intro s hs0 hsT
    by_contra hys
    replace hys : y s ≤ 0 := le_of_not_gt hys
    have hcont : ContinuousOn y (Icc 0 s) := hy_contOn.mono Icc_subset_Ici_self
    have hmem : (0 : ℝ) ∈ Icc (y s) (y 0) := by
      rw [hy0]; exact ⟨hys, by norm_num⟩
    obtain ⟨U, hU, hUy⟩ := (intermediate_value_Icc' hs0 hcont) hmem
    have hUZ : U ∈ Z := by
      refine ⟨⟨hU.1, le_trans hU.2 (le_trans (le_of_lt hsT) hTt₀)⟩, ?_⟩
      simp [hUy]
    have : T ≤ U := hTmin hUZ
    linarith [hU.2]
  have hform := inv_sq_eq_of_pos_before hTpos hy_diff hy_cont hy0 hy_pos_before
  -- Continuity at the first zero forces y small nearby, contradicting energy identity
  have hbound : 0 < 1 + 2 * T := by linarith
  let ε : ℝ := (Real.sqrt (2 * (1 + 2 * T)))⁻¹
  have hεpos : 0 < ε := inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hcontT : ContinuousWithinAt y (Ici 0) T := hy_contOn T (le_of_lt hTpos)
  obtain ⟨δ, hδpos, hδ⟩ := (continuousWithinAt_iff.mp hcontT) ε hεpos
  let d : ℝ := min (δ / 2) (T / 2)
  have hdpos : 0 < d := lt_min (half_pos hδpos) (half_pos hTpos)
  let b : ℝ := T - d
  have hb0 : 0 < b := by
    have : d ≤ T / 2 := min_le_right _ _
    linarith
  have hbT : b < T := sub_lt_self _ hdpos
  have hdist : dist b T < δ := by
    have : T - b = d := by ring
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_of_lt hbT)), this]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδpos)
  have hyb_pos : 0 < y b := hy_pos_before b (le_of_lt hb0) hbT
  have hby : y b < ε := by
    have := hδ (le_of_lt hb0) hdist
    rwa [hTy, Real.dist_eq, sub_zero, abs_of_pos hyb_pos] at this
  have hεinv_sq : ε⁻¹ ^ 2 = 2 * (1 + 2 * T) := by
    simp only [ε, inv_inv]
    rw [Real.sq_sqrt (by positivity)]
  have hyb_inv_sq : (y b) ^ (-2 : ℤ) = (y b)⁻¹ ^ 2 := by
    simp [zpow_neg, zpow_two, pow_two]
  have hbig : 2 * (1 + 2 * T) < (y b) ^ (-2 : ℤ) := by
    have h1 : ε⁻¹ < (y b)⁻¹ := (inv_lt_inv₀ hεpos hyb_pos).mpr hby
    have h2 : ε⁻¹ ^ 2 < (y b)⁻¹ ^ 2 := by
      nlinarith [inv_pos.mpr hεpos, inv_pos.mpr hyb_pos, h1]
    rwa [hyb_inv_sq, ← hεinv_sq]
  have hsmall : (y b) ^ (-2 : ℤ) < 2 * (1 + 2 * T) := by
    rw [hform b hb0 hbT]
    linarith
  linarith

end Submission.Helpers
