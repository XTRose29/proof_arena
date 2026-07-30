import Submission.Crofton

open LeanEval.Geometry.FaryMilnorProblem
open MeasureTheory
open ProbabilityTheory
open Set
open Filter
open scoped ENNReal
open scoped RealInnerProductSpace

namespace Submission.Helpers

noncomputable def dyadicSignChangeIndices (r : ℝ → Space) (n : ℕ)
    (u : Space) : Finset ℕ := by
  classical
  exact (Finset.range (2 ^ (n + 1))).filter fun i =>
    u ∈ gaussianSeparatingDirections (dyadicTangentSample r n i)
      (dyadicTangentSample r n (i + 1))

theorem dyadicSignChangeCount_eq_card (r : ℝ → Space) (n : ℕ)
    (u : Space) :
    dyadicSignChangeCount r n u =
      ((dyadicSignChangeIndices r n u).card : ℝ≥0∞) := by
  classical
  unfold dyadicSignChangeCount dyadicSignChangeIndices
  exact Finset.sum_boole _ _

theorem exists_bool_transition (b : ℕ → Bool) (i d : ℕ)
    (hneq : b i ≠ b (i + d + 1)) :
    ∃ k : ℕ, i ≤ k ∧ k ≤ i + d ∧ b k ≠ b (k + 1) := by
  induction d with
  | zero =>
      exact ⟨i, le_rfl, le_rfl, by simpa using hneq⟩
  | succ d ih =>
      by_cases hfirst : b i ≠ b (i + d + 1)
      · obtain ⟨k, hik, hkd, hk⟩ := ih hfirst
        exact ⟨k, hik, hkd.trans (by omega), hk⟩
      · refine ⟨i + d + 1, by omega, by omega, ?_⟩
        have heq : b i = b (i + d + 1) := not_ne_iff.mp hfirst
        intro hlast
        apply hneq
        exact heq.trans (by simpa [add_assoc] using hlast)

theorem exists_bool_transition_between (b : ℕ → Bool) {i j : ℕ}
    (hij : i < j) (hneq : b i ≠ b j) :
    ∃ k : ℕ, i ≤ k ∧ k < j ∧ b k ≠ b (k + 1) := by
  let d := j - i - 1
  have hj : i + d + 1 = j := by
    dsimp [d]
    omega
  obtain ⟨k, hik, hkd, hk⟩ := exists_bool_transition b i d (by simpa [hj] using hneq)
  exact ⟨k, hik, by omega, hk⟩

theorem decide_pos_ne_iff_mul_neg {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    decide (0 < x) ≠ decide (0 < y) ↔ x * y < 0 := by
  by_cases hxp : 0 < x
  · by_cases hyp : 0 < y
    · have hprod : ¬ x * y < 0 := not_lt_of_ge (mul_nonneg hxp.le hyp.le)
      simp [hxp, hyp, hprod]
    · have hyn : y < 0 := lt_of_le_of_ne (le_of_not_gt hyp) hy
      have hprod : x * y < 0 := mul_neg_of_pos_of_neg hxp hyn
      simp [hxp, hyp, hprod]
  · have hxn : x < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx
    by_cases hyp : 0 < y
    · have hprod : x * y < 0 := mul_neg_of_neg_of_pos hxn hyp
      simp [hxp, hyp, hprod]
    · have hyn : y < 0 := lt_of_le_of_ne (le_of_not_gt hyp) hy
      have hprod : ¬ x * y < 0 :=
        not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hxn.le hyn.le)
      simp [hxp, hyp, hprod]

theorem four_le_card_of_four_mem {s : Finset ℕ} {k₀ k₁ k₂ k₃ : ℕ}
    (h₀ : k₀ ∈ s) (h₁ : k₁ ∈ s) (h₂ : k₂ ∈ s) (h₃ : k₃ ∈ s)
    (h₀₁ : k₀ ≠ k₁) (h₀₂ : k₀ ≠ k₂) (h₀₃ : k₀ ≠ k₃)
    (h₁₂ : k₁ ≠ k₂) (h₁₃ : k₁ ≠ k₃) (h₂₃ : k₂ ≠ k₃) :
    4 ≤ s.card := by
  have hsub : ({k₀, k₁, k₂, k₃} : Finset ℕ) ⊆ s := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
  have hcard := Finset.card_le_card hsub
  have hfour : ({k₀, k₁, k₂, k₃} : Finset ℕ).card = 4 := by
    simp [h₀₁, h₀₂, h₀₃, h₁₂, h₁₃, h₂₃]
  omega

theorem four_le_card_cyclic_bool_transitions (b : ℕ → Bool) {N : ℕ}
    {i₀ i₁ i₂ i₃ : ℕ} (hi₀₁ : i₀ < i₁) (hi₁₂ : i₁ < i₂)
    (hi₂₃ : i₂ < i₃) (hi₃N : i₃ < N) (hcycle : b N = b 0)
    (h₀₁ : b i₀ ≠ b i₁) (h₁₂ : b i₁ ≠ b i₂)
    (h₂₃ : b i₂ ≠ b i₃) (h₃₀ : b i₃ ≠ b i₀) :
    4 ≤ ((Finset.range N).filter fun i => b i ≠ b (i + 1)).card := by
  obtain ⟨k₀, hi₀k₀, hk₀i₁, hk₀⟩ :=
    exists_bool_transition_between b hi₀₁ h₀₁
  obtain ⟨k₁, hi₁k₁, hk₁i₂, hk₁⟩ :=
    exists_bool_transition_between b hi₁₂ h₁₂
  obtain ⟨k₂, hi₂k₂, hk₂i₃, hk₂⟩ :=
    exists_bool_transition_between b hi₂₃ h₂₃
  have hk₀mem : k₀ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hk₀i₁.trans (hi₁₂.trans (hi₂₃.trans hi₃N))), hk₀⟩
  have hk₁mem : k₁ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hk₁i₂.trans (hi₂₃.trans hi₃N)), hk₁⟩
  have hk₂mem : k₂ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hk₂i₃.trans hi₃N), hk₂⟩
  by_cases h₃N : b i₃ ≠ b N
  · obtain ⟨k₃, hi₃k₃, hk₃N, hk₃⟩ :=
      exists_bool_transition_between b hi₃N h₃N
    have hk₃mem : k₃ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk₃N, hk₃⟩
    apply four_le_card_of_four_mem hk₀mem hk₁mem hk₂mem hk₃mem
    all_goals omega
  · have hNi₃ : b N = b i₃ := (not_ne_iff.mp h₃N).symm
    have h0i₀ : b 0 ≠ b i₀ := by
      rw [← hcycle, hNi₃]
      exact h₃₀
    have hi₀pos : 0 < i₀ := by
      by_contra hi₀zero
      have hi₀eq : i₀ = 0 := Nat.eq_zero_of_not_pos hi₀zero
      subst i₀
      exact h0i₀ rfl
    obtain ⟨k₃, _hzero, hk₃i₀, hk₃⟩ :=
      exists_bool_transition_between b hi₀pos h0i₀
    have hk₃mem : k₃ ∈ (Finset.range N).filter fun i => b i ≠ b (i + 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (hk₃i₀.trans (hi₀₁.trans (hi₁₂.trans (hi₂₃.trans hi₃N)))), hk₃⟩
    apply four_le_card_of_four_mem hk₀mem hk₁mem hk₂mem hk₃mem
    all_goals omega

theorem dyadicTangentSample_last {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (n : ℕ) :
    dyadicTangentSample r n (2 ^ (n + 1)) =
      dyadicTangentSample r n 0 := by
  unfold dyadicTangentSample
  have hpow : (((2 ^ (n + 1) : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [mul_div_cancel_right₀ period hpow]
  norm_num
  simpa using periodic_unitTangent hknot 0

theorem isDyadicRegular_next {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {n : ℕ} {u : Space}
    (hreg : IsDyadicRegular r n u) {i : ℕ}
    (hi : i < 2 ^ (n + 1)) :
    inner ℝ u (dyadicTangentSample r n (i + 1)) ≠ 0 := by
  by_cases hinext : i + 1 < 2 ^ (n + 1)
  · exact hreg (i + 1) (Finset.mem_range.mpr hinext)
  · have hieq : i + 1 = 2 ^ (n + 1) := by omega
    rw [hieq, dyadicTangentSample_last hknot n]
    exact hreg 0 (Finset.mem_range.mpr (by positivity))

theorem four_le_dyadicSignChangeIndices_card_of_alternating
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {n : ℕ} {u : Space}
    (hreg : IsDyadicRegular r n u) {i₀ i₁ i₂ i₃ : ℕ}
    (hi₀₁ : i₀ < i₁) (hi₁₂ : i₁ < i₂) (hi₂₃ : i₂ < i₃)
    (hi₃N : i₃ < 2 ^ (n + 1))
    (h₀₁ : inner ℝ u (dyadicTangentSample r n i₀) *
      inner ℝ u (dyadicTangentSample r n i₁) < 0)
    (h₁₂ : inner ℝ u (dyadicTangentSample r n i₁) *
      inner ℝ u (dyadicTangentSample r n i₂) < 0)
    (h₂₃ : inner ℝ u (dyadicTangentSample r n i₂) *
      inner ℝ u (dyadicTangentSample r n i₃) < 0)
    (h₃₀ : inner ℝ u (dyadicTangentSample r n i₃) *
      inner ℝ u (dyadicTangentSample r n i₀) < 0) :
    4 ≤ (dyadicSignChangeIndices r n u).card := by
  let N : ℕ := 2 ^ (n + 1)
  let b : ℕ → Bool := fun i =>
    decide (0 < inner ℝ u (dyadicTangentSample r n i))
  have hi₀N : i₀ < N := hi₀₁.trans (hi₁₂.trans (hi₂₃.trans hi₃N))
  have hi₁N : i₁ < N := hi₁₂.trans (hi₂₃.trans hi₃N)
  have hi₂N : i₂ < N := hi₂₃.trans hi₃N
  have hcycle : b N = b 0 := by
    dsimp [b, N]
    rw [dyadicTangentSample_last hknot n]
  have hb₀₁ : b i₀ ≠ b i₁ := by
    exact (decide_pos_ne_iff_mul_neg
      (hreg i₀ (Finset.mem_range.mpr hi₀N))
      (hreg i₁ (Finset.mem_range.mpr hi₁N))).2 h₀₁
  have hb₁₂ : b i₁ ≠ b i₂ := by
    exact (decide_pos_ne_iff_mul_neg
      (hreg i₁ (Finset.mem_range.mpr hi₁N))
      (hreg i₂ (Finset.mem_range.mpr hi₂N))).2 h₁₂
  have hb₂₃ : b i₂ ≠ b i₃ := by
    exact (decide_pos_ne_iff_mul_neg
      (hreg i₂ (Finset.mem_range.mpr hi₂N))
      (hreg i₃ (Finset.mem_range.mpr hi₃N))).2 h₂₃
  have hb₃₀ : b i₃ ≠ b i₀ := by
    exact (decide_pos_ne_iff_mul_neg
      (hreg i₃ (Finset.mem_range.mpr hi₃N))
      (hreg i₀ (Finset.mem_range.mpr hi₀N))).2 h₃₀
  have hfour := four_le_card_cyclic_bool_transitions b hi₀₁ hi₁₂ hi₂₃
    hi₃N hcycle hb₀₁ hb₁₂ hb₂₃ hb₃₀
  have hfilter : ((Finset.range N).filter fun i => b i ≠ b (i + 1)) =
      dyadicSignChangeIndices r n u := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, dyadicSignChangeIndices]
    constructor
    · rintro ⟨hi, hchange⟩
      refine ⟨hi, ?_⟩
      change inner ℝ u (dyadicTangentSample r n i) *
        inner ℝ u (dyadicTangentSample r n (i + 1)) < 0
      exact (decide_pos_ne_iff_mul_neg (hreg i (Finset.mem_range.mpr hi))
        (isDyadicRegular_next hknot hreg hi)).1 hchange
    · rintro ⟨hi, hchange⟩
      refine ⟨hi, ?_⟩
      apply (decide_pos_ne_iff_mul_neg (hreg i (Finset.mem_range.mpr hi))
        (isDyadicRegular_next hknot hreg hi)).2
      exact hchange
  rw [hfilter] at hfour
  exact hfour

theorem dyadicTangentSample_refine_iter (r : ℝ → Space)
    (m d i : ℕ) :
    dyadicTangentSample r (m + d) (2 ^ d * i) =
      dyadicTangentSample r m i := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show m + (d + 1) = (m + d) + 1 by omega]
      rw [show 2 ^ (d + 1) * i = 2 * (2 ^ d * i) by ring]
      rw [dyadicTangentSample_refine_even]
      exact ih

theorem dyadicTangentSample_refine_of_le (r : ℝ → Space)
    {m n i : ℕ} (hmn : m ≤ n) :
    dyadicTangentSample r n (2 ^ (n - m) * i) =
      dyadicTangentSample r m i := by
  have hn : m + (n - m) = n := Nat.add_sub_of_le hmn
  simpa only [hn] using dyadicTangentSample_refine_iter r m (n - m) i

def HasFourAlternatingDyadicSigns (r : ℝ → Space) (u : Space) : Prop :=
  ∃ m i₀ i₁ i₂ i₃ : ℕ,
    i₀ < i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < 2 ^ (m + 1) ∧
    inner ℝ u (dyadicTangentSample r m i₀) *
      inner ℝ u (dyadicTangentSample r m i₁) < 0 ∧
    inner ℝ u (dyadicTangentSample r m i₁) *
      inner ℝ u (dyadicTangentSample r m i₂) < 0 ∧
    inner ℝ u (dyadicTangentSample r m i₂) *
      inner ℝ u (dyadicTangentSample r m i₃) < 0 ∧
    inner ℝ u (dyadicTangentSample r m i₃) *
      inner ℝ u (dyadicTangentSample r m i₀) < 0

theorem exists_unit_not_hasFourAlternatingDyadicSigns_of_lt
    {r : ℝ → Space} (hknot : IsSmoothKnot r)
    (hK : totalCurvature r < 4 * Real.pi) :
    ∃ u : Space, ‖u‖ = 1 ∧ ¬ HasFourAlternatingDyadicSigns r u := by
  classical
  have hwitness : ∀ n : ℕ, ∃ u : Space, ‖u‖ = 1 ∧
      IsDyadicRegular r n u ∧ dyadicSignChangeCount r n u < 4 := by
    intro n
    exact exists_unit_regular_dyadicSignChangeCount_lt_four hknot n
      ((dyadicSphericalLength_le_totalCurvature hknot n).trans_lt hK)
  choose u hunorm hureg hucount using hwitness
  have huSphere : ∀ n, u n ∈ Metric.sphere (0 : Space) 1 := by
    intro n
    simpa [Metric.mem_sphere, dist_eq_norm] using hunorm n
  obtain ⟨v, hvSphere, φ, hφmono, hconv⟩ :=
    (isCompact_sphere (0 : Space) 1).tendsto_subseq huSphere
  have hvnorm : ‖v‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hvSphere
  refine ⟨v, hvnorm, ?_⟩
  rintro ⟨m, i₀, i₁, i₂, i₃, hi₀₁, hi₁₂, hi₂₃, hi₃N,
    h₀₁, h₁₂, h₂₃, h₃₀⟩
  let x₀ := dyadicTangentSample r m i₀
  let x₁ := dyadicTangentSample r m i₁
  let x₂ := dyadicTangentSample r m i₂
  let x₃ := dyadicTangentSample r m i₃
  have hinner (x : Space) :
      Tendsto (fun k => inner ℝ (u (φ k)) x) atTop
        (nhds (inner ℝ v x)) := by
    have hc : Continuous (fun w : Space => inner ℝ w x) :=
      continuous_id.inner continuous_const
    change Tendsto ((fun w : Space => inner ℝ w x) ∘ (u ∘ φ)) atTop
      (nhds (inner ℝ v x))
    exact hc.continuousAt.tendsto.comp hconv
  have he₀₁ : ∀ᶠ k in atTop,
      inner ℝ (u (φ k)) x₀ * inner ℝ (u (φ k)) x₁ < 0 := by
    have ht := (hinner x₀).mul (hinner x₁)
    exact (tendsto_order.1 ht).2 0 (by simpa [x₀, x₁] using h₀₁)
  have he₁₂ : ∀ᶠ k in atTop,
      inner ℝ (u (φ k)) x₁ * inner ℝ (u (φ k)) x₂ < 0 := by
    have ht := (hinner x₁).mul (hinner x₂)
    exact (tendsto_order.1 ht).2 0 (by simpa [x₁, x₂] using h₁₂)
  have he₂₃ : ∀ᶠ k in atTop,
      inner ℝ (u (φ k)) x₂ * inner ℝ (u (φ k)) x₃ < 0 := by
    have ht := (hinner x₂).mul (hinner x₃)
    exact (tendsto_order.1 ht).2 0 (by simpa [x₂, x₃] using h₂₃)
  have he₃₀ : ∀ᶠ k in atTop,
      inner ℝ (u (φ k)) x₃ * inner ℝ (u (φ k)) x₀ < 0 := by
    have ht := (hinner x₃).mul (hinner x₀)
    exact (tendsto_order.1 ht).2 0 (by simpa [x₃, x₀] using h₃₀)
  have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hem : ∀ᶠ k in atTop, m ≤ φ k :=
    hφtop.eventually (eventually_ge_atTop m)
  obtain ⟨k, hk₀₁, hk₁₂, hk₂₃, hk₃₀, hmk⟩ :=
    (he₀₁.and (he₁₂.and (he₂₃.and (he₃₀.and hem)))).exists
  let n := φ k
  let c : ℕ := 2 ^ (n - m)
  let j₀ := c * i₀
  let j₁ := c * i₁
  let j₂ := c * i₂
  let j₃ := c * i₃
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hj₀₁ : j₀ < j₁ := by
    dsimp [j₀, j₁]
    exact (Nat.mul_lt_mul_left hcpos).2 hi₀₁
  have hj₁₂ : j₁ < j₂ := by
    dsimp [j₁, j₂]
    exact (Nat.mul_lt_mul_left hcpos).2 hi₁₂
  have hj₂₃ : j₂ < j₃ := by
    dsimp [j₂, j₃]
    exact (Nat.mul_lt_mul_left hcpos).2 hi₂₃
  have hpow : c * 2 ^ (m + 1) = 2 ^ (n + 1) := by
    dsimp [c]
    rw [← pow_add]
    congr 1
    omega
  have hj₃N : j₃ < 2 ^ (n + 1) := by
    dsimp [j₃]
    calc
      c * i₃ < c * 2 ^ (m + 1) := (Nat.mul_lt_mul_left hcpos).2 hi₃N
      _ = 2 ^ (n + 1) := hpow
  have hsamp₀ : dyadicTangentSample r n j₀ = x₀ := by
    dsimp [j₀, c, x₀]
    exact dyadicTangentSample_refine_of_le r hmk
  have hsamp₁ : dyadicTangentSample r n j₁ = x₁ := by
    dsimp [j₁, c, x₁]
    exact dyadicTangentSample_refine_of_le r hmk
  have hsamp₂ : dyadicTangentSample r n j₂ = x₂ := by
    dsimp [j₂, c, x₂]
    exact dyadicTangentSample_refine_of_le r hmk
  have hsamp₃ : dyadicTangentSample r n j₃ = x₃ := by
    dsimp [j₃, c, x₃]
    exact dyadicTangentSample_refine_of_le r hmk
  have hcard : 4 ≤ (dyadicSignChangeIndices r n (u n)).card := by
    apply four_le_dyadicSignChangeIndices_card_of_alternating
      hknot (hureg n) hj₀₁ hj₁₂ hj₂₃ hj₃N
    · simpa [n, hsamp₀, hsamp₁] using hk₀₁
    · simpa [n, hsamp₁, hsamp₂] using hk₁₂
    · simpa [n, hsamp₂, hsamp₃] using hk₂₃
    · simpa [n, hsamp₃, hsamp₀] using hk₃₀
  have hcountLower : (4 : ℝ≥0∞) ≤ dyadicSignChangeCount r n (u n) := by
    rw [dyadicSignChangeCount_eq_card]
    exact_mod_cast hcard
  exact (not_lt_of_ge hcountLower) (hucount n)

theorem exists_dyadic_fraction_mem_Ioo {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b < 1) :
    ∃ n i : ℕ, i < 2 ^ (n + 1) ∧
      a < (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) ∧
      (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) < b := by
  let c : ℝ := (a + b) / 2
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  have hfloor : Tendsto
      (fun n : ℕ => (⌊c * (2 : ℝ) ^ (n + 1)⌋₊ : ℝ) /
        (2 : ℝ) ^ (n + 1)) atTop (nhds c) := by
    exact (tendsto_nat_floor_mul_div_atTop hc0).comp hpow
  have hmem : Ioo a b ∈ nhds c := isOpen_Ioo.mem_nhds ⟨hac, hcb⟩
  obtain ⟨n, hn⟩ := (hfloor.eventually hmem).exists
  let i : ℕ := ⌊c * (2 : ℝ) ^ (n + 1)⌋₊
  have hn' : a < (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) ∧
      (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) < b := by
    simpa [i] using hn
  have hiReal : (i : ℝ) < (((2 ^ (n + 1) : ℕ) : ℝ)) := by
    apply (div_lt_one (by positivity)).mp
    exact hn'.2.trans hb1
  have hi : i < 2 ^ (n + 1) := by exact_mod_cast hiReal
  exact ⟨n, i, hi, hn'⟩

theorem eventually_exists_dyadic_fraction_mem_Ioo {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b < 1) :
    ∀ᶠ n : ℕ in atTop, ∃ i : ℕ, i < 2 ^ (n + 1) ∧
      a < (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) ∧
      (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) < b := by
  let c : ℝ := (a + b) / 2
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  have hfloor : Tendsto
      (fun n : ℕ => (⌊c * (2 : ℝ) ^ (n + 1)⌋₊ : ℝ) /
        (2 : ℝ) ^ (n + 1)) atTop (nhds c) := by
    exact (tendsto_nat_floor_mul_div_atTop hc0).comp hpow
  have hmem : Ioo a b ∈ nhds c := isOpen_Ioo.mem_nhds ⟨hac, hcb⟩
  filter_upwards [hfloor.eventually hmem] with n hn
  let i : ℕ := ⌊c * (2 : ℝ) ^ (n + 1)⌋₊
  have hn' : a < (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) ∧
      (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) < b := by
    simpa [i] using hn
  have hiReal : (i : ℝ) < (((2 ^ (n + 1) : ℕ) : ℝ)) := by
    apply (div_lt_one (by positivity)).mp
    exact hn'.2.trans hb1
  exact ⟨i, by exact_mod_cast hiReal, hn'⟩

theorem eventually_exists_dyadic_parameter_mem_Ioo {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a < b) (hb : b < period) :
    ∀ᶠ n : ℕ in atTop, ∃ i : ℕ, i < 2 ^ (n + 1) ∧
      period * (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) ∈ Ioo a b := by
  have hp : 0 < period := by simp [period, Real.pi_pos]
  have hfrac := eventually_exists_dyadic_fraction_mem_Ioo
    (a := a / period) (b := b / period)
    (div_nonneg ha0 hp.le) ((div_lt_div_iff_of_pos_right hp).2 hab)
    ((div_lt_one hp).2 hb)
  filter_upwards [hfrac] with n hn
  obtain ⟨i, hi, hia, hib⟩ := hn
  refine ⟨i, hi, ?_, ?_⟩
  · have h := (div_lt_iff₀ hp).mp hia
    calc
      a < (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) * period := h
      _ = period * (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) := by ring
  · have h := (lt_div_iff₀ hp).mp hib
    calc
      period * (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) =
          (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) * period := by ring
      _ < b := h

theorem eventually_exists_dyadic_parameter_same_sign
    {r : ℝ → Space} (hknot : IsSmoothKnot r) (u : Space)
    {L t R : ℝ} (hL0 : 0 ≤ L) (hLt : L < t) (htR : t < R)
    (hRP : R ≤ period) (hgt : directionalUnitTangent r u t ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∃ i : ℕ, i < 2 ^ (n + 1) ∧
      period * (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) ∈ Ioo L R ∧
      0 < directionalUnitTangent r u
          (period * (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ))) *
        directionalUnitTangent r u t := by
  let S : Set ℝ := {z | 0 < directionalUnitTangent r u z *
    directionalUnitTangent r u t}
  have hSopen : IsOpen S := by
    exact isOpen_lt continuous_const
      ((continuous_directionalUnitTangent hknot u).mul continuous_const)
  have htS : t ∈ S := by
    change 0 < directionalUnitTangent r u t * directionalUnitTangent r u t
    exact mul_self_pos.mpr hgt
  have hnear : S ∩ Ioo L R ∈ nhds t :=
    inter_mem (hSopen.mem_nhds htS) (Ioo_mem_nhds hLt htR)
  obtain ⟨l, q, htI, hlq⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let A : ℝ := max l L
  let B : ℝ := min q R
  have hAt : A < t := by
    dsimp [A]
    exact max_lt htI.1 hLt
  have htB : t < B := by
    dsimp [B]
    exact lt_min htI.2 htR
  let a : ℝ := (A + t) / 2
  let b : ℝ := (t + B) / 2
  have ha0 : 0 ≤ a := by
    dsimp [a, A]
    have : 0 ≤ max l L := le_max_of_le_right hL0
    linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hbP : b < period := by
    dsimp [b]
    have hBP : B ≤ period := by
      exact (min_le_right q R).trans hRP
    linarith
  have hdyadic := eventually_exists_dyadic_parameter_mem_Ioo ha0 hab hbP
  filter_upwards [hdyadic] with n hn
  obtain ⟨i, hi, hia, hib⟩ := hn
  let z : ℝ := period * (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ))
  have hzAB : z ∈ Ioo A B := by
    dsimp [z, a, b] at hia hib ⊢
    constructor <;> linarith
  have hzlu : z ∈ Ioo l q := by
    constructor
    · exact (le_max_left l L).trans_lt hzAB.1
    · exact hzAB.2.trans_le (min_le_left q R)
  have hzmem := hlq hzlu
  exact ⟨i, hi, hzmem.2, hzmem.1⟩

theorem mul_neg_of_same_sign_of_same_sign_of_mul_neg
    {a b x y : ℝ} (hax : 0 < a * x) (hby : 0 < b * y)
    (hxy : x * y < 0) : a * b < 0 := by
  rcases (mul_pos_iff.mp hax) with ⟨ha, hx⟩ | ⟨ha, hx⟩ <;>
    rcases (mul_pos_iff.mp hby) with ⟨hb, hy⟩ | ⟨hb, hy⟩ <;>
    rcases (mul_neg_iff.mp hxy) with ⟨hx', hy'⟩ | ⟨hx', hy'⟩
  all_goals try linarith
  · exact mul_neg_of_pos_of_neg ha hb
  · exact mul_neg_of_neg_of_pos ha hb

theorem dyadic_index_lt_of_parameter_lt {n i j : ℕ}
    (h : period * (i : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ)) <
      period * (j : ℝ) / (((2 ^ (n + 1) : ℕ) : ℝ))) :
    i < j := by
  have hperiod : 0 < period := by
    simp [period, Real.pi_pos]
  have hdenom : 0 < (((2 ^ (n + 1) : ℕ) : ℝ)) := by
    positivity
  have hcoef : 0 < period / (((2 ^ (n + 1) : ℕ) : ℝ)) := by
    exact div_pos hperiod hdenom
  have hscaled :
      (period / (((2 ^ (n + 1) : ℕ) : ℝ))) * (i : ℝ) <
        (period / (((2 ^ (n + 1) : ℕ) : ℝ))) * (j : ℝ) := by
    convert h using 1 <;> ring
  have hcast : (i : ℝ) < (j : ℝ) := by
    nlinarith
  exact_mod_cast hcast

def HasFourAlternatingSigns (r : ℝ → Space) (u : Space) : Prop :=
  ∃ t₀ t₁ t₂ t₃ : ℝ,
    0 < t₀ ∧ t₀ < t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < period ∧
    directionalUnitTangent r u t₀ * directionalUnitTangent r u t₁ < 0 ∧
    directionalUnitTangent r u t₁ * directionalUnitTangent r u t₂ < 0 ∧
    directionalUnitTangent r u t₂ * directionalUnitTangent r u t₃ < 0 ∧
    directionalUnitTangent r u t₃ * directionalUnitTangent r u t₀ < 0

theorem hasFourAlternatingDyadicSigns_of_hasFourAlternatingSigns
    {r : ℝ → Space} (hknot : IsSmoothKnot r) {u : Space}
    (hfour : HasFourAlternatingSigns r u) :
    HasFourAlternatingDyadicSigns r u := by
  rcases hfour with ⟨t₀, t₁, t₂, t₃, ht₀, ht₀₁, ht₁₂, ht₂₃, ht₃P,
    h₀₁, h₁₂, h₂₃, h₃₀⟩
  have hg₀ : directionalUnitTangent r u t₀ ≠ 0 := by
    intro h
    rw [h] at h₀₁
    norm_num at h₀₁
  have hg₁ : directionalUnitTangent r u t₁ ≠ 0 := by
    intro h
    rw [h] at h₀₁
    norm_num at h₀₁
  have hg₂ : directionalUnitTangent r u t₂ ≠ 0 := by
    intro h
    rw [h] at h₁₂
    norm_num at h₁₂
  have hg₃ : directionalUnitTangent r u t₃ ≠ 0 := by
    intro h
    rw [h] at h₂₃
    norm_num at h₂₃
  let q₀₁ : ℝ := (t₀ + t₁) / 2
  let q₁₂ : ℝ := (t₁ + t₂) / 2
  let q₂₃ : ℝ := (t₂ + t₃) / 2
  have hq₀₁0 : 0 ≤ q₀₁ := by dsimp [q₀₁]; linarith
  have ht₀q₀₁ : t₀ < q₀₁ := by dsimp [q₀₁]; linarith
  have hq₀₁t₁ : q₀₁ < t₁ := by dsimp [q₀₁]; linarith
  have hq₁₂t₂ : q₁₂ < t₂ := by dsimp [q₁₂]; linarith
  have ht₁q₁₂ : t₁ < q₁₂ := by dsimp [q₁₂]; linarith
  have hq₂₃t₃ : q₂₃ < t₃ := by dsimp [q₂₃]; linarith
  have ht₂q₂₃ : t₂ < q₂₃ := by dsimp [q₂₃]; linarith
  have hq₁₂P : q₁₂ ≤ period := by dsimp [q₁₂]; linarith
  have hq₂₃P : q₂₃ ≤ period := by dsimp [q₂₃]; linarith
  have hq₀₁P : q₀₁ ≤ period := by dsimp [q₀₁]; linarith
  have he₀ := eventually_exists_dyadic_parameter_same_sign hknot u
    (L := 0) (t := t₀) (R := q₀₁) le_rfl ht₀ ht₀q₀₁ hq₀₁P hg₀
  have he₁ := eventually_exists_dyadic_parameter_same_sign hknot u
    (L := q₀₁) (t := t₁) (R := q₁₂) hq₀₁0 hq₀₁t₁ ht₁q₁₂ hq₁₂P hg₁
  have he₂ := eventually_exists_dyadic_parameter_same_sign hknot u
    (L := q₁₂) (t := t₂) (R := q₂₃) (by dsimp [q₁₂]; linarith)
      hq₁₂t₂ ht₂q₂₃ hq₂₃P hg₂
  have he₃ := eventually_exists_dyadic_parameter_same_sign hknot u
    (L := q₂₃) (t := t₃) (R := period) (by dsimp [q₂₃]; linarith)
      hq₂₃t₃ ht₃P le_rfl hg₃
  obtain ⟨n, hn₀, hn₁, hn₂, hn₃⟩ :=
    (he₀.and (he₁.and (he₂.and he₃))).exists
  obtain ⟨i₀, hi₀N, hi₀band, hi₀sign⟩ := hn₀
  obtain ⟨i₁, hi₁N, hi₁band, hi₁sign⟩ := hn₁
  obtain ⟨i₂, hi₂N, hi₂band, hi₂sign⟩ := hn₂
  obtain ⟨i₃, hi₃N, hi₃band, hi₃sign⟩ := hn₃
  have hi₀₁ : i₀ < i₁ := dyadic_index_lt_of_parameter_lt
    (hi₀band.2.trans hi₁band.1)
  have hi₁₂ : i₁ < i₂ := dyadic_index_lt_of_parameter_lt
    (hi₁band.2.trans hi₂band.1)
  have hi₂₃ : i₂ < i₃ := dyadic_index_lt_of_parameter_lt
    (hi₂band.2.trans hi₃band.1)
  refine ⟨n, i₀, i₁, i₂, i₃, hi₀₁, hi₁₂, hi₂₃, hi₃N, ?_, ?_, ?_, ?_⟩
  · exact mul_neg_of_same_sign_of_same_sign_of_mul_neg hi₀sign hi₁sign h₀₁
  · exact mul_neg_of_same_sign_of_same_sign_of_mul_neg hi₁sign hi₂sign h₁₂
  · exact mul_neg_of_same_sign_of_same_sign_of_mul_neg hi₂sign hi₃sign h₂₃
  · exact mul_neg_of_same_sign_of_same_sign_of_mul_neg hi₃sign hi₀sign h₃₀

theorem exists_unit_not_hasFourAlternatingSigns_of_lt
    {r : ℝ → Space} (hknot : IsSmoothKnot r)
    (hK : totalCurvature r < 4 * Real.pi) :
    ∃ u : Space, ‖u‖ = 1 ∧ ¬ HasFourAlternatingSigns r u := by
  obtain ⟨u, hu, hfour⟩ :=
    exists_unit_not_hasFourAlternatingDyadicSigns_of_lt hknot hK
  exact ⟨u, hu, fun h => hfour
    (hasFourAlternatingDyadicSigns_of_hasFourAlternatingSigns hknot h)⟩

end Submission.Helpers

