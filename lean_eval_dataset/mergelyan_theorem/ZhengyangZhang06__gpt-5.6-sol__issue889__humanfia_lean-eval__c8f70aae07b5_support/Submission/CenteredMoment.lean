import Submission.KernelExpansion

open Set
open scoped Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- At every frontier point one can choose an exterior pole whose distance
is comparable to any prescribed positive localization scale.  Connectedness
is used with two overlapping radial regions; compactness supplies a point of
the complement in the far region. -/
theorem exists_compl_point_controlled_distance_of_mem_frontier
    (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    {x : ℂ} (hx : x ∈ frontier K) (r : ℝ) (hr : 0 < r) :
    ∃ a ∈ Kᶜ, 3 * r < dist x a ∧ dist x a < 4 * r := by
  let U : Set ℂ := Metric.ball x (4 * r)
  let V : Set ℂ := (Metric.closedBall x (3 * r))ᶜ
  have hUopen : IsOpen U :=
    Metric.isOpen_ball
  have hVopen : IsOpen V :=
    Metric.isClosed_closedBall.isOpen_compl
  have hcover : Kᶜ ⊆ U ∪ V := by
    intro z hz
    by_cases hzx : dist z x < 4 * r
    · exact Or.inl (by simpa only [U, Metric.mem_ball] using hzx)
    · apply Or.inr
      simp only [V, mem_compl_iff, Metric.mem_closedBall, not_le]
      have hfour : 4 * r ≤ dist z x :=
        le_of_not_gt hzx
      linarith
  have hnear : (Kᶜ ∩ U).Nonempty := by
    have hxclosure : x ∈ closure (Kᶜ) := by
      rw [frontier_eq_closure_inter_closure] at hx
      exact hx.2
    obtain ⟨a, haKc, hax⟩ :=
      (Metric.mem_closure_iff.mp hxclosure)
        (4 * r) (by positivity)
    exact ⟨a, haKc, by
      simpa only [U, Metric.mem_ball, dist_comm] using hax⟩
  have hfar : (Kᶜ ∩ V).Nonempty := by
    obtain ⟨R₀, hKR₀⟩ :=
      hK.isBounded.subset_closedBall (0 : ℂ)
    let R : ℝ := max R₀ 1
    have hR : 0 < R := by
      exact lt_max_of_lt_right zero_lt_one
    have hKR : ∀ z ∈ K, ‖z‖ ≤ R := by
      intro z hz
      have hzR := hKR₀ hz
      rw [Metric.mem_closedBall, dist_zero_right] at hzR
      exact hzR.trans (le_max_left _ _)
    let T : ℝ := R + ‖x‖ + 3 * r + 1
    have hT : 0 < T := by
      dsimp [T]
      positivity
    let a : ℂ := x + T
    have hTnorm : T ≤ ‖a‖ + ‖x‖ := by
      have ha := norm_sub_le a x
      simpa [a, abs_of_pos hT] using ha
    have haR : R < ‖a‖ := by
      dsimp [T] at hTnorm
      nlinarith [norm_nonneg x]
    have haK : a ∉ K := by
      intro ha
      exact (not_lt_of_ge (hKR a ha)) haR
    have hdist : dist a x = T := by
      rw [dist_eq_norm]
      simp [a, abs_of_pos hT]
    have haV : a ∈ V := by
      simp only [V, mem_compl_iff, Metric.mem_closedBall, not_le,
        hdist]
      dsimp [T]
      nlinarith [hR, norm_nonneg x]
    exact
      ⟨a, by simpa only [mem_compl_iff] using haK, haV⟩
  obtain ⟨a, haKc, haU, haV⟩ :=
    hKc.isPreconnected U V hUopen hVopen hcover hnear hfar
  refine ⟨a, haKc, ?_, ?_⟩
  · simpa only [V, mem_compl_iff, Metric.mem_closedBall, not_le,
      dist_comm] using haV
  · simpa only [U, Metric.mem_ball, dist_comm] using haU

/-- Add a cubic resolvent term to a two-moment model so that the resulting
rational function vanishes at the chosen center `x`. -/
def centeredMomentModel
    (a x m₀ m₁ z : ℂ) : ℂ :=
  (a - z)⁻¹ * m₀ -
    (a - z)⁻¹ ^ 2 * m₁ +
    (a - z)⁻¹ ^ 3 *
      (-(a - x) ^ 2 * m₀ + (a - x) * m₁)

/-- The centered model factors by `z - x`.  Besides proving cancellation at
the center, this identity exposes the scale of the model near `x`. -/
theorem centeredMomentModel_eq
    {a x z m₀ m₁ : ℂ} (haz : a ≠ z) :
    centeredMomentModel a x m₀ m₁ z =
      (z - x) *
        (m₁ - 2 * (a - x) * m₀ + (z - x) * m₀) *
          (a - z)⁻¹ ^ 3 := by
  dsimp only [centeredMomentModel]
  field_simp [sub_ne_zero.mpr haz]
  ring

@[simp]
theorem centeredMomentModel_center
    {a x m₀ m₁ : ℂ} (hax : a ≠ x) :
    centeredMomentModel a x m₀ m₁ x = 0 := by
  rw [centeredMomentModel_eq hax]
  simp

/-- A direct near-field norm bound for the centered model. -/
theorem norm_centeredMomentModel_le
    {a x z m₀ m₁ : ℂ} (haz : a ≠ z) :
    ‖centeredMomentModel a x m₀ m₁ z‖ ≤
      ‖z - x‖ *
        (‖m₁‖ + (2 * ‖a - x‖ + ‖z - x‖) * ‖m₀‖) *
          ‖(a - z)⁻¹‖ ^ 3 := by
  rw [centeredMomentModel_eq haz]
  simp only [norm_mul, norm_pow]
  gcongr
  calc
    ‖m₁ - 2 * (a - x) * m₀ + (z - x) * m₀‖
        ≤ ‖m₁‖ + ‖2 * (a - x) * m₀‖ +
            ‖(z - x) * m₀‖ := by
      calc
        _ ≤ ‖m₁ - 2 * (a - x) * m₀‖ +
              ‖(z - x) * m₀‖ :=
          norm_add_le _ _
        _ ≤ (‖m₁‖ + ‖2 * (a - x) * m₀‖) +
              ‖(z - x) * m₀‖ := by
          gcongr
          exact norm_sub_le _ _
    _ = ‖m₁‖ +
          (2 * ‖a - x‖ + ‖z - x‖) * ‖m₀‖ := by
      simp only [norm_mul]
      norm_num
      ring

/-- The coefficient of the added cubic term has the expected cubic scale
when the first two moments have their natural linear and quadratic scales. -/
theorem norm_centeredMomentCoefficient_le
    (a x m₀ m₁ : ℂ) :
    ‖-(a - x) ^ 2 * m₀ + (a - x) * m₁‖ ≤
      ‖a - x‖ ^ 2 * ‖m₀‖ + ‖a - x‖ * ‖m₁‖ := by
  calc
    ‖-(a - x) ^ 2 * m₀ + (a - x) * m₁‖
        ≤ ‖-(a - x) ^ 2 * m₀‖ +
            ‖(a - x) * m₁‖ :=
      norm_add_le _ _
    _ = ‖a - x‖ ^ 2 * ‖m₀‖ +
          ‖a - x‖ * ‖m₁‖ := by
      simp only [norm_mul, norm_neg, norm_pow]

/-- The centered model remains in the closed polynomial algebra because it
is a cubic polynomial in a resolvent whose pole misses `K`. -/
theorem exists_centeredMomentModel_mem_polynomialClosure
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    (a : ℂ) (ha : a ∉ K) (x m₀ m₁ : ℂ) :
    ∃ u : (polynomialFunctions K).topologicalClosure,
      ∀ z : K,
        (u : C(K, ℂ)) z =
          centeredMomentModel a x m₀ m₁ (z : ℂ) := by
  obtain ⟨s, hs⟩ :=
    exists_resolvent_mem_polynomialClosure hKc ha
  let C : ℂ :=
    -(a - x) ^ 2 * m₀ + (a - x) * m₁
  let u : (polynomialFunctions K).topologicalClosure :=
    m₀ • s - m₁ • s ^ 2 + C • s ^ 3
  refine ⟨u, fun z ↦ ?_⟩
  simp [u, C, centeredMomentModel, hs, mul_comm]

/-- A finite sum of centered moment models belongs to the closed polynomial
algebra whenever all of its poles miss `K`. -/
theorem exists_centeredMomentModelSum_mem_polynomialClosure
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι]
    (a x m₀ m₁ : ι → ℂ) (ha : ∀ i, a i ∉ K) :
    ∃ u : (polynomialFunctions K).topologicalClosure,
      ∀ z : K,
        (u : C(K, ℂ)) z =
          ∑ i, centeredMomentModel
            (a i) (x i) (m₀ i) (m₁ i) (z : ℂ) := by
  classical
  choose u hu using fun i ↦
    exists_centeredMomentModel_mem_polynomialClosure
      hKc (a i) (ha i) (x i) (m₀ i) (m₁ i)
  refine ⟨∑ i, u i, fun z ↦ ?_⟩
  change
    ((polynomialFunctions K).topologicalClosure.val
      (∑ i, u i)) z =
    ∑ i, centeredMomentModel
      (a i) (x i) (m₀ i) (m₁ i) (z : ℂ)
  rw [map_sum, ContinuousMap.sum_apply]
  exact Finset.sum_congr rfl fun i _hi ↦ hu i z

end Submission.Helpers
