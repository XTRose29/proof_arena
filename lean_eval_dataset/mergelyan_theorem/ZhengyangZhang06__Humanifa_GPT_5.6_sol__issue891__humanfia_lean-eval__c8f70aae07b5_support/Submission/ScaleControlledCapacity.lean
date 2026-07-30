import Submission.PolygonalCapacity

open Filter Function Metric Set
open scoped Pointwise Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- A polygonal branch cut supplies bounded Laurent-capacity data whose
threshold, linear norm bound, and cubic remainder have their natural
localization scales.  The initial and terminal vertices are retained so the
leading coefficients remain explicit. -/
theorem exists_scaleControlled_polygonalCapacity
    {K : Set ℂ} [CompactSpace K]
    (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (c₂ : ℂ) (B ρ : ℝ) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hTaylor :
      ∀ s : ℂ, ‖s‖ ≤ ρ →
        ‖baseCapacityGerm s -
            (s * (1 / 100) + s ^ 2 * c₂)‖ ≤
          B * ‖s‖ ^ 3)
    {x : ℂ} (hx : x ∈ frontier K)
    (r : ℝ) (hr : 0 < r) :
    ∃ (q a : ℂ) (R : ℝ)
        (d : BoundedLaurentCapacity K a R),
      dist x q < r ∧
      dist x a = 3 * r ∧
      2 * r < ‖q - a‖ ∧
      ‖q - a‖ < 4 * r ∧
      R = max (7 * r) (4 * r * ρ⁻¹) ∧
      d.c₁ = (q - a) * (1 / 100) ∧
      d.c₂ = (q - a) ^ 2 * c₂ ∧
      d.L =
        4 *
          (B * ρ ^ 2 + ‖(1 / 100 : ℂ)‖ +
            ρ * ‖c₂‖) * r ∧
      d.B = 64 * B * r ^ 3 := by
  obtain ⟨N, p, hN, htrace, hq, ha⟩ :=
    exists_local_complement_polygon K hK hKc hx r hr
  have htraceKc :
      polygonalTrace p N ⊆ Kᶜ :=
    htrace.trans inter_subset_left
  have htraceBall :
      polygonalTrace p N ⊆
        Metric.closedBall x (3 * r) :=
    htrace.trans inter_subset_right
  have hend : p 0 ≠ p N := by
    intro heq
    rw [heq, ha] at hq
    linarith
  have hdeltaLower :
      2 * r < ‖p 0 - p N‖ := by
    rw [← dist_eq_norm]
    have htri :
        dist x (p N) ≤
          dist x (p 0) + dist (p 0) (p N) :=
      dist_triangle _ _ _
    rw [ha] at htri
    linarith
  have hdeltaUpper :
      ‖p 0 - p N‖ < 4 * r := by
    rw [← dist_eq_norm]
    calc
      dist (p 0) (p N) ≤
          dist (p 0) x + dist x (p N) :=
        dist_triangle _ _ _
      _ < r + 3 * r := by
        rw [ha]
        have hq' : dist (p 0) x < r := by
          simpa only [dist_comm] using hq
        linarith
      _ = 4 * r := by ring
  let G : ℂ → ℂ :=
    polygonalCapacityFunction p N
  have hKtrace :
      K ⊆ (polygonalTrace p N)ᶜ := by
    intro z hzK hzTrace
    exact htraceKc hzTrace hzK
  have hGanalytic :
      AnalyticOnNhd ℂ G ((polygonalTrace p N)ᶜ) := by
    apply DifferentiableOn.analyticOnNhd
    · intro z hz
      exact
        (differentiableAt_polygonalCapacityFunction
          hN hend hz).differentiableWithinAt
    · exact (isCompact_polygonalTrace p N).isClosed.isOpen_compl
  obtain ⟨u, hu⟩ :=
    exists_analyticOnNhd_restriction_mem_polynomialClosure
      hKc G
      (isCompact_polygonalTrace p N).isClosed.isOpen_compl
      hKtrace hGanalytic
  let R : ℝ :=
    max (7 * r) (4 * r * ρ⁻¹)
  let L₀ : ℝ :=
    B * ρ ^ 2 + ‖(1 / 100 : ℂ)‖ + ρ * ‖c₂‖
  let L : ℝ :=
    4 * L₀ * r
  let B₃ : ℝ :=
    64 * B * r ^ 3
  have hRpos : 0 < R := by
    exact
      (by positivity : 0 < 7 * r).trans_le
        (le_max_left _ _)
  have hL₀ : 0 ≤ L₀ := by
    dsimp only [L₀]
    positivity
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hB₃ : 0 ≤ B₃ := by
    dsimp only [B₃]
    positivity
  have hfarBase
      (z : K) (hz : R ≤ dist (p N) (z : ℂ)) :
      G z =
        baseCapacityGerm
          ((p 0 - p N) * (p N - (z : ℂ))⁻¹) := by
    have h7 :
        7 * r ≤ dist (p N) (z : ℂ) :=
      (le_max_left _ _).trans hz
    have hzExterior :
        (z : ℂ) ∈
          (Metric.closedBall (p N) (6 * r))ᶜ := by
      simp only [mem_compl_iff, Metric.mem_closedBall, not_le]
      rw [dist_comm]
      linarith
    calc
      G z =
          endpointCapacityGerm (p 0) (p N)
            (p N - (z : ℂ))⁻¹ :=
        polygonalCapacityFunction_eq_endpointCapacityGerm
          hN hr htraceBall hq ha hzExterior
      _ =
          baseCapacityGerm
            ((p 0 - p N) *
              (p N - (z : ℂ))⁻¹) :=
        endpointCapacityGerm_eq_baseCapacityGerm _ _ _
  have hscaledNorm
      (z : K) (hz : R ≤ dist (p N) (z : ℂ)) :
      ‖(p 0 - p N) * (p N - (z : ℂ))⁻¹‖ ≤ ρ := by
    let D : ℝ := dist (p N) (z : ℂ)
    have hD : 0 < D :=
      hRpos.trans_le hz
    have hscale :
        4 * r * ρ⁻¹ ≤ D :=
      (le_max_right _ _).trans hz
    have hfour :
        4 * r ≤ D * ρ := by
      have := (div_le_iff₀ hρ).mp
        (show 4 * r / ρ ≤ D by
          simpa only [div_eq_mul_inv] using hscale)
      nlinarith
    rw [norm_mul, norm_inv]
    rw [show ‖p N - (z : ℂ)‖ = D by
      dsimp only [D]
      rw [dist_eq_norm]]
    rw [← div_eq_mul_inv]
    exact
      (div_le_iff₀ hD).2
        (hdeltaUpper.le.trans
          (by simpa only [mul_comm] using hfour))
  let d : BoundedLaurentCapacity K (p N) R := {
    u := u
    c₁ := (p 0 - p N) * (1 / 100)
    c₂ := (p 0 - p N) ^ 2 * c₂
    c₁_ne_zero := by
      exact mul_ne_zero (sub_ne_zero.mpr hend)
        (by norm_num)
    L := L
    B := B₃
    L_nonneg := hL
    B_nonneg := hB₃
    norm_le_one := by
      intro z
      rw [hu z]
      exact
        norm_polygonalCapacityFunction_le_one
          hN hr htraceBall hq ha
            (hKtrace z.property)
    norm_le_inv := by
      intro z hz
      let D : ℝ := dist (p N) (z : ℂ)
      let s : ℂ := (p N - (z : ℂ))⁻¹
      let t : ℂ := (p 0 - p N) * s
      have hD : 0 < D :=
        hRpos.trans_le hz
      have hsNorm : ‖s‖ = D⁻¹ := by
        dsimp only [s, D]
        rw [norm_inv, ← dist_eq_norm]
      have htNorm :
          ‖t‖ = ‖p 0 - p N‖ * D⁻¹ := by
        dsimp only [t]
        rw [norm_mul, hsNorm]
      have htρ : ‖t‖ ≤ ρ := by
        exact hscaledNorm z hz
      rw [hu z, hfarBase z hz]
      change ‖baseCapacityGerm t‖ ≤ L * D⁻¹
      calc
        ‖baseCapacityGerm t‖ ≤ L₀ * ‖t‖ :=
          norm_le_linear_of_cubic_taylor_bound
            baseCapacityGerm (1 / 100) c₂ B ρ
              hB hρ.le hTaylor t htρ
        _ = L₀ * (‖p 0 - p N‖ * D⁻¹) := by
          rw [htNorm]
        _ ≤ L₀ * (4 * r * D⁻¹) := by
          exact
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hdeltaUpper.le
                (by positivity)) hL₀
        _ = L * D⁻¹ := by
          dsimp only [L]
          ring
    norm_sub_laurent_le := by
      intro z hz
      let D : ℝ := dist (p N) (z : ℂ)
      let s : ℂ := (p N - (z : ℂ))⁻¹
      let t : ℂ := (p 0 - p N) * s
      have hD : 0 < D :=
        hRpos.trans_le hz
      have hsNorm : ‖s‖ = D⁻¹ := by
        dsimp only [s, D]
        rw [norm_inv, ← dist_eq_norm]
      have htNorm :
          ‖t‖ = ‖p 0 - p N‖ * D⁻¹ := by
        dsimp only [t]
        rw [norm_mul, hsNorm]
      have htρ : ‖t‖ ≤ ρ := by
        exact hscaledNorm z hz
      rw [hu z, hfarBase z hz]
      change
        ‖baseCapacityGerm t -
            (s * ((p 0 - p N) * (1 / 100)) +
              s ^ 2 * ((p 0 - p N) ^ 2 * c₂))‖ ≤
          B₃ * D⁻¹ ^ 3
      calc
        ‖baseCapacityGerm t -
            (s * ((p 0 - p N) * (1 / 100)) +
              s ^ 2 * ((p 0 - p N) ^ 2 * c₂))‖ =
            ‖baseCapacityGerm t -
              (t * (1 / 100) + t ^ 2 * c₂)‖ := by
          congr 2
          dsimp only [t]
          ring
        _ ≤ B * ‖t‖ ^ 3 :=
          hTaylor t htρ
        _ =
            B * ‖p 0 - p N‖ ^ 3 * D⁻¹ ^ 3 := by
          rw [htNorm]
          ring
        _ ≤
            (64 * B * r ^ 3) * D⁻¹ ^ 3 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hpow :
              ‖p 0 - p N‖ ^ 3 ≤ (4 * r) ^ 3 :=
            pow_le_pow_left₀ (norm_nonneg _)
              hdeltaUpper.le 3
          calc
            B * ‖p 0 - p N‖ ^ 3
                ≤ B * (4 * r) ^ 3 :=
              mul_le_mul_of_nonneg_left hpow hB
            _ = 64 * B * r ^ 3 := by ring
        _ = B₃ * D⁻¹ ^ 3 := by
          rfl
  }
  refine ⟨p 0, p N, R, d, hq, ha,
    hdeltaLower, hdeltaUpper, rfl, rfl, rfl, ?_, rfl⟩
  rfl

end Submission.Helpers
