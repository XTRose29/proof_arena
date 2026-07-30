import Submission.SubadditiveErgodic
import Submission.PartitionSupport

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology

noncomputable def supportedLogNormFderiv
    (T : EucPlane → EucPlane) (K : Set EucPlane) (n : ℕ) (x : EucPlane) : ℝ :=
  K.indicator (fun y => Real.log ‖fderiv ℝ (T^[n]) y‖) x

lemma measurable_supportedLogNormFderiv
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    {K : Set EucPlane} (hK_measurable : MeasurableSet K) (n : ℕ) :
    Measurable (supportedLogNormFderiv T K n) := by
  exact (((contDiff_iterate T hT_smooth n).continuous_fderiv
    (by norm_num)).measurable.norm.log).indicator hK_measurable

lemma fderiv_iterate_add_eq
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    (m n : ℕ) (x : EucPlane) :
    fderiv ℝ (T^[m + n]) x =
      fderiv ℝ (T^[m]) (T^[n] x) ∘L fderiv ℝ (T^[n]) x := by
  rw [Function.iterate_add, fderiv_comp]
  · exact (hT_smooth.differentiable (by norm_num)).iterate m |>.differentiableAt
  · exact (hT_smooth.differentiable (by norm_num)).iterate n |>.differentiableAt

lemma log_norm_fderiv_iterate_add_le
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (m n : ℕ) (x : EucPlane) :
    Real.log ‖fderiv ℝ (T^[m + n]) x‖ ≤
      Real.log ‖fderiv ℝ (T^[m]) (T^[n] x)‖ +
        Real.log ‖fderiv ℝ (T^[n]) x‖ := by
  have hmpos := norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right m (T^[n] x)
  have hnpos := norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right n x
  have hmnpos := norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right (m + n) x
  have hnorm : ‖fderiv ℝ (T^[m + n]) x‖ ≤
      ‖fderiv ℝ (T^[m]) (T^[n] x)‖ * ‖fderiv ℝ (T^[n]) x‖ := by
    rw [fderiv_iterate_add_eq T hT_smooth]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hlog := Real.log_le_log hmnpos hnorm
  rw [Real.log_mul hmpos.ne' hnpos.ne'] at hlog
  exact hlog

lemma isSubadditiveCocycle_supportedLogNormFderiv
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K) :
    IsSubadditiveCocycle T (supportedLogNormFderiv T K) := by
  intro m n x
  classical
  by_cases hx : x ∈ K
  · have hxn : T^[n] x ∈ K := by
      rw [← image_iterate_eq_of_image_eq T hK_inv n]
      exact ⟨x, hx, rfl⟩
    simp only [supportedLogNormFderiv, Set.indicator_of_mem hx,
      Set.indicator_of_mem hxn]
    exact log_norm_fderiv_iterate_add_le T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right m n x
  · have hxn : T^[n] x ∉ K := by
      intro h
      apply hx
      have hxpre : x ∈ T^[n] ⁻¹' K := h
      rw [preimage_iterate_eq_of_image_eq T hT_left.injective hK_inv n] at hxpre
      exact hxpre
    simp [supportedLogNormFderiv, hx, hxn]

lemma supportedLogNormFderiv_zero
    (T : EucPlane → EucPlane) (K : Set EucPlane) (x : EucPlane) :
    supportedLogNormFderiv T K 0 x = 0 := by
  classical
  by_cases hx : x ∈ K <;> simp [supportedLogNormFderiv, hx, fderiv_id]

lemma abs_supportedLogNormFderiv_le
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {C D B : ℝ} (hC_one : 1 ≤ C) (hD_one : 1 ≤ D)
    (hC : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ C)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    (hCB : Real.log C ≤ B) (hDB : Real.log D ≤ B)
    (n : ℕ) (x : EucPlane) :
    |supportedLogNormFderiv T K n x| ≤ B * n := by
  classical
  by_cases hx : x ∈ K
  · rw [supportedLogNormFderiv, Set.indicator_of_mem hx, abs_le]
    cases n with
    | zero => simp [fderiv_id]
    | succ n =>
        have hn : (0 : ℝ) < n + 1 := by positivity
        have hu := log_norm_fderiv_iterate_div_le T hT_smooth hK_inv
          hC_one hC (n + 1) hx
        have hl := neg_log_le_log_norm_fderiv_iterate_div T T_inv
          hT_smooth hT_inv_smooth hT_left hT_right hK_inv
          hD_one hD (n + 1) hx
        norm_num [Nat.cast_add, Nat.cast_one] at hu hl
        constructor
        · have hbudget := mul_le_mul_of_nonneg_right hDB hn.le
          have hl' := (le_div_iff₀ hn).mp hl
          have hl'' : -Real.log D * ((n : ℝ) + 1) ≤
              Real.log ‖fderiv ℝ (T^[n + 1]) x‖ := by
            simpa [Function.iterate_succ, Nat.cast_add, Nat.cast_one] using hl'
          have hbudget' : Real.log D * ((n : ℝ) + 1) ≤
              B * ((n : ℝ) + 1) := by simpa using hbudget
          norm_num [Nat.cast_add, Nat.cast_one]
          nlinarith
        · have hbudget := mul_le_mul_of_nonneg_right hCB hn.le
          have hu' := (div_le_iff₀ hn).mp hu
          have hu'' : Real.log ‖fderiv ℝ (T^[n + 1]) x‖ ≤
              Real.log C * ((n : ℝ) + 1) := by
            simpa [Function.iterate_succ, Nat.cast_add, Nat.cast_one] using hu'
          have hbudget' : Real.log C * ((n : ℝ) + 1) ≤
              B * ((n : ℝ) + 1) := by simpa using hbudget
          norm_num [Nat.cast_add, Nat.cast_one]
          nlinarith
  · simp [supportedLogNormFderiv, hx, mul_nonneg (le_trans (Real.log_nonneg hC_one) hCB)
      (Nat.cast_nonneg n)]

lemma supportedLogNormFderiv_pad_le
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {D B : ℝ} (hD_one : 1 ≤ D)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    (hDB : Real.log D ≤ B) :
    ∀ n s x, supportedLogNormFderiv T K n x ≤
      supportedLogNormFderiv T K (n + s) x + B * s := by
  intro n s x
  classical
  by_cases hx : x ∈ K
  · simp only [supportedLogNormFderiv, Set.indicator_of_mem hx]
    have hxns : T^[n] x ∈ K := by
      rw [← image_iterate_eq_of_image_eq T hK_inv n]
      exact ⟨x, hx, rfl⟩
    have hinvBound := norm_fderiv_iterate_inverse_le_pow T T_inv hT_smooth
      hT_inv_smooth hT_left hT_right hK_inv hD_one hD s hxns
    have hnpos := norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
    have hnspos := norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right (n + s) x
    have hinvpos : 0 < ‖(fderiv ℝ (T^[s]) (T^[n] x)).inverse‖ := by
      rw [fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right]
      exact norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
        hT_right hT_left s (T^[s] (T^[n] x))
    have hfactor : fderiv ℝ (T^[n]) x =
        (fderiv ℝ (T^[s]) (T^[n] x)).inverse ∘L
          fderiv ℝ (T^[n + s]) x := by
      have hadd := fderiv_iterate_add_eq T hT_smooth s n x
      rw [Nat.add_comm s n] at hadd
      rw [hadd]
      rw [← ContinuousLinearMap.comp_assoc]
      rw [fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right]
      simp
    have hnorm : ‖fderiv ℝ (T^[n]) x‖ ≤
        ‖(fderiv ℝ (T^[s]) (T^[n] x)).inverse‖ *
          ‖fderiv ℝ (T^[n + s]) x‖ := by
      rw [hfactor]
      exact ContinuousLinearMap.opNorm_comp_le _ _
    have hlog := Real.log_le_log hnpos hnorm
    rw [Real.log_mul hinvpos.ne' hnspos.ne'] at hlog
    have hlogInv : Real.log ‖(fderiv ℝ (T^[s]) (T^[n] x)).inverse‖ ≤
        (s : ℝ) * Real.log D := by
      have hDpos : 0 < D := zero_lt_one.trans_le hD_one
      have hlog' := Real.log_le_log hinvpos hinvBound
      simpa [Real.log_pow] using hlog'
    have hbudget := mul_le_mul_of_nonneg_left hDB (Nat.cast_nonneg s)
    nlinarith
  · have hxns : x ∉ K := hx
    simp [supportedLogNormFderiv, hx,
      mul_nonneg (le_trans (Real.log_nonneg hD_one) hDB) (Nat.cast_nonneg s)]

lemma abs_supportedLogNormFderiv_map_sub_le
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {C D : ℝ} (hC_one : 1 ≤ C) (hD_one : 1 ≤ D)
    (hC : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ C)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    (n : ℕ) (x : EucPlane) :
    |supportedLogNormFderiv T K n (T x) -
      supportedLogNormFderiv T K n x| ≤ Real.log C + Real.log D := by
  classical
  have hmem : T x ∈ K ↔ x ∈ K := by
    have hpre := congrArg (fun s : Set EucPlane => x ∈ s)
      (preimage_iterate_eq_of_image_eq T hT_left.injective hK_inv 1)
    simpa [Function.iterate_one] using hpre
  by_cases hx : x ∈ K
  · have hTx : T x ∈ K := hmem.mpr hx
    simp only [supportedLogNormFderiv, Set.indicator_of_mem hx,
      Set.indicator_of_mem hTx]
    have hforward := log_norm_fderiv_iterate_succ_le T T_inv hT_smooth
      hT_inv_smooth hT_left hT_right n x
    have hbackward := log_norm_fderiv_iterate_at_image_le T T_inv hT_smooth
      hT_inv_smooth hT_left hT_right n x
    have hTn : T^[n] x ∈ K := by
      rw [← image_iterate_eq_of_image_eq T hK_inv n]
      exact ⟨x, hx, rfl⟩
    have hlogC : Real.log ‖fderiv ℝ T x‖ ≤ Real.log C := by
      have hpos := norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right 1 x
      exact Real.log_le_log (by simpa [Function.iterate_one] using hpos) (hC x hx)
    have hlogD : Real.log ‖(fderiv ℝ T x).inverse‖ ≤ Real.log D := by
      rw [show (fderiv ℝ T x).inverse = fderiv ℝ T_inv (T x) by
        simpa [Function.iterate_one] using
          fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
            hT_left hT_right 1 x]
      have hpos := norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
        hT_right hT_left 1 (T x)
      exact Real.log_le_log (by simpa [Function.iterate_one] using hpos) (hD (T x) hTx)
    have hnextUpper : Real.log ‖fderiv ℝ (T^[n + 1]) x‖ ≤
        Real.log ‖fderiv ℝ (T^[n]) x‖ + Real.log C := by
      have hnext := log_norm_fderiv_iterate_add_le T T_inv hT_smooth
        hT_inv_smooth hT_left hT_right 1 n x
      have hlogCTn : Real.log ‖fderiv ℝ T (T^[n] x)‖ ≤ Real.log C := by
        have hpos := norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right 1 (T^[n] x)
        exact Real.log_le_log (by simpa [Function.iterate_one] using hpos)
          (hC (T^[n] x) hTn)
      calc
        Real.log ‖fderiv ℝ (T^[n + 1]) x‖ ≤
            Real.log ‖fderiv ℝ (T^[1]) (T^[n] x)‖ +
              Real.log ‖fderiv ℝ (T^[n]) x‖ := by
          simpa [Nat.add_comm] using hnext
        _ ≤ Real.log C + Real.log ‖fderiv ℝ (T^[n]) x‖ :=
          add_le_add hlogCTn (le_refl _)
        _ = Real.log ‖fderiv ℝ (T^[n]) x‖ + Real.log C := add_comm _ _
    have hnextLower : Real.log ‖fderiv ℝ (T^[n]) x‖ ≤
        Real.log ‖fderiv ℝ (T^[n + 1]) x‖ + Real.log D := by
      have hpad := supportedLogNormFderiv_pad_le T T_inv hT_smooth
        hT_inv_smooth hT_left hT_right hK_inv hD_one hD le_rfl n 1 x
      simpa [supportedLogNormFderiv, hx] using hpad
    rw [abs_le]
    constructor <;> linarith
  · have hTx : T x ∉ K := fun h => hx (hmem.mp h)
    simp [supportedLogNormFderiv, hx, hTx,
      add_nonneg (Real.log_nonneg hC_one) (Real.log_nonneg hD_one)]

theorem ae_tendsto_log_norm_fderiv_iterate_div_lyapunovUpperAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu) :
    ∀ᵐ x ∂mu, Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n)
      atTop (nhds (lyapunovUpperAt T x)) := by
  obtain ⟨C, hC_one, hC⟩ := compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨D, hD_one, hD⟩ := compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  let B : ℝ := max (Real.log C) (Real.log D)
  have hB : 0 ≤ B := (Real.log_nonneg hC_one).trans (le_max_left _ _)
  have hCB : Real.log C ≤ B := le_max_left _ _
  have hDB : Real.log D ≤ B := le_max_right _ _
  have hconv := ae_tendsto_subadditiveCocycle_div_limsup
    mu T hT hErg (supportedLogNormFderiv T K)
    (measurable_supportedLogNormFderiv T hT_smooth hK_compact.isClosed.measurableSet)
    (supportedLogNormFderiv_zero T K)
    (isSubadditiveCocycle_supportedLogNormFderiv T T_inv hT_smooth
      hT_inv_smooth hT_left hT_right hK_inv)
    hB (add_nonneg (Real.log_nonneg hC_one) (Real.log_nonneg hD_one))
    (abs_supportedLogNormFderiv_le T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hK_inv hC_one hD_one hC hD hCB hDB)
    (abs_supportedLogNormFderiv_map_sub_le T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hK_inv hC_one hD_one hC hD)
    (supportedLogNormFderiv_pad_le T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hK_inv hD_one hD hDB)
  filter_upwards [hconv, mem_ae_iff.mpr hmu_supp] with x hxconv hxK
  simpa [supportedLogNormFderiv, Set.indicator_of_mem hxK,
    lyapunovUpperAt] using hxconv

theorem ae_tendsto_log_norm_fderiv_iterate_inverse_div_neg_lyapunovLowerAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu) :
    ∀ᵐ x ∂mu, Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n)
      atTop (nhds (-lyapunovLowerAt T x)) := by
  have hnorm := ae_tendsto_log_norm_fderiv_iterate_div_lyapunovUpperAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K hK_compact hK_inv
      mu hmu_supp hT hErg
  have hjac := ae_tendsto_logJacobianIterate_div_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right hK_compact
      mu hmu_supp hT hErg
  have hsum := ae_lyapunovUpperAt_add_lyapunovLowerAt_eq_integral_logJacobian
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right hK_compact
      hK_inv mu hmu_supp hT hErg
  filter_upwards [hnorm, hjac, hsum] with x hxnorm hxjac hxsum
  have hdiff := hxnorm.sub hxjac
  convert hdiff using 1
  · funext n
    rw [logJacobianIterate_eq_log_norm_sub_log_norm_inverse
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right]
    ring
  · rw [← hxsum]
    ring_nf

end Submission.Helpers
