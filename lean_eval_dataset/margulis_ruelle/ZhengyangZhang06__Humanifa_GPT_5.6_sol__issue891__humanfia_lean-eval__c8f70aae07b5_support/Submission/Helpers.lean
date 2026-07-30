import Submission.Definitions

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

def measurableEquivOfContDiffInverse
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) :
    EucPlane ≃ᵐ EucPlane :=
  MeasurableEquiv.mk (Equiv.mk T T_inv hT_left hT_right)
    hT_smooth.continuous.measurable hT_inv_smooth.continuous.measurable

lemma measure_eq_one_of_compl_eq_zero
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    {K : Set EucPlane} (hμ_supp : μ Kᶜ = 0) :
    μ K = 1 := by
  rw [measure_of_measure_compl_eq_zero hμ_supp, measure_univ]

lemma nonempty_of_isProbabilityMeasure_compl_eq_zero
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    {K : Set EucPlane} (hμ_supp : μ Kᶜ = 0) :
    K.Nonempty := by
  by_contra hK
  have hμK := measure_eq_one_of_compl_eq_zero μ hμ_supp
  rw [Set.not_nonempty_iff_eq_empty.mp hK] at hμK
  simp at hμK

lemma inverse_image_eq_of_image_eq
    {T T_inv : EucPlane → EucPlane}
    (hT_left : Function.LeftInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K) :
    T_inv '' K = K := by
  calc
    T_inv '' K = T_inv '' (T '' K) := congrArg (fun s => T_inv '' s) hK_inv.symm
    _ = K := hT_left.image_image K

lemma image_iterate_eq_of_image_eq
    (T : EucPlane → EucPlane) {K : Set EucPlane}
    (hK_inv : T '' K = K) (n : ℕ) :
    T^[n] '' K = K := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ, Set.image_comp, hK_inv, ih]

lemma contDiff_iterate
    (T : EucPlane → EucPlane) {k : WithTop ℕ∞}
    (hT : ContDiff ℝ k T) (n : ℕ) :
    ContDiff ℝ k (T^[n]) := by
  induction n with
  | zero => simpa using (contDiff_id : ContDiff ℝ k (id : EucPlane → EucPlane))
  | succ n ih =>
      rw [Function.iterate_succ]
      exact ih.comp hT

lemma compact_fderiv_bound
    (T : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    {K : Set EucPlane} (hK_compact : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ C := by
  have hcont : Continuous fun x => ‖fderiv ℝ T x‖ :=
    (hT_smooth.continuous_fderiv (by norm_num)).norm
  obtain ⟨C, hC⟩ := hK_compact.bddAbove_image hcont.continuousOn
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro x hx
  exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)

lemma norm_fderiv_iterate_le_pow
    (T : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {C : ℝ} (hC_one : 1 ≤ C)
    (hC : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ C) :
    ∀ n : ℕ, ∀ x ∈ K, ‖fderiv ℝ (T^[n]) x‖ ≤ C ^ n := by
  have hT_diff : Differentiable ℝ T := hT_smooth.differentiable (by norm_num)
  intro n
  induction n with
  | zero =>
      intro x hx
      simp [fderiv_id]
  | succ n ih =>
      intro x hx
      have hTx : T x ∈ K := by
        rw [← hK_inv]
        exact ⟨x, hx, rfl⟩
      rw [Function.iterate_succ, fderiv_comp x
        (hT_diff.iterate n).differentiableAt hT_diff.differentiableAt]
      calc
        ‖fderiv ℝ (T^[n]) (T x) ∘L fderiv ℝ T x‖ ≤
            ‖fderiv ℝ (T^[n]) (T x)‖ * ‖fderiv ℝ T x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ C ^ n * C := mul_le_mul (ih (T x) hTx) (hC x hx)
          (norm_nonneg _) (pow_nonneg (zero_le_one.trans hC_one) n)
        _ = C ^ (n + 1) := (pow_succ C n).symm

lemma measurePreserving_inverse
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (μ : Measure EucPlane)
    (hμ_pres : MeasurePreserving T μ μ) :
    MeasurePreserving T_inv μ μ := by
  let e := measurableEquivOfContDiffInverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right
  have he : MeasurePreserving (e : EucPlane → EucPlane) μ μ := by
    simpa [e, measurableEquivOfContDiffInverse] using hμ_pres
  simpa [e, measurableEquivOfContDiffInverse] using MeasurePreserving.symm e he

lemma ergodic_inverse
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (μ : Measure EucPlane)
    (hμ_erg : Ergodic T μ) :
    Ergodic T_inv μ := by
  let e := measurableEquivOfContDiffInverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right
  have he : Ergodic (e : EucPlane → EucPlane) μ := by
    simpa [e, measurableEquivOfContDiffInverse] using hμ_erg
  simpa [e, measurableEquivOfContDiffInverse] using Ergodic.symm he

lemma fderiv_iterate_inverse
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    (fderiv ℝ (T^[n]) x).inverse =
      fderiv ℝ (T_inv^[n]) (T^[n] x) := by
  have hT_diff : Differentiable ℝ T := hT_smooth.differentiable (by norm_num)
  have hT_inv_diff : Differentiable ℝ T_inv :=
    hT_inv_smooth.differentiable (by norm_num)
  have hleft := hT_left.iterate n
  have hright := hT_right.iterate n
  apply ContinuousLinearMap.inverse_eq
  · calc
      fderiv ℝ (T^[n]) x ∘L fderiv ℝ (T_inv^[n]) (T^[n] x) =
          fderiv ℝ (T^[n]) ((T_inv^[n]) (T^[n] x)) ∘L
            fderiv ℝ (T_inv^[n]) (T^[n] x) := by rw [hleft x]
      _ = fderiv ℝ ((T^[n]) ∘ (T_inv^[n])) (T^[n] x) := by
        rw [fderiv_comp]
        · exact (hT_diff.iterate n).differentiableAt
        · exact (hT_inv_diff.iterate n).differentiableAt
      _ = ContinuousLinearMap.id ℝ EucPlane := by
        rw [hright.comp_eq_id, fderiv_id]
  · calc
      fderiv ℝ (T_inv^[n]) (T^[n] x) ∘L fderiv ℝ (T^[n]) x =
          fderiv ℝ ((T_inv^[n]) ∘ (T^[n])) x := by
        rw [fderiv_comp]
        · exact (hT_inv_diff.iterate n).differentiableAt
        · exact (hT_diff.iterate n).differentiableAt
      _ = ContinuousLinearMap.id ℝ EucPlane := by
        rw [hleft.comp_eq_id, fderiv_id]

lemma fderiv_iterate_comp_inverse
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    fderiv ℝ (T^[n]) x ∘L (fderiv ℝ (T^[n]) x).inverse =
      ContinuousLinearMap.id ℝ EucPlane := by
  rw [fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth hT_left hT_right]
  have hT_diff : Differentiable ℝ T := hT_smooth.differentiable (by norm_num)
  have hT_inv_diff : Differentiable ℝ T_inv :=
    hT_inv_smooth.differentiable (by norm_num)
  have hleft := hT_left.iterate n
  have hright := hT_right.iterate n
  calc
    fderiv ℝ (T^[n]) x ∘L fderiv ℝ (T_inv^[n]) (T^[n] x) =
        fderiv ℝ (T^[n]) ((T_inv^[n]) (T^[n] x)) ∘L
          fderiv ℝ (T_inv^[n]) (T^[n] x) := by rw [hleft x]
    _ = fderiv ℝ ((T^[n]) ∘ (T_inv^[n])) (T^[n] x) := by
      rw [fderiv_comp]
      · exact (hT_diff.iterate n).differentiableAt
      · exact (hT_inv_diff.iterate n).differentiableAt
    _ = ContinuousLinearMap.id ℝ EucPlane := by
      rw [hright.comp_eq_id, fderiv_id]

lemma norm_fderiv_iterate_pos
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    0 < ‖fderiv ℝ (T^[n]) x‖ := by
  have hcomp := fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right n x
  have hprod : 1 ≤ ‖fderiv ℝ (T^[n]) x‖ * ‖(fderiv ℝ (T^[n]) x).inverse‖ := by
    calc
      1 = ‖ContinuousLinearMap.id ℝ EucPlane‖ :=
        (ContinuousLinearMap.norm_id (𝕜 := ℝ) (E := EucPlane)).symm
      _ = ‖fderiv ℝ (T^[n]) x ∘L (fderiv ℝ (T^[n]) x).inverse‖ :=
        congrArg norm hcomp.symm
      _ ≤ ‖fderiv ℝ (T^[n]) x‖ * ‖(fderiv ℝ (T^[n]) x).inverse‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
  have hne : ‖fderiv ℝ (T^[n]) x‖ ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hprod
    norm_num at hprod
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)

lemma norm_fderiv_iterate_inverse_le_pow
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {D : ℝ} (hD_one : 1 ≤ D)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    (n : ℕ) {x : EucPlane} (hx : x ∈ K) :
    ‖(fderiv ℝ (T^[n]) x).inverse‖ ≤ D ^ n := by
  rw [fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth hT_left hT_right]
  apply norm_fderiv_iterate_le_pow T_inv hT_inv_smooth
    (inverse_image_eq_of_image_eq hT_left hK_inv) hD_one hD n
  rw [← image_iterate_eq_of_image_eq T hK_inv n]
  exact ⟨x, hx, rfl⟩

lemma log_norm_fderiv_iterate_div_le
    (T : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {C : ℝ} (hC_one : 1 ≤ C)
    (hC : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ C)
    (n : ℕ) {x : EucPlane} (hx : x ∈ K) :
    Real.log ‖fderiv ℝ (T^[n]) x‖ / n ≤ Real.log C := by
  cases n with
  | zero => simp [fderiv_id, Real.log_nonneg hC_one]
  | succ n =>
      have hnorm := norm_fderiv_iterate_le_pow T hT_smooth hK_inv hC_one hC n.succ x hx
      have hlog : Real.log ‖fderiv ℝ (T^[n.succ]) x‖ ≤ Real.log (C ^ n.succ) := by
        by_cases hz : ‖fderiv ℝ (T^[n.succ]) x‖ = 0
        · rw [hz, Real.log_zero, Real.log_pow]
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hC_one)
        · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)) hnorm
      rw [div_le_iff₀ (Nat.cast_pos.mpr n.succ_pos)]
      calc
        Real.log ‖fderiv ℝ (T^[n.succ]) x‖ ≤ Real.log (C ^ n.succ) := hlog
        _ = (n.succ : ℝ) * Real.log C := Real.log_pow C n.succ
        _ = Real.log C * (n.succ : ℝ) := mul_comm _ _

lemma neg_log_le_log_norm_fderiv_iterate_div
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {D : ℝ} (hD_one : 1 ≤ D)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    (n : ℕ) {x : EucPlane} (hx : x ∈ K) :
    -Real.log D ≤ Real.log ‖fderiv ℝ (T^[n]) x‖ / n := by
  cases n with
  | zero => simp [fderiv_id, Real.log_nonneg hD_one]
  | succ n =>
      have hcomp := fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n.succ x
      have hprod : 1 ≤ ‖fderiv ℝ (T^[n.succ]) x‖ *
          ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ := by
        calc
          1 = ‖ContinuousLinearMap.id ℝ EucPlane‖ :=
            (ContinuousLinearMap.norm_id (𝕜 := ℝ) (E := EucPlane)).symm
          _ = ‖fderiv ℝ (T^[n.succ]) x ∘L
              (fderiv ℝ (T^[n.succ]) x).inverse‖ := congrArg norm hcomp.symm
          _ ≤ ‖fderiv ℝ (T^[n.succ]) x‖ *
              ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
      have hinv := norm_fderiv_iterate_inverse_le_pow T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right hK_inv hD_one hD n.succ hx
      have hprodD : 1 ≤ ‖fderiv ℝ (T^[n.succ]) x‖ * D ^ n.succ :=
        hprod.trans (mul_le_mul_of_nonneg_left hinv (norm_nonneg _))
      have hDpos : 0 < D := zero_lt_one.trans_le hD_one
      have hDpowpos : 0 < D ^ n.succ := pow_pos hDpos _
      have hnormLow : 1 / D ^ n.succ ≤ ‖fderiv ℝ (T^[n.succ]) x‖ :=
        (div_le_iff₀ hDpowpos).2 hprodD
      have hlog := Real.log_le_log (one_div_pos.mpr hDpowpos) hnormLow
      rw [Real.log_div one_ne_zero hDpowpos.ne', Real.log_one, Real.log_pow] at hlog
      rw [le_div_iff₀ (Nat.cast_pos.mpr n.succ_pos)]
      calc
        -Real.log D * (n.succ : ℝ) = 0 - (n.succ : ℝ) * Real.log D := by ring
        _ ≤ Real.log ‖fderiv ℝ (T^[n.succ]) x‖ := hlog

lemma lyapunovUpperAt_le_log_bound
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {C D : ℝ} (hC_one : 1 ≤ C) (hD_one : 1 ≤ D)
    (hC : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ C)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    {x : EucPlane} (hx : x ∈ K) :
    lyapunovUpperAt T x ≤ Real.log C := by
  rw [lyapunovUpperAt]
  refine limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (x := -Real.log D) fun n => ?_) ?_
  · exact neg_log_le_log_norm_fderiv_iterate_div T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hK_inv hD_one hD n hx
  · exact Eventually.of_forall fun n =>
      log_norm_fderiv_iterate_div_le T hT_smooth hK_inv hC_one hC n hx

lemma neg_log_bound_le_lyapunovUpperAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {C D : ℝ} (hC_one : 1 ≤ C) (hD_one : 1 ≤ D)
    (hC : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ C)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    {x : EucPlane} (hx : x ∈ K) :
    -Real.log D ≤ lyapunovUpperAt T x := by
  rw [lyapunovUpperAt]
  refine le_limsup_of_frequently_le (Frequently.of_forall fun n => ?_)
    (isBoundedUnder_of_eventually_le (a := Real.log C)
      (Eventually.of_forall fun n => ?_))
  · exact neg_log_le_log_norm_fderiv_iterate_div T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hK_inv hD_one hD n hx
  · exact log_norm_fderiv_iterate_div_le T hT_smooth hK_inv hC_one hC n hx

lemma log_norm_fderiv_iterate_inverse_div_le
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {D : ℝ} (hD_one : 1 ≤ D)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    (n : ℕ) {x : EucPlane} (hx : x ∈ K) :
    Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n ≤ Real.log D := by
  cases n with
  | zero => simp [fderiv_id, Real.log_nonneg hD_one]
  | succ n =>
      have hnorm := norm_fderiv_iterate_inverse_le_pow T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right hK_inv hD_one hD n.succ hx
      have hlog : Real.log ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ ≤
          Real.log (D ^ n.succ) := by
        by_cases hz : ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ = 0
        · rw [hz, Real.log_zero, Real.log_pow]
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hD_one)
        · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)) hnorm
      rw [div_le_iff₀ (Nat.cast_pos.mpr n.succ_pos)]
      calc
        Real.log ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ ≤ Real.log (D ^ n.succ) := hlog
        _ = (n.succ : ℝ) * Real.log D := Real.log_pow D n.succ
        _ = Real.log D * (n.succ : ℝ) := mul_comm _ _

lemma neg_log_le_log_norm_fderiv_iterate_inverse_div
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {C : ℝ} (hC_one : 1 ≤ C)
    (hC : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ C)
    (n : ℕ) {x : EucPlane} (hx : x ∈ K) :
    -Real.log C ≤ Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n := by
  cases n with
  | zero => simp [fderiv_id, Real.log_nonneg hC_one]
  | succ n =>
      have hcomp := fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n.succ x
      have hprod : 1 ≤ ‖fderiv ℝ (T^[n.succ]) x‖ *
          ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ := by
        calc
          1 = ‖ContinuousLinearMap.id ℝ EucPlane‖ :=
            (ContinuousLinearMap.norm_id (𝕜 := ℝ) (E := EucPlane)).symm
          _ = ‖fderiv ℝ (T^[n.succ]) x ∘L
              (fderiv ℝ (T^[n.succ]) x).inverse‖ := congrArg norm hcomp.symm
          _ ≤ ‖fderiv ℝ (T^[n.succ]) x‖ *
              ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
      have hfwd := norm_fderiv_iterate_le_pow T hT_smooth hK_inv hC_one hC n.succ x hx
      have hprodC : 1 ≤ C ^ n.succ * ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ :=
        hprod.trans (mul_le_mul_of_nonneg_right hfwd (norm_nonneg _))
      have hCpos : 0 < C := zero_lt_one.trans_le hC_one
      have hCpowpos : 0 < C ^ n.succ := pow_pos hCpos _
      have hnormLow : 1 / C ^ n.succ ≤ ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ :=
        (div_le_iff₀ hCpowpos).2 (by simpa [mul_comm] using hprodC)
      have hlog := Real.log_le_log (one_div_pos.mpr hCpowpos) hnormLow
      rw [Real.log_div one_ne_zero hCpowpos.ne', Real.log_one, Real.log_pow] at hlog
      rw [le_div_iff₀ (Nat.cast_pos.mpr n.succ_pos)]
      calc
        -Real.log C * (n.succ : ℝ) = 0 - (n.succ : ℝ) * Real.log C := by ring
        _ ≤ Real.log ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ := hlog

lemma neg_log_bound_le_lyapunovLowerAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {C D : ℝ} (hC_one : 1 ≤ C) (hD_one : 1 ≤ D)
    (hC : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ C)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    {x : EucPlane} (hx : x ∈ K) :
    -Real.log D ≤ lyapunovLowerAt T x := by
  rw [lyapunovLowerAt]
  apply neg_le_neg
  refine limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (x := -Real.log C) fun n => ?_) ?_
  · exact neg_log_le_log_norm_fderiv_iterate_inverse_div T T_inv hT_smooth
      hT_inv_smooth hT_left hT_right hK_inv hC_one hC n hx
  · exact Eventually.of_forall fun n =>
      log_norm_fderiv_iterate_inverse_div_le T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right hK_inv hD_one hD n hx

lemma lyapunovLowerAt_le_log_bound
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {C D : ℝ} (hC_one : 1 ≤ C) (hD_one : 1 ≤ D)
    (hC : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ C)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    {x : EucPlane} (hx : x ∈ K) :
    lyapunovLowerAt T x ≤ Real.log C := by
  rw [lyapunovLowerAt]
  have hlim : -Real.log C ≤ limsup
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n) atTop := by
    refine le_limsup_of_frequently_le (Frequently.of_forall fun n => ?_)
      (isBoundedUnder_of_eventually_le (a := Real.log D)
        (Eventually.of_forall fun n => ?_))
    · exact neg_log_le_log_norm_fderiv_iterate_inverse_div T T_inv hT_smooth
        hT_inv_smooth hT_left hT_right hK_inv hC_one hC n hx
    · exact log_norm_fderiv_iterate_inverse_div_le T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right hK_inv hD_one hD n hx
  simpa using neg_le_neg hlim

lemma measurable_log_norm_fderiv_iterate_div
    (T : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (n : ℕ) :
    Measurable fun x => Real.log ‖fderiv ℝ (T^[n]) x‖ / n := by
  exact (((contDiff_iterate T hT_smooth n).continuous_fderiv
    (by norm_num)).measurable.norm.log).div_const n

lemma measurable_lyapunovUpperAt
    (T : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) :
    Measurable (lyapunovUpperAt T) := by
  change Measurable fun x => lyapunovUpperAt T x
  simpa [lyapunovUpperAt] using
    (Measurable.limsup fun n => measurable_log_norm_fderiv_iterate_div T hT_smooth n)

lemma measurable_log_norm_fderiv_iterate_inverse_div
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) :
    Measurable fun x => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n := by
  have hcont : Continuous fun x => fderiv ℝ (T_inv^[n]) (T^[n] x) :=
    ((contDiff_iterate T_inv hT_inv_smooth n).continuous_fderiv (by norm_num)).comp
      (contDiff_iterate T hT_smooth n).continuous
  convert (hcont.measurable.norm.log.div_const n) using 1
  funext x
  rw [fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth hT_left hT_right]

lemma measurable_lyapunovLowerAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) :
    Measurable (lyapunovLowerAt T) := by
  change Measurable fun x => lyapunovLowerAt T x
  simpa [lyapunovLowerAt] using
    (Measurable.limsup fun n =>
      measurable_log_norm_fderiv_iterate_inverse_div T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n).neg

lemma integrable_of_full_measure_bounds
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    {K : Set EucPlane} (hμ_supp : μ Kᶜ = 0)
    {f : EucPlane → ℝ} (hf : Measurable f)
    {a b : ℝ}
    (hlower : ∀ x ∈ K, -a ≤ f x)
    (hupper : ∀ x ∈ K, f x ≤ b) :
    Integrable f μ := by
  refine (integrable_const (μ := μ) (max a b)).mono' hf.aestronglyMeasurable ?_
  filter_upwards [mem_ae_iff.mpr hμ_supp] with x hx
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨(neg_le_neg (le_max_left a b)).trans (hlower x hx),
    (hupper x hx).trans (le_max_right a b)⟩

lemma integrable_lyapunovUpperAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_supp : μ Kᶜ = 0) :
    Integrable (lyapunovUpperAt T) μ := by
  obtain ⟨C, hC_one, hC⟩ := compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨D, hD_one, hD⟩ := compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  apply integrable_of_full_measure_bounds μ hμ_supp (measurable_lyapunovUpperAt T hT_smooth)
  · exact fun x hx => neg_log_bound_le_lyapunovUpperAt T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hK_inv hC_one hD_one hC hD hx
  · exact fun x hx => lyapunovUpperAt_le_log_bound T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hK_inv hC_one hD_one hC hD hx

lemma integrable_lyapunovLowerAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_supp : μ Kᶜ = 0) :
    Integrable (lyapunovLowerAt T) μ := by
  obtain ⟨C, hC_one, hC⟩ := compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨D, hD_one, hD⟩ := compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  apply integrable_of_full_measure_bounds μ hμ_supp
    (measurable_lyapunovLowerAt T T_inv hT_smooth hT_inv_smooth hT_left hT_right)
  · exact fun x hx => neg_log_bound_le_lyapunovLowerAt T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hK_inv hC_one hD_one hC hD hx
  · exact fun x hx => lyapunovLowerAt_le_log_bound T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hK_inv hC_one hD_one hC hD hx

lemma liminf_neg_real {α : Type*} (u : α → ℝ) (f : Filter α) :
    liminf (fun x => -u x) f = -limsup u f := by
  rw [liminf_eq, limsup_eq, ← Real.sSup_neg]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_neg]
  constructor
  · intro h
    filter_upwards [h] with x hx
    linarith
  · intro h
    filter_upwards [h] with x hx
    linarith

lemma neg_log_norm_inverse_div_le_log_norm
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    -(Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n) ≤
      Real.log ‖fderiv ℝ (T^[n]) x‖ / n := by
  cases n with
  | zero => simp [fderiv_id]
  | succ n =>
      have hcomp := fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n.succ x
      have hprod : 1 ≤ ‖fderiv ℝ (T^[n.succ]) x‖ *
          ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ := by
        calc
          1 = ‖ContinuousLinearMap.id ℝ EucPlane‖ :=
            (ContinuousLinearMap.norm_id (𝕜 := ℝ) (E := EucPlane)).symm
          _ = ‖fderiv ℝ (T^[n.succ]) x ∘L
              (fderiv ℝ (T^[n.succ]) x).inverse‖ := congrArg norm hcomp.symm
          _ ≤ ‖fderiv ℝ (T^[n.succ]) x‖ *
              ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
      have hforward : 0 < ‖fderiv ℝ (T^[n.succ]) x‖ :=
        norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right n.succ x
      have hinverse : 0 < ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ := by
        apply lt_of_le_of_ne (norm_nonneg _)
        intro hzero
        rw [← hzero, mul_zero] at hprod
        norm_num at hprod
      have hlog : 0 ≤ Real.log ‖fderiv ℝ (T^[n.succ]) x‖ +
          Real.log ‖(fderiv ℝ (T^[n.succ]) x).inverse‖ := by
        rw [← Real.log_mul hforward.ne' hinverse.ne']
        exact Real.log_nonneg hprod
      rw [← neg_div]
      exact (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr n.succ_pos)).2 (by linarith)

lemma lyapunovLowerAt_le_lyapunovUpperAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hx : x ∈ K) :
    lyapunovLowerAt T x ≤ lyapunovUpperAt T x := by
  obtain ⟨C, hC_one, hC⟩ := compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨D, hD_one, hD⟩ := compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  rw [lyapunovLowerAt, lyapunovUpperAt, ← liminf_neg_real]
  apply liminf_le_limsup_of_frequently_le
  · exact Frequently.of_forall fun n =>
      neg_log_norm_inverse_div_le_log_norm T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x
  · apply isBoundedUnder_of_eventually_ge (a := -Real.log D)
    exact Eventually.of_forall fun n => by
      have h := log_norm_fderiv_iterate_inverse_div_le T T_inv hT_smooth
        hT_inv_smooth hT_left hT_right hK_inv hD_one hD n hx
      linarith
  · apply isBoundedUnder_of_eventually_le (a := Real.log C)
    exact Eventually.of_forall fun n =>
      log_norm_fderiv_iterate_div_le T hT_smooth hK_inv hC_one hC n hx

lemma integral_lyapunovLowerAt_le_integral_lyapunovUpperAt
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_supp : μ Kᶜ = 0) :
    (∫ x, lyapunovLowerAt T x ∂μ) ≤ ∫ x, lyapunovUpperAt T x ∂μ := by
  apply integral_mono_ae
    (integrable_lyapunovLowerAt T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv μ hμ_supp)
    (integrable_lyapunovUpperAt T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv μ hμ_supp)
  filter_upwards [mem_ae_iff.mpr hμ_supp] with x hx
  exact lyapunovLowerAt_le_lyapunovUpperAt T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right hK_compact hK_inv hx

lemma isMeasurablePartition_singleton_univ
    {M : Type*} [MeasurableSpace M] (μ : Measure M) :
    IsMeasurablePartition μ {Set.univ} := by
  constructor <;> simp

lemma entropyW_singleton_univ
    {M : Type*} [MeasurableSpace M] (μ : Measure M) (T : M → M) :
    entropyW μ T {Set.univ} = 0 := by
  simpa [entropyW, partitionEntropy, iteratedJoin] using
    (tendsto_const_div_atTop_nhds_zero_nat
      (Real.negMulLog (μ Set.univ).toReal)).limsup_eq

lemma kolmogorovSinaiEntropy_nonneg
    {M : Type*} [MeasurableSpace M] (μ : Measure M) (T : M → M) :
    0 ≤ kolmogorovSinaiEntropy μ T := by
  unfold kolmogorovSinaiEntropy
  let S : Set ℝ := {h | ∃ P : Finset (Set M),
    IsMeasurablePartition μ P ∧ entropyW μ T P = h}
  have hzero : 0 ∈ S := by
    exact ⟨{Set.univ}, isMeasurablePartition_singleton_univ μ,
      entropyW_singleton_univ μ T⟩
  by_cases hS : BddAbove S
  · exact le_csSup hS hzero
  · rw [csSup_of_not_bddAbove hS]
    simp

lemma dimMeasure_le_dimH_of_full_measure
    {M : Type*} [EMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) {s : Set M}
    (hs : MeasurableSet s) (hμs : μ sᶜ = 0) :
    dimMeasure μ ≤ dimH s := by
  unfold dimMeasure
  exact sInf_le ⟨s, hs, hμs, rfl⟩

lemma dimMeasure_ne_top_of_compact_full_measure
    (μ : Measure EucPlane) {K : Set EucPlane}
    (hK_compact : IsCompact K) (hμ_supp : μ Kᶜ = 0) :
    dimMeasure μ ≠ ⊤ := by
  exact ne_top_of_le_ne_top (Real.dimH_ne_top K)
    (dimMeasure_le_dimH_of_full_measure μ hK_compact.isClosed.measurableSet hμ_supp)

lemma dimMeasure_toReal_le_two
    (μ : Measure EucPlane) {K : Set EucPlane}
    (hK_compact : IsCompact K) (hμ_supp : μ Kᶜ = 0) :
    (dimMeasure μ).toReal ≤ 2 := by
  have hdim_le : dimMeasure μ ≤ dimH (Set.univ : Set EucPlane) :=
    (dimMeasure_le_dimH_of_full_measure μ hK_compact.isClosed.measurableSet hμ_supp).trans
      (dimH_mono (Set.subset_univ K))
  have hto : (dimMeasure μ).toReal ≤ (dimH (Set.univ : Set EucPlane)).toReal :=
    (ENNReal.toReal_le_toReal
      (dimMeasure_ne_top_of_compact_full_measure μ hK_compact hμ_supp)
      (Real.dimH_ne_top _)).2 hdim_le
  simpa [Real.dimH_univ_eq_finrank, finrank_euclideanSpace] using hto

lemma dimH_image_eq_of_contDiff_inverse
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (s : Set EucPlane) :
    dimH (T '' s) = dimH s := by
  apply le_antisymm
  · exact (hT_smooth.of_le (by norm_num)).contDiffOn.dimH_image_le
      convex_univ (Set.subset_univ s)
  · calc
      dimH s = dimH (T_inv '' (T '' s)) := congrArg dimH (hT_left.image_image s).symm
      _ ≤ dimH (T '' s) :=
        (hT_inv_smooth.of_le (by norm_num)).contDiffOn.dimH_image_le
          convex_univ (Set.subset_univ (T '' s))

lemma dimH_image_iterate_eq_of_contDiff_inverse
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (n : ℕ) (s : Set EucPlane) :
    dimH (T^[n] '' s) = dimH s := by
  exact dimH_image_eq_of_contDiff_inverse (T^[n]) (T_inv^[n])
    (contDiff_iterate T hT_smooth n) (contDiff_iterate T_inv hT_inv_smooth n)
    (hT_left.iterate n) s

lemma dimMeasure_eq_zero_of_finite_full_measure
    (μ : Measure EucPlane) (s : Finset EucPlane)
    (hμs : μ (s : Set EucPlane)ᶜ = 0) :
    dimMeasure μ = 0 := by
  apply bot_unique
  simpa using dimMeasure_le_dimH_of_full_measure μ s.measurableSet hμs

lemma iteratedJoin_measure_inter_eq_zero
    {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (T : M → M) (P : Finset (Set M))
    (hP : IsMeasurablePartition μ P)
    (hT : MeasurePreserving T μ μ)
    (n : ℕ) {A B : Set M}
    (hA : A ∈ iteratedJoin T P n)
    (hB : B ∈ iteratedJoin T P n)
    (hAB : A ≠ B) :
    μ (A ∩ B) = 0 := by
  rw [iteratedJoin] at hA hB
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hB
  have hfg : f ≠ g := by
    intro h
    subst g
    exact hAB rfl
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hfg
  have hfk : f k ∈ P := (Fintype.mem_piFinset.mp hf) k
  have hgk : g k ∈ P := (Fintype.mem_piFinset.mp hg) k
  apply measure_mono_null (t := T^[(k : ℕ)] ⁻¹' (f k ∩ g k))
  · intro x hx
    exact ⟨Set.mem_iInter.mp hx.1 k, Set.mem_iInter.mp hx.2 k⟩
  · exact (hT.iterate k).preimage_null (hP.disjoint (f k) hfk (g k) hgk hk)

lemma exists_mem_finset_of_measure_ne_zero
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure M) (s : Finset M) (hμs : μ (s : Set M)ᶜ = 0)
    {A : Set M} (hA : μ A ≠ 0) :
    ∃ x ∈ s, x ∈ A ∧ μ {x} ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let q := s.filter fun x => x ∈ A
  have hq : μ (q : Set M) = 0 := by
    rw [← MeasureTheory.sum_measure_singleton]
    exact Finset.sum_eq_zero fun x hx => h x (Finset.mem_filter.mp hx).1
      (Finset.mem_filter.mp hx).2
  have hq_set : (q : Set M) = A ∩ (s : Set M) := by
    ext x
    simp [q, and_comm]
  have hAs : μ (A ∩ (s : Set M)) = μ A := by
    calc
      μ (A ∩ (s : Set M)) = μ (A \ (s : Set M)ᶜ) := by
        congr 1
        ext x
        simp
      _ = μ A := measure_sdiff_null'
        (measure_mono_null Set.inter_subset_right hμs)
  exact hA (hAs ▸ hq_set ▸ hq)

lemma card_filter_measure_ne_zero_iteratedJoin_le
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure M) (T : M → M) (P : Finset (Set M))
    (hP : IsMeasurablePartition μ P)
    (hT : MeasurePreserving T μ μ)
    (s : Finset M) (hμs : μ (s : Set M)ᶜ = 0)
    (n : ℕ) :
    ((iteratedJoin T P n).filter fun A => μ A ≠ 0).card ≤ s.card := by
  classical
  let Q := (iteratedJoin T P n).filter fun A => μ A ≠ 0
  have hpoint : ∀ A : ↥Q, ∃ x ∈ s, x ∈ (A : Set M) ∧ μ {x} ≠ 0 := by
    intro A
    exact exists_mem_finset_of_measure_ne_zero μ s hμs
      (Finset.mem_filter.mp A.property).2
  let pick : ↥Q → ↥s := fun A =>
    ⟨Classical.choose (hpoint A), (Classical.choose_spec (hpoint A)).1⟩
  have hpick_mem (A : ↥Q) : (pick A : M) ∈ (A : Set M) :=
    (Classical.choose_spec (hpoint A)).2.1
  have hpick_measure (A : ↥Q) : μ ({(pick A : M)} : Set M) ≠ 0 :=
    (Classical.choose_spec (hpoint A)).2.2
  change Q.card ≤ s.card
  refine Finset.card_le_card_of_injective (f := pick) ?_
  intro A B hAB
  apply Subtype.ext
  by_contra hne
  have hinter := iteratedJoin_measure_inter_eq_zero μ T P hP hT n
    (Finset.mem_filter.mp A.property).1 (Finset.mem_filter.mp B.property).1 hne
  apply hpick_measure A
  apply measure_mono_null _ hinter
  intro x hx
  have hxpick : x = pick A := Set.mem_singleton_iff.mp hx
  subst x
  exact ⟨hpick_mem A, hAB ▸ hpick_mem B⟩

lemma partitionEntropy_nonneg
    {M : Type*} [MeasurableSpace M]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (P : Finset (Set M)) :
    0 ≤ partitionEntropy μ P := by
  rw [partitionEntropy]
  apply Finset.sum_nonneg
  intro A hA
  apply Real.negMulLog_nonneg measureReal_nonneg
  calc
    μ.real A ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ A)
    _ = 1 := by simp

lemma partitionEntropy_iteratedJoin_le_card_support
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (T : M → M) (P : Finset (Set M))
    (hP : IsMeasurablePartition μ P)
    (hT : MeasurePreserving T μ μ)
    (s : Finset M) (hμs : μ (s : Set M)ᶜ = 0)
    (n : ℕ) :
    partitionEntropy μ (iteratedJoin T P n) ≤ s.card := by
  classical
  let Q := iteratedJoin T P n
  let Qpos := Q.filter fun A => μ A ≠ 0
  have hsum : partitionEntropy μ Q =
      ∑ A ∈ Qpos, Real.negMulLog (μ A).toReal := by
    rw [partitionEntropy]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro A hA
    split_ifs with h
    · rfl
    · rw [not_ne_iff.mp h, ENNReal.toReal_zero, Real.negMulLog_zero]
  rw [hsum]
  calc
    (∑ A ∈ Qpos, Real.negMulLog (μ A).toReal) ≤ ∑ _A ∈ Qpos, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro A hA
      exact (Real.negMulLog_le_one_sub_self measureReal_nonneg).trans
        (sub_le_self 1 measureReal_nonneg)
    _ = Qpos.card := by simp
    _ ≤ s.card := by
      exact_mod_cast card_filter_measure_ne_zero_iteratedJoin_le μ T P hP hT s hμs n

lemma entropyW_eq_zero_of_finite_full_measure
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (T : M → M) (P : Finset (Set M))
    (hP : IsMeasurablePartition μ P)
    (hT : MeasurePreserving T μ μ)
    (s : Finset M) (hμs : μ (s : Set M)ᶜ = 0) :
    entropyW μ T P = 0 := by
  rw [entropyW]
  apply Filter.Tendsto.limsup_eq
  apply squeeze_zero
  · intro n
    exact div_nonneg (partitionEntropy_nonneg μ (iteratedJoin T P n)) (Nat.cast_nonneg n)
  · intro n
    exact div_le_div_of_nonneg_right
      (partitionEntropy_iteratedJoin_le_card_support μ T P hP hT s hμs n)
      (Nat.cast_nonneg n)
  · exact tendsto_const_div_atTop_nhds_zero_nat (s.card : ℝ)

lemma kolmogorovSinaiEntropy_eq_zero_of_finite_full_measure
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (T : M → M) (hT : MeasurePreserving T μ μ)
    (s : Finset M) (hμs : μ (s : Set M)ᶜ = 0) :
    kolmogorovSinaiEntropy μ T = 0 := by
  unfold kolmogorovSinaiEntropy
  have hset : {h : ℝ | ∃ P : Finset (Set M),
      IsMeasurablePartition μ P ∧ entropyW μ T P = h} = {0} := by
    ext h
    constructor
    · rintro ⟨P, hP, rfl⟩
      simp [entropyW_eq_zero_of_finite_full_measure μ T P hP hT s hμs]
    · intro hh
      rw [Set.mem_singleton_iff] at hh
      subst h
      exact ⟨{Set.univ}, isMeasurablePartition_singleton_univ μ,
        entropyW_eq_zero_of_finite_full_measure μ T {Set.univ}
          (isMeasurablePartition_singleton_univ μ) hT s hμs⟩
  rw [hset]
  simp

lemma entropy_dimension_lyapunov_of_finite_full_measure
    (T : EucPlane → EucPlane)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_pres : MeasurePreserving T μ μ)
    (s : Finset EucPlane) (hμs : μ (s : Set EucPlane)ᶜ = 0) :
    kolmogorovSinaiEntropy μ T =
      (dimMeasure μ).toReal *
        harmonicMeanLyapunov
          (∫ x, lyapunovUpperAt T x ∂μ)
          (∫ x, lyapunovLowerAt T x ∂μ) / 2 := by
  rw [kolmogorovSinaiEntropy_eq_zero_of_finite_full_measure μ T hμ_pres s hμs,
    dimMeasure_eq_zero_of_finite_full_measure μ s hμs]
  simp

lemma finite_setOf_measure_singleton_eq
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure M) [IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : p ≠ 0) :
    Set.Finite {x : M | μ {x} = p} := by
  classical
  let S : Set M := {x | μ {x} = p}
  by_contra hS
  have hSinf : S.Infinite := hS
  letI : Infinite S := Set.infinite_coe_iff.mpr hSinf
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hp (measure_ne_top μ Set.univ)
  obtain ⟨q, hq⟩ := Finset.exists_card_eq (α := S) N
  let q' : Finset M := q.map (Function.Embedding.subtype S)
  have hq'measure : μ (q' : Set M) = N * p := by
    rw [← MeasureTheory.sum_measure_singleton]
    calc
      (∑ y ∈ q', μ {y}) = ∑ y ∈ q, μ {(y : M)} := by
        simp only [q', Finset.sum_map, Function.Embedding.subtype_apply]
        apply Finset.sum_congr rfl
        intro y hy
        rfl
      _ = ∑ _y ∈ q, p := by
        apply Finset.sum_congr rfl
        intro y hy
        exact y.property
      _ = N * p := by simp [hq]
  exact (not_lt_of_ge (hq'measure ▸ measure_mono (Set.subset_univ (q' : Set M)))) hN

lemma measure_singleton_map_eq
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure M) (T : M → M)
    (hT_inj : Function.Injective T)
    (hT : MeasurePreserving T μ μ)
    (x : M) :
    μ {T x} = μ {x} := by
  rw [← hT.measure_preimage (measurableSet_singleton (T x)).nullMeasurableSet]
  congr 1
  ext y
  simp [hT_inj.eq_iff]

lemma finite_full_measure_of_atom_of_ergodic
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (T : M → M) (hT_inj : Function.Injective T)
    (hT : MeasurePreserving T μ μ) (hErg : Ergodic T μ)
    {x : M} (hx : μ {x} ≠ 0) :
    ∃ s : Finset M, μ (s : Set M)ᶜ = 0 := by
  classical
  let S : Set M := {y | μ {y} = μ {x}}
  have hSfinite : S.Finite := finite_setOf_measure_singleton_eq μ hx
  have hSmeas : MeasurableSet S := hSfinite.measurableSet
  have hSinv : T ⁻¹' S = S := by
    ext y
    change μ {T y} = μ {x} ↔ μ {y} = μ {x}
    rw [measure_singleton_map_eq μ T hT_inj hT y]
  have hxS : x ∈ S := rfl
  have hμS : μ S ≠ 0 := by
    intro hzero
    apply hx
    exact measure_mono_null (Set.singleton_subset_iff.mpr hxS) hzero
  have hμS_one : μ S = 1 :=
    (hErg.prob_eq_zero_or_one hSmeas hSinv).resolve_left hμS
  have hμScompl : μ Sᶜ = 0 := by
    rw [measure_compl hSmeas (by finiteness), measure_univ, hμS_one]
    simp
  exact ⟨hSfinite.toFinset, by simpa using hμScompl⟩

lemma entropy_dimension_lyapunov_of_atom_of_ergodic
    (T : EucPlane → EucPlane)
    (hT_inj : Function.Injective T)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_pres : MeasurePreserving T μ μ)
    (hμ_erg : Ergodic T μ)
    {x : EucPlane} (hx : μ {x} ≠ 0) :
    kolmogorovSinaiEntropy μ T =
      (dimMeasure μ).toReal *
        harmonicMeanLyapunov
          (∫ y, lyapunovUpperAt T y ∂μ)
          (∫ y, lyapunovLowerAt T y ∂μ) / 2 := by
  obtain ⟨s, hs⟩ := finite_full_measure_of_atom_of_ergodic μ T hT_inj hμ_pres hμ_erg hx
  exact entropy_dimension_lyapunov_of_finite_full_measure T μ hμ_pres s hs

lemma exists_atom_of_countable_full_measure
    {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure M) [IsProbabilityMeasure μ]
    {s : Set M} (hs : s.Countable) (hμs : μ sᶜ = 0) :
    ∃ x ∈ s, μ {x} ≠ 0 := by
  by_contra h
  push Not at h
  have hall : ∀ x : M, μ {x} = 0 := by
    intro x
    by_cases hxs : x ∈ s
    · exact h x hxs
    · exact measure_mono_null (Set.singleton_subset_iff.mpr hxs) hμs
  letI : NoAtoms μ := ⟨hall⟩
  have hs_zero : μ s = 0 := hs.measure_zero μ
  have hs_one : μ s = 1 := by
    rw [measure_of_measure_compl_eq_zero hμs, measure_univ]
  rw [hs_zero] at hs_one
  simp at hs_one

lemma entropy_dimension_lyapunov_of_countable_full_measure
    (T : EucPlane → EucPlane)
    (hT_inj : Function.Injective T)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_pres : MeasurePreserving T μ μ)
    (hμ_erg : Ergodic T μ)
    {s : Set EucPlane} (hs : s.Countable) (hμs : μ sᶜ = 0) :
    kolmogorovSinaiEntropy μ T =
      (dimMeasure μ).toReal *
        harmonicMeanLyapunov
          (∫ y, lyapunovUpperAt T y ∂μ)
          (∫ y, lyapunovLowerAt T y ∂μ) / 2 := by
  obtain ⟨x, _hxs, hx⟩ := exists_atom_of_countable_full_measure μ hs hμs
  exact entropy_dimension_lyapunov_of_atom_of_ergodic T hT_inj μ hμ_pres hμ_erg hx

lemma young_identity_of_dimension_formula
    {entropy dim lam1 lam2 : ℝ}
    (hlam1 : lam1 ≠ 0)
    (hlam2 : lam2 ≠ 0)
    (hne : lam1 ≠ lam2)
    (hdim : dim = entropy / lam1 - entropy / lam2) :
    entropy = dim * harmonicMeanLyapunov lam1 lam2 / 2 := by
  rw [hdim, harmonicMeanLyapunov]
  field_simp
  ring

lemma young_identity_of_zero_of_degenerate
    {entropy dim lam1 lam2 : ℝ}
    (hentropy : entropy = 0)
    (hdeg : dim = 0 ∨ lam1 = 0 ∨ lam2 = 0 ∨ lam1 = lam2) :
    entropy = dim * harmonicMeanLyapunov lam1 lam2 / 2 := by
  rcases hdeg with hdim | hlam1 | hlam2 | hsame
  · simp [hentropy, hdim]
  · simp [hentropy, hlam1, harmonicMeanLyapunov]
  · simp [hentropy, hlam2, harmonicMeanLyapunov]
  · simp [hentropy, hsame, harmonicMeanLyapunov]

lemma young_identity_of_hyperbolic_or_zero_dim
    {entropy dim lam1 lam2 : ℝ}
    (hhyper : 0 < lam1 → lam2 < 0 → dim = entropy / lam1 - entropy / lam2)
    (hnonhyper : lam1 ≤ 0 ∨ 0 ≤ lam2 → entropy = 0 ∧ dim = 0) :
    entropy = dim * harmonicMeanLyapunov lam1 lam2 / 2 := by
  by_cases hlam1 : 0 < lam1
  · by_cases hlam2 : lam2 < 0
    · exact young_identity_of_dimension_formula hlam1.ne' hlam2.ne
        (ne_of_gt (hlam2.trans hlam1)) (hhyper hlam1 hlam2)
    · obtain ⟨hentropy, hdim⟩ := hnonhyper (Or.inr (le_of_not_gt hlam2))
      exact young_identity_of_zero_of_degenerate hentropy (Or.inl hdim)
  · obtain ⟨hentropy, hdim⟩ := hnonhyper (Or.inl (le_of_not_gt hlam1))
    exact young_identity_of_zero_of_degenerate hentropy (Or.inl hdim)

lemma young_identity_of_hyperbolic_or_degenerate
    {entropy dim lam1 lam2 : ℝ}
    (hhyper : 0 < lam1 → lam2 < 0 → dim = entropy / lam1 - entropy / lam2)
    (hzero : lam1 = 0 ∨ lam2 = 0 → entropy = 0)
    (hsameSign : lam1 < 0 ∨ 0 < lam2 → entropy = 0 ∧ dim = 0) :
    entropy = dim * harmonicMeanLyapunov lam1 lam2 / 2 := by
  by_cases hlam1pos : 0 < lam1
  · by_cases hlam2neg : lam2 < 0
    · exact young_identity_of_dimension_formula hlam1pos.ne' hlam2neg.ne
        (ne_of_gt (hlam2neg.trans hlam1pos)) (hhyper hlam1pos hlam2neg)
    · have hlam2nonneg : 0 ≤ lam2 := le_of_not_gt hlam2neg
      by_cases hlam2zero : lam2 = 0
      · have hentropy := hzero (Or.inr hlam2zero)
        simp [hentropy, hlam2zero, harmonicMeanLyapunov]
      · have hlam2pos : 0 < lam2 := lt_of_le_of_ne hlam2nonneg (Ne.symm hlam2zero)
        obtain ⟨hentropy, hdim⟩ := hsameSign (Or.inr hlam2pos)
        simp [hentropy, hdim]
  · have hlam1nonpos : lam1 ≤ 0 := le_of_not_gt hlam1pos
    by_cases hlam1zero : lam1 = 0
    · have hentropy := hzero (Or.inl hlam1zero)
      simp [hentropy, hlam1zero, harmonicMeanLyapunov]
    · have hlam1neg : lam1 < 0 := lt_of_le_of_ne hlam1nonpos hlam1zero
      obtain ⟨hentropy, hdim⟩ := hsameSign (Or.inl hlam1neg)
      simp [hentropy, hdim]

end Submission.Helpers
