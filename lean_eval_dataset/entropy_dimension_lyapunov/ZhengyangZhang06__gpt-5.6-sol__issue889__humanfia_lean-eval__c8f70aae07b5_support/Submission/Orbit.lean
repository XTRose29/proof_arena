import Submission.Helpers

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology

lemma limsup_le_limsup_of_eventually_le_add_tendsto_zero
    {α : Type*} {f : Filter α} [f.NeBot]
    {u v e : α → ℝ}
    (h : u ≤ᶠ[f] v + e)
    (hu_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) f u)
    (hv_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) f v)
    (hv_upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) f v)
    (he : Tendsto e f (𝓝 0)) :
    limsup u f ≤ limsup v f := by
  calc
    limsup u f ≤ limsup (v + e) f := limsup_le_limsup h
      hu_lower.isCobounded_flip (isBoundedUnder_le_add hv_upper he.isBoundedUnder_le)
    _ ≤ limsup v f + limsup e f :=
      limsup_add_le hv_lower hv_upper he.isCoboundedUnder_le he.isBoundedUnder_le
    _ = limsup v f := by rw [he.limsup_eq]; simp

lemma fderiv_iterate_succ_eq
    (T : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (n : ℕ) (x : EucPlane) :
    fderiv ℝ (T^[n + 1]) x =
      fderiv ℝ (T^[n]) (T x) ∘L fderiv ℝ T x := by
  rw [Function.iterate_succ, fderiv_comp]
  · exact (hT_smooth.differentiable (by norm_num)).iterate n |>.differentiableAt
  · exact (hT_smooth.differentiable (by norm_num)).differentiableAt

lemma fderiv_iterate_at_image_eq
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    fderiv ℝ (T^[n]) (T x) =
      fderiv ℝ (T^[n + 1]) x ∘L (fderiv ℝ T x).inverse := by
  rw [fderiv_iterate_succ_eq T hT_smooth]
  rw [ContinuousLinearMap.comp_assoc]
  have hcomp : fderiv ℝ T x ∘L (fderiv ℝ T x).inverse =
      ContinuousLinearMap.id ℝ EucPlane := by
    simpa [Function.iterate_one] using
      Submission.Helpers.fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right 1 x
  rw [hcomp]
  simp

lemma fderiv_iterate_inverse_comp
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    (fderiv ℝ (T^[n]) x).inverse ∘L fderiv ℝ (T^[n]) x =
      ContinuousLinearMap.id ℝ EucPlane := by
  rw [Submission.Helpers.fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right]
  have hT_diff : Differentiable ℝ T := hT_smooth.differentiable (by norm_num)
  have hT_inv_diff : Differentiable ℝ T_inv :=
    hT_inv_smooth.differentiable (by norm_num)
  have hleft := hT_left.iterate n
  calc
    fderiv ℝ (T_inv^[n]) (T^[n] x) ∘L fderiv ℝ (T^[n]) x =
        fderiv ℝ ((T_inv^[n]) ∘ (T^[n])) x := by
      rw [fderiv_comp]
      · exact (hT_inv_diff.iterate n).differentiableAt
      · exact (hT_diff.iterate n).differentiableAt
    _ = ContinuousLinearMap.id ℝ EucPlane := by
      rw [hleft.comp_eq_id, fderiv_id]

lemma fderiv_iterate_succ_inverse_eq
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    (fderiv ℝ (T^[n + 1]) x).inverse =
      (fderiv ℝ T x).inverse ∘L (fderiv ℝ (T^[n]) (T x)).inverse := by
  have hcomp : fderiv ℝ T x ∘L (fderiv ℝ T x).inverse =
      ContinuousLinearMap.id ℝ EucPlane := by
    simpa [Function.iterate_one] using
      (Submission.Helpers.fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right 1 x)
  have hinvcomp : (fderiv ℝ T x).inverse ∘L fderiv ℝ T x =
      ContinuousLinearMap.id ℝ EucPlane := by
    simpa [Function.iterate_one] using
      (fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right 1 x)
  have hA : (fderiv ℝ T x).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hcomp hinvcomp
  rw [fderiv_iterate_succ_eq T hT_smooth]
  exact hA.inverse_comp_of_right

lemma fderiv_iterate_at_image_inverse_eq
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    (fderiv ℝ (T^[n]) (T x)).inverse =
      fderiv ℝ T x ∘L (fderiv ℝ (T^[n + 1]) x).inverse := by
  rw [fderiv_iterate_succ_inverse_eq T T_inv hT_smooth hT_inv_smooth hT_left hT_right]
  rw [← ContinuousLinearMap.comp_assoc]
  have hcomp : fderiv ℝ T x ∘L (fderiv ℝ T x).inverse =
      ContinuousLinearMap.id ℝ EucPlane := by
    simpa [Function.iterate_one] using
      Submission.Helpers.fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right 1 x
  rw [hcomp]
  simp

lemma log_norm_fderiv_iterate_succ_le
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    Real.log ‖fderiv ℝ (T^[n + 1]) x‖ ≤
      Real.log ‖fderiv ℝ (T^[n]) (T x)‖ + Real.log ‖fderiv ℝ T x‖ := by
  have hnpos := Submission.Helpers.norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right n (T x)
  have hTpos := Submission.Helpers.norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right 1 x
  have hsuccpos := Submission.Helpers.norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right (n + 1) x
  have hnorm : ‖fderiv ℝ (T^[n + 1]) x‖ ≤
      ‖fderiv ℝ (T^[n]) (T x)‖ * ‖fderiv ℝ T x‖ := by
    rw [fderiv_iterate_succ_eq T hT_smooth]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hlog := Real.log_le_log hsuccpos hnorm
  rw [Real.log_mul hnpos.ne' (by simpa [Function.iterate_one] using hTpos.ne')] at hlog
  exact hlog

lemma log_norm_fderiv_iterate_at_image_le
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    Real.log ‖fderiv ℝ (T^[n]) (T x)‖ ≤
      Real.log ‖fderiv ℝ (T^[n + 1]) x‖ +
        Real.log ‖(fderiv ℝ T x).inverse‖ := by
  have hnpos := Submission.Helpers.norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right n (T x)
  have hsuccpos := Submission.Helpers.norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right (n + 1) x
  have hinvpos : 0 < ‖(fderiv ℝ T x).inverse‖ := by
    have hinveq : (fderiv ℝ T x).inverse = fderiv ℝ T_inv (T x) := by
      simpa [Function.iterate_one] using
        Submission.Helpers.fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right 1 x
    rw [hinveq]
    simpa [Function.iterate_one] using
      Submission.Helpers.norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
        hT_right hT_left 1 (T x)
  have hnorm : ‖fderiv ℝ (T^[n]) (T x)‖ ≤
      ‖fderiv ℝ (T^[n + 1]) x‖ * ‖(fderiv ℝ T x).inverse‖ := by
    rw [fderiv_iterate_at_image_eq T T_inv hT_smooth hT_inv_smooth hT_left hT_right]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hlog := Real.log_le_log hnpos hnorm
  rw [Real.log_mul hsuccpos.ne' hinvpos.ne'] at hlog
  exact hlog

lemma log_norm_fderiv_iterate_succ_inverse_le
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    Real.log ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ ≤
      Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ +
        Real.log ‖(fderiv ℝ T x).inverse‖ := by
  have hsuccpos : 0 < ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ := by
    rw [Submission.Helpers.fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right]
    exact Submission.Helpers.norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
      hT_right hT_left (n + 1) (T^[n + 1] x)
  have hnpos : 0 < ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ := by
    rw [Submission.Helpers.fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right]
    exact Submission.Helpers.norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
      hT_right hT_left n (T^[n] (T x))
  have hApos : 0 < ‖(fderiv ℝ T x).inverse‖ := by
    rw [show (fderiv ℝ T x).inverse = fderiv ℝ T_inv (T x) by
      simpa [Function.iterate_one] using
        Submission.Helpers.fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right 1 x]
    simpa [Function.iterate_one] using
      Submission.Helpers.norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
        hT_right hT_left 1 (T x)
  have hnorm : ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ ≤
      ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ * ‖(fderiv ℝ T x).inverse‖ := by
    rw [fderiv_iterate_succ_inverse_eq T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)
  have hlog := Real.log_le_log hsuccpos hnorm
  rw [Real.log_mul hnpos.ne' hApos.ne'] at hlog
  exact hlog

lemma log_norm_fderiv_iterate_at_image_inverse_le
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) (x : EucPlane) :
    Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ ≤
      Real.log ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ + Real.log ‖fderiv ℝ T x‖ := by
  have hnpos : 0 < ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ := by
    rw [Submission.Helpers.fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right]
    exact Submission.Helpers.norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
      hT_right hT_left n (T^[n] (T x))
  have hsuccpos : 0 < ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ := by
    rw [Submission.Helpers.fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right]
    exact Submission.Helpers.norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
      hT_right hT_left (n + 1) (T^[n + 1] x)
  have hApos := Submission.Helpers.norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right 1 x
  have hnorm : ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ ≤
      ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ * ‖fderiv ℝ T x‖ := by
    rw [fderiv_iterate_at_image_inverse_eq T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right]
    exact (ContinuousLinearMap.opNorm_comp_le (fderiv ℝ T x)
      (fderiv ℝ (T^[n + 1]) x).inverse).trans_eq (mul_comm _ _)
  have hlog := Real.log_le_log hnpos hnorm
  rw [Real.log_mul hsuccpos.ne' (by simpa [Function.iterate_one] using hApos.ne')] at hlog
  exact hlog

lemma lyapunovUpperAt_map_eq
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hx : x ∈ K) :
    lyapunovUpperAt T (T x) = lyapunovUpperAt T x := by
  obtain ⟨C, hC_one, hC⟩ :=
    Submission.Helpers.compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨D, hD_one, hD⟩ :=
    Submission.Helpers.compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  have hTx : T x ∈ K := by
    rw [← hK_inv]
    exact ⟨x, hx, rfl⟩
  let p : ℕ → ℝ := fun n => Real.log ‖fderiv ℝ (T^[n + 1]) x‖ / (n + 1)
  let q : ℕ → ℝ := fun n => Real.log ‖fderiv ℝ (T^[n]) (T x)‖ / n
  let e₁ : ℕ → ℝ := fun n =>
    (Real.log ‖fderiv ℝ T x‖ - (-Real.log D)) / (n + 1)
  let e₂ : ℕ → ℝ := fun n =>
    (Real.log C + Real.log ‖(fderiv ℝ T x).inverse‖) / n
  have hp_lower : ∀ n, -Real.log D ≤ p n := by
    intro n
    simpa [p, Nat.cast_add, Nat.cast_one] using
      Submission.Helpers.neg_log_le_log_norm_fderiv_iterate_div T T_inv
        hT_smooth hT_inv_smooth hT_left hT_right hK_inv hD_one hD (n + 1) hx
  have hp_upper : ∀ n, p n ≤ Real.log C := by
    intro n
    simpa [p, Nat.cast_add, Nat.cast_one] using
      Submission.Helpers.log_norm_fderiv_iterate_div_le T hT_smooth hK_inv
        hC_one hC (n + 1) hx
  have hq_lower : ∀ n, -Real.log D ≤ q n := by
    intro n
    exact Submission.Helpers.neg_log_le_log_norm_fderiv_iterate_div T T_inv
      hT_smooth hT_inv_smooth hT_left hT_right hK_inv hD_one hD n hTx
  have hq_upper : ∀ n, q n ≤ Real.log C := by
    intro n
    exact Submission.Helpers.log_norm_fderiv_iterate_div_le T hT_smooth hK_inv
      hC_one hC n hTx
  have hp_lower' : IsBoundedUnder (fun a b : ℝ => a ≥ b) atTop p :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hp_lower)
  have hp_upper' : IsBoundedUnder (fun a b : ℝ => a ≤ b) atTop p :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hp_upper)
  have hq_lower' : IsBoundedUnder (fun a b : ℝ => a ≥ b) atTop q :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hq_lower)
  have hq_upper' : IsBoundedUnder (fun a b : ℝ => a ≤ b) atTop q :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hq_upper)
  have he₁ : Tendsto e₁ atTop (𝓝 0) := by
    simpa [e₁, Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat
        (Real.log ‖fderiv ℝ T x‖ - (-Real.log D))).comp (tendsto_add_atTop_nat 1)
  have he₂ : Tendsto e₂ atTop (𝓝 0) := by
    simpa [e₂] using tendsto_const_div_atTop_nhds_zero_nat
      (Real.log C + Real.log ‖(fderiv ℝ T x).inverse‖)
  have hpq : p ≤ᶠ[atTop] q + e₁ := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
    have hn1nonneg : (0 : ℝ) ≤ n + 1 := by positivity
    have hlog := log_norm_fderiv_iterate_succ_le T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
    have hlower := hq_lower n
    change Real.log ‖fderiv ℝ (T^[n + 1]) x‖ / (n + 1) ≤
      Real.log ‖fderiv ℝ (T^[n]) (T x)‖ / n +
        (Real.log ‖fderiv ℝ T x‖ - -Real.log D) / (n + 1)
    calc
      Real.log ‖fderiv ℝ (T^[n + 1]) x‖ / (n + 1) ≤
          (Real.log ‖fderiv ℝ (T^[n]) (T x)‖ + Real.log ‖fderiv ℝ T x‖) /
            (n + 1) := div_le_div_of_nonneg_right hlog hn1nonneg
      _ = Real.log ‖fderiv ℝ (T^[n]) (T x)‖ / n +
          (Real.log ‖fderiv ℝ T x‖ -
            Real.log ‖fderiv ℝ (T^[n]) (T x)‖ / n) / (n + 1) := by
        field_simp
        ring
      _ ≤ Real.log ‖fderiv ℝ (T^[n]) (T x)‖ / n +
          (Real.log ‖fderiv ℝ T x‖ - -Real.log D) / (n + 1) := by
        exact add_le_add (le_refl _)
          (div_le_div_of_nonneg_right
            (sub_le_sub_left hlower (Real.log ‖fderiv ℝ T x‖)) hn1nonneg)
  have hqp : q ≤ᶠ[atTop] p + e₂ := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hlog := log_norm_fderiv_iterate_at_image_le T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
    have hupper := hp_upper n
    change Real.log ‖fderiv ℝ (T^[n]) (T x)‖ / n ≤
      Real.log ‖fderiv ℝ (T^[n + 1]) x‖ / (n + 1) +
        (Real.log C + Real.log ‖(fderiv ℝ T x).inverse‖) / n
    calc
      Real.log ‖fderiv ℝ (T^[n]) (T x)‖ / n ≤
          (Real.log ‖fderiv ℝ (T^[n + 1]) x‖ +
            Real.log ‖(fderiv ℝ T x).inverse‖) / n :=
        div_le_div_of_nonneg_right hlog hnnonneg
      _ = Real.log ‖fderiv ℝ (T^[n + 1]) x‖ / (n + 1) +
          (Real.log ‖fderiv ℝ (T^[n + 1]) x‖ / (n + 1) +
            Real.log ‖(fderiv ℝ T x).inverse‖) / n := by
        field_simp
        ring
      _ ≤ Real.log ‖fderiv ℝ (T^[n + 1]) x‖ / (n + 1) +
          (Real.log C + Real.log ‖(fderiv ℝ T x).inverse‖) / n := by
        exact add_le_add (le_refl _)
          (div_le_div_of_nonneg_right
            (add_le_add hupper (le_refl (Real.log ‖(fderiv ℝ T x).inverse‖))) hnnonneg)
  rw [lyapunovUpperAt, lyapunovUpperAt]
  rw [← limsup_nat_add
    (fun n => Real.log ‖fderiv ℝ (T^[n]) x‖ / n) 1]
  apply le_antisymm
  · simpa [p, q, Nat.cast_add, Nat.cast_one] using
      limsup_le_limsup_of_eventually_le_add_tendsto_zero hqp hq_lower'
        hp_lower' hp_upper' he₂
  · simpa [p, q, Nat.cast_add, Nat.cast_one] using
      limsup_le_limsup_of_eventually_le_add_tendsto_zero hpq hp_lower'
        hq_lower' hq_upper' he₁

lemma lyapunovLowerAt_map_eq
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hx : x ∈ K) :
    lyapunovLowerAt T (T x) = lyapunovLowerAt T x := by
  obtain ⟨C, hC_one, hC⟩ :=
    Submission.Helpers.compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨D, hD_one, hD⟩ :=
    Submission.Helpers.compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  have hTx : T x ∈ K := by
    rw [← hK_inv]
    exact ⟨x, hx, rfl⟩
  let p : ℕ → ℝ := fun n =>
    Real.log ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ / (n + 1)
  let q : ℕ → ℝ := fun n =>
    Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ / n
  let e₁ : ℕ → ℝ := fun n =>
    (Real.log ‖(fderiv ℝ T x).inverse‖ - (-Real.log C)) / (n + 1)
  let e₂ : ℕ → ℝ := fun n => (Real.log D + Real.log ‖fderiv ℝ T x‖) / n
  have hp_lower : ∀ n, -Real.log C ≤ p n := by
    intro n
    simpa [p, Nat.cast_add, Nat.cast_one] using
      Submission.Helpers.neg_log_le_log_norm_fderiv_iterate_inverse_div T T_inv
        hT_smooth hT_inv_smooth hT_left hT_right hK_inv hC_one hC (n + 1) hx
  have hp_upper : ∀ n, p n ≤ Real.log D := by
    intro n
    simpa [p, Nat.cast_add, Nat.cast_one] using
      Submission.Helpers.log_norm_fderiv_iterate_inverse_div_le T T_inv hT_smooth
        hT_inv_smooth hT_left hT_right hK_inv hD_one hD (n + 1) hx
  have hq_lower : ∀ n, -Real.log C ≤ q n := by
    intro n
    exact Submission.Helpers.neg_log_le_log_norm_fderiv_iterate_inverse_div T T_inv
      hT_smooth hT_inv_smooth hT_left hT_right hK_inv hC_one hC n hTx
  have hq_upper : ∀ n, q n ≤ Real.log D := by
    intro n
    exact Submission.Helpers.log_norm_fderiv_iterate_inverse_div_le T T_inv hT_smooth
      hT_inv_smooth hT_left hT_right hK_inv hD_one hD n hTx
  have hp_lower' : IsBoundedUnder (fun a b : ℝ => a ≥ b) atTop p :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hp_lower)
  have hp_upper' : IsBoundedUnder (fun a b : ℝ => a ≤ b) atTop p :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hp_upper)
  have hq_lower' : IsBoundedUnder (fun a b : ℝ => a ≥ b) atTop q :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hq_lower)
  have hq_upper' : IsBoundedUnder (fun a b : ℝ => a ≤ b) atTop q :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hq_upper)
  have he₁ : Tendsto e₁ atTop (𝓝 0) := by
    simpa [e₁, Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat
        (Real.log ‖(fderiv ℝ T x).inverse‖ - (-Real.log C))).comp
          (tendsto_add_atTop_nat 1)
  have he₂ : Tendsto e₂ atTop (𝓝 0) := by
    simpa [e₂] using tendsto_const_div_atTop_nhds_zero_nat
      (Real.log D + Real.log ‖fderiv ℝ T x‖)
  have hpq : p ≤ᶠ[atTop] q + e₁ := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hn1nonneg : (0 : ℝ) ≤ n + 1 := by positivity
    have hlog := log_norm_fderiv_iterate_succ_inverse_le T T_inv hT_smooth
      hT_inv_smooth hT_left hT_right n x
    have hlower := hq_lower n
    change Real.log ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ / (n + 1) ≤
      Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ / n +
        (Real.log ‖(fderiv ℝ T x).inverse‖ - -Real.log C) / (n + 1)
    calc
      Real.log ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ / (n + 1) ≤
          (Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ +
            Real.log ‖(fderiv ℝ T x).inverse‖) / (n + 1) :=
        div_le_div_of_nonneg_right hlog hn1nonneg
      _ = Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ / n +
          (Real.log ‖(fderiv ℝ T x).inverse‖ -
            Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ / n) / (n + 1) := by
        field_simp
        ring
      _ ≤ Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ / n +
          (Real.log ‖(fderiv ℝ T x).inverse‖ - -Real.log C) / (n + 1) := by
        exact add_le_add (le_refl _)
          (div_le_div_of_nonneg_right
            (sub_le_sub_left hlower (Real.log ‖(fderiv ℝ T x).inverse‖)) hn1nonneg)
  have hqp : q ≤ᶠ[atTop] p + e₂ := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hlog := log_norm_fderiv_iterate_at_image_inverse_le T T_inv hT_smooth
      hT_inv_smooth hT_left hT_right n x
    have hupper := hp_upper n
    change Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ / n ≤
      Real.log ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ / (n + 1) +
        (Real.log D + Real.log ‖fderiv ℝ T x‖) / n
    calc
      Real.log ‖(fderiv ℝ (T^[n]) (T x)).inverse‖ / n ≤
          (Real.log ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ +
            Real.log ‖fderiv ℝ T x‖) / n :=
        div_le_div_of_nonneg_right hlog hnnonneg
      _ = Real.log ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ / (n + 1) +
          (Real.log ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ / (n + 1) +
            Real.log ‖fderiv ℝ T x‖) / n := by
        field_simp
        ring
      _ ≤ Real.log ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ / (n + 1) +
          (Real.log D + Real.log ‖fderiv ℝ T x‖) / n := by
        exact add_le_add (le_refl _)
          (div_le_div_of_nonneg_right
            (add_le_add hupper (le_refl (Real.log ‖fderiv ℝ T x‖))) hnnonneg)
  have hlim : limsup q atTop = limsup p atTop := by
    apply le_antisymm
    · exact limsup_le_limsup_of_eventually_le_add_tendsto_zero hqp hq_lower'
        hp_lower' hp_upper' he₂
    · exact limsup_le_limsup_of_eventually_le_add_tendsto_zero hpq hp_lower'
        hq_lower' hq_upper' he₁
  rw [lyapunovLowerAt, lyapunovLowerAt]
  rw [← limsup_nat_add
    (fun n => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n) 1]
  exact congrArg Neg.neg (by simpa [p, q, Nat.cast_add, Nat.cast_one] using hlim)

lemma lyapunovUpperAt_ae_eq_integral
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_supp : μ Kᶜ = 0) (hμ_erg : Ergodic T μ) :
    lyapunovUpperAt T =ᵐ[μ]
      fun _ => ∫ x, lyapunovUpperAt T x ∂μ := by
  have hinv : lyapunovUpperAt T ∘ T =ᵐ[μ] lyapunovUpperAt T := by
    filter_upwards [mem_ae_iff.mpr hμ_supp] with x hx
    exact lyapunovUpperAt_map_eq T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv hx
  obtain ⟨c, hc⟩ := hμ_erg.ae_eq_const_of_ae_eq_comp_ae
    (Submission.Helpers.measurable_lyapunovUpperAt T hT_smooth).aestronglyMeasurable hinv
  have hint : (∫ x, lyapunovUpperAt T x ∂μ) = c := by
    rw [integral_congr_ae hc]
    change (∫ _ : EucPlane, c ∂μ) = c
    rw [integral_const]
    simp [measureReal_def]
  simpa [hint, Function.const_def] using hc

lemma lyapunovLowerAt_ae_eq_integral
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_supp : μ Kᶜ = 0) (hμ_erg : Ergodic T μ) :
    lyapunovLowerAt T =ᵐ[μ]
      fun _ => ∫ x, lyapunovLowerAt T x ∂μ := by
  have hinv : lyapunovLowerAt T ∘ T =ᵐ[μ] lyapunovLowerAt T := by
    filter_upwards [mem_ae_iff.mpr hμ_supp] with x hx
    exact lyapunovLowerAt_map_eq T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact hK_inv hx
  obtain ⟨c, hc⟩ := hμ_erg.ae_eq_const_of_ae_eq_comp_ae
    (Submission.Helpers.measurable_lyapunovLowerAt T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right).aestronglyMeasurable hinv
  have hint : (∫ x, lyapunovLowerAt T x ∂μ) = c := by
    rw [integral_congr_ae hc]
    change (∫ _ : EucPlane, c ∂μ) = c
    rw [integral_const]
    simp [measureReal_def]
  simpa [hint, Function.const_def] using hc

end Submission.Helpers
