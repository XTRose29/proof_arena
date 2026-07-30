import Submission.NonlinearStoppingGrowth
import Submission.DerivativeDistortion

namespace Submission.Helpers

open LeanEval.Dynamics

lemma exists_common_fderiv_lipschitz_constant_iterates_on_compact_convex
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    {S : Set EucPlane} (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ n, n ≤ N → ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (T^[n]) x - fderiv ℝ (T^[n]) y‖ ≤ B * dist x y := by
  let bound : ℕ → ℝ := fun n =>
    (exists_fderiv_lipschitz_constant_on_compact_convex
      (T^[n]) (contDiff_iterate T hT_smooth n) hS_compact hS_convex).choose
  have hbound (n : ℕ) : 1 ≤ bound n ∧ ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (T^[n]) x - fderiv ℝ (T^[n]) y‖ ≤ bound n * dist x y :=
    (exists_fderiv_lipschitz_constant_on_compact_convex
      (T^[n]) (contDiff_iterate T hT_smooth n) hS_compact hS_convex).choose_spec
  let B := 1 + ∑ n ∈ Finset.range (N + 1), bound n
  have hB_one : 1 ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun n _hn =>
      zero_le_one.trans (hbound n).1)
  refine ⟨B, hB_one, ?_⟩
  intro n hn x hx y hy
  have hnmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hbound_le_sum : bound n ≤ ∑ i ∈ Finset.range (N + 1), bound i :=
    Finset.single_le_sum
      (fun i _hi => zero_le_one.trans (hbound i).1) hnmem
  calc
    ‖fderiv ℝ (T^[n]) x - fderiv ℝ (T^[n]) y‖ ≤
        bound n * dist x y := (hbound n).2 x hx y hy
    _ ≤ B * dist x y := by
      gcongr
      dsimp [B]
      linarith

lemma one_div_pow_le_norm_fderiv_iterate
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_inv : T '' K = K)
    {D : ℝ} (hD_one : 1 ≤ D)
    (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    (n : ℕ) {x : EucPlane} (hx : x ∈ K) :
    1 / D ^ n ≤ ‖fderiv ℝ (T^[n]) x‖ := by
  have hcomp := fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right n x
  have hprod : 1 ≤ ‖fderiv ℝ (T^[n]) x‖ *
      ‖(fderiv ℝ (T^[n]) x).inverse‖ := by
    calc
      1 = ‖ContinuousLinearMap.id ℝ EucPlane‖ :=
        (ContinuousLinearMap.norm_id (𝕜 := ℝ) (E := EucPlane)).symm
      _ = ‖fderiv ℝ (T^[n]) x ∘L
          (fderiv ℝ (T^[n]) x).inverse‖ := congrArg norm hcomp.symm
      _ ≤ ‖fderiv ℝ (T^[n]) x‖ *
          ‖(fderiv ℝ (T^[n]) x).inverse‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
  have hinv := norm_fderiv_iterate_inverse_le_pow T T_inv hT_smooth
    hT_inv_smooth hT_left hT_right hK_inv hD_one hD n hx
  have hprodD : 1 ≤ ‖fderiv ℝ (T^[n]) x‖ * D ^ n :=
    hprod.trans (mul_le_mul_of_nonneg_left hinv (norm_nonneg _))
  exact (div_le_iff₀ (pow_pos (zero_lt_one.trans_le hD_one) n)).2 hprodD

lemma dist_iterate_le_exp_eta_mul_norm
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K S : Set EucPlane} (hK_inv : T '' K = K)
    (hKS : K ⊆ S) (hS_convex : Convex ℝ S)
    {D B delta eta : ℝ} {N n : ℕ}
    (hD_one : 1 ≤ D) (hD : ∀ x ∈ K, ‖fderiv ℝ T_inv x‖ ≤ D)
    (hB : 0 ≤ B)
    (hderiv : ∀ q, q ≤ N → ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (T^[q]) x - fderiv ℝ (T^[q]) y‖ ≤ B * dist x y)
    (heta : 0 < eta)
    (hdelta : B * delta ≤ (1 / D ^ N) * (Real.exp eta - 1))
    (hn_pos : 0 < n) (hnN : n ≤ N)
    {x y : EucPlane} (hx : x ∈ K) (hy : y ∈ K)
    (hxy : dist x y ≤ delta) :
    dist (T^[n] x) (T^[n] y) ≤
      Real.exp (eta * n) * ‖fderiv ℝ (T^[n]) x‖ * dist x y := by
  let F := T^[n]
  let A := fderiv ℝ F x
  let z := y - x
  have hlinearization := norm_image_sub_linearization_le
    F (contDiff_iterate T hT_smooth n) hS_convex hB
      (hderiv n hnN) (hKS hx) (hKS hy)
  have hDpow_pos : 0 < D ^ N := pow_pos (zero_lt_one.trans_le hD_one) N
  have hDpow_n_pos : 0 < D ^ n := pow_pos (zero_lt_one.trans_le hD_one) n
  have hpow : D ^ n ≤ D ^ N := pow_le_pow_right₀ hD_one hnN
  have hc_le : 1 / D ^ N ≤ 1 / D ^ n :=
    one_div_le_one_div_of_le hDpow_n_pos hpow
  have hlower : 1 / D ^ N ≤ ‖A‖ := by
    exact hc_le.trans (one_div_pow_le_norm_fderiv_iterate
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        (K := K) (D := D) hK_inv hD_one hD n hx)
  have htheta_nonneg : 0 ≤ Real.exp eta - 1 :=
    (sub_nonneg.mpr (Real.one_le_exp heta.le))
  have hBdist : B * dist x y ≤ ‖A‖ * (Real.exp eta - 1) := by
    calc
      B * dist x y ≤ B * delta := mul_le_mul_of_nonneg_left hxy hB
      _ ≤ (1 / D ^ N) * (Real.exp eta - 1) := hdelta
      _ ≤ ‖A‖ * (Real.exp eta - 1) :=
        mul_le_mul_of_nonneg_right hlower htheta_nonneg
  have heta_one : Real.exp eta ≤ Real.exp (eta * n) := by
    apply Real.exp_le_exp.mpr
    have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
    exact (le_mul_iff_one_le_right heta).2 hn_real
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖F y - F x‖ = ‖(F y - F x - A z) + A z‖ := by
      congr 1
      abel
    _ ≤ ‖F y - F x - A z‖ + ‖A z‖ := norm_add_le _ _
    _ ≤ B * ‖z‖ ^ 2 + ‖A‖ * ‖z‖ :=
      add_le_add hlinearization (A.le_opNorm z)
    _ = (B * dist x y + ‖A‖) * dist x y := by
      simp only [z, dist_eq_norm, norm_sub_rev]
      ring
    _ ≤ (‖A‖ * (Real.exp eta - 1) + ‖A‖) * dist x y := by
      gcongr
    _ = Real.exp eta * ‖A‖ * dist x y := by ring
    _ ≤ Real.exp (eta * n) * ‖A‖ * dist x y := by
      gcongr

theorem exists_delta_dist_iterate_le_exp_eta_mul_norm
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (N : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ n, 0 < n → n ≤ N →
      ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ delta →
        dist (T^[n] x) (T^[n] y) ≤
          Real.exp (eta * n) * ‖fderiv ℝ (T^[n]) x‖ * dist x y := by
  obtain ⟨R, hKR⟩ := hK_compact.isBounded.subset_closedBall (0 : EucPlane)
  let S := Metric.closedBall (0 : EucPlane) R
  have hS_compact : IsCompact S := isCompact_closedBall _ _
  have hS_convex : Convex ℝ S := convex_closedBall _ _
  obtain ⟨B, hB_one, hderiv⟩ :=
    exists_common_fderiv_lipschitz_constant_iterates_on_compact_convex
      T hT_smooth hS_compact hS_convex N
  obtain ⟨D, hD_one, hD⟩ := compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  let delta := (1 / D ^ N) * (Real.exp eta - 1) / B
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact div_pos (mul_pos (one_div_pos.mpr
      (pow_pos (zero_lt_one.trans_le hD_one) N))
        (sub_pos.mpr ((Real.one_lt_exp_iff).2 heta)))
      (zero_lt_one.trans_le hB_one)
  refine ⟨delta, hdelta_pos, ?_⟩
  intro n hn_pos hnN x hx y hy hxy
  have hdelta_budget : B * delta ≤
      (1 / D ^ N) * (Real.exp eta - 1) := by
    dsimp [delta]
    field_simp [(zero_lt_one.trans_le hB_one).ne']
    exact le_rfl
  exact dist_iterate_le_exp_eta_mul_norm
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      (K := K) (S := S) hK_inv hKR hS_convex hD_one hD
      (zero_le_one.trans hB_one) hderiv
      heta hdelta_budget (n := n) hn_pos hnN hx hy hxy

end Submission.Helpers
