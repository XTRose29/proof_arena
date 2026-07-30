import Submission.LyapunovGrowth

namespace Submission.Helpers

open LeanEval.Dynamics

lemma exists_lipschitz_constant_on_compact
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    {K : Set EucPlane} (hK_compact : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ x ∈ K, ∀ y ∈ K, dist (T x) (T y) ≤ C * dist x y := by
  obtain ⟨R, hKR⟩ := hK_compact.isBounded.subset_closedBall (0 : EucPlane)
  obtain ⟨C, hC_one, hC⟩ :=
    compact_fderiv_bound T hT_smooth (isCompact_closedBall (0 : EucPlane) R)
  refine ⟨C, hC_one, ?_⟩
  intro x hx y hy
  have hdiff : Differentiable ℝ T := hT_smooth.differentiable (by norm_num)
  have hnorm := (convex_closedBall (0 : EucPlane) R).norm_image_sub_le_of_norm_fderiv_le
    (fun _z _hz => hdiff.differentiableAt) hC (hKR hx) (hKR hy)
  simpa [dist_eq_norm, norm_sub_rev] using hnorm

lemma dist_iterate_le_pow_of_lipschitz_on_invariant
    (T : EucPlane → EucPlane) {K : Set EucPlane} (hK_inv : T '' K = K)
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hC : ∀ x ∈ K, ∀ y ∈ K, dist (T x) (T y) ≤ C * dist x y) :
    ∀ n : ℕ, ∀ x ∈ K, ∀ y ∈ K,
      dist (T^[n] x) (T^[n] y) ≤ C ^ n * dist x y := by
  intro n
  induction n with
  | zero =>
      intro x hx y hy
      simp
  | succ n ih =>
      intro x hx y hy
      have hTx : T x ∈ K := by
        rw [← hK_inv]
        exact ⟨x, hx, rfl⟩
      have hTy : T y ∈ K := by
        rw [← hK_inv]
        exact ⟨y, hy, rfl⟩
      rw [Function.iterate_succ_apply]
      calc
        dist (T^[n] (T x)) (T^[n] (T y)) ≤
            C ^ n * dist (T x) (T y) := ih (T x) hTx (T y) hTy
        _ ≤ C ^ n * (C * dist x y) :=
          mul_le_mul_of_nonneg_left (hC x hx y hy) (pow_nonneg hC_nonneg n)
        _ = C ^ (n + 1) * dist x y := by ring

lemma mem_centeredJoin_atom_of_dist_lt_global_radius
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K s : Set EucPlane} (hsK : s ⊆ K)
    (hK_inv : T '' K = K) (hs_invariant : T '' s = s)
    {p : ℕ} (center : Fin p → EucPlane) (radius : Fin p → ℝ)
    (P : Finset (Set EucPlane))
    (hstable : ∀ {u v}, u ∈ s → v ∈ s →
      (∀ i, u ∈ Metric.ball (center i) (radius i) ↔
        v ∈ Metric.ball (center i) (radius i)) →
      ∀ A ∈ P, u ∈ A ↔ v ∈ A)
    {C D delta : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (_hdelta : 0 < delta)
    (hforward_lipschitz :
      ∀ x ∈ K, ∀ y ∈ K, dist (T x) (T y) ≤ C * dist x y)
    (hbackward_lipschitz :
      ∀ x ∈ K, ∀ y ∈ K, dist (T_inv x) (T_inv y) ≤ D * dist x y)
    {m n : ℕ} {x y : EucPlane} {A : Set EucPlane}
    (hA : A ∈ centeredJoin T T_inv P m n) (hxA : x ∈ A)
    (hxs : x ∈ s) (hys : y ∈ s)
    (havoid : x ∉ centeredBoundaryBadReal
      T T_inv center radius delta m n)
    (hxy : dist x y < delta / max (C ^ n) (D ^ m)) :
    y ∈ A := by
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hforward := dist_iterate_le_pow_of_lipschitz_on_invariant
    T hK_inv (zero_le_one.trans hC) hforward_lipschitz
  have hbackward := dist_iterate_le_pow_of_lipschitz_on_invariant
    T_inv hK_inv_inv (zero_le_one.trans hD) hbackward_lipschitz
  have hmax_pos : 0 < max (C ^ n) (D ^ m) := by
    exact lt_of_lt_of_le (pow_pos (lt_of_lt_of_le zero_lt_one hC) n) (le_max_left _ _)
  have hxy_mul : dist x y * max (C ^ n) (D ^ m) < delta :=
    (lt_div_iff₀ hmax_pos).mp hxy
  apply mem_centeredJoin_atom_of_orbit_close_avoiding_boundariesReal
    T T_inv hT_left hT_right hs_invariant center radius P hstable
      hA hxA hxs hys havoid
  · intro j
    calc
      dist (T^[j.val] x) (T^[j.val] y) ≤
          C ^ j.val * dist x y :=
        hforward j.val x (hsK hxs) y (hsK hys)
      _ ≤ max (C ^ n) (D ^ m) * dist x y := by
        gcongr
        exact (pow_le_pow_right₀ hC (Nat.le_of_lt j.isLt)).trans
          (le_max_left _ _)
      _ = dist x y * max (C ^ n) (D ^ m) := mul_comm _ _
      _ < delta := hxy_mul
  · intro q hq_pos hq_le
    calc
      dist (T_inv^[q] x) (T_inv^[q] y) ≤
          D ^ q * dist x y :=
        hbackward q x (hsK hxs) y (hsK hys)
      _ ≤ max (C ^ n) (D ^ m) * dist x y := by
        gcongr
        exact (pow_le_pow_right₀ hD hq_le).trans (le_max_right _ _)
      _ = dist x y * max (C ^ n) (D ^ m) := mul_comm _ _
      _ < delta := hxy_mul

end Submission.Helpers
