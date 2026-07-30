import Submission.GlobalOrbitGeometry
import Submission.LinearCocyclePerturbation
import Submission.ScaledBallCover

namespace Submission.Helpers

open LeanEval.Dynamics

/-- A common one-step bound turns a small initial separation into an explicit
operator error for the whole secant product. -/
lemma norm_orbitSecantPrefix_sub_fderiv_le_of_start_dist
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    {K S : Set EucPlane} (hK_inv : T '' K = K) (hKS : K ⊆ S)
    (hS_convex : Convex ℝ S)
    {M r : ℝ} (hM : 1 ≤ M) (hr : 0 ≤ r)
    (hT_lipschitz : ∀ x ∈ K, ∀ y ∈ K,
      dist (T x) (T y) ≤ M * dist x y)
    (hderiv : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ M)
    (hderiv_lipschitz : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ M * dist x y)
    {n : ℕ} (x y : EucPlane) (hx : x ∈ K) (hy : y ∈ K)
    (hxy : dist x y ≤ r)
    (hsmall : M ^ n * r ≤ 1) :
    ‖clmPrefixProduct (orbitSecantStep T x y) n -
        fderiv ℝ (T^[n]) x‖ ≤
      n * (M * (M ^ n * r)) * (2 * M) ^ (n + 1) := by
  have hM_nonneg : 0 ≤ M := zero_le_one.trans hM
  have hr_nonneg : 0 ≤ M ^ n * r := mul_nonneg (pow_nonneg hM_nonneg n) hr
  have horbitK (z : EucPlane) (hz : z ∈ K) (k : ℕ) : T^[k] z ∈ K := by
    rw [← image_iterate_eq_of_image_eq T hK_inv k]
    exact ⟨z, hz, rfl⟩
  have hgrowth := dist_iterate_le_pow_of_lipschitz_on_invariant
    T hK_inv hM_nonneg hT_lipschitz
  have horbit : ∀ k, k < n →
      ‖T^[k] y - T^[k] x‖ ≤ M ^ n * r := by
    intro k hk
    have hpow : M ^ k ≤ M ^ n := pow_le_pow_right₀ hM hk.le
    calc
      ‖T^[k] y - T^[k] x‖ = dist (T^[k] x) (T^[k] y) := by
        simp [dist_eq_norm, norm_sub_rev]
      _ ≤ M ^ k * dist x y := hgrowth k x hx y hy
      _ ≤ M ^ k * r := mul_le_mul_of_nonneg_left hxy (pow_nonneg hM_nonneg k)
      _ ≤ M ^ n * r := mul_le_mul_of_nonneg_right hpow hr
  have hrem : ∀ k, k < n →
      ‖T (T^[k] y) - T (T^[k] x) -
          fderiv ℝ T (T^[k] x) (T^[k] y - T^[k] x)‖ ≤
        M * ‖T^[k] y - T^[k] x‖ ^ 2 := by
    intro k _hk
    exact norm_image_sub_linearization_le T hT_smooth hS_convex
      hM_nonneg hderiv_lipschitz
        (hKS (horbitK x hx k)) (hKS (horbitK y hy k))
  have hbase_one : 1 ≤ M + M * (M ^ n * r) :=
    hM.trans (le_add_of_nonneg_right (mul_nonneg hM_nonneg hr_nonneg))
  have hraw :=
    norm_clmPrefixProduct_orbitSecantStep_sub_fderiv_iterate_le_of_lt
      T (hT_smooth.differentiable (by norm_num)) x y hM_nonneg hr_nonneg
        hbase_one n (fun k _hk => hderiv _ (horbitK x hx k)) horbit hrem
  apply hraw.trans
  have hbase : M + M * (M ^ n * r) ≤ 2 * M := by
    calc
      M + M * (M ^ n * r) ≤ M + M * 1 := by
        gcongr
      _ = 2 * M := by ring
  have hpow : (M + M * (M ^ n * r)) ^ (n + 1) ≤
      (2 * M) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) hbase (n + 1)
  gcongr

noncomputable def linearNetPairRadius (R : ℝ) (D n : ℕ) : ℝ :=
  2 * scaledNetRadius R (D * (n + 1))

lemma mul_pow_linearNetPairRadius_le_one
    {M R : ℝ} (hM : 1 ≤ M) (hR : 0 < R) {D : ℕ}
    (hscaleR : 2 * R ≤ (4 : ℝ) ^ D)
    (hscaleM : M ≤ (4 : ℝ) ^ D) (n : ℕ) :
    M ^ n * linearNetPairRadius R D n ≤ 1 := by
  let Q : ℝ := (4 : ℝ) ^ D
  have hQ : 0 < Q := by positivity
  have hR_nonneg : 0 ≤ 2 * R := by positivity
  have hM_nonneg : 0 ≤ M := zero_le_one.trans hM
  have hRQ : 0 ≤ 2 * R / Q := div_nonneg hR_nonneg hQ.le
  have hRQ_one : 2 * R / Q ≤ 1 := (div_le_one hQ).2 hscaleR
  have hMQ : 0 ≤ M / Q := div_nonneg hM_nonneg hQ.le
  have hMQ_one : M / Q ≤ 1 := (div_le_one hQ).2 hscaleM
  have heq : M ^ n * linearNetPairRadius R D n =
      (2 * R / Q) * (M / Q) ^ n := by
    dsimp [linearNetPairRadius, scaledNetRadius, Q]
    rw [pow_mul, pow_succ]
    rw [div_pow]
    field_simp
  rw [heq]
  calc
    (2 * R / Q) * (M / Q) ^ n ≤ 1 * 1 ^ n := by gcongr
    _ = 1 := by simp

lemma linearNetPairRadius_secant_budget
    {M R a : ℝ} (hM : 1 ≤ M) (hR : 0 < R) {D : ℕ}
    (hscaleConst : 4 * R * M ^ 2 ≤ (4 : ℝ) ^ D)
    (hscaleRate : 4 * M ^ 2 * Real.exp (-a) ≤ (4 : ℝ) ^ D)
    (n : ℕ) :
    n * (M * (M ^ n * linearNetPairRadius R D n)) *
        (2 * M) ^ (n + 1) ≤ Real.exp (a * n) := by
  let Q : ℝ := (4 : ℝ) ^ D
  have hQ : 0 < Q := by positivity
  have hM_nonneg : 0 ≤ M := zero_le_one.trans hM
  have hradius_nonneg (k : ℕ) : 0 ≤ linearNetPairRadius R D k := by
    exact mul_nonneg (by norm_num) (scaledNetRadius_pos hR _).le
  have hn_two : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.le_of_lt n.lt_two_pow_self)
  have hcoef : 4 * R * M ^ 2 / Q ≤ 1 :=
    (div_le_one hQ).2 hscaleConst
  have hbase : 4 * M ^ 2 / Q ≤ Real.exp a := by
    apply (div_le_iff₀ hQ).2
    have hmul := mul_le_mul_of_nonneg_right hscaleRate (Real.exp_pos a).le
    calc
      4 * M ^ 2 ≤ (4 * M ^ 2 * Real.exp (-a)) * Real.exp a := by
        rw [mul_assoc, ← Real.exp_add]
        norm_num
      _ ≤ Q * Real.exp a := by simpa [Q] using hmul
      _ = Real.exp a * Q := by ring
  have hrearrange :
      (2 : ℝ) ^ n * (M * (M ^ n * linearNetPairRadius R D n)) *
          (2 * M) ^ (n + 1) =
        (4 * R * M ^ 2 / Q) * (4 * M ^ 2 / Q) ^ n := by
    have hsq (z : ℝ) : (z ^ 2) ^ n = z ^ n * z ^ n := by
      rw [← pow_mul]
      rw [show 2 * n = n + n by omega, pow_add]
    have hfour : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
      calc
        (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by norm_num
        _ = (2 : ℝ) ^ n * (2 : ℝ) ^ n := hsq 2
    dsimp [linearNetPairRadius, scaledNetRadius, Q]
    rw [pow_mul, pow_succ]
    simp only [div_pow]
    field_simp
    rw [pow_succ, mul_pow, mul_pow, hsq, hfour]
    ring
  calc
    (n : ℝ) * (M * (M ^ n * linearNetPairRadius R D n)) *
          (2 * M) ^ (n + 1) ≤
        (2 : ℝ) ^ n * (M * (M ^ n * linearNetPairRadius R D n)) *
          (2 * M) ^ (n + 1) := by
      have hfactor : 0 ≤ M * (M ^ n * linearNetPairRadius R D n) := by
        exact mul_nonneg hM_nonneg
          (mul_nonneg (pow_nonneg hM_nonneg n) (hradius_nonneg n))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hn_two hfactor)
        (pow_nonneg (mul_nonneg (by norm_num) hM_nonneg) _)
    _ = (4 * R * M ^ 2 / Q) * (4 * M ^ 2 / Q) ^ n := hrearrange
    _ ≤ 1 * (Real.exp a) ^ n := by gcongr
    _ = Real.exp (a * n) := by
      rw [← Real.exp_nat_mul]
      ring_nf

end Submission.Helpers
