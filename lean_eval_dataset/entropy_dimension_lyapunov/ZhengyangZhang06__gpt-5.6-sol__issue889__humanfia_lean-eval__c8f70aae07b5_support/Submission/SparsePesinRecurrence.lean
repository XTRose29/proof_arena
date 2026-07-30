import Submission.SparseExponentialComparison
import Submission.SparsePesinSegments

namespace Submission.Helpers

open LeanEval.Dynamics

lemma iterate_sub_apply_iterate
    (F : EucPlane → EucPlane) {p q : ℕ} (hpq : p ≤ q) (z : EucPlane) :
    F^[q - p] (F^[p] z) = F^[q] z := by
  rw [← Function.iterate_add_apply]
  congr 2
  omega

/-- At selected full-Pesin nodes, sufficiently accurate secant products on
the adjacent gaps give the tridiagonal recurrence used by the exponential
path comparison. -/
lemma sparse_pesin_neighbor_recurrence
    {N : ℕ}
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {carrier : Set EucPlane} (hcarrier : T '' carrier = carrier)
    (hsource : ∀ z ∈ carrier, SourceSplittingData T T_inv z)
    (hcov : ∀ z ∈ carrier,
      lyapunovStableComponent T T_inv (T z) ∘L fderiv ℝ T z =
          fderiv ℝ T z ∘L lyapunovStableComponent T T_inv z ∧
      lyapunovUnstableComponent T T_inv (T z) ∘L fderiv ℝ T z =
          fderiv ℝ T z ∘L lyapunovUnstableComponent T T_inv z)
    {lam1 lam2 eta : ℝ} {C : ℕ}
    (t : Fin (N + 1) → ℕ)
    (ht : ∀ i j, i.val < j.val → t i < t j)
    (edgeError : Fin N → ℝ)
    (x y : EucPlane)
    (hxcarrier : x ∈ carrier)
    (hxG : ∀ i, T^[t i] x ∈
      pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
    (herror : ∀ k : Fin N,
      ‖clmPrefixProduct
            (orbitSecantStep T (T^[t k.castSucc] x) (T^[t k.castSucc] y))
            (t k.succ - t k.castSucc) -
          fderiv ℝ (T^[t k.succ - t k.castSucc])
            (T^[t k.castSucc] x)‖ ≤ edgeError k)
    (hstableError : ∀ k : Fin N,
      edgeError k ≤ Real.exp ((lam2 + 6 * eta) *
        ((t k.succ - t k.castSucc : ℕ) : ℝ)))
    (hunstableError : ∀ k : Fin N,
      (C : ℝ) * Real.exp ((-lam1 + 6 * eta) *
          ((t k.succ - t k.castSucc : ℕ) : ℝ)) * edgeError k ≤ 1 / 2) :
    ∀ i : Fin (N + 1), 0 < i.val → i.val < N →
      ‖T^[t i] y - T^[t i] x‖ ≤
        (4 * C) * Real.exp ((lam2 + 6 * eta) *
            ((t i - t (pathPrev i) : ℕ) : ℝ)) *
          ‖T^[t (pathPrev i)] y - T^[t (pathPrev i)] x‖ +
        (4 * C) * Real.exp ((-lam1 + 6 * eta) *
            ((t (pathNext i) - t i : ℕ) : ℝ)) *
          ‖T^[t (pathNext i)] y - T^[t (pathNext i)] x‖ := by
  intro i hi0 hiN
  let ip := pathPrev i
  let inx := pathNext i
  let kp : Fin N := ⟨i.val - 1, by omega⟩
  let kn : Fin N := ⟨i.val, hiN⟩
  have hkp_cast : kp.castSucc = ip := by
    apply Fin.ext
    rfl
  have hkp_succ : kp.succ = i := by
    apply Fin.ext
    dsimp [kp]
    omega
  have hkn_cast : kn.castSucc = i := by
    apply Fin.ext
    rfl
  have hkn_succ : kn.succ = inx := by
    apply Fin.ext
    simp [kn, inx, pathNext, min_eq_left (Nat.succ_le_iff.mpr hiN)]
  have hp_lt : t ip < t i := ht ip i (by
    dsimp [ip, pathPrev]
    omega)
  have hi_lt : t i < t inx := ht i inx (by
    dsimp [inx]
    simp [pathNext, min_eq_left (Nat.succ_le_iff.mpr hiN)])
  have horbitcarrier (m : ℕ) : T^[m] x ∈ carrier := by
    rw [← image_iterate_eq_of_image_eq T hcarrier m]
    exact ⟨x, hxcarrier, rfl⟩
  have herrp := herror kp
  rw [hkp_cast, hkp_succ] at herrp
  have herrn := herror kn
  rw [hkn_cast, hkn_succ] at herrn
  have hstableErrp := hstableError kp
  rw [hkp_cast, hkp_succ] at hstableErrp
  have hunstableErrn := hunstableError kn
  rw [hkn_cast, hkn_succ] at hunstableErrn
  have hstable0 := norm_stable_orbit_displacement_le_of_secant_error
    T T_inv hT_smooth hcarrier (fun z hz => (hcov z hz).1)
      (lam1 := lam1) (lam2 := lam2) (eta := eta)
      (x := T^[t ip] x) (y := T^[t ip] y) (n := t i - t ip)
      (horbitcarrier (t ip)) (hxG ip) (by
        simpa [iterate_sub_apply_iterate T hp_lt.le] using hxG i) herrp
  have hstable :
      ‖lyapunovStableComponent T T_inv (T^[t i] x)
          (T^[t i] y - T^[t i] x)‖ ≤
        (2 * C) * Real.exp ((lam2 + 6 * eta) *
            ((t i - t ip : ℕ) : ℝ)) *
          ‖T^[t ip] y - T^[t ip] x‖ := by
    rw [iterate_sub_apply_iterate T hp_lt.le,
      iterate_sub_apply_iterate T hp_lt.le] at hstable0
    apply hstable0.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      (C : ℝ) * Real.exp ((lam2 + 6 * eta) *
              ((t i - t ip : ℕ) : ℝ)) + C * edgeError kp ≤
          C * Real.exp ((lam2 + 6 * eta) *
              ((t i - t ip : ℕ) : ℝ)) +
            C * Real.exp ((lam2 + 6 * eta) *
              ((t i - t ip : ℕ) : ℝ)) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hstableErrp (Nat.cast_nonneg C))
      _ = (2 * C) * Real.exp ((lam2 + 6 * eta) *
            ((t i - t ip : ℕ) : ℝ)) := by ring
  have hunstable := norm_unstable_orbit_displacement_le_of_secant_error
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right hcarrier
      (fun z hz => (hcov z hz).2)
      (lam1 := lam1) (lam2 := lam2) (eta := eta)
      (x := T^[t i] x) (y := T^[t i] y) (n := t inx - t i)
      (horbitcarrier (t i)) (by
        simpa [iterate_sub_apply_iterate T hi_lt.le] using hxG inx) herrn
  rw [iterate_sub_apply_iterate T hi_lt.le,
    iterate_sub_apply_iterate T hi_lt.le] at hunstable
  have hnodecarrier : T^[t i] x ∈ carrier := horbitcarrier (t i)
  have hsum := lyapunovComponents_add T T_inv
    (hsource (T^[t i] x) hnodecarrier)
  have hdecomp :
      lyapunovStableComponent T T_inv (T^[t i] x)
          (T^[t i] y - T^[t i] x) +
        lyapunovUnstableComponent T T_inv (T^[t i] x)
          (T^[t i] y - T^[t i] x) =
        T^[t i] y - T^[t i] x := by
    simpa only [add_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun A : EucPlane →L[ℝ] EucPlane =>
        A (T^[t i] y - T^[t i] x)) hsum
  have hmain :
      ‖T^[t i] y - T^[t i] x‖ ≤
        (2 * C) * Real.exp ((lam2 + 6 * eta) *
            ((t i - t ip : ℕ) : ℝ)) *
          ‖T^[t ip] y - T^[t ip] x‖ +
        C * Real.exp ((-lam1 + 6 * eta) *
            ((t inx - t i : ℕ) : ℝ)) *
          (‖T^[t inx] y - T^[t inx] x‖ +
            edgeError kn * ‖T^[t i] y - T^[t i] x‖) := by
    calc
      ‖T^[t i] y - T^[t i] x‖ =
          ‖lyapunovStableComponent T T_inv (T^[t i] x)
              (T^[t i] y - T^[t i] x) +
            lyapunovUnstableComponent T T_inv (T^[t i] x)
              (T^[t i] y - T^[t i] x)‖ := congrArg norm hdecomp.symm
      _ ≤ ‖lyapunovStableComponent T T_inv (T^[t i] x)
              (T^[t i] y - T^[t i] x)‖ +
            ‖lyapunovUnstableComponent T T_inv (T^[t i] x)
              (T^[t i] y - T^[t i] x)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hstable hunstable
  have habsorb :
      ((C : ℝ) * Real.exp ((-lam1 + 6 * eta) *
          ((t inx - t i : ℕ) : ℝ)) * edgeError kn) *
          ‖T^[t i] y - T^[t i] x‖ ≤
        (1 / 2) * ‖T^[t i] y - T^[t i] x‖ :=
    mul_le_mul_of_nonneg_right hunstableErrn (norm_nonneg _)
  have hleft_nonneg : 0 ≤
      (C : ℝ) * Real.exp ((lam2 + 6 * eta) *
          ((t i - t ip : ℕ) : ℝ)) *
        ‖T^[t ip] y - T^[t ip] x‖ := by positivity
  have hright_nonneg : 0 ≤
      (C : ℝ) * Real.exp ((-lam1 + 6 * eta) *
          ((t inx - t i : ℕ) : ℝ)) *
        ‖T^[t inx] y - T^[t inx] x‖ := by positivity
  dsimp [ip, inx] at hmain habsorb hleft_nonneg hright_nonneg ⊢
  nlinarith

end Submission.Helpers
