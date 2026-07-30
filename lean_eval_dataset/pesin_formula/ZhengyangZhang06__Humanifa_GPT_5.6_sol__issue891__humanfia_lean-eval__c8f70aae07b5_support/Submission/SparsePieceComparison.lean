import Submission.SparsePesinRecurrence

namespace Submission.Helpers

open LeanEval.Dynamics

/-- Compose the Pesin neighbor recurrence with the finite exponential path
comparison.  This is the analytic core used for each sparse pattern piece. -/
lemma sparse_pesin_path_displacement_le
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
          ((t k.succ - t k.castSucc : ℕ) : ℝ)) * edgeError k ≤ 1 / 2)
    {q delta : ℝ}
    (hq : 0 < q) (hdelta : 0 ≤ delta)
    (hAq : (4 * C : ℝ) / q ≤ 1 / 4)
    (hcross : ∀ k : Fin N,
      (4 * C : ℝ) * q *
          Real.exp (((lam2 + 6 * eta) + (-lam1 + 6 * eta)) *
            ((t k.succ - t k.castSucc : ℕ) : ℝ)) ≤ 1 / 4)
    (hboundary_left :
      ‖T^[t 0] y - T^[t 0] x‖ ≤ delta)
    (hboundary_right :
      ‖T^[t (Fin.last N)] y - T^[t (Fin.last N)] x‖ ≤ delta) :
    ∀ i : Fin (N + 1),
      ‖T^[t i] y - T^[t i] x‖ ≤
        delta *
          (q ^ i.val *
              Real.exp ((lam2 + 6 * eta) * ((t i : ℝ) - t 0)) +
            q ^ (N - i.val) *
              Real.exp ((-lam1 + 6 * eta) *
                ((t (Fin.last N) : ℝ) - t i))) := by
  let d : Fin (N + 1) → ℝ := fun i => ‖T^[t i] y - T^[t i] x‖
  apply finite_exponential_path_comparison_nat d t
    (fun i => norm_nonneg _) (by positivity) hq hdelta ht hAq
  · intro i hi0 hiN
    let k : Fin N := ⟨i.val - 1, by omega⟩
    have hk_cast : k.castSucc = pathPrev i := by
      apply Fin.ext
      rfl
    have hk_succ : k.succ = i := by
      apply Fin.ext
      dsimp [k]
      omega
    simpa [hk_cast, hk_succ] using hcross k
  · intro i hi0 hiN
    let k : Fin N := ⟨i.val, hiN⟩
    have hk_cast : k.castSucc = i := by
      apply Fin.ext
      rfl
    have hk_succ : k.succ = pathNext i := by
      apply Fin.ext
      simp [k, pathNext, min_eq_left (Nat.succ_le_iff.mpr hiN)]
    simpa [hk_cast, hk_succ] using hcross k
  · exact hboundary_left
  · exact hboundary_right
  · exact sparse_pesin_neighbor_recurrence
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hcarrier hsource hcov t ht edgeError x y hxcarrier hxG
        herror hstableError hunstableError

end Submission.Helpers
