import Submission.CocycleCheapFrequency
import Submission.FiniteIterateDistortion

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

theorem exists_ae_nonlinear_orbit_growth
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam rho : ℝ}
    (hlam : lam = ∫ x, lyapunovUpperAt T x ∂mu) (hrho : 0 < rho) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ᵐ x ∂mu,
      ∃ G : ℝ, 0 ≤ G ∧ ∀ m : ℕ, ∀ y ∈ K,
        dist x y * Real.exp (max 0 ((lam + rho) * m) + G) ≤ delta →
          dist (T^[m] x) (T^[m] y) ≤
            Real.exp ((lam + rho) * m + G) * dist x y := by
  let e : ℝ := rho / 4
  have he : 0 < e := div_pos hrho (by norm_num)
  obtain ⟨C₀, hC₀_one, hC₀⟩ :=
    compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨D₀, hD₀_one, hD₀⟩ :=
    compact_fderiv_bound T_inv hT_inv_smooth hK_compact
  let B : ℝ := max (Real.log C₀) (Real.log D₀)
  have hB : 0 ≤ B :=
    (Real.log_nonneg hC₀_one).trans (le_max_left _ _)
  have hC₀B : Real.log C₀ ≤ B := le_max_left _ _
  have hD₀B : Real.log D₀ ≤ B := le_max_right _ _
  let f := supportedLogNormFderiv T K
  have hf : ∀ n, Measurable (f n) := fun n =>
    measurable_supportedLogNormFderiv T hT_smooth
      hK_compact.isClosed.measurableSet n
  have hlogconv :=
    ae_tendsto_log_norm_fderiv_iterate_div_lyapunovUpperAt
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
        hK_compact hK_inv mu hmu_supp hT hErg
  have hlyap := lyapunovUpperAt_ae_eq_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
      hK_compact hK_inv mu hmu_supp hErg
  have hfconv : ∀ᵐ x ∂mu, Tendsto (fun n : ℕ => f n x / n)
      atTop (nhds lam) := by
    filter_upwards [hlogconv, hlyap, mem_ae_iff.mpr hmu_supp]
      with x hxconv hxlyap hxK
    simpa [f, supportedLogNormFderiv, hxK, hxlyap, ← hlam] using hxconv
  let a : ℝ := lam + e
  let C : ℝ := B + |a|
  have hC : 0 ≤ C := add_nonneg hB (abs_nonneg a)
  obtain ⟨N, hN_pos, hbad⟩ := exists_ae_eventually_badCount_mul_lt
    mu T hT hErg f hf
      (rate := lam) (a := a) (C := C) (eta := e)
      (by dsimp [a]; linarith) he hfconv
  obtain ⟨delta, hdelta, hdist⟩ :=
    exists_delta_dist_iterate_le_exp_eta_mul_norm
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv N he
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [hbad, mem_ae_iff.mpr hmu_supp] with x hxbad hxK
  obtain ⟨M, hM⟩ := eventually_atTop.1 hxbad
  let G : ℝ := C * N + C * M
  have hG : 0 ≤ G := by
    dsimp [G]
    positivity
  refine ⟨G, hG, ?_⟩
  intro m y hyK hsmall
  let d : ℕ → ℝ := fun k => dist (T^[k] x) (T^[k] y)
  let cheap : ℕ → Prop := fun k => T^[k] x ∈ cocycleCheapSet f a N
  have horbitK (z : EucPlane) (hz : z ∈ K) (k : ℕ) : T^[k] z ∈ K := by
    rw [← image_iterate_eq_of_image_eq T hK_inv k]
    exact ⟨z, hz, rfl⟩
  have hd : ∀ k, 0 ≤ d k := fun k => dist_nonneg
  have hcheap : ∀ k, d k ≤ delta → cheap k →
      ∃ n ∈ Finset.Icc 1 N,
        d (k + n) ≤ Real.exp ((a + e) * n) * d k := by
    intro k hdk hkcheap
    obtain ⟨n, hnmem⟩ := Set.mem_iUnion.mp hkcheap
    obtain ⟨hnIcc, hnlog⟩ := Set.mem_iUnion.mp hnmem
    have hn_pos : 0 < n := (Finset.mem_Icc.mp hnIcc).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
    have hxk : T^[k] x ∈ K := horbitK x hxK k
    have hyk : T^[k] y ∈ K := horbitK y hyK k
    have hnormlog : Real.log ‖fderiv ℝ (T^[n]) (T^[k] x)‖ ≤ a * n := by
      simpa [f, supportedLogNormFderiv, hxk] using hnlog
    have hnorm : ‖fderiv ℝ (T^[n]) (T^[k] x)‖ ≤ Real.exp (a * n) :=
      Real.le_exp_of_log_le hnormlog
    refine ⟨n, hnIcc, ?_⟩
    calc
      d (k + n) = dist (T^[n] (T^[k] x)) (T^[n] (T^[k] y)) := by
        have hxadd : T^[k + n] x = T^[n] (T^[k] x) := by
          rw [Nat.add_comm k n]
          exact Function.iterate_add_apply T n k x
        have hyadd : T^[k + n] y = T^[n] (T^[k] y) := by
          rw [Nat.add_comm k n]
          exact Function.iterate_add_apply T n k y
        simp only [d, hxadd, hyadd]
      _ ≤ Real.exp (e * n) * ‖fderiv ℝ (T^[n]) (T^[k] x)‖ *
          dist (T^[k] x) (T^[k] y) :=
        hdist n hn_pos hnN (T^[k] x) hxk (T^[k] y) hyk hdk
      _ ≤ Real.exp (e * n) * Real.exp (a * n) * d k := by
        dsimp [d]
        gcongr
      _ = Real.exp ((a + e) * n) * d k := by
        rw [← Real.exp_add]
        congr 2
        ring_nf
  have hshort : ∀ k n, 0 < n → n ≤ N → d k ≤ delta →
      d (k + n) ≤ Real.exp ((B + e) * n) * d k := by
    intro k n hn_pos hnN hdk
    have hxk : T^[k] x ∈ K := horbitK x hxK k
    have hyk : T^[k] y ∈ K := horbitK y hyK k
    have hlog : Real.log ‖fderiv ℝ (T^[n]) (T^[k] x)‖ ≤ B * n := by
      have habs := abs_supportedLogNormFderiv_le
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right hK_inv
          hC₀_one hD₀_one hC₀ hD₀ hC₀B hD₀B n (T^[k] x)
      have hle := (le_abs_self (f n (T^[k] x))).trans habs
      simpa [f, supportedLogNormFderiv, hxk] using hle
    have hnorm : ‖fderiv ℝ (T^[n]) (T^[k] x)‖ ≤ Real.exp (B * n) :=
      Real.le_exp_of_log_le hlog
    calc
      d (k + n) = dist (T^[n] (T^[k] x)) (T^[n] (T^[k] y)) := by
        have hxadd : T^[k + n] x = T^[n] (T^[k] x) := by
          rw [Nat.add_comm k n]
          exact Function.iterate_add_apply T n k x
        have hyadd : T^[k + n] y = T^[n] (T^[k] y) := by
          rw [Nat.add_comm k n]
          exact Function.iterate_add_apply T n k y
        simp only [d, hxadd, hyadd]
      _ ≤ Real.exp (e * n) * ‖fderiv ℝ (T^[n]) (T^[k] x)‖ *
          dist (T^[k] x) (T^[k] y) :=
        hdist n hn_pos hnN (T^[k] x) hxk (T^[k] y) hyk hdk
      _ ≤ Real.exp (e * n) * Real.exp (B * n) * d k := by
        dsimp [d]
        gcongr
      _ = Real.exp ((B + e) * n) * d k := by
        rw [← Real.exp_add]
        congr 2
        ring_nf
  have hbad_all : ∀ j : ℕ,
      C * badCount cheap 0 j ≤ e * j + C * M := by
    intro j
    by_cases hMj : M ≤ j
    · have hj := hM j hMj
      exact hj.le.trans (le_add_of_nonneg_right
        (mul_nonneg hC (Nat.cast_nonneg M)))
    · have hjM : j ≤ M := Nat.le_of_lt (lt_of_not_ge hMj)
      have hcount := badCount_le_natCast cheap 0 j
      calc
        C * badCount cheap 0 j ≤ C * j :=
          mul_le_mul_of_nonneg_left hcount hC
        _ ≤ C * M := by
          gcongr
        _ ≤ e * j + C * M :=
          le_add_of_nonneg_left (mul_nonneg he.le (Nat.cast_nonneg j))
  have hsmall_prefix : ∀ j, j ≤ m →
      d 0 * Real.exp
        ((a + e) * j + C * N + C * badCount cheap 0 j) ≤ delta := by
    intro j hjm
    have hjreal : (j : ℝ) ≤ m := by exact_mod_cast hjm
    have hexponent :
        (a + e) * j + C * N + C * badCount cheap 0 j ≤
          max 0 ((lam + rho) * m) + G := by
      have hbadj := hbad_all j
      dsimp [a, e, G] at *
      by_cases hrate : 0 ≤ lam + rho
      · rw [max_eq_right (mul_nonneg hrate (Nat.cast_nonneg m))]
        nlinarith [mul_le_mul_of_nonneg_left hjreal hrate]
      · rw [max_eq_left (mul_nonpos_of_nonpos_of_nonneg
          (le_of_not_ge hrate) (Nat.cast_nonneg m))]
        nlinarith [mul_nonpos_of_nonpos_of_nonneg
          (le_of_not_ge hrate) (Nat.cast_nonneg j)]
    calc
      d 0 * Real.exp
          ((a + e) * j + C * N + C * badCount cheap 0 j) ≤
          d 0 * Real.exp (max 0 ((lam + rho) * m) + G) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (hd 0)
      _ = dist x y * Real.exp (max 0 ((lam + rho) * m) + G) := by
        simp [d]
      _ ≤ delta := hsmall
  have hstop := nonlinear_stopping_bound d cheap hd hB hN_pos
    hcheap hshort 0 m hsmall_prefix
  have hbadm := hbad_all m
  have hexponent :
      (a + e) * m + C * N + C * badCount cheap 0 m ≤
        (lam + rho) * m + G := by
    dsimp [a, e, G] at *
    nlinarith [mul_nonneg hrho.le (Nat.cast_nonneg m)]
  calc
    dist (T^[m] x) (T^[m] y) = d (0 + m) := by simp [d]
    _ ≤ Real.exp
        ((a + e) * m + C * N + C * badCount cheap 0 m) * d 0 := by
      simpa [C] using hstop
    _ ≤ Real.exp ((lam + rho) * m + G) * d 0 := by
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr hexponent) (hd 0)
    _ = Real.exp ((lam + rho) * m + G) * dist x y := by simp [d]

end Submission.Helpers
