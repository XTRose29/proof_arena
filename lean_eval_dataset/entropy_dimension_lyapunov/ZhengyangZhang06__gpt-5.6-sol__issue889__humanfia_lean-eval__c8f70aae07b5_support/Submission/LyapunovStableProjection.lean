import Submission.PlaneStableApproximation
import Submission.CenteredLinearControl
import Mathlib.MeasureTheory.Function.FactorsThrough

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology

noncomputable def stableApproxProjection
    (T : EucPlane → EucPlane) (n : ℕ) (x : EucPlane) :
    EucPlane →L[ℝ] EucPlane :=
  planeMinProjection (fderiv ℝ (T^[n]) x)

noncomputable def stableAlgebraicApproxProjection
    (T : EucPlane → EucPlane) (n : ℕ) (x : EucPlane) :
    EucPlane →L[ℝ] EucPlane :=
  planeStableApproximation (fderiv ℝ (T^[n]) x)

noncomputable def stableProjection
    (T : EucPlane → EucPlane) (x : EucPlane) :
    EucPlane →L[ℝ] EucPlane :=
  limUnder atTop (fun n => stableAlgebraicApproxProjection T n x)

lemma continuous_stableAlgebraicApproxProjection
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (n : ℕ) :
    Continuous (stableAlgebraicApproxProjection T n) := by
  let A : EucPlane → EucPlane →L[ℝ] EucPlane := fun x =>
    fderiv ℝ (T^[n]) x
  have hA : Continuous A :=
    (contDiff_iterate T hT_smooth n).continuous_fderiv (by norm_num)
  have hA_ne : ∀ x, ‖A x‖ ^ 2 ≠ 0 := by
    intro x
    exact pow_ne_zero 2 (norm_fderiv_iterate_pos T T_inv hT_smooth
      hT_inv_smooth hT_left hT_right n x).ne'
  have hscalar : Continuous fun x => (‖A x‖ ^ 2)⁻¹ :=
    (hA.norm.pow 2).inv₀ hA_ne
  have hgram : Continuous fun x => (A x).adjoint ∘L A x :=
    (ContinuousLinearMap.adjoint.continuous.comp hA).clm_comp hA
  change Continuous fun x => ContinuousLinearMap.id ℝ EucPlane -
    (‖A x‖ ^ 2)⁻¹ • ((A x).adjoint ∘L A x)
  exact continuous_const.sub (hscalar.smul hgram)

set_option synthInstance.maxHeartbeats 100000 in
lemma stronglyMeasurable_stableProjection
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) :
    StronglyMeasurable (stableProjection T) := by
  exact MeasureTheory.StronglyMeasurable.limUnder fun n =>
    (continuous_stableAlgebraicApproxProjection
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right n).stronglyMeasurable

theorem exists_stableProjection_limit_of_lyapunov_limits
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hxK : x ∈ K)
    {lam1 lam2 eta : ℝ} (heta : 0 < eta)
    (hgap : 2 * eta < lam1 - lam2)
    (hforward : Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n)
      atTop (nhds lam1))
    (hinverse : Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n)
      atTop (nhds (-lam2))) :
    ∃ Q : EucPlane →L[ℝ] EucPlane, ∃ n0 : ℕ,
      Tendsto (fun n => stableApproxProjection T n x) atTop (nhds Q) ∧
        ∀ k, ‖stableApproxProjection T (k + n0) x - Q‖ ≤
          ((2 * Real.sqrt 2 *
              ((compact_fderiv_bound T_inv hT_inv_smooth hK_compact).choose) *
                Real.exp (lam2 + eta)) *
              Real.exp (-(lam1 - lam2 - 2 * eta) * n0)) *
            Real.exp (-(lam1 - lam2 - 2 * eta)) ^ k /
              (1 - Real.exp (-(lam1 - lam2 - 2 * eta))) := by
  let D := (compact_fderiv_bound T_inv hT_inv_smooth hK_compact).choose
  have hD := (compact_fderiv_bound T_inv hT_inv_smooth hK_compact).choose_spec
  have hD_one : 1 ≤ D := hD.1
  have hD_bound : ∀ z ∈ K, ‖fderiv ℝ T_inv z‖ ≤ D := hD.2
  have hnorm_lower : ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam1 - eta) * n) ≤ ‖fderiv ℝ (T^[n]) x‖ :=
    eventually_exp_sub_le_of_tendsto_log_div
      (fun n : ℕ => n) tendsto_id
      (fun n => norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x)
      heta hforward
  have hinverse_lower : ∀ᶠ n : ℕ in atTop,
      Real.exp ((-lam2 - eta) * n) ≤
        ‖(fderiv ℝ (T^[n]) x).inverse‖ :=
    eventually_exp_sub_le_of_tendsto_log_div
      (fun n : ℕ => n) tendsto_id
      (fun n => by
        rw [fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right]
        exact norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
          hT_right hT_left n (T^[n] x))
      heta hinverse
  have hinverse_lower_succ : ∀ᶠ n : ℕ in atTop,
      Real.exp ((-lam2 - eta) * (n + 1)) ≤
        ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ := by
    simpa using (tendsto_add_atTop_nat 1).eventually hinverse_lower
  let gamma := lam1 - lam2 - 2 * eta
  let C₀ := 2 * Real.sqrt 2 * D * Real.exp (lam2 + eta)
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hstep : ∀ᶠ n : ℕ in atTop,
      ‖stableApproxProjection T n x - stableApproxProjection T (n + 1) x‖ ≤
        C₀ * Real.exp (-gamma * n) := by
    filter_upwards [hnorm_lower, hinverse_lower_succ]
      with n hnorm hinverseNorm
    let A := fderiv ℝ (T^[n]) x
    let C := fderiv ℝ T (T^[n] x)
    let C_inv := fderiv ℝ T_inv (T (T^[n] x))
    have hx_iter : ∀ q : ℕ, T^[q] x ∈ K := by
      intro q
      rw [← image_iterate_eq_of_image_eq T hK_inv q]
      exact ⟨x, hxK, rfl⟩
    have hC_inv_bound : ‖C_inv‖ ≤ D := by
      dsimp [C_inv]
      apply hD_bound
      rw [← hK_inv]
      exact ⟨T^[n] x, hx_iter n, rfl⟩
    have hC_left : C_inv ∘L C = ContinuousLinearMap.id ℝ EucPlane := by
      have hC_inv_eq : C_inv = C.inverse := by
        dsimp [C_inv, C]
        symm
        simpa [Function.iterate_one] using
          (fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
            hT_left hT_right 1 (T^[n] x))
      rw [hC_inv_eq]
      simpa [C, Function.iterate_one] using
        (fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right 1 (T^[n] x))
    have hcomp : C ∘L A = fderiv ℝ (T^[n + 1]) x := by
      dsimp [C, A]
      simpa [Nat.add_comm] using
        (fderiv_iterate_add_eq T hT_smooth 1 n x).symm
    have hA_det : A.toLinearMap.det ≠ 0 := by
      dsimp [A]
      exact det_fderiv_iterate_ne_zero T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x
    have hnext_left : (fderiv ℝ (T^[n + 1]) x).inverse ∘L
        fderiv ℝ (T^[n + 1]) x = ContinuousLinearMap.id ℝ EucPlane :=
      fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right (n + 1) x
    have hnext_det :
        (fderiv ℝ (T^[n + 1]) x).toLinearMap.det ≠ 0 :=
      det_fderiv_iterate_ne_zero T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right (n + 1) x
    have hmin_next :
        ‖fderiv ℝ (T^[n + 1]) x
            (planeSingularBasis (fderiv ℝ (T^[n + 1]) x) 1)‖ ≤
          Real.exp ((lam2 + eta) * (n + 1)) := by
      rw [norm_minSingular_eq_one_div_norm_inverse
        (fderiv ℝ (T^[n + 1]) x)
        (fderiv ℝ (T^[n + 1]) x).inverse hnext_det hnext_left]
      calc
        1 / ‖(fderiv ℝ (T^[n + 1]) x).inverse‖ ≤
            1 / Real.exp ((-lam2 - eta) * (n + 1)) :=
          one_div_le_one_div_of_le (Real.exp_pos _) hinverseNorm
        _ = Real.exp ((lam2 + eta) * (n + 1)) := by
          rw [div_eq_mul_inv, one_mul, ← Real.exp_neg]
          congr 1
          ring_nf
    have hprojection :=
      norm_planeMinProjection_sub_comp_le_div_norm A C C_inv hA_det hC_left
    rw [hcomp] at hprojection
    change ‖stableApproxProjection T n x -
        stableApproxProjection T (n + 1) x‖ ≤ _
    calc
      ‖stableApproxProjection T n x -
          stableApproxProjection T (n + 1) x‖ ≤
          2 * Real.sqrt 2 *
            (‖C_inv‖ *
                ‖fderiv ℝ (T^[n + 1]) x
                  (planeSingularBasis (fderiv ℝ (T^[n + 1]) x) 1)‖ /
              ‖A‖) := by
        simpa [stableApproxProjection, A] using hprojection
      _ ≤ 2 * Real.sqrt 2 *
            (D * Real.exp ((lam2 + eta) * (n + 1)) /
              Real.exp ((lam1 - eta) * n)) := by
        gcongr
      _ = C₀ * Real.exp (-gamma * n) := by
        dsimp [C₀, gamma]
        rw [div_eq_mul_inv, ← Real.exp_neg]
        rw [show (lam2 + eta) * ((n : ℝ) + 1) =
            (lam2 + eta) + (lam2 + eta) * (n : ℝ) by ring]
        rw [Real.exp_add]
        calc
          2 * Real.sqrt 2 *
              (D * (Real.exp (lam2 + eta) *
                Real.exp ((lam2 + eta) * (n : ℝ))) *
                Real.exp (-((lam1 - eta) * (n : ℝ)))) =
              2 * Real.sqrt 2 * D * Real.exp (lam2 + eta) *
                (Real.exp ((lam2 + eta) * (n : ℝ)) *
                  Real.exp (-((lam1 - eta) * (n : ℝ)))) := by ring_nf
          _ = 2 * Real.sqrt 2 * D * Real.exp (lam2 + eta) *
              Real.exp (-(lam1 - lam2 - 2 * eta) * (n : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
  simpa [D, C₀, gamma] using
    exists_limit_of_projection_eventually_geometric_step
      (fun n => stableApproxProjection T n x) hgamma hstep

theorem tendsto_stableAlgebraicApproxProjection_of_lyapunov_limits
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K : Set EucPlane} (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    {x : EucPlane} (hxK : x ∈ K)
    {lam1 lam2 eta : ℝ} (heta : 0 < eta)
    (hgap : 2 * eta < lam1 - lam2)
    (hforward : Tendsto
      (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n)
      atTop (nhds lam1))
    (hinverse : Tendsto
      (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n)
      atTop (nhds (-lam2))) :
    Tendsto (fun n => stableAlgebraicApproxProjection T n x)
        atTop (nhds (stableProjection T x)) ∧
      Tendsto (fun n => stableApproxProjection T n x)
        atTop (nhds (stableProjection T x)) := by
  obtain ⟨Q, _n0, hQ, _hQbound⟩ :=
    exists_stableProjection_limit_of_lyapunov_limits
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hK_compact hK_inv hxK heta hgap hforward hinverse
  have hnorm_lower : ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam1 - eta) * n) ≤ ‖fderiv ℝ (T^[n]) x‖ :=
    eventually_exp_sub_le_of_tendsto_log_div
      (fun n : ℕ => n) tendsto_id
      (fun n => norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x)
      heta hforward
  have hinverse_lower : ∀ᶠ n : ℕ in atTop,
      Real.exp ((-lam2 - eta) * n) ≤
        ‖(fderiv ℝ (T^[n]) x).inverse‖ :=
    eventually_exp_sub_le_of_tendsto_log_div
      (fun n : ℕ => n) tendsto_id
      (fun n => by
        rw [fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right]
        exact norm_fderiv_iterate_pos T_inv T hT_inv_smooth hT_smooth
          hT_right hT_left n (T^[n] x))
      heta hinverse
  let gamma := lam1 - lam2 - 2 * eta
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hdist_bound : ∀ᶠ n : ℕ in atTop,
      dist (stableApproxProjection T n x)
          (stableAlgebraicApproxProjection T n x) ≤
        Real.exp (-2 * gamma * n) := by
    filter_upwards [hnorm_lower, hinverse_lower]
      with n hnorm hinverseNorm
    let A := fderiv ℝ (T^[n]) x
    have hA_ne : A ≠ 0 := by
      apply norm_ne_zero_iff.mp
      exact (norm_fderiv_iterate_pos T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x).ne'
    have hA_det : A.toLinearMap.det ≠ 0 := by
      dsimp [A]
      exact det_fderiv_iterate_ne_zero T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x
    have hA_left : A.inverse ∘L A = ContinuousLinearMap.id ℝ EucPlane := by
      dsimp [A]
      exact fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x
    have hmin : ‖A (planeSingularBasis A 1)‖ ≤
        Real.exp ((lam2 + eta) * n) := by
      rw [norm_minSingular_eq_one_div_norm_inverse A A.inverse hA_det hA_left]
      calc
        1 / ‖A.inverse‖ ≤ 1 / Real.exp ((-lam2 - eta) * n) :=
          one_div_le_one_div_of_le (Real.exp_pos _) hinverseNorm
        _ = Real.exp ((lam2 + eta) * n) := by
          rw [div_eq_mul_inv, one_mul, ← Real.exp_neg]
          congr 1
          ring_nf
    have hratio :
        ‖A (planeSingularBasis A 1)‖ / ‖A‖ ≤
          Real.exp ((lam2 + eta) * n) /
            Real.exp ((lam1 - eta) * n) := by
      gcongr
    rw [dist_comm, dist_eq_norm]
    change ‖stableAlgebraicApproxProjection T n x -
      stableApproxProjection T n x‖ ≤ _
    rw [stableAlgebraicApproxProjection, stableApproxProjection,
      norm_planeStableApproximation_sub_minProjection A hA_ne]
    calc
      (‖A (planeSingularBasis A 1)‖ / ‖A‖) ^ 2 ≤
          (Real.exp ((lam2 + eta) * n) /
            Real.exp ((lam1 - eta) * n)) ^ 2 := by
        gcongr
      _ = Real.exp (-2 * gamma * n) := by
        dsimp [gamma]
        rw [div_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
          div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
        congr 1
        ring_nf
  have hupper : Tendsto (fun n : ℕ => Real.exp (-2 * gamma * n))
      atTop (nhds 0) := by
    have hr : Real.exp (-2 * gamma) < 1 :=
      (Real.exp_lt_one_iff).2 (by linarith)
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (Real.exp_nonneg (-2 * gamma)) hr
    convert hpow using 1
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdist : Tendsto
      (fun n => dist (stableApproxProjection T n x)
        (stableAlgebraicApproxProjection T n x))
      atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
      hdist_bound hupper
  have hAlgQ : Tendsto (fun n => stableAlgebraicApproxProjection T n x)
      atTop (nhds Q) := hQ.congr_dist hdist
  have hlim := tendsto_nhds_limUnder ⟨Q, hAlgQ⟩
  have hStable : Tendsto (fun n => stableAlgebraicApproxProjection T n x)
      atTop (nhds (stableProjection T x)) := by
    simpa [stableProjection] using hlim
  have hQeq : Q = stableProjection T x :=
    tendsto_nhds_unique hAlgQ hStable
  exact ⟨hStable, by simpa [hQeq] using hQ⟩

lemma stableProjection_idempotent_of_tendsto
    {T : EucPlane → EucPlane} {x : EucPlane}
    (hP : Tendsto (fun n => stableApproxProjection T n x)
      atTop (nhds (stableProjection T x))) :
    stableProjection T x ∘L stableProjection T x = stableProjection T x := by
  have hcomp : Tendsto
      (fun n => stableApproxProjection T n x ∘L
        stableApproxProjection T n x) atTop
      (nhds (stableProjection T x ∘L stableProjection T x)) := by
    apply (((continuous_fst.clm_comp continuous_snd).tendsto
      (stableProjection T x, stableProjection T x)).comp
        (hP.prodMk_nhds hP)).congr'
    filter_upwards [] with n
    rfl
  have hsame : Tendsto
      (fun n => stableApproxProjection T n x ∘L
        stableApproxProjection T n x) atTop
      (nhds (stableProjection T x)) := by
    apply hP.congr'
    filter_upwards [] with n
    exact (planeMinProjection_idempotent
      (fderiv ℝ (T^[n]) x)).symm
  exact tendsto_nhds_unique hcomp hsame

lemma stableProjection_adjoint_of_tendsto
    {T : EucPlane → EucPlane} {x : EucPlane}
    (hP : Tendsto (fun n => stableApproxProjection T n x)
      atTop (nhds (stableProjection T x))) :
    (stableProjection T x).adjoint = stableProjection T x := by
  have hadjoint : Tendsto
      (fun n => (stableApproxProjection T n x).adjoint) atTop
      (nhds (stableProjection T x).adjoint) :=
    (ContinuousLinearMap.adjoint.continuous.tendsto
      (stableProjection T x)).comp hP
  have hsame : Tendsto
      (fun n => (stableApproxProjection T n x).adjoint) atTop
      (nhds (stableProjection T x)) := by
    apply hP.congr'
    filter_upwards [] with n
    exact (planeMinProjection_adjoint
      (fderiv ℝ (T^[n]) x)).symm
  exact tendsto_nhds_unique hadjoint hsame

lemma norm_stableProjection_of_tendsto
    {T : EucPlane → EucPlane} {x : EucPlane}
    (hP : Tendsto (fun n => stableApproxProjection T n x)
      atTop (nhds (stableProjection T x))) :
    ‖stableProjection T x‖ = 1 := by
  have hone : Tendsto (fun n => ‖stableApproxProjection T n x‖)
      atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    exact (norm_planeMinProjection (fderiv ℝ (T^[n]) x)).symm
  exact tendsto_nhds_unique hP.norm hone

lemma stableProjection_comp_quarterTurn_of_tendsto
    {T : EucPlane → EucPlane} {x : EucPlane}
    (hP : Tendsto (fun n => stableApproxProjection T n x)
      atTop (nhds (stableProjection T x))) :
    stableProjection T x ∘L
        planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap =
      planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (ContinuousLinearMap.id ℝ EucPlane - stableProjection T x) := by
  let J := planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap
  have hleft : Tendsto
      (fun n => stableApproxProjection T n x ∘L J) atTop
      (nhds (stableProjection T x ∘L J)) := by
    apply (((continuous_id.clm_comp continuous_const).tendsto
      (stableProjection T x)).comp hP).congr'
    filter_upwards [] with n
    rfl
  have hright : Tendsto
      (fun n => J ∘L
        (ContinuousLinearMap.id ℝ EucPlane - stableApproxProjection T n x))
      atTop
      (nhds (J ∘L
        (ContinuousLinearMap.id ℝ EucPlane - stableProjection T x))) := by
    apply (((continuous_const.clm_comp
      (continuous_const.sub continuous_id)).tendsto
        (stableProjection T x)).comp hP).congr'
    filter_upwards [] with n
    rfl
  have hright' : Tendsto
      (fun n => stableApproxProjection T n x ∘L J) atTop
      (nhds (J ∘L
        (ContinuousLinearMap.id ℝ EucPlane - stableProjection T x))) := by
    apply hright.congr'
    filter_upwards [] with n
    exact (planeMinProjection_comp_quarterTurn
      (fderiv ℝ (T^[n]) x)).symm
  simpa [J] using tendsto_nhds_unique hleft hright'

end Submission.Helpers
