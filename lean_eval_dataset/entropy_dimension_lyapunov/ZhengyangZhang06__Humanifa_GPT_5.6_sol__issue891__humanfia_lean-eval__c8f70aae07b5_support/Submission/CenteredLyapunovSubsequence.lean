import Submission.LyapunovTimeReversal
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory Topology

noncomputable def centeredFderiv
    (T T_inv : EucPlane → EucPlane) (m n : ℕ) (x : EucPlane) :
    EucPlane →L[ℝ] EucPlane :=
  fderiv ℝ (T^[n]) x ∘L (fderiv ℝ (T_inv^[m]) x).inverse

lemma centeredFderiv_eq_fderiv_iterate
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (m n : ℕ) (x : EucPlane) :
    centeredFderiv T T_inv m n x =
      fderiv ℝ (T^[m + n]) (T_inv^[m] x) := by
  rw [centeredFderiv]
  rw [fderiv_iterate_inverse T_inv T hT_inv_smooth hT_smooth
    hT_right hT_left]
  have hreturn : T^[m] (T_inv^[m] x) = x := (hT_right.iterate m) x
  calc
    fderiv ℝ (T^[n]) x ∘L fderiv ℝ (T^[m]) (T_inv^[m] x) =
        fderiv ℝ (T^[n]) (T^[m] (T_inv^[m] x)) ∘L
          fderiv ℝ (T^[m]) (T_inv^[m] x) := by rw [hreturn]
    _ = fderiv ℝ (T^[n + m]) (T_inv^[m] x) :=
      (fderiv_iterate_add_eq T hT_smooth n m (T_inv^[m] x)).symm
    _ = fderiv ℝ (T^[m + n]) (T_inv^[m] x) := by rw [Nat.add_comm]

lemma measurable_log_norm_centeredFderiv_div
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (m n : ℕ) :
    Measurable fun x => Real.log ‖centeredFderiv T T_inv m n x‖ / (m + n) := by
  rw [show (fun x => Real.log ‖centeredFderiv T T_inv m n x‖ / (m + n)) =
      fun x => Real.log ‖fderiv ℝ (T^[m + n]) (T_inv^[m] x)‖ / (m + n) by
    funext x
    rw [centeredFderiv_eq_fderiv_iterate T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right]]
  simpa [Function.comp_def, Nat.cast_add] using
    (measurable_log_norm_fderiv_iterate_div T hT_smooth (m + n)).comp
      (hT_inv_smooth.continuous.iterate m).measurable

theorem tendstoInMeasure_log_norm_centeredFderiv_div_integral
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (m n : ℕ → ℕ) (hsplit : ∀ L, m L + n L = L) :
    TendstoInMeasure mu
      (fun L x => Real.log ‖centeredFderiv T T_inv (m L) (n L) x‖ / L)
      atTop (fun _ => ∫ y, lyapunovUpperAt T y ∂mu) := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hconv := ae_tendsto_log_norm_fderiv_iterate_div_lyapunovUpperAt
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
      hK_compact hK_inv mu hmu_supp hT hErg
  have hexp := lyapunovUpperAt_ae_eq_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K
      hK_compact hK_inv mu hmu_supp hErg
  have hbase_ae : ∀ᵐ x ∂mu, Tendsto
      (fun L : ℕ => Real.log ‖fderiv ℝ (T^[L]) x‖ / L)
      atTop (nhds (∫ y, lyapunovUpperAt T y ∂mu)) := by
    filter_upwards [hconv, hexp] with x hxconv hxexp
    simpa [hxexp] using hxconv
  have hbase : TendstoInMeasure mu
      (fun L x => Real.log ‖fderiv ℝ (T^[L]) x‖ / L)
      atTop (fun _ => ∫ y, lyapunovUpperAt T y ∂mu) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro L
      exact (measurable_log_norm_fderiv_iterate_div T hT_smooth L).aestronglyMeasurable
    · exact hbase_ae
  rw [tendstoInMeasure_iff_dist] at hbase ⊢
  intro epsilon hepsilon
  have htend := hbase epsilon hepsilon
  convert htend using 1
  funext L
  let bad : Set EucPlane :=
    {z | epsilon ≤ dist
      (Real.log ‖fderiv ℝ (T^[L]) z‖ / L)
      (∫ y, lyapunovUpperAt T y ∂mu)}
  have hbad_measurable : MeasurableSet bad := by
    exact measurableSet_le measurable_const
      ((measurable_log_norm_fderiv_iterate_div T hT_smooth L).dist measurable_const)
  have hset :
      {x | epsilon ≤ dist
        (Real.log ‖centeredFderiv T T_inv (m L) (n L) x‖ / L)
        ((fun _ : EucPlane => ∫ y, lyapunovUpperAt T y ∂mu) x)} =
        T_inv^[m L] ⁻¹' bad := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [centeredFderiv_eq_fderiv_iterate T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right, hsplit L]
    rfl
  rw [hset, (hT_inv.iterate (m L)).measure_preimage hbad_measurable.nullMeasurableSet]

theorem exists_centeredLyapunov_subsequence
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (m n : ℕ → ℕ) (hsplit : ∀ L, m L + n L = L) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ ∀ᵐ x ∂mu, Tendsto
      (fun k => Real.log
        ‖centeredFderiv T T_inv (m (N k)) (n (N k)) x‖ / (N k))
      atTop (nhds (∫ y, lyapunovUpperAt T y ∂mu)) := by
  exact (tendstoInMeasure_log_norm_centeredFderiv_div_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right K hK_compact
      hK_inv mu hmu_supp hT hErg m n hsplit).exists_seq_tendsto_ae

end Submission.Helpers
