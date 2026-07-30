import Submission.CenteredLinearControl
import Submission.PesinExpansionBlock

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

/-- Uniform upper bounds for the full forward cocycle, together with a
uniform lower bound for its Jacobian.  The latter is what permits inversion
on the stable line without assuming that intermediate orbit points lie in a
fixed Pesin block. -/
def pesinFullBlock
    (T : EucPlane → EucPlane) (lam1 lam2 eta : ℝ) (C : ℕ) : Set EucPlane :=
  {x | ∀ n : ℕ,
    ‖fderiv ℝ (T^[n]) x‖ ≤ C * Real.exp ((lam1 + eta) * n) ∧
    Real.exp ((lam1 + lam2 - eta) * n) ≤
      C * |(fderiv ℝ (T^[n]) x).det|}

lemma measurableSet_pesinFullBlock
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    (lam1 lam2 eta : ℝ) (C : ℕ) :
    MeasurableSet (pesinFullBlock T lam1 lam2 eta C) := by
  have hD (n : ℕ) : Measurable fun x => fderiv ℝ (T^[n]) x :=
    ((contDiff_iterate T hT_smooth n).continuous_fderiv (by norm_num)).measurable
  have heq : pesinFullBlock T lam1 lam2 eta C =
      ⋂ n : ℕ,
        {x | ‖fderiv ℝ (T^[n]) x‖ ≤ C * Real.exp ((lam1 + eta) * n)} ∩
        {x | Real.exp ((lam1 + lam2 - eta) * n) ≤
          C * |(fderiv ℝ (T^[n]) x).det|} := by
    ext x
    simp [pesinFullBlock]
  rw [heq]
  exact MeasurableSet.iInter fun n =>
    (measurableSet_le (hD n).norm measurable_const).inter
      (measurableSet_le measurable_const
        (measurable_const.mul
          ((ContinuousLinearMap.continuous_det.measurable.comp (hD n)).abs)))

lemma monotone_pesinFullBlock
    (T : EucPlane → EucPlane) (lam1 lam2 eta : ℝ) :
    Monotone (pesinFullBlock T lam1 lam2 eta) := by
  intro C D hCD x hx n
  constructor
  · exact (hx n).1.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCD) (Real.exp_nonneg _))
  · exact (hx n).2.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCD) (abs_nonneg _))

theorem ae_mem_iUnion_pesinFullBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (heta : 0 < eta) :
    ∀ᵐ x ∂mu, x ∈ ⋃ C : ℕ, pesinFullBlock T lam1 lam2 eta C := by
  have hnorm := ae_eventually_norm_fderiv_iterate_lt_exp_integral_add
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hErg heta
  have hjac := ae_tendsto_logJacobianIterate_div_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact mu hmu_supp hT hErg
  have hjacIntegral := integral_logJacobian_eq_integral_lyapunovUpper_add_lower
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
  filter_upwards [hnorm, hjac] with x hxnorm hxjac
  have hxnorm' : ∀ᶠ n : ℕ in atTop,
      ‖fderiv ℝ (T^[n]) x‖ ≤ Real.exp ((lam1 + eta) * n) := by
    filter_upwards [hxnorm] with n hn
    simpa [hlam1] using hn.le
  have hxdet_pos (n : ℕ) : 0 < |(fderiv ℝ (T^[n]) x).det| :=
    abs_pos.mpr (det_fderiv_iterate_ne_zero
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right n x)
  have hxjac' : Tendsto
      (fun n : ℕ => Real.log |(fderiv ℝ (T^[n]) x).det| / n)
      atTop (nhds (lam1 + lam2)) := by
    simpa [logJacobianIterate, hjacIntegral, ← hlam1, ← hlam2] using hxjac
  have hxdet : ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam1 + lam2 - eta) * n) ≤
        |(fderiv ℝ (T^[n]) x).det| :=
    eventually_exp_sub_le_of_tendsto_log_div
      (N := fun n : ℕ => n) tendsto_id hxdet_pos heta hxjac'
  obtain ⟨Cn, hCn⟩ := exists_nat_mul_exp_bound_of_eventually
    (fun n => ‖fderiv ℝ (T^[n]) x‖) (fun _ => norm_nonneg _)
      (lam1 + eta) hxnorm'
  obtain ⟨Cd, hCd⟩ := exists_nat_mul_lower_bound_of_eventually
    (fun n => |(fderiv ℝ (T^[n]) x).det|) hxdet_pos
      (lam1 + lam2 - eta) hxdet
  refine Set.mem_iUnion.mpr ⟨max Cn Cd, fun n => ⟨?_, ?_⟩⟩
  · exact (hCn n).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_left Cn Cd) (Real.exp_nonneg _))
  · exact (hCd n).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right Cn Cd) (abs_nonneg _))

theorem tendsto_measureReal_compl_pesinFullBlock_zero
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (heta : 0 < eta) :
    Tendsto (fun C : ℕ => mu.real (pesinFullBlock T lam1 lam2 eta C)ᶜ)
      atTop (nhds 0) := by
  have hfull := ae_mem_iUnion_pesinFullBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hlam1 hlam2 heta
  have hfullUnion : mu (⋃ C : ℕ, pesinFullBlock T lam1 lam2 eta C)ᶜ = 0 :=
    mem_ae_iff.mp hfull
  have hinter : ⋂ C : ℕ, (pesinFullBlock T lam1 lam2 eta C)ᶜ =
      (⋃ C : ℕ, pesinFullBlock T lam1 lam2 eta C)ᶜ := by simp
  have hmeasure := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun C => (measurableSet_pesinFullBlock T hT_smooth lam1 lam2 eta C).compl.nullMeasurableSet)
    (fun C D hCD => Set.compl_subset_compl.mpr
      (monotone_pesinFullBlock T lam1 lam2 eta hCD))
    ⟨0, measure_ne_top mu _⟩
  rw [hinter, hfullUnion] at hmeasure
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun C => measure_ne_top mu (pesinFullBlock T lam1 lam2 eta C)ᶜ)).2 hmeasure

end Submission.Helpers
