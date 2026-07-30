import Submission.LyapunovComponentTempering
import Submission.PesinContractionBlock

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology

def pesinTemperingBlock
    (T T_inv : EucPlane → EucPlane) (eta : ℝ) (C : ℕ) : Set EucPlane :=
  {x | ∀ n : ℕ,
    ‖lyapunovStableComponent T T_inv (T^[n] x)‖ ≤
        C * Real.exp (9 * eta * n) ∧
    ‖lyapunovUnstableComponent T T_inv (T^[n] x)‖ ≤
        C * Real.exp (9 * eta * n) ∧
    ‖lyapunovStableComponent T T_inv (T_inv^[n] x)‖ ≤
        C * Real.exp (9 * eta * n) ∧
    ‖lyapunovUnstableComponent T T_inv (T_inv^[n] x)‖ ≤
        C * Real.exp (9 * eta * n)}

lemma measurableSet_pesinTemperingBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (eta : ℝ) (C : ℕ) :
    MeasurableSet (pesinTemperingBlock T T_inv eta C) := by
  have hS := measurable_lyapunovStableComponent
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
  have hU := measurable_lyapunovUnstableComponent
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
  have hTf (n : ℕ) : Measurable (T^[n]) :=
    (hT_smooth.continuous.iterate n).measurable
  have hTb (n : ℕ) : Measurable (T_inv^[n]) :=
    (hT_inv_smooth.continuous.iterate n).measurable
  have heq : pesinTemperingBlock T T_inv eta C =
      ⋂ n : ℕ,
        {x | ‖lyapunovStableComponent T T_inv (T^[n] x)‖ ≤
          C * Real.exp (9 * eta * n)} ∩
        {x | ‖lyapunovUnstableComponent T T_inv (T^[n] x)‖ ≤
          C * Real.exp (9 * eta * n)} ∩
        {x | ‖lyapunovStableComponent T T_inv (T_inv^[n] x)‖ ≤
          C * Real.exp (9 * eta * n)} ∩
        {x | ‖lyapunovUnstableComponent T T_inv (T_inv^[n] x)‖ ≤
          C * Real.exp (9 * eta * n)} := by
    ext x
    simp [pesinTemperingBlock, and_assoc]
  rw [heq]
  apply MeasurableSet.iInter
  intro n
  exact (((measurableSet_le ((hS.comp (hTf n)).norm) measurable_const).inter
      (measurableSet_le ((hU.comp (hTf n)).norm) measurable_const)).inter
      (measurableSet_le ((hS.comp (hTb n)).norm) measurable_const)).inter
      (measurableSet_le ((hU.comp (hTb n)).norm) measurable_const)

lemma monotone_pesinTemperingBlock
    (T T_inv : EucPlane → EucPlane) (eta : ℝ) :
    Monotone (pesinTemperingBlock T T_inv eta) := by
  intro C D hCD x hx n
  have hscale : (C : ℝ) * Real.exp (9 * eta * n) ≤
      D * Real.exp (9 * eta * n) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hCD) (Real.exp_nonneg _)
  exact ⟨(hx n).1.trans hscale,
    (hx n).2.1.trans hscale,
    (hx n).2.2.1.trans hscale,
    (hx n).2.2.2.trans hscale⟩

theorem ae_mem_iUnion_pesinTemperingBlock
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
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, x ∈ ⋃ C : ℕ, pesinTemperingBlock T T_inv eta C := by
  have hforward := ae_eventually_norm_lyapunovComponents_iterate_le_exp
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have hbackward := ae_eventually_norm_lyapunovComponents_inverse_iterate_le_exp
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  filter_upwards [hforward, hbackward] with x hxf hxb
  have hSf : ∀ᶠ n : ℕ in atTop,
      ‖lyapunovStableComponent T T_inv (T^[n] x)‖ ≤
        Real.exp ((9 * eta) * n) := hxf.mono fun n hn => hn.1
  have hUf : ∀ᶠ n : ℕ in atTop,
      ‖lyapunovUnstableComponent T T_inv (T^[n] x)‖ ≤
        Real.exp ((9 * eta) * n) := hxf.mono fun n hn => hn.2
  have hSb : ∀ᶠ n : ℕ in atTop,
      ‖lyapunovStableComponent T T_inv (T_inv^[n] x)‖ ≤
        Real.exp ((9 * eta) * n) := hxb.mono fun n hn => hn.1
  have hUb : ∀ᶠ n : ℕ in atTop,
      ‖lyapunovUnstableComponent T T_inv (T_inv^[n] x)‖ ≤
        Real.exp ((9 * eta) * n) := hxb.mono fun n hn => hn.2
  obtain ⟨CSf, hCSf⟩ := exists_nat_mul_exp_bound_of_eventually
    (fun n => ‖lyapunovStableComponent T T_inv (T^[n] x)‖)
      (fun _ => norm_nonneg _) (9 * eta) hSf
  obtain ⟨CUf, hCUf⟩ := exists_nat_mul_exp_bound_of_eventually
    (fun n => ‖lyapunovUnstableComponent T T_inv (T^[n] x)‖)
      (fun _ => norm_nonneg _) (9 * eta) hUf
  obtain ⟨CSb, hCSb⟩ := exists_nat_mul_exp_bound_of_eventually
    (fun n => ‖lyapunovStableComponent T T_inv (T_inv^[n] x)‖)
      (fun _ => norm_nonneg _) (9 * eta) hSb
  obtain ⟨CUb, hCUb⟩ := exists_nat_mul_exp_bound_of_eventually
    (fun n => ‖lyapunovUnstableComponent T T_inv (T_inv^[n] x)‖)
      (fun _ => norm_nonneg _) (9 * eta) hUb
  let C := max (max CSf CUf) (max CSb CUb)
  refine Set.mem_iUnion.mpr ⟨C, ?_⟩
  intro n
  have hCSfC : CSf ≤ C :=
    (le_max_left CSf CUf).trans (le_max_left _ _)
  have hCUfC : CUf ≤ C :=
    (le_max_right CSf CUf).trans (le_max_left _ _)
  have hCSbC : CSb ≤ C :=
    (le_max_left CSb CUb).trans (le_max_right _ _)
  have hCUbC : CUb ≤ C :=
    (le_max_right CSb CUb).trans (le_max_right _ _)
  have hscale (a : ℕ) (ha : a ≤ C) :
      (a : ℝ) * Real.exp (9 * eta * n) ≤
        C * Real.exp (9 * eta * n) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast ha) (Real.exp_nonneg _)
  exact ⟨(hCSf n).trans (hscale CSf hCSfC),
    (hCUf n).trans (hscale CUf hCUfC),
    (hCSb n).trans (hscale CSb hCSbC),
    (hCUb n).trans (hscale CUb hCUbC)⟩

theorem tendsto_measureReal_compl_pesinTemperingBlock_zero
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
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    Tendsto (fun C : ℕ => mu.real
      (pesinTemperingBlock T T_inv eta C)ᶜ) atTop (nhds 0) := by
  have hfull := ae_mem_iUnion_pesinTemperingBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have hfullUnion : mu (⋃ C : ℕ,
      pesinTemperingBlock T T_inv eta C)ᶜ = 0 := mem_ae_iff.mp hfull
  have hinter : ⋂ C : ℕ, (pesinTemperingBlock T T_inv eta C)ᶜ =
      (⋃ C : ℕ, pesinTemperingBlock T T_inv eta C)ᶜ := by simp
  have hmeasure := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun C => (measurableSet_pesinTemperingBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right eta C).compl.nullMeasurableSet)
    (fun C D hCD => Set.compl_subset_compl.mpr
      (monotone_pesinTemperingBlock T T_inv eta hCD))
    ⟨0, measure_ne_top mu _⟩
  rw [hinter, hfullUnion] at hmeasure
  change Tendsto (fun C : ℕ =>
      (mu (pesinTemperingBlock T T_inv eta C)ᶜ).toReal) atTop (nhds 0)
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun C => measure_ne_top mu
      (pesinTemperingBlock T T_inv eta C)ᶜ)).2 hmeasure

end Submission.Helpers
