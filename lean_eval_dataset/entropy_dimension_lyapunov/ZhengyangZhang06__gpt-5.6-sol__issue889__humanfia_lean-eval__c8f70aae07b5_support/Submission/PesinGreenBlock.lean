import Submission.ComponentAdjugate
import Submission.PesinContractionBlock
import Submission.PesinStructuralCarrier

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

noncomputable def greenStableGrowth
    (T T_inv : EucPlane → EucPlane) (n : ℕ) (x : EucPlane) : ℝ :=
  ‖(fderiv ℝ (T_inv^[n]) x).inverse ∘L
    lyapunovStableComponent T T_inv (T_inv^[n] x)‖

noncomputable def greenUnstableGrowth
    (T T_inv : EucPlane → EucPlane) (n : ℕ) (x : EucPlane) : ℝ :=
  ‖(fderiv ℝ (T^[n]) x).inverse ∘L
    lyapunovUnstableComponent T T_inv (T^[n] x)‖

lemma greenStableGrowth_eq_component_kernel
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {carrier : Set EucPlane} (hcarrier : T '' carrier = carrier)
    (hcov : ∀ z ∈ carrier,
      lyapunovStableComponent T T_inv (T z) ∘L fderiv ℝ T z =
        fderiv ℝ T z ∘L lyapunovStableComponent T T_inv z)
    {x : EucPlane} (hx : x ∈ carrier) (n : ℕ) :
    greenStableGrowth T T_inv n x =
      ‖lyapunovStableComponent T T_inv x ∘L
        fderiv ℝ (T^[n]) (T_inv^[n] x)‖ := by
  have hcarrier_inv : T_inv '' carrier = carrier :=
    inverse_image_eq_of_image_eq hT_left hcarrier
  have hpast : T_inv^[n] x ∈ carrier := by
    rw [← image_iterate_eq_of_image_eq T_inv hcarrier_inv n]
    exact ⟨x, hx, rfl⟩
  have hcovn := stableComponent_fderiv_iterate_covariant_on_structuralCarrier
    T hT_smooth (lyapunovStableComponent T T_inv) hcarrier hcov hpast n
  rw [(hT_right.iterate n) x] at hcovn
  rw [greenStableGrowth,
    fderiv_iterate_inverse T_inv T hT_inv_smooth hT_smooth
      hT_right hT_left]
  exact congrArg norm hcovn.symm

lemma greenUnstableGrowth_eq_component_kernel
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {carrier : Set EucPlane} (hcarrier : T '' carrier = carrier)
    (hcov : ∀ z ∈ carrier,
      lyapunovUnstableComponent T T_inv (T z) ∘L fderiv ℝ T z =
        fderiv ℝ T z ∘L lyapunovUnstableComponent T T_inv z)
    {x : EucPlane} (hx : x ∈ carrier) (n : ℕ) :
    greenUnstableGrowth T T_inv n x =
      ‖lyapunovUnstableComponent T T_inv x ∘L
        fderiv ℝ (T_inv^[n]) (T^[n] x)‖ := by
  have hcovn := component_fderiv_inverse_iterate_covariant_on_structuralCarrier
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      (lyapunovUnstableComponent T T_inv) hcarrier hcov
      (show T^[n] x ∈ carrier by
        rw [← image_iterate_eq_of_image_eq T hcarrier n]
        exact ⟨x, hx, rfl⟩) n
  rw [(hT_left.iterate n) x] at hcovn
  rw [greenUnstableGrowth,
    fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right]
  exact congrArg norm hcovn.symm

lemma lyapunovUnstableComponent_swap
    (T T_inv : EucPlane → EucPlane) (x : EucPlane) :
    lyapunovUnstableComponent T_inv T x =
      lyapunovStableComponent T T_inv x := by
  unfold lyapunovUnstableComponent lyapunovStableComponent
  unfold unstableComponent stableComponent
  rw [add_comm]

lemma measurable_greenStableGrowth
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) (n : ℕ) :
    Measurable (greenStableGrowth T T_inv n) := by
  have hD : Measurable fun x => fderiv ℝ (T_inv^[n]) x :=
    ((contDiff_iterate T_inv hT_inv_smooth n).continuous_fderiv
      (by norm_num)).measurable
  have hS := measurable_lyapunovStableComponent
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
  have hSinv := hS.comp (hT_inv_smooth.continuous.iterate n).measurable
  exact ((ContinuousLinearMap.compL ℝ EucPlane EucPlane EucPlane).continuous₂
    |>.measurable.comp ((measurable_planeCLM_inverse.comp hD).prodMk hSinv)).norm

lemma measurable_greenUnstableGrowth
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) (n : ℕ) :
    Measurable (greenUnstableGrowth T T_inv n) := by
  have hD : Measurable fun x => fderiv ℝ (T^[n]) x :=
    ((contDiff_iterate T hT_smooth n).continuous_fderiv
      (by norm_num)).measurable
  have hU := measurable_lyapunovUnstableComponent
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
  have hUfuture := hU.comp (hT_smooth.continuous.iterate n).measurable
  exact ((ContinuousLinearMap.compL ℝ EucPlane EucPlane EucPlane).continuous₂
    |>.measurable.comp ((measurable_planeCLM_inverse.comp hD).prodMk hUfuture)).norm

def pesinGreenBlock
    (T T_inv : EucPlane → EucPlane)
    (lam1 lam2 eta : ℝ) (C : ℕ) : Set EucPlane :=
  {x | ∀ n : ℕ,
    greenStableGrowth T T_inv n x ≤
        C * Real.exp ((lam2 + 7 * eta) * n) ∧
    greenUnstableGrowth T T_inv n x ≤
        C * Real.exp ((-lam1 + 7 * eta) * n)}

lemma measurableSet_pesinGreenBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (lam1 lam2 eta : ℝ) (C : ℕ) :
    MeasurableSet (pesinGreenBlock T T_inv lam1 lam2 eta C) := by
  have heq : pesinGreenBlock T T_inv lam1 lam2 eta C =
      ⋂ n : ℕ,
        {x | greenStableGrowth T T_inv n x ≤
          C * Real.exp ((lam2 + 7 * eta) * n)} ∩
        {x | greenUnstableGrowth T T_inv n x ≤
          C * Real.exp ((-lam1 + 7 * eta) * n)} := by
    ext x
    simp [pesinGreenBlock]
  rw [heq]
  exact MeasurableSet.iInter fun n =>
    (measurableSet_le
      (measurable_greenStableGrowth T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n) measurable_const).inter
      (measurableSet_le
        (measurable_greenUnstableGrowth T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right n) measurable_const)

lemma monotone_pesinGreenBlock
    (T T_inv : EucPlane → EucPlane) (lam1 lam2 eta : ℝ) :
    Monotone (pesinGreenBlock T T_inv lam1 lam2 eta) := by
  intro C D hCD x hx n
  constructor
  · exact (hx n).1.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCD) (Real.exp_nonneg _))
  · exact (hx n).2.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCD) (Real.exp_nonneg _))

theorem ae_eventually_greenStableGrowth_le_exp
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
    (_hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      greenStableGrowth T T_inv n x ≤
        Real.exp ((lam2 + 7 * eta) * n) := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hupper_inv :=
    integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
  have hupper_swap :=
    integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
      T_inv T hT_inv_smooth hT_smooth hT_right hT_left
        K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
  have hlam1_inv : -lam2 = ∫ x, lyapunovUpperAt T_inv x ∂mu := by
    calc
      -lam2 = -∫ x, lyapunovLowerAt T x ∂mu := congrArg Neg.neg hlam2
      _ = ∫ x, lyapunovUpperAt T_inv x ∂mu := hupper_inv.symm
  have hlam2_inv : -lam1 = ∫ x, lyapunovLowerAt T_inv x ∂mu := by
    rw [← hlam1] at hupper_swap
    linarith
  have hrate_inv :
      8 * eta < hyperbolicRate (-lam2) (-lam1) := by
    convert hrate using 1
    dsimp [hyperbolicRate]
    ring
  have hgap_inv : 8 * eta < -lam2 - -lam1 := by
    rw [show -lam2 - -lam1 = lam1 - lam2 by ring]
    exact _hgap
  have hstable :=
    ae_eventually_norm_fderiv_inverse_comp_futureUnstable_le_exp
      (lam1 := -lam2) (lam2 := -lam1)
      T_inv T hT_inv_smooth hT_smooth hT_right hT_left
        K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
        hlam1_inv hlam2_inv (neg_pos.mpr hlam2_neg)
        (neg_neg_of_pos hlam1_pos) heta hgap_inv hunstable_neg
        (by simpa using hstable_neg) hrate_inv
  filter_upwards [hstable] with x hx
  filter_upwards [hx] with n hn
  simpa [greenStableGrowth, lyapunovUnstableComponent_swap] using hn

theorem ae_mem_iUnion_pesinGreenBlock
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
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, x ∈ ⋃ C : ℕ,
      pesinGreenBlock T T_inv lam1 lam2 eta C := by
  have hstable := ae_eventually_greenStableGrowth_le_exp
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hunstable :=
    ae_eventually_norm_fderiv_inverse_comp_futureUnstable_le_exp
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
        hstable_neg hunstable_neg hrate
  filter_upwards [hstable, hunstable] with x hxs hxu
  obtain ⟨Cs, hCs⟩ := exists_nat_mul_exp_bound_of_eventually
    (greenStableGrowth T T_inv · x) (fun _ => norm_nonneg _)
      (lam2 + 7 * eta) hxs
  obtain ⟨Cu, hCu⟩ := exists_nat_mul_exp_bound_of_eventually
    (greenUnstableGrowth T T_inv · x) (fun _ => norm_nonneg _)
      (-lam1 + 7 * eta) (by simpa [greenUnstableGrowth] using hxu)
  refine Set.mem_iUnion.mpr ⟨max Cs Cu, ?_⟩
  intro n
  constructor
  · exact (hCs n).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_left Cs Cu) (Real.exp_nonneg _))
  · exact (hCu n).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right Cs Cu) (Real.exp_nonneg _))

theorem tendsto_measureReal_compl_pesinGreenBlock_zero
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
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    Tendsto (fun C : ℕ => mu.real
      (pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ) atTop (nhds 0) := by
  have hfull := ae_mem_iUnion_pesinGreenBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hfullUnion : mu (⋃ C : ℕ,
      pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ = 0 := mem_ae_iff.mp hfull
  have hinter : ⋂ C : ℕ,
      (pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ =
        (⋃ C : ℕ, pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ := by simp
  have hmeasure := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun C => (measurableSet_pesinGreenBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C).compl.nullMeasurableSet)
    (fun C D hCD => Set.compl_subset_compl.mpr
      (monotone_pesinGreenBlock T T_inv lam1 lam2 eta hCD))
    ⟨0, measure_ne_top mu _⟩
  rw [hinter, hfullUnion] at hmeasure
  change Tendsto (fun C : ℕ =>
      (mu (pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ).toReal)
    atTop (nhds 0)
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun C => measure_ne_top mu
      (pesinGreenBlock T T_inv lam1 lam2 eta C)ᶜ)).2 hmeasure

end Submission.Helpers
