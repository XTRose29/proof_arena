import Submission.PesinEndpointBlock
import Submission.PesinFullBlock

namespace Submission.Helpers

open LeanEval.Dynamics MeasureTheory

def pesinFullShadowingBlock
    (T T_inv : EucPlane → EucPlane)
    (lam1 lam2 eta : ℝ) (C : ℕ) : Set EucPlane :=
  (pesinShadowingBlock T T_inv lam1 lam2 eta C ∩
      pesinFullBlock T lam1 lam2 eta C) ∩
    pesinFullBlock T_inv (-lam2) (-lam1) eta C

lemma measurableSet_pesinFullShadowingBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (lam1 lam2 eta : ℝ) (C : ℕ) :
    MeasurableSet (pesinFullShadowingBlock T T_inv lam1 lam2 eta C) :=
  ((measurableSet_pesinShadowingBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C).inter
      (measurableSet_pesinFullBlock T hT_smooth lam1 lam2 eta C)).inter
    (measurableSet_pesinFullBlock T_inv hT_inv_smooth
      (-lam2) (-lam1) eta C)

lemma monotone_pesinFullShadowingBlock
    (T T_inv : EucPlane → EucPlane) (lam1 lam2 eta : ℝ) :
    Monotone (pesinFullShadowingBlock T T_inv lam1 lam2 eta) := by
  intro C D hCD x hx
  exact ⟨⟨monotone_pesinShadowingBlock T T_inv lam1 lam2 eta hCD hx.1.1,
      monotone_pesinFullBlock T lam1 lam2 eta hCD hx.1.2⟩,
    monotone_pesinFullBlock T_inv (-lam2) (-lam1) eta hCD hx.2⟩

theorem tendsto_measureReal_compl_pesinFullShadowingBlock_zero
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
    Filter.Tendsto (fun C : ℕ => mu.real
      (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)ᶜ)
      Filter.atTop (nhds 0) := by
  have hshadow := tendsto_measureReal_compl_pesinShadowingBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hfull := tendsto_measureReal_compl_pesinFullBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hlam1 hlam2 heta
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
  have hfull_inv := tendsto_measureReal_compl_pesinFullBlock_zero
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
      hlam1_inv hlam2_inv heta
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun C => measureReal_nonneg
      (μ := mu) (s := (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)ᶜ))
    (Filter.Eventually.of_forall fun C => ?_)
    (by simpa using (hshadow.add hfull).add hfull_inv)
  rw [pesinFullShadowingBlock, Set.compl_inter, Set.compl_inter]
  exact (measureReal_union_le _ _).trans
    (add_le_add (measureReal_union_le _ _) le_rfl)

theorem exists_uniform_balancedFullEndpointBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta gamma : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2)
    (hgamma : 0 < gamma) :
    ∃ C : ℕ,
      let G := pesinFullShadowingBlock T T_inv lam1 lam2 eta C
      MeasurableSet G ∧
        ∀ L : ℕ,
          MeasurableSet (balancedEndpointBlock T T_inv lam1 lam2 G L) ∧
          mu.real (balancedEndpointBlock T T_inv lam1 lam2 G L)ᶜ < gamma := by
  have hmeasure := tendsto_measureReal_compl_pesinFullShadowingBlock_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hhalf : 0 < gamma / 2 := div_pos hgamma (by norm_num)
  have hsmall : ∀ᶠ C : ℕ in Filter.atTop,
      mu.real (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)ᶜ <
        gamma / 2 := (tendsto_order.1 hmeasure).2 _ hhalf
  obtain ⟨C, hC⟩ := hsmall.exists
  let G := pesinFullShadowingBlock T T_inv lam1 lam2 eta C
  have hG : MeasurableSet G := measurableSet_pesinFullShadowingBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right lam1 lam2 eta C
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  refine ⟨C, hG, fun L => ⟨
    measurableSet_balancedEndpointBlock T T_inv hT.measurable hT_inv.measurable
      lam1 lam2 hG L, ?_⟩⟩
  have hle := measureReal_compl_balancedEndpointBlock_le
    mu T T_inv hT hT_inv lam1 lam2 hG L
  dsimp [G] at hle ⊢
  nlinarith

end Submission.Helpers
