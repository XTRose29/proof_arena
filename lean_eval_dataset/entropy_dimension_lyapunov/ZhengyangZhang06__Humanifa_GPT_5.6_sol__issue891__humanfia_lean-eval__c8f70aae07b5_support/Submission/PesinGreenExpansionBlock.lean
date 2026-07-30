import Submission.LyapunovComponentLower
import Submission.PesinExpansionBlock
import Submission.PesinGreenBlock

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

theorem ae_eventually_exp_le_greenUnstableGrowth
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
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      Real.exp ((-lam1 - 3 * eta) * n) ≤
        greenUnstableGrowth T T_inv n x := by
  simpa [greenUnstableGrowth] using
    (ae_eventually_exp_le_norm_fderiv_inverse_comp_futureUnstable
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
        hstable_neg hunstable_neg hrate)

theorem ae_eventually_exp_le_greenStableGrowth
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
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      Real.exp ((lam2 - 3 * eta) * n) ≤
        greenStableGrowth T T_inv n x := by
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
  have hlower := ae_eventually_exp_le_norm_fderiv_inverse_comp_futureUnstable
    (lam1 := -lam2) (lam2 := -lam1)
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
      hlam1_inv hlam2_inv (neg_pos.mpr hlam2_neg)
      (neg_neg_of_pos hlam1_pos) heta (by linarith only [hgap])
      hunstable_neg (by simpa using hstable_neg) (by
        convert hrate using 1
        dsimp [hyperbolicRate]
        ring)
  filter_upwards [hlower] with x hx
  filter_upwards [hx] with n hn
  simpa [greenStableGrowth, lyapunovUnstableComponent_swap] using hn

def pesinGreenExpansionBlock
    (T T_inv : EucPlane → EucPlane)
    (lam1 lam2 eta : ℝ) (C : ℕ) : Set EucPlane :=
  {x | ∀ n : ℕ,
    Real.exp ((lam2 - 3 * eta) * n) ≤
        C * greenStableGrowth T T_inv n x ∧
    Real.exp ((-lam1 - 3 * eta) * n) ≤
        C * greenUnstableGrowth T T_inv n x}

lemma measurableSet_pesinGreenExpansionBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (lam1 lam2 eta : ℝ) (C : ℕ) :
    MeasurableSet (pesinGreenExpansionBlock T T_inv lam1 lam2 eta C) := by
  have heq : pesinGreenExpansionBlock T T_inv lam1 lam2 eta C =
      ⋂ n : ℕ,
        {x | Real.exp ((lam2 - 3 * eta) * n) ≤
          C * greenStableGrowth T T_inv n x} ∩
        {x | Real.exp ((-lam1 - 3 * eta) * n) ≤
          C * greenUnstableGrowth T T_inv n x} := by
    ext x
    simp [pesinGreenExpansionBlock]
  rw [heq]
  exact MeasurableSet.iInter fun n =>
    (measurableSet_le measurable_const
      (measurable_const.mul
        (measurable_greenStableGrowth T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right n))).inter
      (measurableSet_le measurable_const
        (measurable_const.mul
          (measurable_greenUnstableGrowth T T_inv hT_smooth hT_inv_smooth
            hT_left hT_right n)))

lemma monotone_pesinGreenExpansionBlock
    (T T_inv : EucPlane → EucPlane) (lam1 lam2 eta : ℝ) :
    Monotone (pesinGreenExpansionBlock T T_inv lam1 lam2 eta) := by
  intro C D hCD x hx n
  constructor
  · exact (hx n).1.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCD) (norm_nonneg _))
  · exact (hx n).2.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCD) (norm_nonneg _))

theorem ae_mem_iUnion_pesinGreenExpansionBlock
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
      pesinGreenExpansionBlock T T_inv lam1 lam2 eta C := by
  have hstable := ae_eventually_exp_le_greenStableGrowth
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hunstable := ae_eventually_exp_le_greenUnstableGrowth
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hsource := ae_sourceSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have hstableStructure := ae_stableProjection_structure
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta (by linarith)
  have hunstableStructure := ae_unstableProjection_structure
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta (by linarith)
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hsourceF := ae_all_iterates_of_ae hT.quasiMeasurePreserving hsource
  have hsourceB := ae_all_iterates_of_ae hT_inv.quasiMeasurePreserving hsource
  have hstableF := ae_all_iterates_of_ae
    hT.quasiMeasurePreserving hstableStructure
  have hstableB := ae_all_iterates_of_ae
    hT_inv.quasiMeasurePreserving hstableStructure
  have hunstableF := ae_all_iterates_of_ae
    hT.quasiMeasurePreserving hunstableStructure
  filter_upwards [hstable, hunstable, hsourceF, hsourceB,
    hstableF, hstableB, hunstableF]
    with x hxs hxu hxsourceF hxsourceB hxstableF hxstableB hxunstableF
  have hgreenStable_pos (n : ℕ) :
      0 < greenStableGrowth T T_inv n x := by
    apply norm_comp_pos_of_isInvertible_left
    · apply ContinuousLinearMap.IsInvertible.of_inverse
          (g := fderiv ℝ (T_inv^[n]) x)
      · exact fderiv_iterate_inverse_comp
          T_inv T hT_inv_smooth hT_smooth hT_right hT_left n x
      · exact fderiv_iterate_comp_inverse
          T_inv T hT_inv_smooth hT_smooth hT_right hT_left n x
    · let z := T_inv^[n] x
      have hnorm :
          1 ≤ ‖lyapunovStableComponent T T_inv z‖ := by
        simpa [lyapunovStableComponent] using
          one_le_norm_stableComponent
            (stableProjection T z) (stableProjection T_inv z)
            (hxsourceB n).invertible (hxsourceB n).stableIdempotent
            (hxsourceB n).unstableIdempotent (hxsourceB n).transverse
            (hxstableB n).2.2.1
      simpa [z] using (zero_lt_one.trans_le hnorm)
  have hgreenUnstable_pos (n : ℕ) :
      0 < greenUnstableGrowth T T_inv n x := by
    apply norm_comp_pos_of_isInvertible_left
    · apply ContinuousLinearMap.IsInvertible.of_inverse
          (g := fderiv ℝ (T^[n]) x)
      · exact fderiv_iterate_inverse_comp
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right n x
      · exact fderiv_iterate_comp_inverse
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right n x
    · let z := T^[n] x
      have hnorm :
          1 ≤ ‖lyapunovUnstableComponent T T_inv z‖ := by
        simpa [lyapunovUnstableComponent] using
          one_le_norm_unstableComponent
            (stableProjection T z) (stableProjection T_inv z)
            (hxsourceF n).invertible (hxsourceF n).stableIdempotent
            (hxsourceF n).unstableIdempotent (hxsourceF n).transverse
            (hxunstableF n).2.2.1
      simpa [z] using (zero_lt_one.trans_le hnorm)
  obtain ⟨Cs, hCs⟩ := exists_nat_mul_lower_bound_of_eventually
    (greenStableGrowth T T_inv · x) hgreenStable_pos
      (lam2 - 3 * eta) hxs
  obtain ⟨Cu, hCu⟩ := exists_nat_mul_lower_bound_of_eventually
    (greenUnstableGrowth T T_inv · x) hgreenUnstable_pos
      (-lam1 - 3 * eta) hxu
  refine Set.mem_iUnion.mpr ⟨max Cs Cu, fun n => ⟨?_, ?_⟩⟩
  · exact (hCs n).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_left Cs Cu) (norm_nonneg _))
  · exact (hCu n).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right Cs Cu) (norm_nonneg _))

theorem tendsto_measureReal_compl_pesinGreenExpansionBlock_zero
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
      (pesinGreenExpansionBlock T T_inv lam1 lam2 eta C)ᶜ)
      atTop (nhds 0) := by
  have hfull := ae_mem_iUnion_pesinGreenExpansionBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hfullUnion : mu (⋃ C : ℕ,
      pesinGreenExpansionBlock T T_inv lam1 lam2 eta C)ᶜ = 0 :=
    mem_ae_iff.mp hfull
  have hinter : ⋂ C : ℕ,
      (pesinGreenExpansionBlock T T_inv lam1 lam2 eta C)ᶜ =
        (⋃ C : ℕ, pesinGreenExpansionBlock T T_inv lam1 lam2 eta C)ᶜ := by
    simp
  have hmeasure := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun C => (measurableSet_pesinGreenExpansionBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C).compl.nullMeasurableSet)
    (fun C D hCD => Set.compl_subset_compl.mpr
      (monotone_pesinGreenExpansionBlock T T_inv lam1 lam2 eta hCD))
    ⟨0, measure_ne_top mu _⟩
  rw [hinter, hfullUnion] at hmeasure
  change Tendsto (fun C : ℕ =>
      (mu (pesinGreenExpansionBlock T T_inv lam1 lam2 eta C)ᶜ).toReal)
    atTop (nhds 0)
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun C => measure_ne_top mu
      (pesinGreenExpansionBlock T T_inv lam1 lam2 eta C)ᶜ)).2 hmeasure

end Submission.Helpers
