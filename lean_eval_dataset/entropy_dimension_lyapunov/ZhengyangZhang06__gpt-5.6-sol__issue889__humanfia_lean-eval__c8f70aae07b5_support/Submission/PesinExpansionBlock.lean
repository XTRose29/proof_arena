import Submission.LyapunovComponentLower
import Submission.PesinContractionBlock

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

lemma exists_nat_mul_lower_bound_of_eventually
    (f : ℕ → ℝ) (hf : ∀ n, 0 < f n) (rate : ℝ)
    (h : ∀ᶠ n : ℕ in atTop, Real.exp (rate * n) ≤ f n) :
    ∃ C : ℕ, ∀ n : ℕ, Real.exp (rate * n) ≤ C * f n := by
  let g : ℕ → ℝ := fun n => Real.exp (rate * n) / f n
  have hg : ∀ n, 0 ≤ g n := fun n => div_nonneg (Real.exp_nonneg _) (hf n).le
  have hgone : ∀ᶠ n : ℕ in atTop, g n ≤ Real.exp (0 * n) := by
    filter_upwards [h] with n hn
    simp only [zero_mul, Real.exp_zero]
    exact (div_le_one (hf n)).2 hn
  obtain ⟨C, hC⟩ := exists_nat_mul_exp_bound_of_eventually g hg 0 hgone
  refine ⟨C, fun n => ?_⟩
  have hn := hC n
  simp only [zero_mul, Real.exp_zero, mul_one] at hn
  exact (div_le_iff₀ (hf n)).mp hn

lemma norm_comp_pos_of_isInvertible_left
    (D A : EucPlane →L[ℝ] EucPlane)
    (hD : D.IsInvertible) (hA : 0 < ‖A‖) :
    0 < ‖D ∘L A‖ := by
  rw [norm_pos_iff]
  intro hzero
  have hrecover : A = D.inverse ∘L (D ∘L A) := by
    calc
      A = (ContinuousLinearMap.id ℝ EucPlane) ∘L A := by simp
      _ = (D.inverse ∘L D) ∘L A := by rw [hD.inverse_comp_self]
      _ = D.inverse ∘L (D ∘L A) :=
        ContinuousLinearMap.comp_assoc _ _ _
  rw [hzero, ContinuousLinearMap.comp_zero] at hrecover
  exact (norm_pos_iff.mp hA) hrecover

def pesinExpansionBlock
    (T T_inv : EucPlane → EucPlane)
    (lam1 lam2 eta : ℝ) (C : ℕ) : Set EucPlane :=
  {x | ∀ n : ℕ,
    Real.exp ((lam2 - 2 * eta) * n) ≤
        C * stableComponentGrowth T T_inv n x ∧
    Real.exp ((-lam1 - 2 * eta) * n) ≤
        C * unstableComponentGrowth T T_inv n x}

lemma measurableSet_pesinExpansionBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (lam1 lam2 eta : ℝ) (C : ℕ) :
    MeasurableSet (pesinExpansionBlock T T_inv lam1 lam2 eta C) := by
  have heq : pesinExpansionBlock T T_inv lam1 lam2 eta C =
      ⋂ n : ℕ,
        {x | Real.exp ((lam2 - 2 * eta) * n) ≤
          C * stableComponentGrowth T T_inv n x} ∩
        {x | Real.exp ((-lam1 - 2 * eta) * n) ≤
          C * unstableComponentGrowth T T_inv n x} := by
    ext x
    simp [pesinExpansionBlock]
  rw [heq]
  exact MeasurableSet.iInter fun n =>
    (measurableSet_le measurable_const
      (measurable_const.mul
        (measurable_stableComponentGrowth T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right n))).inter
      (measurableSet_le measurable_const
        (measurable_const.mul
          (measurable_unstableComponentGrowth T T_inv hT_smooth hT_inv_smooth
            hT_left hT_right n)))

lemma monotone_pesinExpansionBlock
    (T T_inv : EucPlane → EucPlane) (lam1 lam2 eta : ℝ) :
    Monotone (pesinExpansionBlock T T_inv lam1 lam2 eta) := by
  intro C D hCD x hx n
  constructor
  · exact (hx n).1.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCD) (norm_nonneg _))
  · exact (hx n).2.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCD) (norm_nonneg _))

theorem ae_mem_iUnion_pesinExpansionBlock
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
      pesinExpansionBlock T T_inv lam1 lam2 eta C := by
  have hstable :=
    ae_eventually_exp_le_norm_fderiv_comp_lyapunovStableComponent
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
        hstable_neg hunstable_neg hrate
  have hunstable :=
    ae_eventually_exp_le_norm_fderiv_inverse_comp_lyapunovUnstableComponent
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
  filter_upwards [hstable, hunstable, hsource, hstableStructure,
    hunstableStructure] with x hxs hxu hxsource hxS hxU
  have hSnorm : 1 ≤ ‖lyapunovStableComponent T T_inv x‖ := by
    simpa [lyapunovStableComponent] using one_le_norm_stableComponent
      (stableProjection T x) (stableProjection T_inv x)
      hxsource.invertible hxsource.stableIdempotent hxsource.unstableIdempotent
      hxsource.transverse hxS.2.2.1
  have hUnorm : 1 ≤ ‖lyapunovUnstableComponent T T_inv x‖ := by
    simpa [lyapunovUnstableComponent] using one_le_norm_unstableComponent
      (stableProjection T x) (stableProjection T_inv x)
      hxsource.invertible hxsource.stableIdempotent hxsource.unstableIdempotent
      hxsource.transverse hxU.2.2.1
  have hstable_pos (n : ℕ) : 0 < stableComponentGrowth T T_inv n x := by
    apply norm_comp_pos_of_isInvertible_left
    · apply ContinuousLinearMap.IsInvertible.of_inverse
        (g := (fderiv ℝ (T^[n]) x).inverse)
      · exact fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right n x
      · exact fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right n x
    · exact zero_lt_one.trans_le hSnorm
  have hunstable_pos (n : ℕ) : 0 < unstableComponentGrowth T T_inv n x := by
    apply norm_comp_pos_of_isInvertible_left
    · apply ContinuousLinearMap.IsInvertible.of_inverse
        (g := (fderiv ℝ (T_inv^[n]) x).inverse)
      · exact fderiv_iterate_comp_inverse T_inv T hT_inv_smooth hT_smooth
          hT_right hT_left n x
      · exact fderiv_iterate_inverse_comp T_inv T hT_inv_smooth hT_smooth
          hT_right hT_left n x
    · exact zero_lt_one.trans_le hUnorm
  obtain ⟨Cs, hCs⟩ := exists_nat_mul_lower_bound_of_eventually
    (stableComponentGrowth T T_inv · x) hstable_pos (lam2 - 2 * eta) hxs
  obtain ⟨Cu, hCu⟩ := exists_nat_mul_lower_bound_of_eventually
    (unstableComponentGrowth T T_inv · x) hunstable_pos (-lam1 - 2 * eta) hxu
  refine Set.mem_iUnion.mpr ⟨max Cs Cu, fun n => ⟨?_, ?_⟩⟩
  · exact (hCs n).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_left Cs Cu) (norm_nonneg _))
  · exact (hCu n).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right Cs Cu) (norm_nonneg _))

theorem tendsto_measureReal_compl_pesinExpansionBlock_zero
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
      (pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ)
      atTop (nhds 0) := by
  have hfull := ae_mem_iUnion_pesinExpansionBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hfullUnion : mu (⋃ C : ℕ,
      pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ = 0 :=
    mem_ae_iff.mp hfull
  have hinter : ⋂ C : ℕ,
      (pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ =
        (⋃ C : ℕ, pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ := by
    simp
  have hmeasure := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun C => (measurableSet_pesinExpansionBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C).compl.nullMeasurableSet)
    (fun C D hCD => Set.compl_subset_compl.mpr
      (monotone_pesinExpansionBlock T T_inv lam1 lam2 eta hCD))
    ⟨0, measure_ne_top mu _⟩
  rw [hinter, hfullUnion] at hmeasure
  change Tendsto (fun C : ℕ =>
      (mu (pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ).toReal)
    atTop (nhds 0)
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun C => measure_ne_top mu
      (pesinExpansionBlock T T_inv lam1 lam2 eta C)ᶜ)).2 hmeasure

end Submission.Helpers
