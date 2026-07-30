import Submission.PesinTemperingBlock

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

def pesinRegularBlock
    (T T_inv : EucPlane → EucPlane)
    (lam1 lam2 eta : ℝ) (C : ℕ) : Set EucPlane :=
  pesinContractionBlock T T_inv lam1 lam2 eta C ∩
    pesinTemperingBlock T T_inv eta C

lemma measurableSet_pesinRegularBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (lam1 lam2 eta : ℝ) (C : ℕ) :
    MeasurableSet (pesinRegularBlock T T_inv lam1 lam2 eta C) := by
  exact (measurableSet_pesinContractionBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right lam1 lam2 eta C).inter
      (measurableSet_pesinTemperingBlock
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right eta C)

lemma monotone_pesinRegularBlock
    (T T_inv : EucPlane → EucPlane) (lam1 lam2 eta : ℝ) :
    Monotone (pesinRegularBlock T T_inv lam1 lam2 eta) := by
  intro C D hCD x hx
  exact ⟨monotone_pesinContractionBlock T T_inv lam1 lam2 eta hCD hx.1,
    monotone_pesinTemperingBlock T T_inv eta hCD hx.2⟩

theorem ae_mem_iUnion_pesinRegularBlock
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
    ∀ᵐ x ∂mu, x ∈ ⋃ C : ℕ,
      pesinRegularBlock T T_inv lam1 lam2 eta C := by
  have hcontraction := ae_mem_iUnion_pesinContractionBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have htempering := ae_mem_iUnion_pesinTemperingBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  filter_upwards [hcontraction, htempering] with x hxc hxt
  obtain ⟨Cc, hCc⟩ := Set.mem_iUnion.mp hxc
  obtain ⟨Ct, hCt⟩ := Set.mem_iUnion.mp hxt
  refine Set.mem_iUnion.mpr ⟨max Cc Ct, ?_⟩
  exact ⟨monotone_pesinContractionBlock T T_inv lam1 lam2 eta
      (le_max_left _ _) hCc,
    monotone_pesinTemperingBlock T T_inv eta (le_max_right _ _) hCt⟩

theorem tendsto_measureReal_compl_pesinRegularBlock_zero
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
      (pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ)
      atTop (nhds 0) := by
  have hfull := ae_mem_iUnion_pesinRegularBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have hfullUnion : mu (⋃ C : ℕ,
      pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ = 0 := mem_ae_iff.mp hfull
  have hinter : ⋂ C : ℕ,
      (pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ =
        (⋃ C : ℕ, pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ := by simp
  have hmeasure := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun C => (measurableSet_pesinRegularBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C).compl.nullMeasurableSet)
    (fun C D hCD => Set.compl_subset_compl.mpr
      (monotone_pesinRegularBlock T T_inv lam1 lam2 eta hCD))
    ⟨0, measure_ne_top mu _⟩
  rw [hinter, hfullUnion] at hmeasure
  change Tendsto (fun C : ℕ =>
      (mu (pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ).toReal)
    atTop (nhds 0)
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun C => measure_ne_top mu
      (pesinRegularBlock T T_inv lam1 lam2 eta C)ᶜ)).2 hmeasure

end Submission.Helpers
