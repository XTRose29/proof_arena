import Submission.LyapunovComponentContraction

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology

noncomputable def stableComponentGrowth
    (T T_inv : EucPlane → EucPlane) (n : ℕ) (x : EucPlane) : ℝ :=
  ‖fderiv ℝ (T^[n]) x ∘L lyapunovStableComponent T T_inv x‖

noncomputable def unstableComponentGrowth
    (T T_inv : EucPlane → EucPlane) (n : ℕ) (x : EucPlane) : ℝ :=
  ‖fderiv ℝ (T_inv^[n]) x ∘L lyapunovUnstableComponent T T_inv x‖

lemma measurable_stableComponentGrowth
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) (n : ℕ) :
    Measurable (stableComponentGrowth T T_inv n) := by
  have hA : Measurable fun x => fderiv ℝ (T^[n]) x :=
    ((contDiff_iterate T hT_smooth n).continuous_fderiv (by norm_num)).measurable
  have hS := measurable_lyapunovStableComponent
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
  exact ((ContinuousLinearMap.compL ℝ EucPlane EucPlane EucPlane).continuous₂
    |>.measurable.comp (hA.prodMk hS)).norm

lemma measurable_unstableComponentGrowth
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) (n : ℕ) :
    Measurable (unstableComponentGrowth T T_inv n) := by
  have hA : Measurable fun x => fderiv ℝ (T_inv^[n]) x :=
    ((contDiff_iterate T_inv hT_inv_smooth n).continuous_fderiv
      (by norm_num)).measurable
  have hU := measurable_lyapunovUnstableComponent
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
  exact ((ContinuousLinearMap.compL ℝ EucPlane EucPlane EucPlane).continuous₂
    |>.measurable.comp (hA.prodMk hU)).norm

lemma exists_nat_mul_exp_bound_of_eventually
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (rate : ℝ)
    (h : ∀ᶠ n : ℕ in atTop, f n ≤ Real.exp (rate * n)) :
    ∃ C : ℕ, ∀ n, f n ≤ C * Real.exp (rate * n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  let A : ℝ := 1 + ∑ n ∈ Finset.range N, f n / Real.exp (rate * n)
  obtain ⟨C, hC⟩ := exists_nat_ge A
  refine ⟨C, fun n => ?_⟩
  by_cases hn : N ≤ n
  · have hC_one : (1 : ℝ) ≤ C := by
      calc
        (1 : ℝ) ≤ A := by
          dsimp [A]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
            div_nonneg (hf i) (Real.exp_pos _).le)
        _ ≤ C := hC
    calc
      f n ≤ Real.exp (rate * n) := hN n hn
      _ ≤ C * Real.exp (rate * n) := by
        exact (le_mul_iff_one_le_left (Real.exp_pos _)).2 hC_one
  · have hnN : n < N := lt_of_not_ge hn
    have hnmem : n ∈ Finset.range N := Finset.mem_range.mpr hnN
    have hterm : f n / Real.exp (rate * n) ≤
        ∑ i ∈ Finset.range N, f i / Real.exp (rate * i) :=
      Finset.single_le_sum
        (fun i _ => div_nonneg (hf i)
          (Real.exp_pos (rate * (i : ℝ))).le) hnmem
    have hratio : f n / Real.exp (rate * n) ≤ C := by
      calc
        f n / Real.exp (rate * n) ≤
            ∑ i ∈ Finset.range N, f i / Real.exp (rate * i) := hterm
        _ ≤ A := by
          dsimp [A]
          linarith
        _ ≤ C := hC
    exact (div_le_iff₀ (Real.exp_pos _)).mp hratio

def pesinContractionBlock
    (T T_inv : EucPlane → EucPlane)
    (lam1 lam2 eta : ℝ) (C : ℕ) : Set EucPlane :=
  {x | ∀ n : ℕ,
    stableComponentGrowth T T_inv n x ≤
        C * Real.exp ((lam2 + 6 * eta) * n) ∧
    unstableComponentGrowth T T_inv n x ≤
        C * Real.exp ((-lam1 + 6 * eta) * n)}

lemma measurableSet_pesinContractionBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (lam1 lam2 eta : ℝ) (C : ℕ) :
    MeasurableSet (pesinContractionBlock T T_inv lam1 lam2 eta C) := by
  have hstable (n : ℕ) : MeasurableSet {x |
      stableComponentGrowth T T_inv n x ≤
        C * Real.exp ((lam2 + 6 * eta) * n)} :=
    measurableSet_le
      (measurable_stableComponentGrowth T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n) measurable_const
  have hunstable (n : ℕ) : MeasurableSet {x |
      unstableComponentGrowth T T_inv n x ≤
        C * Real.exp ((-lam1 + 6 * eta) * n)} :=
    measurableSet_le
      (measurable_unstableComponentGrowth T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n) measurable_const
  have heq : pesinContractionBlock T T_inv lam1 lam2 eta C =
      ⋂ n : ℕ, {x |
        stableComponentGrowth T T_inv n x ≤
          C * Real.exp ((lam2 + 6 * eta) * n)} ∩
        {x | unstableComponentGrowth T T_inv n x ≤
          C * Real.exp ((-lam1 + 6 * eta) * n)} := by
    ext x
    simp [pesinContractionBlock]
  rw [heq]
  exact MeasurableSet.iInter fun n => (hstable n).inter (hunstable n)

lemma monotone_pesinContractionBlock
    (T T_inv : EucPlane → EucPlane) (lam1 lam2 eta : ℝ) :
    Monotone (pesinContractionBlock T T_inv lam1 lam2 eta) := by
  intro C D hCD x hx n
  constructor
  · exact (hx n).1.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCD) (Real.exp_nonneg _))
  · exact (hx n).2.trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hCD) (Real.exp_nonneg _))

theorem ae_mem_iUnion_pesinContractionBlock
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
      pesinContractionBlock T T_inv lam1 lam2 eta C := by
  have hstable :=
    ae_eventually_norm_fderiv_comp_lyapunovStableComponent_le_exp
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta
        hstable_neg hunstable_neg hrate
  have hunstable :=
    ae_eventually_norm_fderiv_inverse_comp_lyapunovUnstableComponent_le_exp
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta
        hstable_neg hunstable_neg hrate
  filter_upwards [hstable, hunstable] with x hxstable hxunstable
  obtain ⟨Cs, hCs⟩ := exists_nat_mul_exp_bound_of_eventually
    (fun n => stableComponentGrowth T T_inv n x)
    (fun _ => norm_nonneg _) (lam2 + 6 * eta) hxstable
  obtain ⟨Cu, hCu⟩ := exists_nat_mul_exp_bound_of_eventually
    (fun n => unstableComponentGrowth T T_inv n x)
    (fun _ => norm_nonneg _) (-lam1 + 6 * eta) hxunstable
  refine Set.mem_iUnion.mpr ⟨max Cs Cu, ?_⟩
  intro n
  constructor
  · exact (hCs n).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_left Cs Cu) (Real.exp_nonneg _))
  · exact (hCu n).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast le_max_right Cs Cu) (Real.exp_nonneg _))

theorem tendsto_measureReal_compl_pesinContractionBlock_zero
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
      (pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ)
      atTop (nhds 0) := by
  have hfull := ae_mem_iUnion_pesinContractionBlock
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have hfullUnion : mu (⋃ C : ℕ,
      pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ = 0 :=
    mem_ae_iff.mp hfull
  have hinter : ⋂ C : ℕ,
      (pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ =
        (⋃ C : ℕ, pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ := by
    simp
  have hmeasure := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun C => (measurableSet_pesinContractionBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C).compl.nullMeasurableSet)
    (fun C D hCD => Set.compl_subset_compl.mpr
      (monotone_pesinContractionBlock T T_inv lam1 lam2 eta hCD))
    ⟨0, measure_ne_top mu _⟩
  rw [hinter, hfullUnion] at hmeasure
  change Tendsto (fun C : ℕ =>
      (mu (pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ).toReal)
    atTop (nhds 0)
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun C => measure_ne_top mu
      (pesinContractionBlock T T_inv lam1 lam2 eta C)ᶜ)).2 hmeasure

end Submission.Helpers
