import Submission.HyperbolicUpper

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

theorem exists_ae_eventually_balanced_nonlinear_orbit_control_of_dominated_rates
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {actual1 actual2 lam1 lam2 epsilon : ℝ}
    (hactual1 : actual1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hactual2 : actual2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hactual1_nonneg : 0 ≤ actual1) (hactual2_nonpos : actual2 ≤ 0)
    (hdom1 : actual1 < lam1) (hdom2 : lam2 < actual2)
    (hepsilon : 0 < epsilon) :
    ∃ q : NNReal, 0 < q ∧ q < 1 ∧
      ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
        ∀ y ∈ K,
          dist x y ≤ Real.exp
              (-(hyperbolicRate lam1 lam2 + epsilon) * L) →
            (∀ j : Fin (balancedForward lam1 lam2 L),
              dist (T^[j.val] x) (T^[j.val] y) <
                geometricBoundaryScale q L) ∧
            ∀ k, 0 < k → k ≤ balancedBackward lam1 lam2 L →
              dist (T_inv^[k] x) (T_inv^[k] y) <
                geometricBoundaryScale q L := by
  have hlam1_pos : 0 < lam1 := hactual1_nonneg.trans_lt hdom1
  have hlam2_neg : lam2 < 0 := hdom2.trans_le hactual2_nonpos
  let rhoF : ℝ := (lam1 - actual1) / 2
  let rhoB : ℝ := (actual2 - lam2) / 2
  let s : ℝ := 3 * epsilon / 4
  let t : ℝ := epsilon / 2
  let q : NNReal := ⟨Real.exp (-t), Real.exp_nonneg _⟩
  have hrhoF : 0 < rhoF := div_pos (sub_pos.mpr hdom1) (by norm_num)
  have hrhoB : 0 < rhoB := div_pos (sub_pos.mpr hdom2) (by norm_num)
  have hgrowthF : actual1 + rhoF ≤ lam1 := by
    dsimp [rhoF]
    linarith
  have hgrowthB : -actual2 + rhoB ≤ -lam2 := by
    dsimp [rhoB]
    linarith
  have hgrowthF_nonneg : 0 ≤ actual1 + rhoF :=
    add_nonneg hactual1_nonneg hrhoF.le
  have hgrowthB_nonneg : 0 ≤ -actual2 + rhoB :=
    add_nonneg (neg_nonneg.mpr hactual2_nonpos) hrhoB.le
  have hs : 0 < s := by
    dsimp [s]
    linarith
  have hts : t < s := by
    dsimp [t, s]
    linarith
  have hq_pos : 0 < q := by
    change 0 < Real.exp (-t)
    positivity
  have hq_lt : q < 1 := by
    change Real.exp (-t) < 1
    exact (Real.exp_lt_one_iff).2 (by dsimp [t]; linarith)
  have hT_inv := measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right mu hT
  have hErg_inv := ergodic_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right mu hErg
  have hK_inv_inv : T_inv '' K = K := inverse_image_eq_of_image_eq hT_left hK_inv
  obtain ⟨deltaF, hdeltaF, hforward⟩ := exists_ae_nonlinear_orbit_growth
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hactual1 hrhoF
  have hactual_inv : -actual2 = ∫ x, lyapunovUpperAt T_inv x ∂mu := by
    calc
      -actual2 = -∫ x, lyapunovLowerAt T x ∂mu := congrArg Neg.neg hactual2
      _ = ∫ x, lyapunovUpperAt T_inv x ∂mu :=
        (integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right K hK_compact
            hK_inv mu hmu_supp hT hErg).symm
  obtain ⟨deltaB, hdeltaB, hbackward⟩ := exists_ae_nonlinear_orbit_growth
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
      hactual_inv hrhoB
  refine ⟨q, hq_pos, hq_lt, ?_⟩
  filter_upwards [hforward, hbackward] with x hxforward hxbackward
  obtain ⟨GF, hGF, hxforward⟩ := hxforward
  obtain ⟨GB, hGB, hxbackward⟩ := hxbackward
  have hsmallF := eventually_exp_neg_mul_add_lt hs hdeltaF (lam1 + GF)
  have hsmallB := eventually_exp_neg_mul_add_lt hs hdeltaB GB
  have hgeomF :=
    eventually_exp_neg_mul_add_lt_geometricBoundaryScale hts (lam1 + GF)
  have hgeomB := eventually_exp_neg_mul_add_lt_geometricBoundaryScale hts GB
  filter_upwards [hsmallF, hsmallB, hgeomF, hgeomB]
    with L hLFsmall hLBsmall hLFgeom hLBgeom
  intro y hyK hxy
  have hforward_budget :
      lam1 * balancedForward lam1 lam2 L ≤
        hyperbolicRate lam1 lam2 * L + lam1 :=
    forward_budget_le_hyperbolicRate_add hlam1_pos hlam2_neg L
  have hbackward_budget :
      (-lam2) * balancedBackward lam1 lam2 L ≤
        hyperbolicRate lam1 lam2 * L :=
    backward_budget_le_hyperbolicRate hlam1_pos hlam2_neg L
  constructor
  · intro j
    have hjL : j.val ≤ L :=
      (Nat.le_of_lt j.isLt).trans (Nat.sub_le _ _)
    have hjbudget : (actual1 + rhoF) * j.val ≤
        hyperbolicRate lam1 lam2 * L + lam1 := by
      have hjcast : (j.val : ℝ) ≤ balancedForward lam1 lam2 L := by
        exact_mod_cast Nat.le_of_lt j.isLt
      calc
        (actual1 + rhoF) * j.val ≤
            lam1 * j.val := mul_le_mul_of_nonneg_right hgrowthF
              (Nat.cast_nonneg _)
        _ ≤ lam1 * balancedForward lam1 lam2 L :=
          mul_le_mul_of_nonneg_left hjcast hlam1_pos.le
        _ ≤ hyperbolicRate lam1 lam2 * L + lam1 := hforward_budget
    have hexponent :
        -(hyperbolicRate lam1 lam2 + epsilon) * L +
            ((actual1 + rhoF) * j.val + GF) ≤
          -s * L + (lam1 + GF) := by
      dsimp [s]
      have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith
    have hinit : dist x y * Real.exp
        ((actual1 + rhoF) * j.val + GF) ≤ deltaF := by
      calc
        dist x y * Real.exp ((actual1 + rhoF) * j.val + GF) ≤
            Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L) *
              Real.exp ((actual1 + rhoF) * j.val + GF) :=
          mul_le_mul_of_nonneg_right hxy (Real.exp_nonneg _)
        _ = Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L +
              ((actual1 + rhoF) * j.val + GF)) :=
          (Real.exp_add _ _).symm
        _ ≤ Real.exp (-s * L + (lam1 + GF)) :=
          Real.exp_le_exp.mpr hexponent
        _ ≤ deltaF := hLFsmall.le
    have hjgrowth := hxforward j.val y hyK (by
      simpa [max_eq_right (mul_nonneg hgrowthF_nonneg
        (Nat.cast_nonneg j.val))] using hinit)
    calc
      dist (T^[j.val] x) (T^[j.val] y) ≤
          Real.exp ((actual1 + rhoF) * j.val + GF) * dist x y := hjgrowth
      _ ≤ Real.exp ((actual1 + rhoF) * j.val + GF) *
          Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L) :=
        mul_le_mul_of_nonneg_left hxy (Real.exp_nonneg _)
      _ = Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L +
            ((actual1 + rhoF) * j.val + GF)) := by
        rw [mul_comm, ← Real.exp_add]
      _ ≤ Real.exp (-s * L + (lam1 + GF)) :=
        Real.exp_le_exp.mpr hexponent
      _ < geometricBoundaryScale q L := hLFgeom
  · intro k hk_pos hk_le
    have hkL : k ≤ L := hk_le.trans (balancedBackward_le hlam1_pos hlam2_neg L)
    have hkbudget : (-actual2 + rhoB) * k ≤
        hyperbolicRate lam1 lam2 * L := by
      calc
        (-actual2 + rhoB) * k ≤ (-lam2) * k :=
          mul_le_mul_of_nonneg_right hgrowthB (Nat.cast_nonneg _)
        _ ≤ (-lam2) * balancedBackward lam1 lam2 L :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hk_le)
            (neg_pos.mpr hlam2_neg).le
        _ ≤ hyperbolicRate lam1 lam2 * L := hbackward_budget
    have hexponent :
        -(hyperbolicRate lam1 lam2 + epsilon) * L +
            ((-actual2 + rhoB) * k + GB) ≤ -s * L + GB := by
      dsimp [s]
      have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith
    have hinit : dist x y * Real.exp ((-actual2 + rhoB) * k + GB) ≤
        deltaB := by
      calc
        dist x y * Real.exp ((-actual2 + rhoB) * k + GB) ≤
            Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L) *
              Real.exp ((-actual2 + rhoB) * k + GB) :=
          mul_le_mul_of_nonneg_right hxy (Real.exp_nonneg _)
        _ = Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L +
              ((-actual2 + rhoB) * k + GB)) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-s * L + GB) := Real.exp_le_exp.mpr hexponent
        _ ≤ deltaB := hLBsmall.le
    have hkgrowth := hxbackward k y hyK (by
      simpa [max_eq_right (mul_nonneg hgrowthB_nonneg
        (Nat.cast_nonneg k))] using hinit)
    calc
      dist (T_inv^[k] x) (T_inv^[k] y) ≤
          Real.exp ((-actual2 + rhoB) * k + GB) * dist x y := hkgrowth
      _ ≤ Real.exp ((-actual2 + rhoB) * k + GB) *
          Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L) :=
        mul_le_mul_of_nonneg_left hxy (Real.exp_nonneg _)
      _ = Real.exp (-(hyperbolicRate lam1 lam2 + epsilon) * L +
            ((-actual2 + rhoB) * k + GB)) := by
        rw [mul_comm, ← Real.exp_add]
      _ ≤ Real.exp (-s * L + GB) := Real.exp_le_exp.mpr hexponent
      _ < geometricBoundaryScale q L := hLBgeom

theorem kolmogorovSinaiEntropy_sub_le_dimMeasure_mul_dominated_rate_add
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu] [NoAtoms mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {actual1 actual2 lam1 lam2 epsilon : ℝ}
    (hactual1 : actual1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hactual2 : actual2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hactual1_nonneg : 0 ≤ actual1) (hactual2_nonpos : actual2 ≤ 0)
    (hdom1 : actual1 < lam1) (hdom2 : lam2 < actual2)
    (hepsilon : 0 < epsilon) :
    kolmogorovSinaiEntropy mu T - epsilon ≤
      (dimMeasure mu).toReal *
        (hyperbolicRate lam1 lam2 + epsilon) := by
  have hlam1_pos : 0 < lam1 := hactual1_nonneg.trans_lt hdom1
  have hlam2_neg : lam2 < 0 := hdom2.trans_le hactual2_nonpos
  have hT_inv := measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right mu hT
  have hErg_inv := ergodic_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right mu hErg
  obtain ⟨carrier, hcarrier_measurable, hcarrier_full,
      hcarrier_invariant, hcarrierK, hcarrier_dim⟩ :=
    exists_invariant_full_measure_dimMeasure_subset
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp
  obtain ⟨q, hq_pos, hq_lt, horbitK⟩ :=
    exists_ae_eventually_balanced_nonlinear_orbit_control_of_dominated_rates
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hactual1 hactual2 hactual1_nonneg hactual2_nonpos
        hdom1 hdom2 hepsilon
  have horbit : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ y ∈ carrier,
        dist x y ≤ Real.exp
            (-(hyperbolicRate lam1 lam2 + epsilon) * L) →
          (∀ j : Fin (balancedForward lam1 lam2 L),
            dist (T^[j.val] x) (T^[j.val] y) <
              geometricBoundaryScale q L) ∧
          ∀ k, 0 < k → k ≤ balancedBackward lam1 lam2 L →
            dist (T_inv^[k] x) (T_inv^[k] y) <
              geometricBoundaryScale q L := by
    filter_upwards [horbitK] with x hx
    filter_upwards [hx] with L hL
    intro y hy
    exact hL y (hcarrierK hy)
  exact kolmogorovSinaiEntropy_sub_le_dimMeasure_mul_rate_of_orbit_control
    mu T T_inv hT_left hT_right hT hT_inv hErg hErg_inv
      hK_compact hcarrier_measurable hcarrier_full hcarrier_invariant
      hcarrierK hcarrier_dim
      (dimMeasure_ne_top_of_compact_full_measure mu hK_compact hmu_supp)
      q hq_pos hq_lt hlam1_pos hlam2_neg hepsilon
      (add_pos (hyperbolicRate_pos hlam1_pos hlam2_neg) hepsilon) horbit

lemma hyperbolicRate_le_left
    {lam1 lam2 : ℝ} (hlam1 : 0 ≤ lam1) (hlam2 : lam2 ≤ 0)
    (hne : lam1 - lam2 ≠ 0) :
    hyperbolicRate lam1 lam2 ≤ lam1 := by
  have hdenom : 0 < lam1 - lam2 := by
    exact lt_of_le_of_ne (sub_nonneg.mpr (hlam2.trans hlam1)) (Ne.symm hne)
  rw [hyperbolicRate]
  apply (div_le_iff₀ hdenom).2
  nlinarith

lemma hyperbolicRate_le_neg_right
    {lam1 lam2 : ℝ} (hlam1 : 0 ≤ lam1) (hlam2 : lam2 ≤ 0)
    (hne : lam1 - lam2 ≠ 0) :
    hyperbolicRate lam1 lam2 ≤ -lam2 := by
  have hdenom : 0 < lam1 - lam2 := by
    exact lt_of_le_of_ne (sub_nonneg.mpr (hlam2.trans hlam1)) (Ne.symm hne)
  rw [hyperbolicRate]
  apply (div_le_iff₀ hdenom).2
  nlinarith

theorem kolmogorovSinaiEntropy_eq_zero_of_zero_lyapunov
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu] [NoAtoms mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_nonneg : 0 ≤ lam1) (hlam2_nonpos : lam2 ≤ 0)
    (hzero : lam1 = 0 ∨ lam2 = 0) :
    kolmogorovSinaiEntropy mu T = 0 := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    let t := epsilon / 6
    have ht : 0 < t := div_pos hepsilon (by norm_num)
    have hdim : (dimMeasure mu).toReal ≤ 2 :=
      dimMeasure_toReal_le_two mu hK_compact hmu_supp
    rcases hzero with hlam1_zero | hlam2_zero
    · let upper := t
      let lower := lam2 - t
      have hdom1 : lam1 < upper := by simp [upper, hlam1_zero, ht]
      have hdom2 : lower < lam2 := by dsimp [lower]; linarith
      have hlower_nonpos : lower ≤ 0 := by dsimp [lower]; linarith
      have hrate : hyperbolicRate upper lower ≤ upper :=
        hyperbolicRate_le_left ht.le hlower_nonpos (by
          dsimp [upper, lower]
          linarith)
      have hbound :=
        kolmogorovSinaiEntropy_sub_le_dimMeasure_mul_dominated_rate_add
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right
            K hK_compact hK_inv mu hmu_supp hT hErg
            hlam1 hlam2 hlam1_nonneg hlam2_nonpos hdom1 hdom2 ht
      dsimp [upper, t] at hrate hbound
      have hdim_nonneg : 0 ≤ (dimMeasure mu).toReal := ENNReal.toReal_nonneg
      nlinarith
    · let upper := lam1 + t
      let lower := -t
      have hdom1 : lam1 < upper := by dsimp [upper]; linarith
      have hdom2 : lower < lam2 := by simp [lower, hlam2_zero, ht]
      have hupper_nonneg : 0 ≤ upper := by dsimp [upper]; linarith
      have hrate : hyperbolicRate upper lower ≤ -lower :=
        hyperbolicRate_le_neg_right hupper_nonneg (by dsimp [lower]; linarith)
          (by dsimp [upper, lower]; linarith)
      have hbound :=
        kolmogorovSinaiEntropy_sub_le_dimMeasure_mul_dominated_rate_add
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right
            K hK_compact hK_inv mu hmu_supp hT hErg
            hlam1 hlam2 hlam1_nonneg hlam2_nonpos hdom1 hdom2 ht
      dsimp [lower, t] at hrate hbound
      have hdim_nonneg : 0 ≤ (dimMeasure mu).toReal := ENNReal.toReal_nonneg
      nlinarith
  · exact kolmogorovSinaiEntropy_nonneg mu T

end Submission.Helpers
