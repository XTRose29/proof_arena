import Submission.HyperbolicUpper
import Submission.SparseShiftedHausdorff
import Submission.GlobalOrbitGeometry
import Submission.DerivativeDistortion

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

lemma entropyW_le_kolmogorovSinaiEntropy_of_hyperbolic
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
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P) :
    entropyW mu T P ≤ kolmogorovSinaiEntropy mu T := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  obtain ⟨carrier, hcarrier_measurable, hcarrier_full,
      hcarrier_invariant, hcarrierK, hcarrier_dim⟩ :=
    exists_invariant_full_measure_dimMeasure_subset
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp
  obtain ⟨q, hq_pos, hq_lt, horbitK⟩ :=
    exists_ae_eventually_balanced_nonlinear_orbit_control
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg (by norm_num : (0 : ℝ) < 1)
  have horbit : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ y ∈ carrier,
        dist x y ≤ Real.exp
            (-(hyperbolicRate lam1 lam2 + 1) * L) →
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
  let S : Set ℝ := {h | ∃ Q : Finset (Set EucPlane),
    IsMeasurablePartition mu Q ∧ entropyW mu T Q = h}
  have hSbdd : BddAbove S := by
    refine ⟨(dimMeasure mu).toReal *
        (hyperbolicRate lam1 lam2 + 1) + 1, ?_⟩
    rintro h ⟨Q, hQ, rfl⟩
    have hbound := entropyW_sub_le_dimMeasure_mul_rate_of_orbit_control
      mu T T_inv hT_left hT_right hT hT_inv hErg hErg_inv
        hK_compact hcarrier_measurable hcarrier_full hcarrier_invariant
        hcarrierK hcarrier_dim
        (dimMeasure_ne_top_of_compact_full_measure mu hK_compact hmu_supp)
        q hq_pos hq_lt hlam1_pos hlam2_neg
        (by norm_num : (0 : ℝ) < 1)
        (add_pos (hyperbolicRate_pos hlam1_pos hlam2_neg)
          (by norm_num : (0 : ℝ) < 1))
        horbit Q hQ
    linarith
  unfold kolmogorovSinaiEntropy
  exact le_csSup hSbdd ⟨P, hP, rfl⟩

lemma exists_pos_mul_le_three
    {a b c u v w : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    ∃ delta : ℝ, 0 < delta ∧
      a * delta ≤ u ∧ b * delta ≤ v ∧ c * delta ≤ w := by
  let delta := min (u / a) (min (v / b) (w / c)) / 2
  have hua : 0 < u / a := div_pos hu ha
  have hvb : 0 < v / b := div_pos hv hb
  have hwc : 0 < w / c := div_pos hw hc
  have hmin : 0 < min (u / a) (min (v / b) (w / c)) :=
    lt_min hua (lt_min hvb hwc)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta_min :
      delta ≤ min (u / a) (min (v / b) (w / c)) := by
    dsimp [delta]
    linarith
  refine ⟨delta, hdelta, ?_, ?_, ?_⟩
  · have hle : delta ≤ u / a :=
      hdelta_min.trans (min_le_left _ _)
    have := (le_div_iff₀ ha).mp hle
    simpa [mul_comm] using this
  · have hle : delta ≤ v / b :=
      hdelta_min.trans ((min_le_right _ _).trans (min_le_left _ _))
    have := (le_div_iff₀ hb).mp hle
    simpa [mul_comm] using this
  · have hle : delta ≤ w / c :=
      hdelta_min.trans ((min_le_right _ _).trans (min_le_right _ _))
    have := (le_div_iff₀ hc).mp hle
    simpa [mul_comm] using this

lemma exists_sparse_geometry_constants
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    (K : Set EucPlane) (hK_compact : IsCompact K)
    (lam2 eta : ℝ) :
    ∃ S : Set EucPlane, ∃ Lip : ℝ, ∃ D : ℕ,
      K ⊆ S ∧ Convex ℝ S ∧ 1 ≤ Lip ∧
      (∀ x ∈ K, ∀ y ∈ K,
        dist (T x) (T y) ≤ Lip * dist x y) ∧
      (∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ Lip) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ Lip * dist x y) ∧
      0 < D ∧
      2 * (1 : ℝ) ≤ 4 ^ D ∧
      Lip ≤ 4 ^ D ∧
      4 * (1 : ℝ) * Lip ^ 2 ≤ 4 ^ D ∧
      4 * Lip ^ 2 * Real.exp (-(lam2 + 6 * eta)) ≤ 4 ^ D := by
  obtain ⟨R, hKR⟩ :=
    hK_compact.isBounded.subset_closedBall (0 : EucPlane)
  let S := Metric.closedBall (0 : EucPlane) R
  have hS_compact : IsCompact S := isCompact_closedBall _ _
  have hS_convex : Convex ℝ S := convex_closedBall _ _
  obtain ⟨Lmap, hLmap, hmap⟩ :=
    exists_lipschitz_constant_on_compact T hT_smooth hK_compact
  obtain ⟨Lder, hLder, hder⟩ :=
    compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨Ldiff, hLdiff, hdiff⟩ :=
    exists_fderiv_lipschitz_constant_on_compact_convex
      T hT_smooth hS_compact hS_convex
  let Lip := max Lmap (max Lder Ldiff)
  have hLmapLip : Lmap ≤ Lip := le_max_left _ _
  have hLderLip : Lder ≤ Lip :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hLdiffLip : Ldiff ≤ Lip :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hLip : 1 ≤ Lip := hLmap.trans hLmapLip
  have hmapLip : ∀ x ∈ K, ∀ y ∈ K,
      dist (T x) (T y) ≤ Lip * dist x y := by
    intro x hx y hy
    exact (hmap x hx y hy).trans
      (mul_le_mul_of_nonneg_right hLmapLip (dist_nonneg.trans le_rfl))
  have hderLip : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ Lip := by
    intro x hx
    exact (hder x hx).trans hLderLip
  have hdiffLip : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ Lip * dist x y := by
    intro x hx y hy
    exact (hdiff x hx y hy).trans
      (mul_le_mul_of_nonneg_right hLdiffLip (dist_nonneg.trans le_rfl))
  let target : ℝ :=
    max 2 (max Lip
      (max (4 * Lip ^ 2)
        (4 * Lip ^ 2 * Real.exp (-(lam2 + 6 * eta)))))
  have hpow : Tendsto (fun D : ℕ => (4 : ℝ) ^ D) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlarge : ∀ᶠ D : ℕ in atTop, target ≤ (4 : ℝ) ^ D :=
    (tendsto_atTop.1 hpow target)
  obtain ⟨D, hDlarge, hDpos⟩ :=
    (hlarge.and (eventually_gt_atTop 0)).exists
  dsimp [target] at hDlarge
  refine ⟨S, Lip, D, hKR, hS_convex, hLip, hmapLip, hderLip,
    hdiffLip, hDpos, ?_, ?_, ?_, ?_⟩
  · simpa using (le_max_left _ _).trans hDlarge
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hDlarge
  · simpa using (((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hDlarge
  · exact (((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hDlarge

lemma exists_sparse_spacing
    {lam1 lam2 eta kappa rho : ℝ} (C : ℕ)
    (heta : 0 < eta) (hkappa : 0 < kappa)
    (hab : lam2 + 6 * eta + (-lam1 + 6 * eta) < 0) :
    ∃ H : ℕ, 0 < H ∧
      2 * Real.log 2 / H ≤ kappa / 2 ∧
      Real.log rho ≤ eta * H ∧
      (4 * C : ℝ) * rho *
          Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) ≤
        1 / 4 ∧
      (C : ℝ) *
          Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) ≤
        1 / 2 := by
  let a := lam2 + 6 * eta + (-lam1 + 6 * eta)
  have ha : a < 0 := by simpa [a] using hab
  have harg : Tendsto (fun H : ℕ => a * (H : ℝ)) atTop atBot :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg ha
  have hexp : Tendsto (fun H : ℕ => Real.exp (a * (H : ℝ)))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hcross : Tendsto
      (fun H : ℕ => (4 * C : ℝ) * rho * Real.exp (a * (H : ℝ)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hexp
  have hunstable : Tendsto
      (fun H : ℕ => (C : ℝ) * Real.exp (a * (H : ℝ)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hexp
  have hgrid : Tendsto (fun H : ℕ => 2 * Real.log 2 / H)
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 * Real.log 2)
  have hlinear : Tendsto (fun H : ℕ => eta * (H : ℝ))
      atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop heta
  have hevent : ∀ᶠ H : ℕ in atTop,
      0 < H ∧
      2 * Real.log 2 / H ≤ kappa / 2 ∧
      Real.log rho ≤ eta * H ∧
      (4 * C : ℝ) * rho *
          Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) ≤
        1 / 4 ∧
      (C : ℝ) *
          Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) ≤
        1 / 2 := by
    filter_upwards [
      eventually_gt_atTop 0,
      (tendsto_order.1 hgrid).2 (kappa / 2) (by linarith),
      tendsto_atTop.1 hlinear (Real.log rho),
      (tendsto_order.1 hcross).2 (1 / 4) (by norm_num),
      (tendsto_order.1 hunstable).2 (1 / 2) (by norm_num)]
      with H hH hgridH hlogH hcrossH hunstableH
    exact ⟨hH, hgridH.le, hlogH, by simpa [a] using hcrossH.le,
      by simpa [a] using hunstableH.le⟩
  exact hevent.exists

set_option maxHeartbeats 8000000 in
theorem dimMeasure_le_of_hyperbolic_sparse_covers
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu] [NoAtoms mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta alpha kappa : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hstable : lam2 + 6 * eta < 0)
    (hunstable : -lam1 + 6 * eta < 0)
    (hrate_eta : 8 * eta < hyperbolicRate lam1 lam2)
    (halpha : 0 < alpha) (halpha_lt : alpha < 1)
    (hkappa : 0 < kappa)
    (d : NNReal)
    (hrate :
      kolmogorovSinaiEntropy mu T / alpha + kappa <
        (hyperbolicRate lam1 lam2 - 8 * eta) * (d : ℝ)) :
    dimMeasure mu ≤ d := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  obtain ⟨carrier, hcarrier_measurable, hcarrier_full,
      hcarrier, hcarrierK, hsource, hcov, _hdet⟩ :=
    exists_pesinStructuralCarrier
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta
        (by linarith) (by linarith) (by linarith) hrate_eta
  obtain ⟨S, Lip, D, hKS, hS_convex, hLip, hT_lipschitz,
      hderiv, hderiv_lipschitz, hDpos, hscaleR, hscaleLip,
      hscaleConst, hscaleRate⟩ :=
    exists_sparse_geometry_constants T hT_smooth K hK_compact lam2 eta
  obtain ⟨F, hFnet⟩ := exists_quarter_unit_net
  have hF : F.Nonempty := by
    obtain ⟨f, hf, _hzero⟩ := hFnet 0 (by simp)
    exact ⟨f, hf⟩
  have hFcard : 0 < F.card := Finset.card_pos.mpr hF
  have hFcard_one : (1 : ℝ) ≤ F.card := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hFcard.ne')
  have hlogF : 0 ≤ Real.log F.card :=
    Real.log_nonneg hFcard_one
  let gamma0 := (1 - alpha) / 8
  have hgamma0 : 0 < gamma0 := by
    dsimp [gamma0]
    linarith
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hdenom :
      0 < (16 : ℝ) * D * (Real.log F.card + 1) := by
    positivity
  let q := min (1 / 2 : ℝ)
    (kappa / ((16 : ℝ) * D * (Real.log F.card + 1)))
  have hq : 0 < q := by
    dsimp [q]
    exact lt_min (by norm_num) (div_pos hkappa hdenom)
  have hq_half : q ≤ 1 / 2 := by
    exact min_le_left _ _
  have hq_one : q ≤ 1 := hq_half.trans (by norm_num)
  have hq_frac :
      q ≤ kappa / ((16 : ℝ) * D * (Real.log F.card + 1)) := by
    exact min_le_right _ _
  have hq_budget :
      q * ((16 : ℝ) * D * (Real.log F.card + 1)) ≤ kappa :=
    (le_div_iff₀ hdenom).mp hq_frac
  have hlabel :
      (8 : ℝ) * D * q * Real.log F.card ≤ kappa / 2 := by
    calc
      (8 : ℝ) * D * q * Real.log F.card ≤
          8 * D * q * (Real.log F.card + 1) := by
        gcongr
        linarith
      _ = (q * (16 * D * (Real.log F.card + 1))) / 2 := by ring
      _ ≤ kappa / 2 := by gcongr
  have hmeasure :=
    tendsto_measureReal_compl_pesinFullShadowingBlock_zero
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta
        (by linarith) (by linarith) (by linarith) hrate_eta
  have hqgamma : 0 < q * gamma0 := mul_pos hq hgamma0
  have hsmall : ∀ᶠ C : ℕ in atTop,
      mu.real
          (pesinFullShadowingBlock T T_inv lam1 lam2 eta C)ᶜ <
        q * gamma0 :=
    (tendsto_order.1 hmeasure).2 _ hqgamma
  obtain ⟨C, hCsmall⟩ := hsmall.exists
  let G := pesinFullShadowingBlock T T_inv lam1 lam2 eta C
  have hG : MeasurableSet G :=
    measurableSet_pesinFullShadowingBlock
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        lam1 lam2 eta C
  have hGsmall : mu.real Gᶜ < q * gamma0 := by
    simpa [G] using hCsmall
  have hGcompl : mu.real Gᶜ ≤ gamma0 := by
    calc
      mu.real Gᶜ ≤ q * gamma0 := hGsmall.le
      _ ≤ 1 * gamma0 :=
        mul_le_mul_of_nonneg_right hq_one hgamma0.le
      _ = gamma0 := one_mul _
  let rho := max 1 (16 * (C : ℝ))
  have hrho : 1 ≤ rho := le_max_left _ _
  have hrho_pos : 0 < rho := zero_lt_one.trans_le hrho
  have hCrho : (16 : ℝ) * C ≤ rho := le_max_right _ _
  have hAq : (4 * C : ℝ) / rho ≤ 1 / 4 := by
    apply (div_le_iff₀ hrho_pos).2
    nlinarith
  have hab : lam2 + 6 * eta + (-lam1 + 6 * eta) < 0 := by
    linarith
  obtain ⟨H, hH, hgrid, hlog, hcrossH, hunstableH⟩ :=
    exists_sparse_spacing C heta hkappa hab (rho := rho)
  have hprefixMax :
      q * mu.real (maximalForwardBadPrefixBlock (T^[H]) G q)ᶜ ≤
        mu.real Gᶜ :=
    mul_measureReal_compl_maximalForwardBadPrefixBlock_le
      mu (T^[H]) (hT.iterate H) hG hq.le
  have hprefix :
      mu.real (maximalForwardBadPrefixBlock (T^[H]) G q)ᶜ ≤
        gamma0 := by
    nlinarith
  let a1 : ℝ := Lip ^ H
  let a2 : ℝ :=
    (H : ℝ) * Lip * Lip ^ H * (2 * Lip) ^ (H + 1)
  let a3 : ℝ :=
    Lip ^ H * 2 *
      Real.exp ((-lam2) * (H + 1) + lam1 * H + eta * H)
  have ha1 : 0 < a1 := by
    dsimp [a1]
    positivity
  have ha2 : 0 < a2 := by
    dsimp [a2]
    positivity
  have ha3 : 0 < a3 := by
    dsimp [a3]
    positivity
  obtain ⟨delta, hdelta, hshort_small', hshort_error', hconstant'⟩ :=
    exists_pos_mul_le_three ha1 ha2 ha3
      (by norm_num : (0 : ℝ) < 1)
      (Real.exp_pos ((lam2 + 6 * eta) * H))
      (by norm_num : (0 : ℝ) < 1)
  have hshort_small : Lip ^ H * delta ≤ 1 := by
    simpa [a1] using hshort_small'
  have hshort_error :
      (H : ℝ) * (Lip * (Lip ^ H * delta)) *
          (2 * Lip) ^ (H + 1) ≤
        Real.exp ((lam2 + 6 * eta) * H) := by
    calc
      (H : ℝ) * (Lip * (Lip ^ H * delta)) *
          (2 * Lip) ^ (H + 1) = a2 * delta := by
        dsimp [a2]
        ring
      _ ≤ _ := hshort_error'
  have hdelta_one : delta ≤ 1 := by
    calc
      delta = 1 * delta := (one_mul _).symm
      _ ≤ Lip ^ H * delta := by
        gcongr
        exact one_le_pow₀ hLip
      _ ≤ 1 := hshort_small
  obtain ⟨P, hP, hPsubset, hPdiamRaw⟩ :=
    exists_small_measurable_partition
      mu hK_compact hcarrier_measurable hcarrier_full hcarrierK
        (half_pos hdelta)
  have hPdiam :
      ∀ A ∈ P, Metric.ediam A ≤ ENNReal.ofReal delta := by
    intro A hA
    calc
      Metric.ediam A ≤ 2 * ENNReal.ofReal (delta / 2) :=
        hPdiamRaw A hA
      _ = ENNReal.ofReal delta := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have hentropyP :
      entropyW mu T P ≤ kolmogorovSinaiEntropy mu T :=
    entropyW_le_kolmogorovSinaiEntropy_of_hyperbolic
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg P hP
  have hrate_pos :
      0 < hyperbolicRate lam1 lam2 - 8 * eta := sub_pos.mpr hrate_eta
  have hqlinear : Tendsto (fun L : ℕ => q * (L : ℝ))
      atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hq
  have hlargeEventually : ∀ᶠ L : ℕ in atTop,
      H ≤ L ∧
      (H : ℝ) * (q + 1) ≤ q * L ∧
      0 < balancedForward lam1 lam2 L := by
    filter_upwards [
      eventually_ge_atTop H,
      tendsto_atTop.1 hqlinear ((H : ℝ) * (q + 1)),
      tendsto_atTop.1
        (tendsto_balancedForward_atTop hlam1_pos hlam2_neg) 1]
      with L hHL habsorb hforward
    exact ⟨hHL, habsorb, by omega⟩
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 hlargeEventually
  let m : ℕ → ℕ := fun j =>
    balancedBackward lam1 lam2 (j + L0)
  let nforward : ℕ → ℕ := fun j =>
    balancedForward lam1 lam2 (j + L0)
  let good : ℕ → Set EucPlane := fun j =>
    sparseWindowGoodSet T T_inv carrier G q
      (m j) (nforward j) H
  let pieces : ℕ → Set EucPlane → Finset (Set EucPlane) := fun j A =>
    sparseWindowPieces T T_inv G (good j) A F 1
      (m j) (nforward j) H D
  let M : ℕ → ℕ := fun j =>
    sparsePieceMultiplicity F.card H D q (j + L0)
  have hgood_measurable : ∀ j, MeasurableSet (good j) := by
    intro j
    exact measurableSet_sparseWindowGoodSet
      T T_inv hT.measurable hT_inv.measurable
        hcarrier_measurable hG q (m j) (nforward j) H
  have hgood_compl : ∀ j, mu.real (good j)ᶜ ≤ 4 * gamma0 := by
    intro j
    exact (measureReal_compl_sparseWindowGoodSet_le
      mu T T_inv hT hT_inv hcarrier_full hG
        (m j) (nforward j) H hprefix hGcompl).trans_eq (by ring)
  have hmass : alpha + 4 * gamma0 < 1 := by
    dsimp [gamma0]
    linarith
  have hactual :
      2 * Real.log 2 / H +
          8 * D * q * Real.log F.card ≤ kappa := by
    exact (add_le_add hgrid hlabel).trans_eq (by ring)
  have hM : ∀ j, (M j : ℝ) ≤
      Real.exp (kappa * ((j : ℝ) + (L0 : ℝ))) := by
    intro j
    have hjlarge := hL0 (j + L0) (by omega)
    have hbound := sparsePieceMultiplicity_le_exp
      (D := D) hH hjlarge.1 hFcard hq hjlarge.2.1
    calc
      (M j : ℝ) ≤
          Real.exp
            ((2 * Real.log 2 / H +
              8 * D * q * Real.log F.card) *
                ((j : ℝ) + (L0 : ℝ))) := by
        simpa [M, Nat.cast_add] using hbound
      _ ≤ Real.exp (kappa * ((j : ℝ) + (L0 : ℝ))) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hactual
          (add_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg L0))
  apply dimMeasure_le_of_shifted_balanced_uniform_piece_covers
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      mu hT hT_inv hErg P hP hlam1_pos hlam2_neg
      L0 good hgood_measurable hgood_compl pieces M
      (kappa := kappa)
      (R := hyperbolicRate lam1 lam2 - 8 * eta)
      (delta := alpha) (d := d) hM
  · intro j A hA
    have hjlarge := hL0 (j + L0) (by omega)
    have hcard := card_sparseWindowPieces_le
      T T_inv G carrier (q := q) (R := 1) A F
        (m := m j) (n := nforward j) (H := H) (D := D)
        hH hjlarge.2.2 hF
    rw [balancedBackward_add_balancedForward
      hlam1_pos hlam2_neg (j + L0)] at hcard
    simpa [pieces, good, m, nforward, M] using hcard
  · intro j A hA B hB
    have hcentered :=
      isMeasurablePartition_centeredJoin
        mu T T_inv hT hT_inv P hP (m j) (nforward j)
    exact measurableSet_of_mem_sparseWindowPieces
      T T_inv hT_smooth.continuous hT_inv_smooth.continuous
        hG (hgood_measurable j) (hcentered.1 A hA)
        F 1 (m j) (nforward j) H D hB
  · intro j A hA
    exact sparseWindowPieces_cover
      T T_inv G carrier q P hdelta.le hdelta_one hPdiam hA
        F hFnet (by norm_num)
  · intro j A hA B hB
    have hjlarge := hL0 (j + L0) (by omega)
    obtain ⟨p, _hp, hBp⟩ := Finset.mem_biUnion.mp hB
    have hconstant :
        Lip ^ H * delta * 2 *
            Real.exp ((-lam2) * (H + 1) + lam1 * H + eta * H) ≤
          Real.exp (eta * ((j + L0 : ℕ) : ℝ)) := by
      calc
        Lip ^ H * delta * 2 *
            Real.exp ((-lam2) * (H + 1) + lam1 * H + eta * H) =
            a3 * delta := by
          dsimp [a3]
          ring
        _ ≤ 1 := hconstant'
        _ ≤ Real.exp (eta * ((j + L0 : ℕ) : ℝ)) :=
          Real.one_le_exp (mul_nonneg heta.le
            (Nat.cast_nonneg (j + L0)))
    have hdiam := ediam_of_mem_sparsePatternPieces_balanced
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hK_inv hKS hS_convex hcarrier hcarrierK hsource hcov
        hLip hT_lipschitz hderiv hderiv_lipschitz
        P hdelta.le hPdiam hlam1_pos hlam2_neg heta.le hH
        hjlarge.2.2 (by norm_num : (0 : ℝ) < 1) hrho
        (G := G) (C := C) (rho := rho) (qbad := q)
        (by rfl) hab hAq hcrossH hunstableH
        hshort_small hshort_error hscaleR hscaleLip
        hscaleConst hscaleRate hlog hconstant hA F p hBp
    exact hdiam.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
      have hjle : (j : ℝ) ≤ ((j + L0 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right j L0
      exact mul_le_mul_of_nonpos_left hjle
        (neg_nonpos.mpr hrate_pos.le))))
  · exact hrate_pos
  · exact halpha
  · exact hmass
  · exact lt_of_le_of_lt
      (add_le_add
        (div_le_div_of_nonneg_right hentropyP halpha.le) le_rfl)
      hrate

set_option maxHeartbeats 4000000 in
theorem dimMeasure_mul_hyperbolicRate_sub_le_kolmogorovSinaiEntropy
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu] [NoAtoms mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 epsilon : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (hepsilon : 0 < epsilon) :
    (dimMeasure mu).toReal *
        (hyperbolicRate lam1 lam2 - epsilon) ≤
      kolmogorovSinaiEntropy mu T := by
  let dim := (dimMeasure mu).toReal
  let entropy := kolmogorovSinaiEntropy mu T
  let rate := hyperbolicRate lam1 lam2
  have hdim_nonneg : 0 ≤ dim := ENNReal.toReal_nonneg
  have hentropy_nonneg : 0 ≤ entropy :=
    kolmogorovSinaiEntropy_nonneg mu T
  have hrate_pos : 0 < rate := hyperbolicRate_pos hlam1_pos hlam2_neg
  by_cases htarget : 0 < rate - epsilon
  · apply le_of_not_gt
    intro hfail
    have hfail' : entropy < dim * (rate - epsilon) := by
      simpa [entropy, dim, rate] using hfail
    have hdim_pos : 0 < dim := by
      by_contra hdim_zero
      have hdim_le : dim ≤ 0 := le_of_not_gt hdim_zero
      have hdim_eq : dim = 0 := le_antisymm hdim_le hdim_nonneg
      rw [hdim_eq, zero_mul] at hfail'
      exact (not_lt_of_ge hentropy_nonneg) hfail'
    let z := min epsilon
      (min (-lam2) (min lam1 rate))
    have hz_pos : 0 < z := by
      dsimp [z]
      exact lt_min hepsilon
        (lt_min (neg_pos.mpr hlam2_neg) (lt_min hlam1_pos hrate_pos))
    have hz_epsilon : z ≤ epsilon := min_le_left _ _
    have hz_stable : z ≤ -lam2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hz_unstable : z ≤ lam1 :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    have hz_rate : z ≤ rate :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    let eta := z / 16
    have heta : 0 < eta := div_pos hz_pos (by norm_num)
    have hstable : lam2 + 6 * eta < 0 := by
      dsimp [eta]
      linarith
    have hunstable : -lam1 + 6 * eta < 0 := by
      dsimp [eta]
      linarith
    have hrate_eta : 8 * eta < rate := by
      dsimp [eta]
      linarith
    have heta_epsilon : 8 * eta < epsilon := by
      dsimp [eta]
      linarith
    let coverRate := rate - 8 * eta
    have hcoverRate : 0 < coverRate := by
      dsimp [coverRate]
      linarith
    have htarget_cover : rate - epsilon < coverRate := by
      dsimp [coverRate]
      linarith
    have hentropy_lt : entropy < dim * coverRate := by
      exact hfail'.trans (mul_lt_mul_of_pos_left htarget_cover hdim_pos)
    have hdimRate : 0 < dim * coverRate :=
      mul_pos hdim_pos hcoverRate
    let ratio := entropy / (dim * coverRate)
    have hratio_nonneg : 0 ≤ ratio :=
      div_nonneg hentropy_nonneg hdimRate.le
    have hratio_lt : ratio < 1 :=
      (div_lt_one hdimRate).2 hentropy_lt
    let alpha := (ratio + 1) / 2
    have halpha : 0 < alpha := by
      dsimp [alpha]
      linarith
    have halpha_lt : alpha < 1 := by
      dsimp [alpha]
      linarith
    have hratio_alpha : ratio < alpha := by
      dsimp [alpha]
      linarith
    have hentropy_div :
        entropy / alpha < dim * coverRate := by
      have hmul :
          entropy < alpha * (dim * coverRate) := by
        have hmul' :=
          mul_lt_mul_of_pos_right hratio_alpha hdimRate
        dsimp [ratio] at hmul'
        exact (div_mul_cancel₀ entropy hdimRate.ne').symm ▸ hmul'
      exact (div_lt_iff₀ halpha).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    let gap := dim * coverRate - entropy / alpha
    have hgap : 0 < gap := sub_pos.mpr hentropy_div
    let kappa := gap / 4
    have hkappa : 0 < kappa := div_pos hgap (by norm_num)
    have hnumerator :
        entropy / alpha + kappa < dim * coverRate := by
      dsimp [kappa, gap]
      linarith
    let qdim := (entropy / alpha + kappa) / coverRate
    have hqdim_nonneg : 0 ≤ qdim := by
      dsimp [qdim]
      exact div_nonneg
        (add_nonneg (div_nonneg hentropy_nonneg halpha.le) hkappa.le)
        hcoverRate.le
    have hqdim_lt : qdim < dim := by
      dsimp [qdim]
      exact (div_lt_iff₀ hcoverRate).2 (by
        simpa [mul_comm] using hnumerator)
    let dReal := (qdim + dim) / 2
    have hdReal_nonneg : 0 ≤ dReal := by
      dsimp [dReal]
      linarith
    let d : NNReal := ⟨dReal, hdReal_nonneg⟩
    have hd_lt : (d : ℝ) < dim := by
      change dReal < dim
      dsimp [dReal]
      linarith
    have hcore :
        entropy / alpha + kappa <
          coverRate * (d : ℝ) := by
      have hqd : qdim < (d : ℝ) := by
        change qdim < dReal
        dsimp [dReal]
        linarith
      calc
        entropy / alpha + kappa = coverRate * qdim := by
          dsimp [qdim]
          field_simp [hcoverRate.ne', halpha.ne']
        _ < coverRate * (d : ℝ) :=
          mul_lt_mul_of_pos_left hqd hcoverRate
    have hdim_le := dimMeasure_le_of_hyperbolic_sparse_covers
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta
        hstable hunstable hrate_eta halpha halpha_lt hkappa d (by
          simpa [entropy, rate, coverRate] using hcore)
    have hdim_toReal : dim ≤ (d : ℝ) := by
      have htop :=
        dimMeasure_ne_top_of_compact_full_measure mu hK_compact hmu_supp
      have hto := (ENNReal.toReal_le_toReal htop ENNReal.coe_ne_top).2 hdim_le
      simpa [dim] using hto
    exact (not_lt_of_ge hdim_toReal) hd_lt
  · have htarget_nonpos : rate - epsilon ≤ 0 := le_of_not_gt htarget
    exact (mul_nonpos_of_nonneg_of_nonpos hdim_nonneg htarget_nonpos).trans
      hentropy_nonneg

end Submission.Helpers
