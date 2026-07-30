import Submission.ShiftedCenteredEntropy
import Submission.AsymptoticMultiplicityEntropy
import Submission.HyperbolicUpper
import Submission.HyperbolicConclusion
import Submission.PesinStructuralCarrier
import Submission.PesinFullEndpointBlock
import Submission.SmallPartitions
import Submission.CarrierAtoms

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

set_option maxHeartbeats 2000000 in
/-- Sparse Pesin-block coding gives the lower entropy estimate in the
full-dimensional surface case. -/
theorem dimMeasure_mul_hyperbolicRate_sub_le_kolmogorovSinaiEntropy_of_sparse
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu] [NoAtoms mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (hdim : dimMeasure mu = 2)
    {lam1 lam2 epsilon : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (hepsilon : 0 < epsilon) :
    (dimMeasure mu).toReal *
        (hyperbolicRate lam1 lam2 - epsilon) ≤
      kolmogorovSinaiEntropy mu T := by
  classical
  let rate := hyperbolicRate lam1 lam2
  have hrate : 0 < rate := by
    simpa [rate] using hyperbolicRate_pos hlam1_pos hlam2_neg
  by_cases hepsilon_rate : epsilon < rate
  · let eta := sparseEta rate lam1 lam2 epsilon
    obtain ⟨heta, heta_gap, hstableRate, hunstableRate,
        heta_rate, heta_epsilon⟩ :
        0 < eta ∧
          8 * eta < lam1 - lam2 ∧
          lam2 + 6 * eta < 0 ∧
          -lam1 + 6 * eta < 0 ∧
          8 * eta < rate ∧
          6 * eta < epsilon / 16 := by
      simpa [eta] using
        sparseEta_spec hrate hlam1_pos hlam2_neg hepsilon
    have hstableFive : lam2 + 5 * eta < 0 := by linarith
    have hunstableFive : -lam1 + 5 * eta < 0 := by linarith
    obtain ⟨carrier, hcarrier_measurable, hcarrier_full,
        hcarrier, hcarrierK, hsource, hcov, _hdet⟩ :=
      exists_pesinStructuralCarrier
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
          K hK_compact hK_inv mu hmu_supp hT hErg
          hlam1 hlam2 hlam1_pos hlam2_neg heta heta_gap
          hstableFive hunstableFive (by simpa [rate] using heta_rate)
    obtain ⟨S, M, hKS, hSconvex, hM, hT_lipschitz,
        hderiv, hderiv_lipschitz⟩ :=
      exists_sparseGeometry T hT_smooth K hK_compact
    obtain ⟨D, hD, hscaleM, hscaleConstBase, hscaleRate⟩ :=
      exists_sparseDepth (M := M)
        (stableRate := lam2 + 6 * eta) hM
    obtain ⟨F, hFnet⟩ := exists_quarter_unit_net
    have hFnonempty : F.Nonempty := by
      obtain ⟨f, hf, _hclose⟩ := hFnet 0 (by simp)
      exact ⟨f, hf⟩
    have hFcard : 0 < F.card := Finset.card_pos.mpr hFnonempty
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
    have hFcard_one : (1 : ℝ) ≤ F.card := by
      have hone : 1 ≤ F.card := hFcard
      exact_mod_cast hone
    have hlogF : 0 ≤ Real.log (F.card : ℝ) :=
      Real.log_nonneg hFcard_one
    let diameterCoeff :=
      max (Real.log M + 2 * (-lam2)) (Real.log M + lam1)
    let multiplicityCoeff :=
      (4 * D : ℝ) * Real.log (F.card : ℝ)
    have hdiameterCoeff : 0 ≤ diameterCoeff := by
      dsimp [diameterCoeff]
      exact le_max_of_le_left (add_nonneg hlogM
        (mul_nonneg (by norm_num) (neg_nonneg.mpr hlam2_neg.le)))
    have hmultiplicityCoeff : 0 ≤ multiplicityCoeff := by
      dsimp [multiplicityCoeff]
      positivity
    let q0 := sparseBadDensity epsilon diameterCoeff multiplicityCoeff
    obtain ⟨hq0, hq0_one, hq0_diameter, hq0_multiplicity⟩ :
        0 < q0 ∧ q0 ≤ 1 ∧
          q0 * diameterCoeff < epsilon / 64 ∧
          q0 * multiplicityCoeff < epsilon / 64 := by
      simpa [q0] using sparseBadDensity_spec
        hepsilon hdiameterCoeff hmultiplicityCoeff
    let ratio := lam1 / (lam1 - lam2)
    have hratio : 0 < ratio := by
      dsimp [ratio]
      exact div_pos hlam1_pos (sub_pos.mpr (hlam2_neg.trans hlam1_pos))
    let qbad := min q0 (ratio / 2)
    have hqbad : 0 < qbad := by
      dsimp [qbad]
      exact lt_min hq0 (half_pos hratio)
    have hqbad_nonneg : 0 ≤ qbad := hqbad.le
    have hqbad_one : qbad ≤ 1 :=
      (min_le_left q0 (ratio / 2)).trans hq0_one
    have hqbad_ratio : qbad < ratio := by
      have hle : qbad ≤ ratio / 2 := min_le_right _ _
      linarith
    have hqbad_diameter :
        qbad * diameterCoeff < epsilon / 64 := by
      exact (mul_le_mul_of_nonneg_right
        (min_le_left q0 (ratio / 2)) hdiameterCoeff).trans_lt
          hq0_diameter
    have hqbad_multiplicity :
        qbad * multiplicityCoeff < epsilon / 64 := by
      exact (mul_le_mul_of_nonneg_right
        (min_le_left q0 (ratio / 2)) hmultiplicityCoeff).trans_lt
          hq0_multiplicity
    let kappa := epsilon / 2
    let Rdecay := rate - epsilon / 4
    have hkappa : 0 ≤ kappa := (half_pos hepsilon).le
    have hRdecay : 0 < Rdecay := by
      dsimp [Rdecay]
      linarith
    have hdim_top : dimMeasure mu ≠ ⊤ :=
      dimMeasure_ne_top_of_compact_full_measure mu hK_compact hmu_supp
    have hbound :
        (dimMeasure mu).toReal * Rdecay ≤
          kolmogorovSinaiEntropy mu T + kappa := by
      apply
        dimMeasure_mul_rate_le_entropy_add_of_asymptotic_piece_covers
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right
            mu hErg hdim_top hkappa hRdecay
      intro gamma hgamma
      have hblockLimit :=
        tendsto_measureReal_compl_pesinFullShadowingBlock_zero
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right
            K hK_compact hK_inv mu hmu_supp hT hErg
            hlam1 hlam2 hlam1_pos hlam2_neg heta heta_gap
            hstableFive hunstableFive (by simpa [rate] using heta_rate)
      have hscaledBlock :
          Tendsto
            (fun C : ℕ =>
              2 * mu.real
                (pesinFullShadowingBlock
                  T T_inv lam1 lam2 eta C)ᶜ)
            atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul hblockLimit
      have htarget : 0 < qbad * gamma := mul_pos hqbad hgamma
      have hsmallBlock :
          ∀ᶠ C : ℕ in atTop,
            2 * mu.real
                (pesinFullShadowingBlock
                  T T_inv lam1 lam2 eta C)ᶜ <
              qbad * gamma :=
        (tendsto_order.1 hscaledBlock).2 _ htarget
      obtain ⟨C, hCsmall, hC_one⟩ :=
        (hsmallBlock.and (eventually_ge_atTop 1)).exists
      let G := pesinFullShadowingBlock T T_inv lam1 lam2 eta C
      let good := maximalTwoSidedBadPrefixBlock T T_inv G qbad
      have hG : MeasurableSet G := by
        exact measurableSet_pesinFullShadowingBlock
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right
            lam1 lam2 eta C
      have hT_inv : MeasurePreserving T_inv mu mu :=
        measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right mu hT
      have hgood : MeasurableSet good := by
        exact measurableSet_maximalTwoSidedBadPrefixBlock
          hT.measurable hT_inv.measurable hG qbad
      have hgood_compl : mu.real goodᶜ ≤ gamma := by
        have hmeasure :=
          mul_measureReal_compl_maximalTwoSidedBadPrefixBlock_le
            mu T T_inv hT hT_inv hG hqbad_nonneg
        dsimp [G, good] at hmeasure hCsmall ⊢
        have hstrict :
            qbad * mu.real
                (maximalTwoSidedBadPrefixBlock T T_inv
                  (pesinFullShadowingBlock
                    T T_inv lam1 lam2 eta C) qbad)ᶜ <
              qbad * gamma :=
          hmeasure.trans_lt hCsmall
        exact le_of_mul_le_mul_left hstrict.le hqbad
      let qpath : ℝ := 16 * C
      have hCpos : (0 : ℝ) < C := by
        have hCnat : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
        exact_mod_cast hCnat
      have hqpath : 1 ≤ qpath := by
        have hConeReal : (1 : ℝ) ≤ C := by exact_mod_cast hC_one
        dsimp [qpath]
        nlinarith
      have hsumRate :
          (lam2 + 6 * eta) + (-lam1 + 6 * eta) < 0 := by
        have heta_lam1 : eta ≤ lam1 / 100 := by
          dsimp [eta, sparseEta]
          have hle :
              min (min rate (min lam1 (-lam2))) epsilon ≤ lam1 :=
            (min_le_left _ _).trans
              ((min_le_right rate _).trans (min_le_left _ _))
          linarith
        have heta_lam2 : eta ≤ (-lam2) / 100 := by
          dsimp [eta, sparseEta]
          have hle :
              min (min rate (min lam1 (-lam2))) epsilon ≤ -lam2 :=
            (min_le_left _ _).trans
              ((min_le_right rate _).trans (min_le_right _ _))
          linarith
        linarith
      obtain ⟨H, hH, hlogqH, hlog2H, hcross, hunstable⟩ :=
        exists_sparseSpacing
          (stableRate := lam2 + 6 * eta)
          (unstableRate := -lam1 + 6 * eta)
          (C := C) (qpath := qpath) (epsilon := epsilon)
          hstableRate hunstableRate hsumRate hCpos hqpath hepsilon
      have hAq : (4 * C : ℝ) / qpath ≤ 1 / 4 := by
        dsimp [qpath]
        have hCne : (C : ℝ) ≠ 0 := hCpos.ne'
        field_simp [hCne]
        norm_num
      have hstableCoeff :
          Real.log M + 2 * (-lam2) ≤ diameterCoeff := by
        exact le_max_left _ _
      have hunstableCoeff :
          Real.log M + lam1 ≤ diameterCoeff := by
        exact le_max_right _ _
      have hqbad_stable :
          qbad * (Real.log M + 2 * (-lam2)) < epsilon / 64 :=
        (mul_le_mul_of_nonneg_left hstableCoeff hqbad_nonneg).trans_lt
          hqbad_diameter
      have hqbad_unstable :
          qbad * (Real.log M + lam1) < epsilon / 64 :=
        (mul_le_mul_of_nonneg_left hunstableCoeff hqbad_nonneg).trans_lt
          hqbad_diameter
      have hstableLoss :
          6 * eta +
              qbad * (Real.log M + 2 * (-lam2)) +
              Real.log qpath / H <
            rate - Rdecay := by
        dsimp [Rdecay]
        linarith
      have hunstableLoss :
          6 * eta +
              qbad * (Real.log M + lam1) +
              Real.log qpath / H <
            rate - Rdecay := by
        dsimp [Rdecay]
        linarith
      let R := sparseRadius M (lam2 + 6 * eta) H
      obtain ⟨hR, hR_one, hshortSmall, hshortError⟩ :
          0 < R ∧ R ≤ 1 ∧ M ^ H * R ≤ 1 ∧
            H * (M * (M ^ H * R)) * (2 * M) ^ (H + 1) ≤
              Real.exp ((lam2 + 6 * eta) * H) := by
        simpa [R] using
          sparseRadius_spec (M := M)
            (stableRate := lam2 + 6 * eta) hM hH
      have hMsq : 1 ≤ M ^ 2 := one_le_pow₀ hM
      have hscaleR : 2 * R ≤ (4 : ℝ) ^ D := by
        calc
          2 * R ≤ 2 := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hR_one
                (show (0 : ℝ) ≤ 2 by norm_num)
          _ ≤ 4 * M ^ 2 := by
            calc
              (2 : ℝ) ≤ 4 := by norm_num
              _ ≤ 4 * M ^ 2 := by
                simpa only [mul_one] using
                  mul_le_mul_of_nonneg_left hMsq
                    (show (0 : ℝ) ≤ 4 by norm_num)
          _ ≤ (4 : ℝ) ^ D := hscaleConstBase
      have hscaleConst :
          4 * R * M ^ 2 ≤ (4 : ℝ) ^ D := by
        have h4R : 4 * R ≤ (4 : ℝ) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hR_one
              (show (0 : ℝ) ≤ 4 by norm_num)
        calc
          4 * R * M ^ 2 ≤ 4 * M ^ 2 :=
            mul_le_mul_of_nonneg_right h4R (sq_nonneg M)
          _ ≤ (4 : ℝ) ^ D := hscaleConstBase
      obtain ⟨P, hP, hPcarrier, hPdiameter⟩ :=
        exists_small_measurable_partition
          mu hK_compact hcarrier_measurable hcarrier_full hcarrierK
            (half_pos hR)
      have hPdiameterR :
          ∀ A ∈ P, Metric.ediam A ≤ ENNReal.ofReal R := by
        intro A hA
        refine (hPdiameter A hA).trans_eq ?_
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      have hcenteredCarrier
          {m₀ n₀ : ℕ} (hmn₀ : 0 < m₀ + n₀)
          {A : Set EucPlane}
          (hA : A ∈ centeredJoin T T_inv P m₀ n₀) :
          A ⊆ carrier := by
        rw [centeredJoin, preimagePartition] at hA
        obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_image.mp hA
        intro x hx
        have hxleft : T_inv^[m₀] x ∈ carrier :=
          iteratedJoin_atom_subset_of_partition_atoms
            T P hPcarrier hmn₀ hA₀ hx
        rw [← image_iterate_eq_of_image_eq T hcarrier m₀]
        exact ⟨T_inv^[m₀] x, hxleft, (hT_right.iterate m₀ x)⟩
      have hpartitionRate :
          entropyW mu T P ≤ kolmogorovSinaiEntropy mu T :=
        entropyW_le_kolmogorovSinaiEntropy_of_hyperbolic
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right
            K hK_compact hK_inv mu hmu_supp hT hErg
            hlam1 hlam2 hlam1_pos hlam2_neg P hP
      have hcoverRate :
          sparseCoverRate H D F.card qbad < kappa := by
        have hmultRewrite :
            (4 * D : ℝ) * qbad * Real.log (F.card : ℝ) =
              qbad * multiplicityCoeff := by
          dsimp [multiplicityCoeff]
          ring
        rw [sparseCoverRate, hmultRewrite]
        dsimp [kappa]
        linarith
      have hcenterEvent :=
        eventually_sparseCenterBound_le
          (lam1 := lam1) (lam2 := lam2) (eta := eta)
          (qbad := qbad) (M := M) (R := R)
          (qpath := qpath) (Rdecay := Rdecay)
          hlam1_pos hlam2_neg heta hqbad_nonneg hM hR hqpath
          hH hstableRate hunstableRate hstableLoss hunstableLoss
      have hbudgetEvent :=
        eventually_sparseBadBudget_add_le_balancedBackward
          hlam1_pos hlam2_neg hqbad_nonneg hqbad_ratio H
      have hforwardEvent :
          ∀ᶠ N : ℕ in atTop,
            0 < balancedForward lam1 lam2 N :=
        (tendsto_balancedForward_atTop hlam1_pos hlam2_neg).eventually
          (eventually_gt_atTop 0)
      have hcardEvent :=
        eventually_sparseCoverCardBound_le_exp
          hqbad_nonneg hH D F.card hFcard hcoverRate
      have hall :
          ∀ᶠ N : ℕ in atTop,
            (M ^ (sparseBadBudget qbad N + H) * R *
                (qpath ^ (N / H + 1) *
                    Real.exp ((lam2 + 6 * eta) *
                      ((balancedBackward lam1 lam2 N : ℝ) -
                        2 * sparseBadBudget qbad N - 2 * H)) +
                  qpath ^ (N / H + 1) *
                    Real.exp ((-lam1 + 6 * eta) *
                      ((balancedForward lam1 lam2 N : ℝ) -
                        sparseBadBudget qbad N - H))) ≤
              Real.exp (-Rdecay * N)) ∧
            sparseBadBudget qbad N + H ≤
              balancedBackward lam1 lam2 N ∧
            0 < balancedForward lam1 lam2 N ∧
            (H * (2 ^ (N / H + 1) *
                F.card ^ (4 * D * sparseBadBudget qbad N)) : ℕ) ≤
              Real.exp (kappa * N) := by
        filter_upwards [hcenterEvent, hbudgetEvent,
          hforwardEvent, hcardEvent] with N hc hb hn hcard
        exact ⟨hc, hb, hn, hcard⟩
      obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hall
      let total : ℕ → ℕ := fun L => L + N₀
      let m : ℕ → ℕ := fun L =>
        balancedBackward lam1 lam2 (total L)
      let n : ℕ → ℕ := fun L =>
        balancedForward lam1 lam2 (total L)
      let B : ℕ → ℕ := fun L =>
        sparseBadBudget qbad (total L)
      let Pseq : ℕ → Finset (Set EucPlane) := fun L =>
        centeredJoin T T_inv P (m L) (n L)
      let goodSeq : ℕ → Set EucPlane := fun _ => good
      let pieces : ℕ → Set EucPlane → Finset (Set EucPlane) :=
        fun L A =>
          sparsePhasePieces T T_inv G F R good A
            (m L) (n L) H D (B L)
      let Mcard : ℕ → ℕ := fun L =>
        H * (2 ^ (total L / H + 1) *
          F.card ^ (4 * D * B L))
      let growth : ℕ → ℝ := fun L => kappa * total L
      refine ⟨Pseq, goodSeq, pieces, Mcard, growth,
        entropyW mu T P, ?_, ?_, hpartitionRate, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro L
        exact isMeasurablePartition_centeredJoin
          mu T T_inv hT hT_inv P hP (m L) (n L)
      · simpa [Pseq, m, n, total] using
          tendsto_shifted_centeredJoin_entropy_div
            mu T T_inv hT_left hT_right hT hT_inv P hP
              hlam1_pos hlam2_neg N₀
      · intro L
        simpa [goodSeq] using hgood
      · intro L
        simpa [goodSeq] using hgood_compl
      · intro L A _hA
        have htotal :
            m L + n L = total L :=
          balancedBackward_add_balancedForward
            hlam1_pos hlam2_neg (total L)
        simpa [pieces, Mcard, htotal] using
          card_sparsePhasePieces_le
            T T_inv G F R good A (m L) (n L) hH D (B L) hFcard
      · intro L A hA U hU
        apply measurableSet_of_mem_sparsePhasePieces
          T T_inv hT_smooth.continuous hT_inv_smooth.continuous
            hG hgood
        · exact (isMeasurablePartition_centeredJoin
            mu T T_inv hT hT_inv P hP (m L) (n L)).measurable A hA
        · exact hU
      · intro L A hA
        have hlarge := hN₀ (total L) (by
          dsimp [total]
          omega)
        have htotal :
            m L + n L = total L := by
          exact balancedBackward_add_balancedForward
            hlam1_pos hlam2_neg (total L)
        have hn : 0 < n L := by
          simpa [n] using hlarge.2.2.1
        have hbudget : B L + H ≤ m L := by
          simpa [B, m] using hlarge.2.1
        apply sparsePhasePieces_cover
          T T_inv hT_right G F hFnet hR good A
            (m L) (n L) hH
            (by
              omega)
            D (B L)
        · intro x hx
          rw [finiteBadCountNat_centeredOrbitGoodTime]
          apply nat_le_sparseBadBudget hqbad_one
          have hcount :=
            sparseCenteredBadCount_le_of_twoSidedBadPrefixBlock
              T T_inv hT_left hT_right G
                (m := m L) (n := n L) hlarge.2.2.1 hx
          have htotalReal :
              (m L : ℝ) + (n L : ℝ) = (total L : ℝ) := by
            exact_mod_cast htotal
          calc
            (sparseCenteredBadCount T T_inv G (m L) (n L) x : ℝ) ≤
                qbad * ((m L : ℝ) + (n L : ℝ) + 1) := hcount
            _ = qbad * ((total L : ℝ) + 1) := by rw [htotalReal]
        · intro x hx y hy i
          have hclose :=
            norm_centeredOrbit_sub_le_of_mem_centeredJoin_atom
              T T_inv P hR.le hPdiameterR hA hx hy i
          simpa [dist_eq_norm, norm_sub_rev] using hclose
      · intro L A hA U hU
        have hlarge := hN₀ (total L) (by
          dsimp [total]
          omega)
        apply Metric.ediam_le_of_forall_dist_le
        intro y hy z hz
        have htotal :
            m L + n L = total L :=
          balancedBackward_add_balancedForward
            hlam1_pos hlam2_neg (total L)
        have hn : 0 < n L := by
          simpa [n] using hlarge.2.2.1
        have hcenter :=
          dist_le_of_mem_sparsePhasePiece
            T T_inv hT_smooth hT_inv_smooth hT_left hT_right
              hK_inv hKS hSconvex hcarrier hcarrierK hsource hcov
              hM hR hT_lipschitz hderiv hderiv_lipschitz
              F good A
              (hcenteredCarrier (by omega) hA)
              (m L) (n L) hH D (B L)
              hlarge.2.2.1 hlarge.2.1
              (fun x hx y hy i => by
                have hclose :=
                  norm_centeredOrbit_sub_le_of_mem_centeredJoin_atom
                    T T_inv P hR.le hPdiameterR hA hx hy i
                simpa [dist_eq_norm, norm_sub_rev] using hclose)
              hshortSmall hshortError hscaleR hscaleM
              hscaleConst hscaleRate hqpath hAq hcross hunstable
              hstableRate hunstableRate hU hy hz
        have hreal :
            dist y z ≤ Real.exp (-Rdecay * L) := by
          calc
            dist y z ≤
                M ^ (B L + H) * R *
                  (qpath ^ (total L / H + 1) *
                      Real.exp ((lam2 + 6 * eta) *
                        ((m L : ℝ) - 2 * B L - 2 * H)) +
                    qpath ^ (total L / H + 1) *
                      Real.exp ((-lam1 + 6 * eta) *
                        ((n L : ℝ) - B L - H))) := by
              simpa [htotal] using hcenter
            _ ≤ Real.exp (-Rdecay * total L) := hlarge.1
            _ ≤ Real.exp (-Rdecay * L) := by
              apply Real.exp_le_exp.mpr
              have hleNat : L ≤ total L := by
                dsimp [total]
                omega
              have hleReal : (L : ℝ) ≤ (total L : ℝ) := by
                exact_mod_cast hleNat
              exact mul_le_mul_of_nonpos_left hleReal
                (neg_nonpos.mpr hRdecay.le)
        exact hreal
      · intro L
        have hlarge := hN₀ (total L) (by
          dsimp [total]
          omega)
        simpa [Mcard, B, growth] using hlarge.2.2.2
      · simpa [growth, total] using
          tendsto_const_mul_nat_add_div kappa N₀
    have hdimReal : (dimMeasure mu).toReal = 2 := by
      rw [hdim]
      norm_num
    rw [hdimReal] at hbound ⊢
    dsimp [Rdecay, kappa, rate] at hbound ⊢
    linarith only [hbound, hepsilon]
  · have hnonpos : rate - epsilon ≤ 0 := by linarith
    exact (mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
      (by simpa [rate] using hnonpos)).trans
        (kolmogorovSinaiEntropy_nonneg mu T)

/-- The hyperbolic Young identity, now with its lower bound discharged by
sparse Pesin coding. -/
theorem hyperbolic_young_identity_of_sparse
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu] [NoAtoms mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    (hdim : dimMeasure mu = 2)
    {lam1 lam2 : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0) :
    kolmogorovSinaiEntropy mu T =
      (dimMeasure mu).toReal *
        harmonicMeanLyapunov lam1 lam2 / 2 := by
  apply young_identity_of_approx_hyperbolic_bounds ENNReal.toReal_nonneg
  · intro epsilon hepsilon
    exact kolmogorovSinaiEntropy_sub_le_dimMeasure_mul_hyperbolicRate_add
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg hepsilon
  · intro epsilon hepsilon
    exact
      dimMeasure_mul_hyperbolicRate_sub_le_kolmogorovSinaiEntropy_of_sparse
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
          K hK_compact hK_inv mu hmu_supp hT hErg hdim
          hlam1 hlam2 hlam1_pos hlam2_neg hepsilon

end Submission.Helpers
