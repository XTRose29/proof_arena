import ChallengeDeps
import Submission.Helpers
import Submission.GreenSolver

open LeanEval.Dynamics.HyperbolicShadowingProblem
open scoped Topology

variable {d : ℕ}

namespace Submission

set_option maxHeartbeats 2000000 in
theorem hyperbolic_has_shadowing (T : E d ≃ₜ E d) (K : Set (E d))
    (hKc : IsCompact K) (hK : IsHyperbolic T K) :
    HasShadowing (T : E d → E d) K := by
  by_cases hKempty : K = ∅
  · exact Submission.Helpers.hasShadowing_of_eq_empty T K hKempty
  · rcases hK with ⟨hs⟩
    have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
    have hProjection :
        Submission.Shadowing.UniformProjectionBounds T K hKc hKne hs :=
      Submission.Shadowing.uniformProjectionBounds hKc hKne hs
    have hRemainder :
        Submission.Shadowing.UniformFirstOrderRemainderEstimates T K hKc hs := by
      exact Submission.Shadowing.uniformFirstOrderRemainderEstimates hKc hs
    have hEstimates :
        Submission.Shadowing.NonemptyAnalyticEstimates T K hKc hKne hs := by
      have hProjection' := hProjection
      have hRemainder' := hRemainder
      let M : ℝ := Classical.choose hProjection
      have hM_pos : 0 < M := (Classical.choose_spec hProjection).1
      have hM_projection_bound :
          ∀ z : E d, ∀ hz : z ∈ K, ∀ v : E d,
            ‖Submission.Shadowing.stableProjection hs z hz v‖ ≤ M * ‖v‖ ∧
              ‖Submission.Shadowing.unstableProjection hs z hz v‖ ≤ M * ‖v‖ :=
        (Classical.choose_spec hProjection).2
      let greenBound : ℝ :=
        64 * M * M + 64 * M + 4 * M * hs.const / (1 - hs.rate) + 1
      have hgreen_pos : 0 < greenBound := by
        have hden_pos : 0 < 1 - hs.rate := sub_pos.mpr hs.rate_lt_one
        have hquad_nonneg : 0 ≤ 64 * M * M := by nlinarith [hM_pos]
        have hlinear_nonneg : 0 ≤ 64 * M := by nlinarith [hM_pos]
        have hnum_nonneg : 0 ≤ 4 * M * hs.const := by
          nlinarith [hM_pos, hs.const_pos]
        have hmain_nonneg : 0 ≤ 4 * M * hs.const / (1 - hs.rate) := by
          exact div_nonneg hnum_nonneg hden_pos.le
        dsimp [greenBound]
        linarith
      let η : ℝ := 1 / (4 * greenBound)
      have hη_pos : 0 < η := by
        dsimp [η]
        exact one_div_pos.mpr (by nlinarith [hgreen_pos])
      have hblockTarget_pos : 0 < η / 16 := by positivity
      let hBlockPack :=
        Submission.Shadowing.exists_positive_small_hyperbolic_iterate (T := T) (K := K) hs
          hblockTarget_pos
      let blockN : ℕ := Classical.choose hBlockPack
      have hblock_pos : 0 < blockN := by
        exact (Classical.choose_spec hBlockPack).1
      have hblock_contract : hs.const * hs.rate ^ blockN < η / 16 :=
        (Classical.choose_spec hBlockPack).2
      let U : Set (E d) := Classical.choose hRemainder
      have hRemainder_spec := Classical.choose_spec hRemainder
      have hrem : ∀ η > 0, ∃ r > 0, ∀ x : E d, x ∈ K → ∀ z : E d, z ∈ U →
          ‖z - x‖ < r →
            ‖T z - T x - fderiv ℝ (T : E d → E d) x (z - x)‖ ≤ η * ‖z - x‖ ∧
            ‖T.symm z - T.symm x - fderiv ℝ (T.symm : E d → E d) x (z - x)‖ ≤
              η * ‖z - x‖ := hRemainder_spec.2.2
      let ρU : ℝ := Classical.choose
        (Submission.Shadowing.exists_localTube_subset_open hKc hRemainder_spec.1
          hRemainder_spec.2.1)
      have hρU_pos : 0 < ρU := (Classical.choose_spec
        (Submission.Shadowing.exists_localTube_subset_open hKc hRemainder_spec.1
          hRemainder_spec.2.1)).1
      have hρU_subset : Submission.Shadowing.localTube K ρU ⊆ U :=
        (Classical.choose_spec
          (Submission.Shadowing.exists_localTube_subset_open hKc hRemainder_spec.1
            hRemainder_spec.2.1)).2
      let hTaylorPack := hrem η hη_pos
      let rTaylor : ℝ := Classical.choose hTaylorPack
      have hrTaylor_pos : 0 < rTaylor := (Classical.choose_spec hTaylorPack).1
      have hremTaylor :
          ∀ a : E d, a ∈ K → ∀ z : E d, z ∈ U →
            ‖z - a‖ < rTaylor →
              ‖T z - T a - fderiv ℝ (T : E d → E d) a (z - a)‖ ≤
                  η * ‖z - a‖ ∧
                ‖T.symm z - T.symm a - fderiv ℝ (T.symm : E d → E d) a (z - a)‖ ≤
                  η * ‖z - a‖ :=
        (Classical.choose_spec hTaylorPack).2
      let hIncrementPack :=
        Submission.Shadowing.compactUniformTwoPointLinearization (K := K) hKc
          hs.contDiff_fwd hη_pos
      let rIncrement : ℝ := Classical.choose hIncrementPack
      have hrIncrement_pos : 0 < rIncrement := (Classical.choose_spec hIncrementPack).1
      have hIncrementRaw :
          ∀ a : E d, a ∈ K → ∀ z w : E d,
            ‖z - a‖ < rIncrement → ‖w - a‖ < rIncrement →
              ‖T z - T w - fderiv ℝ (T : E d → E d) a (z - w)‖ ≤
                η * ‖z - w‖ :=
        (Classical.choose_spec hIncrementPack).2
      let hBlockFwdDerivPack :=
        Submission.Shadowing.compactUniformFDerivWithin (K := K) hKc
          (Submission.Shadowing.contDiff_iterate hs.contDiff_fwd blockN)
          hblockTarget_pos
      let rBlockFwd : ℝ := Classical.choose hBlockFwdDerivPack
      have hrBlockFwd_pos : 0 < rBlockFwd :=
        (Classical.choose_spec hBlockFwdDerivPack).1
      have hBlockFwdDeriv :
          ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < rBlockFwd →
            ‖fderiv ℝ ((T : E d → E d)^[blockN]) z -
                fderiv ℝ ((T : E d → E d)^[blockN]) a‖ ≤ η / 16 :=
        (Classical.choose_spec hBlockFwdDerivPack).2
      let hBlockBwdDerivPack :=
        Submission.Shadowing.compactUniformFDerivWithin (K := K) hKc
          (Submission.Shadowing.contDiff_iterate hs.contDiff_bwd blockN)
          hblockTarget_pos
      let rBlockBwd : ℝ := Classical.choose hBlockBwdDerivPack
      have hrBlockBwd_pos : 0 < rBlockBwd :=
        (Classical.choose_spec hBlockBwdDerivPack).1
      have hBlockBwdDeriv :
          ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < rBlockBwd →
            ‖fderiv ℝ ((T.symm : E d → E d)^[blockN]) z -
                fderiv ℝ ((T.symm : E d → E d)^[blockN]) a‖ ≤ η / 16 :=
        (Classical.choose_spec hBlockBwdDerivPack).2
      let derivativeBound : ℝ :=
        Classical.choose (Submission.Shadowing.finiteTimeDerivativeBounds hKc hs 1)
      have hderivativeBound_spec :
          0 ≤ derivativeBound ∧ ∀ z : E d, z ∈ K →
            ‖fderiv ℝ ((T : E d → E d)^[1]) z‖ ≤ derivativeBound ∧
            ‖fderiv ℝ ((T.symm : E d → E d)^[1]) z‖ ≤ derivativeBound :=
        Classical.choose_spec (Submission.Shadowing.finiteTimeDerivativeBounds hKc hs 1)
      let solverBound : ℝ :=
        Submission.Shadowing.crudeGreenBound M derivativeBound blockN
      have hsolverBound_pos : 0 < solverBound := by
        dsimp [solverBound]
        exact Submission.Shadowing.crudeGreenBound_pos hM_pos hderivativeBound_spec.1
      let ζ : ℝ := 1 / (4 * solverBound)
      have hζ_pos : 0 < ζ := by
        dsimp [ζ]
        exact one_div_pos.mpr (by nlinarith [hsolverBound_pos])
      let hSolverIncrementPack :=
        Submission.Shadowing.compactUniformTwoPointLinearization (K := K) hKc
          hs.contDiff_fwd hζ_pos
      let rSolverIncrement : ℝ := Classical.choose hSolverIncrementPack
      have hrSolverIncrement_pos : 0 < rSolverIncrement :=
        (Classical.choose_spec hSolverIncrementPack).1
      have hSolverIncrementRaw :
          ∀ a : E d, a ∈ K → ∀ z w : E d,
            ‖z - a‖ < rSolverIncrement → ‖w - a‖ < rSolverIncrement →
              ‖T z - T w - fderiv ℝ (T : E d → E d) a (z - w)‖ ≤
                ζ * ‖z - w‖ :=
        (Classical.choose_spec hSolverIncrementPack).2
      let blockGrowth : ℝ := derivativeBound ^ blockN
      have hblockGrowth_nonneg : 0 ≤ blockGrowth := by
        dsimp [blockGrowth]
        exact pow_nonneg hderivativeBound_spec.1 blockN
      let endpointLeakTol : ℝ := (1 / 64 : ℝ) / ((M + 1) * (blockGrowth + 1))
      have hendpointLeakTol_pos : 0 < endpointLeakTol := by
        dsimp [endpointLeakTol]
        exact div_pos (by norm_num)
          (mul_pos (by nlinarith [hM_pos]) (by nlinarith [hblockGrowth_nonneg]))
      have hendpointLeakTol_nonneg : 0 ≤ endpointLeakTol := le_of_lt hendpointLeakTol_pos
      let productStepTol : ℝ :=
        (η / 16) /
          (Submission.Shadowing.finiteProductPerturbation derivativeBound 1 blockN + 1)
      have hproductStepTol_pos : 0 < productStepTol := by
        dsimp [productStepTol]
        exact div_pos hblockTarget_pos
          (Submission.Shadowing.finiteProductPerturbation_denom_pos
            hderivativeBound_spec.1 blockN)
      have hproductStepTol_nonneg : 0 ≤ productStepTol := le_of_lt hproductStepTol_pos
      have hproductPerturbation_le :
          Submission.Shadowing.finiteProductPerturbation derivativeBound
              productStepTol blockN ≤ η / 16 := by
        dsimp [productStepTol]
        exact Submission.Shadowing.finiteProductPerturbation_scaled_step_le
          hderivativeBound_spec.1 hblockTarget_pos.le blockN
      let hStepFwdDerivPack :=
        Submission.Shadowing.compactUniformFDerivWithin (K := K) hKc
          hs.contDiff_fwd hproductStepTol_pos
      let rStepFwd : ℝ := Classical.choose hStepFwdDerivPack
      have hrStepFwd_pos : 0 < rStepFwd :=
        (Classical.choose_spec hStepFwdDerivPack).1
      have hStepFwdDeriv :
          ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < rStepFwd →
            ‖fderiv ℝ (T : E d → E d) z -
                fderiv ℝ (T : E d → E d) a‖ ≤ productStepTol :=
        (Classical.choose_spec hStepFwdDerivPack).2
      let hStepBwdDerivPack :=
        Submission.Shadowing.compactUniformFDerivWithin (K := K) hKc
          hs.contDiff_bwd hproductStepTol_pos
      let rStepBwd : ℝ := Classical.choose hStepBwdDerivPack
      have hrStepBwd_pos : 0 < rStepBwd :=
        (Classical.choose_spec hStepBwdDerivPack).1
      have hStepBwdDeriv :
          ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < rStepBwd →
            ‖fderiv ℝ (T.symm : E d → E d) z -
                fderiv ℝ (T.symm : E d → E d) a‖ ≤ productStepTol :=
        (Classical.choose_spec hStepBwdDerivPack).2
      let hStableLeakPack :=
        Submission.Shadowing.exists_unstableProjection_of_stable_nearby_small
          (T := T) (K := K) hKc hs hη_pos
      let rStableLeak : ℝ := Classical.choose hStableLeakPack
      have hrStableLeak_pos : 0 < rStableLeak := (Classical.choose_spec hStableLeakPack).1
      have hstable_leak :
          ∀ z : E d, z ∈ K → ∀ y : E d, ∀ hy : y ∈ K,
            ‖y - z‖ < rStableLeak → ∀ v : E d, v ∈ hs.stable z →
              ‖Submission.Shadowing.unstableProjection hs y hy v‖ ≤ η * ‖v‖ :=
        (Classical.choose_spec hStableLeakPack).2
      let hUnstableLeakPack :=
        Submission.Shadowing.exists_stableProjection_of_unstable_nearby_small
          (T := T) (K := K) hKc hs hη_pos
      let rUnstableLeak : ℝ := Classical.choose hUnstableLeakPack
      have hrUnstableLeak_pos : 0 < rUnstableLeak :=
        (Classical.choose_spec hUnstableLeakPack).1
      have hunstable_leak :
          ∀ z : E d, z ∈ K → ∀ y : E d, ∀ hy : y ∈ K,
            ‖y - z‖ < rUnstableLeak → ∀ v : E d, v ∈ hs.unstable z →
              ‖Submission.Shadowing.stableProjection hs y hy v‖ ≤ η * ‖v‖ :=
        (Classical.choose_spec hUnstableLeakPack).2
      let hStableEndpointLeakPack :=
        Submission.Shadowing.exists_unstableProjection_of_stable_nearby_small
          (T := T) (K := K) hKc hs hendpointLeakTol_pos
      let rStableEndpointLeak : ℝ := Classical.choose hStableEndpointLeakPack
      have hrStableEndpointLeak_pos : 0 < rStableEndpointLeak :=
        (Classical.choose_spec hStableEndpointLeakPack).1
      have hstable_endpoint_leak :
          ∀ z : E d, z ∈ K → ∀ y : E d, ∀ hy : y ∈ K,
            ‖y - z‖ < rStableEndpointLeak → ∀ v : E d, v ∈ hs.stable z →
              ‖Submission.Shadowing.unstableProjection hs y hy v‖ ≤
                endpointLeakTol * ‖v‖ :=
        (Classical.choose_spec hStableEndpointLeakPack).2
      let hUnstableEndpointLeakPack :=
        Submission.Shadowing.exists_stableProjection_of_unstable_nearby_small
          (T := T) (K := K) hKc hs hendpointLeakTol_pos
      let rUnstableEndpointLeak : ℝ := Classical.choose hUnstableEndpointLeakPack
      have hrUnstableEndpointLeak_pos : 0 < rUnstableEndpointLeak :=
        (Classical.choose_spec hUnstableEndpointLeakPack).1
      have hunstable_endpoint_leak :
          ∀ z : E d, z ∈ K → ∀ y : E d, ∀ hy : y ∈ K,
            ‖y - z‖ < rUnstableEndpointLeak → ∀ v : E d, v ∈ hs.unstable z →
              ‖Submission.Shadowing.stableProjection hs y hy v‖ ≤
                endpointLeakTol * ‖v‖ :=
        (Classical.choose_spec hUnstableEndpointLeakPack).2
      let transitionScale : ℝ := derivativeBound + η + 2
      have htransitionScale_pos : 0 < transitionScale := by
        dsimp [transitionScale]
        nlinarith [hderivativeBound_spec.1, hη_pos]
      let rEndpointLeak : ℝ := min rStableEndpointLeak rUnstableEndpointLeak
      have hrEndpointLeak_pos : 0 < rEndpointLeak := by
        dsimp [rEndpointLeak]
        exact lt_min hrStableEndpointLeak_pos hrUnstableEndpointLeak_pos
      have hrEndpointLeak_le_stable : rEndpointLeak ≤ rStableEndpointLeak := by
        dsimp [rEndpointLeak]
        exact min_le_left rStableEndpointLeak rUnstableEndpointLeak
      have hrEndpointLeak_le_unstable : rEndpointLeak ≤ rUnstableEndpointLeak := by
        dsimp [rEndpointLeak]
        exact min_le_right rStableEndpointLeak rUnstableEndpointLeak
      let rLeak : ℝ := min (min rStableLeak rUnstableLeak) rEndpointLeak
      have hrLeak_pos : 0 < rLeak := by
        dsimp [rLeak]
        exact lt_min (lt_min hrStableLeak_pos hrUnstableLeak_pos) hrEndpointLeak_pos
      have hrLeak_le_stable : rLeak ≤ rStableLeak := by
        dsimp [rLeak]
        exact (min_le_left (min rStableLeak rUnstableLeak) rEndpointLeak).trans
          (min_le_left rStableLeak rUnstableLeak)
      have hrLeak_le_unstable : rLeak ≤ rUnstableLeak := by
        dsimp [rLeak]
        exact (min_le_left (min rStableLeak rUnstableLeak) rEndpointLeak).trans
          (min_le_right rStableLeak rUnstableLeak)
      have hrLeak_le_stable_endpoint : rLeak ≤ rStableEndpointLeak := by
        dsimp [rLeak]
        exact (min_le_right (min rStableLeak rUnstableLeak) rEndpointLeak).trans
          hrEndpointLeak_le_stable
      have hrLeak_le_unstable_endpoint : rLeak ≤ rUnstableEndpointLeak := by
        dsimp [rLeak]
        exact (min_le_right (min rStableLeak rUnstableLeak) rEndpointLeak).trans
          hrEndpointLeak_le_unstable
      let rAnalytic : ℝ := min (min rTaylor rIncrement) rSolverIncrement
      have hrAnalytic_pos : 0 < rAnalytic := by
        dsimp [rAnalytic]
        exact lt_min (lt_min hrTaylor_pos hrIncrement_pos) hrSolverIncrement_pos
      let rStepBwdImage : ℝ := rStepBwd / (2 * (derivativeBound + η + 1))
      have hrStepBwdImage_pos : 0 < rStepBwdImage := by
        dsimp [rStepBwdImage]
        exact div_pos hrStepBwd_pos (by nlinarith [hderivativeBound_spec.1, hη_pos])
      let rStepControl : ℝ := min rStepFwd rStepBwdImage
      have hrStepControl_pos : 0 < rStepControl := by
        dsimp [rStepControl]
        exact lt_min hrStepFwd_pos hrStepBwdImage_pos
      let rBlock : ℝ := min (min rBlockFwd rBlockBwd) rStepControl
      have hrBlock_pos : 0 < rBlock := by
        dsimp [rBlock]
        exact lt_min (lt_min hrBlockFwd_pos hrBlockBwd_pos) hrStepControl_pos
      let rLocal : ℝ := min (min rAnalytic rBlock) rLeak
      have hrLocal_pos : 0 < rLocal := by
        dsimp [rLocal]
        exact lt_min (lt_min hrAnalytic_pos hrBlock_pos) hrLeak_pos
      have hrLocal_le_rIncrement : rLocal ≤ rIncrement := by
        dsimp [rLocal, rAnalytic]
        exact (min_le_left (min rAnalytic rBlock) rLeak).trans
          ((min_le_left rAnalytic rBlock).trans
            ((min_le_left (min rTaylor rIncrement) rSolverIncrement).trans
              (min_le_right rTaylor rIncrement)))
      have hrLocal_le_rSolverIncrement : rLocal ≤ rSolverIncrement := by
        dsimp [rLocal, rAnalytic]
        exact (min_le_left (min rAnalytic rBlock) rLeak).trans
          ((min_le_left rAnalytic rBlock).trans
            (min_le_right (min rTaylor rIncrement) rSolverIncrement))
      have hrLocal_le_rLeak : rLocal ≤ rLeak := by
        dsimp [rLocal]
        exact min_le_right (min rAnalytic rBlock) rLeak
      have hrLocal_le_rStableLeak : rLocal ≤ rStableLeak :=
        hrLocal_le_rLeak.trans hrLeak_le_stable
      have hrLocal_le_rUnstableLeak : rLocal ≤ rUnstableLeak :=
        hrLocal_le_rLeak.trans hrLeak_le_unstable
      let trackingScale : ℝ :=
        Submission.Shadowing.finiteTrackingAmplificationCap (derivativeBound + η) blockN
      have htrackingScale_pos : 0 < trackingScale := by
        dsimp [trackingScale]
        exact Submission.Shadowing.finiteTrackingAmplificationCap_pos
          (by nlinarith [hderivativeBound_spec.1, hη_pos]) blockN
      have htrackingScale_nonneg : 0 ≤ trackingScale := le_of_lt htrackingScale_pos
      have htrackingScale_ge :
          ∀ j : ℕ, j ≤ blockN →
            Submission.Shadowing.finiteTrackingAmplification (derivativeBound + η) j ≤
              trackingScale := by
        intro j hj
        dsimp [trackingScale]
        exact Submission.Shadowing.finiteTrackingAmplification_le_cap
          (by nlinarith [hderivativeBound_spec.1, hη_pos]) hj
      let rTracking : ℝ := rLocal / (4 * transitionScale * trackingScale)
      have hrTracking_pos : 0 < rTracking := by
        dsimp [rTracking]
        exact div_pos hrLocal_pos (by nlinarith [htransitionScale_pos, htrackingScale_pos])
      let rBridge : ℝ := min (rLeak / (4 * transitionScale)) rTracking
      have hrBridge_pos : 0 < rBridge := by
        dsimp [rBridge]
        exact lt_min (div_pos hrLeak_pos (by nlinarith [htransitionScale_pos]))
          hrTracking_pos
      have hrBridge_le_leak : rBridge ≤ rLeak / (4 * transitionScale) := by
        dsimp [rBridge]
        exact min_le_left (rLeak / (4 * transitionScale)) rTracking
      have hrBridge_le_tracking : rBridge ≤ rTracking := by
        dsimp [rBridge]
        exact min_le_right (rLeak / (4 * transitionScale)) rTracking
      let r : ℝ := min rLocal rBridge
      have hr_pos : 0 < r := by
        dsimp [r]
        exact lt_min hrLocal_pos hrBridge_pos
      have hr_le_rTaylor : r ≤ rTaylor := by
        dsimp [r, rLocal, rAnalytic]
        exact (min_le_left rLocal rBridge).trans
          ((min_le_left (min rAnalytic rBlock) rLeak).trans
            ((min_le_left rAnalytic rBlock).trans
              ((min_le_left (min rTaylor rIncrement) rSolverIncrement).trans
                (min_le_left rTaylor rIncrement))))
      have hr_le_rIncrement : r ≤ rIncrement := by
        dsimp [r, rLocal, rAnalytic]
        exact (min_le_left rLocal rBridge).trans
          ((min_le_left (min rAnalytic rBlock) rLeak).trans
            ((min_le_left rAnalytic rBlock).trans
              ((min_le_left (min rTaylor rIncrement) rSolverIncrement).trans
                (min_le_right rTaylor rIncrement))))
      have hr_le_rSolverIncrement : r ≤ rSolverIncrement :=
        (min_le_left rLocal rBridge).trans hrLocal_le_rSolverIncrement
      have hr_le_rBlockFwd : r ≤ rBlockFwd := by
        dsimp [r, rLocal, rBlock, rStepControl]
        exact (min_le_left rLocal rBridge).trans
          ((min_le_left (min rAnalytic rBlock) rLeak).trans
            ((min_le_right rAnalytic rBlock).trans
              ((min_le_left (min rBlockFwd rBlockBwd) (min rStepFwd rStepBwdImage)).trans
                (min_le_left rBlockFwd rBlockBwd))))
      have hr_le_rBlockBwd : r ≤ rBlockBwd := by
        dsimp [r, rLocal, rBlock, rStepControl]
        exact (min_le_left rLocal rBridge).trans
          ((min_le_left (min rAnalytic rBlock) rLeak).trans
            ((min_le_right rAnalytic rBlock).trans
              ((min_le_left (min rBlockFwd rBlockBwd) (min rStepFwd rStepBwdImage)).trans
                (min_le_right rBlockFwd rBlockBwd))))
      have hrLocal_le_rStepFwd : rLocal ≤ rStepFwd := by
        dsimp [rLocal, rBlock, rStepControl]
        exact (min_le_left (min rAnalytic rBlock) rLeak).trans
          ((min_le_right rAnalytic rBlock).trans
            ((min_le_right (min rBlockFwd rBlockBwd) (min rStepFwd rStepBwdImage)).trans
              (min_le_left rStepFwd rStepBwdImage)))
      have hrLocal_le_rStepBwdImage : rLocal ≤ rStepBwdImage := by
        dsimp [rLocal, rBlock, rStepControl]
        exact (min_le_left (min rAnalytic rBlock) rLeak).trans
          ((min_le_right rAnalytic rBlock).trans
            ((min_le_right (min rBlockFwd rBlockBwd) (min rStepFwd rStepBwdImage)).trans
              (min_le_right rStepFwd rStepBwdImage)))
      have hr_le_rBridge : r ≤ rBridge := by
        dsimp [r]
        exact min_le_right rLocal rBridge
      let ρ : ℝ := min r ρU / 4
      have hρ_pos : 0 < ρ := by
        dsimp [ρ]
        nlinarith only [hr_pos, hρU_pos, lt_min hr_pos hρU_pos]
      have hρ_le_r : ρ ≤ r := by
        dsimp [ρ]
        nlinarith only [hr_pos, hρU_pos, min_le_left r ρU]
      have hρ_le_rBridge : ρ ≤ rBridge := hρ_le_r.trans hr_le_rBridge
      have hρ_le_ρU : ρ ≤ ρU := by
        dsimp [ρ]
        nlinarith only [hr_pos, hρU_pos, min_le_right r ρU]
      have hρ_margin_r : ρ + ρ / 2 < r := by
        dsimp [ρ]
        have hmin_le_r : min r ρU ≤ r := min_le_left r ρU
        have hmin_pos : 0 < min r ρU := lt_min hr_pos hρU_pos
        nlinarith only [hmin_le_r, hmin_pos]
      have hρ_margin_ρU : ρ + ρ / 2 < ρU := by
        dsimp [ρ]
        have hmin_le_ρU : min r ρU ≤ ρU := min_le_right r ρU
        have hmin_pos : 0 < min r ρU := lt_min hr_pos hρU_pos
        nlinarith only [hmin_le_ρU, hmin_pos]
      have hρ_subset_U : Submission.Shadowing.localTube K ρ ⊆ U := by
        intro z hz
        exact hρU_subset (by
          rw [Submission.Shadowing.mem_localTube] at hz ⊢
          rcases hz with ⟨a, haK, haz⟩
          exact ⟨a, haK, lt_of_lt_of_le haz hρ_le_ρU⟩)
      have hrem_r : ∀ a : E d, a ∈ K → ∀ z : E d, z ∈ U →
          ‖z - a‖ < r →
            ‖T z - T a - fderiv ℝ (T : E d → E d) a (z - a)‖ ≤ η * ‖z - a‖ ∧
            ‖T.symm z - T.symm a - fderiv ℝ (T.symm : E d → E d) a (z - a)‖ ≤
              η * ‖z - a‖ := by
        intro a ha z hzU hza
        exact hremTaylor a ha z hzU (lt_of_lt_of_le hza hr_le_rTaylor)
      have hIncrement_r :
          ∀ a : E d, a ∈ K → ∀ z w : E d,
            ‖z - a‖ < r → ‖w - a‖ < r →
              ‖T z - T w - fderiv ℝ (T : E d → E d) a (z - w)‖ ≤
                η * ‖z - w‖ := by
        intro a ha z w hz hw
        exact hIncrementRaw a ha z w
          (lt_of_lt_of_le hz hr_le_rIncrement)
          (lt_of_lt_of_le hw hr_le_rIncrement)
      have hSolverIncrement_r :
          ∀ a : E d, a ∈ K → ∀ z w : E d,
            ‖z - a‖ < r → ‖w - a‖ < r →
              ‖T z - T w - fderiv ℝ (T : E d → E d) a (z - w)‖ ≤
                ζ * ‖z - w‖ := by
        intro a ha z w hz hw
        exact hSolverIncrementRaw a ha z w
          (lt_of_lt_of_le hz hr_le_rSolverIncrement)
          (lt_of_lt_of_le hw hr_le_rSolverIncrement)
      have hBlockFwdDeriv_r :
          ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < r →
            ‖fderiv ℝ ((T : E d → E d)^[blockN]) z -
                fderiv ℝ ((T : E d → E d)^[blockN]) a‖ ≤ η / 16 := by
        intro a ha z hza
        exact hBlockFwdDeriv a ha z (lt_of_lt_of_le hza hr_le_rBlockFwd)
      have hBlockBwdDeriv_r :
          ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < r →
            ‖fderiv ℝ ((T.symm : E d → E d)^[blockN]) z -
                fderiv ℝ ((T.symm : E d → E d)^[blockN]) a‖ ≤ η / 16 := by
        intro a ha z hza
        exact hBlockBwdDeriv a ha z (lt_of_lt_of_le hza hr_le_rBlockBwd)
      have hStepFwdDeriv_rLocal :
          ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < rLocal →
            ‖fderiv ℝ (T : E d → E d) z -
                fderiv ℝ (T : E d → E d) a‖ ≤ productStepTol := by
        intro a ha z hza
        exact hStepFwdDeriv a ha z (lt_of_lt_of_le hza hrLocal_le_rStepFwd)
      refine Submission.Shadowing.nonemptyAnalyticEstimates_of_localTube_shadowing
        ρ hρ_pos hProjection' hRemainder' ?_
      intro δ hδ
      let α : ℝ := Submission.Shadowing.correctionRadius δ ρ
      have hα_pos : 0 < α := by
        exact Submission.Shadowing.correctionRadius_pos hδ hρ_pos
      have hα_lt_delta : α < δ := by
        exact Submission.Shadowing.correctionRadius_lt_delta hδ
      have hα_le_ρ_half : α ≤ ρ / 2 := by
        exact Submission.Shadowing.correctionRadius_le_half_tube δ ρ
      let ε : ℝ := min (α / (2 * solverBound)) (ρ / 2)
      have hε_pos : 0 < ε := by
        dsimp [ε]
        refine lt_min ?_ ?_
        · exact div_pos hα_pos (mul_pos (by norm_num) hsolverBound_pos)
        · linarith only [hρ_pos]
      have hε_le_solver_budget : solverBound * ε ≤ α / 2 := by
        have hε_le : ε ≤ α / (2 * solverBound) := by
          dsimp [ε]
          exact min_le_left (α / (2 * solverBound)) (ρ / 2)
        have hden_pos : 0 < 2 * solverBound := mul_pos (by norm_num) hsolverBound_pos
        have hmul : ε * (2 * solverBound) ≤ α := by
          exact (le_div_iff₀ hden_pos).mp hε_le
        have hmul' : solverBound * ε * 2 ≤ α := by
          nlinarith only [hmul]
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr hmul'
      have hsolver_mul_zeta : solverBound * ζ = (1 / 4 : ℝ) := by
        dsimp [ζ]
        field_simp [ne_of_gt hsolverBound_pos]
      have hgreen_mul_eta : greenBound * η = (1 / 4 : ℝ) := by
        dsimp [η]
        field_simp [ne_of_gt hgreen_pos]
      have hsolver_map_budget : solverBound * (ε + ζ * α) ≤ α := by
        have hbudget_sum : solverBound * ε + (1 / 4 : ℝ) * α ≤ α := by
          nlinarith only [hε_le_solver_budget, hα_pos]
        calc
          solverBound * (ε + ζ * α) =
              solverBound * ε + (solverBound * ζ) * α := by ring
          _ = solverBound * ε + (1 / 4 : ℝ) * α := by rw [hsolver_mul_zeta]
          _ ≤ α := hbudget_sum
      refine ⟨ε, hε_pos, ?_⟩
      intro x hxTube hxPseudo
      let k : ℕ → E d := Submission.Shadowing.localTubeAnchorSeq hxTube
      have hk_mem : ∀ n : ℕ, k n ∈ K := by
        intro n
        exact Submission.Shadowing.localTubeAnchorSeq_mem hxTube n
      have hforcing_projection_le :
          ∀ b : Submission.Shadowing.CorrectionSeq d, ∀ n : ℕ,
            ‖Submission.Shadowing.anchorStableProjection hs hxTube n (b n)‖ ≤ M * ‖b‖ ∧
              ‖Submission.Shadowing.anchorUnstableProjection hs hxTube n (b n)‖ ≤
                M * ‖b‖ := by
        intro b n
        exact Submission.Shadowing.anchorProjection_apply_norm_le_of_bound
          (T := T) (K := K) hs hxTube hM_pos.le hM_projection_bound b n
      have hA_bound :
          ∀ n : ℕ,
            ‖Submission.Shadowing.anchorDerivative (T := T) hxTube n‖ ≤
              derivativeBound := by
        intro n
        simpa [Submission.Shadowing.anchorDerivative, Function.iterate_one] using
          (hderivativeBound_spec.2 (k n) (hk_mem n)).1
      have hxk_close : ∀ n : ℕ, ‖x n - k n‖ < ρ := by
        intro n
        exact Submission.Shadowing.localTubeAnchorSeq_close hxTube n
      have hxk_close_r : ∀ n : ℕ, ‖x n - k n‖ < r := by
        intro n
        exact Submission.Shadowing.localTubeAnchorSeq_close_lt hxTube hρ_le_r n
      have hxU : ∀ n : ℕ, x n ∈ U := by
        intro n
        exact hρ_subset_U (hxTube n)
      have hlocal_rem := fun n : ℕ =>
        Submission.Shadowing.localTubeAnchorSeq_remainder (T := T) (K := K)
          (U := U) (η := η) (r := r) (ρ := ρ) hρ_subset_U hρ_le_r hxTube hrem_r n
      have hdefect := fun n : ℕ =>
        Submission.Shadowing.pseudoOrbitDefect_norm_lt (T := T) hxPseudo n
      have htransition := fun n : ℕ =>
        Submission.Shadowing.anchorTransition_decomp (T := T) (K := K) hxTube n
      have hlinear_transition_bound := fun n : ℕ =>
        Submission.Shadowing.anchorTransition_linearDefect_norm_lt (T := T) (K := K)
          hxTube hxPseudo (fun m : ℕ => (hlocal_rem m).1) hη_pos.le n
      have hanchor_transition_bound := fun n : ℕ =>
        Submission.Shadowing.anchorTransition_norm_lt (T := T) (K := K)
          hxTube hxPseudo (fun m : ℕ => (hlocal_rem m).1) hη_pos.le hA_bound n
      have hbase_linear_bound := fun n : ℕ =>
        Submission.Shadowing.baseLinearDefect_norm_lt (T := T) (K := K)
          hxTube hxPseudo (fun m : ℕ => (hlocal_rem m).1) hη_pos.le n
      have htrial_close_r :
          ∀ u : Submission.Shadowing.CorrectionSeq d,
            u ∈ Submission.Shadowing.correctionBall (d := d) α →
              ∀ n : ℕ, ‖(x n + u n) - k n‖ < r := by
        intro u hu n
        exact Submission.Shadowing.correctionBall_trial_close_anchor_lt
            (K := K) (α := α) (ρ := ρ) (r := r) (x := x) (u := u)
            hxTube hu hα_le_ρ_half hρ_margin_r n
      have htrial_tube_ρU :
          ∀ u : Submission.Shadowing.CorrectionSeq d,
            u ∈ Submission.Shadowing.correctionBall (d := d) α →
              ∀ n : ℕ, x n + u n ∈ Submission.Shadowing.localTube K ρU := by
        intro u hu
        exact Submission.Shadowing.correctionBall_trial_mem_localTube
          (K := K) (α := α) (ρ := ρ) (σ := ρU) (x := x) (u := u)
          hxTube hu hα_le_ρ_half hρ_margin_ρU
      have htrialU :
          ∀ u : Submission.Shadowing.CorrectionSeq d,
            u ∈ Submission.Shadowing.correctionBall (d := d) α →
              ∀ n : ℕ, x n + u n ∈ U := by
        intro u hu n
        exact hρU_subset (htrial_tube_ρU u hu n)
      have htrial_rem :
          ∀ u : Submission.Shadowing.CorrectionSeq d,
            u ∈ Submission.Shadowing.correctionBall (d := d) α →
              ∀ n : ℕ,
                ‖T (x n + u n) - T (k n) -
                    fderiv ℝ (T : E d → E d) (k n) ((x n + u n) - k n)‖ ≤
                  η * ‖(x n + u n) - k n‖ ∧
                ‖T.symm (x n + u n) - T.symm (k n) -
                    fderiv ℝ (T.symm : E d → E d) (k n) ((x n + u n) - k n)‖ ≤
                  η * ‖(x n + u n) - k n‖ := by
        intro u hu n
        exact hrem_r (k n) (hk_mem n) (x n + u n) (htrialU u hu n)
          (htrial_close_r u hu n)
      have htrial_nonlinear_bound :
          ∀ u : Submission.Shadowing.CorrectionSeq d,
            u ∈ Submission.Shadowing.correctionBall (d := d) α →
              ∀ n : ℕ,
                ‖Submission.Shadowing.correctionNonlinearRemainder (T := T) (K := K)
                    (x := x) (u := fun n => u n) hxTube n‖ < η * (ρ + α) := by
        intro u hu n
        exact Submission.Shadowing.correctionNonlinearRemainder_norm_lt_of_correctionBall
          (T := T) (K := K) (ρ := ρ) (α := α) (η := η) (x := x) (u := u)
          hxTube hu hη_pos (fun m : ℕ => (htrial_rem u hu m).1) n
      have hresidual_increment_decomp :
          ∀ u : Submission.Shadowing.CorrectionSeq d, ∀ n : ℕ,
            Submission.Shadowing.correctionResidual (T : E d → E d) x (fun n => u n) n =
              fderiv ℝ (T : E d → E d) (k n) (u n) -
                Submission.Shadowing.pseudoOrbitDefect (T : E d → E d) x n +
                  Submission.Shadowing.correctionIncrementRemainder (T := T) (K := K)
                    (x := x) (u := fun n => u n) hxTube n := by
        intro u n
        simpa [k] using
          Submission.Shadowing.correctionResidual_increment_decomp (T := T) (K := K)
            (x := x) (u := fun n => u n) hxTube n
      have htrial_increment_bound :
          ∀ u : Submission.Shadowing.CorrectionSeq d,
            u ∈ Submission.Shadowing.correctionBall (d := d) α →
              ∀ n : ℕ,
                ‖Submission.Shadowing.correctionIncrementRemainder (T := T) (K := K)
                    (x := x) (u := fun n => u n) hxTube n‖ ≤ ζ * ‖u n‖ := by
        intro u hu n
        exact Submission.Shadowing.correctionIncrementRemainder_norm_le (T := T) (K := K)
          (ρ := ρ) (η := ζ) (r := r) (x := x) (u := u) hxTube
          (by
            intro m
            change ‖x m - k m‖ < r
            exact hxk_close_r m)
          (by
            intro m
            change ‖x m + u m - k m‖ < r
            exact htrial_close_r u hu m)
          hSolverIncrement_r n
      have htrial_increment_lipschitz :
          ∀ u : Submission.Shadowing.CorrectionSeq d,
            u ∈ Submission.Shadowing.correctionBall (d := d) α →
              ∀ v : Submission.Shadowing.CorrectionSeq d,
                v ∈ Submission.Shadowing.correctionBall (d := d) α →
                  ∀ n : ℕ,
                    ‖Submission.Shadowing.correctionIncrementRemainder (T := T) (K := K)
                        (x := x) (u := fun n => u n) hxTube n -
                      Submission.Shadowing.correctionIncrementRemainder (T := T) (K := K)
                        (x := x) (u := fun n => v n) hxTube n‖ ≤
                      ζ * ‖u n - v n‖ := by
        intro u hu v hv n
        exact Submission.Shadowing.correctionIncrementRemainder_sub_norm_le (T := T) (K := K)
          (ρ := ρ) (η := ζ) (r := r) (x := x) (u := u) (v := v) hxTube
          (by
            intro m
            change ‖x m + u m - k m‖ < r
            exact htrial_close_r u hu m)
          (by
            intro m
            change ‖x m + v m - k m‖ < r
            exact htrial_close_r v hv m)
          hSolverIncrement_r n
      let defectSeq : Submission.Shadowing.CorrectionSeq d :=
        Submission.Shadowing.pseudoOrbitDefectSeq (T := (T : E d → E d)) x hdefect
      have hdefectSeq_norm_le : ‖defectSeq‖ ≤ ε := by
        dsimp [defectSeq]
        exact Submission.Shadowing.pseudoOrbitDefectSeq_norm_le
          (T := (T : E d → E d)) x hdefect
      let incrementSeq :
          ∀ u : Submission.Shadowing.CorrectionSeq d,
            u ∈ Submission.Shadowing.correctionBall (d := d) α →
              Submission.Shadowing.CorrectionSeq d :=
        fun u hu =>
          Submission.Shadowing.correctionIncrementRemainderSeq (T := T) (K := K)
            hxTube u hζ_pos.le (htrial_increment_bound u hu)
      have htrial_increment_seq_norm :
          ∀ u : Submission.Shadowing.CorrectionSeq d,
            ∀ hu : u ∈ Submission.Shadowing.correctionBall (d := d) α,
              ‖incrementSeq u hu‖ ≤ ζ * ‖u‖ := by
        intro u hu
        dsimp [incrementSeq]
        exact Submission.Shadowing.correctionIncrementRemainderSeq_norm_le (T := T) (K := K)
          hxTube u hζ_pos.le (htrial_increment_bound u hu)
      have htrial_increment_seq_lipschitz :
          ∀ u : Submission.Shadowing.CorrectionSeq d,
            ∀ hu : u ∈ Submission.Shadowing.correctionBall (d := d) α,
              ∀ v : Submission.Shadowing.CorrectionSeq d,
                ∀ hv : v ∈ Submission.Shadowing.correctionBall (d := d) α,
                  ‖incrementSeq u hu - incrementSeq v hv‖ ≤ ζ * ‖u - v‖ := by
        intro u hu v hv
        dsimp [incrementSeq]
        exact Submission.Shadowing.correctionIncrementRemainderSeq_sub_norm_le (T := T) (K := K)
          hxTube hζ_pos.le (htrial_increment_bound u hu) (htrial_increment_bound v hv)
          (htrial_increment_lipschitz u hu v hv)
      have hsolver_to_shadow :
          ∀ solver : Submission.Shadowing.AnchorLinearSolver (T := T) (K := K) hxTube
              solverBound,
            ∃ y : E d, ∀ n : ℕ, ‖x n - ((T : E d → E d)^[n]) y‖ < δ := by
        intro solver
        let R :
            ∀ u : Submission.Shadowing.CorrectionSeq d,
              u ∈ Submission.Shadowing.correctionBall (d := d) α →
                Submission.Shadowing.CorrectionSeq d :=
          fun u hu => incrementSeq u hu
        have hsolver_zeta_le : solverBound * ζ ≤ (1 / 2 : ℝ) := by
          rw [hsolver_mul_zeta]
          norm_num
        have hresidual_for_solver :
            ∀ u : Submission.Shadowing.CorrectionSeq d,
              ∀ hu : u ∈ Submission.Shadowing.correctionBall (d := d) α,
                ∀ n : ℕ,
                  Submission.Shadowing.correctionResidual (T : E d → E d) x
                      (fun n => u n) n =
                    Submission.Shadowing.anchorDerivative (T := T) hxTube n (u n) -
                      defectSeq n + (R u hu) n := by
          intro u hu n
          simpa [R, incrementSeq, defectSeq, Submission.Shadowing.anchorDerivative, k] using
            hresidual_increment_decomp u n
        rcases Submission.Shadowing.exists_correction_recurrence_of_anchorLinearSolver
            (T := T) (K := K) solver hα_pos.le hsolverBound_pos.le hζ_pos.le hsolver_zeta_le
            hdefectSeq_norm_le R htrial_increment_seq_norm htrial_increment_seq_lipschitz
            hsolver_map_budget hresidual_for_solver with
          ⟨u, hu, hrec⟩
        exact Submission.Shadowing.shadowing_from_correction_recurrence T hrec
          (Submission.Shadowing.correctionBall_apply_norm_lt hu hα_lt_delta)
      have hε_le_ρ_half : ε ≤ ρ / 2 := by
        dsimp [ε]
        exact min_le_right (α / (2 * solverBound)) (ρ / 2)
      have hanchor_transition_close_scaled :
          ∀ n : ℕ,
            ‖k (n + 1) - T (k n)‖ < transitionScale * ρ := by
        intro n
        have hbound := hanchor_transition_bound n
        have hbudget_le :
            ρ + ε + (derivativeBound + η) * ρ ≤ transitionScale * ρ := by
          have hhalf_le_ρ : ρ / 2 ≤ ρ := by linarith [hρ_pos]
          have hε_le_ρ : ε ≤ ρ := hε_le_ρ_half.trans hhalf_le_ρ
          have hsmall : ρ + ε ≤ 2 * ρ := by linarith [hε_le_ρ]
          dsimp [transitionScale]
          linarith only [hsmall]
        have hbound' :
            ‖k (n + 1) - T (k n)‖ <
              ρ + ε + (derivativeBound + η) * ρ := by
          simpa [k] using hbound
        exact lt_of_lt_of_le hbound' hbudget_le
      have htracking_budget :
          ∀ j : ℕ, j ≤ blockN →
            Submission.Shadowing.finiteTrackingAmplification (derivativeBound + η) j *
                (transitionScale * ρ) < rLocal := by
        intro j hj
        have hρ_le_tracking : ρ ≤ rTracking :=
          hρ_le_r.trans (hr_le_rBridge.trans hrBridge_le_tracking)
        have hden_pos : 0 < 4 * transitionScale * trackingScale := by
          exact mul_pos (mul_pos (by norm_num) htransitionScale_pos) htrackingScale_pos
        have hmul : ρ * (4 * transitionScale * trackingScale) ≤ rLocal :=
          (le_div_iff₀ hden_pos).mp hρ_le_tracking
        have hcap_term_le_quarter :
            trackingScale * (transitionScale * ρ) ≤ rLocal / 4 := by
          have hmul' : 4 * (trackingScale * (transitionScale * ρ)) ≤ rLocal := by
            calc
              4 * (trackingScale * (transitionScale * ρ)) =
                  ρ * (4 * transitionScale * trackingScale) := by ring
              _ ≤ rLocal := hmul
          have hmul'' : trackingScale * (transitionScale * ρ) * 4 ≤ rLocal := by
            calc
              trackingScale * (transitionScale * ρ) * 4 =
                  4 * (trackingScale * (transitionScale * ρ)) := by ring
              _ ≤ rLocal := hmul'
          exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr hmul''
        have hamp_le := htrackingScale_ge j hj
        have hterm_le :
            Submission.Shadowing.finiteTrackingAmplification (derivativeBound + η) j *
                (transitionScale * ρ) ≤
              trackingScale * (transitionScale * ρ) := by
          exact mul_le_mul_of_nonneg_right hamp_le
            (mul_nonneg htransitionScale_pos.le hρ_pos.le)
        have hquarter_lt : rLocal / 4 < rLocal := by nlinarith only [hrLocal_pos]
        exact lt_of_le_of_lt (hterm_le.trans hcap_term_le_quarter) hquarter_lt
      have hblock_tracking :
          ∀ n j : ℕ, j ≤ blockN →
            ‖k (n + j) - ((T : E d → E d)^[j]) (k n)‖ < rLocal := by
        intro n j hj
        exact Submission.Shadowing.selectedAnchorBlockTracking_lt
          (T := T) (K := K) (ρ := ρ) (τ := transitionScale * ρ) (η := η)
          (L := derivativeBound) (r := rLocal) hxTube
          (mul_nonneg htransitionScale_pos.le hρ_pos.le) hη_pos.le
          hderivativeBound_spec.1 hA_bound hanchor_transition_close_scaled
          (by
            intro a ha z w hz hw
            exact hIncrementRaw a ha z w
              (lt_of_lt_of_le hz hrLocal_le_rIncrement)
              (lt_of_lt_of_le hw hrLocal_le_rIncrement))
          htracking_budget n j hj
      have hanchor_fwd_step_deriv_close :
          ∀ n j : ℕ, j < blockN →
            ‖Submission.Shadowing.anchorDerivative (T := T) hxTube (n + j) -
                fderiv ℝ (T : E d → E d)
                  (((T : E d → E d)^[j])
                    (Submission.Shadowing.localTubeAnchorSeq hxTube n))‖ ≤
              productStepTol := by
        intro n j hj
        have htrack :
            ‖k (n + j) -
                ((T : E d → E d)^[j])
                  (Submission.Shadowing.localTubeAnchorSeq hxTube n)‖ < rLocal := by
          change ‖k (n + j) - ((T : E d → E d)^[j]) (k n)‖ < rLocal
          exact hblock_tracking n j (Nat.le_of_lt hj)
        simpa [Submission.Shadowing.anchorDerivative, k] using
          hStepFwdDeriv_rLocal
            (((T : E d → E d)^[j]) (Submission.Shadowing.localTubeAnchorSeq hxTube n))
            (Submission.Shadowing.forward_iterate_mem hs
              (Submission.Shadowing.localTubeAnchorSeq_mem hxTube n) j)
            (k (n + j)) htrack
      have hanchor_fwd_step_bound :
          ∀ n j : ℕ, j < blockN →
            ‖Submission.Shadowing.anchorDerivative (T := T) hxTube (n + j)‖ ≤
              derivativeBound := by
        intro n j _hj
        exact hA_bound (n + j)
      have hselected_fwd_product_bound :
          ∀ n m : ℕ, m ≤ blockN → ∀ v : E d,
            ‖Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n m v‖ ≤
              derivativeBound ^ m * ‖v‖ := by
        intro n m hm v
        exact Submission.Shadowing.anchorDerivativeProduct_apply_norm_le_of_step_bound
          (T := T) (K := K) hxTube hderivativeBound_spec.1
          (fun j hj => hanchor_fwd_step_bound n j (Nat.lt_of_lt_of_le hj hm)) v
      have htrue_fwd_step_bound :
          ∀ n j : ℕ, j < blockN →
            ‖fderiv ℝ (T : E d → E d)
                (((T : E d → E d)^[j])
                  (Submission.Shadowing.localTubeAnchorSeq hxTube n))‖ ≤ derivativeBound := by
        intro n j _hj
        simpa [Function.iterate_one] using
          (hderivativeBound_spec.2
            (((T : E d → E d)^[j]) (Submission.Shadowing.localTubeAnchorSeq hxTube n))
            (Submission.Shadowing.forward_iterate_mem hs
              (Submission.Shadowing.localTubeAnchorSeq_mem hxTube n) j)).1
      have hselected_fwd_product_perturbation_local :
          ∀ n : ℕ, ∀ v : E d,
            ‖Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n blockN v -
                fderiv ℝ ((T : E d → E d)^[blockN])
                  (Submission.Shadowing.localTubeAnchorSeq hxTube n) v‖ ≤
              Submission.Shadowing.finiteProductPerturbation derivativeBound productStepTol blockN *
                ‖v‖ := by
        intro n v
        exact Submission.Shadowing.anchorDerivativeProduct_fderiv_iterate_apply_norm_sub_le
          (T := T) (K := K) (B := derivativeBound) (ξ := productStepTol)
          (N := blockN) hs hxTube hderivativeBound_spec.1 hproductStepTol_nonneg
          hanchor_fwd_step_bound htrue_fwd_step_bound hanchor_fwd_step_deriv_close
          n blockN le_rfl v
      have hselected_fwd_product_perturbation :
          ∀ n : ℕ, ∀ v : E d,
            ‖Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n blockN v -
                fderiv ℝ ((T : E d → E d)^[blockN]) (k n) v‖ ≤
              Submission.Shadowing.finiteProductPerturbation derivativeBound productStepTol blockN *
                ‖v‖ := by
        intro n v
        change
          ‖Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n blockN v -
              fderiv ℝ ((T : E d → E d)^[blockN])
                (Submission.Shadowing.localTubeAnchorSeq hxTube n) v‖ ≤
            Submission.Shadowing.finiteProductPerturbation derivativeBound productStepTol blockN *
              ‖v‖
        exact hselected_fwd_product_perturbation_local n v
      have hselected_fwd_product_perturbation_small :
          ∀ n : ℕ, ∀ v : E d,
            ‖Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n blockN v -
                fderiv ℝ ((T : E d → E d)^[blockN]) (k n) v‖ ≤
              (η / 16) * ‖v‖ := by
        intro n v
        exact (hselected_fwd_product_perturbation n v).trans
          (mul_le_mul_of_nonneg_right hproductPerturbation_le (norm_nonneg v))
      have htrue_fwd_product_stable_le :
          ∀ n : ℕ, ∀ vs : E d, vs ∈ hs.stable (k n) →
            ‖fderiv ℝ ((T : E d → E d)^[blockN]) (k n) vs‖ ≤
              (η / 16) * ‖vs‖ := by
        intro n vs hvs
        exact (hs.contract_stable (k n) (hk_mem n) vs hvs blockN).trans
          (mul_le_mul_of_nonneg_right (le_of_lt hblock_contract) (norm_nonneg vs))
      have hselected_fwd_product_stable_le :
          ∀ n : ℕ, ∀ vs : E d, vs ∈ hs.stable (k n) →
            ‖Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n blockN vs‖ ≤
              (η / 8) * ‖vs‖ := by
        intro n vs hvs
        let P : E d →L[ℝ] E d :=
          Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n blockN
        let Q : E d →L[ℝ] E d :=
          fderiv ℝ ((T : E d → E d)^[blockN]) (k n)
        have hpert : ‖P vs - Q vs‖ ≤ (η / 16) * ‖vs‖ := by
          dsimp [P, Q]
          exact hselected_fwd_product_perturbation_small n vs
        have hexact : ‖Q vs‖ ≤ (η / 16) * ‖vs‖ := by
          dsimp [Q]
          exact (hs.contract_stable (k n) (hk_mem n) vs hvs blockN).trans
            (mul_le_mul_of_nonneg_right (le_of_lt hblock_contract) (norm_nonneg vs))
        have hdecomp : P vs = (P vs - Q vs) + Q vs := by
          abel
        calc
          ‖P vs‖ = ‖(P vs - Q vs) + Q vs‖ := congrArg norm hdecomp
          _ ≤ ‖P vs - Q vs‖ + ‖Q vs‖ := norm_add_le _ _
          _ ≤ (η / 16) * ‖vs‖ + (η / 16) * ‖vs‖ := add_le_add hpert hexact
          _ = (η / 8) * ‖vs‖ := by
            ring
      have hblock_endpoint_close_stable_leak :
          ∀ n : ℕ, ‖k (n + blockN) - ((T : E d → E d)^[blockN]) (k n)‖ <
            rStableEndpointLeak := by
        intro n
        exact lt_of_lt_of_le (hblock_tracking n blockN le_rfl)
          (hrLocal_le_rLeak.trans hrLeak_le_stable_endpoint)
      have hblock_endpoint_close_unstable_leak :
          ∀ n : ℕ, ‖k (n + blockN) - ((T : E d → E d)^[blockN]) (k n)‖ <
            rUnstableEndpointLeak := by
        intro n
        exact lt_of_lt_of_le (hblock_tracking n blockN le_rfl)
          (hrLocal_le_rLeak.trans hrLeak_le_unstable_endpoint)
      have hselected_fwd_endpoint_projection_le :
          ∀ n : ℕ, ∀ vs : E d, vs ∈ hs.stable (k n) →
            ‖Submission.Shadowing.anchorStableProjection hs hxTube (n + blockN)
                (Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n blockN vs)‖ ≤
                M * ((η / 16) * ‖vs‖ + (η / 16) * ‖vs‖) ∧
              ‖Submission.Shadowing.anchorUnstableProjection hs hxTube (n + blockN)
                (Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n blockN vs)‖ ≤
                M * ((η / 16) * ‖vs‖) + endpointLeakTol * ((η / 16) * ‖vs‖) := by
        intro n vs hvs
        have hpert_local :
            ∀ v : E d,
              ‖Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n blockN v -
                  fderiv ℝ ((T : E d → E d)^[blockN])
                    (Submission.Shadowing.localTubeAnchorSeq hxTube n) v‖ ≤
                (η / 16) * ‖v‖ := by
          intro v
          simpa [k] using hselected_fwd_product_perturbation_small n v
        have hexact_local :
            ∀ v : E d, v ∈ hs.stable (Submission.Shadowing.localTubeAnchorSeq hxTube n) →
              ‖fderiv ℝ ((T : E d → E d)^[blockN])
                  (Submission.Shadowing.localTubeAnchorSeq hxTube n) v‖ ≤
                (η / 16) * ‖v‖ := by
          intro v hv
          simpa [k] using htrue_fwd_product_stable_le n v hv
        have hendpoint_local :
            ‖Submission.Shadowing.localTubeAnchorSeq hxTube (n + blockN) -
                ((T : E d → E d)^[blockN])
                  (Submission.Shadowing.localTubeAnchorSeq hxTube n)‖ <
              rStableEndpointLeak := by
          simpa [k] using hblock_endpoint_close_stable_leak n
        have hvs_local : vs ∈ hs.stable (Submission.Shadowing.localTubeAnchorSeq hxTube n) := by
          simpa [k] using hvs
        simpa [k] using
          Submission.Shadowing.selectedForwardStableBlock_endpoint_projection_le
            (T := T) (K := K) hs hxTube hendpointLeakTol_nonneg hM_pos.le
            hM_projection_bound hstable_endpoint_leak
            (n := n) (N := blockN) hendpoint_local hpert_local hexact_local hvs_local
      have hanchor_bwd_step_deriv_close :
          ∀ n j : ℕ, j < blockN →
            ‖Submission.Shadowing.anchorInverseDerivative (T := T) hxTube (n + j) -
                fderiv ℝ (T.symm : E d → E d)
                  (((T : E d → E d)^[j + 1]) (k n))‖ ≤
              productStepTol := by
        intro n j hj
        let a : E d := ((T : E d → E d)^[j]) (k n)
        have ha : a ∈ K := by
          dsimp [a]
          exact Submission.Shadowing.forward_iterate_mem hs (hk_mem n) j
        have hnext_mem : ((T : E d → E d)^[j + 1]) (k n) ∈ K :=
          Submission.Shadowing.forward_iterate_mem hs (hk_mem n) (j + 1)
        have hTa : T a = ((T : E d → E d)^[j + 1]) (k n) := by
          dsimp [a]
          simpa [Function.iterate_succ] using
            (Submission.Shadowing.iterate_apply_self_comm_aux
              (T : E d → E d) j (k n)).symm
        have htrack : ‖k (n + j) - a‖ < rLocal := by
          dsimp [a]
          exact hblock_tracking n j (Nat.le_of_lt hj)
        have htrack_increment : ‖k (n + j) - a‖ < rIncrement :=
          lt_of_lt_of_le htrack hrLocal_le_rIncrement
        have hzero_increment : ‖a - a‖ < rIncrement := by
          simpa using hrIncrement_pos
        have hlin :
            ‖T (k (n + j)) - T a -
                fderiv ℝ (T : E d → E d) a (k (n + j) - a)‖ ≤
              η * ‖k (n + j) - a‖ :=
          hIncrementRaw a ha (k (n + j)) a htrack_increment hzero_increment
        have hDop : ‖fderiv ℝ (T : E d → E d) a‖ ≤ derivativeBound := by
          simpa [a, Function.iterate_one] using (hderivativeBound_spec.2 a ha).1
        have hDnorm :
            ‖fderiv ℝ (T : E d → E d) a (k (n + j) - a)‖ ≤
              derivativeBound * ‖k (n + j) - a‖ := by
          calc
            ‖fderiv ℝ (T : E d → E d) a (k (n + j) - a)‖ ≤
                ‖fderiv ℝ (T : E d → E d) a‖ * ‖k (n + j) - a‖ :=
              (fderiv ℝ (T : E d → E d) a).le_opNorm (k (n + j) - a)
            _ ≤ derivativeBound * ‖k (n + j) - a‖ :=
              mul_le_mul_of_nonneg_right hDop (norm_nonneg _)
        have himage_norm_le :
            ‖T (k (n + j)) - T a‖ ≤
              (η + derivativeBound) * ‖k (n + j) - a‖ := by
          have hdecomp :
              T (k (n + j)) - T a =
                (T (k (n + j)) - T a -
                    fderiv ℝ (T : E d → E d) a (k (n + j) - a)) +
                  fderiv ℝ (T : E d → E d) a (k (n + j) - a) := by
            abel
          calc
            ‖T (k (n + j)) - T a‖ =
                ‖(T (k (n + j)) - T a -
                    fderiv ℝ (T : E d → E d) a (k (n + j) - a)) +
                  fderiv ℝ (T : E d → E d) a (k (n + j) - a)‖ := by
              exact congrArg norm hdecomp
            _ ≤
                ‖T (k (n + j)) - T a -
                    fderiv ℝ (T : E d → E d) a (k (n + j) - a)‖ +
                  ‖fderiv ℝ (T : E d → E d) a (k (n + j) - a)‖ :=
              norm_add_le _ _
            _ ≤ η * ‖k (n + j) - a‖ +
                derivativeBound * ‖k (n + j) - a‖ := add_le_add hlin hDnorm
            _ = (η + derivativeBound) * ‖k (n + j) - a‖ := by ring
        have hdist_budget : ‖k (n + j) - a‖ < rStepBwdImage :=
          lt_of_lt_of_le htrack hrLocal_le_rStepBwdImage
        have hdist_budget_div :
            ‖k (n + j) - a‖ <
              rStepBwd / (2 * (derivativeBound + η + 1)) := by
          simpa [rStepBwdImage] using hdist_budget
        have hden_pos : 0 < 2 * (derivativeBound + η + 1) := by
          nlinarith [hderivativeBound_spec.1, hη_pos]
        have hmul_budget :
            ‖k (n + j) - a‖ * (2 * (derivativeBound + η + 1)) < rStepBwd :=
          (lt_div_iff₀ hden_pos).mp hdist_budget_div
        have hscale_nonneg : 0 ≤ η + derivativeBound := by
          nlinarith [hderivativeBound_spec.1, hη_pos]
        have hscale_le : η + derivativeBound ≤ derivativeBound + η + 1 := by
          linarith
        have hdist_nonneg : 0 ≤ ‖k (n + j) - a‖ := norm_nonneg _
        have hscale_mul_le :
            ‖k (n + j) - a‖ * (η + derivativeBound) ≤
              ‖k (n + j) - a‖ * (derivativeBound + η + 1) :=
          mul_le_mul_of_nonneg_left hscale_le hdist_nonneg
        have htwice_le :
            2 * ((η + derivativeBound) * ‖k (n + j) - a‖) ≤
              ‖k (n + j) - a‖ * (2 * (derivativeBound + η + 1)) := by
          calc
            2 * ((η + derivativeBound) * ‖k (n + j) - a‖) =
                2 * (‖k (n + j) - a‖ * (η + derivativeBound)) := by ring
            _ ≤ 2 * (‖k (n + j) - a‖ * (derivativeBound + η + 1)) :=
              mul_le_mul_of_nonneg_left hscale_mul_le (by norm_num)
            _ = ‖k (n + j) - a‖ * (2 * (derivativeBound + η + 1)) := by ring
        have htwice_lt :
            2 * ((η + derivativeBound) * ‖k (n + j) - a‖) < rStepBwd :=
          lt_of_le_of_lt htwice_le hmul_budget
        have hscale_mul_nonneg :
            0 ≤ (η + derivativeBound) * ‖k (n + j) - a‖ :=
          mul_nonneg hscale_nonneg hdist_nonneg
        have hscale_mul_lt :
            (η + derivativeBound) * ‖k (n + j) - a‖ < rStepBwd := by
          calc
            (η + derivativeBound) * ‖k (n + j) - a‖ =
                1 * ((η + derivativeBound) * ‖k (n + j) - a‖) := by ring
            _ ≤ 2 * ((η + derivativeBound) * ‖k (n + j) - a‖) :=
              mul_le_mul_of_nonneg_right (by norm_num) hscale_mul_nonneg
            _ < rStepBwd := htwice_lt
        have himage_lt_raw : ‖T (k (n + j)) - T a‖ < rStepBwd :=
          lt_of_le_of_lt himage_norm_le hscale_mul_lt
        have himage_lt :
            ‖T (k (n + j)) - ((T : E d → E d)^[j + 1]) (k n)‖ < rStepBwd := by
          simpa [hTa] using himage_lt_raw
        simpa [Submission.Shadowing.anchorInverseDerivative, k] using
          hStepBwdDeriv (((T : E d → E d)^[j + 1]) (k n)) hnext_mem
            (T (k (n + j))) himage_lt
      have hanchor_bwd_step_bound :
          ∀ n j : ℕ, j < blockN →
            ‖Submission.Shadowing.anchorInverseDerivative (T := T) hxTube (n + j)‖ ≤
              derivativeBound := by
        intro n j _hj
        simpa [Submission.Shadowing.anchorInverseDerivative, Function.iterate_one, k] using
          (hderivativeBound_spec.2 (T (k (n + j)))
            (Submission.Shadowing.forward_mem hs (hk_mem (n + j)))).2
      have htrue_bwd_step_bound :
          ∀ n j : ℕ, j < blockN →
            ‖fderiv ℝ (T.symm : E d → E d)
                (((T : E d → E d)^[j + 1]) (k n))‖ ≤ derivativeBound := by
        intro n j _hj
        simpa [Function.iterate_one] using
          (hderivativeBound_spec.2 (((T : E d → E d)^[j + 1]) (k n))
            (Submission.Shadowing.forward_iterate_mem hs (hk_mem n) (j + 1))).2
      have hselected_bwd_product_perturbation :
          ∀ n : ℕ, ∀ v : E d,
            ‖Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n blockN v -
                fderiv ℝ ((T.symm : E d → E d)^[blockN])
                  (((T : E d → E d)^[blockN]) (k n)) v‖ ≤
              Submission.Shadowing.finiteProductPerturbation derivativeBound productStepTol blockN *
                ‖v‖ := by
        intro n v
        simpa [k] using
          Submission.Shadowing.anchorInverseDerivativeProduct_fderiv_symm_iterate_apply_norm_sub_le
            (T := T) (K := K) (B := derivativeBound) (ξ := productStepTol)
            (N := blockN) hs hxTube hderivativeBound_spec.1 hproductStepTol_nonneg
            hanchor_bwd_step_bound htrue_bwd_step_bound hanchor_bwd_step_deriv_close
            n blockN le_rfl v
      have hselected_bwd_product_perturbation_small :
          ∀ n : ℕ, ∀ v : E d,
            ‖Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n blockN v -
                fderiv ℝ ((T.symm : E d → E d)^[blockN])
                  (((T : E d → E d)^[blockN]) (k n)) v‖ ≤
              (η / 16) * ‖v‖ := by
        intro n v
        exact (hselected_bwd_product_perturbation n v).trans
          (mul_le_mul_of_nonneg_right hproductPerturbation_le (norm_nonneg v))
      have hselected_bwd_product_unstable_le :
          ∀ n : ℕ, ∀ vu : E d,
            vu ∈ hs.unstable (((T : E d → E d)^[blockN]) (k n)) →
              ‖Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n
                  blockN vu‖ ≤
                (η / 8) * ‖vu‖ := by
        intro n vu hvu
        let P : E d →L[ℝ] E d :=
          Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n blockN
        let Q : E d →L[ℝ] E d :=
          fderiv ℝ ((T.symm : E d → E d)^[blockN])
            (((T : E d → E d)^[blockN]) (k n))
        have hpert : ‖P vu - Q vu‖ ≤ (η / 16) * ‖vu‖ := by
          dsimp [P, Q]
          exact hselected_bwd_product_perturbation_small n vu
        have hexact : ‖Q vu‖ ≤ (η / 16) * ‖vu‖ := by
          dsimp [Q]
          exact (hs.contract_unstable (((T : E d → E d)^[blockN]) (k n))
              (Submission.Shadowing.forward_iterate_mem hs (hk_mem n) blockN)
              vu hvu blockN).trans
            (mul_le_mul_of_nonneg_right (le_of_lt hblock_contract) (norm_nonneg vu))
        have hdecomp : P vu = (P vu - Q vu) + Q vu := by
          abel
        calc
          ‖P vu‖ = ‖(P vu - Q vu) + Q vu‖ := congrArg norm hdecomp
          _ ≤ ‖P vu - Q vu‖ + ‖Q vu‖ := norm_add_le _ _
          _ ≤ (η / 16) * ‖vu‖ + (η / 16) * ‖vu‖ := add_le_add hpert hexact
          _ = (η / 8) * ‖vu‖ := by
            ring
      have hselected_bwd_product_bound_finite :
          ∀ n m : ℕ, m ≤ blockN → ∀ v : E d,
            ‖Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n
                m v‖ ≤ derivativeBound ^ m * ‖v‖ := by
        intro n m hm v
        exact Submission.Shadowing.anchorInverseDerivativeProduct_apply_norm_le_of_step_bound
          (T := T) (K := K) hxTube hderivativeBound_spec.1
          (fun j hj => hanchor_bwd_step_bound n j (Nat.lt_of_lt_of_le hj hm)) v
      have hselected_bwd_product_bound :
          ∀ n : ℕ, ∀ v : E d,
            ‖Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n
                blockN v‖ ≤ derivativeBound ^ blockN * ‖v‖ := by
        intro n v
        exact hselected_bwd_product_bound_finite n blockN le_rfl v
      have hselected_bwd_endpoint_projection_le :
          ∀ n : ℕ, ∀ vu : E d, vu ∈ hs.unstable (k (n + blockN)) →
            ‖Submission.Shadowing.anchorStableProjection hs hxTube n
                (Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n
                  blockN vu)‖ ≤
                M * (derivativeBound ^ blockN * (endpointLeakTol * ‖vu‖) +
                  (η / 8) * (M * ‖vu‖)) ∧
              ‖Submission.Shadowing.anchorUnstableProjection hs hxTube n
                (Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n
                  blockN vu)‖ ≤
                M * (derivativeBound ^ blockN * (endpointLeakTol * ‖vu‖) +
                  (η / 8) * (M * ‖vu‖)) := by
        intro n vu hvu
        have hendpoint_local :
            ‖Submission.Shadowing.localTubeAnchorSeq hxTube (n + blockN) -
                ((T : E d → E d)^[blockN])
                  (Submission.Shadowing.localTubeAnchorSeq hxTube n)‖ <
              rUnstableEndpointLeak := by
          simpa [k] using hblock_endpoint_close_unstable_leak n
        have hback_bound_local :
            ∀ v : E d,
              ‖Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n
                  blockN v‖ ≤ derivativeBound ^ blockN * ‖v‖ := by
          intro v
          exact hselected_bwd_product_bound n v
        have hcontract_local :
            ∀ v : E d,
              v ∈ hs.unstable
                (((T : E d → E d)^[blockN])
                  (Submission.Shadowing.localTubeAnchorSeq hxTube n)) →
                ‖Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n
                    blockN v‖ ≤ (η / 8) * ‖v‖ := by
          intro v hv
          simpa [k] using hselected_bwd_product_unstable_le n v hv
        have hvu_local :
            vu ∈ hs.unstable (Submission.Shadowing.localTubeAnchorSeq hxTube (n + blockN)) := by
          simpa [k] using hvu
        simpa [k] using
          Submission.Shadowing.selectedBackwardUnstableBlock_endpoint_projection_le
            (T := T) (K := K) hs hxTube hendpointLeakTol_nonneg hM_pos.le
            (pow_nonneg hderivativeBound_spec.1 blockN)
            (by positivity : 0 ≤ η / 8) hM_projection_bound hunstable_endpoint_leak
            (n := n) (N := blockN) hendpoint_local hback_bound_local hcontract_local hvu_local
      let blockQ : ℝ := 1 / 16
      have hblockQ_nonneg : 0 ≤ blockQ := by
        dsimp [blockQ]
        norm_num
      have hblockQ_lt_one : blockQ < 1 := by
        dsimp [blockQ]
        norm_num
      have hendpointLeak_first_term_le :
          M * (blockGrowth * endpointLeakTol) ≤ (1 / 64 : ℝ) := by
        simpa [endpointLeakTol] using
          Submission.Shadowing.endpointLeak_first_term_le
            (M := M) (L := blockGrowth) hM_pos.le hblockGrowth_nonneg
      have hgreen_ge_quad : 64 * M * M ≤ greenBound := by
        have hden_pos : 0 < 1 - hs.rate := sub_pos.mpr hs.rate_lt_one
        have hlinear_nonneg : 0 ≤ 64 * M := by
          exact mul_nonneg (by norm_num) hM_pos.le
        have hnum_nonneg : 0 ≤ 4 * M * hs.const := by
          exact mul_nonneg (mul_nonneg (by norm_num) hM_pos.le) hs.const_pos.le
        have hmain_nonneg : 0 ≤ 4 * M * hs.const / (1 - hs.rate) := by
          exact div_nonneg hnum_nonneg hden_pos.le
        change 64 * M * M ≤
          64 * M * M + 64 * M + 4 * M * hs.const / (1 - hs.rate) + 1
        linarith only [hlinear_nonneg, hmain_nonneg]
      have hendpointLeak_second_term_le :
          M * ((η / 8) * M) ≤ (1 / 64 : ℝ) := by
        exact Submission.Shadowing.endpointLeak_second_term_le
          (M := M) (η := η) (G := greenBound) hM_pos.le hη_pos.le hgreen_mul_eta
          hgreen_ge_quad
      have hselected_bwd_endpoint_coeff_le :
          M * (blockGrowth * endpointLeakTol + (η / 8) * M) ≤ blockQ := by
        exact Submission.Shadowing.selectedBackwardEndpointCoeff_le
          (M := M) (L := blockGrowth) (η := η) (endpointLeakTol := endpointLeakTol)
          (q := blockQ) hendpointLeak_first_term_le hendpointLeak_second_term_le
          (by dsimp [blockQ]; norm_num)
      have hselected_bwd_endpoint_strict_le :
          ∀ n : ℕ, ∀ vu : E d, vu ∈ hs.unstable (k (n + blockN)) →
            ‖Submission.Shadowing.anchorStableProjection hs hxTube n
                (Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n
                  blockN vu)‖ ≤ blockQ * ‖vu‖ ∧
              ‖Submission.Shadowing.anchorUnstableProjection hs hxTube n
                (Submission.Shadowing.anchorInverseDerivativeProduct (T := T) hxTube n
                  blockN vu)‖ ≤ blockQ * ‖vu‖ := by
        intro n vu hvu
        have hraw := hselected_bwd_endpoint_projection_le n vu hvu
        have hcoef_norm :
            M * (derivativeBound ^ blockN * (endpointLeakTol * ‖vu‖) +
                (η / 8) * (M * ‖vu‖)) ≤ blockQ * ‖vu‖ := by
          have hnorm_nonneg : 0 ≤ ‖vu‖ := norm_nonneg vu
          simpa [blockGrowth] using
            Submission.Shadowing.selectedBackwardEndpointNorm_le
              (M := M) (L := blockGrowth) (η := η) (endpointLeakTol := endpointLeakTol)
              (q := blockQ) (r := ‖vu‖) hnorm_nonneg
              hselected_bwd_endpoint_coeff_le
        exact ⟨hraw.1.trans hcoef_norm, hraw.2.trans hcoef_norm⟩
      have hgreen_ge_M : M ≤ greenBound := by
        simpa [greenBound] using
          Submission.Shadowing.selectedGreenBound_ge_M
            (M := M) (C := hs.const) (rate := hs.rate) hM_pos hs.const_pos hs.rate_lt_one
      have hgreen_ge_M_add_one : M + 1 ≤ greenBound := by
        simpa [greenBound] using
          Submission.Shadowing.selectedGreenBound_ge_M_add_one
            (M := M) (C := hs.const) (rate := hs.rate) hM_pos hs.const_pos hs.rate_lt_one
      have hendpointLeakTol_le_one : endpointLeakTol ≤ 1 := by
        simpa [endpointLeakTol] using
          Submission.Shadowing.endpointLeakTol_le_one
            (M := M) (L := blockGrowth) hM_pos.le hblockGrowth_nonneg
      have hselected_fwd_stable_coeff_le :
          M * (η / 8) ≤ blockQ := by
        exact Submission.Shadowing.selectedForwardStableEndpointCoeff_le
          (M := M) (η := η) (G := greenBound) (q := blockQ)
          hη_pos.le hgreen_mul_eta hgreen_ge_M (by dsimp [blockQ]; norm_num)
      have hselected_fwd_unstable_coeff_le :
          M * (η / 16) + endpointLeakTol * (η / 16) ≤ blockQ := by
        exact Submission.Shadowing.selectedForwardUnstableEndpointCoeff_le
          (M := M) (η := η) (endpointLeakTol := endpointLeakTol) (G := greenBound)
          (q := blockQ) hη_pos.le hendpointLeakTol_le_one hgreen_mul_eta
          hgreen_ge_M_add_one (by dsimp [blockQ]; norm_num)
      have hselected_fwd_endpoint_strict_le :
          ∀ n : ℕ, ∀ vs : E d, vs ∈ hs.stable (k n) →
            ‖Submission.Shadowing.anchorStableProjection hs hxTube (n + blockN)
                (Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n
                  blockN vs)‖ ≤ blockQ * ‖vs‖ ∧
              ‖Submission.Shadowing.anchorUnstableProjection hs hxTube (n + blockN)
                (Submission.Shadowing.anchorDerivativeProduct (T := T) hxTube n
                  blockN vs)‖ ≤ blockQ * ‖vs‖ := by
        intro n vs hvs
        have hraw := hselected_fwd_endpoint_projection_le n vs hvs
        have hnorm_nonneg : 0 ≤ ‖vs‖ := norm_nonneg vs
        have hstable_norm :
            M * ((η / 16) * ‖vs‖ + (η / 16) * ‖vs‖) ≤ blockQ * ‖vs‖ :=
          Submission.Shadowing.selectedForwardStableEndpointNorm_le
            (M := M) (η := η) (q := blockQ) (r := ‖vs‖) hnorm_nonneg
            hselected_fwd_stable_coeff_le
        have hunstable_norm :
            M * ((η / 16) * ‖vs‖) + endpointLeakTol * ((η / 16) * ‖vs‖) ≤
              blockQ * ‖vs‖ :=
          Submission.Shadowing.selectedForwardUnstableEndpointNorm_le
            (M := M) (η := η) (endpointLeakTol := endpointLeakTol)
            (q := blockQ) (r := ‖vs‖) hnorm_nonneg hselected_fwd_unstable_coeff_le
        exact ⟨hraw.1.trans hstable_norm, hraw.2.trans hunstable_norm⟩
      have hanchor_transition_close_bridge :
          ∀ n : ℕ,
            ‖k (n + 1) - T (k n)‖ < rLeak := by
        intro n
        have hscale_le_quarter : transitionScale * ρ ≤ rLeak / 4 := by
          have hden_pos : 0 < 4 * transitionScale := by
            exact mul_pos (by norm_num) htransitionScale_pos
          have hρ_le_bridge_unfold : ρ ≤ rLeak / (4 * transitionScale) := by
            exact hρ_le_rBridge.trans hrBridge_le_leak
          have hmul : ρ * (4 * transitionScale) ≤ rLeak :=
            (le_div_iff₀ hden_pos).mp hρ_le_bridge_unfold
          have hmul' : 4 * (transitionScale * ρ) ≤ rLeak := by
            calc
              4 * (transitionScale * ρ) = ρ * (4 * transitionScale) := by ring
              _ ≤ rLeak := hmul
          have hmul'' : transitionScale * ρ * 4 ≤ rLeak := by
            calc
              transitionScale * ρ * 4 = 4 * (transitionScale * ρ) := by ring
              _ ≤ rLeak := hmul'
          exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr hmul''
        have hquarter_le : rLeak / 4 ≤ rLeak := by
          have hmul : rLeak ≤ rLeak * 4 := by
            calc
              rLeak = rLeak * 1 := by rw [mul_one]
              _ ≤ rLeak * 4 :=
                mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) ≤ 4) hrLeak_pos.le
          exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr hmul
        exact lt_of_lt_of_le (hanchor_transition_close_scaled n)
          (hscale_le_quarter.trans hquarter_le)
      have hanchor_transition_close_stable_leak :
          ∀ n : ℕ,
            ‖k (n + 1) - T (k n)‖ < rStableLeak := by
        intro n
        exact lt_of_lt_of_le (hanchor_transition_close_bridge n) hrLeak_le_stable
      have hanchor_transition_close_unstable_leak :
          ∀ n : ℕ,
            ‖k (n + 1) - T (k n)‖ < rUnstableLeak := by
        intro n
        exact lt_of_lt_of_le (hanchor_transition_close_bridge n) hrLeak_le_unstable
      have hanchor_stable_leak :
          ∀ n : ℕ, ∀ v : E d, v ∈ hs.stable (T (k n)) →
            ‖Submission.Shadowing.unstableProjection hs (k (n + 1)) (hk_mem (n + 1)) v‖ ≤
              η * ‖v‖ := by
        intro n v hv
        exact hstable_leak (T (k n)) (Submission.Shadowing.forward_mem hs (hk_mem n))
          (k (n + 1)) (hk_mem (n + 1)) (hanchor_transition_close_stable_leak n) v hv
      have hanchor_stable_leak_local :
          ∀ n : ℕ, ∀ v : E d,
            v ∈ hs.stable (T (Submission.Shadowing.localTubeAnchorSeq hxTube n)) →
              ‖Submission.Shadowing.unstableProjection hs
                  (Submission.Shadowing.localTubeAnchorSeq hxTube (n + 1))
                  (Submission.Shadowing.localTubeAnchorSeq_mem hxTube (n + 1)) v‖ ≤
                η * ‖v‖ := by
        intro n v hv
        change ‖Submission.Shadowing.unstableProjection hs (k (n + 1)) (hk_mem (n + 1)) v‖ ≤
          η * ‖v‖
        exact hanchor_stable_leak n v hv
      have hanchor_unstable_leak :
          ∀ n : ℕ, ∀ v : E d, v ∈ hs.unstable (T (k n)) →
            ‖Submission.Shadowing.stableProjection hs (k (n + 1)) (hk_mem (n + 1)) v‖ ≤
              η * ‖v‖ := by
        intro n v hv
        exact hunstable_leak (T (k n)) (Submission.Shadowing.forward_mem hs (hk_mem n))
          (k (n + 1)) (hk_mem (n + 1)) (hanchor_transition_close_unstable_leak n) v hv
      have hanchor_unstable_leak_local :
          ∀ n : ℕ, ∀ v : E d,
            v ∈ hs.unstable (T (Submission.Shadowing.localTubeAnchorSeq hxTube n)) →
              ‖Submission.Shadowing.stableProjection hs
                  (Submission.Shadowing.localTubeAnchorSeq hxTube (n + 1))
                  (Submission.Shadowing.localTubeAnchorSeq_mem hxTube (n + 1)) v‖ ≤
                η * ‖v‖ := by
        intro n v hv
        change ‖Submission.Shadowing.stableProjection hs (k (n + 1)) (hk_mem (n + 1)) v‖ ≤
          η * ‖v‖
        exact hanchor_unstable_leak n v hv
      have hanchor_offdiag_le :
          ∀ n : ℕ, ∀ vs vu : E d,
            vs ∈ hs.stable (Submission.Shadowing.localTubeAnchorSeq hxTube n) →
              vu ∈ hs.unstable (Submission.Shadowing.localTubeAnchorSeq hxTube n) →
              ‖Submission.Shadowing.anchorUnstableProjection hs hxTube (n + 1)
                  (Submission.Shadowing.anchorDerivative (T := T) hxTube n vs)‖ ≤
                    η * ‖Submission.Shadowing.anchorDerivative (T := T) hxTube n vs‖ ∧
                ‖Submission.Shadowing.anchorStableProjection hs hxTube (n + 1)
                  (Submission.Shadowing.anchorDerivative (T := T) hxTube n vu)‖ ≤
                    η * ‖Submission.Shadowing.anchorDerivative (T := T) hxTube n vu‖ := by
        intro n vs vu hvs hvu
        exact Submission.Shadowing.anchorDerivative_offDiagonal_le (T := T) (K := K) hs
          hxTube hanchor_stable_leak_local hanchor_unstable_leak_local hvs hvu
      have hanchor_diagonal_step_le :
          ∀ n : ℕ, ∀ vs vu : E d,
            vs ∈ hs.stable (Submission.Shadowing.localTubeAnchorSeq hxTube n) →
              vu ∈ hs.unstable (Submission.Shadowing.localTubeAnchorSeq hxTube n) →
              ‖Submission.Shadowing.anchorStableProjection hs hxTube (n + 1)
                  (Submission.Shadowing.anchorDerivative (T := T) hxTube n vs)‖ ≤
                    (1 + η) * derivativeBound * ‖vs‖ ∧
                ‖Submission.Shadowing.anchorUnstableProjection hs hxTube (n + 1)
                  (Submission.Shadowing.anchorDerivative (T := T) hxTube n vu)‖ ≤
                    (1 + η) * derivativeBound * ‖vu‖ := by
        intro n vs vu hvs hvu
        exact Submission.Shadowing.anchorDerivative_projected_diagonal_norm_le
          (T := T) (K := K) hs hxTube hη_pos.le hA_bound hanchor_offdiag_le hvs hvu
      have hselected_block_inputs :
          Submission.Shadowing.SelectedAnchorBlockSolverInputs (T := T) (K := K) hs
            (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
            hxTube blockN := by
        exact Submission.Shadowing.selectedAnchorBlockSolverInputs_of_estimates
          (T := T) (K := K) hs hxTube hη_pos hr_pos hM_pos hgreen_pos hblock_pos
          hblock_contract hanchor_offdiag_le hforcing_projection_le hBlockFwdDeriv_r
          hBlockBwdDeriv_r
      have hselected_strict_block_estimates :
          Submission.Shadowing.SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
            (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
            (blockQ := blockQ) (derivativeBound := derivativeBound) hxTube blockN := by
        refine Submission.Shadowing.selectedAnchorStrictBlockEstimates_of_endpoint_bounds
          (T := T) (K := K) hs hxTube hselected_block_inputs hblockQ_nonneg hblockQ_lt_one
          hderivativeBound_spec.1 ?_ ?_ hselected_fwd_product_bound
          hselected_bwd_product_bound_finite
        · intro n vs hvs
          have hvs' : vs ∈ hs.stable (k n) := by
            simpa [k] using hvs
          simpa [k] using hselected_fwd_endpoint_strict_le n vs hvs'
        · intro n vu hvu
          have hvu' : vu ∈ hs.unstable (k (n + blockN)) := by
            simpa [k] using hvu
          simpa [k] using hselected_bwd_endpoint_strict_le n vu hvu'
      have hselected_block_remainder_estimates :
          Submission.Shadowing.SelectedAnchorBlockRemainderEstimates (T := T) (K := K) hs
            (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
            (blockQ := blockQ) (derivativeBound := derivativeBound) hxTube blockN := by
        exact Submission.Shadowing.selectedAnchorBlockRemainderEstimates_of_strict
          (T := T) (K := K) hs hxTube hselected_strict_block_estimates
      let solver : Submission.Shadowing.AnchorLinearSolver (T := T) (K := K) hxTube
          solverBound :=
        Submission.Shadowing.anchorLinearSolver_of_strictBlock hs
          hselected_strict_block_estimates hA_bound
      exact hsolver_to_shadow solver
    exact Submission.Shadowing.hasShadowing_of_nonemptyAnalyticEstimates hEstimates

end Submission
