import Submission.BridgeStraight

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Filter
open scoped Real
open scoped Topology
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def mateContractionFactor (k s : ℝ) : ℝ :=
  k * isotopyWeight s

theorem mateContractionFactor_nonneg {k : ℝ} (hk0 : 0 ≤ k) (s : ℝ) :
    0 ≤ mateContractionFactor k s :=
  mul_nonneg hk0 (isotopyWeight_nonneg s)

theorem mateContractionFactor_lt_one {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (s : ℝ) : mateContractionFactor k s < 1 := by
  have hw := isotopyWeight_le_one s
  have hle : mateContractionFactor k s ≤ k := by
    unfold mateContractionFactor
    nlinarith [isotopyWeight_nonneg s]
  exact hle.trans_lt hk1

@[simp] theorem mateContractionFactor_zero (k : ℝ) :
    mateContractionFactor k 0 = k := by
  simp [mateContractionFactor]

@[simp] theorem mateContractionFactor_one (k : ℝ) :
    mateContractionFactor k 1 = 0 := by
  simp [mateContractionFactor]

theorem contDiff_mateContractionFactor (k : ℝ) :
    ContDiff ℝ ⊤ (mateContractionFactor k) := by
  exact contDiff_const.mul contDiff_isotopyWeight

noncomputable def contractMateDirectionIsotopyMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (k t s : ℝ) : Space :=
  contractedBridgeCurveMinMax hknot u hdata (mateContractionFactor k s) t

@[simp] theorem contractMateDirectionIsotopyMinMax_zero {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (k t : ℝ) :
    contractMateDirectionIsotopyMinMax hknot u hdata k t 0 =
      contractedBridgeCurveMinMax hknot u hdata k t := by
  simp [contractMateDirectionIsotopyMinMax]

@[simp] theorem contractMateDirectionIsotopyMinMax_one {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b : ℝ}
    (hdata : MinMaxBridgeData r u a b) (k t : ℝ) :
    contractMateDirectionIsotopyMinMax hknot u hdata k t 1 =
      contractedBridgeCurveMinMax hknot u hdata 0 t := by
  simp [contractMateDirectionIsotopyMinMax]

theorem contDiff_contractMateDirectionIsotopyMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) (u : Space) {a b k : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      contractMateDirectionIsotopyMinMax hknot u hdata k p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let κ : ℝ × ℝ → ℝ := fun z => mateContractionFactor k z.2
  let h : ℝ × ℝ → ℝ := fun z => height r u z.1
  let x : ℝ × ℝ → ℝ := fun z =>
    bridgeHeightContraction (height r u a) (height r u b) (κ z) (h z)
  have hκ : ContDiff ℝ ⊤ κ :=
    (contDiff_mateContractionFactor k).comp contDiff_snd
  have hh : ContDiff ℝ ⊤ h := (contDiff_height hknot u).comp contDiff_fst
  have hxcont : ContDiff ℝ ⊤ x := by
    unfold x bridgeHeightContraction bridgeHeightMidpoint
    fun_prop
  have hpheight : h p ∈ Icc (height r u a) (height r u b) :=
    height_mem_Icc_minMax hknot u hdata
  have hκ0 : 0 ≤ κ p := mateContractionFactor_nonneg hk0 p.2
  have hκ1 : κ p < 1 := mateContractionFactor_lt_one hk0 hk1 p.2
  have hxmem : x p ∈ Ioo (height r u a) (height r u b) :=
    bridgeHeightContraction_mem_Ioo hdata.height_endpoints_lt hκ0 hκ1 hpheight
  have hd : ContDiffAt ℝ ⊤
      (fun z : ℝ × ℝ => centralMateDirectionMinMax hknot u hdata (x z)) p :=
    (contDiffAt_centralMateDirectionMinMax hknot u hdata hxmem).comp p
      hxcont.contDiffAt
  have huconst : ContDiffAt ℝ ⊤ (fun _ : ℝ × ℝ => u) p := contDiffAt_const
  change ContDiffAt ℝ ⊤ (fun z : ℝ × ℝ =>
    h z • u + directionalUnitTangent r u z.1 •
      centralMateDirectionMinMax hknot u hdata (x z)) p
  exact (hh.contDiffAt.smul huconst).add
    (((contDiff_directionalUnitTangent hknot u).comp contDiff_fst).contDiffAt.smul hd)

theorem isSmoothKnot_contractMateDirectionIsotopyMinMax {r : ℝ → Space}
    (hknot : IsSmoothKnot r) {u : Space} (hu : ‖u‖ = 1) {a b k s : ℝ}
    (hdata : MinMaxBridgeData r u a b) (hk0 : 0 ≤ k) (hk1 : k < 1) :
    IsSmoothKnot
      (fun t => contractMateDirectionIsotopyMinMax hknot u hdata k t s) := by
  exact isSmoothKnot_contractedBridgeCurveMinMax hknot hu hdata
    (mateContractionFactor_nonneg hk0 s)
    (mateContractionFactor_lt_one hk0 hk1 s)

end Submission.Helpers
