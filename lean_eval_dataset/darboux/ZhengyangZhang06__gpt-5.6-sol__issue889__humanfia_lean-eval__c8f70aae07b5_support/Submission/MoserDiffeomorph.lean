import Submission.MoserSmoothFlow

open Set Function Metric Filter
open scoped ContDiff NNReal Topology

namespace Submission.MoserDiffeomorph

noncomputable section

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

def reverseField (f : ℝ → V → V) (t : ℝ) (z : V) : V :=
  -f (1 - t) z

omit [FiniteDimensional ℝ V] in
theorem reverseField_contDiff (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (uncurry f)) :
    ContDiff ℝ ∞ (uncurry (reverseField f)) := by
  unfold reverseField
  exact (hf.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)).neg

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem reverseField_norm_le (f : ℝ → V → V) (L : ℝ≥0)
    (hbound : ∀ t z, ‖f t z‖ ≤ L) :
    ∀ t z, ‖reverseField f t z‖ ≤ L := by
  intro t z
  simpa [reverseField] using hbound (1 - t) z

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem reverseField_lipschitz (f : ℝ → V → V) (K : ℝ≥0)
    (hlip : ∀ t, LipschitzWith K (f t)) :
    ∀ t, LipschitzWith K (reverseField f t) := by
  intro t
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [reverseField] using (hlip (1 - t)).dist_le_mul x y

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
@[simp]
theorem reverseField_reverse (f : ℝ → V → V) : reverseField (reverseField f) = f := by
  funext t z
  simp [reverseField]

section

variable (f : ℝ → V → V) (hf : ContDiff ℝ ∞ (uncurry f))
  (L K : ℝ≥0) (hbound : ∀ t z, ‖f t z‖ ≤ L)
  (hlip : ∀ t, LipschitzWith K (f t))

include f hf L K hbound hlip

def forwardMap : V → V :=
  Submission.MoserSmoothFlow.unitTimeOneMap f hf L K hbound hlip

def backwardMap : V → V :=
  Submission.MoserSmoothFlow.unitTimeOneMap (reverseField f)
    (reverseField_contDiff f hf) L K
    (reverseField_norm_le f L hbound) (reverseField_lipschitz f K hlip)

theorem backward_forward (x : V) :
    backwardMap f hf L K hbound hlip (forwardMap f hf L K hbound hlip x) = x := by
  let flow := Submission.MoserGlobal.unitFlow f hf L K hbound hlip
  let rf := reverseField f
  let hrf := reverseField_contDiff f hf
  let hrbound := reverseField_norm_le f L hbound
  let hrlip := reverseField_lipschitz f K hlip
  let rflow := Submission.MoserGlobal.unitFlow rf hrf L K hrbound hrlip
  let reversedPath : ℝ → V := fun s =>
    flow (projIcc (0 : ℝ) 1 zero_le_one (1 - s)) x
  let reverseSolution : ℝ → V := fun s =>
    rflow (projIcc (0 : ℝ) 1 zero_le_one s) (forwardMap f hf L K hbound hlip x)
  have hreversedCont : ContinuousOn reversedPath (Icc (0 : ℝ) 1) := by
    exact ((Submission.MoserGlobal.unitFlow_continuous f hf L K hbound hlip x).comp
      (continuous_projIcc.comp (continuous_const.sub continuous_id))).continuousOn
  have hreverseCont : ContinuousOn reverseSolution (Icc (0 : ℝ) 1) := by
    exact ((Submission.MoserGlobal.unitFlow_continuous rf hrf L K hrbound hrlip
      (forwardMap f hf L K hbound hlip x)).comp continuous_projIcc).continuousOn
  have hreversedDeriv : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt reversedPath (rf s (reversedPath s)) (Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
    have hqIcc : 1 - s ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2]
    have hbase := Submission.MoserGlobal.unitFlow_hasDerivWithinAt
      f hf L K hbound hlip x ⟨1 - s, hqIcc⟩
    have hq : HasDerivWithinAt (fun u : ℝ => 1 - u) (-1)
        (Icc (0 : ℝ) 1) s :=
      by
        have h : HasDerivWithinAt ((fun _ : ℝ => 1) - id) (0 - 1)
            (Icc (0 : ℝ) 1) s :=
          ((hasDerivAt_const (x := s) (1 : ℝ)).sub
            (hasDerivAt_id s)).hasDerivWithinAt
        change HasDerivWithinAt (fun u : ℝ => 1 - u) (0 - 1)
          (Icc (0 : ℝ) 1) s at h
        simpa using h
    have hmaps : MapsTo (fun u : ℝ => 1 - u) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2]
    have hcomp := HasFDerivWithinAt.comp_hasDerivWithinAt s
      hbase.hasFDerivWithinAt hq hmaps
    have hright := hcomp.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
    have hright' : HasDerivWithinAt
        (fun u : ℝ => Submission.MoserGlobal.unitFlow f hf L K hbound hlip
          (projIcc (0 : ℝ) 1 zero_le_one (1 - u)) x)
        (-f (1 - s) (Submission.MoserGlobal.unitFlow f hf L K hbound hlip
          ⟨1 - s, hqIcc⟩ x)) (Ici s) s := by
      convert hright using 1
      · funext u
        rfl
      · simp only [ContinuousLinearMap.toSpanSingleton_apply, neg_one_smul]
    dsimp [reversedPath, rf, flow]
    simpa only [reverseField, projIcc_of_mem zero_le_one hqIcc] using hright'
  have hreverseDeriv : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt reverseSolution (rf s (reverseSolution s)) (Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
    have hd := Submission.MoserGlobal.unitFlow_hasDerivWithinAt
      rf hrf L K hrbound hrlip (forwardMap f hf L K hbound hlip x) ⟨s, hsIcc⟩
    have hright := hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
    simpa only [reverseSolution, projIcc_of_mem zero_le_one hsIcc] using hright
  have hstart : reverseSolution 0 = reversedPath 0 := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    calc
      reverseSolution 0 = forwardMap f hf L K hbound hlip x := by
        dsimp [reverseSolution]
        rw [projIcc_of_mem zero_le_one h0]
        exact Submission.MoserGlobal.unitFlow_zero_time rf hrf L K hrbound hrlip _
      _ = reversedPath 0 := by
        dsimp [reversedPath, forwardMap, Submission.MoserSmoothFlow.unitTimeOneMap,
          Submission.MoserSmoothFlow.unitEndTime]
        rw [show (1 : ℝ) - 0 = 1 by ring, projIcc_of_mem zero_le_one h1]
        change flow Submission.MoserSmoothFlow.unitEndTime x = flow ⟨1, h1⟩ x
        congr 1
  have heq := ODE_solution_unique (reverseField_lipschitz f K hlip)
    hreverseCont hreverseDeriv hreversedCont hreversedDeriv hstart
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hend := heq h1mem
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  calc
    backwardMap f hf L K hbound hlip (forwardMap f hf L K hbound hlip x) =
        reverseSolution 1 := by
      dsimp [backwardMap, reverseSolution, Submission.MoserSmoothFlow.unitTimeOneMap,
        Submission.MoserSmoothFlow.unitEndTime]
      rw [projIcc_of_mem zero_le_one h1mem]
      change rflow Submission.MoserSmoothFlow.unitEndTime
          (forwardMap f hf L K hbound hlip x) =
        rflow ⟨1, h1mem⟩ (forwardMap f hf L K hbound hlip x)
      congr 1
    _ = reversedPath 1 := hend
    _ = x := by
      dsimp [reversedPath]
      rw [show (1 : ℝ) - 1 = 0 by ring, projIcc_of_mem zero_le_one h0mem]
      exact Submission.MoserGlobal.unitFlow_zero_time f hf L K hbound hlip x

theorem forward_backward (x : V) :
    forwardMap f hf L K hbound hlip (backwardMap f hf L K hbound hlip x) = x := by
  let rf := reverseField f
  let hrf := reverseField_contDiff f hf
  let hrbound := reverseField_norm_le f L hbound
  let hrlip := reverseField_lipschitz f K hlip
  have h := backward_forward rf hrf L K hrbound hrlip x
  simpa only [forwardMap, backwardMap, rf, hrf, hrbound, hrlip,
    reverseField_reverse] using h

def timeOneHomeomorph : V ≃ₜ V where
  toFun := forwardMap f hf L K hbound hlip
  invFun := backwardMap f hf L K hbound hlip
  left_inv := backward_forward f hf L K hbound hlip
  right_inv := forward_backward f hf L K hbound hlip
  continuous_toFun :=
    (Submission.MoserSmoothFlow.unitTimeOneMap_contDiff f hf L K hbound hlip).continuous
  continuous_invFun :=
    (Submission.MoserSmoothFlow.unitTimeOneMap_contDiff (reverseField f)
      (reverseField_contDiff f hf) L K (reverseField_norm_le f L hbound)
      (reverseField_lipschitz f K hlip)).continuous

end

end

end Submission.MoserDiffeomorph
