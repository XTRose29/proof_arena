import Submission.Green

open LeanEval.Dynamics.HyperbolicShadowingProblem
open scoped Topology NNReal

namespace Submission.Shadowing

noncomputable section

set_option maxHeartbeats 1000000

variable {d : ℕ} {T : E d ≃ₜ E d} {K : Set (E d)}

abbrev BlockStableFiber (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (N j : ℕ) :=
  hs.stable (localTubeAnchorSeq hx (j * N))

abbrev BlockUnstableFiber (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (N j : ℕ) :=
  hs.unstable (localTubeAnchorSeq hx (j * N))

theorem anchorProjection_vector_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound blockQ derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := blockQ) (derivativeBound := derivativeBound) hx N)
    (n : ℕ) (v : E d) :
    ‖anchorStableProjection hs hx n v‖ ≤ M * ‖v‖ ∧
      ‖anchorUnstableProjection hs hx n v‖ ≤ M * ‖v‖ := by
  let c : CorrectionSeq d := BoundedContinuousFunction.const ℕ v
  have hc := strict.inputs.forcing_projection_le c n
  simpa [c] using hc

def linearForcingAdvance {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d)
    (n : ℕ) : ℕ → E d
  | 0 => 0
  | m + 1 => anchorDerivative (T := T) hx (n + m)
      (linearForcingAdvance hx b n m) + b (n + m)

@[simp]
theorem linearForcingAdvance_zero {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d) (n : ℕ) :
    linearForcingAdvance (T := T) hx b n 0 = 0 :=
  rfl

@[simp]
theorem linearForcingAdvance_succ {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d) (n m : ℕ) :
    linearForcingAdvance (T := T) hx b n (m + 1) =
      anchorDerivative (T := T) hx (n + m)
        (linearForcingAdvance (T := T) hx b n m) + b (n + m) :=
  rfl

theorem linearForcingAdvance_norm_le {ρ D : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d)
    (hD_nonneg : 0 ≤ D) (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ D) :
    ∀ n m : ℕ,
      ‖linearForcingAdvance (T := T) hx b n m‖ ≤
        finiteTrackingAmplification D m * ‖b‖ := by
  intro n m
  induction m with
  | zero => simp [finiteTrackingAmplification]
  | succ m ih =>
      have hlin :
          ‖anchorDerivative (T := T) hx (n + m)
              (linearForcingAdvance (T := T) hx b n m)‖ ≤
            D * ‖linearForcingAdvance (T := T) hx b n m‖ := by
        exact ((anchorDerivative (T := T) hx (n + m)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hA (n + m)) (norm_nonneg _))
      have hb : ‖b (n + m)‖ ≤ ‖b‖ := correctionSeq_apply_norm_le_norm b (n + m)
      calc
        ‖linearForcingAdvance (T := T) hx b n (m + 1)‖ ≤
            ‖anchorDerivative (T := T) hx (n + m)
                (linearForcingAdvance (T := T) hx b n m)‖ + ‖b (n + m)‖ :=
          norm_add_le _ _
        _ ≤ D * ‖linearForcingAdvance (T := T) hx b n m‖ + ‖b‖ :=
          add_le_add hlin hb
        _ ≤ D * (finiteTrackingAmplification D m * ‖b‖) + ‖b‖ :=
          add_le_add (mul_le_mul_of_nonneg_left ih hD_nonneg) le_rfl
        _ = finiteTrackingAmplification D (m + 1) * ‖b‖ := by
          simp [finiteTrackingAmplification]
          ring

theorem linearForcingAdvance_sub {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b c : CorrectionSeq d) (n : ℕ) :
    ∀ m : ℕ,
      linearForcingAdvance (T := T) hx b n m -
          linearForcingAdvance (T := T) hx c n m =
        linearForcingAdvance (T := T) hx (b - c) n m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [linearForcingAdvance_succ]
      rw [← ih, map_sub]
      simp
      abel

noncomputable def blockForcingSeq {ρ D : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d)
    (N : ℕ) (hD_nonneg : 0 ≤ D)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ D) : CorrectionSeq d :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun j : ℕ => linearForcingAdvance (T := T) hx b (j * N) N)
    (finiteTrackingAmplification D N * ‖b‖)
    (fun j => linearForcingAdvance_norm_le (T := T) hx b hD_nonneg hA (j * N) N)

@[simp]
theorem blockForcingSeq_apply {ρ D : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d)
    (N : ℕ) (hD_nonneg : 0 ≤ D)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ D) (j : ℕ) :
    blockForcingSeq (T := T) hx b N hD_nonneg hA j =
      linearForcingAdvance (T := T) hx b (j * N) N :=
  rfl

theorem blockForcingSeq_norm_le {ρ D : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d)
    (N : ℕ) (hD_nonneg : 0 ≤ D)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ D) :
    ‖blockForcingSeq (T := T) hx b N hD_nonneg hA‖ ≤
      finiteTrackingAmplification D N * ‖b‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  change ‖linearForcingAdvance (T := T) hx b (j * N) N‖ ≤ _
  exact linearForcingAdvance_norm_le (T := T) hx b hD_nonneg hA (j * N) N

theorem blockForcingSeq_sub_norm_le {ρ D : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b c : CorrectionSeq d)
    (N : ℕ) (hD_nonneg : 0 ≤ D)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ D) :
    ‖blockForcingSeq (T := T) hx b N hD_nonneg hA -
        blockForcingSeq (T := T) hx c N hD_nonneg hA‖ ≤
      finiteTrackingAmplification D N * ‖b - c‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  change
    ‖linearForcingAdvance (T := T) hx b (j * N) N -
        linearForcingAdvance (T := T) hx c (j * N) N‖ ≤ _
  rw [linearForcingAdvance_sub]
  exact linearForcingAdvance_norm_le (T := T) hx (b - c) hD_nonneg hA (j * N) N

def unstableBlockMap (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (_strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (u : BlockUnstableFiber hs hx N j) :
    BlockUnstableFiber hs hx N (j + 1) :=
  ⟨anchorUnstableProjection hs hx ((j + 1) * N)
      (anchorDerivativeProduct (T := T) hx (j * N) N (u : E d)),
    anchorUnstableProjection_mem hs hx _ _⟩

def unstableApproxInverse (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (_strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (v : BlockUnstableFiber hs hx N (j + 1)) :
    BlockUnstableFiber hs hx N j :=
  ⟨anchorUnstableProjection hs hx (j * N)
      (anchorInverseDerivativeProduct (T := T) hx (j * N) N (v : E d)),
    anchorUnstableProjection_mem hs hx _ _⟩

def unstableRightDefect (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (v : BlockUnstableFiber hs hx N (j + 1)) :
    BlockUnstableFiber hs hx N (j + 1) :=
  v - unstableBlockMap hs strict j (unstableApproxInverse hs strict j v)

theorem unstableRightDefect_coe (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (v : BlockUnstableFiber hs hx N (j + 1)) :
    (unstableRightDefect hs strict j v : E d) =
      anchorUnstableProjection hs hx ((j + 1) * N)
        (anchorDerivativeProduct (T := T) hx (j * N) N
          (anchorStableProjection hs hx (j * N)
            (anchorInverseDerivativeProduct (T := T) hx (j * N) N (v : E d)))) := by
  let w : E d :=
    anchorInverseDerivativeProduct (T := T) hx (j * N) N (v : E d)
  let ps : E d := anchorStableProjection hs hx (j * N) w
  let pu : E d := anchorUnstableProjection hs hx (j * N) w
  have hdecomp : ps + pu = w := by
    exact anchorProjection_decomp (T := T) (K := K) hs hx (j * N) w
  have hAw : anchorDerivativeProduct (T := T) hx (j * N) N w = (v : E d) := by
    dsimp [w]
    exact anchorDerivativeProduct_apply_anchorInverseDerivativeProduct
      (T := T) (K := K) hs hx (j * N) N (v : E d)
  have hvproj : anchorUnstableProjection hs hx ((j + 1) * N) (v : E d) = v := by
    exact unstableProjection_apply_of_mem_unstable hs
      (localTubeAnchorSeq_mem hx ((j + 1) * N)) v.property
  change (v : E d) - anchorUnstableProjection hs hx ((j + 1) * N)
      (anchorDerivativeProduct (T := T) hx (j * N) N pu) =
    anchorUnstableProjection hs hx ((j + 1) * N)
      (anchorDerivativeProduct (T := T) hx (j * N) N ps)
  have hAdecomp :
      anchorDerivativeProduct (T := T) hx (j * N) N ps +
          anchorDerivativeProduct (T := T) hx (j * N) N pu = (v : E d) := by
    rw [← map_add, hdecomp, hAw]
  rw [← hvproj, ← hAdecomp, map_add]
  abel

theorem unstableRightDefect_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (v : BlockUnstableFiber hs hx N (j + 1)) :
    ‖unstableRightDefect hs strict j v‖ ≤ (1 / 256 : ℝ) * ‖v‖ := by
  let w : E d :=
    anchorInverseDerivativeProduct (T := T) hx (j * N) N (v : E d)
  let ps : E d := anchorStableProjection hs hx (j * N) w
  have hv_endpoint :
      (v : E d) ∈ hs.unstable (localTubeAnchorSeq hx (j * N + N)) := by
    rw [← show (j + 1) * N = j * N + N by simp [Nat.add_mul]]
    exact v.property
  have hback := (strict.backward_endpoint_le (j * N) (v : E d) hv_endpoint).1
  have hps : ‖ps‖ ≤ (1 / 16 : ℝ) * ‖v‖ := by
    simpa [ps, w, Nat.add_mul] using hback
  have hps_mem : ps ∈ hs.stable (localTubeAnchorSeq hx (j * N)) :=
    anchorStableProjection_mem hs hx _ _
  have hfwd := (strict.forward_endpoint_le (j * N) ps hps_mem).2
  have hfwd' :
      ‖anchorUnstableProjection hs hx ((j + 1) * N)
          (anchorDerivativeProduct (T := T) hx (j * N) N ps)‖ ≤
        (1 / 16 : ℝ) * ‖ps‖ := by
    simpa [Nat.add_mul] using hfwd
  change ‖(unstableRightDefect hs strict j v : E d)‖ ≤ (1 / 256 : ℝ) * ‖(v : E d)‖
  rw [unstableRightDefect_coe]
  exact hfwd'.trans (by
    calc
      (1 / 16 : ℝ) * ‖ps‖ ≤ (1 / 16 : ℝ) * ((1 / 16 : ℝ) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hps (by norm_num)
      _ = (1 / 256 : ℝ) * ‖v‖ := by ring)

theorem unstableRightDefect_sub (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (v w : BlockUnstableFiber hs hx N (j + 1)) :
    unstableRightDefect hs strict j v - unstableRightDefect hs strict j w =
      unstableRightDefect hs strict j (v - w) := by
  apply Subtype.ext
  simp [unstableRightDefect, unstableBlockMap, unstableApproxInverse, map_sub]
  abel

theorem unstableRightDefect_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (v w : BlockUnstableFiber hs hx N (j + 1)) :
    ‖unstableRightDefect hs strict j v - unstableRightDefect hs strict j w‖ ≤
      (1 / 256 : ℝ) * ‖v - w‖ := by
  rw [unstableRightDefect_sub]
  exact unstableRightDefect_norm_le hs strict j (v - w)

def unstableInverseIteration (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target z : BlockUnstableFiber hs hx N (j + 1)) :
    BlockUnstableFiber hs hx N (j + 1) :=
  target + unstableRightDefect hs strict j z

theorem unstableInverseIteration_contracting (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target : BlockUnstableFiber hs hx N (j + 1)) :
    ContractingWith (1 / 128 : NNReal) (unstableInverseIteration hs strict j target) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro v w
  change
    dist (unstableInverseIteration hs strict j target v)
        (unstableInverseIteration hs strict j target w) ≤
      (1 / 128 : ℝ) * dist v w
  simp only [dist_eq_norm]
  have hdefect := unstableRightDefect_sub_norm_le hs strict j v w
  have heq :
      unstableInverseIteration hs strict j target v -
          unstableInverseIteration hs strict j target w =
        unstableRightDefect hs strict j v - unstableRightDefect hs strict j w := by
    apply Subtype.ext
    simp [unstableInverseIteration]
  rw [heq]
  exact hdefect.trans (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))

noncomputable def unstableBlockRightInverse (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target : BlockUnstableFiber hs hx N (j + 1)) :
    BlockUnstableFiber hs hx N j :=
  unstableApproxInverse hs strict j
    (ContractingWith.fixedPoint (unstableInverseIteration hs strict j target)
      (unstableInverseIteration_contracting hs strict j target))

theorem unstableBlockRightInverse_right (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target : BlockUnstableFiber hs hx N (j + 1)) :
    unstableBlockMap hs strict j (unstableBlockRightInverse hs strict j target) = target := by
  let z : BlockUnstableFiber hs hx N (j + 1) :=
    ContractingWith.fixedPoint (unstableInverseIteration hs strict j target)
      (unstableInverseIteration_contracting hs strict j target)
  have hfixed : unstableInverseIteration hs strict j target z = z :=
    (unstableInverseIteration_contracting hs strict j target).fixedPoint_isFixedPt
  change unstableBlockMap hs strict j (unstableApproxInverse hs strict j z) = target
  apply Subtype.ext
  have hfixed' :
      (target : E d) + (unstableRightDefect hs strict j z : E d) = (z : E d) :=
    congrArg Subtype.val hfixed
  have hrecover :
      (unstableBlockMap hs strict j (unstableApproxInverse hs strict j z) : E d) =
        (z : E d) - (unstableRightDefect hs strict j z : E d) := by
    change
      (unstableBlockMap hs strict j (unstableApproxInverse hs strict j z) : E d) =
        (z : E d) -
          ((z : E d) -
            (unstableBlockMap hs strict j (unstableApproxInverse hs strict j z) : E d))
    abel
  rw [hrecover, ← hfixed']
  abel

theorem unstableFixedPoint_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target : BlockUnstableFiber hs hx N (j + 1)) :
    ‖ContractingWith.fixedPoint (unstableInverseIteration hs strict j target)
        (unstableInverseIteration_contracting hs strict j target)‖ ≤ 2 * ‖target‖ := by
  let z : BlockUnstableFiber hs hx N (j + 1) :=
    ContractingWith.fixedPoint (unstableInverseIteration hs strict j target)
      (unstableInverseIteration_contracting hs strict j target)
  have hfixed : unstableInverseIteration hs strict j target z = z :=
    (unstableInverseIteration_contracting hs strict j target).fixedPoint_isFixedPt
  have hsum : ‖z‖ ≤ ‖target‖ + ‖unstableRightDefect hs strict j z‖ := by
    calc
      ‖z‖ = ‖unstableInverseIteration hs strict j target z‖ :=
        congrArg norm hfixed.symm
      _ = ‖target + unstableRightDefect hs strict j z‖ := rfl
      _ ≤ ‖target‖ + ‖unstableRightDefect hs strict j z‖ := norm_add_le _ _
  have hdefect := unstableRightDefect_norm_le hs strict j z
  change ‖z‖ ≤ 2 * ‖target‖
  nlinarith only [hsum, hdefect, norm_nonneg z, norm_nonneg target]

theorem unstableBlockRightInverse_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target : BlockUnstableFiber hs hx N (j + 1)) :
    ‖unstableBlockRightInverse hs strict j target‖ ≤ (1 / 8 : ℝ) * ‖target‖ := by
  let z : BlockUnstableFiber hs hx N (j + 1) :=
    ContractingWith.fixedPoint (unstableInverseIteration hs strict j target)
      (unstableInverseIteration_contracting hs strict j target)
  have hz : ‖z‖ ≤ 2 * ‖target‖ := unstableFixedPoint_norm_le hs strict j target
  have hz_endpoint :
      (z : E d) ∈ hs.unstable (localTubeAnchorSeq hx (j * N + N)) := by
    rw [← show (j + 1) * N = j * N + N by simp [Nat.add_mul]]
    exact z.property
  have hback := (strict.backward_endpoint_le (j * N) (z : E d) hz_endpoint).2
  change ‖anchorUnstableProjection hs hx (j * N)
      (anchorInverseDerivativeProduct (T := T) hx (j * N) N (z : E d))‖ ≤
    (1 / 8 : ℝ) * ‖target‖
  exact hback.trans (by
    calc
      (1 / 16 : ℝ) * ‖z‖ ≤ (1 / 16 : ℝ) * (2 * ‖target‖) :=
        mul_le_mul_of_nonneg_left hz (by norm_num)
      _ = (1 / 8 : ℝ) * ‖target‖ := by ring)

theorem unstableFixedPoint_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target₁ target₂ : BlockUnstableFiber hs hx N (j + 1)) :
    ‖ContractingWith.fixedPoint (unstableInverseIteration hs strict j target₁)
          (unstableInverseIteration_contracting hs strict j target₁) -
        ContractingWith.fixedPoint (unstableInverseIteration hs strict j target₂)
          (unstableInverseIteration_contracting hs strict j target₂)‖ ≤
      2 * ‖target₁ - target₂‖ := by
  let z₁ : BlockUnstableFiber hs hx N (j + 1) :=
    ContractingWith.fixedPoint (unstableInverseIteration hs strict j target₁)
      (unstableInverseIteration_contracting hs strict j target₁)
  let z₂ : BlockUnstableFiber hs hx N (j + 1) :=
    ContractingWith.fixedPoint (unstableInverseIteration hs strict j target₂)
      (unstableInverseIteration_contracting hs strict j target₂)
  have hfixed₁ : unstableInverseIteration hs strict j target₁ z₁ = z₁ :=
    (unstableInverseIteration_contracting hs strict j target₁).fixedPoint_isFixedPt
  have hfixed₂ : unstableInverseIteration hs strict j target₂ z₂ = z₂ :=
    (unstableInverseIteration_contracting hs strict j target₂).fixedPoint_isFixedPt
  have hdecomp :
      z₁ - z₂ =
        (target₁ - target₂) +
          (unstableRightDefect hs strict j z₁ - unstableRightDefect hs strict j z₂) := by
    apply Subtype.ext
    have hfixed₁' := congrArg Subtype.val hfixed₁
    have hfixed₂' := congrArg Subtype.val hfixed₂
    simp only [unstableInverseIteration] at hfixed₁' hfixed₂'
    change (z₁ : E d) - (z₂ : E d) =
      ((target₁ : E d) - (target₂ : E d)) +
        ((unstableRightDefect hs strict j z₁ : E d) -
          (unstableRightDefect hs strict j z₂ : E d))
    rw [← hfixed₁', ← hfixed₂']
    simp
    abel
  have hsum :
      ‖z₁ - z₂‖ ≤ ‖target₁ - target₂‖ +
        ‖unstableRightDefect hs strict j z₁ - unstableRightDefect hs strict j z₂‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  have hdefect := unstableRightDefect_sub_norm_le hs strict j z₁ z₂
  change ‖z₁ - z₂‖ ≤ 2 * ‖target₁ - target₂‖
  nlinarith only [hsum, hdefect, norm_nonneg (z₁ - z₂), norm_nonneg (target₁ - target₂)]

theorem unstableBlockRightInverse_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target₁ target₂ : BlockUnstableFiber hs hx N (j + 1)) :
    ‖unstableBlockRightInverse hs strict j target₁ -
        unstableBlockRightInverse hs strict j target₂‖ ≤
      (1 / 8 : ℝ) * ‖target₁ - target₂‖ := by
  let z₁ : BlockUnstableFiber hs hx N (j + 1) :=
    ContractingWith.fixedPoint (unstableInverseIteration hs strict j target₁)
      (unstableInverseIteration_contracting hs strict j target₁)
  let z₂ : BlockUnstableFiber hs hx N (j + 1) :=
    ContractingWith.fixedPoint (unstableInverseIteration hs strict j target₂)
      (unstableInverseIteration_contracting hs strict j target₂)
  have hz : ‖z₁ - z₂‖ ≤ 2 * ‖target₁ - target₂‖ :=
    unstableFixedPoint_sub_norm_le hs strict j target₁ target₂
  have hz_endpoint :
      ((z₁ : E d) - (z₂ : E d)) ∈
        hs.unstable (localTubeAnchorSeq hx (j * N + N)) := by
    rw [← show (j + 1) * N = j * N + N by simp [Nat.add_mul]]
    exact Submodule.sub_mem _ z₁.property z₂.property
  have hback := (strict.backward_endpoint_le (j * N)
    ((z₁ : E d) - (z₂ : E d)) hz_endpoint).2
  change
    ‖anchorUnstableProjection hs hx (j * N)
          (anchorInverseDerivativeProduct (T := T) hx (j * N) N (z₁ : E d)) -
        anchorUnstableProjection hs hx (j * N)
          (anchorInverseDerivativeProduct (T := T) hx (j * N) N (z₂ : E d))‖ ≤
      (1 / 8 : ℝ) * ‖target₁ - target₂‖
  rw [← map_sub, ← map_sub]
  exact hback.trans (by
    calc
      (1 / 16 : ℝ) * ‖(z₁ : E d) - (z₂ : E d)‖ ≤
          (1 / 16 : ℝ) * (2 * ‖target₁ - target₂‖) :=
        mul_le_mul_of_nonneg_left hz (by norm_num)
      _ = (1 / 8 : ℝ) * ‖target₁ - target₂‖ := by ring)

def unstableBlockCross (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target : BlockUnstableFiber hs hx N (j + 1)) :
    hs.stable (localTubeAnchorSeq hx ((j + 1) * N)) :=
  ⟨anchorStableProjection hs hx ((j + 1) * N)
      (anchorDerivativeProduct (T := T) hx (j * N) N
        (unstableBlockRightInverse hs strict j target : E d)),
    anchorStableProjection_mem hs hx _ _⟩

theorem unstableBlockCross_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target : BlockUnstableFiber hs hx N (j + 1)) :
    ‖unstableBlockCross hs strict j target‖ ≤ (1 / 128 : ℝ) * ‖target‖ := by
  let z : BlockUnstableFiber hs hx N (j + 1) :=
    ContractingWith.fixedPoint (unstableInverseIteration hs strict j target)
      (unstableInverseIteration_contracting hs strict j target)
  let w : E d := anchorInverseDerivativeProduct (T := T) hx (j * N) N (z : E d)
  let ps : E d := anchorStableProjection hs hx (j * N) w
  let pu : E d := anchorUnstableProjection hs hx (j * N) w
  have hz : ‖z‖ ≤ 2 * ‖target‖ := unstableFixedPoint_norm_le hs strict j target
  have hz_endpoint :
      (z : E d) ∈ hs.unstable (localTubeAnchorSeq hx (j * N + N)) := by
    rw [← show (j + 1) * N = j * N + N by simp [Nat.add_mul]]
    exact z.property
  have hback := (strict.backward_endpoint_le (j * N) (z : E d) hz_endpoint).1
  have hps : ‖ps‖ ≤ (1 / 16 : ℝ) * ‖z‖ := by
    simpa [ps, w] using hback
  have hps_mem : ps ∈ hs.stable (localTubeAnchorSeq hx (j * N)) :=
    anchorStableProjection_mem hs hx _ _
  have hfwd := (strict.forward_endpoint_le (j * N) ps hps_mem).1
  have hdecomp : ps + pu = w := anchorProjection_decomp (T := T) (K := K) hs hx _ w
  have hAw : anchorDerivativeProduct (T := T) hx (j * N) N w = (z : E d) :=
    anchorDerivativeProduct_apply_anchorInverseDerivativeProduct
      (T := T) (K := K) hs hx (j * N) N (z : E d)
  have hz_stable_zero : anchorStableProjection hs hx ((j + 1) * N) (z : E d) = 0 :=
    stableProjection_apply_of_mem_unstable hs
      (localTubeAnchorSeq_mem hx ((j + 1) * N)) z.property
  have hcross_eq :
      (unstableBlockCross hs strict j target : E d) =
        -anchorStableProjection hs hx ((j + 1) * N)
          (anchorDerivativeProduct (T := T) hx (j * N) N ps) := by
    change anchorStableProjection hs hx ((j + 1) * N)
        (anchorDerivativeProduct (T := T) hx (j * N) N pu) = _
    have hsum :
        anchorStableProjection hs hx ((j + 1) * N)
            (anchorDerivativeProduct (T := T) hx (j * N) N ps) +
          anchorStableProjection hs hx ((j + 1) * N)
            (anchorDerivativeProduct (T := T) hx (j * N) N pu) = 0 := by
      rw [← map_add, ← map_add, hdecomp, hAw, hz_stable_zero]
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hsum
  change ‖(unstableBlockCross hs strict j target : E d)‖ ≤
    (1 / 128 : ℝ) * ‖(target : E d)‖
  rw [hcross_eq, norm_neg]
  have hfwd' :
      ‖anchorStableProjection hs hx ((j + 1) * N)
          (anchorDerivativeProduct (T := T) hx (j * N) N ps)‖ ≤
        (1 / 16 : ℝ) * ‖ps‖ := by
    simpa [Nat.add_mul] using hfwd
  exact hfwd'.trans (by
    calc
      (1 / 16 : ℝ) * ‖ps‖ ≤ (1 / 16 : ℝ) * ((1 / 16 : ℝ) * ‖z‖) :=
        mul_le_mul_of_nonneg_left hps (by norm_num)
      _ ≤ (1 / 256 : ℝ) * (2 * ‖target‖) := by
        nlinarith only [hz]
      _ = (1 / 128 : ℝ) * ‖target‖ := by ring)

theorem unstableBlockCross_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (target₁ target₂ : BlockUnstableFiber hs hx N (j + 1)) :
    ‖unstableBlockCross hs strict j target₁ - unstableBlockCross hs strict j target₂‖ ≤
      (1 / 128 : ℝ) * ‖target₁ - target₂‖ := by
  let z₁ : BlockUnstableFiber hs hx N (j + 1) :=
    ContractingWith.fixedPoint (unstableInverseIteration hs strict j target₁)
      (unstableInverseIteration_contracting hs strict j target₁)
  let z₂ : BlockUnstableFiber hs hx N (j + 1) :=
    ContractingWith.fixedPoint (unstableInverseIteration hs strict j target₂)
      (unstableInverseIteration_contracting hs strict j target₂)
  let zd : E d := (z₁ : E d) - (z₂ : E d)
  let w : E d := anchorInverseDerivativeProduct (T := T) hx (j * N) N zd
  let ps : E d := anchorStableProjection hs hx (j * N) w
  let pu : E d := anchorUnstableProjection hs hx (j * N) w
  have hz : ‖z₁ - z₂‖ ≤ 2 * ‖target₁ - target₂‖ :=
    unstableFixedPoint_sub_norm_le hs strict j target₁ target₂
  have hzd_endpoint :
      zd ∈ hs.unstable (localTubeAnchorSeq hx (j * N + N)) := by
    dsimp [zd]
    rw [← show (j + 1) * N = j * N + N by simp [Nat.add_mul]]
    exact Submodule.sub_mem _ z₁.property z₂.property
  have hback := (strict.backward_endpoint_le (j * N) zd hzd_endpoint).1
  have hps : ‖ps‖ ≤ (1 / 16 : ℝ) * ‖zd‖ := by
    simpa [ps, w] using hback
  have hps_mem : ps ∈ hs.stable (localTubeAnchorSeq hx (j * N)) :=
    anchorStableProjection_mem hs hx _ _
  have hfwd := (strict.forward_endpoint_le (j * N) ps hps_mem).1
  have hdecomp : ps + pu = w := anchorProjection_decomp (T := T) (K := K) hs hx _ w
  have hAw : anchorDerivativeProduct (T := T) hx (j * N) N w = zd := by
    dsimp [w]
    exact anchorDerivativeProduct_apply_anchorInverseDerivativeProduct
      (T := T) (K := K) hs hx (j * N) N zd
  have hzd_stable_zero :
      anchorStableProjection hs hx ((j + 1) * N) zd = 0 := by
    dsimp [zd]
    rw [map_sub]
    have hz₁_zero : anchorStableProjection hs hx ((j + 1) * N) (z₁ : E d) = 0 := by
      change stableProjection hs (localTubeAnchorSeq hx ((j + 1) * N))
          (localTubeAnchorSeq_mem hx ((j + 1) * N)) (z₁ : E d) = 0
      exact stableProjection_apply_of_mem_unstable hs
        (localTubeAnchorSeq_mem hx ((j + 1) * N)) z₁.property
    have hz₂_zero : anchorStableProjection hs hx ((j + 1) * N) (z₂ : E d) = 0 := by
      change stableProjection hs (localTubeAnchorSeq hx ((j + 1) * N))
          (localTubeAnchorSeq_mem hx ((j + 1) * N)) (z₂ : E d) = 0
      exact stableProjection_apply_of_mem_unstable hs
        (localTubeAnchorSeq_mem hx ((j + 1) * N)) z₂.property
    rw [hz₁_zero, hz₂_zero]
    simp
  have hright_diff :
      (unstableBlockRightInverse hs strict j target₁ : E d) -
          (unstableBlockRightInverse hs strict j target₂ : E d) = pu := by
    change anchorUnstableProjection hs hx (j * N)
        (anchorInverseDerivativeProduct (T := T) hx (j * N) N (z₁ : E d)) -
      anchorUnstableProjection hs hx (j * N)
        (anchorInverseDerivativeProduct (T := T) hx (j * N) N (z₂ : E d)) = pu
    rw [← map_sub, ← map_sub]
  have hcross_eq :
      (unstableBlockCross hs strict j target₁ : E d) -
          (unstableBlockCross hs strict j target₂ : E d) =
        -anchorStableProjection hs hx ((j + 1) * N)
          (anchorDerivativeProduct (T := T) hx (j * N) N ps) := by
    change anchorStableProjection hs hx ((j + 1) * N)
        (anchorDerivativeProduct (T := T) hx (j * N) N
          (unstableBlockRightInverse hs strict j target₁ : E d)) -
      anchorStableProjection hs hx ((j + 1) * N)
        (anchorDerivativeProduct (T := T) hx (j * N) N
          (unstableBlockRightInverse hs strict j target₂ : E d)) = _
    rw [← map_sub, ← map_sub, hright_diff]
    have hsum :
        anchorStableProjection hs hx ((j + 1) * N)
            (anchorDerivativeProduct (T := T) hx (j * N) N ps) +
          anchorStableProjection hs hx ((j + 1) * N)
            (anchorDerivativeProduct (T := T) hx (j * N) N pu) = 0 := by
      rw [← map_add, ← map_add, hdecomp, hAw, hzd_stable_zero]
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hsum
  change
    ‖(unstableBlockCross hs strict j target₁ : E d) -
        (unstableBlockCross hs strict j target₂ : E d)‖ ≤
      (1 / 128 : ℝ) * ‖(target₁ : E d) - (target₂ : E d)‖
  rw [hcross_eq, norm_neg]
  have hfwd' :
      ‖anchorStableProjection hs hx ((j + 1) * N)
          (anchorDerivativeProduct (T := T) hx (j * N) N ps)‖ ≤
        (1 / 16 : ℝ) * ‖ps‖ := by
    simpa [Nat.add_mul] using hfwd
  have hz' : ‖zd‖ ≤ 2 * ‖target₁ - target₂‖ := by
    simpa [zd] using hz
  exact hfwd'.trans (by
    calc
      (1 / 16 : ℝ) * ‖ps‖ ≤ (1 / 16 : ℝ) * ((1 / 16 : ℝ) * ‖zd‖) :=
        mul_le_mul_of_nonneg_left hps (by norm_num)
      _ ≤ (1 / 256 : ℝ) * (2 * ‖target₁ - target₂‖) := by
        nlinarith only [hz']
      _ = (1 / 128 : ℝ) * ‖target₁ - target₂‖ := by ring)

def blockTransferTarget (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (_strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    BlockUnstableFiber hs hx N (j + 1) :=
  ⟨anchorUnstableProjection hs hx ((j + 1) * N)
      ((uNext : E d) -
        anchorDerivativeProduct (T := T) hx (j * N) N (s : E d) - c),
    anchorUnstableProjection_mem hs hx _ _⟩

def blockTransferUnstable (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    BlockUnstableFiber hs hx N j :=
  unstableBlockRightInverse hs strict j (blockTransferTarget hs strict j s uNext c)

def blockTransferStable (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    BlockStableFiber hs hx N (j + 1) :=
  ⟨anchorStableProjection hs hx ((j + 1) * N)
      (anchorDerivativeProduct (T := T) hx (j * N) N
          ((s : E d) + (blockTransferUnstable hs strict j s uNext c : E d)) + c),
    anchorStableProjection_mem hs hx _ _⟩

theorem blockTransfer_exact (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    (blockTransferStable hs strict j s uNext c : E d) + (uNext : E d) =
      anchorDerivativeProduct (T := T) hx (j * N) N
          ((s : E d) + (blockTransferUnstable hs strict j s uNext c : E d)) + c := by
  let rhs : E d :=
    anchorDerivativeProduct (T := T) hx (j * N) N
        ((s : E d) + (blockTransferUnstable hs strict j s uNext c : E d)) + c
  have hright := unstableBlockRightInverse_right hs strict j
    (blockTransferTarget hs strict j s uNext c)
  have huNext_proj : anchorUnstableProjection hs hx ((j + 1) * N) (uNext : E d) = uNext := by
    change unstableProjection hs (localTubeAnchorSeq hx ((j + 1) * N))
        (localTubeAnchorSeq_mem hx ((j + 1) * N)) (uNext : E d) = (uNext : E d)
    exact unstableProjection_apply_of_mem_unstable hs
      (localTubeAnchorSeq_mem hx ((j + 1) * N)) uNext.property
  have hunstable : anchorUnstableProjection hs hx ((j + 1) * N) rhs = uNext := by
    dsimp [rhs]
    rw [map_add, map_add, map_add]
    have hright' :
        anchorUnstableProjection hs hx ((j + 1) * N)
            (anchorDerivativeProduct (T := T) hx (j * N) N
              (blockTransferUnstable hs strict j s uNext c : E d)) =
          blockTransferTarget hs strict j s uNext c := by
      exact congrArg Subtype.val hright
    rw [hright']
    change anchorUnstableProjection hs hx ((j + 1) * N)
          (anchorDerivativeProduct (T := T) hx (j * N) N (s : E d)) +
        anchorUnstableProjection hs hx ((j + 1) * N)
          ((uNext : E d) -
            anchorDerivativeProduct (T := T) hx (j * N) N (s : E d) - c) +
        anchorUnstableProjection hs hx ((j + 1) * N) c = (uNext : E d)
    rw [map_sub, map_sub, huNext_proj]
    abel
  change anchorStableProjection hs hx ((j + 1) * N) rhs + (uNext : E d) = rhs
  rw [← hunstable]
  exact anchorProjection_decomp (T := T) (K := K) hs hx ((j + 1) * N) rhs

theorem blockTransferTarget_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    ‖blockTransferTarget hs strict j s uNext c‖ ≤
      M * (‖uNext‖ + (1 / 8 : ℝ) * ‖s‖ + ‖c‖) := by
  have hs_fwd := strict.forward_endpoint_le (j * N) (s : E d) s.property
  have hA :
      ‖anchorDerivativeProduct (T := T) hx (j * N) N (s : E d)‖ ≤
        (1 / 8 : ℝ) * ‖s‖ := by
    let ps := anchorStableProjection hs hx ((j + 1) * N)
      (anchorDerivativeProduct (T := T) hx (j * N) N (s : E d))
    let pu := anchorUnstableProjection hs hx ((j + 1) * N)
      (anchorDerivativeProduct (T := T) hx (j * N) N (s : E d))
    have hdecomp : ps + pu =
        anchorDerivativeProduct (T := T) hx (j * N) N (s : E d) :=
      anchorProjection_decomp (T := T) (K := K) hs hx _ _
    have hs_fwd_stable : ‖ps‖ ≤ (1 / 16 : ℝ) * ‖s‖ := by
      simpa [ps, Nat.add_mul] using hs_fwd.1
    have hs_fwd_unstable : ‖pu‖ ≤ (1 / 16 : ℝ) * ‖s‖ := by
      simpa [pu, Nat.add_mul] using hs_fwd.2
    calc
      ‖anchorDerivativeProduct (T := T) hx (j * N) N (s : E d)‖ = ‖ps + pu‖ := by
        rw [hdecomp]
      _ ≤ ‖ps‖ + ‖pu‖ := norm_add_le _ _
      _ ≤ (1 / 16 : ℝ) * ‖s‖ + (1 / 16 : ℝ) * ‖s‖ :=
        add_le_add hs_fwd_stable hs_fwd_unstable
      _ = (1 / 8 : ℝ) * ‖s‖ := by ring
  have harg :
      ‖(uNext : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s : E d) - c‖ ≤
        ‖uNext‖ + (1 / 8 : ℝ) * ‖s‖ + ‖c‖ := by
    calc
      ‖(uNext : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s : E d) - c‖ ≤
          ‖uNext‖ + ‖anchorDerivativeProduct (T := T) hx (j * N) N (s : E d)‖ + ‖c‖ := by
        calc
          _ ≤ ‖(uNext : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s : E d)‖ + ‖c‖ :=
            norm_sub_le _ _
          _ ≤ (‖uNext‖ + ‖anchorDerivativeProduct (T := T) hx (j * N) N (s : E d)‖) + ‖c‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ ‖uNext‖ + (1 / 8 : ℝ) * ‖s‖ + ‖c‖ :=
        add_le_add (add_le_add le_rfl hA) le_rfl
  exact (anchorProjection_vector_norm_le hs strict ((j + 1) * N)
    ((uNext : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s : E d) - c)).2.trans
      (mul_le_mul_of_nonneg_left harg strict.inputs.projectionBound_pos.le)

theorem blockTransferTarget_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s₁ s₂ : BlockStableFiber hs hx N j)
    (u₁ u₂ : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    ‖blockTransferTarget hs strict j s₁ u₁ c - blockTransferTarget hs strict j s₂ u₂ c‖ ≤
      ‖u₁ - u₂‖ + (1 / 16 : ℝ) * ‖s₁ - s₂‖ := by
  have hs_mem :
      ((s₁ : E d) - (s₂ : E d)) ∈ hs.stable (localTubeAnchorSeq hx (j * N)) :=
    Submodule.sub_mem _ s₁.property s₂.property
  have hfwd := (strict.forward_endpoint_le (j * N)
    ((s₁ : E d) - (s₂ : E d)) hs_mem).2
  have hu_proj :
      anchorUnstableProjection hs hx ((j + 1) * N) ((u₁ : E d) - (u₂ : E d)) =
        (u₁ : E d) - (u₂ : E d) := by
    rw [map_sub]
    have h₁ : anchorUnstableProjection hs hx ((j + 1) * N) (u₁ : E d) = u₁ := by
      change unstableProjection hs (localTubeAnchorSeq hx ((j + 1) * N))
          (localTubeAnchorSeq_mem hx ((j + 1) * N)) (u₁ : E d) = (u₁ : E d)
      exact unstableProjection_apply_of_mem_unstable hs
        (localTubeAnchorSeq_mem hx ((j + 1) * N)) u₁.property
    have h₂ : anchorUnstableProjection hs hx ((j + 1) * N) (u₂ : E d) = u₂ := by
      change unstableProjection hs (localTubeAnchorSeq hx ((j + 1) * N))
          (localTubeAnchorSeq_mem hx ((j + 1) * N)) (u₂ : E d) = (u₂ : E d)
      exact unstableProjection_apply_of_mem_unstable hs
        (localTubeAnchorSeq_mem hx ((j + 1) * N)) u₂.property
    rw [h₁, h₂]
  change
    ‖anchorUnstableProjection hs hx ((j + 1) * N)
          ((u₁ : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s₁ : E d) - c) -
        anchorUnstableProjection hs hx ((j + 1) * N)
          ((u₂ : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s₂ : E d) - c)‖ ≤ _
  rw [← map_sub]
  have harg :
      ((u₁ : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s₁ : E d) - c) -
          ((u₂ : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s₂ : E d) - c) =
        ((u₁ : E d) - (u₂ : E d)) -
          anchorDerivativeProduct (T := T) hx (j * N) N ((s₁ : E d) - (s₂ : E d)) := by
    rw [map_sub]
    abel
  rw [harg, map_sub, hu_proj]
  have hfwd' :
      ‖anchorUnstableProjection hs hx ((j + 1) * N)
          (anchorDerivativeProduct (T := T) hx (j * N) N
            ((s₁ : E d) - (s₂ : E d)))‖ ≤
        (1 / 16 : ℝ) * ‖s₁ - s₂‖ := by
    simpa [Nat.add_mul] using hfwd
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hfwd')

theorem blockTransferTarget_forcing_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c₁ c₂ : E d) :
    ‖blockTransferTarget hs strict j s uNext c₁ -
        blockTransferTarget hs strict j s uNext c₂‖ ≤ M * ‖c₁ - c₂‖ := by
  change
    ‖anchorUnstableProjection hs hx ((j + 1) * N)
          ((uNext : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s : E d) - c₁) -
        anchorUnstableProjection hs hx ((j + 1) * N)
          ((uNext : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s : E d) - c₂)‖ ≤ _
  rw [← map_sub]
  have harg :
      ((uNext : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s : E d) - c₁) -
          ((uNext : E d) - anchorDerivativeProduct (T := T) hx (j * N) N (s : E d) - c₂) =
        -(c₁ - c₂) := by abel
  rw [harg, map_neg, norm_neg]
  exact (anchorProjection_vector_norm_le hs strict ((j + 1) * N) (c₁ - c₂)).2

theorem blockTransferUnstable_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    ‖blockTransferUnstable hs strict j s uNext c‖ ≤
      (1 / 8 : ℝ) * ‖blockTransferTarget hs strict j s uNext c‖ :=
  unstableBlockRightInverse_norm_le hs strict j _

theorem blockTransferUnstable_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s₁ s₂ : BlockStableFiber hs hx N j)
    (u₁ u₂ : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    ‖blockTransferUnstable hs strict j s₁ u₁ c -
        blockTransferUnstable hs strict j s₂ u₂ c‖ ≤
      (1 / 8 : ℝ) * (‖u₁ - u₂‖ + (1 / 16 : ℝ) * ‖s₁ - s₂‖) := by
  exact (unstableBlockRightInverse_sub_norm_le hs strict j
    (blockTransferTarget hs strict j s₁ u₁ c)
    (blockTransferTarget hs strict j s₂ u₂ c)).trans
      (mul_le_mul_of_nonneg_left
        (blockTransferTarget_sub_norm_le hs strict j s₁ s₂ u₁ u₂ c) (by norm_num))

theorem blockTransferUnstable_forcing_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c₁ c₂ : E d) :
    ‖blockTransferUnstable hs strict j s uNext c₁ -
        blockTransferUnstable hs strict j s uNext c₂‖ ≤
      (M / 8) * ‖c₁ - c₂‖ := by
  exact (unstableBlockRightInverse_sub_norm_le hs strict j
    (blockTransferTarget hs strict j s uNext c₁)
    (blockTransferTarget hs strict j s uNext c₂)).trans (by
      calc
        (1 / 8 : ℝ) *
            ‖blockTransferTarget hs strict j s uNext c₁ -
              blockTransferTarget hs strict j s uNext c₂‖ ≤
            (1 / 8 : ℝ) * (M * ‖c₁ - c₂‖) :=
          mul_le_mul_of_nonneg_left
            (blockTransferTarget_forcing_sub_norm_le hs strict j s uNext c₁ c₂)
            (by norm_num)
        _ = (M / 8) * ‖c₁ - c₂‖ := by ring)

theorem blockTransferStable_decomp (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    (blockTransferStable hs strict j s uNext c : E d) =
      anchorStableProjection hs hx ((j + 1) * N)
          (anchorDerivativeProduct (T := T) hx (j * N) N (s : E d)) +
        (unstableBlockCross hs strict j (blockTransferTarget hs strict j s uNext c) : E d) +
        anchorStableProjection hs hx ((j + 1) * N) c := by
  change anchorStableProjection hs hx ((j + 1) * N)
      (anchorDerivativeProduct (T := T) hx (j * N) N
          ((s : E d) + (blockTransferUnstable hs strict j s uNext c : E d)) + c) = _
  rw [map_add, map_add, map_add]
  rfl

theorem blockTransferStable_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    ‖blockTransferStable hs strict j s uNext c‖ ≤
      (1 / 16 : ℝ) * ‖s‖ +
        (1 / 128 : ℝ) * ‖blockTransferTarget hs strict j s uNext c‖ + M * ‖c‖ := by
  have hs_fwd := (strict.forward_endpoint_le (j * N) (s : E d) s.property).1
  have hs_fwd' :
      ‖anchorStableProjection hs hx ((j + 1) * N)
          (anchorDerivativeProduct (T := T) hx (j * N) N (s : E d))‖ ≤
        (1 / 16 : ℝ) * ‖s‖ := by
    simpa [Nat.add_mul] using hs_fwd
  have hcross := unstableBlockCross_norm_le hs strict j
    (blockTransferTarget hs strict j s uNext c)
  have hc := (anchorProjection_vector_norm_le hs strict ((j + 1) * N) c).1
  change ‖(blockTransferStable hs strict j s uNext c : E d)‖ ≤ _
  rw [blockTransferStable_decomp]
  exact (by
    calc
      ‖anchorStableProjection hs hx ((j + 1) * N)
            (anchorDerivativeProduct (T := T) hx (j * N) N (s : E d)) +
          (unstableBlockCross hs strict j (blockTransferTarget hs strict j s uNext c) : E d) +
          anchorStableProjection hs hx ((j + 1) * N) c‖ ≤
          ‖anchorStableProjection hs hx ((j + 1) * N)
            (anchorDerivativeProduct (T := T) hx (j * N) N (s : E d))‖ +
            ‖unstableBlockCross hs strict j (blockTransferTarget hs strict j s uNext c)‖ +
            ‖anchorStableProjection hs hx ((j + 1) * N) c‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (1 / 16 : ℝ) * ‖s‖ +
          (1 / 128 : ℝ) * ‖blockTransferTarget hs strict j s uNext c‖ + M * ‖c‖ :=
        add_le_add (add_le_add hs_fwd' hcross) hc)

theorem blockTransferStable_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s₁ s₂ : BlockStableFiber hs hx N j)
    (u₁ u₂ : BlockUnstableFiber hs hx N (j + 1)) (c : E d) :
    ‖blockTransferStable hs strict j s₁ u₁ c -
        blockTransferStable hs strict j s₂ u₂ c‖ ≤
      (1 / 16 : ℝ) * ‖s₁ - s₂‖ +
        (1 / 128 : ℝ) * (‖u₁ - u₂‖ + (1 / 16 : ℝ) * ‖s₁ - s₂‖) := by
  have hs_mem :
      ((s₁ : E d) - (s₂ : E d)) ∈ hs.stable (localTubeAnchorSeq hx (j * N)) :=
    Submodule.sub_mem _ s₁.property s₂.property
  have hs_fwd := (strict.forward_endpoint_le (j * N)
    ((s₁ : E d) - (s₂ : E d)) hs_mem).1
  have hs_fwd' :
      ‖anchorStableProjection hs hx ((j + 1) * N)
          (anchorDerivativeProduct (T := T) hx (j * N) N
            ((s₁ : E d) - (s₂ : E d)))‖ ≤
        (1 / 16 : ℝ) * ‖s₁ - s₂‖ := by
    simpa [Nat.add_mul] using hs_fwd
  have hcross := unstableBlockCross_sub_norm_le hs strict j
    (blockTransferTarget hs strict j s₁ u₁ c)
    (blockTransferTarget hs strict j s₂ u₂ c)
  have htarget := blockTransferTarget_sub_norm_le hs strict j s₁ s₂ u₁ u₂ c
  change
    ‖(blockTransferStable hs strict j s₁ u₁ c : E d) -
        (blockTransferStable hs strict j s₂ u₂ c : E d)‖ ≤ _
  rw [blockTransferStable_decomp, blockTransferStable_decomp]
  simp only [add_sub_add_right_eq_sub]
  rw [add_sub_add_comm, ← map_sub, ← map_sub]
  exact (norm_add_le _ _).trans (add_le_add hs_fwd'
    (hcross.trans (mul_le_mul_of_nonneg_left htarget (by norm_num))))

theorem blockTransferStable_forcing_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (j : ℕ) (s : BlockStableFiber hs hx N j)
    (uNext : BlockUnstableFiber hs hx N (j + 1)) (c₁ c₂ : E d) :
    ‖blockTransferStable hs strict j s uNext c₁ -
        blockTransferStable hs strict j s uNext c₂‖ ≤
      (129 * M / 128) * ‖c₁ - c₂‖ := by
  have hcross := unstableBlockCross_sub_norm_le hs strict j
    (blockTransferTarget hs strict j s uNext c₁)
    (blockTransferTarget hs strict j s uNext c₂)
  have htarget := blockTransferTarget_forcing_sub_norm_le hs strict j s uNext c₁ c₂
  have hc := (anchorProjection_vector_norm_le hs strict ((j + 1) * N) (c₁ - c₂)).1
  change
    ‖(blockTransferStable hs strict j s uNext c₁ : E d) -
        (blockTransferStable hs strict j s uNext c₂ : E d)‖ ≤ _
  rw [blockTransferStable_decomp, blockTransferStable_decomp]
  have hdiff :
      (anchorStableProjection hs hx ((j + 1) * N)
            (anchorDerivativeProduct (T := T) hx (j * N) N (s : E d)) +
          (unstableBlockCross hs strict j (blockTransferTarget hs strict j s uNext c₁) : E d) +
          anchorStableProjection hs hx ((j + 1) * N) c₁) -
        (anchorStableProjection hs hx ((j + 1) * N)
            (anchorDerivativeProduct (T := T) hx (j * N) N (s : E d)) +
          (unstableBlockCross hs strict j (blockTransferTarget hs strict j s uNext c₂) : E d) +
          anchorStableProjection hs hx ((j + 1) * N) c₂) =
        ((unstableBlockCross hs strict j (blockTransferTarget hs strict j s uNext c₁) : E d) -
          (unstableBlockCross hs strict j (blockTransferTarget hs strict j s uNext c₂) : E d)) +
          anchorStableProjection hs hx ((j + 1) * N) (c₁ - c₂) := by
    rw [map_sub]
    abel
  rw [hdiff]
  exact (norm_add_le _ _).trans (by
    calc
      ‖(unstableBlockCross hs strict j (blockTransferTarget hs strict j s uNext c₁) : E d) -
          (unstableBlockCross hs strict j (blockTransferTarget hs strict j s uNext c₂) : E d)‖ +
          ‖anchorStableProjection hs hx ((j + 1) * N) (c₁ - c₂)‖ ≤
        (1 / 128 : ℝ) * (M * ‖c₁ - c₂‖) + M * ‖c₁ - c₂‖ :=
          add_le_add
            (hcross.trans (mul_le_mul_of_nonneg_left htarget (by norm_num))) hc
      _ = (129 * M / 128) * ‖c₁ - c₂‖ := by ring)

def blockStableAt (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (s : BlockStableSeq hs hx N) (j : ℕ) : BlockStableFiber hs hx N j :=
  ⟨(s : CorrectionSeq d) j, s.property j⟩

def blockUnstableAt (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (u : BlockUnstableSeq hs hx N) (j : ℕ) : BlockUnstableFiber hs hx N j :=
  ⟨(u : CorrectionSeq d) j, u.property j⟩

noncomputable def blockTransferTargetSeq (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    EdgeUnstableSeq hs hx N := by
  let C : ℝ := M *
    (‖(p.2 : CorrectionSeq d)‖ + (1 / 8 : ℝ) * ‖(p.1 : CorrectionSeq d)‖ + ‖c‖)
  let f : ℕ → E d := fun j =>
    blockTransferTarget hs strict j (blockStableAt hs p.1 j)
      (blockUnstableAt hs p.2 (j + 1)) (c j)
  have hf : ∀ j : ℕ, ‖f j‖ ≤ C := by
    intro j
    have hpoint := blockTransferTarget_norm_le hs strict j (blockStableAt hs p.1 j)
      (blockUnstableAt hs p.2 (j + 1)) (c j)
    have hs_eval : ‖(p.1 : CorrectionSeq d) j‖ ≤ ‖(p.1 : CorrectionSeq d)‖ :=
      correctionSeq_apply_norm_le_norm (p.1 : CorrectionSeq d) j
    have hu_eval : ‖(p.2 : CorrectionSeq d) (j + 1)‖ ≤ ‖(p.2 : CorrectionSeq d)‖ :=
      correctionSeq_apply_norm_le_norm (p.2 : CorrectionSeq d) (j + 1)
    have hc_eval : ‖c j‖ ≤ ‖c‖ := correctionSeq_apply_norm_le_norm c j
    exact hpoint.trans (mul_le_mul_of_nonneg_left (by
      dsimp [blockStableAt, blockUnstableAt]
      nlinarith only [hs_eval, hu_eval, hc_eval]) strict.inputs.projectionBound_pos.le)
  let target : CorrectionSeq d :=
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f C hf
  refine ⟨target, ?_⟩
  intro j
  exact (blockTransferTarget hs strict j (blockStableAt hs p.1 j)
    (blockUnstableAt hs p.2 (j + 1)) (c j)).property

@[simp]
theorem blockTransferTargetSeq_apply (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N)
    (j : ℕ) :
    (blockTransferTargetSeq hs strict c p : CorrectionSeq d) j =
      blockTransferTarget hs strict j (blockStableAt hs p.1 j)
        (blockUnstableAt hs p.2 (j + 1)) (c j) :=
  rfl

theorem blockTransferTargetSeq_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(blockTransferTargetSeq hs strict c p : CorrectionSeq d)‖ ≤
      M * (‖(p.2 : CorrectionSeq d)‖ +
        (1 / 8 : ℝ) * ‖(p.1 : CorrectionSeq d)‖ + ‖c‖) := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  rw [blockTransferTargetSeq_apply]
  have hpoint := blockTransferTarget_norm_le hs strict j (blockStableAt hs p.1 j)
    (blockUnstableAt hs p.2 (j + 1)) (c j)
  have hs_eval : ‖(p.1 : CorrectionSeq d) j‖ ≤ ‖(p.1 : CorrectionSeq d)‖ :=
    correctionSeq_apply_norm_le_norm (p.1 : CorrectionSeq d) j
  have hu_eval : ‖(p.2 : CorrectionSeq d) (j + 1)‖ ≤ ‖(p.2 : CorrectionSeq d)‖ :=
    correctionSeq_apply_norm_le_norm (p.2 : CorrectionSeq d) (j + 1)
  have hc_eval : ‖c j‖ ≤ ‖c‖ := correctionSeq_apply_norm_le_norm c j
  exact hpoint.trans (mul_le_mul_of_nonneg_left (by
    dsimp [blockStableAt, blockUnstableAt]
    nlinarith only [hs_eval, hu_eval, hc_eval]) strict.inputs.projectionBound_pos.le)

theorem blockTransferTargetSeq_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d)
    (p q : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(blockTransferTargetSeq hs strict c p : CorrectionSeq d) -
        (blockTransferTargetSeq hs strict c q : CorrectionSeq d)‖ ≤
      ‖(p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d)‖ +
        (1 / 16 : ℝ) * ‖(p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  change
    ‖blockTransferTarget hs strict j (blockStableAt hs p.1 j)
          (blockUnstableAt hs p.2 (j + 1)) (c j) -
        blockTransferTarget hs strict j (blockStableAt hs q.1 j)
          (blockUnstableAt hs q.2 (j + 1)) (c j)‖ ≤ _
  have hpoint := blockTransferTarget_sub_norm_le hs strict j
    (blockStableAt hs p.1 j) (blockStableAt hs q.1 j)
    (blockUnstableAt hs p.2 (j + 1)) (blockUnstableAt hs q.2 (j + 1)) (c j)
  have hs_eval :
      ‖(p.1 : CorrectionSeq d) j - (q.1 : CorrectionSeq d) j‖ ≤
        ‖(p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)‖ := by
    simpa using correctionSeq_apply_norm_le_norm
      ((p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)) j
  have hu_eval :
      ‖(p.2 : CorrectionSeq d) (j + 1) - (q.2 : CorrectionSeq d) (j + 1)‖ ≤
        ‖(p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d)‖ := by
    simpa using correctionSeq_apply_norm_le_norm
      ((p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d)) (j + 1)
  exact hpoint.trans (by
    dsimp [blockStableAt, blockUnstableAt]
    exact add_le_add hu_eval (mul_le_mul_of_nonneg_left hs_eval (by norm_num)))

theorem blockTransferTargetSeq_forcing_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c₁ c₂ : CorrectionSeq d)
    (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(blockTransferTargetSeq hs strict c₁ p : CorrectionSeq d) -
        (blockTransferTargetSeq hs strict c₂ p : CorrectionSeq d)‖ ≤
      M * ‖c₁ - c₂‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  change
    ‖blockTransferTarget hs strict j (blockStableAt hs p.1 j)
          (blockUnstableAt hs p.2 (j + 1)) (c₁ j) -
        blockTransferTarget hs strict j (blockStableAt hs p.1 j)
          (blockUnstableAt hs p.2 (j + 1)) (c₂ j)‖ ≤ _
  have hpoint := blockTransferTarget_forcing_sub_norm_le hs strict j
    (blockStableAt hs p.1 j) (blockUnstableAt hs p.2 (j + 1)) (c₁ j) (c₂ j)
  have hc_eval : ‖c₁ j - c₂ j‖ ≤ ‖c₁ - c₂‖ := by
    simpa using correctionSeq_apply_norm_le_norm (c₁ - c₂) j
  exact hpoint.trans
    (mul_le_mul_of_nonneg_left hc_eval strict.inputs.projectionBound_pos.le)

def edgeUnstableAt (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (u : EdgeUnstableSeq hs hx N) (j : ℕ) : BlockUnstableFiber hs hx N (j + 1) :=
  ⟨(u : CorrectionSeq d) j, u.property j⟩

noncomputable def blockTransferUnstableSeq (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    BlockUnstableSeq hs hx N := by
  let target := blockTransferTargetSeq hs strict c p
  let C : ℝ := (1 / 8 : ℝ) * ‖(target : CorrectionSeq d)‖
  let f : ℕ → E d := fun j =>
    unstableBlockRightInverse hs strict j (edgeUnstableAt hs target j)
  have hf : ∀ j : ℕ, ‖f j‖ ≤ C := by
    intro j
    exact (unstableBlockRightInverse_norm_le hs strict j (edgeUnstableAt hs target j)).trans
      (mul_le_mul_of_nonneg_left
        (correctionSeq_apply_norm_le_norm (target : CorrectionSeq d) j) (by norm_num))
  let u : CorrectionSeq d :=
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f C hf
  refine ⟨u, ?_⟩
  intro j
  exact (unstableBlockRightInverse hs strict j (edgeUnstableAt hs target j)).property

@[simp]
theorem blockTransferUnstableSeq_apply (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N)
    (j : ℕ) :
    (blockTransferUnstableSeq hs strict c p : CorrectionSeq d) j =
      unstableBlockRightInverse hs strict j
        (edgeUnstableAt hs (blockTransferTargetSeq hs strict c p) j) :=
  rfl

theorem blockTransferUnstableSeq_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(blockTransferUnstableSeq hs strict c p : CorrectionSeq d)‖ ≤
      (1 / 8 : ℝ) * ‖(blockTransferTargetSeq hs strict c p : CorrectionSeq d)‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  rw [blockTransferUnstableSeq_apply]
  exact (unstableBlockRightInverse_norm_le hs strict j _).trans
    (mul_le_mul_of_nonneg_left
      (correctionSeq_apply_norm_le_norm
        (blockTransferTargetSeq hs strict c p : CorrectionSeq d) j) (by norm_num))

theorem blockTransferUnstableSeq_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d)
    (p q : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(blockTransferUnstableSeq hs strict c p : CorrectionSeq d) -
        (blockTransferUnstableSeq hs strict c q : CorrectionSeq d)‖ ≤
      (1 / 8 : ℝ) *
        (‖(p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d)‖ +
          (1 / 16 : ℝ) * ‖(p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)‖) := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  change
    ‖unstableBlockRightInverse hs strict j
          (edgeUnstableAt hs (blockTransferTargetSeq hs strict c p) j) -
        unstableBlockRightInverse hs strict j
          (edgeUnstableAt hs (blockTransferTargetSeq hs strict c q) j)‖ ≤ _
  have hpoint := unstableBlockRightInverse_sub_norm_le hs strict j
    (edgeUnstableAt hs (blockTransferTargetSeq hs strict c p) j)
    (edgeUnstableAt hs (blockTransferTargetSeq hs strict c q) j)
  have htarget := blockTransferTargetSeq_sub_norm_le hs strict c p q
  have heval :
      ‖(blockTransferTargetSeq hs strict c p : CorrectionSeq d) j -
          (blockTransferTargetSeq hs strict c q : CorrectionSeq d) j‖ ≤
        ‖(blockTransferTargetSeq hs strict c p : CorrectionSeq d) -
          (blockTransferTargetSeq hs strict c q : CorrectionSeq d)‖ := by
    simpa using correctionSeq_apply_norm_le_norm
      ((blockTransferTargetSeq hs strict c p : CorrectionSeq d) -
        (blockTransferTargetSeq hs strict c q : CorrectionSeq d)) j
  exact hpoint.trans (mul_le_mul_of_nonneg_left
    (heval.trans htarget) (by norm_num))

theorem blockTransferUnstableSeq_forcing_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c₁ c₂ : CorrectionSeq d)
    (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(blockTransferUnstableSeq hs strict c₁ p : CorrectionSeq d) -
        (blockTransferUnstableSeq hs strict c₂ p : CorrectionSeq d)‖ ≤
      (M / 8) * ‖c₁ - c₂‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  change
    ‖unstableBlockRightInverse hs strict j
          (edgeUnstableAt hs (blockTransferTargetSeq hs strict c₁ p) j) -
        unstableBlockRightInverse hs strict j
          (edgeUnstableAt hs (blockTransferTargetSeq hs strict c₂ p) j)‖ ≤ _
  have hpoint := unstableBlockRightInverse_sub_norm_le hs strict j
    (edgeUnstableAt hs (blockTransferTargetSeq hs strict c₁ p) j)
    (edgeUnstableAt hs (blockTransferTargetSeq hs strict c₂ p) j)
  have htarget := blockTransferTargetSeq_forcing_sub_norm_le hs strict c₁ c₂ p
  have heval :
      ‖(blockTransferTargetSeq hs strict c₁ p : CorrectionSeq d) j -
          (blockTransferTargetSeq hs strict c₂ p : CorrectionSeq d) j‖ ≤
        ‖(blockTransferTargetSeq hs strict c₁ p : CorrectionSeq d) -
          (blockTransferTargetSeq hs strict c₂ p : CorrectionSeq d)‖ := by
    simpa using correctionSeq_apply_norm_le_norm
      ((blockTransferTargetSeq hs strict c₁ p : CorrectionSeq d) -
        (blockTransferTargetSeq hs strict c₂ p : CorrectionSeq d)) j
  exact hpoint.trans (by
    calc
      (1 / 8 : ℝ) *
          ‖edgeUnstableAt hs (blockTransferTargetSeq hs strict c₁ p) j -
            edgeUnstableAt hs (blockTransferTargetSeq hs strict c₂ p) j‖ ≤
        (1 / 8 : ℝ) * (M * ‖c₁ - c₂‖) :=
          mul_le_mul_of_nonneg_left (heval.trans htarget) (by norm_num)
      _ = (M / 8) * ‖c₁ - c₂‖ := by ring)

noncomputable def blockTransferStableSeq (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    BlockStableSeq hs hx N := by
  let target := blockTransferTargetSeq hs strict c p
  let C : ℝ := (1 / 16 : ℝ) * ‖(p.1 : CorrectionSeq d)‖ +
    (1 / 128 : ℝ) * ‖(target : CorrectionSeq d)‖ + M * ‖c‖
  let f : ℕ → E d := fun j =>
    match j with
    | 0 => 0
    | k + 1 => blockTransferStable hs strict k (blockStableAt hs p.1 k)
        (blockUnstableAt hs p.2 (k + 1)) (c k)
  have hf : ∀ j : ℕ, ‖f j‖ ≤ C := by
    intro j
    cases j with
    | zero =>
        dsimp [f, C]
        have h₁ : 0 ≤ (1 / 16 : ℝ) * ‖(p.1 : CorrectionSeq d)‖ :=
          mul_nonneg (by norm_num) (norm_nonneg _)
        have h₂ : 0 ≤ (1 / 128 : ℝ) * ‖(target : CorrectionSeq d)‖ :=
          mul_nonneg (by norm_num) (norm_nonneg _)
        have h₃ : 0 ≤ M * ‖c‖ :=
          mul_nonneg strict.inputs.projectionBound_pos.le (norm_nonneg _)
        rw [norm_zero]
        exact add_nonneg (add_nonneg h₁ h₂) h₃
    | succ k =>
        have hpoint := blockTransferStable_norm_le hs strict k (blockStableAt hs p.1 k)
          (blockUnstableAt hs p.2 (k + 1)) (c k)
        have hs_eval := correctionSeq_apply_norm_le_norm (p.1 : CorrectionSeq d) k
        have ht_eval := correctionSeq_apply_norm_le_norm (target : CorrectionSeq d) k
        have hc_eval := correctionSeq_apply_norm_le_norm c k
        dsimp [f, C]
        exact hpoint.trans (by
          dsimp [blockStableAt]
          exact add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left hs_eval (by norm_num))
            (mul_le_mul_of_nonneg_left ht_eval (by norm_num)))
            (mul_le_mul_of_nonneg_left hc_eval strict.inputs.projectionBound_pos.le))
  let s : CorrectionSeq d :=
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f C hf
  refine ⟨s, ?_⟩
  intro j
  cases j with
  | zero => exact Submodule.zero_mem _
  | succ k => exact (blockTransferStable hs strict k (blockStableAt hs p.1 k)
      (blockUnstableAt hs p.2 (k + 1)) (c k)).property

@[simp]
theorem blockTransferStableSeq_zero (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    (blockTransferStableSeq hs strict c p : CorrectionSeq d) 0 = 0 :=
  rfl

@[simp]
theorem blockTransferStableSeq_succ (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N)
    (k : ℕ) :
    (blockTransferStableSeq hs strict c p : CorrectionSeq d) (k + 1) =
      blockTransferStable hs strict k (blockStableAt hs p.1 k)
        (blockUnstableAt hs p.2 (k + 1)) (c k) :=
  rfl

theorem blockTransferStableSeq_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(blockTransferStableSeq hs strict c p : CorrectionSeq d)‖ ≤
      (1 / 16 : ℝ) * ‖(p.1 : CorrectionSeq d)‖ +
        (1 / 128 : ℝ) * ‖(blockTransferTargetSeq hs strict c p : CorrectionSeq d)‖ +
        M * ‖c‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  cases j with
  | zero =>
      rw [blockTransferStableSeq_zero, norm_zero]
      have h₁ : 0 ≤ (1 / 16 : ℝ) * ‖(p.1 : CorrectionSeq d)‖ :=
        mul_nonneg (by norm_num) (norm_nonneg _)
      have h₂ : 0 ≤ (1 / 128 : ℝ) *
          ‖(blockTransferTargetSeq hs strict c p : CorrectionSeq d)‖ :=
        mul_nonneg (by norm_num) (norm_nonneg _)
      have h₃ : 0 ≤ M * ‖c‖ :=
        mul_nonneg strict.inputs.projectionBound_pos.le (norm_nonneg _)
      exact add_nonneg (add_nonneg h₁ h₂) h₃
  | succ k =>
      rw [blockTransferStableSeq_succ]
      have hpoint := blockTransferStable_norm_le hs strict k (blockStableAt hs p.1 k)
        (blockUnstableAt hs p.2 (k + 1)) (c k)
      have hs_eval := correctionSeq_apply_norm_le_norm (p.1 : CorrectionSeq d) k
      have ht_eval := correctionSeq_apply_norm_le_norm
        (blockTransferTargetSeq hs strict c p : CorrectionSeq d) k
      have hc_eval := correctionSeq_apply_norm_le_norm c k
      exact hpoint.trans (by
        dsimp [blockStableAt]
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hs_eval (by norm_num))
          (mul_le_mul_of_nonneg_left ht_eval (by norm_num)))
          (mul_le_mul_of_nonneg_left hc_eval strict.inputs.projectionBound_pos.le))

theorem blockTransferStableSeq_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d)
    (p q : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(blockTransferStableSeq hs strict c p : CorrectionSeq d) -
        (blockTransferStableSeq hs strict c q : CorrectionSeq d)‖ ≤
      (1 / 16 : ℝ) * ‖(p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)‖ +
        (1 / 128 : ℝ) *
          (‖(p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d)‖ +
            (1 / 16 : ℝ) * ‖(p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)‖) := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  cases j with
  | zero =>
      change
        ‖(blockTransferStableSeq hs strict c p : CorrectionSeq d) 0 -
            (blockTransferStableSeq hs strict c q : CorrectionSeq d) 0‖ ≤ _
      rw [blockTransferStableSeq_zero, blockTransferStableSeq_zero, sub_zero, norm_zero]
      positivity
  | succ k =>
      change
        ‖(blockTransferStableSeq hs strict c p : CorrectionSeq d) (k + 1) -
            (blockTransferStableSeq hs strict c q : CorrectionSeq d) (k + 1)‖ ≤ _
      rw [blockTransferStableSeq_succ, blockTransferStableSeq_succ]
      have hpoint := blockTransferStable_sub_norm_le hs strict k
        (blockStableAt hs p.1 k) (blockStableAt hs q.1 k)
        (blockUnstableAt hs p.2 (k + 1)) (blockUnstableAt hs q.2 (k + 1)) (c k)
      have hs_eval :
          ‖(p.1 : CorrectionSeq d) k - (q.1 : CorrectionSeq d) k‖ ≤
            ‖(p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)‖ := by
        simpa using correctionSeq_apply_norm_le_norm
          ((p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)) k
      have hu_eval :
          ‖(p.2 : CorrectionSeq d) (k + 1) - (q.2 : CorrectionSeq d) (k + 1)‖ ≤
            ‖(p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d)‖ := by
        simpa using correctionSeq_apply_norm_le_norm
          ((p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d)) (k + 1)
      exact hpoint.trans (by
        dsimp [blockStableAt, blockUnstableAt]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hs_eval (by norm_num))
          (mul_le_mul_of_nonneg_left
            (add_le_add hu_eval (mul_le_mul_of_nonneg_left hs_eval (by norm_num)))
            (by norm_num)))

theorem blockTransferStableSeq_forcing_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c₁ c₂ : CorrectionSeq d)
    (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(blockTransferStableSeq hs strict c₁ p : CorrectionSeq d) -
        (blockTransferStableSeq hs strict c₂ p : CorrectionSeq d)‖ ≤
      (129 * M / 128) * ‖c₁ - c₂‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  cases j with
  | zero =>
      change
        ‖(blockTransferStableSeq hs strict c₁ p : CorrectionSeq d) 0 -
            (blockTransferStableSeq hs strict c₂ p : CorrectionSeq d) 0‖ ≤ _
      rw [blockTransferStableSeq_zero, blockTransferStableSeq_zero, sub_zero, norm_zero]
      have hM : 0 ≤ M := strict.inputs.projectionBound_pos.le
      positivity
  | succ k =>
      change
        ‖(blockTransferStableSeq hs strict c₁ p : CorrectionSeq d) (k + 1) -
            (blockTransferStableSeq hs strict c₂ p : CorrectionSeq d) (k + 1)‖ ≤ _
      rw [blockTransferStableSeq_succ, blockTransferStableSeq_succ]
      have hpoint := blockTransferStable_forcing_sub_norm_le hs strict k
        (blockStableAt hs p.1 k) (blockUnstableAt hs p.2 (k + 1)) (c₁ k) (c₂ k)
      have hc_eval : ‖c₁ k - c₂ k‖ ≤ ‖c₁ - c₂‖ := by
        simpa using correctionSeq_apply_norm_le_norm (c₁ - c₂) k
      exact hpoint.trans (mul_le_mul_of_nonneg_left hc_eval (by
        have hM : 0 ≤ M := strict.inputs.projectionBound_pos.le
        positivity))

noncomputable def blockBoundaryStep (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d)
    (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    BlockStableSeq hs hx N × BlockUnstableSeq hs hx N :=
  (blockTransferStableSeq hs strict c p, blockTransferUnstableSeq hs strict c p)

theorem blockPair_fst_norm_le_dist (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (p q : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)‖ ≤ dist p q := by
  have h : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  change dist (p.1 : CorrectionSeq d) (q.1 : CorrectionSeq d) ≤ dist p q at h
  simpa [dist_eq_norm] using h

theorem blockPair_snd_norm_le_dist (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (p q : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    ‖(p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d)‖ ≤ dist p q := by
  have h : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  change dist (p.2 : CorrectionSeq d) (q.2 : CorrectionSeq d) ≤ dist p q at h
  simpa [dist_eq_norm] using h

theorem blockBoundaryStep_contracting (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) :
    ContractingWith (1 / 4 : NNReal) (blockBoundaryStep hs strict c) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro p q
  let R : ℝ := dist p q
  have hs_in : ‖(p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)‖ ≤ R :=
    blockPair_fst_norm_le_dist hs p q
  have hu_in : ‖(p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d)‖ ≤ R :=
    blockPair_snd_norm_le_dist hs p q
  have hs_out_raw := blockTransferStableSeq_sub_norm_le hs strict c p q
  have hu_out_raw := blockTransferUnstableSeq_sub_norm_le hs strict c p q
  have hR_nonneg : 0 ≤ R := dist_nonneg
  have hs_out :
      ‖(blockTransferStableSeq hs strict c p : CorrectionSeq d) -
          (blockTransferStableSeq hs strict c q : CorrectionSeq d)‖ ≤
        (1 / 4 : ℝ) * R := by
    exact hs_out_raw.trans (by
      nlinarith only [hs_in, hu_in, hR_nonneg,
        norm_nonneg ((p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)),
        norm_nonneg ((p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d))])
  have hu_out :
      ‖(blockTransferUnstableSeq hs strict c p : CorrectionSeq d) -
          (blockTransferUnstableSeq hs strict c q : CorrectionSeq d)‖ ≤
        (1 / 4 : ℝ) * R := by
    exact hu_out_raw.trans (by
      nlinarith only [hs_in, hu_in, hR_nonneg,
        norm_nonneg ((p.1 : CorrectionSeq d) - (q.1 : CorrectionSeq d)),
        norm_nonneg ((p.2 : CorrectionSeq d) - (q.2 : CorrectionSeq d))])
  change dist (blockBoundaryStep hs strict c p) (blockBoundaryStep hs strict c q) ≤
    (1 / 4 : ℝ) * dist p q
  rw [Prod.dist_eq, max_le_iff]
  constructor
  · change
      dist (blockTransferStableSeq hs strict c p : CorrectionSeq d)
          (blockTransferStableSeq hs strict c q : CorrectionSeq d) ≤ _
    simpa [dist_eq_norm] using hs_out
  · change
      dist (blockTransferUnstableSeq hs strict c p : CorrectionSeq d)
          (blockTransferUnstableSeq hs strict c q : CorrectionSeq d) ≤ _
    simpa [dist_eq_norm] using hu_out

theorem blockBoundaryStep_forcing_dist_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c₁ c₂ : CorrectionSeq d)
    (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) :
    dist (blockBoundaryStep hs strict c₁ p) (blockBoundaryStep hs strict c₂ p) ≤
      2 * M * ‖c₁ - c₂‖ := by
  have hs_out := blockTransferStableSeq_forcing_sub_norm_le hs strict c₁ c₂ p
  have hu_out := blockTransferUnstableSeq_forcing_sub_norm_le hs strict c₁ c₂ p
  have hM : 0 ≤ M := strict.inputs.projectionBound_pos.le
  change
    max
      (dist (blockTransferStableSeq hs strict c₁ p)
        (blockTransferStableSeq hs strict c₂ p))
      (dist (blockTransferUnstableSeq hs strict c₁ p)
        (blockTransferUnstableSeq hs strict c₂ p)) ≤ _
  rw [max_le_iff]
  constructor
  · change
      dist (blockTransferStableSeq hs strict c₁ p : CorrectionSeq d)
        (blockTransferStableSeq hs strict c₂ p : CorrectionSeq d) ≤ _
    rw [dist_eq_norm]
    exact hs_out.trans (by
      have hn : 0 ≤ ‖c₁ - c₂‖ := norm_nonneg _
      nlinarith)
  · change
      dist (blockTransferUnstableSeq hs strict c₁ p : CorrectionSeq d)
        (blockTransferUnstableSeq hs strict c₂ p : CorrectionSeq d) ≤ _
    rw [dist_eq_norm]
    exact hu_out.trans (by
      have hn : 0 ≤ ‖c₁ - c₂‖ := norm_nonneg _
      nlinarith)

def zeroBlockStableSeq (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) :
    BlockStableSeq hs hx N :=
  ⟨0, fun _j => Submodule.zero_mem _⟩

def zeroBlockUnstableSeq (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) :
    BlockUnstableSeq hs hx N :=
  ⟨0, fun _j => Submodule.zero_mem _⟩

def zeroBlockPair (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) :
    BlockStableSeq hs hx N × BlockUnstableSeq hs hx N :=
  (zeroBlockStableSeq hs hx N, zeroBlockUnstableSeq hs hx N)

instance instNonemptyBlockStableSeq (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ} :
    Nonempty (BlockStableSeq hs hx N) :=
  ⟨zeroBlockStableSeq hs hx N⟩

instance instNonemptyBlockUnstableSeq (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ} :
    Nonempty (BlockUnstableSeq hs hx N) :=
  ⟨zeroBlockUnstableSeq hs hx N⟩

instance instCompleteSpaceBlockStableSeq (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ} :
    CompleteSpace (BlockStableSeq hs hx N) := by
  change CompleteSpace (SubmoduleSeqSet fun j => hs.stable (localTubeAnchorSeq hx (j * N)))
  infer_instance

instance instCompleteSpaceBlockUnstableSeq (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ} :
    CompleteSpace (BlockUnstableSeq hs hx N) := by
  change CompleteSpace (SubmoduleSeqSet fun j => hs.unstable (localTubeAnchorSeq hx (j * N)))
  infer_instance

theorem blockBoundaryStep_zeroPair_dist_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) :
    dist (blockBoundaryStep hs strict c (zeroBlockPair hs hx N))
      (zeroBlockPair hs hx N) ≤ 2 * M * ‖c‖ := by
  let p := zeroBlockPair hs hx N
  have htarget := blockTransferTargetSeq_norm_le hs strict c p
  have hp_stable : ‖(p.1 : CorrectionSeq d)‖ = 0 := by
    simp [p, zeroBlockPair, zeroBlockStableSeq]
  have hp_unstable : ‖(p.2 : CorrectionSeq d)‖ = 0 := by
    simp [p, zeroBlockPair, zeroBlockUnstableSeq]
  have htarget' :
      ‖(blockTransferTargetSeq hs strict c p : CorrectionSeq d)‖ ≤ M * ‖c‖ := by
    simpa [hp_stable, hp_unstable] using htarget
  have hu := blockTransferUnstableSeq_norm_le hs strict c p
  have hs' := blockTransferStableSeq_norm_le hs strict c p
  have hM : 0 ≤ M := strict.inputs.projectionBound_pos.le
  have hstable :
      ‖(blockTransferStableSeq hs strict c p : CorrectionSeq d)‖ ≤ 2 * M * ‖c‖ := by
    exact hs'.trans (by
      rw [hp_stable]
      have hn : 0 ≤ ‖c‖ := norm_nonneg _
      nlinarith only [htarget', hM, hn,
        norm_nonneg (blockTransferTargetSeq hs strict c p : CorrectionSeq d)])
  have hunstable :
      ‖(blockTransferUnstableSeq hs strict c p : CorrectionSeq d)‖ ≤ 2 * M * ‖c‖ := by
    exact hu.trans (by
      have hn : 0 ≤ ‖c‖ := norm_nonneg _
      nlinarith only [htarget', hM, hn,
        norm_nonneg (blockTransferTargetSeq hs strict c p : CorrectionSeq d)])
  rw [Prod.dist_eq, max_le_iff]
  constructor
  · change
      dist (blockTransferStableSeq hs strict c p : CorrectionSeq d)
        (zeroBlockStableSeq hs hx N : CorrectionSeq d) ≤ _
    change dist (blockTransferStableSeq hs strict c p : CorrectionSeq d) 0 ≤ _
    simpa [dist_eq_norm] using hstable
  · change
      dist (blockTransferUnstableSeq hs strict c p : CorrectionSeq d)
        (zeroBlockUnstableSeq hs hx N : CorrectionSeq d) ≤ _
    change dist (blockTransferUnstableSeq hs strict c p : CorrectionSeq d) 0 ≤ _
    simpa [dist_eq_norm] using hunstable

noncomputable def blockBoundaryFixedPoint (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N :=
  ContractingWith.fixedPoint (blockBoundaryStep hs strict c)
    (blockBoundaryStep_contracting hs strict c)

theorem blockBoundaryFixedPoint_isFixed (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) :
    blockBoundaryStep hs strict c (blockBoundaryFixedPoint hs strict c) =
      blockBoundaryFixedPoint hs strict c :=
  (blockBoundaryStep_contracting hs strict c).fixedPoint_isFixedPt

theorem blockBoundaryFixedPoint_dist_zero_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) :
    dist (blockBoundaryFixedPoint hs strict c) (zeroBlockPair hs hx N) ≤
      4 * M * ‖c‖ := by
  let z := blockBoundaryFixedPoint hs strict c
  let p₀ := zeroBlockPair hs hx N
  have hfixed : blockBoundaryStep hs strict c z = z :=
    blockBoundaryFixedPoint_isFixed hs strict c
  have hcontract :
      dist (blockBoundaryStep hs strict c z) (blockBoundaryStep hs strict c p₀) ≤
        (1 / 4 : ℝ) * dist z p₀ := by
    simpa using (blockBoundaryStep_contracting hs strict c).dist_le_mul z p₀
  have hzero :
      dist (blockBoundaryStep hs strict c p₀) p₀ ≤ 2 * M * ‖c‖ := by
    simpa [p₀] using blockBoundaryStep_zeroPair_dist_le hs strict c
  have htri :
      dist z p₀ ≤
        dist (blockBoundaryStep hs strict c z) (blockBoundaryStep hs strict c p₀) +
          dist (blockBoundaryStep hs strict c p₀) p₀ := by
    rw [hfixed]
    exact dist_triangle _ _ _
  have hM : 0 ≤ M := strict.inputs.projectionBound_pos.le
  have hn : 0 ≤ ‖c‖ := norm_nonneg _
  have hdist : 0 ≤ dist z p₀ := dist_nonneg
  change dist z p₀ ≤ 4 * M * ‖c‖
  nlinarith only [hcontract, hzero, htri, hM, hn, hdist]

theorem blockBoundaryFixedPoint_dist_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c₁ c₂ : CorrectionSeq d) :
    dist (blockBoundaryFixedPoint hs strict c₁) (blockBoundaryFixedPoint hs strict c₂) ≤
      4 * M * ‖c₁ - c₂‖ := by
  have h := (blockBoundaryStep_contracting hs strict c₁).fixedPoint_lipschitz_in_map
    (blockBoundaryStep_contracting hs strict c₂)
    (blockBoundaryStep_forcing_dist_le hs strict c₁ c₂)
  have hM : 0 ≤ M := strict.inputs.projectionBound_pos.le
  have hn : 0 ≤ ‖c₁ - c₂‖ := norm_nonneg _
  exact h.trans (by
    norm_num
    nlinarith)

theorem blockBoundaryFixedPoint_fst_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) :
    ‖((blockBoundaryFixedPoint hs strict c).1 : CorrectionSeq d)‖ ≤ 4 * M * ‖c‖ := by
  let z := blockBoundaryFixedPoint hs strict c
  let p₀ := zeroBlockPair hs hx N
  have hcomp := blockPair_fst_norm_le_dist hs z p₀
  have hdist := blockBoundaryFixedPoint_dist_zero_le hs strict c
  have hzero : (p₀.1 : CorrectionSeq d) = 0 := by
    rfl
  change ‖(z.1 : CorrectionSeq d)‖ ≤ 4 * M * ‖c‖
  rw [← sub_zero (z.1 : CorrectionSeq d), ← hzero]
  exact hcomp.trans hdist

theorem blockBoundaryFixedPoint_snd_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) :
    ‖((blockBoundaryFixedPoint hs strict c).2 : CorrectionSeq d)‖ ≤ 4 * M * ‖c‖ := by
  let z := blockBoundaryFixedPoint hs strict c
  let p₀ := zeroBlockPair hs hx N
  have hcomp := blockPair_snd_norm_le_dist hs z p₀
  have hdist := blockBoundaryFixedPoint_dist_zero_le hs strict c
  have hzero : (p₀.2 : CorrectionSeq d) = 0 := by
    rfl
  change ‖(z.2 : CorrectionSeq d)‖ ≤ 4 * M * ‖c‖
  rw [← sub_zero (z.2 : CorrectionSeq d), ← hzero]
  exact hcomp.trans hdist

theorem blockBoundaryFixedPoint_fst_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c₁ c₂ : CorrectionSeq d) :
    ‖((blockBoundaryFixedPoint hs strict c₁).1 : CorrectionSeq d) -
        ((blockBoundaryFixedPoint hs strict c₂).1 : CorrectionSeq d)‖ ≤
      4 * M * ‖c₁ - c₂‖ :=
  (blockPair_fst_norm_le_dist hs (blockBoundaryFixedPoint hs strict c₁)
    (blockBoundaryFixedPoint hs strict c₂)).trans
      (blockBoundaryFixedPoint_dist_le hs strict c₁ c₂)

theorem blockBoundaryFixedPoint_snd_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c₁ c₂ : CorrectionSeq d) :
    ‖((blockBoundaryFixedPoint hs strict c₁).2 : CorrectionSeq d) -
        ((blockBoundaryFixedPoint hs strict c₂).2 : CorrectionSeq d)‖ ≤
      4 * M * ‖c₁ - c₂‖ :=
  (blockPair_snd_norm_le_dist hs (blockBoundaryFixedPoint hs strict c₁)
    (blockBoundaryFixedPoint hs strict c₂)).trans
      (blockBoundaryFixedPoint_dist_le hs strict c₁ c₂)

def blockBoundaryValue (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (p : BlockStableSeq hs hx N × BlockUnstableSeq hs hx N) (j : ℕ) : E d :=
  (p.1 : CorrectionSeq d) j + (p.2 : CorrectionSeq d) j

theorem blockBoundaryFixedPoint_recurrence (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (j : ℕ) :
    blockBoundaryValue hs (blockBoundaryFixedPoint hs strict c) (j + 1) =
      anchorDerivativeProduct (T := T) hx (j * N) N
        (blockBoundaryValue hs (blockBoundaryFixedPoint hs strict c) j) + c j := by
  let p := blockBoundaryFixedPoint hs strict c
  have hfixed := blockBoundaryFixedPoint_isFixed hs strict c
  have hfst : blockTransferStableSeq hs strict c p = p.1 := congrArg Prod.fst hfixed
  have hsnd : blockTransferUnstableSeq hs strict c p = p.2 := congrArg Prod.snd hfixed
  have hstable :
      (blockTransferStable hs strict j (blockStableAt hs p.1 j)
          (blockUnstableAt hs p.2 (j + 1)) (c j) : E d) =
        (p.1 : CorrectionSeq d) (j + 1) := by
    have h := congrArg (fun s : BlockStableSeq hs hx N => (s : CorrectionSeq d) (j + 1)) hfst
    simpa using h
  have hunstable :
      (blockTransferUnstable hs strict j (blockStableAt hs p.1 j)
          (blockUnstableAt hs p.2 (j + 1)) (c j) : E d) =
        (p.2 : CorrectionSeq d) j := by
    have h := congrArg (fun u : BlockUnstableSeq hs hx N => (u : CorrectionSeq d) j) hsnd
    simpa [blockTransferUnstable, edgeUnstableAt] using h
  have hexact := blockTransfer_exact hs strict j (blockStableAt hs p.1 j)
    (blockUnstableAt hs p.2 (j + 1)) (c j)
  dsimp [blockBoundaryValue]
  rw [← hstable, ← hunstable]
  exact hexact

noncomputable def blockBoundarySeq (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) : CorrectionSeq d :=
  let p := blockBoundaryFixedPoint hs strict c
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (blockBoundaryValue hs p) (8 * M * ‖c‖)
    (by
      intro j
      have hs_norm := blockBoundaryFixedPoint_fst_norm_le hs strict c
      have hu_norm := blockBoundaryFixedPoint_snd_norm_le hs strict c
      have hs_eval := correctionSeq_apply_norm_le_norm (p.1 : CorrectionSeq d) j
      have hu_eval := correctionSeq_apply_norm_le_norm (p.2 : CorrectionSeq d) j
      exact (norm_add_le _ _).trans (by
        nlinarith only [hs_norm, hu_norm, hs_eval, hu_eval,
          norm_nonneg ((p.1 : CorrectionSeq d) j), norm_nonneg ((p.2 : CorrectionSeq d) j),
          strict.inputs.projectionBound_pos.le, norm_nonneg c]))

@[simp]
theorem blockBoundarySeq_apply (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) (j : ℕ) :
    blockBoundarySeq hs strict c j =
      blockBoundaryValue hs (blockBoundaryFixedPoint hs strict c) j :=
  rfl

theorem blockBoundarySeq_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c : CorrectionSeq d) :
    ‖blockBoundarySeq hs strict c‖ ≤ 8 * M * ‖c‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  have hs_norm := blockBoundaryFixedPoint_fst_norm_le hs strict c
  have hu_norm := blockBoundaryFixedPoint_snd_norm_le hs strict c
  have hs_eval := correctionSeq_apply_norm_le_norm
    ((blockBoundaryFixedPoint hs strict c).1 : CorrectionSeq d) j
  have hu_eval := correctionSeq_apply_norm_le_norm
    ((blockBoundaryFixedPoint hs strict c).2 : CorrectionSeq d) j
  rw [blockBoundarySeq_apply]
  exact (norm_add_le _ _).trans (by
    nlinarith only [hs_norm, hu_norm, hs_eval, hu_eval,
      norm_nonneg (((blockBoundaryFixedPoint hs strict c).1 : CorrectionSeq d) j),
      norm_nonneg (((blockBoundaryFixedPoint hs strict c).2 : CorrectionSeq d) j),
      strict.inputs.projectionBound_pos.le, norm_nonneg c])

theorem blockBoundarySeq_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (c₁ c₂ : CorrectionSeq d) :
    ‖blockBoundarySeq hs strict c₁ - blockBoundarySeq hs strict c₂‖ ≤
      8 * M * ‖c₁ - c₂‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro j
  let p₁ := blockBoundaryFixedPoint hs strict c₁
  let p₂ := blockBoundaryFixedPoint hs strict c₂
  have hs_norm := blockBoundaryFixedPoint_fst_sub_norm_le hs strict c₁ c₂
  have hu_norm := blockBoundaryFixedPoint_snd_sub_norm_le hs strict c₁ c₂
  have hs_eval :
      ‖(p₁.1 : CorrectionSeq d) j - (p₂.1 : CorrectionSeq d) j‖ ≤
        ‖(p₁.1 : CorrectionSeq d) - (p₂.1 : CorrectionSeq d)‖ := by
    simpa using correctionSeq_apply_norm_le_norm
      ((p₁.1 : CorrectionSeq d) - (p₂.1 : CorrectionSeq d)) j
  have hu_eval :
      ‖(p₁.2 : CorrectionSeq d) j - (p₂.2 : CorrectionSeq d) j‖ ≤
        ‖(p₁.2 : CorrectionSeq d) - (p₂.2 : CorrectionSeq d)‖ := by
    simpa using correctionSeq_apply_norm_le_norm
      ((p₁.2 : CorrectionSeq d) - (p₂.2 : CorrectionSeq d)) j
  change
    ‖((p₁.1 : CorrectionSeq d) j + (p₁.2 : CorrectionSeq d) j) -
        ((p₂.1 : CorrectionSeq d) j + (p₂.2 : CorrectionSeq d) j)‖ ≤ _
  have hdecomp :
      ((p₁.1 : CorrectionSeq d) j + (p₁.2 : CorrectionSeq d) j) -
          ((p₂.1 : CorrectionSeq d) j + (p₂.2 : CorrectionSeq d) j) =
        ((p₁.1 : CorrectionSeq d) j - (p₂.1 : CorrectionSeq d) j) +
          ((p₁.2 : CorrectionSeq d) j - (p₂.2 : CorrectionSeq d) j) := by
    abel
  rw [hdecomp]
  exact (norm_add_le _ _).trans (by
    nlinarith only [hs_norm, hu_norm, hs_eval, hu_eval,
      norm_nonneg ((p₁.1 : CorrectionSeq d) j - (p₂.1 : CorrectionSeq d) j),
      norm_nonneg ((p₁.2 : CorrectionSeq d) j - (p₂.2 : CorrectionSeq d) j),
      strict.inputs.projectionBound_pos.le, norm_nonneg (c₁ - c₂)])

noncomputable def linearRecurrence {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d) (v₀ : E d) : ℕ → E d
  | 0 => v₀
  | n + 1 => anchorDerivative (T := T) hx n (linearRecurrence hx b v₀ n) + b n

@[simp]
theorem linearRecurrence_zero {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d) (v₀ : E d) :
    linearRecurrence (T := T) hx b v₀ 0 = v₀ :=
  rfl

@[simp]
theorem linearRecurrence_succ {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d) (v₀ : E d) (n : ℕ) :
    linearRecurrence (T := T) hx b v₀ (n + 1) =
      anchorDerivative (T := T) hx n (linearRecurrence (T := T) hx b v₀ n) + b n :=
  rfl

theorem linearRecurrence_affine_advance {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (b : CorrectionSeq d) (v₀ : E d) :
    ∀ n m : ℕ,
      linearRecurrence (T := T) hx b v₀ (n + m) =
        anchorDerivativeProduct (T := T) hx n m (linearRecurrence (T := T) hx b v₀ n) +
          linearForcingAdvance (T := T) hx b n m := by
  intro n m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, linearRecurrence_succ, ih, map_add]
      rw [anchorDerivativeProduct_succ_apply, linearForcingAdvance_succ]
      abel

noncomputable def blockLinearSolutionFun (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ derivativeBound)
    (b : CorrectionSeq d) : ℕ → E d :=
  let c := blockForcingSeq (T := T) hx b N strict.derivativeBound_nonneg
    hA
  linearRecurrence (T := T) hx b (blockBoundarySeq hs strict c 0)

theorem blockLinearSolutionFun_recurrence (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ derivativeBound)
    (b : CorrectionSeq d) (n : ℕ) :
    blockLinearSolutionFun hs strict hA b (n + 1) =
      anchorDerivative (T := T) hx n (blockLinearSolutionFun hs strict hA b n) + b n :=
  rfl

theorem blockLinearSolutionFun_block (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ derivativeBound)
    (b : CorrectionSeq d) :
    ∀ j : ℕ,
      blockLinearSolutionFun hs strict hA b (j * N) =
        blockBoundarySeq hs strict
          (blockForcingSeq (T := T) hx b N strict.derivativeBound_nonneg hA) j := by
  intro j
  let c := blockForcingSeq (T := T) hx b N strict.derivativeBound_nonneg hA
  induction j with
  | zero =>
      simp [blockLinearSolutionFun]
  | succ j ih =>
      have ih' :
          linearRecurrence (T := T) hx b (blockBoundarySeq hs strict c 0) (j * N) =
            blockBoundarySeq hs strict c j := by
        simpa [blockLinearSolutionFun, c] using ih
      have haffine := linearRecurrence_affine_advance (T := T) hx b
        (blockBoundarySeq hs strict c 0) (j * N) N
      have hrec := blockBoundaryFixedPoint_recurrence hs strict c j
      change
        linearRecurrence (T := T) hx b (blockBoundarySeq hs strict c 0) ((j + 1) * N) =
          blockBoundarySeq hs strict c (j + 1)
      rw [show (j + 1) * N = j * N + N by simp [Nat.add_mul]]
      rw [haffine, ih']
      have hc : linearForcingAdvance (T := T) hx b (j * N) N = c j := by
        rfl
      rw [hc]
      simpa [blockBoundarySeq_apply] using hrec.symm

def finitePowerCap (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => max (a ^ (n + 1)) (finitePowerCap a n)

theorem finitePowerCap_pos {a : ℝ} (_ha : 0 ≤ a) :
    ∀ n : ℕ, 0 < finitePowerCap a n := by
  intro n
  induction n with
  | zero => simp [finitePowerCap]
  | succ n ih =>
      exact lt_of_lt_of_le ih (le_max_right _ _)

theorem pow_le_finitePowerCap {a : ℝ} (_ha : 0 ≤ a) :
    ∀ {m N : ℕ}, m ≤ N → a ^ m ≤ finitePowerCap a N := by
  intro m N hm
  induction N generalizing m with
  | zero =>
      have hm0 : m = 0 := by omega
      subst hm0
      simp [finitePowerCap]
  | succ N ih =>
      by_cases hmN : m ≤ N
      · exact (ih hmN).trans (le_max_right _ _)
      · have hm_eq : m = N + 1 := by omega
        subst hm_eq
        exact le_max_left _ _

def crudeGreenBound (M D : ℝ) (N : ℕ) : ℝ :=
  finitePowerCap D N * (8 * M * finiteTrackingAmplification D N) +
    finiteTrackingAmplificationCap D N + 1

theorem crudeGreenBound_pos {M D : ℝ} {N : ℕ} (hM : 0 < M) (hD : 0 ≤ D) :
    0 < crudeGreenBound M D N := by
  have hpow : 0 < finitePowerCap D N := finitePowerCap_pos hD N
  have hamp : 0 ≤ finiteTrackingAmplification D N :=
    finiteTrackingAmplification_nonneg hD N
  have hcap : 0 < finiteTrackingAmplificationCap D N :=
    finiteTrackingAmplificationCap_pos hD N
  dsimp [crudeGreenBound]
  positivity

theorem blockLinearSolutionFun_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ derivativeBound)
    (b : CorrectionSeq d) (n : ℕ) :
    ‖blockLinearSolutionFun hs strict hA b n‖ ≤ crudeGreenBound M derivativeBound N * ‖b‖ := by
  let c := blockForcingSeq (T := T) hx b N strict.derivativeBound_nonneg hA
  let q : ℕ := n / N
  let m : ℕ := n % N
  have hN : 0 < N := strict.inputs.block_pos
  have hm_lt : m < N := Nat.mod_lt n hN
  have hn : n = q * N + m := by
    dsimp [q, m]
    calc
      n = n % N + N * (n / N) := (Nat.mod_add_div n N).symm
      _ = (n / N) * N + n % N := by ac_rfl
  have haffine := linearRecurrence_affine_advance (T := T) hx b
    (blockBoundarySeq hs strict c 0) (q * N) m
  have hblock := blockLinearSolutionFun_block hs strict hA b q
  have hblock' :
      linearRecurrence (T := T) hx b (blockBoundarySeq hs strict c 0) (q * N) =
        blockBoundarySeq hs strict c q := by
    simpa [blockLinearSolutionFun, c] using hblock
  have hboundary_norm := blockBoundarySeq_norm_le hs strict c
  have hc_norm := blockForcingSeq_norm_le (T := T) hx b N strict.derivativeBound_nonneg hA
  have hboundary_eval := correctionSeq_apply_norm_le_norm (blockBoundarySeq hs strict c) q
  have hprod := strict.forward_inside_bound (q * N) m (Nat.le_of_lt hm_lt)
    (blockBoundarySeq hs strict c q)
  have hforcing := linearForcingAdvance_norm_le (T := T) hx b
    strict.derivativeBound_nonneg hA (q * N) m
  have hpow_cap := pow_le_finitePowerCap strict.derivativeBound_nonneg (Nat.le_of_lt hm_lt)
  have hamp_cap := finiteTrackingAmplification_le_cap strict.derivativeBound_nonneg
    (Nat.le_of_lt hm_lt)
  rw [hn]
  change
    ‖linearRecurrence (T := T) hx b (blockBoundarySeq hs strict c 0) (q * N + m)‖ ≤ _
  rw [haffine]
  rw [hblock']
  calc
    ‖anchorDerivativeProduct (T := T) hx (q * N) m (blockBoundarySeq hs strict c q) +
        linearForcingAdvance (T := T) hx b (q * N) m‖ ≤
      ‖anchorDerivativeProduct (T := T) hx (q * N) m (blockBoundarySeq hs strict c q)‖ +
        ‖linearForcingAdvance (T := T) hx b (q * N) m‖ := norm_add_le _ _
    _ ≤ derivativeBound ^ m * ‖blockBoundarySeq hs strict c q‖ +
        finiteTrackingAmplification derivativeBound m * ‖b‖ :=
      add_le_add hprod hforcing
    _ ≤ derivativeBound ^ m * (8 * M * ‖c‖) +
        finiteTrackingAmplification derivativeBound m * ‖b‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hboundary_eval.trans hboundary_norm)
          (pow_nonneg strict.derivativeBound_nonneg m)) le_rfl
    _ ≤ derivativeBound ^ m *
          (8 * M * (finiteTrackingAmplification derivativeBound N * ‖b‖)) +
        finiteTrackingAmplification derivativeBound m * ‖b‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hc_norm
            (mul_nonneg (by norm_num) strict.inputs.projectionBound_pos.le))
          (pow_nonneg strict.derivativeBound_nonneg m)) le_rfl
    _ ≤ finitePowerCap derivativeBound N *
          (8 * M * (finiteTrackingAmplification derivativeBound N * ‖b‖)) +
        finiteTrackingAmplificationCap derivativeBound N * ‖b‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right hpow_cap
          (mul_nonneg
            (mul_nonneg (by norm_num) strict.inputs.projectionBound_pos.le)
            (mul_nonneg
              (finiteTrackingAmplification_nonneg strict.derivativeBound_nonneg N)
              (norm_nonneg b))))
        (mul_le_mul_of_nonneg_right hamp_cap (norm_nonneg b))
    _ ≤ crudeGreenBound M derivativeBound N * ‖b‖ := by
      have hcap_nonneg : 0 ≤ finiteTrackingAmplificationCap derivativeBound N :=
        (finiteTrackingAmplificationCap_pos strict.derivativeBound_nonneg N).le
      have hpow_nonneg : 0 ≤ finitePowerCap derivativeBound N :=
        (finitePowerCap_pos strict.derivativeBound_nonneg N).le
      have hamp_nonneg : 0 ≤ finiteTrackingAmplification derivativeBound N :=
        finiteTrackingAmplification_nonneg strict.derivativeBound_nonneg N
      have hb_nonneg : 0 ≤ ‖b‖ := norm_nonneg b
      dsimp [crudeGreenBound]
      ring_nf
      nlinarith

theorem blockLinearSolutionFun_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ derivativeBound)
    (b c : CorrectionSeq d) (n : ℕ) :
    ‖blockLinearSolutionFun hs strict hA b n -
        blockLinearSolutionFun hs strict hA c n‖ ≤
      crudeGreenBound M derivativeBound N * ‖b - c‖ := by
  let fb := blockForcingSeq (T := T) hx b N strict.derivativeBound_nonneg hA
  let fc := blockForcingSeq (T := T) hx c N strict.derivativeBound_nonneg hA
  let q : ℕ := n / N
  let m : ℕ := n % N
  have hN : 0 < N := strict.inputs.block_pos
  have hm_lt : m < N := Nat.mod_lt n hN
  have hn : n = q * N + m := by
    dsimp [q, m]
    calc
      n = n % N + N * (n / N) := (Nat.mod_add_div n N).symm
      _ = (n / N) * N + n % N := by ac_rfl
  have haffine_b := linearRecurrence_affine_advance (T := T) hx b
    (blockBoundarySeq hs strict fb 0) (q * N) m
  have haffine_c := linearRecurrence_affine_advance (T := T) hx c
    (blockBoundarySeq hs strict fc 0) (q * N) m
  have hblock_b := blockLinearSolutionFun_block hs strict hA b q
  have hblock_c := blockLinearSolutionFun_block hs strict hA c q
  have hblock_b' :
      linearRecurrence (T := T) hx b (blockBoundarySeq hs strict fb 0) (q * N) =
        blockBoundarySeq hs strict fb q := by
    simpa [blockLinearSolutionFun, fb] using hblock_b
  have hblock_c' :
      linearRecurrence (T := T) hx c (blockBoundarySeq hs strict fc 0) (q * N) =
        blockBoundarySeq hs strict fc q := by
    simpa [blockLinearSolutionFun, fc] using hblock_c
  have hboundary_norm := blockBoundarySeq_sub_norm_le hs strict fb fc
  have hforcing_block_norm := blockForcingSeq_sub_norm_le (T := T) hx b c N
    strict.derivativeBound_nonneg hA
  have hboundary_eval :
      ‖blockBoundarySeq hs strict fb q - blockBoundarySeq hs strict fc q‖ ≤
        ‖blockBoundarySeq hs strict fb - blockBoundarySeq hs strict fc‖ := by
    simpa using correctionSeq_apply_norm_le_norm
      (blockBoundarySeq hs strict fb - blockBoundarySeq hs strict fc) q
  have hprod := strict.forward_inside_bound (q * N) m (Nat.le_of_lt hm_lt)
    (blockBoundarySeq hs strict fb q - blockBoundarySeq hs strict fc q)
  have hforcing := linearForcingAdvance_norm_le (T := T) hx (b - c)
    strict.derivativeBound_nonneg hA (q * N) m
  have hpow_cap := pow_le_finitePowerCap strict.derivativeBound_nonneg (Nat.le_of_lt hm_lt)
  have hamp_cap := finiteTrackingAmplification_le_cap strict.derivativeBound_nonneg
    (Nat.le_of_lt hm_lt)
  rw [hn]
  change
    ‖linearRecurrence (T := T) hx b (blockBoundarySeq hs strict fb 0) (q * N + m) -
        linearRecurrence (T := T) hx c (blockBoundarySeq hs strict fc 0) (q * N + m)‖ ≤ _
  rw [haffine_b, haffine_c, hblock_b', hblock_c']
  have hdecomp :
      anchorDerivativeProduct (T := T) hx (q * N) m (blockBoundarySeq hs strict fb q) +
            linearForcingAdvance (T := T) hx b (q * N) m -
          (anchorDerivativeProduct (T := T) hx (q * N) m (blockBoundarySeq hs strict fc q) +
            linearForcingAdvance (T := T) hx c (q * N) m) =
        anchorDerivativeProduct (T := T) hx (q * N) m
            (blockBoundarySeq hs strict fb q - blockBoundarySeq hs strict fc q) +
          (linearForcingAdvance (T := T) hx b (q * N) m -
            linearForcingAdvance (T := T) hx c (q * N) m) := by
    rw [map_sub]
    abel
  rw [hdecomp, linearForcingAdvance_sub]
  calc
    ‖anchorDerivativeProduct (T := T) hx (q * N) m
          (blockBoundarySeq hs strict fb q - blockBoundarySeq hs strict fc q) +
        linearForcingAdvance (T := T) hx (b - c) (q * N) m‖ ≤
      ‖anchorDerivativeProduct (T := T) hx (q * N) m
          (blockBoundarySeq hs strict fb q - blockBoundarySeq hs strict fc q)‖ +
        ‖linearForcingAdvance (T := T) hx (b - c) (q * N) m‖ := norm_add_le _ _
    _ ≤ derivativeBound ^ m *
          ‖blockBoundarySeq hs strict fb q - blockBoundarySeq hs strict fc q‖ +
        finiteTrackingAmplification derivativeBound m * ‖b - c‖ :=
      add_le_add hprod hforcing
    _ ≤ derivativeBound ^ m *
          (8 * M * ‖blockForcingSeq (T := T) hx b N strict.derivativeBound_nonneg hA -
            blockForcingSeq (T := T) hx c N strict.derivativeBound_nonneg hA‖) +
        finiteTrackingAmplification derivativeBound m * ‖b - c‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left (hboundary_eval.trans hboundary_norm)
          (pow_nonneg strict.derivativeBound_nonneg m)) le_rfl
    _ ≤ derivativeBound ^ m *
          (8 * M * (finiteTrackingAmplification derivativeBound N * ‖b - c‖)) +
        finiteTrackingAmplification derivativeBound m * ‖b - c‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hforcing_block_norm
            (mul_nonneg (by norm_num) strict.inputs.projectionBound_pos.le))
          (pow_nonneg strict.derivativeBound_nonneg m)) le_rfl
    _ ≤ finitePowerCap derivativeBound N *
          (8 * M * (finiteTrackingAmplification derivativeBound N * ‖b - c‖)) +
        finiteTrackingAmplificationCap derivativeBound N * ‖b - c‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right hpow_cap
          (mul_nonneg
            (mul_nonneg (by norm_num) strict.inputs.projectionBound_pos.le)
            (mul_nonneg
              (finiteTrackingAmplification_nonneg strict.derivativeBound_nonneg N)
              (norm_nonneg (b - c)))))
        (mul_le_mul_of_nonneg_right hamp_cap (norm_nonneg (b - c)))
    _ ≤ crudeGreenBound M derivativeBound N * ‖b - c‖ := by
      have hcap_nonneg : 0 ≤ finiteTrackingAmplificationCap derivativeBound N :=
        (finiteTrackingAmplificationCap_pos strict.derivativeBound_nonneg N).le
      have hpow_nonneg : 0 ≤ finitePowerCap derivativeBound N :=
        (finitePowerCap_pos strict.derivativeBound_nonneg N).le
      have hamp_nonneg : 0 ≤ finiteTrackingAmplification derivativeBound N :=
        finiteTrackingAmplification_nonneg strict.derivativeBound_nonneg N
      have hbc_nonneg : 0 ≤ ‖b - c‖ := norm_nonneg (b - c)
      dsimp [crudeGreenBound]
      ring_nf
      nlinarith

noncomputable def blockLinearSolution (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ derivativeBound)
    (b : CorrectionSeq d) : CorrectionSeq d :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (blockLinearSolutionFun hs strict hA b)
    (crudeGreenBound M derivativeBound N * ‖b‖)
    (blockLinearSolutionFun_norm_le hs strict hA b)

@[simp]
theorem blockLinearSolution_apply (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ derivativeBound)
    (b : CorrectionSeq d) (n : ℕ) :
    blockLinearSolution hs strict hA b n = blockLinearSolutionFun hs strict hA b n :=
  rfl

theorem blockLinearSolution_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ derivativeBound)
    (b : CorrectionSeq d) :
    ‖blockLinearSolution hs strict hA b‖ ≤ crudeGreenBound M derivativeBound N * ‖b‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro n
  exact blockLinearSolutionFun_norm_le hs strict hA b n

theorem blockLinearSolution_sub_norm_le (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ derivativeBound)
    (b c : CorrectionSeq d) :
    ‖blockLinearSolution hs strict hA b - blockLinearSolution hs strict hA c‖ ≤
      crudeGreenBound M derivativeBound N * ‖b - c‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro n
  exact blockLinearSolutionFun_sub_norm_le hs strict hA b c n

noncomputable def anchorLinearSolver_of_strictBlock (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (hA : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ derivativeBound) :
    AnchorLinearSolver (T := T) (K := K) hx (crudeGreenBound M derivativeBound N) where
  solve := blockLinearSolution hs strict hA
  recurrence := fun b n => blockLinearSolutionFun_recurrence hs strict hA b n
  bound := blockLinearSolution_norm_le hs strict hA
  lipschitz := blockLinearSolution_sub_norm_le hs strict hA

end

end Submission.Shadowing
