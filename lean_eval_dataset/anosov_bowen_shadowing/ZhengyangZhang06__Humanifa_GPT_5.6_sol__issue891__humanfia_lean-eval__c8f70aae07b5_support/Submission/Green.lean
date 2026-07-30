import Submission.Shadowing

open LeanEval.Dynamics.HyperbolicShadowingProblem
open scoped Topology NNReal

namespace Submission.Shadowing

variable {d : ℕ} {T : E d ≃ₜ E d} {K : Set (E d)}

def SubmoduleSeqSet (V : ℕ → Submodule ℝ (E d)) : Set (CorrectionSeq d) :=
  {u | ∀ n : ℕ, u n ∈ V n}

theorem isClosed_submoduleSeqSet (V : ℕ → Submodule ℝ (E d)) :
    IsClosed (SubmoduleSeqSet V) := by
  rw [show SubmoduleSeqSet V = ⋂ n : ℕ, {u : CorrectionSeq d | u n ∈ V n} by
    ext u
    simp [SubmoduleSeqSet]]
  exact isClosed_iInter fun n =>
    (Submodule.closed_of_finiteDimensional (V n)).preimage
      (BoundedContinuousFunction.evalCLM ℝ n).continuous

instance instCompleteSpaceSubmoduleSeqSet (V : ℕ → Submodule ℝ (E d)) :
    CompleteSpace (SubmoduleSeqSet V) :=
  (isClosed_submoduleSeqSet V).completeSpace_coe

instance instNonemptySubmoduleSeqSet (V : ℕ → Submodule ℝ (E d)) :
    Nonempty (SubmoduleSeqSet V) :=
  ⟨⟨0, by intro n; exact (V n).zero_mem⟩⟩

def BlockStableSet (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) : Set (CorrectionSeq d) :=
  SubmoduleSeqSet fun j => hs.stable (localTubeAnchorSeq hx (j * N))

def BlockUnstableSet (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) : Set (CorrectionSeq d) :=
  SubmoduleSeqSet fun j => hs.unstable (localTubeAnchorSeq hx (j * N))

def EdgeStableSet (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) : Set (CorrectionSeq d) :=
  SubmoduleSeqSet fun j => hs.stable (localTubeAnchorSeq hx ((j + 1) * N))

def EdgeUnstableSet (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) : Set (CorrectionSeq d) :=
  SubmoduleSeqSet fun j => hs.unstable (localTubeAnchorSeq hx ((j + 1) * N))

abbrev BlockStableSeq (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) :=
  {u : CorrectionSeq d // u ∈ BlockStableSet hs hx N}

abbrev BlockUnstableSeq (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) :=
  {u : CorrectionSeq d // u ∈ BlockUnstableSet hs hx N}

abbrev EdgeStableSeq (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) :=
  {u : CorrectionSeq d // u ∈ EdgeStableSet hs hx N}

abbrev EdgeUnstableSeq (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) :=
  {u : CorrectionSeq d // u ∈ EdgeUnstableSet hs hx N}

abbrev EdgeSplitSeq (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (N : ℕ) :=
  EdgeStableSeq hs hx N × EdgeUnstableSeq hs hx N

noncomputable def stableBlockStep (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (g : EdgeStableSeq hs hx N) (s : BlockStableSeq hs hx N) :
    BlockStableSeq hs hx N := by
  let C : ℝ := (1 / 16 : ℝ) * ‖(s : CorrectionSeq d)‖ + ‖(g : CorrectionSeq d)‖
  let f : ℕ → E d := fun j =>
    match j with
    | 0 => 0
    | k + 1 =>
        anchorStableProjection hs hx ((k + 1) * N)
            (anchorDerivativeProduct (T := T) hx (k * N) N ((s : CorrectionSeq d) k)) +
          (g : CorrectionSeq d) k
  have hf_bound : ∀ j : ℕ, ‖f j‖ ≤ C := by
    intro j
    cases j with
    | zero =>
        dsimp [f, C]
        have hs_nonneg : 0 ≤ ‖(s : CorrectionSeq d)‖ := norm_nonneg _
        have hg_nonneg : 0 ≤ ‖(g : CorrectionSeq d)‖ := norm_nonneg _
        norm_num
        positivity
    | succ k =>
        have hs_mem : (s : CorrectionSeq d) k ∈
            hs.stable (localTubeAnchorSeq hx (k * N)) := s.property k
        have hendpoint :=
          (strict.forward_endpoint_le (k * N) ((s : CorrectionSeq d) k) hs_mem).1
        have hs_norm : ‖(s : CorrectionSeq d) k‖ ≤ ‖(s : CorrectionSeq d)‖ := by
          simpa using correctionSeq_apply_norm_le_norm (s : CorrectionSeq d) k
        have hg_norm : ‖(g : CorrectionSeq d) k‖ ≤ ‖(g : CorrectionSeq d)‖ := by
          simpa using correctionSeq_apply_norm_le_norm (g : CorrectionSeq d) k
        dsimp [f, C]
        calc
          ‖anchorStableProjection hs hx ((k + 1) * N)
                (anchorDerivativeProduct (T := T) hx (k * N) N
                  ((s : CorrectionSeq d) k)) + (g : CorrectionSeq d) k‖ ≤
              ‖anchorStableProjection hs hx ((k + 1) * N)
                (anchorDerivativeProduct (T := T) hx (k * N) N
                  ((s : CorrectionSeq d) k))‖ + ‖(g : CorrectionSeq d) k‖ :=
            norm_add_le _ _
          _ ≤ (1 / 16 : ℝ) * ‖(s : CorrectionSeq d) k‖ +
              ‖(g : CorrectionSeq d) k‖ := by
            exact add_le_add (by simpa [Nat.add_mul] using hendpoint) le_rfl
          _ ≤ (1 / 16 : ℝ) * ‖(s : CorrectionSeq d)‖ +
              ‖(g : CorrectionSeq d)‖ :=
            add_le_add (mul_le_mul_of_nonneg_left hs_norm (by norm_num)) hg_norm
  let u : CorrectionSeq d :=
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete f C hf_bound
  refine ⟨u, ?_⟩
  intro j
  cases j with
  | zero =>
      change (0 : E d) ∈ hs.stable (localTubeAnchorSeq hx (0 * N))
      exact Submodule.zero_mem _
  | succ k =>
      change
        anchorStableProjection hs hx ((k + 1) * N)
              (anchorDerivativeProduct (T := T) hx (k * N) N
                ((s : CorrectionSeq d) k)) + (g : CorrectionSeq d) k ∈
          hs.stable (localTubeAnchorSeq hx ((k + 1) * N))
      exact Submodule.add_mem _ (anchorStableProjection_mem hs hx _ _) (g.property k)

@[simp]
theorem stableBlockStep_zero (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (g : EdgeStableSeq hs hx N) (s : BlockStableSeq hs hx N) :
    (stableBlockStep hs strict g s : CorrectionSeq d) 0 = 0 :=
  rfl

@[simp]
theorem stableBlockStep_succ (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (g : EdgeStableSeq hs hx N) (s : BlockStableSeq hs hx N) (k : ℕ) :
    (stableBlockStep hs strict g s : CorrectionSeq d) (k + 1) =
      anchorStableProjection hs hx ((k + 1) * N)
          (anchorDerivativeProduct (T := T) hx (k * N) N ((s : CorrectionSeq d) k)) +
        (g : CorrectionSeq d) k :=
  rfl

theorem stableBlockStep_contracting (hs : HyperbolicStructure T K)
    {ρ η r M greenBound derivativeBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ} {N : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := (1 / 16 : ℝ)) (derivativeBound := derivativeBound) hx N)
    (g : EdgeStableSeq hs hx N) :
    ContractingWith (1 / 8 : NNReal) (stableBlockStep hs strict g) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro s t
  have hpoint : ∀ j : ℕ,
      ‖(stableBlockStep hs strict g s : CorrectionSeq d) j -
          (stableBlockStep hs strict g t : CorrectionSeq d) j‖ ≤
        (1 / 16 : ℝ) * ‖(s : CorrectionSeq d) - (t : CorrectionSeq d)‖ := by
    intro j
    cases j with
    | zero => simp
    | succ k =>
        have hst_mem : (s : CorrectionSeq d) k - (t : CorrectionSeq d) k ∈
            hs.stable (localTubeAnchorSeq hx (k * N)) :=
          Submodule.sub_mem _ (s.property k) (t.property k)
        have hendpoint := (strict.forward_endpoint_le (k * N)
          ((s : CorrectionSeq d) k - (t : CorrectionSeq d) k) hst_mem).1
        have heval : ‖(s : CorrectionSeq d) k - (t : CorrectionSeq d) k‖ ≤
            ‖(s : CorrectionSeq d) - (t : CorrectionSeq d)‖ := by
          simpa using correctionSeq_apply_norm_le_norm
            ((s : CorrectionSeq d) - (t : CorrectionSeq d)) k
        rw [stableBlockStep_succ, stableBlockStep_succ]
        simp only [add_sub_add_right_eq_sub, ← map_sub]
        have hendpoint' :
            ‖anchorStableProjection hs hx ((k + 1) * N)
                (anchorDerivativeProduct (T := T) hx (k * N) N
                  ((s : CorrectionSeq d) k - (t : CorrectionSeq d) k))‖ ≤
              (1 / 16 : ℝ) * ‖(s : CorrectionSeq d) k - (t : CorrectionSeq d) k‖ := by
          simpa [Nat.add_mul] using hendpoint
        exact hendpoint'.trans
          (mul_le_mul_of_nonneg_left heval (by norm_num))
  have hnorm :
      ‖(stableBlockStep hs strict g s : CorrectionSeq d) -
          (stableBlockStep hs strict g t : CorrectionSeq d)‖ ≤
        (1 / 16 : ℝ) * ‖(s : CorrectionSeq d) - (t : CorrectionSeq d)‖ :=
    correctionSeq_norm_le_of_pointwise (d := d) hpoint
  change
    dist (stableBlockStep hs strict g s : CorrectionSeq d)
        (stableBlockStep hs strict g t : CorrectionSeq d) ≤
      (1 / 8 : ℝ) * dist (s : CorrectionSeq d) (t : CorrectionSeq d)
  simp only [dist_eq_norm]
  exact hnorm.trans (mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _))

end Submission.Shadowing
