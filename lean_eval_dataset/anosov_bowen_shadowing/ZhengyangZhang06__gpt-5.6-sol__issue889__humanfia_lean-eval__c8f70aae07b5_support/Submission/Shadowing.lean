import ChallengeDeps

open LeanEval.Dynamics.HyperbolicShadowingProblem
open scoped Topology
open Filter

namespace Submission.Shadowing

variable {d : ℕ} {T : E d ≃ₜ E d} {K : Set (E d)}

theorem forward_mem (hs : HyperbolicStructure T K) {x : E d} (hx : x ∈ K) :
    T x ∈ K := by
  rw [← hs.invariant]
  exact ⟨x, hx, rfl⟩

theorem backward_mem (hs : HyperbolicStructure T K) {x : E d} (hx : x ∈ K) :
    T.symm x ∈ K := by
  have hx_image : x ∈ (T : E d → E d) '' K := by
    rw [hs.invariant]
    exact hx
  rcases hx_image with ⟨y, hy, hyx⟩
  have hsymm : T.symm x = y := by
    rw [← hyx]
    simp
  simpa [hsymm] using hy

theorem forward_iterate_mem (hs : HyperbolicStructure T K) {x : E d} (hx : x ∈ K) :
    ∀ n : ℕ, ((T : E d → E d)^[n]) x ∈ K := by
  intro n
  induction n with
  | zero =>
      simpa using hx
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using forward_mem hs ih

theorem backward_iterate_mem (hs : HyperbolicStructure T K) {x : E d} (hx : x ∈ K) :
    ∀ n : ℕ, ((T.symm : E d → E d)^[n]) x ∈ K := by
  intro n
  induction n with
  | zero =>
      simpa using hx
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using backward_mem hs ih

theorem stable_fderiv_mem (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.stable x) :
    fderiv ℝ (T : E d → E d) x v ∈ hs.stable (T x) := by
  have hmem :
      fderiv ℝ (T : E d → E d) x v ∈
        (hs.stable x).map (fderiv ℝ (T : E d → E d) x : E d →ₗ[ℝ] E d) :=
    ⟨v, hv, rfl⟩
  simpa [hs.stable_invariant x hx] using hmem

theorem unstable_fderiv_mem (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.unstable x) :
    fderiv ℝ (T : E d → E d) x v ∈ hs.unstable (T x) := by
  have hmem :
      fderiv ℝ (T : E d → E d) x v ∈
        (hs.unstable x).map (fderiv ℝ (T : E d → E d) x : E d →ₗ[ℝ] E d) :=
    ⟨v, hv, rfl⟩
  simpa [hs.unstable_invariant x hx] using hmem

noncomputable def stableProjection (hs : HyperbolicStructure T K) (x : E d) (hx : x ∈ K) :
    E d →ₗ[ℝ] E d :=
  (hs.stable x).projection (hs.unstable x) (hs.isCompl_stable_unstable x hx)

noncomputable def unstableProjection (hs : HyperbolicStructure T K) (x : E d) (hx : x ∈ K) :
    E d →ₗ[ℝ] E d :=
  (hs.unstable x).projection (hs.stable x) (hs.isCompl_stable_unstable x hx).symm

@[simp]
theorem stableProjection_mem (hs : HyperbolicStructure T K) {x : E d} (hx : x ∈ K)
    (v : E d) :
    stableProjection hs x hx v ∈ hs.stable x := by
  simp [stableProjection]

@[simp]
theorem unstableProjection_mem (hs : HyperbolicStructure T K) {x : E d} (hx : x ∈ K)
    (v : E d) :
    unstableProjection hs x hx v ∈ hs.unstable x := by
  simp [unstableProjection]

theorem stable_add_unstable_projection (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) (v : E d) :
    stableProjection hs x hx v + unstableProjection hs x hx v = v := by
  simpa [stableProjection, unstableProjection] using
    Submodule.projection_add_projection_eq_self (hs.isCompl_stable_unstable x hx) v

@[simp]
theorem stableProjection_apply_of_mem_stable (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.stable x) :
    stableProjection hs x hx v = v := by
  simpa [stableProjection] using
    Submodule.projection_apply_of_mem_left (hs.isCompl_stable_unstable x hx) hv

@[simp]
theorem stableProjection_apply_of_mem_unstable (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.unstable x) :
    stableProjection hs x hx v = 0 := by
  simpa [stableProjection] using
    Submodule.projection_apply_of_mem_right (hs.isCompl_stable_unstable x hx) hv

@[simp]
theorem unstableProjection_apply_of_mem_unstable (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.unstable x) :
    unstableProjection hs x hx v = v := by
  simpa [unstableProjection] using
    Submodule.projection_apply_of_mem_left (hs.isCompl_stable_unstable x hx).symm hv

@[simp]
theorem unstableProjection_apply_of_mem_stable (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.stable x) :
    unstableProjection hs x hx v = 0 := by
  simpa [unstableProjection] using
    Submodule.projection_apply_of_mem_right (hs.isCompl_stable_unstable x hx).symm hv

theorem stableProjection_range (hs : HyperbolicStructure T K) {x : E d} (hx : x ∈ K) :
    (stableProjection hs x hx).range = hs.stable x := by
  simp [stableProjection, Submodule.range_projection (hs.isCompl_stable_unstable x hx)]

theorem unstableProjection_range (hs : HyperbolicStructure T K) {x : E d} (hx : x ∈ K) :
    (unstableProjection hs x hx).range = hs.unstable x := by
  simp [unstableProjection, Submodule.range_projection (hs.isCompl_stable_unstable x hx).symm]

theorem stableProjection_pointwise_bound (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : E d, ‖stableProjection hs x hx v‖ ≤ M * ‖v‖ := by
  let L : E d →L[ℝ] E d := LinearMap.toContinuousLinearMap (stableProjection hs x hx)
  refine ⟨‖L‖, ContinuousLinearMap.opNorm_nonneg L, ?_⟩
  intro v
  simpa [L] using L.le_opNorm v

theorem unstableProjection_pointwise_bound (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : E d, ‖unstableProjection hs x hx v‖ ≤ M * ‖v‖ := by
  let L : E d →L[ℝ] E d := LinearMap.toContinuousLinearMap (unstableProjection hs x hx)
  refine ⟨‖L‖, ContinuousLinearMap.opNorm_nonneg L, ?_⟩
  intro v
  simpa [L] using L.le_opNorm v

def PointwiseProjectionBounds (hs : HyperbolicStructure T K) : Prop :=
  ∀ x : E d, ∀ hx : x ∈ K, ∃ M : ℝ, 0 < M ∧
    ∀ v : E d,
      ‖stableProjection hs x hx v‖ ≤ M * ‖v‖ ∧
      ‖unstableProjection hs x hx v‖ ≤ M * ‖v‖

theorem pointwiseProjectionBounds (hs : HyperbolicStructure T K) :
    PointwiseProjectionBounds hs := by
  intro x hx
  rcases stableProjection_pointwise_bound hs hx with ⟨Ms, _hMs_nonneg, hMs_bound⟩
  rcases unstableProjection_pointwise_bound hs hx with ⟨Mu, _hMu_nonneg, hMu_bound⟩
  let M : ℝ := max (max Ms Mu) 1
  refine ⟨M, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right (max Ms Mu) 1)
  · intro v
    constructor
    · exact (hMs_bound v).trans (mul_le_mul_of_nonneg_right
        ((le_max_left Ms Mu).trans (le_max_left (max Ms Mu) 1)) (norm_nonneg v))
    · exact (hMu_bound v).trans (mul_le_mul_of_nonneg_right
        ((le_max_right Ms Mu).trans (le_max_left (max Ms Mu) 1)) (norm_nonneg v))

theorem contDiff_iterate {f : E d → E d} (hf : ContDiff ℝ 1 f) :
    ∀ n : ℕ, ContDiff ℝ 1 (f^[n]) := by
  intro n
  induction n with
  | zero =>
      simpa [Function.iterate_zero] using (contDiff_id : ContDiff ℝ 1 (id : E d → E d))
  | succ n ih =>
      simpa [Function.iterate_succ] using ih.comp hf

theorem fderiv_iterate_succ_apply (hs : HyperbolicStructure T K)
    (n : ℕ) (x v : E d) :
    fderiv ℝ ((T : E d → E d)^[n + 1]) x v =
      fderiv ℝ (T : E d → E d) (((T : E d → E d)^[n]) x)
        (fderiv ℝ ((T : E d → E d)^[n]) x v) := by
  have hT_diff : DifferentiableAt ℝ (T : E d → E d) (((T : E d → E d)^[n]) x) :=
    (hs.contDiff_fwd.differentiable (by norm_num)).differentiableAt
  have hiter_diff : DifferentiableAt ℝ ((T : E d → E d)^[n]) x :=
    ((contDiff_iterate hs.contDiff_fwd n).differentiable (by norm_num)).differentiableAt
  have hcomp :
      fderiv ℝ ((T : E d → E d) ∘ ((T : E d → E d)^[n])) x v =
        fderiv ℝ (T : E d → E d) (((T : E d → E d)^[n]) x)
          (fderiv ℝ ((T : E d → E d)^[n]) x v) := by
    simpa using congrArg (fun L : E d →L[ℝ] E d => L v)
      (fderiv_comp (𝕜 := ℝ) (f := ((T : E d → E d)^[n]))
        (g := (T : E d → E d)) x hT_diff hiter_diff)
  rw [Function.iterate_succ']
  exact hcomp

theorem iterate_apply_self_comm_aux {α : Type*} (f : α → α) :
    ∀ n : ℕ, ∀ x : α, (f^[n]) (f x) = f ((f^[n]) x) := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      exact ih (f x)

theorem fderiv_symm_iterate_succ_forward_apply (hs : HyperbolicStructure T K)
    (n : ℕ) (x v : E d) :
    fderiv ℝ ((T.symm : E d → E d)^[n + 1])
        (((T : E d → E d)^[n + 1]) x) v =
      fderiv ℝ ((T.symm : E d → E d)^[n]) (((T : E d → E d)^[n]) x)
        (fderiv ℝ (T.symm : E d → E d) (((T : E d → E d)^[n + 1]) x) v) := by
  have hbwd_diff :
      DifferentiableAt ℝ (T.symm : E d → E d) (((T : E d → E d)^[n + 1]) x) :=
    (hs.contDiff_bwd.differentiable (by norm_num)).differentiableAt
  have hiter_diff :
      DifferentiableAt ℝ ((T.symm : E d → E d)^[n])
        (T.symm (((T : E d → E d)^[n + 1]) x)) :=
    ((contDiff_iterate hs.contDiff_bwd n).differentiable (by norm_num)).differentiableAt
  have hbase' :
      T.symm (((T : E d → E d)^[n]) (T x)) = ((T : E d → E d)^[n]) x := by
    have hcomm :
        ((T : E d → E d)^[n]) (T x) =
          T (((T : E d → E d)^[n]) x) := by
      exact iterate_apply_self_comm_aux (T : E d → E d) n x
    rw [hcomm]
    simp
  have hbase :
      T.symm (((T : E d → E d)^[n + 1]) x) = ((T : E d → E d)^[n]) x := by
    simpa [Function.iterate_succ_apply] using hbase'
  have hcomp :
      fderiv ℝ (((T.symm : E d → E d)^[n]) ∘ (T.symm : E d → E d))
          (((T : E d → E d)^[n + 1]) x) v =
        fderiv ℝ ((T.symm : E d → E d)^[n])
          (T.symm (((T : E d → E d)^[n + 1]) x))
          (fderiv ℝ (T.symm : E d → E d) (((T : E d → E d)^[n + 1]) x) v) := by
    simpa using congrArg (fun L : E d →L[ℝ] E d => L v)
      (fderiv_comp (𝕜 := ℝ) (f := (T.symm : E d → E d))
        (g := ((T.symm : E d → E d)^[n])) (((T : E d → E d)^[n + 1]) x)
        hiter_diff hbwd_diff)
  rw [Function.iterate_succ]
  simpa [Function.iterate_succ_apply, hbase'] using hcomp

theorem iterate_apply_self_comm {α : Type*} (f : α → α) :
    ∀ n : ℕ, ∀ x : α, (f^[n]) (f x) = f ((f^[n]) x) := by
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      exact ih (f x)

theorem backward_forward_iterate_apply (T : E d ≃ₜ E d) :
    ∀ N : ℕ, ∀ x : E d,
      ((T.symm : E d → E d)^[N]) (((T : E d → E d)^[N]) x) = x := by
  intro N
  induction N with
  | zero =>
      intro x
      simp [Function.iterate_zero]
  | succ N ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
      simp [ih]

theorem forward_backward_iterate_apply (T : E d ≃ₜ E d) :
    ∀ N : ℕ, ∀ x : E d,
      ((T : E d → E d)^[N]) (((T.symm : E d → E d)^[N]) x) = x := by
  intro N
  induction N with
  | zero =>
      intro x
      simp [Function.iterate_zero]
  | succ N ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
      simp [ih]

theorem fderiv_backward_forward_iterate_apply (hs : HyperbolicStructure T K)
    (N : ℕ) (x v : E d) :
    fderiv ℝ ((T.symm : E d → E d)^[N]) (((T : E d → E d)^[N]) x)
      (fderiv ℝ ((T : E d → E d)^[N]) x v) = v := by
  have hbwd_diff :
      DifferentiableAt ℝ ((T.symm : E d → E d)^[N])
        (((T : E d → E d)^[N]) x) :=
    ((contDiff_iterate hs.contDiff_bwd N).differentiable (by norm_num)).differentiableAt
  have hfwd_diff : DifferentiableAt ℝ ((T : E d → E d)^[N]) x :=
    ((contDiff_iterate hs.contDiff_fwd N).differentiable (by norm_num)).differentiableAt
  have hcomp :
      fderiv ℝ (((T.symm : E d → E d)^[N]) ∘ ((T : E d → E d)^[N])) x v =
        fderiv ℝ ((T.symm : E d → E d)^[N]) (((T : E d → E d)^[N]) x)
          (fderiv ℝ ((T : E d → E d)^[N]) x v) := by
    simpa using congrArg (fun L : E d →L[ℝ] E d => L v)
      (fderiv_comp (𝕜 := ℝ) (f := ((T : E d → E d)^[N]))
        (g := ((T.symm : E d → E d)^[N])) x hbwd_diff hfwd_diff)
  have hfun :
      ((T.symm : E d → E d)^[N]) ∘ ((T : E d → E d)^[N]) = id := by
    funext y
    exact backward_forward_iterate_apply T N y
  have hid :
      fderiv ℝ (((T.symm : E d → E d)^[N]) ∘ ((T : E d → E d)^[N])) x v = v := by
    rw [hfun, fderiv_id]
    rfl
  rw [← hcomp]
  exact hid

theorem fderiv_forward_backward_iterate_apply (hs : HyperbolicStructure T K)
    (N : ℕ) (x v : E d) :
    fderiv ℝ ((T : E d → E d)^[N]) (((T.symm : E d → E d)^[N]) x)
      (fderiv ℝ ((T.symm : E d → E d)^[N]) x v) = v := by
  have hfwd_diff :
      DifferentiableAt ℝ ((T : E d → E d)^[N])
        (((T.symm : E d → E d)^[N]) x) :=
    ((contDiff_iterate hs.contDiff_fwd N).differentiable (by norm_num)).differentiableAt
  have hbwd_diff : DifferentiableAt ℝ ((T.symm : E d → E d)^[N]) x :=
    ((contDiff_iterate hs.contDiff_bwd N).differentiable (by norm_num)).differentiableAt
  have hcomp :
      fderiv ℝ (((T : E d → E d)^[N]) ∘ ((T.symm : E d → E d)^[N])) x v =
        fderiv ℝ ((T : E d → E d)^[N]) (((T.symm : E d → E d)^[N]) x)
          (fderiv ℝ ((T.symm : E d → E d)^[N]) x v) := by
    simpa using congrArg (fun L : E d →L[ℝ] E d => L v)
      (fderiv_comp (𝕜 := ℝ) (f := ((T.symm : E d → E d)^[N]))
        (g := ((T : E d → E d)^[N])) x hfwd_diff hbwd_diff)
  have hfun :
      ((T : E d → E d)^[N]) ∘ ((T.symm : E d → E d)^[N]) = id := by
    funext y
    exact forward_backward_iterate_apply T N y
  have hid :
      fderiv ℝ (((T : E d → E d)^[N]) ∘ ((T.symm : E d → E d)^[N])) x v = v := by
    rw [hfun, fderiv_id]
    rfl
  rw [← hcomp]
  exact hid

theorem stable_fderiv_iterate_mem (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.stable x) :
    ∀ n : ℕ, fderiv ℝ ((T : E d → E d)^[n]) x v ∈
      hs.stable (((T : E d → E d)^[n]) x) := by
  intro n
  induction n with
  | zero =>
      simpa [Function.iterate_zero, fderiv_id] using hv
  | succ n ih =>
      have hx_n : ((T : E d → E d)^[n]) x ∈ K := forward_iterate_mem hs hx n
      have hTdiff :
          DifferentiableAt ℝ (T : E d → E d) (((T : E d → E d)^[n]) x) :=
        (hs.contDiff_fwd.differentiable (by norm_num)).differentiableAt
      have hIterdiff : DifferentiableAt ℝ ((T : E d → E d)^[n]) x :=
        ((contDiff_iterate hs.contDiff_fwd n).differentiable (by norm_num)).differentiableAt
      have hEq :
          fderiv ℝ ((T : E d → E d) ∘ ((T : E d → E d)^[n])) x v =
            fderiv ℝ (T : E d → E d) (((T : E d → E d)^[n]) x)
              (fderiv ℝ ((T : E d → E d)^[n]) x v) := by
        simpa using congrArg (fun L : E d →L[ℝ] E d => L v)
          (fderiv_comp (𝕜 := ℝ) (f := ((T : E d → E d)^[n]))
            (g := (T : E d → E d)) x hTdiff hIterdiff)
      rw [Function.iterate_succ']
      rw [hEq]
      exact stable_fderiv_mem hs hx_n ih

theorem unstable_fderiv_iterate_mem (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.unstable x) :
    ∀ n : ℕ, fderiv ℝ ((T : E d → E d)^[n]) x v ∈
      hs.unstable (((T : E d → E d)^[n]) x) := by
  intro n
  induction n with
  | zero =>
      simpa [Function.iterate_zero, fderiv_id] using hv
  | succ n ih =>
      have hx_n : ((T : E d → E d)^[n]) x ∈ K := forward_iterate_mem hs hx n
      have hTdiff :
          DifferentiableAt ℝ (T : E d → E d) (((T : E d → E d)^[n]) x) :=
        (hs.contDiff_fwd.differentiable (by norm_num)).differentiableAt
      have hIterdiff : DifferentiableAt ℝ ((T : E d → E d)^[n]) x :=
        ((contDiff_iterate hs.contDiff_fwd n).differentiable (by norm_num)).differentiableAt
      have hEq :
          fderiv ℝ ((T : E d → E d) ∘ ((T : E d → E d)^[n])) x v =
            fderiv ℝ (T : E d → E d) (((T : E d → E d)^[n]) x)
              (fderiv ℝ ((T : E d → E d)^[n]) x v) := by
        simpa using congrArg (fun L : E d →L[ℝ] E d => L v)
          (fderiv_comp (𝕜 := ℝ) (f := ((T : E d → E d)^[n]))
            (g := (T : E d → E d)) x hTdiff hIterdiff)
      rw [Function.iterate_succ']
      rw [hEq]
      exact unstable_fderiv_mem hs hx_n ih

theorem stable_fderiv_symm_mem (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.stable x) :
    fderiv ℝ (T.symm : E d → E d) x v ∈ hs.stable (T.symm x) := by
  have hsymm_mem : T.symm x ∈ K := backward_mem hs hx
  have hmap :
      (hs.stable (T.symm x)).map
          (fderiv ℝ (T : E d → E d) (T.symm x) : E d →ₗ[ℝ] E d) =
        hs.stable (T (T.symm x)) :=
    hs.stable_invariant (T.symm x) hsymm_mem
  have hv_image :
      v ∈ (hs.stable (T.symm x)).map
          (fderiv ℝ (T : E d → E d) (T.symm x) : E d →ₗ[ℝ] E d) := by
    rw [hmap]
    simpa using hv
  rcases hv_image with ⟨w, hw, hw_eq⟩
  have hleft :
      fderiv ℝ (T.symm : E d → E d) x v = w := by
    have hid :=
      fderiv_backward_forward_iterate_apply (T := T) (K := K) hs 1 (T.symm x) w
    have hid' :
        fderiv ℝ (T.symm : E d → E d) (T (T.symm x))
            (fderiv ℝ (T : E d → E d) (T.symm x) w) = w := by
      simpa [Function.iterate_one] using hid
    have hw_eq' : fderiv ℝ (T : E d → E d) (T.symm x) w = v := by
      exact hw_eq
    rw [hw_eq'] at hid'
    simpa using hid'
  rw [hleft]
  exact hw

theorem unstable_fderiv_symm_mem (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.unstable x) :
    fderiv ℝ (T.symm : E d → E d) x v ∈ hs.unstable (T.symm x) := by
  have hsymm_mem : T.symm x ∈ K := backward_mem hs hx
  have hmap :
      (hs.unstable (T.symm x)).map
          (fderiv ℝ (T : E d → E d) (T.symm x) : E d →ₗ[ℝ] E d) =
        hs.unstable (T (T.symm x)) :=
    hs.unstable_invariant (T.symm x) hsymm_mem
  have hv_image :
      v ∈ (hs.unstable (T.symm x)).map
          (fderiv ℝ (T : E d → E d) (T.symm x) : E d →ₗ[ℝ] E d) := by
    rw [hmap]
    simpa using hv
  rcases hv_image with ⟨w, hw, hw_eq⟩
  have hleft :
      fderiv ℝ (T.symm : E d → E d) x v = w := by
    have hid :=
      fderiv_backward_forward_iterate_apply (T := T) (K := K) hs 1 (T.symm x) w
    have hid' :
        fderiv ℝ (T.symm : E d → E d) (T (T.symm x))
            (fderiv ℝ (T : E d → E d) (T.symm x) w) = w := by
      simpa [Function.iterate_one] using hid
    have hw_eq' : fderiv ℝ (T : E d → E d) (T.symm x) w = v := by
      exact hw_eq
    rw [hw_eq'] at hid'
    simpa using hid'
  rw [hleft]
  exact hw

theorem stable_fderiv_symm_iterate_mem (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.stable x) :
    ∀ n : ℕ, fderiv ℝ ((T.symm : E d → E d)^[n]) x v ∈
      hs.stable (((T.symm : E d → E d)^[n]) x) := by
  intro n
  induction n with
  | zero =>
      simpa [Function.iterate_zero, fderiv_id] using hv
  | succ n ih =>
      have hx_n : ((T.symm : E d → E d)^[n]) x ∈ K := backward_iterate_mem hs hx n
      have hTdiff :
          DifferentiableAt ℝ (T.symm : E d → E d)
            (((T.symm : E d → E d)^[n]) x) :=
        (hs.contDiff_bwd.differentiable (by norm_num)).differentiableAt
      have hIterdiff : DifferentiableAt ℝ ((T.symm : E d → E d)^[n]) x :=
        ((contDiff_iterate hs.contDiff_bwd n).differentiable (by norm_num)).differentiableAt
      have hEq :
          fderiv ℝ ((T.symm : E d → E d) ∘ ((T.symm : E d → E d)^[n])) x v =
            fderiv ℝ (T.symm : E d → E d) (((T.symm : E d → E d)^[n]) x)
              (fderiv ℝ ((T.symm : E d → E d)^[n]) x v) := by
        simpa using congrArg (fun L : E d →L[ℝ] E d => L v)
          (fderiv_comp (𝕜 := ℝ) (f := ((T.symm : E d → E d)^[n]))
            (g := (T.symm : E d → E d)) x hTdiff hIterdiff)
      rw [Function.iterate_succ']
      rw [hEq]
      exact stable_fderiv_symm_mem hs hx_n ih

theorem unstable_fderiv_symm_iterate_mem (hs : HyperbolicStructure T K) {x : E d}
    (hx : x ∈ K) {v : E d} (hv : v ∈ hs.unstable x) :
    ∀ n : ℕ, fderiv ℝ ((T.symm : E d → E d)^[n]) x v ∈
      hs.unstable (((T.symm : E d → E d)^[n]) x) := by
  intro n
  induction n with
  | zero =>
      simpa [Function.iterate_zero, fderiv_id] using hv
  | succ n ih =>
      have hx_n : ((T.symm : E d → E d)^[n]) x ∈ K := backward_iterate_mem hs hx n
      have hTdiff :
          DifferentiableAt ℝ (T.symm : E d → E d)
            (((T.symm : E d → E d)^[n]) x) :=
        (hs.contDiff_bwd.differentiable (by norm_num)).differentiableAt
      have hIterdiff : DifferentiableAt ℝ ((T.symm : E d → E d)^[n]) x :=
        ((contDiff_iterate hs.contDiff_bwd n).differentiable (by norm_num)).differentiableAt
      have hEq :
          fderiv ℝ ((T.symm : E d → E d) ∘ ((T.symm : E d → E d)^[n])) x v =
            fderiv ℝ (T.symm : E d → E d) (((T.symm : E d → E d)^[n]) x)
              (fderiv ℝ ((T.symm : E d → E d)^[n]) x v) := by
        simpa using congrArg (fun L : E d →L[ℝ] E d => L v)
          (fderiv_comp (𝕜 := ℝ) (f := ((T.symm : E d → E d)^[n]))
            (g := (T.symm : E d → E d)) x hTdiff hIterdiff)
      rw [Function.iterate_succ']
      rw [hEq]
      exact unstable_fderiv_symm_mem hs hx_n ih

theorem exists_small_hyperbolic_iterate (hs : HyperbolicStructure T K) {η : ℝ}
    (hη : 0 < η) :
    ∃ N : ℕ, hs.const * hs.rate ^ N < η := by
  have htend :
      Filter.Tendsto (fun N : ℕ => hs.const * hs.rate ^ N) atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hs.rate_pos.le hs.rate_lt_one).const_mul
        hs.const
  have h_event :
      ∀ᶠ N : ℕ in atTop, hs.const * hs.rate ^ N ∈ Set.Iio η :=
    htend.eventually (isOpen_Iio.mem_nhds hη)
  rcases (Filter.eventually_atTop.1 h_event) with ⟨N, hN⟩
  exact ⟨N, hN N le_rfl⟩

theorem exists_positive_small_hyperbolic_iterate (hs : HyperbolicStructure T K)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ hs.const * hs.rate ^ N < η := by
  rcases exists_small_hyperbolic_iterate hs hη with ⟨N, hN⟩
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  calc
    hs.const * hs.rate ^ (N + 1) = (hs.const * hs.rate ^ N) * hs.rate := by
      rw [pow_succ]
      ring
    _ < η * hs.rate := mul_lt_mul_of_pos_right hN hs.rate_pos
    _ < η := by
      nlinarith [hη, hs.rate_pos, hs.rate_lt_one]

def FiniteTimeDerivativeBounds (T : E d ≃ₜ E d) (K : Set (E d))
    (_hKc : IsCompact K) (_hs : HyperbolicStructure T K) (N : ℕ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ x : E d, x ∈ K →
    ‖fderiv ℝ ((T : E d → E d)^[N]) x‖ ≤ B ∧
    ‖fderiv ℝ ((T.symm : E d → E d)^[N]) x‖ ≤ B

theorem finiteTimeDerivativeBounds (hKc : IsCompact K) (hs : HyperbolicStructure T K)
    (N : ℕ) :
    FiniteTimeDerivativeBounds T K hKc hs N := by
  have hfwd_cont : Continuous (fun x : E d => fderiv ℝ ((T : E d → E d)^[N]) x) :=
    (contDiff_iterate hs.contDiff_fwd N).continuous_fderiv (by norm_num)
  have hbwd_cont : Continuous (fun x : E d => fderiv ℝ ((T.symm : E d → E d)^[N]) x) :=
    (contDiff_iterate hs.contDiff_bwd N).continuous_fderiv (by norm_num)
  rcases hKc.exists_bound_of_continuousOn hfwd_cont.continuousOn with ⟨Bf, hBf⟩
  rcases hKc.exists_bound_of_continuousOn hbwd_cont.continuousOn with ⟨Bb, hBb⟩
  refine ⟨max (max Bf Bb) 0, le_max_right (max Bf Bb) 0, ?_⟩
  intro x hx
  constructor
  · exact (hBf x hx).trans ((le_max_left Bf Bb).trans (le_max_left (max Bf Bb) 0))
  · exact (hBb x hx).trans ((le_max_right Bf Bb).trans (le_max_left (max Bf Bb) 0))

def UniformProjectionBounds (T : E d ≃ₜ E d) (K : Set (E d))
    (_hKc : IsCompact K) (_hKne : K.Nonempty) (hs : HyperbolicStructure T K) : Prop :=
  ∃ M : ℝ, 0 < M ∧
    ∀ x : E d, ∀ hx : x ∈ K, ∀ v : E d,
      ‖stableProjection hs x hx v‖ ≤ M * ‖v‖ ∧
      ‖unstableProjection hs x hx v‖ ≤ M * ‖v‖

theorem uniformProjectionBounds (hKc : IsCompact K) (hKne : K.Nonempty)
    (hs : HyperbolicStructure T K) :
    UniformProjectionBounds T K hKc hKne hs := by
  rcases exists_small_hyperbolic_iterate hs (by norm_num : (0 : ℝ) < 1 / 2) with
    ⟨N, hNsmall⟩
  let a : ℝ := hs.const * hs.rate ^ N
  have ha_pos : 0 < a := by
    exact mul_pos hs.const_pos (pow_pos hs.rate_pos N)
  have ha_lt_half : a < 1 / 2 := by
    simpa [a] using hNsmall
  rcases finiteTimeDerivativeBounds hKc hs N with ⟨B, hB_nonneg, hB⟩
  let M : ℝ := max (2 * B + 3) 1
  refine ⟨M, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right (2 * B + 3) 1)
  · intro x hx v
    let A : E d →L[ℝ] E d := fderiv ℝ ((T : E d → E d)^[N]) x
    let vs : E d := stableProjection hs x hx v
    let vu : E d := unstableProjection hs x hx v
    have hA_norm : ‖A‖ ≤ B := (hB x hx).1
    have hAv : ‖A v‖ ≤ B * ‖v‖ :=
      (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA_norm (norm_nonneg v))
    have hvs_mem : vs ∈ hs.stable x := by
      simp [vs]
    have hvu_mem : vu ∈ hs.unstable x := by
      simp [vu]
    have hstable_contract : ‖A vs‖ ≤ a * ‖vs‖ := by
      simpa [A, a] using hs.contract_stable x hx vs hvs_mem N
    have hxN : ((T : E d → E d)^[N]) x ∈ K := forward_iterate_mem hs hx N
    have hAu_mem :
        A vu ∈ hs.unstable (((T : E d → E d)^[N]) x) := by
      simpa [A, vu] using unstable_fderiv_iterate_mem hs hx hvu_mem N
    have hunstable_contract :
        ‖fderiv ℝ ((T.symm : E d → E d)^[N]) (((T : E d → E d)^[N]) x)
            (A vu)‖ ≤ a * ‖A vu‖ := by
      simpa [A, a] using hs.contract_unstable (((T : E d → E d)^[N]) x) hxN
        (A vu) hAu_mem N
    have hinv : fderiv ℝ ((T.symm : E d → E d)^[N]) (((T : E d → E d)^[N]) x)
        (A vu) = vu := by
      simpa [A] using fderiv_backward_forward_iterate_apply hs N x vu
    have hu_lower : ‖vu‖ ≤ a * ‖A vu‖ := by
      simpa [hinv] using hunstable_contract
    have hdecomp : vs + vu = v := by
      simpa [vs, vu] using stable_add_unstable_projection hs hx v
    have hvu_eq : vu = v - vs := by
      rw [← hdecomp]
      abel
    have hvs_eq : vs = v - vu := by
      rw [← hdecomp]
      abel
    have hA_vu : ‖A vu‖ ≤ ‖A v‖ + ‖A vs‖ := by
      calc
        ‖A vu‖ = ‖A (v - vs)‖ := by rw [hvu_eq]
        _ = ‖A v - A vs‖ := by simp [map_sub]
        _ ≤ ‖A v‖ + ‖A vs‖ := norm_sub_le (A v) (A vs)
    have hA_vu_bound : ‖A vu‖ ≤ B * ‖v‖ + a * ‖vs‖ :=
      hA_vu.trans (add_le_add hAv hstable_contract)
    have hu_ineq : ‖vu‖ ≤ a * (B * ‖v‖ + a * ‖vs‖) :=
      hu_lower.trans (mul_le_mul_of_nonneg_left hA_vu_bound ha_pos.le)
    have hs_ineq : ‖vs‖ ≤ ‖v‖ + ‖vu‖ := by
      calc
        ‖vs‖ = ‖v - vu‖ := by rw [hvs_eq]
        _ ≤ ‖v‖ + ‖vu‖ := norm_sub_le v vu
    have ha_sq_le : a * a ≤ 1 / 4 := by
      nlinarith [ha_pos.le, ha_lt_half]
    have ha_le_one : a ≤ 1 := by
      nlinarith [ha_pos.le, ha_lt_half]
    have hu_step : ‖vu‖ ≤ (B + 1) * ‖v‖ + (1 / 4) * ‖vu‖ := by
      calc
        ‖vu‖ ≤ a * (B * ‖v‖ + a * ‖vs‖) := hu_ineq
        _ ≤ a * (B * ‖v‖ + a * (‖v‖ + ‖vu‖)) := by
          gcongr
        _ = a * B * ‖v‖ + a * a * ‖v‖ + a * a * ‖vu‖ := by ring
        _ ≤ B * ‖v‖ + 1 * ‖v‖ + (1 / 4) * ‖vu‖ := by
          have hterm1 : a * B * ‖v‖ ≤ B * ‖v‖ := by
            calc
              a * B * ‖v‖ = a * (B * ‖v‖) := by ring
              _ ≤ 1 * (B * ‖v‖) :=
                mul_le_mul_of_nonneg_right ha_le_one
                  (mul_nonneg hB_nonneg (norm_nonneg v))
              _ = B * ‖v‖ := by ring
          have hterm2 : a * a * ‖v‖ ≤ 1 * ‖v‖ := by
            have ha_sq_le_one : a * a ≤ 1 := by nlinarith [ha_sq_le]
            calc
              a * a * ‖v‖ = (a * a) * ‖v‖ := by ring
              _ ≤ 1 * ‖v‖ :=
                mul_le_mul_of_nonneg_right ha_sq_le_one (norm_nonneg v)
          have hterm3 : a * a * ‖vu‖ ≤ (1 / 4) * ‖vu‖ := by
            calc
              a * a * ‖vu‖ = (a * a) * ‖vu‖ := by ring
              _ ≤ (1 / 4) * ‖vu‖ :=
                mul_le_mul_of_nonneg_right ha_sq_le (norm_nonneg vu)
          exact add_le_add (add_le_add hterm1 hterm2) hterm3
        _ = (B + 1) * ‖v‖ + (1 / 4) * ‖vu‖ := by ring
    have hu_bound : ‖vu‖ ≤ (2 * (B + 1)) * ‖v‖ := by
      nlinarith [hu_step, hB_nonneg, norm_nonneg v, norm_nonneg vu]
    have hs_bound : ‖vs‖ ≤ (2 * B + 3) * ‖v‖ := by
      nlinarith [hs_ineq, hu_bound, hB_nonneg, norm_nonneg v]
    have hM_stable : 2 * B + 3 ≤ M := le_max_left (2 * B + 3) 1
    have hM_unstable : 2 * (B + 1) ≤ M := by
      dsimp [M]
      nlinarith [le_max_left (2 * B + 3) 1]
    constructor
    · exact hs_bound.trans (mul_le_mul_of_nonneg_right hM_stable (norm_nonneg v))
    · exact hu_bound.trans (mul_le_mul_of_nonneg_right hM_unstable (norm_nonneg v))

theorem unstableProjection_of_stable_nearby_bound (hs : HyperbolicStructure T K)
    {x y v : E d} (hx : x ∈ K) (hy : y ∈ K) {N : ℕ} {ζ : ℝ}
    (hsmall : hs.const * hs.rate ^ N < 1 / 2)
    (hderiv_close :
      ‖fderiv ℝ ((T : E d → E d)^[N]) y -
          fderiv ℝ ((T : E d → E d)^[N]) x‖ ≤ ζ)
    (hζ_nonneg : 0 ≤ ζ) (hv : v ∈ hs.stable x) :
    ‖unstableProjection hs y hy v‖ ≤
      2 * (hs.const * hs.rate ^ N) *
        (2 * (hs.const * hs.rate ^ N) + ζ) * ‖v‖ := by
  let a : ℝ := hs.const * hs.rate ^ N
  let Ax : E d →L[ℝ] E d := fderiv ℝ ((T : E d → E d)^[N]) x
  let Ay : E d →L[ℝ] E d := fderiv ℝ ((T : E d → E d)^[N]) y
  let vs : E d := stableProjection hs y hy v
  let vu : E d := unstableProjection hs y hy v
  have ha_pos : 0 < a := by
    dsimp [a]
    exact mul_pos hs.const_pos (pow_pos hs.rate_pos N)
  have ha_small : a < 1 / 2 := by
    simpa [a] using hsmall
  have hAy_v : ‖Ay v‖ ≤ (a + ζ) * ‖v‖ := by
    have hAx_v : ‖Ax v‖ ≤ a * ‖v‖ := by
      simpa [Ax, a] using hs.contract_stable x hx v hv N
    have hdiff_v : ‖(Ay - Ax) v‖ ≤ ζ * ‖v‖ := by
      calc
        ‖(Ay - Ax) v‖ ≤ ‖Ay - Ax‖ * ‖v‖ := (Ay - Ax).le_opNorm v
        _ ≤ ζ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (by simpa [Ay, Ax] using hderiv_close)
            (norm_nonneg v)
    have hdecomp : Ay v = Ax v + (Ay - Ax) v := by
      simp only [sub_apply]
      abel
    calc
      ‖Ay v‖ = ‖Ax v + (Ay - Ax) v‖ := by rw [hdecomp]
      _ ≤ ‖Ax v‖ + ‖(Ay - Ax) v‖ := norm_add_le (Ax v) ((Ay - Ax) v)
      _ ≤ a * ‖v‖ + ζ * ‖v‖ := add_le_add hAx_v hdiff_v
      _ = (a + ζ) * ‖v‖ := by ring
  have hvs_mem : vs ∈ hs.stable y := by
    simp [vs]
  have hvu_mem : vu ∈ hs.unstable y := by
    simp [vu]
  have hstable_contract : ‖Ay vs‖ ≤ a * ‖vs‖ := by
    simpa [Ay, a] using hs.contract_stable y hy vs hvs_mem N
  have hyN : ((T : E d → E d)^[N]) y ∈ K := forward_iterate_mem hs hy N
  have hAu_mem :
      Ay vu ∈ hs.unstable (((T : E d → E d)^[N]) y) := by
    simpa [Ay, vu] using unstable_fderiv_iterate_mem hs hy hvu_mem N
  have hunstable_contract :
      ‖fderiv ℝ ((T.symm : E d → E d)^[N]) (((T : E d → E d)^[N]) y)
          (Ay vu)‖ ≤ a * ‖Ay vu‖ := by
    simpa [Ay, a] using hs.contract_unstable (((T : E d → E d)^[N]) y) hyN
      (Ay vu) hAu_mem N
  have hinv :
      fderiv ℝ ((T.symm : E d → E d)^[N]) (((T : E d → E d)^[N]) y)
          (Ay vu) = vu := by
    simpa [Ay] using fderiv_backward_forward_iterate_apply hs N y vu
  have hu_lower : ‖vu‖ ≤ a * ‖Ay vu‖ := by
    simpa [hinv] using hunstable_contract
  have hdecomp : vs + vu = v := by
    simpa [vs, vu] using stable_add_unstable_projection hs hy v
  have hvu_eq : vu = v - vs := by
    rw [← hdecomp]
    abel
  have hvs_eq : vs = v - vu := by
    rw [← hdecomp]
    abel
  have hAy_vu : ‖Ay vu‖ ≤ ‖Ay v‖ + ‖Ay vs‖ := by
    calc
      ‖Ay vu‖ = ‖Ay (v - vs)‖ := by rw [hvu_eq]
      _ = ‖Ay v - Ay vs‖ := by rw [map_sub]
      _ ≤ ‖Ay v‖ + ‖Ay vs‖ := norm_sub_le (Ay v) (Ay vs)
  have hAy_vu_bound : ‖Ay vu‖ ≤ (a + ζ) * ‖v‖ + a * ‖vs‖ :=
    hAy_vu.trans (add_le_add hAy_v hstable_contract)
  have hvs_norm : ‖vs‖ ≤ ‖v‖ + ‖vu‖ := by
    calc
      ‖vs‖ = ‖v - vu‖ := by rw [hvs_eq]
      _ ≤ ‖v‖ + ‖vu‖ := norm_sub_le v vu
  have hu_step :
      ‖vu‖ ≤ a * ((a + ζ) * ‖v‖ + a * (‖v‖ + ‖vu‖)) := by
    have hmul_vs : a * ‖vs‖ ≤ a * (‖v‖ + ‖vu‖) :=
      mul_le_mul_of_nonneg_left hvs_norm ha_pos.le
    exact hu_lower.trans
      (mul_le_mul_of_nonneg_left
        (hAy_vu_bound.trans (add_le_add le_rfl hmul_vs))
        ha_pos.le)
  have hu_step' :
      ‖vu‖ ≤ a * (2 * a + ζ) * ‖v‖ + a * a * ‖vu‖ := by
    calc
      ‖vu‖ ≤ a * ((a + ζ) * ‖v‖ + a * (‖v‖ + ‖vu‖)) := hu_step
      _ = a * (2 * a + ζ) * ‖v‖ + a * a * ‖vu‖ := by ring
  have ha_sq_le_half : a * a ≤ 1 / 2 := by
    nlinarith [ha_pos, ha_small]
  have hmain_nonneg : 0 ≤ a * (2 * a + ζ) * ‖v‖ := by
    have hfactor : 0 ≤ 2 * a + ζ := by nlinarith [ha_pos, hζ_nonneg]
    exact mul_nonneg (mul_nonneg ha_pos.le hfactor) (norm_nonneg v)
  have hbound : ‖vu‖ ≤ 2 * (a * (2 * a + ζ) * ‖v‖) := by
    nlinarith [hu_step', ha_sq_le_half, hmain_nonneg, norm_nonneg vu]
  simpa [vu, a, mul_assoc, mul_left_comm, mul_comm] using hbound

theorem compactUniformFDerivWithin {f : E d → E d} (hKc : IsCompact K)
    (hf : ContDiff ℝ 1 f) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ x : E d, x ∈ K → ∀ y : E d, ‖y - x‖ < r →
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ η := by
  let D : E d → (E d →L[ℝ] E d) := fun y => fderiv ℝ f y
  have hDcont : Continuous D := hf.continuous_fderiv (by norm_num)
  have hηhalf : 0 < η / 2 := by linarith
  have hlocal : ∀ a : K, ∃ ρ > 0, ∀ y : E d, dist y (a : E d) < ρ →
      ‖D y - D (a : E d)‖ < η / 2 := by
    intro a
    rcases (Metric.continuousAt_iff.mp hDcont.continuousAt (η / 2) hηhalf) with
      ⟨ρ, hρpos, hρ⟩
    refine ⟨ρ, hρpos, ?_⟩
    intro y hy
    have := hρ hy
    simpa [D, dist_eq_norm] using this
  choose ρ hρpos hρ using hlocal
  rcases hKc.elim_finite_subcover (fun a : K => Metric.ball (a : E d) (ρ a / 2))
      (fun _a => Metric.isOpen_ball)
      (by
        intro x hx
        exact Set.mem_iUnion.mpr
          ⟨⟨x, hx⟩, Metric.mem_ball_self (by linarith [hρpos ⟨x, hx⟩])⟩) with
    ⟨t, ht⟩
  let r : ℝ := if htne : t.Nonempty then
      (t.image fun a : K => ρ a / 4).min' (Finset.image_nonempty.mpr htne) else 1
  have hrpos : 0 < r := by
    by_cases htne : t.Nonempty
    · dsimp [r]
      rw [dif_pos htne]
      exact (Finset.lt_min'_iff _ _).mpr (by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨a, _hat, rfl⟩
        nlinarith [hρpos a])
    · dsimp [r]
      rw [dif_neg htne]
      norm_num
  refine ⟨r, hrpos, ?_⟩
  intro x hx y hyx
  have hxcover := ht hx
  simp only [Set.mem_iUnion] at hxcover
  rcases hxcover with ⟨a, ha⟩
  rcases ha with ⟨hat, hxa⟩
  have htne : t.Nonempty := ⟨a, hat⟩
  have hr_le : r ≤ ρ a / 4 := by
    dsimp [r]
    rw [dif_pos htne]
    exact Finset.min'_le _ (ρ a / 4) (Finset.mem_image.mpr ⟨a, hat, rfl⟩)
  have hyx_dist : dist y x < r := by simpa [dist_eq_norm] using hyx
  have hyx_quarter : dist y x < ρ a / 4 := lt_of_lt_of_le hyx_dist hr_le
  have hxa_half : dist x (a : E d) < ρ a / 2 := hxa
  have hxa_full : dist x (a : E d) < ρ a := by
    nlinarith [hρpos a, hxa_half]
  have hya_full : dist y (a : E d) < ρ a := by
    calc
      dist y (a : E d) ≤ dist y x + dist x (a : E d) := dist_triangle y x (a : E d)
      _ < ρ a / 4 + ρ a / 2 := add_lt_add hyx_quarter hxa_half
      _ < ρ a := by nlinarith [hρpos a]
  have hyD : ‖D y - D (a : E d)‖ < η / 2 := hρ a y hya_full
  have hxD : ‖D x - D (a : E d)‖ < η / 2 := hρ a x hxa_full
  calc
    ‖fderiv ℝ f y - fderiv ℝ f x‖ =
        ‖(D y - D (a : E d)) - (D x - D (a : E d))‖ := by
      simp [D]
    _ ≤ ‖D y - D (a : E d)‖ + ‖D x - D (a : E d)‖ := norm_sub_le _ _
    _ ≤ η := by linarith

theorem exists_unstableProjection_of_stable_nearby_small (hKc : IsCompact K)
    (hs : HyperbolicStructure T K) {θ : ℝ} (hθ : 0 < θ) :
    ∃ r > 0, ∀ x : E d, x ∈ K → ∀ y : E d, ∀ hy : y ∈ K, ‖y - x‖ < r →
      ∀ v : E d, v ∈ hs.stable x →
        ‖unstableProjection hs y hy v‖ ≤ θ * ‖v‖ := by
  let τ : ℝ := min θ 1
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    exact lt_min hθ zero_lt_one
  have hτ_le_θ : τ ≤ θ := by
    dsimp [τ]
    exact min_le_left θ 1
  have hτ_le_one : τ ≤ 1 := by
    dsimp [τ]
    exact min_le_right θ 1
  rcases exists_small_hyperbolic_iterate hs (by positivity : (0 : ℝ) < τ / 16) with
    ⟨N, hNsmall⟩
  let ζ : ℝ := τ / 8
  have hζ_pos : 0 < ζ := by
    dsimp [ζ]
    positivity
  rcases compactUniformFDerivWithin (K := K) hKc
      (contDiff_iterate hs.contDiff_fwd N) hζ_pos with
    ⟨r, hr_pos, hderiv_close⟩
  refine ⟨r, hr_pos, ?_⟩
  intro x hx y hy hyx v hv
  let a : ℝ := hs.const * hs.rate ^ N
  have ha_pos : 0 < a := by
    dsimp [a]
    exact mul_pos hs.const_pos (pow_pos hs.rate_pos N)
  have ha_small_tau : a < τ / 16 := by
    simpa [a] using hNsmall
  have ha_half : hs.const * hs.rate ^ N < 1 / 2 := by
    nlinarith [ha_small_tau, hτ_le_one]
  have hcoef_le :
      2 * (hs.const * hs.rate ^ N) *
          (2 * (hs.const * hs.rate ^ N) + ζ) ≤ θ := by
    have hcoef_tau : 2 * a * (2 * a + ζ) < τ := by
      dsimp [ζ]
      nlinarith [ha_pos, ha_small_tau, hτ_pos, hτ_le_one]
    have hsame :
        2 * (hs.const * hs.rate ^ N) *
            (2 * (hs.const * hs.rate ^ N) + ζ) = 2 * a * (2 * a + ζ) := by
      simp [a]
    rw [hsame]
    exact (le_of_lt hcoef_tau).trans hτ_le_θ
  have hbound :=
    unstableProjection_of_stable_nearby_bound (T := T) (K := K) hs hx hy
      (N := N) (ζ := ζ) ha_half (hderiv_close x hx y hyx) hζ_pos.le hv
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef_le (norm_nonneg v))

theorem stableProjection_of_unstable_nearby_bound (hs : HyperbolicStructure T K)
    {x y v : E d} (hx : x ∈ K) (hy : y ∈ K) {N : ℕ} {ζ : ℝ}
    (hsmall : hs.const * hs.rate ^ N < 1 / 2)
    (hderiv_close :
      ‖fderiv ℝ ((T.symm : E d → E d)^[N]) y -
          fderiv ℝ ((T.symm : E d → E d)^[N]) x‖ ≤ ζ)
    (hζ_nonneg : 0 ≤ ζ) (hv : v ∈ hs.unstable x) :
    ‖stableProjection hs y hy v‖ ≤
      2 * (hs.const * hs.rate ^ N) *
        (2 * (hs.const * hs.rate ^ N) + ζ) * ‖v‖ := by
  let a : ℝ := hs.const * hs.rate ^ N
  let Bx : E d →L[ℝ] E d := fderiv ℝ ((T.symm : E d → E d)^[N]) x
  let By : E d →L[ℝ] E d := fderiv ℝ ((T.symm : E d → E d)^[N]) y
  let vs : E d := stableProjection hs y hy v
  let vu : E d := unstableProjection hs y hy v
  have ha_pos : 0 < a := by
    dsimp [a]
    exact mul_pos hs.const_pos (pow_pos hs.rate_pos N)
  have ha_small : a < 1 / 2 := by
    simpa [a] using hsmall
  have hBy_v : ‖By v‖ ≤ (a + ζ) * ‖v‖ := by
    have hBx_v : ‖Bx v‖ ≤ a * ‖v‖ := by
      simpa [Bx, a] using hs.contract_unstable x hx v hv N
    have hdiff_v : ‖(By - Bx) v‖ ≤ ζ * ‖v‖ := by
      calc
        ‖(By - Bx) v‖ ≤ ‖By - Bx‖ * ‖v‖ := (By - Bx).le_opNorm v
        _ ≤ ζ * ‖v‖ :=
          mul_le_mul_of_nonneg_right (by simpa [By, Bx] using hderiv_close)
            (norm_nonneg v)
    have hdecomp : By v = Bx v + (By - Bx) v := by
      simp only [sub_apply]
      abel
    calc
      ‖By v‖ = ‖Bx v + (By - Bx) v‖ := by rw [hdecomp]
      _ ≤ ‖Bx v‖ + ‖(By - Bx) v‖ := norm_add_le (Bx v) ((By - Bx) v)
      _ ≤ a * ‖v‖ + ζ * ‖v‖ := add_le_add hBx_v hdiff_v
      _ = (a + ζ) * ‖v‖ := by ring
  have hvs_mem : vs ∈ hs.stable y := by
    simp [vs]
  have hvu_mem : vu ∈ hs.unstable y := by
    simp [vu]
  have hunstable_contract : ‖By vu‖ ≤ a * ‖vu‖ := by
    simpa [By, a] using hs.contract_unstable y hy vu hvu_mem N
  have hyN : ((T.symm : E d → E d)^[N]) y ∈ K := backward_iterate_mem hs hy N
  have hBvs_mem :
      By vs ∈ hs.stable (((T.symm : E d → E d)^[N]) y) := by
    simpa [By, vs] using stable_fderiv_symm_iterate_mem hs hy hvs_mem N
  have hstable_contract :
      ‖fderiv ℝ ((T : E d → E d)^[N]) (((T.symm : E d → E d)^[N]) y)
          (By vs)‖ ≤ a * ‖By vs‖ := by
    simpa [By, a] using hs.contract_stable (((T.symm : E d → E d)^[N]) y) hyN
      (By vs) hBvs_mem N
  have hinv :
      fderiv ℝ ((T : E d → E d)^[N]) (((T.symm : E d → E d)^[N]) y)
          (By vs) = vs := by
    simpa [By] using fderiv_forward_backward_iterate_apply hs N y vs
  have hs_lower : ‖vs‖ ≤ a * ‖By vs‖ := by
    simpa [hinv] using hstable_contract
  have hdecomp : vs + vu = v := by
    simpa [vs, vu] using stable_add_unstable_projection hs hy v
  have hvs_eq : vs = v - vu := by
    rw [← hdecomp]
    abel
  have hvu_eq : vu = v - vs := by
    rw [← hdecomp]
    abel
  have hBy_vs : ‖By vs‖ ≤ ‖By v‖ + ‖By vu‖ := by
    calc
      ‖By vs‖ = ‖By (v - vu)‖ := by rw [hvs_eq]
      _ = ‖By v - By vu‖ := by rw [map_sub]
      _ ≤ ‖By v‖ + ‖By vu‖ := norm_sub_le (By v) (By vu)
  have hBy_vs_bound : ‖By vs‖ ≤ (a + ζ) * ‖v‖ + a * ‖vu‖ :=
    hBy_vs.trans (add_le_add hBy_v hunstable_contract)
  have hvu_norm : ‖vu‖ ≤ ‖v‖ + ‖vs‖ := by
    calc
      ‖vu‖ = ‖v - vs‖ := by rw [hvu_eq]
      _ ≤ ‖v‖ + ‖vs‖ := norm_sub_le v vs
  have hs_step :
      ‖vs‖ ≤ a * ((a + ζ) * ‖v‖ + a * (‖v‖ + ‖vs‖)) := by
    have hmul_vu : a * ‖vu‖ ≤ a * (‖v‖ + ‖vs‖) :=
      mul_le_mul_of_nonneg_left hvu_norm ha_pos.le
    exact hs_lower.trans
      (mul_le_mul_of_nonneg_left
        (hBy_vs_bound.trans (add_le_add le_rfl hmul_vu))
        ha_pos.le)
  have hs_step' :
      ‖vs‖ ≤ a * (2 * a + ζ) * ‖v‖ + a * a * ‖vs‖ := by
    calc
      ‖vs‖ ≤ a * ((a + ζ) * ‖v‖ + a * (‖v‖ + ‖vs‖)) := hs_step
      _ = a * (2 * a + ζ) * ‖v‖ + a * a * ‖vs‖ := by ring
  have ha_sq_le_half : a * a ≤ 1 / 2 := by
    nlinarith [ha_pos, ha_small]
  have hmain_nonneg : 0 ≤ a * (2 * a + ζ) * ‖v‖ := by
    have hfactor : 0 ≤ 2 * a + ζ := by nlinarith [ha_pos, hζ_nonneg]
    exact mul_nonneg (mul_nonneg ha_pos.le hfactor) (norm_nonneg v)
  have hbound : ‖vs‖ ≤ 2 * (a * (2 * a + ζ) * ‖v‖) := by
    nlinarith [hs_step', ha_sq_le_half, hmain_nonneg, norm_nonneg vs]
  simpa [vs, a, mul_assoc, mul_left_comm, mul_comm] using hbound

theorem exists_stableProjection_of_unstable_nearby_small (hKc : IsCompact K)
    (hs : HyperbolicStructure T K) {θ : ℝ} (hθ : 0 < θ) :
    ∃ r > 0, ∀ x : E d, x ∈ K → ∀ y : E d, ∀ hy : y ∈ K, ‖y - x‖ < r →
      ∀ v : E d, v ∈ hs.unstable x →
        ‖stableProjection hs y hy v‖ ≤ θ * ‖v‖ := by
  let τ : ℝ := min θ 1
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    exact lt_min hθ zero_lt_one
  have hτ_le_θ : τ ≤ θ := by
    dsimp [τ]
    exact min_le_left θ 1
  have hτ_le_one : τ ≤ 1 := by
    dsimp [τ]
    exact min_le_right θ 1
  rcases exists_small_hyperbolic_iterate hs (by positivity : (0 : ℝ) < τ / 16) with
    ⟨N, hNsmall⟩
  let ζ : ℝ := τ / 8
  have hζ_pos : 0 < ζ := by
    dsimp [ζ]
    positivity
  rcases compactUniformFDerivWithin (K := K) hKc
      (contDiff_iterate hs.contDiff_bwd N) hζ_pos with
    ⟨r, hr_pos, hderiv_close⟩
  refine ⟨r, hr_pos, ?_⟩
  intro x hx y hy hyx v hv
  let a : ℝ := hs.const * hs.rate ^ N
  have ha_pos : 0 < a := by
    dsimp [a]
    exact mul_pos hs.const_pos (pow_pos hs.rate_pos N)
  have ha_small_tau : a < τ / 16 := by
    simpa [a] using hNsmall
  have ha_half : hs.const * hs.rate ^ N < 1 / 2 := by
    nlinarith [ha_small_tau, hτ_le_one]
  have hcoef_le :
      2 * (hs.const * hs.rate ^ N) *
          (2 * (hs.const * hs.rate ^ N) + ζ) ≤ θ := by
    have hcoef_tau : 2 * a * (2 * a + ζ) < τ := by
      dsimp [ζ]
      nlinarith [ha_pos, ha_small_tau, hτ_pos, hτ_le_one]
    have hsame :
        2 * (hs.const * hs.rate ^ N) *
            (2 * (hs.const * hs.rate ^ N) + ζ) = 2 * a * (2 * a + ζ) := by
      simp [a]
    rw [hsame]
    exact (le_of_lt hcoef_tau).trans hτ_le_θ
  have hbound :=
    stableProjection_of_unstable_nearby_bound (T := T) (K := K) hs hx hy
      (N := N) (ζ := ζ) ha_half (hderiv_close x hx y hyx) hζ_pos.le hv
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef_le (norm_nonneg v))

theorem compactUniformTwoPointLinearization {f : E d → E d} (hKc : IsCompact K)
    (hf : ContDiff ℝ 1 f) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ a : E d, a ∈ K → ∀ z w : E d,
      ‖z - a‖ < r → ‖w - a‖ < r →
        ‖f z - f w - fderiv ℝ f a (z - w)‖ ≤ η * ‖z - w‖ := by
  rcases compactUniformFDerivWithin (K := K) hKc hf hη with ⟨r, hrpos, hD⟩
  refine ⟨r, hrpos, ?_⟩
  intro a ha z w hza hwa
  have hbound : ∀ y : E d, y ∈ Metric.ball a r →
      ‖fderiv ℝ f y - fderiv ℝ f a‖ ≤ η := by
    intro y hy
    exact hD a ha y (by simpa [Metric.mem_ball, dist_eq_norm] using hy)
  have hdiff : ∀ y : E d, y ∈ Metric.ball a r → DifferentiableAt ℝ f y := by
    intro y _hy
    exact (hf.differentiable (by norm_num)).differentiableAt
  have hz_ball : z ∈ Metric.ball a r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hza
  have hw_ball : w ∈ Metric.ball a r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hwa
  exact (convex_ball a r).norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (φ := fderiv ℝ f a) hdiff hbound hw_ball hz_ball

theorem compactUniformFirstOrderRemainder {f : E d → E d} (hKc : IsCompact K)
    (hf : ContDiff ℝ 1 f) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ x : E d, x ∈ K → ∀ z : E d, ‖z - x‖ < r →
      ‖f z - f x - fderiv ℝ f x (z - x)‖ ≤ η * ‖z - x‖ := by
  let D : E d → (E d →L[ℝ] E d) := fun y => fderiv ℝ f y
  have hDcont : Continuous D := hf.continuous_fderiv (by norm_num)
  have hηhalf : 0 < η / 2 := by linarith
  have hlocal : ∀ a : K, ∃ ρ > 0, ∀ y : E d, dist y (a : E d) < ρ →
      ‖D y - D (a : E d)‖ < η / 2 := by
    intro a
    rcases (Metric.continuousAt_iff.mp hDcont.continuousAt (η / 2) hηhalf) with
      ⟨ρ, hρpos, hρ⟩
    refine ⟨ρ, hρpos, ?_⟩
    intro y hy
    have := hρ hy
    simpa [D, dist_eq_norm] using this
  choose ρ hρpos hρ using hlocal
  rcases hKc.elim_finite_subcover (fun a : K => Metric.ball (a : E d) (ρ a / 2))
      (fun _a => Metric.isOpen_ball)
      (by
        intro x hx
        exact Set.mem_iUnion.mpr
          ⟨⟨x, hx⟩, Metric.mem_ball_self (by linarith [hρpos ⟨x, hx⟩])⟩) with
    ⟨t, ht⟩
  let r : ℝ := if htne : t.Nonempty then
      (t.image fun a : K => ρ a / 4).min' (Finset.image_nonempty.mpr htne) else 1
  have hrpos : 0 < r := by
    by_cases htne : t.Nonempty
    · dsimp [r]
      rw [dif_pos htne]
      exact (Finset.lt_min'_iff _ _).mpr (by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨a, _hat, rfl⟩
        nlinarith [hρpos a])
    · dsimp [r]
      rw [dif_neg htne]
      norm_num
  refine ⟨r, hrpos, ?_⟩
  intro x hx z hzx
  have hxcover := ht hx
  simp only [Set.mem_iUnion] at hxcover
  rcases hxcover with ⟨a, ha⟩
  rcases ha with ⟨hat, hxa⟩
  have htne : t.Nonempty := ⟨a, hat⟩
  have hr_le : r ≤ ρ a / 4 := by
    dsimp [r]
    rw [dif_pos htne]
    exact Finset.min'_le _ (ρ a / 4) (Finset.mem_image.mpr ⟨a, hat, rfl⟩)
  have hzx_dist : dist z x < r := by simpa [dist_eq_norm] using hzx
  have hz_ball : z ∈ Metric.ball x r := hzx_dist
  have hx_ball : x ∈ Metric.ball x r := Metric.mem_ball_self hrpos
  have hbound : ∀ y : E d, y ∈ Metric.ball x r → ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ η := by
    intro y hy
    have hyx : dist y x < r := hy
    have hyx_quarter : dist y x < ρ a / 4 := lt_of_lt_of_le hyx hr_le
    have hxa_half : dist x (a : E d) < ρ a / 2 := hxa
    have hxa_full : dist x (a : E d) < ρ a := by
      nlinarith [hρpos a, hxa_half]
    have hya_full : dist y (a : E d) < ρ a := by
      calc
        dist y (a : E d) ≤ dist y x + dist x (a : E d) := dist_triangle y x (a : E d)
        _ < ρ a / 4 + ρ a / 2 := add_lt_add hyx_quarter hxa_half
        _ < ρ a := by nlinarith [hρpos a]
    have hyD : ‖D y - D (a : E d)‖ < η / 2 := hρ a y hya_full
    have hxD : ‖D x - D (a : E d)‖ < η / 2 := hρ a x hxa_full
    calc
      ‖fderiv ℝ f y - fderiv ℝ f x‖ =
          ‖(D y - D (a : E d)) - (D x - D (a : E d))‖ := by
        simp [D]
      _ ≤ ‖D y - D (a : E d)‖ + ‖D x - D (a : E d)‖ := norm_sub_le _ _
      _ ≤ η := by linarith
  have hdiff : ∀ y : E d, y ∈ Metric.ball x r → DifferentiableAt ℝ f y := by
    intro y _hy
    exact (hf.differentiable (by norm_num)).differentiableAt
  exact (convex_ball x r).norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (φ := fderiv ℝ f x) hdiff hbound hx_ball hz_ball

def UniformFirstOrderRemainderEstimates (T : E d ≃ₜ E d) (K : Set (E d))
    (_hKc : IsCompact K) (_hs : HyperbolicStructure T K) : Prop :=
  ∃ U : Set (E d), IsOpen U ∧ K ⊆ U ∧
    ∀ η > 0, ∃ r > 0, ∀ x : E d, x ∈ K → ∀ z : E d, z ∈ U →
      ‖z - x‖ < r →
        ‖T z - T x - fderiv ℝ (T : E d → E d) x (z - x)‖ ≤ η * ‖z - x‖ ∧
        ‖T.symm z - T.symm x - fderiv ℝ (T.symm : E d → E d) x (z - x)‖ ≤
          η * ‖z - x‖

theorem uniformFirstOrderRemainderEstimates (hKc : IsCompact K)
    (hs : HyperbolicStructure T K) :
    UniformFirstOrderRemainderEstimates T K hKc hs := by
  refine ⟨Set.univ, isOpen_univ, ?_, ?_⟩
  · intro x _hx
    exact Set.mem_univ x
  · intro η hη
    rcases compactUniformFirstOrderRemainder hKc hs.contDiff_fwd hη with
      ⟨rf, hrf_pos, hf_rem⟩
    rcases compactUniformFirstOrderRemainder hKc hs.contDiff_bwd hη with
      ⟨rb, hrb_pos, hb_rem⟩
    refine ⟨min rf rb, lt_min hrf_pos hrb_pos, ?_⟩
    intro x hx z _hzU hz
    constructor
    · exact hf_rem x hx z (lt_of_lt_of_le hz (min_le_left rf rb))
    · exact hb_rem x hx z (lt_of_lt_of_le hz (min_le_right rf rb))

def localTube (K : Set (E d)) (ρ : ℝ) : Set (E d) :=
  ⋃ x : E d, ⋃ _hx : x ∈ K, Metric.ball x ρ

theorem mem_localTube {K : Set (E d)} {ρ : ℝ} {z : E d} :
    z ∈ localTube K ρ ↔ ∃ x : E d, x ∈ K ∧ ‖z - x‖ < ρ := by
  simp [localTube, Metric.ball, dist_eq_norm, norm_sub_rev]

theorem isOpen_localTube (K : Set (E d)) (ρ : ℝ) :
    IsOpen (localTube K ρ) := by
  classical
  rw [localTube]
  refine isOpen_iUnion fun x => isOpen_iUnion fun _hx => ?_
  exact Metric.isOpen_ball

theorem subset_localTube (K : Set (E d)) {ρ : ℝ} (hρ : 0 < ρ) :
    K ⊆ localTube K ρ := by
  intro x hx
  rw [mem_localTube]
  exact ⟨x, hx, by simpa using hρ⟩

theorem localTube_mono_radius {K : Set (E d)} {ρ σ : ℝ} (hρσ : ρ ≤ σ) :
    localTube K ρ ⊆ localTube K σ := by
  intro z hz
  rw [mem_localTube] at hz ⊢
  rcases hz with ⟨x, hxK, hxz⟩
  exact ⟨x, hxK, lt_of_lt_of_le hxz hρσ⟩

noncomputable def localTubeAnchor {K : Set (E d)} {ρ : ℝ} {z : E d}
    (hz : z ∈ localTube K ρ) : E d :=
  Classical.choose (mem_localTube.mp hz)

theorem localTubeAnchor_mem {K : Set (E d)} {ρ : ℝ} {z : E d}
    (hz : z ∈ localTube K ρ) :
    localTubeAnchor hz ∈ K :=
  (Classical.choose_spec (mem_localTube.mp hz)).1

theorem localTubeAnchor_close {K : Set (E d)} {ρ : ℝ} {z : E d}
    (hz : z ∈ localTube K ρ) :
    ‖z - localTubeAnchor hz‖ < ρ :=
  (Classical.choose_spec (mem_localTube.mp hz)).2

noncomputable def localTubeAnchorSeq {K : Set (E d)} {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) : E d :=
  localTubeAnchor (hx n)

theorem localTubeAnchorSeq_mem {K : Set (E d)} {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) :
    localTubeAnchorSeq hx n ∈ K :=
  localTubeAnchor_mem (hx n)

theorem localTubeAnchorSeq_close {K : Set (E d)} {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) :
    ‖x n - localTubeAnchorSeq hx n‖ < ρ :=
  localTubeAnchor_close (hx n)

theorem localTubeAnchorSeq_close_lt {K : Set (E d)} {r ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (hρr : ρ ≤ r) (n : ℕ) :
    ‖x n - localTubeAnchorSeq hx n‖ < r :=
  lt_of_lt_of_le (localTubeAnchorSeq_close hx n) hρr

theorem localTubeAnchorSeq_remainder
    {U : Set (E d)} {η r ρ : ℝ} {x : ℕ → E d}
    (hρU : localTube K ρ ⊆ U) (hρr : ρ ≤ r)
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hrem : ∀ a : E d, a ∈ K → ∀ z : E d, z ∈ U →
      ‖z - a‖ < r →
        ‖T z - T a - fderiv ℝ (T : E d → E d) a (z - a)‖ ≤ η * ‖z - a‖ ∧
        ‖T.symm z - T.symm a - fderiv ℝ (T.symm : E d → E d) a (z - a)‖ ≤
          η * ‖z - a‖)
    (n : ℕ) :
    ‖T (x n) - T (localTubeAnchorSeq hx n) -
        fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
          (x n - localTubeAnchorSeq hx n)‖ ≤
      η * ‖x n - localTubeAnchorSeq hx n‖ ∧
    ‖T.symm (x n) - T.symm (localTubeAnchorSeq hx n) -
        fderiv ℝ (T.symm : E d → E d) (localTubeAnchorSeq hx n)
          (x n - localTubeAnchorSeq hx n)‖ ≤
      η * ‖x n - localTubeAnchorSeq hx n‖ := by
  exact hrem (localTubeAnchorSeq hx n) (localTubeAnchorSeq_mem hx n) (x n)
    (hρU (hx n)) (localTubeAnchorSeq_close_lt hx hρr n)

theorem localTube_eq_thickening (K : Set (E d)) (ρ : ℝ) :
    localTube K ρ = Metric.thickening ρ K := by
  rw [Metric.thickening_eq_biUnion_ball]
  rfl

theorem exists_localTube_subset_open (hKc : IsCompact K) {U : Set (E d)}
    (hU_open : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ > 0, localTube K ρ ⊆ U := by
  rcases hKc.exists_thickening_subset_open hU_open hKU with ⟨ρ, hρ_pos, hρ_sub⟩
  refine ⟨ρ, hρ_pos, ?_⟩
  rw [localTube_eq_thickening]
  exact hρ_sub

theorem isBounded_localTube (hKc : IsCompact K) (ρ : ℝ) :
    Bornology.IsBounded (localTube K ρ) := by
  rw [localTube_eq_thickening]
  exact hKc.isBounded.thickening

theorem exists_norm_bound_of_forall_mem_localTube (hKc : IsCompact K) {ρ : ℝ}
    {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ) :
    ∃ C : ℝ, ∀ n : ℕ, ‖x n‖ ≤ C := by
  rcases (isBounded_localTube (K := K) hKc ρ).exists_norm_le with ⟨C, hC⟩
  exact ⟨C, fun n => hC (x n) (hx n)⟩

theorem exists_boundedSequence_of_forall_mem_localTube (hKc : IsCompact K) {ρ : ℝ}
    {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ) :
    ∃ xb : BoundedContinuousFunction ℕ (E d), ∀ n : ℕ, xb n = x n := by
  rcases exists_norm_bound_of_forall_mem_localTube (K := K) hKc hx with ⟨C, hC⟩
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroupDiscrete x C hC, ?_⟩
  intro n
  rfl

abbrev CorrectionSeq (d : ℕ) := BoundedContinuousFunction ℕ (E d)

def correctionBall (δ : ℝ) : Set (CorrectionSeq d) :=
  {u : CorrectionSeq d | ‖u‖ ≤ δ}

theorem isClosed_correctionBall (δ : ℝ) :
    IsClosed (correctionBall (d := d) δ) := by
  exact isClosed_Iic.preimage continuous_norm

theorem isComplete_correctionBall (δ : ℝ) :
    IsComplete (correctionBall (d := d) δ) :=
  (isClosed_correctionBall (d := d) δ).isComplete

theorem correctionBall_apply_norm_le {δ : ℝ} {u : CorrectionSeq d}
    (hu : u ∈ correctionBall (d := d) δ) :
    ∀ n : ℕ, ‖u n‖ ≤ δ := by
  exact BoundedContinuousFunction.norm_le_of_nonempty.mp hu

theorem correctionBall_apply_norm_lt {r δ : ℝ} {u : CorrectionSeq d}
    (hu : u ∈ correctionBall (d := d) r) (hrδ : r < δ) :
    ∀ n : ℕ, ‖u n‖ < δ := by
  intro n
  exact lt_of_le_of_lt (correctionBall_apply_norm_le (d := d) hu n) hrδ

theorem correctionSeq_apply_norm_le_norm (u : CorrectionSeq d) (n : ℕ) :
    ‖u n‖ ≤ ‖u‖ :=
  BoundedContinuousFunction.norm_le_of_nonempty.mp (le_rfl : ‖u‖ ≤ ‖u‖) n

theorem correctionSeq_norm_le_of_pointwise {u : CorrectionSeq d} {C : ℝ}
    (hC : ∀ n : ℕ, ‖u n‖ ≤ C) :
    ‖u‖ ≤ C :=
  BoundedContinuousFunction.norm_le_of_nonempty.mpr hC

noncomputable def correctionRadius (δ ρ : ℝ) : ℝ :=
  min (δ / 2) (ρ / 2)

theorem correctionRadius_pos {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    0 < correctionRadius δ ρ := by
  dsimp [correctionRadius]
  refine lt_min ?_ ?_
  · linarith
  · linarith

theorem correctionRadius_lt_delta {δ ρ : ℝ} (hδ : 0 < δ) :
    correctionRadius δ ρ < δ := by
  dsimp [correctionRadius]
  exact lt_of_le_of_lt (min_le_left (δ / 2) (ρ / 2)) (by linarith)

theorem correctionRadius_le_half_tube (δ ρ : ℝ) :
    correctionRadius δ ρ ≤ ρ / 2 := by
  exact min_le_right (δ / 2) (ρ / 2)

theorem correctionRadius_lt_tube {δ ρ : ℝ} (hρ : 0 < ρ) :
    correctionRadius δ ρ < ρ := by
  exact lt_of_le_of_lt (correctionRadius_le_half_tube δ ρ) (by linarith)

theorem correction_trial_close_anchor_lt {x k u : E d} {α ρ r : ℝ}
    (hxk : ‖x - k‖ < ρ) (hu : ‖u‖ ≤ α) (hαρ : α ≤ ρ / 2)
    (hρr : ρ + ρ / 2 < r) :
    ‖(x + u) - k‖ < r := by
  have hdecomp : (x + u) - k = (x - k) + u := by
    abel
  calc
    ‖(x + u) - k‖ = ‖(x - k) + u‖ := by rw [hdecomp]
    _ ≤ ‖x - k‖ + ‖u‖ := norm_add_le (x - k) u
    _ < ρ + α := add_lt_add_of_lt_of_le hxk hu
    _ ≤ ρ + ρ / 2 := by linarith [hαρ]
    _ < r := hρr

theorem correctionBall_trial_close_anchor_lt {α ρ r : ℝ} {x : ℕ → E d}
    {u : CorrectionSeq d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hu : u ∈ correctionBall (d := d) α) (hαρ : α ≤ ρ / 2)
    (hρr : ρ + ρ / 2 < r) (n : ℕ) :
    ‖(x n + u n) - localTubeAnchorSeq hx n‖ < r := by
  exact correction_trial_close_anchor_lt (localTubeAnchorSeq_close hx n)
    (correctionBall_apply_norm_le (d := d) hu n) hαρ hρr

theorem correctionBall_trial_mem_localTube {α ρ σ : ℝ} {x : ℕ → E d}
    {u : CorrectionSeq d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hu : u ∈ correctionBall (d := d) α) (hαρ : α ≤ ρ / 2)
    (hρσ : ρ + ρ / 2 < σ) :
    ∀ n : ℕ, x n + u n ∈ localTube K σ := by
  intro n
  rw [mem_localTube]
  exact ⟨localTubeAnchorSeq hx n, localTubeAnchorSeq_mem hx n,
    correctionBall_trial_close_anchor_lt hx hu hαρ hρσ n⟩

theorem correctionBall_trial_mem_of_localTube_subset {U : Set (E d)} {α ρ σ : ℝ}
    {x : ℕ → E d} {u : CorrectionSeq d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hu : u ∈ correctionBall (d := d) α) (hαρ : α ≤ ρ / 2)
    (hρσ : ρ + ρ / 2 < σ) (hσU : localTube K σ ⊆ U) :
    ∀ n : ℕ, x n + u n ∈ U := by
  intro n
  exact hσU (correctionBall_trial_mem_localTube hx hu hαρ hρσ n)

def pseudoOrbitDefect (T : E d → E d) (x : ℕ → E d) (n : ℕ) : E d :=
  x (n + 1) - T (x n)

theorem anchorTransition_decomp {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) :
    localTubeAnchorSeq hx (n + 1) - T (localTubeAnchorSeq hx n) =
      (localTubeAnchorSeq hx (n + 1) - x (n + 1)) +
        pseudoOrbitDefect (T : E d → E d) x n +
          (T (x n) - T (localTubeAnchorSeq hx n)) := by
  dsimp [pseudoOrbitDefect]
  abel

theorem pseudoOrbitDefect_norm_lt {ε : ℝ} {x : ℕ → E d}
    (hx : IsPseudoOrbit (T : E d → E d) ε x) (n : ℕ) :
    ‖pseudoOrbitDefect (T : E d → E d) x n‖ < ε := by
  simpa [pseudoOrbitDefect] using hx n

noncomputable def pseudoOrbitDefectSeq (T : E d → E d) {ε : ℝ} (x : ℕ → E d)
    (hdefect : ∀ n : ℕ, ‖pseudoOrbitDefect T x n‖ < ε) : CorrectionSeq d :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n : ℕ => pseudoOrbitDefect T x n) ε (fun n => le_of_lt (hdefect n))

@[simp]
theorem pseudoOrbitDefectSeq_apply (T : E d → E d) {ε : ℝ} (x : ℕ → E d)
    (hdefect : ∀ n : ℕ, ‖pseudoOrbitDefect T x n‖ < ε) (n : ℕ) :
    pseudoOrbitDefectSeq T x hdefect n = pseudoOrbitDefect T x n :=
  rfl

theorem pseudoOrbitDefectSeq_norm_le (T : E d → E d) {ε : ℝ} (x : ℕ → E d)
    (hdefect : ∀ n : ℕ, ‖pseudoOrbitDefect T x n‖ < ε) :
    ‖pseudoOrbitDefectSeq T x hdefect‖ ≤ ε :=
  correctionSeq_norm_le_of_pointwise (d := d) (fun n => le_of_lt (hdefect n))

noncomputable def anchorStableProjection (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) :
    E d →ₗ[ℝ] E d :=
  stableProjection hs (localTubeAnchorSeq hx n) (localTubeAnchorSeq_mem hx n)

noncomputable def anchorUnstableProjection (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) :
    E d →ₗ[ℝ] E d :=
  unstableProjection hs (localTubeAnchorSeq hx n) (localTubeAnchorSeq_mem hx n)

noncomputable def anchorDerivative {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) : E d →L[ℝ] E d :=
  fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)

noncomputable def anchorInverseDerivative {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) : E d →L[ℝ] E d :=
  fderiv ℝ (T.symm : E d → E d) (T (localTubeAnchorSeq hx n))

noncomputable def anchorDerivativeProduct {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) : ℕ → E d →L[ℝ] E d
  | 0 => 1
  | m + 1 => (anchorDerivative (T := T) hx (n + m)).comp (anchorDerivativeProduct hx n m)

noncomputable def anchorInverseDerivativeProduct {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) : ℕ → E d →L[ℝ] E d
  | 0 => 1
  | m + 1 =>
      (anchorInverseDerivativeProduct hx n m).comp
        (anchorInverseDerivative (T := T) hx (n + m))

@[simp]
theorem anchorDerivativeProduct_zero {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) :
    anchorDerivativeProduct (T := T) hx n 0 = 1 := by
  rfl

@[simp]
theorem anchorDerivativeProduct_succ {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m : ℕ) :
    anchorDerivativeProduct (T := T) hx n (m + 1) =
      (anchorDerivative (T := T) hx (n + m)).comp
        (anchorDerivativeProduct (T := T) hx n m) := by
  rfl

@[simp]
theorem anchorInverseDerivativeProduct_zero {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) :
    anchorInverseDerivativeProduct (T := T) hx n 0 = 1 := by
  rfl

@[simp]
theorem anchorInverseDerivativeProduct_succ {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m : ℕ) :
    anchorInverseDerivativeProduct (T := T) hx n (m + 1) =
      (anchorInverseDerivativeProduct (T := T) hx n m).comp
        (anchorInverseDerivative (T := T) hx (n + m)) := by
  rfl

theorem anchorDerivativeProduct_succ_apply {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m : ℕ) (v : E d) :
    anchorDerivativeProduct (T := T) hx n (m + 1) v =
      anchorDerivative (T := T) hx (n + m)
        (anchorDerivativeProduct (T := T) hx n m v) := by
  rfl

theorem anchorInverseDerivativeProduct_succ_apply {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m : ℕ) (v : E d) :
    anchorInverseDerivativeProduct (T := T) hx n (m + 1) v =
      anchorInverseDerivativeProduct (T := T) hx n m
        (anchorInverseDerivative (T := T) hx (n + m) v) := by
  rfl

theorem anchorDerivativeProduct_split {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m l : ℕ) :
    anchorDerivativeProduct (T := T) hx n (m + l) =
      (anchorDerivativeProduct (T := T) hx (n + m) l).comp
        (anchorDerivativeProduct (T := T) hx n m) := by
  induction l with
  | zero =>
      apply ContinuousLinearMap.ext
      intro v
      simp
  | succ l ih =>
      apply ContinuousLinearMap.ext
      intro v
      simp only [Nat.add_succ, anchorDerivativeProduct_succ_apply]
      rw [ih]
      simp only [ContinuousLinearMap.comp_apply]
      congr 1
      ring_nf

theorem anchorDerivativeProduct_split_apply {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m l : ℕ) (v : E d) :
    anchorDerivativeProduct (T := T) hx n (m + l) v =
      anchorDerivativeProduct (T := T) hx (n + m) l
        (anchorDerivativeProduct (T := T) hx n m v) := by
  simpa using congrArg (fun L : E d →L[ℝ] E d => L v)
    (anchorDerivativeProduct_split (T := T) hx n m l)

theorem anchorInverseDerivativeProduct_split {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m l : ℕ) :
    anchorInverseDerivativeProduct (T := T) hx n (m + l) =
      (anchorInverseDerivativeProduct (T := T) hx n m).comp
        (anchorInverseDerivativeProduct (T := T) hx (n + m) l) := by
  induction l with
  | zero =>
      apply ContinuousLinearMap.ext
      intro v
      simp
  | succ l ih =>
      apply ContinuousLinearMap.ext
      intro v
      simp only [Nat.add_succ, anchorInverseDerivativeProduct_succ_apply]
      rw [ih]
      simp only [ContinuousLinearMap.comp_apply]
      rw [anchorInverseDerivativeProduct_succ_apply]
      rw [← Nat.add_assoc]

theorem anchorInverseDerivativeProduct_split_apply {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m l : ℕ) (v : E d) :
    anchorInverseDerivativeProduct (T := T) hx n (m + l) v =
      anchorInverseDerivativeProduct (T := T) hx n m
        (anchorInverseDerivativeProduct (T := T) hx (n + m) l v) := by
  simpa using congrArg (fun L : E d →L[ℝ] E d => L v)
    (anchorInverseDerivativeProduct_split (T := T) hx n m l)

theorem anchorDerivativeProduct_apply_norm_le_of_step_bound
    {ρ B : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) {n m : ℕ}
    (hB_nonneg : 0 ≤ B)
    (hstep : ∀ j : ℕ, j < m →
      ‖anchorDerivative (T := T) hx (n + j)‖ ≤ B) :
    ∀ v : E d,
      ‖anchorDerivativeProduct (T := T) hx n m v‖ ≤ B ^ m * ‖v‖ := by
  induction m with
  | zero =>
      intro v
      simp [anchorDerivativeProduct_zero]
  | succ m ih =>
      intro v
      have hm_step :
          ‖anchorDerivative (T := T) hx (n + m)‖ ≤ B :=
        hstep m (Nat.lt_succ_self m)
      have hprev :
          ‖anchorDerivativeProduct (T := T) hx n m v‖ ≤ B ^ m * ‖v‖ :=
        ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self m))) v
      have hstep_v :
          ‖anchorDerivative (T := T) hx (n + m)
              (anchorDerivativeProduct (T := T) hx n m v)‖ ≤
            B * ‖anchorDerivativeProduct (T := T) hx n m v‖ := by
        calc
          ‖anchorDerivative (T := T) hx (n + m)
              (anchorDerivativeProduct (T := T) hx n m v)‖ ≤
              ‖anchorDerivative (T := T) hx (n + m)‖ *
                ‖anchorDerivativeProduct (T := T) hx n m v‖ :=
            (anchorDerivative (T := T) hx (n + m)).le_opNorm
              (anchorDerivativeProduct (T := T) hx n m v)
          _ ≤ B * ‖anchorDerivativeProduct (T := T) hx n m v‖ :=
            mul_le_mul_of_nonneg_right hm_step (norm_nonneg _)
      calc
        ‖anchorDerivativeProduct (T := T) hx n (m + 1) v‖ =
            ‖anchorDerivative (T := T) hx (n + m)
              (anchorDerivativeProduct (T := T) hx n m v)‖ := by
          rw [anchorDerivativeProduct_succ_apply]
        _ ≤ B * ‖anchorDerivativeProduct (T := T) hx n m v‖ := hstep_v
        _ ≤ B * (B ^ m * ‖v‖) :=
          mul_le_mul_of_nonneg_left hprev hB_nonneg
        _ = B ^ (m + 1) * ‖v‖ := by
          rw [pow_succ]
          ring

theorem anchorInverseDerivative_apply_anchorDerivative (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (n : ℕ) (v : E d) :
    anchorInverseDerivative (T := T) hx n (anchorDerivative (T := T) hx n v) = v := by
  simpa [anchorInverseDerivative, anchorDerivative, Function.iterate_one] using
    fderiv_backward_forward_iterate_apply (T := T) (K := K) hs 1
      (localTubeAnchorSeq hx n) v

theorem anchorDerivative_apply_anchorInverseDerivative (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (n : ℕ) (v : E d) :
    anchorDerivative (T := T) hx n (anchorInverseDerivative (T := T) hx n v) = v := by
  simpa [anchorInverseDerivative, anchorDerivative, Function.iterate_one] using
    fderiv_forward_backward_iterate_apply (T := T) (K := K) hs 1
      (T (localTubeAnchorSeq hx n)) v

theorem anchorInverseDerivativeProduct_apply_anchorDerivativeProduct
    (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m : ℕ) (v : E d) :
    anchorInverseDerivativeProduct (T := T) hx n m
        (anchorDerivativeProduct (T := T) hx n m v) = v := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      simp [anchorDerivativeProduct_succ, anchorInverseDerivativeProduct_succ,
        anchorInverseDerivative_apply_anchorDerivative (T := T) (K := K) hs hx (n + m),
        ih]

theorem anchorDerivativeProduct_apply_anchorInverseDerivativeProduct
    (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m : ℕ) (v : E d) :
    anchorDerivativeProduct (T := T) hx n m
        (anchorInverseDerivativeProduct (T := T) hx n m v) = v := by
  induction m generalizing v with
  | zero =>
      simp
  | succ m ih =>
      have hih :
          anchorDerivativeProduct (T := T) hx n m
              (anchorInverseDerivativeProduct (T := T) hx n m
                (anchorInverseDerivative (T := T) hx (n + m) v)) =
            anchorInverseDerivative (T := T) hx (n + m) v :=
        ih (anchorInverseDerivative (T := T) hx (n + m) v)
      simp [anchorDerivativeProduct_succ, anchorInverseDerivativeProduct_succ, hih,
        anchorDerivative_apply_anchorInverseDerivative (T := T) (K := K) hs hx (n + m)]

theorem anchorInverseDerivativeProduct_comp_anchorDerivativeProduct
    (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m : ℕ) :
    (anchorInverseDerivativeProduct (T := T) hx n m).comp
        (anchorDerivativeProduct (T := T) hx n m) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  exact anchorInverseDerivativeProduct_apply_anchorDerivativeProduct
    (T := T) (K := K) hs hx n m v

theorem anchorDerivativeProduct_comp_anchorInverseDerivativeProduct
    (hs : HyperbolicStructure T K) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n m : ℕ) :
    (anchorDerivativeProduct (T := T) hx n m).comp
        (anchorInverseDerivativeProduct (T := T) hx n m) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  exact anchorDerivativeProduct_apply_anchorInverseDerivativeProduct
    (T := T) (K := K) hs hx n m v

def finiteProductPerturbation (B ξ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => B * finiteProductPerturbation B ξ n + ξ * B ^ n

theorem finiteProductPerturbation_nonneg {B ξ : ℝ} (hB : 0 ≤ B) (hξ : 0 ≤ ξ) :
    ∀ n : ℕ, 0 ≤ finiteProductPerturbation B ξ n := by
  intro n
  induction n with
  | zero =>
      simp [finiteProductPerturbation]
  | succ n ih =>
      simp [finiteProductPerturbation]
      exact add_nonneg (mul_nonneg hB ih) (mul_nonneg hξ (pow_nonneg hB n))

theorem finiteProductPerturbation_scale (B ξ : ℝ) :
    ∀ n : ℕ, finiteProductPerturbation B ξ n =
      ξ * finiteProductPerturbation B 1 n := by
  intro n
  induction n with
  | zero =>
      simp [finiteProductPerturbation]
  | succ n ih =>
      simp [finiteProductPerturbation, ih]
      ring

theorem finiteProductPerturbation_denom_pos {B : ℝ} (hB : 0 ≤ B) (n : ℕ) :
    0 < finiteProductPerturbation B 1 n + 1 := by
  have hnonneg : 0 ≤ finiteProductPerturbation B 1 n :=
    finiteProductPerturbation_nonneg hB (by norm_num) n
  linarith

theorem finiteProductPerturbation_scaled_step_le {B target : ℝ} (hB : 0 ≤ B)
    (htarget : 0 ≤ target) (n : ℕ) :
    finiteProductPerturbation B
        (target / (finiteProductPerturbation B 1 n + 1)) n ≤ target := by
  let A : ℝ := finiteProductPerturbation B 1 n
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact finiteProductPerturbation_nonneg hB (by norm_num) n
  have hden_pos : 0 < A + 1 := by linarith
  have hfrac_le_one : A / (A + 1) ≤ 1 := by
    exact (div_le_iff₀ hden_pos).mpr (by linarith)
  calc
    finiteProductPerturbation B (target / (finiteProductPerturbation B 1 n + 1)) n =
        (target / (A + 1)) * A := by
      dsimp [A]
      rw [finiteProductPerturbation_scale]
    _ = target * (A / (A + 1)) := by ring
    _ ≤ target * 1 := mul_le_mul_of_nonneg_left hfrac_le_one htarget
    _ = target := by ring

theorem fderiv_iterate_apply_norm_le_of_step_bound (hs : HyperbolicStructure T K)
    {B : ℝ} (hB_nonneg : 0 ≤ B) {x : E d}
    {m : ℕ}
    (hstep : ∀ j : ℕ, j < m →
      ‖fderiv ℝ (T : E d → E d) (((T : E d → E d)^[j]) x)‖ ≤ B) :
    ∀ v : E d,
      ‖fderiv ℝ ((T : E d → E d)^[m]) x v‖ ≤ B ^ m * ‖v‖ := by
  induction m with
  | zero =>
      intro v
      simp [Function.iterate_zero]
  | succ m ih =>
      intro v
      have hprev :
          ‖fderiv ℝ ((T : E d → E d)^[m]) x v‖ ≤ B ^ m * ‖v‖ :=
        ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self m))) v
      have hstep_m :
          ‖fderiv ℝ (T : E d → E d) (((T : E d → E d)^[m]) x)‖ ≤ B :=
        hstep m (Nat.lt_succ_self m)
      calc
        ‖fderiv ℝ ((T : E d → E d)^[m + 1]) x v‖ =
            ‖fderiv ℝ (T : E d → E d) (((T : E d → E d)^[m]) x)
              (fderiv ℝ ((T : E d → E d)^[m]) x v)‖ := by
          rw [fderiv_iterate_succ_apply (T := T) (K := K) hs]
        _ ≤ ‖fderiv ℝ (T : E d → E d) (((T : E d → E d)^[m]) x)‖ *
            ‖fderiv ℝ ((T : E d → E d)^[m]) x v‖ :=
          (fderiv ℝ (T : E d → E d) (((T : E d → E d)^[m]) x)).le_opNorm
            (fderiv ℝ ((T : E d → E d)^[m]) x v)
        _ ≤ B * (B ^ m * ‖v‖) :=
          mul_le_mul hstep_m hprev (norm_nonneg _) hB_nonneg
        _ = B ^ (m + 1) * ‖v‖ := by
          rw [pow_succ]
          ring

theorem anchorDerivativeProduct_fderiv_iterate_apply_norm_sub_le
    (hs : HyperbolicStructure T K) {ρ B ξ : ℝ} {x : ℕ → E d} {N : ℕ}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (hB_nonneg : 0 ≤ B) (hξ_nonneg : 0 ≤ ξ)
    (hanchor_step :
      ∀ n j : ℕ, j < N → ‖anchorDerivative (T := T) hx (n + j)‖ ≤ B)
    (htrue_step :
      ∀ n j : ℕ, j < N →
        ‖fderiv ℝ (T : E d → E d)
          (((T : E d → E d)^[j]) (localTubeAnchorSeq hx n))‖ ≤ B)
    (hstep_close :
      ∀ n j : ℕ, j < N →
        ‖anchorDerivative (T := T) hx (n + j) -
          fderiv ℝ (T : E d → E d)
            (((T : E d → E d)^[j]) (localTubeAnchorSeq hx n))‖ ≤ ξ) :
    ∀ n m : ℕ, m ≤ N → ∀ v : E d,
      ‖anchorDerivativeProduct (T := T) hx n m v -
          fderiv ℝ ((T : E d → E d)^[m]) (localTubeAnchorSeq hx n) v‖ ≤
        finiteProductPerturbation B ξ m * ‖v‖ := by
  intro n m
  induction m generalizing n with
  | zero =>
      intro _hmN v
      simp [finiteProductPerturbation]
  | succ m ih =>
      intro hmN v
      let A : E d →L[ℝ] E d := anchorDerivative (T := T) hx (n + m)
      let C : E d →L[ℝ] E d :=
        fderiv ℝ (T : E d → E d) (((T : E d → E d)^[m]) (localTubeAnchorSeq hx n))
      let P : E d →L[ℝ] E d := anchorDerivativeProduct (T := T) hx n m
      let Q : E d →L[ℝ] E d :=
        fderiv ℝ ((T : E d → E d)^[m]) (localTubeAnchorSeq hx n)
      have hm_lt_N : m < N := Nat.lt_of_succ_le hmN
      have hm_le_N : m ≤ N := Nat.le_of_lt hm_lt_N
      have hprev : ‖P v - Q v‖ ≤ finiteProductPerturbation B ξ m * ‖v‖ := by
        dsimp [P, Q]
        exact ih n hm_le_N v
      have hQ_norm : ‖Q v‖ ≤ B ^ m * ‖v‖ := by
        dsimp [Q]
        exact fderiv_iterate_apply_norm_le_of_step_bound (T := T) (K := K) hs
          hB_nonneg (x := localTubeAnchorSeq hx n)
          (fun j hj => htrue_step n j (Nat.lt_trans hj hm_lt_N)) v
      have hA_norm : ‖A‖ ≤ B := by
        dsimp [A]
        exact hanchor_step n m hm_lt_N
      have hAC_norm : ‖A - C‖ ≤ ξ := by
        dsimp [A, C]
        exact hstep_close n m hm_lt_N
      have hdecomp : A (P v) - C (Q v) = A (P v - Q v) + (A - C) (Q v) := by
        simp only [map_sub, sub_apply]
        abel
      have hfirst : ‖A (P v - Q v)‖ ≤ B * (finiteProductPerturbation B ξ m * ‖v‖) := by
        calc
          ‖A (P v - Q v)‖ ≤ ‖A‖ * ‖P v - Q v‖ := A.le_opNorm (P v - Q v)
          _ ≤ B * (finiteProductPerturbation B ξ m * ‖v‖) :=
            mul_le_mul hA_norm hprev (norm_nonneg _) hB_nonneg
      have hsecond : ‖(A - C) (Q v)‖ ≤ ξ * (B ^ m * ‖v‖) := by
        calc
          ‖(A - C) (Q v)‖ ≤ ‖A - C‖ * ‖Q v‖ := (A - C).le_opNorm (Q v)
          _ ≤ ξ * (B ^ m * ‖v‖) :=
            mul_le_mul hAC_norm hQ_norm (norm_nonneg _) hξ_nonneg
      calc
        ‖anchorDerivativeProduct (T := T) hx n (m + 1) v -
            fderiv ℝ ((T : E d → E d)^[m + 1]) (localTubeAnchorSeq hx n) v‖ =
            ‖A (P v) - C (Q v)‖ := by
          rw [anchorDerivativeProduct_succ_apply]
          rw [fderiv_iterate_succ_apply (T := T) (K := K) hs]
        _ = ‖A (P v - Q v) + (A - C) (Q v)‖ := by
          rw [hdecomp]
        _ ≤ ‖A (P v - Q v)‖ + ‖(A - C) (Q v)‖ := norm_add_le _ _
        _ ≤ B * (finiteProductPerturbation B ξ m * ‖v‖) +
            ξ * (B ^ m * ‖v‖) := add_le_add hfirst hsecond
        _ = finiteProductPerturbation B ξ (m + 1) * ‖v‖ := by
          simp [finiteProductPerturbation]
          ring

theorem anchorInverseDerivativeProduct_apply_norm_le_of_step_bound
    {ρ B : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) {n m : ℕ}
    (hB_nonneg : 0 ≤ B)
    (hstep : ∀ j : ℕ, j < m →
      ‖anchorInverseDerivative (T := T) hx (n + j)‖ ≤ B) :
    ∀ v : E d,
      ‖anchorInverseDerivativeProduct (T := T) hx n m v‖ ≤ B ^ m * ‖v‖ := by
  induction m with
  | zero =>
      intro v
      simp [anchorInverseDerivativeProduct_zero]
  | succ m ih =>
      intro v
      have hm_step :
          ‖anchorInverseDerivative (T := T) hx (n + m)‖ ≤ B :=
        hstep m (Nat.lt_succ_self m)
      have hprev :
          ‖anchorInverseDerivativeProduct (T := T) hx n m
              (anchorInverseDerivative (T := T) hx (n + m) v)‖ ≤
            B ^ m * ‖anchorInverseDerivative (T := T) hx (n + m) v‖ :=
        ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self m)))
          (anchorInverseDerivative (T := T) hx (n + m) v)
      have hstep_v :
          ‖anchorInverseDerivative (T := T) hx (n + m) v‖ ≤ B * ‖v‖ := by
        calc
          ‖anchorInverseDerivative (T := T) hx (n + m) v‖ ≤
              ‖anchorInverseDerivative (T := T) hx (n + m)‖ * ‖v‖ :=
            (anchorInverseDerivative (T := T) hx (n + m)).le_opNorm v
          _ ≤ B * ‖v‖ :=
            mul_le_mul_of_nonneg_right hm_step (norm_nonneg v)
      calc
        ‖anchorInverseDerivativeProduct (T := T) hx n (m + 1) v‖ =
            ‖anchorInverseDerivativeProduct (T := T) hx n m
              (anchorInverseDerivative (T := T) hx (n + m) v)‖ := by
          rw [anchorInverseDerivativeProduct_succ_apply]
        _ ≤ B ^ m * ‖anchorInverseDerivative (T := T) hx (n + m) v‖ := hprev
        _ ≤ B ^ m * (B * ‖v‖) :=
          mul_le_mul_of_nonneg_left hstep_v (pow_nonneg hB_nonneg m)
        _ = B ^ (m + 1) * ‖v‖ := by
          rw [pow_succ]
          ring

theorem anchorInverseDerivativeProduct_fderiv_symm_iterate_apply_norm_sub_le
    (hs : HyperbolicStructure T K) {ρ B ξ : ℝ} {x : ℕ → E d} {N : ℕ}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (hB_nonneg : 0 ≤ B) (hξ_nonneg : 0 ≤ ξ)
    (hanchor_step :
      ∀ n j : ℕ, j < N → ‖anchorInverseDerivative (T := T) hx (n + j)‖ ≤ B)
    (htrue_step :
      ∀ n j : ℕ, j < N →
        ‖fderiv ℝ (T.symm : E d → E d)
          (((T : E d → E d)^[j + 1]) (localTubeAnchorSeq hx n))‖ ≤ B)
    (hstep_close :
      ∀ n j : ℕ, j < N →
        ‖anchorInverseDerivative (T := T) hx (n + j) -
          fderiv ℝ (T.symm : E d → E d)
            (((T : E d → E d)^[j + 1]) (localTubeAnchorSeq hx n))‖ ≤ ξ) :
    ∀ n m : ℕ, m ≤ N → ∀ v : E d,
      ‖anchorInverseDerivativeProduct (T := T) hx n m v -
          fderiv ℝ ((T.symm : E d → E d)^[m])
            (((T : E d → E d)^[m]) (localTubeAnchorSeq hx n)) v‖ ≤
        finiteProductPerturbation B ξ m * ‖v‖ := by
  intro n m
  induction m generalizing n with
  | zero =>
      intro _hmN v
      simp [finiteProductPerturbation]
  | succ m ih =>
      intro hmN v
      let A : E d →L[ℝ] E d := anchorInverseDerivative (T := T) hx (n + m)
      let C : E d →L[ℝ] E d :=
        fderiv ℝ (T.symm : E d → E d)
          (((T : E d → E d)^[m + 1]) (localTubeAnchorSeq hx n))
      let P : E d →L[ℝ] E d := anchorInverseDerivativeProduct (T := T) hx n m
      let Q : E d →L[ℝ] E d :=
        fderiv ℝ ((T.symm : E d → E d)^[m])
          (((T : E d → E d)^[m]) (localTubeAnchorSeq hx n))
      have hm_lt_N : m < N := Nat.lt_of_succ_le hmN
      have hm_le_N : m ≤ N := Nat.le_of_lt hm_lt_N
      have hprev_C :
          ‖P (C v) - Q (C v)‖ ≤ finiteProductPerturbation B ξ m * ‖C v‖ := by
        dsimp [P, Q]
        exact ih n hm_le_N (C v)
      have hC_norm : ‖C v‖ ≤ B * ‖v‖ := by
        calc
          ‖C v‖ ≤ ‖C‖ * ‖v‖ := C.le_opNorm v
          _ ≤ B * ‖v‖ :=
            mul_le_mul_of_nonneg_right (by
              dsimp [C]
              exact htrue_step n m hm_lt_N) (norm_nonneg v)
      have hP_diff_norm :
          ‖P ((A - C) v)‖ ≤ B ^ m * (ξ * ‖v‖) := by
        have hP_bound :
            ‖P ((A - C) v)‖ ≤ B ^ m * ‖(A - C) v‖ := by
          dsimp [P]
          exact anchorInverseDerivativeProduct_apply_norm_le_of_step_bound
            (T := T) (K := K) hx hB_nonneg
            (fun j hj => hanchor_step n j (Nat.lt_trans hj hm_lt_N)) ((A - C) v)
        have hAC_v : ‖(A - C) v‖ ≤ ξ * ‖v‖ := by
          calc
            ‖(A - C) v‖ ≤ ‖A - C‖ * ‖v‖ := (A - C).le_opNorm v
            _ ≤ ξ * ‖v‖ :=
              mul_le_mul_of_nonneg_right (by
                dsimp [A, C]
                exact hstep_close n m hm_lt_N) (norm_nonneg v)
        exact hP_bound.trans
          (mul_le_mul_of_nonneg_left hAC_v (pow_nonneg hB_nonneg m))
      have hprev_bound :
          ‖P (C v) - Q (C v)‖ ≤ finiteProductPerturbation B ξ m * (B * ‖v‖) :=
        hprev_C.trans
          (mul_le_mul_of_nonneg_left hC_norm
            (finiteProductPerturbation_nonneg hB_nonneg hξ_nonneg m))
      have hdecomp : P (A v) - Q (C v) = P ((A - C) v) + (P (C v) - Q (C v)) := by
        simp only [sub_apply, map_sub]
        abel
      calc
        ‖anchorInverseDerivativeProduct (T := T) hx n (m + 1) v -
            fderiv ℝ ((T.symm : E d → E d)^[m + 1])
              (((T : E d → E d)^[m + 1]) (localTubeAnchorSeq hx n)) v‖ =
            ‖P (A v) - Q (C v)‖ := by
          rw [anchorInverseDerivativeProduct_succ_apply]
          rw [fderiv_symm_iterate_succ_forward_apply (T := T) (K := K) hs]
        _ = ‖P ((A - C) v) + (P (C v) - Q (C v))‖ := by
          rw [hdecomp]
        _ ≤ ‖P ((A - C) v)‖ + ‖P (C v) - Q (C v)‖ := norm_add_le _ _
        _ ≤ B ^ m * (ξ * ‖v‖) + finiteProductPerturbation B ξ m * (B * ‖v‖) :=
          add_le_add hP_diff_norm hprev_bound
        _ = finiteProductPerturbation B ξ (m + 1) * ‖v‖ := by
          simp [finiteProductPerturbation]
          ring

theorem anchorStableProjection_mem (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (n : ℕ) (v : E d) :
    anchorStableProjection hs hx n v ∈ hs.stable (localTubeAnchorSeq hx n) := by
  simp [anchorStableProjection]

theorem anchorUnstableProjection_mem (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (n : ℕ) (v : E d) :
    anchorUnstableProjection hs hx n v ∈ hs.unstable (localTubeAnchorSeq hx n) := by
  simp [anchorUnstableProjection]

theorem anchorProjection_decomp (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (n : ℕ) (v : E d) :
    anchorStableProjection hs hx n v + anchorUnstableProjection hs hx n v = v := by
  simpa [anchorStableProjection, anchorUnstableProjection] using
    stable_add_unstable_projection hs (localTubeAnchorSeq_mem hx n) v

theorem anchorDerivative_stable_mem (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    {n : ℕ} {v : E d} (hv : v ∈ hs.stable (localTubeAnchorSeq hx n)) :
    anchorDerivative (T := T) hx n v ∈ hs.stable (T (localTubeAnchorSeq hx n)) := by
  simpa [anchorDerivative] using
    stable_fderiv_mem hs (localTubeAnchorSeq_mem hx n) hv

theorem anchorDerivative_unstable_mem (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    {n : ℕ} {v : E d} (hv : v ∈ hs.unstable (localTubeAnchorSeq hx n)) :
    anchorDerivative (T := T) hx n v ∈ hs.unstable (T (localTubeAnchorSeq hx n)) := by
  simpa [anchorDerivative] using
    unstable_fderiv_mem hs (localTubeAnchorSeq_mem hx n) hv

theorem localTubeAnchorSeq_eq_iterate_of_step {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hstep : ∀ n : ℕ, localTubeAnchorSeq hx (n + 1) = T (localTubeAnchorSeq hx n)) :
    ∀ n : ℕ, localTubeAnchorSeq hx n =
      ((T : E d → E d)^[n]) (localTubeAnchorSeq hx 0) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [hstep n, ih]
      simp [Function.iterate_succ_apply']

theorem anchorDerivative_stable_mem_next_of_step (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hstep : ∀ n : ℕ, localTubeAnchorSeq hx (n + 1) = T (localTubeAnchorSeq hx n))
    {n : ℕ} {v : E d} (hv : v ∈ hs.stable (localTubeAnchorSeq hx n)) :
    anchorDerivative (T := T) hx n v ∈ hs.stable (localTubeAnchorSeq hx (n + 1)) := by
  simpa [hstep n] using anchorDerivative_stable_mem (T := T) (K := K) hs hx hv

theorem anchorDerivative_unstable_mem_next_of_step (hs : HyperbolicStructure T K)
    {ρ : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hstep : ∀ n : ℕ, localTubeAnchorSeq hx (n + 1) = T (localTubeAnchorSeq hx n))
    {n : ℕ} {v : E d} (hv : v ∈ hs.unstable (localTubeAnchorSeq hx n)) :
    anchorDerivative (T := T) hx n v ∈ hs.unstable (localTubeAnchorSeq hx (n + 1)) := by
  simpa [hstep n] using anchorDerivative_unstable_mem (T := T) (K := K) hs hx hv

theorem anchorDerivative_stable_offDiagonal_le (hs : HyperbolicStructure T K)
    {ρ η : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hstable_leak : ∀ n : ℕ, ∀ v : E d,
      v ∈ hs.stable (T (localTubeAnchorSeq hx n)) →
        ‖unstableProjection hs (localTubeAnchorSeq hx (n + 1))
            (localTubeAnchorSeq_mem hx (n + 1)) v‖ ≤ η * ‖v‖)
    {n : ℕ} {v : E d} (hv : v ∈ hs.stable (localTubeAnchorSeq hx n)) :
    ‖anchorUnstableProjection hs hx (n + 1) (anchorDerivative (T := T) hx n v)‖ ≤
      η * ‖anchorDerivative (T := T) hx n v‖ := by
  have hmem :
      anchorDerivative (T := T) hx n v ∈ hs.stable (T (localTubeAnchorSeq hx n)) :=
    anchorDerivative_stable_mem (T := T) (K := K) hs hx hv
  simpa [anchorUnstableProjection] using
    hstable_leak n (anchorDerivative (T := T) hx n v) hmem

theorem anchorDerivative_unstable_offDiagonal_le (hs : HyperbolicStructure T K)
    {ρ η : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hunstable_leak : ∀ n : ℕ, ∀ v : E d,
      v ∈ hs.unstable (T (localTubeAnchorSeq hx n)) →
        ‖stableProjection hs (localTubeAnchorSeq hx (n + 1))
            (localTubeAnchorSeq_mem hx (n + 1)) v‖ ≤ η * ‖v‖)
    {n : ℕ} {v : E d} (hv : v ∈ hs.unstable (localTubeAnchorSeq hx n)) :
    ‖anchorStableProjection hs hx (n + 1) (anchorDerivative (T := T) hx n v)‖ ≤
      η * ‖anchorDerivative (T := T) hx n v‖ := by
  have hmem :
      anchorDerivative (T := T) hx n v ∈ hs.unstable (T (localTubeAnchorSeq hx n)) :=
    anchorDerivative_unstable_mem (T := T) (K := K) hs hx hv
  simpa [anchorStableProjection] using
    hunstable_leak n (anchorDerivative (T := T) hx n v) hmem

theorem anchorDerivative_offDiagonal_le (hs : HyperbolicStructure T K)
    {ρ η : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hstable_leak : ∀ n : ℕ, ∀ v : E d,
      v ∈ hs.stable (T (localTubeAnchorSeq hx n)) →
        ‖unstableProjection hs (localTubeAnchorSeq hx (n + 1))
            (localTubeAnchorSeq_mem hx (n + 1)) v‖ ≤ η * ‖v‖)
    (hunstable_leak : ∀ n : ℕ, ∀ v : E d,
      v ∈ hs.unstable (T (localTubeAnchorSeq hx n)) →
        ‖stableProjection hs (localTubeAnchorSeq hx (n + 1))
            (localTubeAnchorSeq_mem hx (n + 1)) v‖ ≤ η * ‖v‖)
    {n : ℕ} {vs vu : E d}
    (hvs : vs ∈ hs.stable (localTubeAnchorSeq hx n))
    (hvu : vu ∈ hs.unstable (localTubeAnchorSeq hx n)) :
    ‖anchorUnstableProjection hs hx (n + 1) (anchorDerivative (T := T) hx n vs)‖ ≤
        η * ‖anchorDerivative (T := T) hx n vs‖ ∧
      ‖anchorStableProjection hs hx (n + 1) (anchorDerivative (T := T) hx n vu)‖ ≤
        η * ‖anchorDerivative (T := T) hx n vu‖ := by
  constructor
  · exact anchorDerivative_stable_offDiagonal_le (T := T) (K := K) hs hx hstable_leak hvs
  · exact anchorDerivative_unstable_offDiagonal_le (T := T) (K := K) hs hx hunstable_leak hvu

theorem anchorProjection_apply_norm_le_of_bound (hs : HyperbolicStructure T K)
    {ρ M : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hM_nonneg : 0 ≤ M)
    (hproj : ∀ z : E d, ∀ hz : z ∈ K, ∀ v : E d,
      ‖stableProjection hs z hz v‖ ≤ M * ‖v‖ ∧
        ‖unstableProjection hs z hz v‖ ≤ M * ‖v‖)
    (b : CorrectionSeq d) (n : ℕ) :
    ‖anchorStableProjection hs hx n (b n)‖ ≤ M * ‖b‖ ∧
      ‖anchorUnstableProjection hs hx n (b n)‖ ≤ M * ‖b‖ := by
  have hbn : ‖b n‖ ≤ ‖b‖ := correctionSeq_apply_norm_le_norm b n
  constructor
  · exact ((hproj (localTubeAnchorSeq hx n) (localTubeAnchorSeq_mem hx n) (b n)).1).trans
      (mul_le_mul_of_nonneg_left hbn hM_nonneg)
  · exact ((hproj (localTubeAnchorSeq hx n) (localTubeAnchorSeq_mem hx n) (b n)).2).trans
      (mul_le_mul_of_nonneg_left hbn hM_nonneg)

theorem anchorDerivative_projected_diagonal_norm_le (hs : HyperbolicStructure T K)
    {ρ η L : ℝ} {x : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hη_nonneg : 0 ≤ η)
    (hA_bound : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ L)
    (hoffdiag : ∀ n : ℕ, ∀ vs vu : E d,
      vs ∈ hs.stable (localTubeAnchorSeq hx n) →
        vu ∈ hs.unstable (localTubeAnchorSeq hx n) →
          ‖anchorUnstableProjection hs hx (n + 1) (anchorDerivative (T := T) hx n vs)‖ ≤
              η * ‖anchorDerivative (T := T) hx n vs‖ ∧
            ‖anchorStableProjection hs hx (n + 1) (anchorDerivative (T := T) hx n vu)‖ ≤
              η * ‖anchorDerivative (T := T) hx n vu‖)
    {n : ℕ} {vs vu : E d}
    (hvs : vs ∈ hs.stable (localTubeAnchorSeq hx n))
    (hvu : vu ∈ hs.unstable (localTubeAnchorSeq hx n)) :
    ‖anchorStableProjection hs hx (n + 1) (anchorDerivative (T := T) hx n vs)‖ ≤
        (1 + η) * L * ‖vs‖ ∧
      ‖anchorUnstableProjection hs hx (n + 1) (anchorDerivative (T := T) hx n vu)‖ ≤
        (1 + η) * L * ‖vu‖ := by
  constructor
  · let A := anchorDerivative (T := T) hx n
    let Q := anchorUnstableProjection hs hx (n + 1) (A vs)
    have hQ : ‖Q‖ ≤ η * ‖A vs‖ := by
      simpa [A, Q] using (hoffdiag n vs 0 hvs (zero_mem (hs.unstable (localTubeAnchorSeq hx n)))).1
    have hdecomp := anchorProjection_decomp hs hx (n + 1) (A vs)
    have hp_eq : anchorStableProjection hs hx (n + 1) (A vs) = A vs - Q := by
      calc
        anchorStableProjection hs hx (n + 1) (A vs) =
            (anchorStableProjection hs hx (n + 1) (A vs) +
                anchorUnstableProjection hs hx (n + 1) (A vs)) - Q := by
          dsimp [Q]
          abel
        _ = A vs - Q := by rw [hdecomp]
    have hA_vs : ‖A vs‖ ≤ L * ‖vs‖ := by
      calc
        ‖A vs‖ ≤ ‖A‖ * ‖vs‖ := A.le_opNorm vs
        _ ≤ L * ‖vs‖ := mul_le_mul_of_nonneg_right (hA_bound n) (norm_nonneg vs)
    have hfactor_nonneg : 0 ≤ 1 + η := by linarith
    calc
      ‖anchorStableProjection hs hx (n + 1) (A vs)‖ = ‖A vs - Q‖ := by rw [hp_eq]
      _ ≤ ‖A vs‖ + ‖Q‖ := norm_sub_le (A vs) Q
      _ ≤ ‖A vs‖ + η * ‖A vs‖ := add_le_add le_rfl hQ
      _ = (1 + η) * ‖A vs‖ := by ring
      _ ≤ (1 + η) * (L * ‖vs‖) := mul_le_mul_of_nonneg_left hA_vs hfactor_nonneg
      _ = (1 + η) * L * ‖vs‖ := by ring
  · let A := anchorDerivative (T := T) hx n
    let P := anchorStableProjection hs hx (n + 1) (A vu)
    have hP : ‖P‖ ≤ η * ‖A vu‖ := by
      simpa [A, P] using (hoffdiag n 0 vu (zero_mem (hs.stable (localTubeAnchorSeq hx n))) hvu).2
    have hdecomp := anchorProjection_decomp hs hx (n + 1) (A vu)
    have hq_eq : anchorUnstableProjection hs hx (n + 1) (A vu) = A vu - P := by
      calc
        anchorUnstableProjection hs hx (n + 1) (A vu) =
            (anchorStableProjection hs hx (n + 1) (A vu) +
                anchorUnstableProjection hs hx (n + 1) (A vu)) - P := by
          dsimp [P]
          abel
        _ = A vu - P := by rw [hdecomp]
    have hA_vu : ‖A vu‖ ≤ L * ‖vu‖ := by
      calc
        ‖A vu‖ ≤ ‖A‖ * ‖vu‖ := A.le_opNorm vu
        _ ≤ L * ‖vu‖ := mul_le_mul_of_nonneg_right (hA_bound n) (norm_nonneg vu)
    have hfactor_nonneg : 0 ≤ 1 + η := by linarith
    calc
      ‖anchorUnstableProjection hs hx (n + 1) (A vu)‖ = ‖A vu - P‖ := by rw [hq_eq]
      _ ≤ ‖A vu‖ + ‖P‖ := norm_sub_le (A vu) P
      _ ≤ ‖A vu‖ + η * ‖A vu‖ := add_le_add le_rfl hP
      _ = (1 + η) * ‖A vu‖ := by ring
      _ ≤ (1 + η) * (L * ‖vu‖) := mul_le_mul_of_nonneg_left hA_vu hfactor_nonneg
      _ = (1 + η) * L * ‖vu‖ := by ring

theorem selectedForwardStableBlock_endpoint_projection_le
    (hs : HyperbolicStructure T K)
    {ρ η M ξ μ leakRadius : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hη_nonneg : 0 ≤ η) (hM_nonneg : 0 ≤ M)
    (hproj : ∀ z : E d, ∀ hz : z ∈ K, ∀ v : E d,
      ‖stableProjection hs z hz v‖ ≤ M * ‖v‖ ∧
        ‖unstableProjection hs z hz v‖ ≤ M * ‖v‖)
    (hleak : ∀ z : E d, z ∈ K → ∀ y : E d, ∀ hy : y ∈ K,
      ‖y - z‖ < leakRadius → ∀ v : E d, v ∈ hs.stable z →
        ‖unstableProjection hs y hy v‖ ≤ η * ‖v‖)
    {n N : ℕ}
    (hendpoint : ‖localTubeAnchorSeq hx (n + N) -
        ((T : E d → E d)^[N]) (localTubeAnchorSeq hx n)‖ < leakRadius)
    (hpert : ∀ v : E d,
      ‖anchorDerivativeProduct (T := T) hx n N v -
          fderiv ℝ ((T : E d → E d)^[N]) (localTubeAnchorSeq hx n) v‖ ≤
        ξ * ‖v‖)
    (hexact : ∀ v : E d, v ∈ hs.stable (localTubeAnchorSeq hx n) →
      ‖fderiv ℝ ((T : E d → E d)^[N]) (localTubeAnchorSeq hx n) v‖ ≤
        μ * ‖v‖)
    {vs : E d} (hvs : vs ∈ hs.stable (localTubeAnchorSeq hx n)) :
    ‖anchorStableProjection hs hx (n + N)
        (anchorDerivativeProduct (T := T) hx n N vs)‖ ≤
        M * (ξ * ‖vs‖ + μ * ‖vs‖) ∧
      ‖anchorUnstableProjection hs hx (n + N)
        (anchorDerivativeProduct (T := T) hx n N vs)‖ ≤
        M * (ξ * ‖vs‖) + η * (μ * ‖vs‖) := by
  let P : E d →L[ℝ] E d := anchorDerivativeProduct (T := T) hx n N
  let Q : E d →L[ℝ] E d :=
    fderiv ℝ ((T : E d → E d)^[N]) (localTubeAnchorSeq hx n)
  have hQ_mem : Q vs ∈ hs.stable (((T : E d → E d)^[N]) (localTubeAnchorSeq hx n)) := by
    dsimp [Q]
    exact stable_fderiv_iterate_mem (T := T) (K := K) hs
      (localTubeAnchorSeq_mem hx n) hvs N
  have hdiff : ‖P vs - Q vs‖ ≤ ξ * ‖vs‖ := by
    dsimp [P, Q]
    exact hpert vs
  have hQ_norm : ‖Q vs‖ ≤ μ * ‖vs‖ := by
    dsimp [Q]
    exact hexact vs hvs
  have hP_decomp : P vs = (P vs - Q vs) + Q vs := by
    abel
  have hP_norm : ‖P vs‖ ≤ ξ * ‖vs‖ + μ * ‖vs‖ := by
    calc
      ‖P vs‖ = ‖(P vs - Q vs) + Q vs‖ := congrArg norm hP_decomp
      _ ≤ ‖P vs - Q vs‖ + ‖Q vs‖ := norm_add_le _ _
      _ ≤ ξ * ‖vs‖ + μ * ‖vs‖ := add_le_add hdiff hQ_norm
  have hselected_mem : localTubeAnchorSeq hx (n + N) ∈ K :=
    localTubeAnchorSeq_mem hx (n + N)
  have hexact_mem :
      ((T : E d → E d)^[N]) (localTubeAnchorSeq hx n) ∈ K :=
    forward_iterate_mem hs (localTubeAnchorSeq_mem hx n) N
  constructor
  · exact ((hproj (localTubeAnchorSeq hx (n + N)) hselected_mem (P vs)).1).trans
      (mul_le_mul_of_nonneg_left hP_norm hM_nonneg)
  · let Pu : E d →ₗ[ℝ] E d := anchorUnstableProjection hs hx (n + N)
    have hPu_decomp :
        Pu (P vs) = Pu (P vs - Q vs) + Pu (Q vs) := by
      calc
        Pu (P vs) = Pu ((P vs - Q vs) + Q vs) := congrArg Pu hP_decomp
        _ = Pu (P vs - Q vs) + Pu (Q vs) := map_add Pu _ _
    have hPu_diff : ‖Pu (P vs - Q vs)‖ ≤ M * (ξ * ‖vs‖) := by
      dsimp [Pu, anchorUnstableProjection]
      exact ((hproj (localTubeAnchorSeq hx (n + N)) hselected_mem (P vs - Q vs)).2).trans
        (mul_le_mul_of_nonneg_left hdiff hM_nonneg)
    have hPu_Q : ‖Pu (Q vs)‖ ≤ η * (μ * ‖vs‖) := by
      have hleak_Q :
          ‖unstableProjection hs (localTubeAnchorSeq hx (n + N)) hselected_mem
              (Q vs)‖ ≤ η * ‖Q vs‖ :=
        hleak (((T : E d → E d)^[N]) (localTubeAnchorSeq hx n)) hexact_mem
          (localTubeAnchorSeq hx (n + N)) hselected_mem hendpoint (Q vs) hQ_mem
      dsimp [Pu, anchorUnstableProjection]
      exact hleak_Q.trans (mul_le_mul_of_nonneg_left hQ_norm hη_nonneg)
    calc
      ‖Pu (P vs)‖ = ‖Pu (P vs - Q vs) + Pu (Q vs)‖ := congrArg norm hPu_decomp
      _ ≤ ‖Pu (P vs - Q vs)‖ + ‖Pu (Q vs)‖ := norm_add_le _ _
      _ ≤ M * (ξ * ‖vs‖) + η * (μ * ‖vs‖) := add_le_add hPu_diff hPu_Q

theorem selectedBackwardUnstableBlock_endpoint_projection_le
    (hs : HyperbolicStructure T K)
    {ρ η M L μ leakRadius : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (_hη_nonneg : 0 ≤ η) (hM_nonneg : 0 ≤ M) (hL_nonneg : 0 ≤ L)
    (hμ_nonneg : 0 ≤ μ)
    (hproj : ∀ z : E d, ∀ hz : z ∈ K, ∀ v : E d,
      ‖stableProjection hs z hz v‖ ≤ M * ‖v‖ ∧
        ‖unstableProjection hs z hz v‖ ≤ M * ‖v‖)
    (hleak : ∀ z : E d, z ∈ K → ∀ y : E d, ∀ hy : y ∈ K,
      ‖y - z‖ < leakRadius → ∀ v : E d, v ∈ hs.unstable z →
        ‖stableProjection hs y hy v‖ ≤ η * ‖v‖)
    {n N : ℕ}
    (hendpoint : ‖localTubeAnchorSeq hx (n + N) -
        ((T : E d → E d)^[N]) (localTubeAnchorSeq hx n)‖ < leakRadius)
    (hback_bound : ∀ v : E d,
      ‖anchorInverseDerivativeProduct (T := T) hx n N v‖ ≤ L * ‖v‖)
    (hcontract : ∀ v : E d,
      v ∈ hs.unstable (((T : E d → E d)^[N]) (localTubeAnchorSeq hx n)) →
        ‖anchorInverseDerivativeProduct (T := T) hx n N v‖ ≤ μ * ‖v‖)
    {vu : E d} (hvu : vu ∈ hs.unstable (localTubeAnchorSeq hx (n + N))) :
    ‖anchorStableProjection hs hx n
        (anchorInverseDerivativeProduct (T := T) hx n N vu)‖ ≤
        M * (L * (η * ‖vu‖) + μ * (M * ‖vu‖)) ∧
      ‖anchorUnstableProjection hs hx n
        (anchorInverseDerivativeProduct (T := T) hx n N vu)‖ ≤
        M * (L * (η * ‖vu‖) + μ * (M * ‖vu‖)) := by
  let B : E d →L[ℝ] E d := anchorInverseDerivativeProduct (T := T) hx n N
  let exactEndpoint : E d := ((T : E d → E d)^[N]) (localTubeAnchorSeq hx n)
  let selectedEndpoint : E d := localTubeAnchorSeq hx (n + N)
  have hexact_mem : exactEndpoint ∈ K := by
    dsimp [exactEndpoint]
    exact forward_iterate_mem hs (localTubeAnchorSeq_mem hx n) N
  have hselected_mem : selectedEndpoint ∈ K := by
    dsimp [selectedEndpoint]
    exact localTubeAnchorSeq_mem hx (n + N)
  let su : E d := stableProjection hs exactEndpoint hexact_mem vu
  let uu : E d := unstableProjection hs exactEndpoint hexact_mem vu
  have hdecomp : su + uu = vu := by
    dsimp [su, uu]
    exact stable_add_unstable_projection hs hexact_mem vu
  have hB_decomp : B vu = B su + B uu := by
    calc
      B vu = B (su + uu) := by rw [hdecomp]
      _ = B su + B uu := map_add B su uu
  have hendpoint_rev : ‖exactEndpoint - selectedEndpoint‖ < leakRadius := by
    dsimp [exactEndpoint, selectedEndpoint]
    simpa [norm_sub_rev] using hendpoint
  have hsu_norm : ‖su‖ ≤ η * ‖vu‖ := by
    dsimp [su, exactEndpoint, selectedEndpoint] at hendpoint_rev ⊢
    exact hleak (localTubeAnchorSeq hx (n + N)) (localTubeAnchorSeq_mem hx (n + N))
      (((T : E d → E d)^[N]) (localTubeAnchorSeq hx n)) hexact_mem
      hendpoint_rev vu hvu
  have huu_norm : ‖uu‖ ≤ M * ‖vu‖ := by
    dsimp [uu]
    exact (hproj exactEndpoint hexact_mem vu).2
  have hBS_norm : ‖B su‖ ≤ L * (η * ‖vu‖) := by
    exact (hback_bound su).trans (mul_le_mul_of_nonneg_left hsu_norm hL_nonneg)
  have huu_mem : uu ∈ hs.unstable exactEndpoint := by
    dsimp [uu]
    exact unstableProjection_mem hs hexact_mem vu
  have hBU_norm : ‖B uu‖ ≤ μ * (M * ‖vu‖) := by
    exact (hcontract uu huu_mem).trans (mul_le_mul_of_nonneg_left huu_norm hμ_nonneg)
  have hB_norm : ‖B vu‖ ≤ L * (η * ‖vu‖) + μ * (M * ‖vu‖) := by
    calc
      ‖B vu‖ = ‖B su + B uu‖ := congrArg norm hB_decomp
      _ ≤ ‖B su‖ + ‖B uu‖ := norm_add_le _ _
      _ ≤ L * (η * ‖vu‖) + μ * (M * ‖vu‖) := add_le_add hBS_norm hBU_norm
  constructor
  · exact ((hproj (localTubeAnchorSeq hx n) (localTubeAnchorSeq_mem hx n) (B vu)).1).trans
      (mul_le_mul_of_nonneg_left hB_norm hM_nonneg)
  · exact ((hproj (localTubeAnchorSeq hx n) (localTubeAnchorSeq_mem hx n) (B vu)).2).trans
      (mul_le_mul_of_nonneg_left hB_norm hM_nonneg)

theorem endpointLeak_first_term_le {M L : ℝ}
    (hM_nonneg : 0 ≤ M) (hL_nonneg : 0 ≤ L) :
    M * (L * ((1 / 64 : ℝ) / ((M + 1) * (L + 1)))) ≤ (1 / 64 : ℝ) := by
  have hden_pos : 0 < (M + 1) * (L + 1) := by
    exact mul_pos (by linarith) (by linarith)
  have hprod_le : M * L ≤ (M + 1) * (L + 1) := by
    nlinarith [hM_nonneg, hL_nonneg]
  have hratio_le_one :
      (M * L) / ((M + 1) * (L + 1)) ≤ 1 := by
    exact (div_le_one hden_pos).mpr hprod_le
  calc
    M * (L * ((1 / 64 : ℝ) / ((M + 1) * (L + 1)))) =
        (1 / 64 : ℝ) * ((M * L) / ((M + 1) * (L + 1))) := by
      field_simp [ne_of_gt hden_pos]
    _ ≤ (1 / 64 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hratio_le_one (by norm_num)
    _ = (1 / 64 : ℝ) := by norm_num

theorem endpointLeakTol_le_one {M L : ℝ}
    (hM_nonneg : 0 ≤ M) (hL_nonneg : 0 ≤ L) :
    ((1 / 64 : ℝ) / ((M + 1) * (L + 1))) ≤ 1 := by
  have hden_pos : 0 < (M + 1) * (L + 1) := by
    exact mul_pos (by linarith) (by linarith)
  have hM_one : (1 : ℝ) ≤ M + 1 := by linarith
  have hL_one : (1 : ℝ) ≤ L + 1 := by linarith
  have hden_ge_one : (1 : ℝ) ≤ (M + 1) * (L + 1) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (M + 1) * (L + 1) :=
        mul_le_mul hM_one hL_one (by norm_num) (by linarith)
  have hnum_le_den : (1 / 64 : ℝ) ≤ (M + 1) * (L + 1) :=
    (by norm_num : (1 / 64 : ℝ) ≤ 1).trans hden_ge_one
  exact (div_le_one hden_pos).mpr hnum_le_den

theorem selectedGreenBound_ge_M {M C rate : ℝ}
    (hM_pos : 0 < M) (hC_pos : 0 < C) (hrate_lt_one : rate < 1) :
    M ≤ 64 * M * M + 64 * M + 4 * M * C / (1 - rate) + 1 := by
  have hden_pos : 0 < 1 - rate := sub_pos.mpr hrate_lt_one
  have hquad_nonneg : 0 ≤ 64 * M * M := by
    exact mul_nonneg (mul_nonneg (by norm_num) hM_pos.le) hM_pos.le
  have hlinear_ge : M ≤ 64 * M := by
    calc
      M = 1 * M := by ring
      _ ≤ 64 * M := mul_le_mul_of_nonneg_right (by norm_num) hM_pos.le
  have hnum_nonneg : 0 ≤ 4 * M * C := by
    exact mul_nonneg (mul_nonneg (by norm_num) hM_pos.le) hC_pos.le
  have hmain_nonneg : 0 ≤ 4 * M * C / (1 - rate) := by
    exact div_nonneg hnum_nonneg hden_pos.le
  linarith

theorem selectedGreenBound_ge_M_add_one {M C rate : ℝ}
    (hM_pos : 0 < M) (hC_pos : 0 < C) (hrate_lt_one : rate < 1) :
    M + 1 ≤ 64 * M * M + 64 * M + 4 * M * C / (1 - rate) + 1 := by
  have hden_pos : 0 < 1 - rate := sub_pos.mpr hrate_lt_one
  have hquad_nonneg : 0 ≤ 64 * M * M := by
    exact mul_nonneg (mul_nonneg (by norm_num) hM_pos.le) hM_pos.le
  have hlinear_ge : M ≤ 64 * M := by
    calc
      M = 1 * M := by ring
      _ ≤ 64 * M := mul_le_mul_of_nonneg_right (by norm_num) hM_pos.le
  have hnum_nonneg : 0 ≤ 4 * M * C := by
    exact mul_nonneg (mul_nonneg (by norm_num) hM_pos.le) hC_pos.le
  have hmain_nonneg : 0 ≤ 4 * M * C / (1 - rate) := by
    exact div_nonneg hnum_nonneg hden_pos.le
  linarith

theorem endpointLeak_second_term_le {M η G : ℝ}
    (hM_nonneg : 0 ≤ M) (hη_nonneg : 0 ≤ η)
    (hGη : G * η = (1 / 4 : ℝ)) (hG_ge_quad : 64 * M * M ≤ G) :
    M * ((η / 8) * M) ≤ (1 / 64 : ℝ) := by
  have hM_sq_nonneg : 0 ≤ M * M := mul_nonneg hM_nonneg hM_nonneg
  have hG_ge_two_quad : 2 * (M * M) ≤ G := by
    calc
      2 * (M * M) ≤ 64 * (M * M) :=
        mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 64) hM_sq_nonneg
      _ = 64 * M * M := by ring
      _ ≤ G := hG_ge_quad
  have hηG : η * G = (1 / 4 : ℝ) := by
    rw [mul_comm]
    exact hGη
  have hη_mul_two_quad : η * (2 * (M * M)) ≤ η * G :=
    mul_le_mul_of_nonneg_left hG_ge_two_quad hη_nonneg
  have hη_two_quad_le : 2 * (η * (M * M)) ≤ (1 / 4 : ℝ) := by
    calc
      2 * (η * (M * M)) = η * (2 * (M * M)) := by ring
      _ ≤ η * G := hη_mul_two_quad
      _ = (1 / 4 : ℝ) := hηG
  have hη_quad_le : η * (M * M) ≤ (1 / 8 : ℝ) := by
    have htwo : η * (M * M) * 2 ≤ (1 / 4 : ℝ) := by
      calc
        η * (M * M) * 2 = 2 * (η * (M * M)) := by ring
        _ ≤ (1 / 4 : ℝ) := hη_two_quad_le
    have hdiv : η * (M * M) ≤ (1 / 4 : ℝ) / 2 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr htwo
    calc
      η * (M * M) ≤ (1 / 4 : ℝ) / 2 := hdiv
      _ = (1 / 8 : ℝ) := by norm_num
  calc
    M * ((η / 8) * M) = (η * (M * M)) / 8 := by ring
    _ ≤ (1 / 8 : ℝ) / 8 :=
      div_le_div_of_nonneg_right hη_quad_le (by norm_num)
    _ = (1 / 64 : ℝ) := by norm_num

theorem selectedBackwardEndpointCoeff_le {M L η endpointLeakTol q : ℝ}
    (hfirst : M * (L * endpointLeakTol) ≤ (1 / 64 : ℝ))
    (hsecond : M * ((η / 8) * M) ≤ (1 / 64 : ℝ))
    (hq : (1 / 16 : ℝ) ≤ q) :
    M * (L * endpointLeakTol + (η / 8) * M) ≤ q := by
  calc
    M * (L * endpointLeakTol + (η / 8) * M) =
        M * (L * endpointLeakTol) + M * ((η / 8) * M) := by ring
    _ ≤ (1 / 64 : ℝ) + (1 / 64 : ℝ) := add_le_add hfirst hsecond
    _ ≤ (1 / 16 : ℝ) := by norm_num
    _ ≤ q := hq

theorem selectedBackwardEndpointNorm_le {M L η endpointLeakTol q r : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hcoeff : M * (L * endpointLeakTol + (η / 8) * M) ≤ q) :
    M * (L * (endpointLeakTol * r) + (η / 8) * (M * r)) ≤ q * r := by
  calc
    M * (L * (endpointLeakTol * r) + (η / 8) * (M * r)) =
        M * (L * endpointLeakTol + (η / 8) * M) * r := by ring
    _ ≤ q * r := mul_le_mul_of_nonneg_right hcoeff hr_nonneg

theorem selectedForwardStableEndpointCoeff_le {M η G q : ℝ}
    (hη_nonneg : 0 ≤ η) (hGη : G * η = (1 / 4 : ℝ)) (hM_le_G : M ≤ G)
    (hq : (1 / 16 : ℝ) ≤ q) :
    M * (η / 8) ≤ q := by
  have hMη_le : M * η ≤ (1 / 4 : ℝ) := by
    calc
      M * η ≤ G * η := mul_le_mul_of_nonneg_right hM_le_G hη_nonneg
      _ = (1 / 4 : ℝ) := hGη
  calc
    M * (η / 8) = (M * η) / 8 := by ring
    _ ≤ (1 / 4 : ℝ) / 8 := div_le_div_of_nonneg_right hMη_le (by norm_num)
    _ ≤ (1 / 16 : ℝ) := by norm_num
    _ ≤ q := hq

theorem selectedForwardStableEndpointNorm_le {M η q r : ℝ}
    (hr_nonneg : 0 ≤ r) (hcoeff : M * (η / 8) ≤ q) :
    M * ((η / 16) * r + (η / 16) * r) ≤ q * r := by
  calc
    M * ((η / 16) * r + (η / 16) * r) =
        M * (η / 8) * r := by ring
    _ ≤ q * r := mul_le_mul_of_nonneg_right hcoeff hr_nonneg

theorem selectedForwardUnstableEndpointCoeff_le {M η endpointLeakTol G q : ℝ}
    (hη_nonneg : 0 ≤ η) (hendpoint_le_one : endpointLeakTol ≤ 1)
    (hGη : G * η = (1 / 4 : ℝ)) (hlinear_le_G : M + 1 ≤ G)
    (hq : (1 / 16 : ℝ) ≤ q) :
    M * (η / 16) + endpointLeakTol * (η / 16) ≤ q := by
  have hsum_le_G : M + endpointLeakTol ≤ G := by
    linarith
  have hsumη_le : (M + endpointLeakTol) * η ≤ (1 / 4 : ℝ) := by
    calc
      (M + endpointLeakTol) * η ≤ G * η :=
        mul_le_mul_of_nonneg_right hsum_le_G hη_nonneg
      _ = (1 / 4 : ℝ) := hGη
  calc
    M * (η / 16) + endpointLeakTol * (η / 16) =
        (M + endpointLeakTol) * η / 16 := by ring
    _ ≤ (1 / 4 : ℝ) / 16 := div_le_div_of_nonneg_right hsumη_le (by norm_num)
    _ ≤ (1 / 16 : ℝ) := by norm_num
    _ ≤ q := hq

theorem selectedForwardUnstableEndpointNorm_le {M η endpointLeakTol q r : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hcoeff : M * (η / 16) + endpointLeakTol * (η / 16) ≤ q) :
    M * ((η / 16) * r) + endpointLeakTol * ((η / 16) * r) ≤ q * r := by
  calc
    M * ((η / 16) * r) + endpointLeakTol * ((η / 16) * r) =
        (M * (η / 16) + endpointLeakTol * (η / 16)) * r := by ring
    _ ≤ q * r := mul_le_mul_of_nonneg_right hcoeff hr_nonneg

noncomputable def baseLinearDefect (T : E d ≃ₜ E d) {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) : E d :=
  T (localTubeAnchorSeq hx n) +
      fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
        (x n - localTubeAnchorSeq hx n) -
    x (n + 1)

theorem baseLinearDefect_norm_lt {ρ ε η : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hxPseudo : IsPseudoOrbit (T : E d → E d) ε x)
    (hrem : ∀ n : ℕ,
      ‖T (x n) - T (localTubeAnchorSeq hx n) -
        fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
          (x n - localTubeAnchorSeq hx n)‖ ≤
        η * ‖x n - localTubeAnchorSeq hx n‖)
    (hη_nonneg : 0 ≤ η) (n : ℕ) :
    ‖baseLinearDefect (T := T) (K := K) hx n‖ < ε + η * ρ := by
  let b : E d := pseudoOrbitDefect (T : E d → E d) x n
  let c : E d := T (x n) - T (localTubeAnchorSeq hx n) -
    fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
      (x n - localTubeAnchorSeq hx n)
  have hdecomp : baseLinearDefect (T := T) (K := K) hx n = -(b + c) := by
    dsimp [baseLinearDefect, b, c, pseudoOrbitDefect]
    abel
  have hb : ‖b‖ < ε := by
    dsimp [b]
    exact pseudoOrbitDefect_norm_lt hxPseudo n
  have hc : ‖c‖ ≤ η * ρ := by
    dsimp [c]
    exact (hrem n).trans
      (mul_le_mul_of_nonneg_left (le_of_lt (localTubeAnchorSeq_close hx n)) hη_nonneg)
  calc
    ‖baseLinearDefect (T := T) (K := K) hx n‖ = ‖b + c‖ := by
      rw [hdecomp, norm_neg]
    _ ≤ ‖b‖ + ‖c‖ := norm_add_le b c
    _ < ε + η * ρ := by
      nlinarith [hb, hc]

theorem anchorTransition_linearDefect_norm_lt {ρ ε η : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hxPseudo : IsPseudoOrbit (T : E d → E d) ε x)
    (hrem : ∀ n : ℕ,
      ‖T (x n) - T (localTubeAnchorSeq hx n) -
        fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
          (x n - localTubeAnchorSeq hx n)‖ ≤
        η * ‖x n - localTubeAnchorSeq hx n‖)
    (hη_nonneg : 0 ≤ η) (n : ℕ) :
    ‖localTubeAnchorSeq hx (n + 1) - T (localTubeAnchorSeq hx n) -
        fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
          (x n - localTubeAnchorSeq hx n)‖ <
      ρ + ε + η * ρ := by
  let a : E d := localTubeAnchorSeq hx (n + 1) - x (n + 1)
  let b : E d := pseudoOrbitDefect (T : E d → E d) x n
  let c : E d := T (x n) - T (localTubeAnchorSeq hx n) -
    fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
      (x n - localTubeAnchorSeq hx n)
  have hdecomp :
      localTubeAnchorSeq hx (n + 1) - T (localTubeAnchorSeq hx n) -
          fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
            (x n - localTubeAnchorSeq hx n) =
        a + b + c := by
    dsimp [a, b, c, pseudoOrbitDefect]
    abel
  have ha : ‖a‖ < ρ := by
    dsimp [a]
    simpa [norm_sub_rev] using localTubeAnchorSeq_close hx (n + 1)
  have hb : ‖b‖ < ε := by
    dsimp [b]
    exact pseudoOrbitDefect_norm_lt hxPseudo n
  have hc : ‖c‖ ≤ η * ρ := by
    dsimp [c]
    exact (hrem n).trans
      (mul_le_mul_of_nonneg_left (le_of_lt (localTubeAnchorSeq_close hx n)) hη_nonneg)
  calc
    ‖localTubeAnchorSeq hx (n + 1) - T (localTubeAnchorSeq hx n) -
        fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
          (x n - localTubeAnchorSeq hx n)‖ = ‖a + b + c‖ := by rw [hdecomp]
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
      calc
        ‖a + b + c‖ = ‖(a + b) + c‖ := by abel
        _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le (a + b) c
        _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by
          nlinarith [norm_add_le a b]
        _ = ‖a‖ + ‖b‖ + ‖c‖ := by ring
    _ < ρ + ε + η * ρ := by
      nlinarith [ha, hb, hc]

theorem anchorTransition_norm_lt {ρ ε η L : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hxPseudo : IsPseudoOrbit (T : E d → E d) ε x)
    (hrem : ∀ n : ℕ,
      ‖T (x n) - T (localTubeAnchorSeq hx n) -
        fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
          (x n - localTubeAnchorSeq hx n)‖ ≤
        η * ‖x n - localTubeAnchorSeq hx n‖)
    (hη_nonneg : 0 ≤ η)
    (hA_bound : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ L) (n : ℕ) :
    ‖localTubeAnchorSeq hx (n + 1) - T (localTubeAnchorSeq hx n)‖ <
      ρ + ε + (L + η) * ρ := by
  let a : E d := localTubeAnchorSeq hx (n + 1) - x (n + 1)
  let b : E d := pseudoOrbitDefect (T : E d → E d) x n
  let w : E d :=
    anchorDerivative (T := T) hx n (x n - localTubeAnchorSeq hx n)
  let c : E d := T (x n) - T (localTubeAnchorSeq hx n) -
    fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
      (x n - localTubeAnchorSeq hx n)
  have hdecomp :
      localTubeAnchorSeq hx (n + 1) - T (localTubeAnchorSeq hx n) =
        a + b + (w + c) := by
    dsimp [a, b, w, c, pseudoOrbitDefect, anchorDerivative]
    abel
  have hL_nonneg : 0 ≤ L := (norm_nonneg _).trans (hA_bound n)
  have ha : ‖a‖ < ρ := by
    dsimp [a]
    simpa [norm_sub_rev] using localTubeAnchorSeq_close hx (n + 1)
  have hb : ‖b‖ < ε := by
    dsimp [b]
    exact pseudoOrbitDefect_norm_lt hxPseudo n
  have hw : ‖w‖ ≤ L * ρ := by
    dsimp [w]
    calc
      ‖anchorDerivative (T := T) hx n (x n - localTubeAnchorSeq hx n)‖ ≤
          ‖anchorDerivative (T := T) hx n‖ * ‖x n - localTubeAnchorSeq hx n‖ :=
        (anchorDerivative (T := T) hx n).le_opNorm (x n - localTubeAnchorSeq hx n)
      _ ≤ L * ρ :=
        mul_le_mul (hA_bound n) (le_of_lt (localTubeAnchorSeq_close hx n))
          (norm_nonneg _) hL_nonneg
  have hc : ‖c‖ ≤ η * ρ := by
    dsimp [c]
    exact (hrem n).trans
      (mul_le_mul_of_nonneg_left (le_of_lt (localTubeAnchorSeq_close hx n)) hη_nonneg)
  calc
    ‖localTubeAnchorSeq hx (n + 1) - T (localTubeAnchorSeq hx n)‖ =
        ‖a + b + (w + c)‖ := by rw [hdecomp]
    _ ≤ ‖a‖ + ‖b‖ + (‖w‖ + ‖c‖) := by
      calc
        ‖a + b + (w + c)‖ = ‖(a + b) + (w + c)‖ := by abel
        _ ≤ ‖a + b‖ + ‖w + c‖ := norm_add_le (a + b) (w + c)
        _ ≤ (‖a‖ + ‖b‖) + (‖w‖ + ‖c‖) := by
          exact add_le_add (norm_add_le a b) (norm_add_le w c)
        _ = ‖a‖ + ‖b‖ + (‖w‖ + ‖c‖) := by ring
    _ < ρ + ε + (L + η) * ρ := by
      nlinarith [ha, hb, hw, hc]

def finiteTrackingAmplification (a : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 + a * finiteTrackingAmplification a n

def finiteTrackingAmplificationCap (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => max (finiteTrackingAmplification a (n + 1))
      (finiteTrackingAmplificationCap a n)

theorem finiteTrackingAmplification_nonneg {a : ℝ} (ha : 0 ≤ a) :
    ∀ n : ℕ, 0 ≤ finiteTrackingAmplification a n := by
  intro n
  induction n with
  | zero =>
      simp [finiteTrackingAmplification]
  | succ n ih =>
      simp [finiteTrackingAmplification]
      exact add_nonneg zero_le_one (mul_nonneg ha ih)

theorem finiteTrackingAmplificationCap_pos {a : ℝ} (_ha : 0 ≤ a) :
    ∀ n : ℕ, 0 < finiteTrackingAmplificationCap a n := by
  intro n
  induction n with
  | zero =>
      simp [finiteTrackingAmplificationCap]
  | succ n ih =>
      change
        0 < max (finiteTrackingAmplification a (n + 1))
          (finiteTrackingAmplificationCap a n)
      exact lt_of_lt_of_le ih
        (le_max_right (finiteTrackingAmplification a (n + 1))
          (finiteTrackingAmplificationCap a n))

theorem finiteTrackingAmplification_le_cap {a : ℝ} (_ha : 0 ≤ a) :
    ∀ {j N : ℕ}, j ≤ N →
      finiteTrackingAmplification a j ≤ finiteTrackingAmplificationCap a N := by
  intro j N hj
  induction N generalizing j with
  | zero =>
      have hj0 : j = 0 := by omega
      subst hj0
      simp [finiteTrackingAmplification, finiteTrackingAmplificationCap]
  | succ N ih =>
      by_cases hjN : j ≤ N
      · exact (ih hjN).trans
          (le_max_right (finiteTrackingAmplification a (N + 1))
            (finiteTrackingAmplificationCap a N))
      · have hj_eq : j = N + 1 := by omega
        subst hj_eq
        simp [finiteTrackingAmplificationCap]

theorem selectedAnchorBlockTracking_bound {ρ τ η L r : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (hτ_nonneg : 0 ≤ τ)
    (hη_nonneg : 0 ≤ η) (hL_nonneg : 0 ≤ L)
    (hA_bound : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ L)
    (htransition : ∀ n : ℕ,
      ‖localTubeAnchorSeq hx (n + 1) - T (localTubeAnchorSeq hx n)‖ < τ)
    (htwo : ∀ a : E d, a ∈ K → ∀ z w : E d,
      ‖z - a‖ < r → ‖w - a‖ < r →
        ‖T z - T w - fderiv ℝ (T : E d → E d) a (z - w)‖ ≤ η * ‖z - w‖)
    {N : ℕ}
    (hbudget : ∀ j : ℕ, j ≤ N →
      finiteTrackingAmplification (L + η) j * τ < r) :
    ∀ n j : ℕ, j ≤ N →
      ‖localTubeAnchorSeq hx (n + j) -
          ((T : E d → E d)^[j]) (localTubeAnchorSeq hx n)‖ ≤
        finiteTrackingAmplification (L + η) j * τ := by
  have ha_nonneg : 0 ≤ L + η := by linarith
  intro n j hj
  induction j generalizing n with
  | zero =>
      simp [finiteTrackingAmplification]
  | succ j ih =>
      have hjN : j ≤ N := Nat.le_trans (Nat.le_succ j) hj
      let a : E d := localTubeAnchorSeq hx (n + j)
      let y : E d := ((T : E d → E d)^[j]) (localTubeAnchorSeq hx n)
      have hprev :
          ‖localTubeAnchorSeq hx (n + j) -
              ((T : E d → E d)^[j]) (localTubeAnchorSeq hx n)‖ ≤
            finiteTrackingAmplification (L + η) j * τ :=
        ih n hjN
      have hprev_r :
          ‖localTubeAnchorSeq hx (n + j) -
              ((T : E d → E d)^[j]) (localTubeAnchorSeq hx n)‖ < r :=
        lt_of_le_of_lt hprev (hbudget j hjN)
      have hy_close : ‖y - a‖ < r := by
        dsimp [a, y]
        simpa [norm_sub_rev] using hprev_r
      have hr_pos : 0 < r :=
        lt_of_le_of_lt
          (mul_nonneg (finiteTrackingAmplification_nonneg ha_nonneg j) hτ_nonneg)
          (hbudget j hjN)
      have ha_close : ‖a - a‖ < r := by
        simpa using hr_pos
      have hrem :
          ‖T a - T y - fderiv ℝ (T : E d → E d) a (a - y)‖ ≤ η * ‖a - y‖ := by
        exact htwo a (localTubeAnchorSeq_mem hx (n + j)) a y ha_close hy_close
      have hlinear :
          ‖fderiv ℝ (T : E d → E d) a (a - y)‖ ≤ L * ‖a - y‖ := by
        calc
          ‖fderiv ℝ (T : E d → E d) a (a - y)‖ =
              ‖anchorDerivative (T := T) hx (n + j) (a - y)‖ := by
            rfl
          _ ≤ ‖anchorDerivative (T := T) hx (n + j)‖ * ‖a - y‖ :=
            (anchorDerivative (T := T) hx (n + j)).le_opNorm (a - y)
          _ ≤ L * ‖a - y‖ :=
            mul_le_mul_of_nonneg_right (hA_bound (n + j)) (norm_nonneg _)
      have hT_lip : ‖T a - T y‖ ≤ (L + η) * ‖a - y‖ := by
        have hdecomp :
            T a - T y =
              fderiv ℝ (T : E d → E d) a (a - y) +
                (T a - T y - fderiv ℝ (T : E d → E d) a (a - y)) := by
          abel
        calc
          ‖T a - T y‖ =
              ‖fderiv ℝ (T : E d → E d) a (a - y) +
                (T a - T y - fderiv ℝ (T : E d → E d) a (a - y))‖ := by
            exact congrArg (fun z : E d => ‖z‖) hdecomp
          _ ≤ ‖fderiv ℝ (T : E d → E d) a (a - y)‖ +
              ‖T a - T y - fderiv ℝ (T : E d → E d) a (a - y)‖ :=
            norm_add_le _ _
          _ ≤ L * ‖a - y‖ + η * ‖a - y‖ := add_le_add hlinear hrem
          _ = (L + η) * ‖a - y‖ := by ring
      have hT_lip_amp :
          ‖T a - T y‖ ≤ (L + η) *
              (finiteTrackingAmplification (L + η) j * τ) := by
        exact hT_lip.trans (mul_le_mul_of_nonneg_left (by
          dsimp [a, y] at hprev ⊢
          exact hprev) ha_nonneg)
      have hstep_decomp :
          localTubeAnchorSeq hx (n + (j + 1)) -
              ((T : E d → E d)^[j + 1]) (localTubeAnchorSeq hx n) =
            (localTubeAnchorSeq hx ((n + j) + 1) - T a) + (T a - T y) := by
        have hiter_comm :
            ((T : E d → E d)^[j]) (T (localTubeAnchorSeq hx n)) =
              T (((T : E d → E d)^[j]) (localTubeAnchorSeq hx n)) := by
          exact iterate_apply_self_comm (T : E d → E d) j (localTubeAnchorSeq hx n)
        dsimp [a, y]
        rw [hiter_comm]
        simp only [Nat.add_assoc]
        abel
      have htransition_step :
          ‖localTubeAnchorSeq hx ((n + j) + 1) - T a‖ < τ := by
        dsimp [a]
        exact htransition (n + j)
      have hmain_lt :
          ‖localTubeAnchorSeq hx (n + (j + 1)) -
              ((T : E d → E d)^[j + 1]) (localTubeAnchorSeq hx n)‖ <
            τ + (L + η) *
              (finiteTrackingAmplification (L + η) j * τ) := by
        rw [hstep_decomp]
        exact lt_of_le_of_lt (norm_add_le _ _)
          (add_lt_add_of_lt_of_le htransition_step hT_lip_amp)
      have htarget :
          τ + (L + η) * (finiteTrackingAmplification (L + η) j * τ) =
            finiteTrackingAmplification (L + η) (j + 1) * τ := by
        simp [finiteTrackingAmplification]
        ring
      exact le_of_lt (by simpa [htarget] using hmain_lt)

theorem selectedAnchorBlockTracking_lt {ρ τ η L r : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (hτ_nonneg : 0 ≤ τ)
    (hη_nonneg : 0 ≤ η) (hL_nonneg : 0 ≤ L)
    (hA_bound : ∀ n : ℕ, ‖anchorDerivative (T := T) hx n‖ ≤ L)
    (htransition : ∀ n : ℕ,
      ‖localTubeAnchorSeq hx (n + 1) - T (localTubeAnchorSeq hx n)‖ < τ)
    (htwo : ∀ a : E d, a ∈ K → ∀ z w : E d,
      ‖z - a‖ < r → ‖w - a‖ < r →
        ‖T z - T w - fderiv ℝ (T : E d → E d) a (z - w)‖ ≤ η * ‖z - w‖)
    {N : ℕ}
    (hbudget : ∀ j : ℕ, j ≤ N →
      finiteTrackingAmplification (L + η) j * τ < r) :
    ∀ n j : ℕ, j ≤ N →
      ‖localTubeAnchorSeq hx (n + j) -
          ((T : E d → E d)^[j]) (localTubeAnchorSeq hx n)‖ < r := by
  intro n j hj
  exact lt_of_le_of_lt
    (selectedAnchorBlockTracking_bound (T := T) (K := K) hx hτ_nonneg hη_nonneg
      hL_nonneg hA_bound htransition htwo hbudget n j hj)
    (hbudget j hj)

def ExactCorrectionRecurrence (T : E d → E d) (x u : ℕ → E d) : Prop :=
  ∀ n : ℕ, T (x n + u n) = x (n + 1) + u (n + 1)

def correctionResidual (T : E d → E d) (x u : ℕ → E d) (n : ℕ) : E d :=
  T (x n + u n) - x (n + 1)

noncomputable def correctionNonlinearRemainder (T : E d ≃ₜ E d) {ρ : ℝ} {x u : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) : E d :=
  T (x n + u n) - T (localTubeAnchorSeq hx n) -
    fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
      ((x n + u n) - localTubeAnchorSeq hx n)

noncomputable def correctionIncrementRemainder (T : E d ≃ₜ E d) {ρ : ℝ}
    {x u : ℕ → E d} (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) : E d :=
  T (x n + u n) - T (x n) -
    fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n) (u n)

theorem correctionResidual_decomp {ρ : ℝ} {x u : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) :
    correctionResidual (T : E d → E d) x u n =
      fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n) (u n) +
        baseLinearDefect (T := T) (K := K) hx n +
          correctionNonlinearRemainder (T := T) (K := K) (x := x) (u := u) hx n := by
  let A : E d →L[ℝ] E d :=
    fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
  have harg : (x n + u n) - localTubeAnchorSeq hx n =
      (x n - localTubeAnchorSeq hx n) + u n := by
    abel
  have hAarg : A ((x n + u n) - localTubeAnchorSeq hx n) =
      A (x n - localTubeAnchorSeq hx n) + A (u n) := by
    rw [harg, map_add]
  dsimp [correctionResidual, baseLinearDefect, correctionNonlinearRemainder, A]
  rw [hAarg]
  abel

theorem correctionResidual_increment_decomp {ρ : ℝ} {x u : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (n : ℕ) :
    correctionResidual (T : E d → E d) x u n =
      fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n) (u n) -
        pseudoOrbitDefect (T : E d → E d) x n +
          correctionIncrementRemainder (T := T) (K := K) (x := x) (u := u) hx n := by
  dsimp [correctionResidual, correctionIncrementRemainder, pseudoOrbitDefect]
  abel

theorem correctionIncrementRemainder_norm_le {ρ η r : ℝ} {x : ℕ → E d}
    {u : CorrectionSeq d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hx_close : ∀ n : ℕ, ‖x n - localTubeAnchorSeq hx n‖ < r)
    (htrial_close : ∀ n : ℕ, ‖x n + u n - localTubeAnchorSeq hx n‖ < r)
    (htwo : ∀ a : E d, a ∈ K → ∀ z w : E d,
      ‖z - a‖ < r → ‖w - a‖ < r →
        ‖T z - T w - fderiv ℝ (T : E d → E d) a (z - w)‖ ≤ η * ‖z - w‖)
    (n : ℕ) :
    ‖correctionIncrementRemainder (T := T) (K := K) (x := x) (u := fun n => u n) hx n‖ ≤
      η * ‖u n‖ := by
  have h := htwo (localTubeAnchorSeq hx n) (localTubeAnchorSeq_mem hx n)
    (x n + u n) (x n) (htrial_close n) (hx_close n)
  have harg : (x n + u n) - x n = u n := by
    abel
  simpa [correctionIncrementRemainder, harg] using h

theorem correctionIncrementRemainder_sub_norm_le {ρ η r : ℝ} {x : ℕ → E d}
    {u v : CorrectionSeq d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hu_close : ∀ n : ℕ, ‖x n + u n - localTubeAnchorSeq hx n‖ < r)
    (hv_close : ∀ n : ℕ, ‖x n + v n - localTubeAnchorSeq hx n‖ < r)
    (htwo : ∀ a : E d, a ∈ K → ∀ z w : E d,
      ‖z - a‖ < r → ‖w - a‖ < r →
        ‖T z - T w - fderiv ℝ (T : E d → E d) a (z - w)‖ ≤ η * ‖z - w‖)
    (n : ℕ) :
    ‖correctionIncrementRemainder (T := T) (K := K) (x := x) (u := fun n => u n) hx n -
        correctionIncrementRemainder (T := T) (K := K) (x := x) (u := fun n => v n) hx n‖ ≤
      η * ‖u n - v n‖ := by
  let A : E d →L[ℝ] E d :=
    fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
  have h := htwo (localTubeAnchorSeq hx n) (localTubeAnchorSeq_mem hx n)
    (x n + u n) (x n + v n) (hu_close n) (hv_close n)
  have harg : (x n + u n) - (x n + v n) = u n - v n := by
    abel
  have hdiff :
      correctionIncrementRemainder (T := T) (K := K) (x := x) (u := fun n => u n) hx n -
          correctionIncrementRemainder (T := T) (K := K) (x := x) (u := fun n => v n) hx n =
        T (x n + u n) - T (x n + v n) - A (u n - v n) := by
    dsimp [correctionIncrementRemainder, A]
    rw [map_sub]
    abel
  rw [hdiff]
  simpa [A, harg] using h

noncomputable def correctionIncrementRemainderSeq {ρ η : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (u : CorrectionSeq d)
    (hη_nonneg : 0 ≤ η)
    (hbound : ∀ n : ℕ,
      ‖correctionIncrementRemainder (T := T) (K := K) (x := x)
          (u := fun n => u n) hx n‖ ≤ η * ‖u n‖) : CorrectionSeq d :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n : ℕ =>
      correctionIncrementRemainder (T := T) (K := K) (x := x)
        (u := fun n => u n) hx n)
    (η * ‖u‖)
    (by
      intro n
      exact (hbound n).trans
        (mul_le_mul_of_nonneg_left (correctionSeq_apply_norm_le_norm u n) hη_nonneg))

@[simp]
theorem correctionIncrementRemainderSeq_apply {ρ η : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (u : CorrectionSeq d)
    (hη_nonneg : 0 ≤ η)
    (hbound : ∀ n : ℕ,
      ‖correctionIncrementRemainder (T := T) (K := K) (x := x)
          (u := fun n => u n) hx n‖ ≤ η * ‖u n‖) (n : ℕ) :
    correctionIncrementRemainderSeq (T := T) (K := K) hx u hη_nonneg hbound n =
      correctionIncrementRemainder (T := T) (K := K) (x := x)
        (u := fun n => u n) hx n :=
  rfl

theorem correctionIncrementRemainderSeq_norm_le {ρ η : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (u : CorrectionSeq d)
    (hη_nonneg : 0 ≤ η)
    (hbound : ∀ n : ℕ,
      ‖correctionIncrementRemainder (T := T) (K := K) (x := x)
          (u := fun n => u n) hx n‖ ≤ η * ‖u n‖) :
    ‖correctionIncrementRemainderSeq (T := T) (K := K) hx u hη_nonneg hbound‖ ≤
      η * ‖u‖ :=
  correctionSeq_norm_le_of_pointwise (d := d) (by
    intro n
    exact (hbound n).trans
      (mul_le_mul_of_nonneg_left (correctionSeq_apply_norm_le_norm u n) hη_nonneg))

theorem correctionIncrementRemainderSeq_sub_norm_le {ρ η : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) {u v : CorrectionSeq d}
    (hη_nonneg : 0 ≤ η)
    (hu_bound : ∀ n : ℕ,
      ‖correctionIncrementRemainder (T := T) (K := K) (x := x)
          (u := fun n => u n) hx n‖ ≤ η * ‖u n‖)
    (hv_bound : ∀ n : ℕ,
      ‖correctionIncrementRemainder (T := T) (K := K) (x := x)
          (u := fun n => v n) hx n‖ ≤ η * ‖v n‖)
    (hlip : ∀ n : ℕ,
      ‖correctionIncrementRemainder (T := T) (K := K) (x := x)
          (u := fun n => u n) hx n -
        correctionIncrementRemainder (T := T) (K := K) (x := x)
          (u := fun n => v n) hx n‖ ≤ η * ‖u n - v n‖) :
    ‖correctionIncrementRemainderSeq (T := T) (K := K) hx u hη_nonneg hu_bound -
        correctionIncrementRemainderSeq (T := T) (K := K) hx v hη_nonneg hv_bound‖ ≤
      η * ‖u - v‖ := by
  refine correctionSeq_norm_le_of_pointwise (d := d) ?_
  intro n
  have hpoint :
      ‖(correctionIncrementRemainderSeq (T := T) (K := K) hx u hη_nonneg hu_bound -
          correctionIncrementRemainderSeq (T := T) (K := K) hx v hη_nonneg hv_bound) n‖ ≤
        η * ‖u n - v n‖ := by
    simpa [correctionIncrementRemainderSeq] using hlip n
  have hnorm_uv : ‖u n - v n‖ ≤ ‖u - v‖ := by
    simpa using correctionSeq_apply_norm_le_norm (u - v) n
  exact hpoint.trans (mul_le_mul_of_nonneg_left hnorm_uv hη_nonneg)

structure AnchorLinearSolver {ρ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (greenBound : ℝ) where
  solve : CorrectionSeq d → CorrectionSeq d
  recurrence : ∀ b : CorrectionSeq d, ∀ n : ℕ,
    solve b (n + 1) = anchorDerivative (T := T) hx n (solve b n) + b n
  bound : ∀ b : CorrectionSeq d, ‖solve b‖ ≤ greenBound * ‖b‖
  lipschitz : ∀ b c : CorrectionSeq d, ‖solve b - solve c‖ ≤ greenBound * ‖b - c‖

structure SelectedAnchorBlockSolverInputs (hs : HyperbolicStructure T K)
    {ρ η r M greenBound : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (blockN : ℕ) where
  eta_pos : 0 < η
  radius_pos : 0 < r
  projectionBound_pos : 0 < M
  greenBound_pos : 0 < greenBound
  block_pos : 0 < blockN
  block_contract : hs.const * hs.rate ^ blockN < η / 16
  offdiag_le : ∀ n : ℕ, ∀ vs vu : E d,
    vs ∈ hs.stable (localTubeAnchorSeq hx n) →
      vu ∈ hs.unstable (localTubeAnchorSeq hx n) →
        ‖anchorUnstableProjection hs hx (n + 1)
            (anchorDerivative (T := T) hx n vs)‖ ≤
              η * ‖anchorDerivative (T := T) hx n vs‖ ∧
          ‖anchorStableProjection hs hx (n + 1)
            (anchorDerivative (T := T) hx n vu)‖ ≤
              η * ‖anchorDerivative (T := T) hx n vu‖
  forcing_projection_le : ∀ b : CorrectionSeq d, ∀ n : ℕ,
    ‖anchorStableProjection hs hx n (b n)‖ ≤ M * ‖b‖ ∧
      ‖anchorUnstableProjection hs hx n (b n)‖ ≤ M * ‖b‖
  blockFwdDeriv : ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < r →
    ‖fderiv ℝ ((T : E d → E d)^[blockN]) z -
        fderiv ℝ ((T : E d → E d)^[blockN]) a‖ ≤ η / 16
  blockBwdDeriv : ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < r →
    ‖fderiv ℝ ((T.symm : E d → E d)^[blockN]) z -
        fderiv ℝ ((T.symm : E d → E d)^[blockN]) a‖ ≤ η / 16

theorem selectedAnchorBlockSolverInputs_of_estimates (hs : HyperbolicStructure T K)
    {ρ η r M greenBound : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) {blockN : ℕ}
    (hη_pos : 0 < η) (hr_pos : 0 < r) (hM_pos : 0 < M)
    (hgreen_pos : 0 < greenBound) (hblock_pos : 0 < blockN)
    (hblock_contract : hs.const * hs.rate ^ blockN < η / 16)
    (hoffdiag : ∀ n : ℕ, ∀ vs vu : E d,
      vs ∈ hs.stable (localTubeAnchorSeq hx n) →
        vu ∈ hs.unstable (localTubeAnchorSeq hx n) →
          ‖anchorUnstableProjection hs hx (n + 1)
              (anchorDerivative (T := T) hx n vs)‖ ≤
                η * ‖anchorDerivative (T := T) hx n vs‖ ∧
            ‖anchorStableProjection hs hx (n + 1)
              (anchorDerivative (T := T) hx n vu)‖ ≤
                η * ‖anchorDerivative (T := T) hx n vu‖)
    (hforcing : ∀ b : CorrectionSeq d, ∀ n : ℕ,
      ‖anchorStableProjection hs hx n (b n)‖ ≤ M * ‖b‖ ∧
        ‖anchorUnstableProjection hs hx n (b n)‖ ≤ M * ‖b‖)
    (hBlockFwdDeriv : ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < r →
      ‖fderiv ℝ ((T : E d → E d)^[blockN]) z -
          fderiv ℝ ((T : E d → E d)^[blockN]) a‖ ≤ η / 16)
    (hBlockBwdDeriv : ∀ a : E d, a ∈ K → ∀ z : E d, ‖z - a‖ < r →
      ‖fderiv ℝ ((T.symm : E d → E d)^[blockN]) z -
          fderiv ℝ ((T.symm : E d → E d)^[blockN]) a‖ ≤ η / 16) :
    SelectedAnchorBlockSolverInputs (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      hx blockN := by
  exact
    { eta_pos := hη_pos
      radius_pos := hr_pos
      projectionBound_pos := hM_pos
      greenBound_pos := hgreen_pos
      block_pos := hblock_pos
      block_contract := hblock_contract
      offdiag_le := hoffdiag
      forcing_projection_le := hforcing
      blockFwdDeriv := hBlockFwdDeriv
      blockBwdDeriv := hBlockBwdDeriv }

structure SelectedAnchorStrictBlockEstimates (hs : HyperbolicStructure T K)
    {ρ η r M greenBound blockQ derivativeBound : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (blockN : ℕ) where
  inputs : SelectedAnchorBlockSolverInputs (T := T) (K := K) hs
    (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound) hx blockN
  blockQ_nonneg : 0 ≤ blockQ
  blockQ_lt_one : blockQ < 1
  derivativeBound_nonneg : 0 ≤ derivativeBound
  forward_endpoint_le : ∀ n : ℕ, ∀ vs : E d,
    vs ∈ hs.stable (localTubeAnchorSeq hx n) →
      ‖anchorStableProjection hs hx (n + blockN)
          (anchorDerivativeProduct (T := T) hx n blockN vs)‖ ≤ blockQ * ‖vs‖ ∧
        ‖anchorUnstableProjection hs hx (n + blockN)
          (anchorDerivativeProduct (T := T) hx n blockN vs)‖ ≤ blockQ * ‖vs‖
  backward_endpoint_le : ∀ n : ℕ, ∀ vu : E d,
    vu ∈ hs.unstable (localTubeAnchorSeq hx (n + blockN)) →
      ‖anchorStableProjection hs hx n
          (anchorInverseDerivativeProduct (T := T) hx n blockN vu)‖ ≤ blockQ * ‖vu‖ ∧
        ‖anchorUnstableProjection hs hx n
          (anchorInverseDerivativeProduct (T := T) hx n blockN vu)‖ ≤ blockQ * ‖vu‖
  forward_inside_bound : ∀ n m : ℕ, m ≤ blockN → ∀ v : E d,
    ‖anchorDerivativeProduct (T := T) hx n m v‖ ≤ derivativeBound ^ m * ‖v‖
  backward_inside_bound : ∀ n m : ℕ, m ≤ blockN → ∀ v : E d,
    ‖anchorInverseDerivativeProduct (T := T) hx n m v‖ ≤ derivativeBound ^ m * ‖v‖

theorem selectedAnchorStrictBlockEstimates_of_endpoint_bounds
    (hs : HyperbolicStructure T K)
    {ρ η r M greenBound blockQ derivativeBound : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) {blockN : ℕ}
    (inputs : SelectedAnchorBlockSolverInputs (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound) hx blockN)
    (hblockQ_nonneg : 0 ≤ blockQ) (hblockQ_lt_one : blockQ < 1)
    (hderivativeBound_nonneg : 0 ≤ derivativeBound)
    (hfwd : ∀ n : ℕ, ∀ vs : E d,
      vs ∈ hs.stable (localTubeAnchorSeq hx n) →
        ‖anchorStableProjection hs hx (n + blockN)
            (anchorDerivativeProduct (T := T) hx n blockN vs)‖ ≤ blockQ * ‖vs‖ ∧
          ‖anchorUnstableProjection hs hx (n + blockN)
            (anchorDerivativeProduct (T := T) hx n blockN vs)‖ ≤ blockQ * ‖vs‖)
    (hbwd : ∀ n : ℕ, ∀ vu : E d,
      vu ∈ hs.unstable (localTubeAnchorSeq hx (n + blockN)) →
        ‖anchorStableProjection hs hx n
            (anchorInverseDerivativeProduct (T := T) hx n blockN vu)‖ ≤ blockQ * ‖vu‖ ∧
          ‖anchorUnstableProjection hs hx n
            (anchorInverseDerivativeProduct (T := T) hx n blockN vu)‖ ≤ blockQ * ‖vu‖)
    (hfwd_inside : ∀ n m : ℕ, m ≤ blockN → ∀ v : E d,
      ‖anchorDerivativeProduct (T := T) hx n m v‖ ≤ derivativeBound ^ m * ‖v‖)
    (hbwd_inside : ∀ n m : ℕ, m ≤ blockN → ∀ v : E d,
      ‖anchorInverseDerivativeProduct (T := T) hx n m v‖ ≤ derivativeBound ^ m * ‖v‖) :
    SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := blockQ) (derivativeBound := derivativeBound) hx blockN := by
  exact
    { inputs := inputs
      blockQ_nonneg := hblockQ_nonneg
      blockQ_lt_one := hblockQ_lt_one
      derivativeBound_nonneg := hderivativeBound_nonneg
      forward_endpoint_le := hfwd
      backward_endpoint_le := hbwd
      forward_inside_bound := hfwd_inside
      backward_inside_bound := hbwd_inside }

structure SelectedAnchorBlockRemainderEstimates (hs : HyperbolicStructure T K)
    {ρ η r M greenBound blockQ derivativeBound : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (blockN : ℕ) where
  strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
    (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
    (blockQ := blockQ) (derivativeBound := derivativeBound) hx blockN
  forward_block_remainder_le : ∀ n m : ℕ, m ≤ blockN → ∀ vs : E d,
    vs ∈ hs.stable (localTubeAnchorSeq hx n) →
      ‖anchorDerivativeProduct (T := T) hx n (blockN + m) vs‖ ≤
        derivativeBound ^ m * ((2 * blockQ) * ‖vs‖)
  backward_remainder_block_le : ∀ n m : ℕ, m ≤ blockN → ∀ vu : E d,
    vu ∈ hs.unstable (localTubeAnchorSeq hx (n + m + blockN)) →
      ‖anchorInverseDerivativeProduct (T := T) hx n (m + blockN) vu‖ ≤
        derivativeBound ^ m * ((2 * blockQ) * ‖vu‖)
  time_decomp : ∀ t : ℕ, t = blockN * (t / blockN) + t % blockN
  time_remainder_lt : ∀ t : ℕ, t % blockN < blockN

theorem selectedAnchorBlockRemainderEstimates_of_strict
    (hs : HyperbolicStructure T K)
    {ρ η r M greenBound blockQ derivativeBound : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) {blockN : ℕ}
    (strict : SelectedAnchorStrictBlockEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := blockQ) (derivativeBound := derivativeBound) hx blockN) :
    SelectedAnchorBlockRemainderEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := blockQ) (derivativeBound := derivativeBound) hx blockN := by
  refine
    { strict := strict
      forward_block_remainder_le := ?_
      backward_remainder_block_le := ?_
      time_decomp := ?_
      time_remainder_lt := ?_ }
  · intro n m hm vs hvs
    let w : E d := anchorDerivativeProduct (T := T) hx n blockN vs
    let ps : E d := anchorStableProjection hs hx (n + blockN) w
    let pu : E d := anchorUnstableProjection hs hx (n + blockN) w
    have hendpoint := strict.forward_endpoint_le n vs hvs
    have hdecomp : ps + pu = w := by
      dsimp [ps, pu, w]
      exact anchorProjection_decomp (T := T) (K := K) hs hx (n + blockN)
        (anchorDerivativeProduct (T := T) hx n blockN vs)
    have hw_norm : ‖w‖ ≤ (2 * blockQ) * ‖vs‖ := by
      calc
        ‖w‖ = ‖ps + pu‖ := by rw [← hdecomp]
        _ ≤ ‖ps‖ + ‖pu‖ := norm_add_le ps pu
        _ ≤ blockQ * ‖vs‖ + blockQ * ‖vs‖ := by
          dsimp [ps, pu, w]
          exact add_le_add hendpoint.1 hendpoint.2
        _ = (2 * blockQ) * ‖vs‖ := by ring
    calc
      ‖anchorDerivativeProduct (T := T) hx n (blockN + m) vs‖ =
          ‖anchorDerivativeProduct (T := T) hx (n + blockN) m w‖ := by
        dsimp [w]
        rw [anchorDerivativeProduct_split_apply]
      _ ≤ derivativeBound ^ m * ‖w‖ :=
        strict.forward_inside_bound (n + blockN) m hm w
      _ ≤ derivativeBound ^ m * ((2 * blockQ) * ‖vs‖) :=
        mul_le_mul_of_nonneg_left hw_norm (pow_nonneg strict.derivativeBound_nonneg m)
  · intro n m hm vu hvu
    let w : E d := anchorInverseDerivativeProduct (T := T) hx (n + m) blockN vu
    let ps : E d := anchorStableProjection hs hx (n + m) w
    let pu : E d := anchorUnstableProjection hs hx (n + m) w
    have hvu' :
        vu ∈ hs.unstable (localTubeAnchorSeq hx ((n + m) + blockN)) := by
      simpa [Nat.add_assoc] using hvu
    have hendpoint := strict.backward_endpoint_le (n + m) vu hvu'
    have hdecomp : ps + pu = w := by
      dsimp [ps, pu, w]
      exact anchorProjection_decomp (T := T) (K := K) hs hx (n + m)
        (anchorInverseDerivativeProduct (T := T) hx (n + m) blockN vu)
    have hw_norm : ‖w‖ ≤ (2 * blockQ) * ‖vu‖ := by
      calc
        ‖w‖ = ‖ps + pu‖ := by rw [← hdecomp]
        _ ≤ ‖ps‖ + ‖pu‖ := norm_add_le ps pu
        _ ≤ blockQ * ‖vu‖ + blockQ * ‖vu‖ := by
          dsimp [ps, pu, w]
          exact add_le_add hendpoint.1 hendpoint.2
        _ = (2 * blockQ) * ‖vu‖ := by ring
    calc
      ‖anchorInverseDerivativeProduct (T := T) hx n (m + blockN) vu‖ =
          ‖anchorInverseDerivativeProduct (T := T) hx n m w‖ := by
        dsimp [w]
        rw [anchorInverseDerivativeProduct_split_apply]
      _ ≤ derivativeBound ^ m * ‖w‖ :=
        strict.backward_inside_bound n m hm w
      _ ≤ derivativeBound ^ m * ((2 * blockQ) * ‖vu‖) :=
        mul_le_mul_of_nonneg_left hw_norm (pow_nonneg strict.derivativeBound_nonneg m)
  · intro t
    exact (Nat.div_add_mod t blockN).symm
  · intro t
    exact Nat.mod_lt t strict.inputs.block_pos

structure SelectedAnchorBlockLatticeEstimates (hs : HyperbolicStructure T K)
    {ρ η r M greenBound blockQ derivativeBound latticeQ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (blockN : ℕ) where
  remainder : SelectedAnchorBlockRemainderEstimates (T := T) (K := K) hs
    (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
    (blockQ := blockQ) (derivativeBound := derivativeBound) hx blockN
  latticeQ_nonneg : 0 ≤ latticeQ
  latticeQ_lt_one : latticeQ < 1
  forward_lattice_le : ∀ n a : ℕ, ∀ vs : E d,
    vs ∈ hs.stable (localTubeAnchorSeq hx n) →
      ‖anchorDerivativeProduct (T := T) hx n (a * blockN) vs‖ ≤
        latticeQ ^ a * ‖vs‖
  backward_lattice_le : ∀ n a : ℕ, ∀ vu : E d,
    vu ∈ hs.unstable (localTubeAnchorSeq hx (n + a * blockN)) →
      ‖anchorInverseDerivativeProduct (T := T) hx n (a * blockN) vu‖ ≤
        latticeQ ^ a * ‖vu‖

structure SelectedAnchorArbitraryTimeEstimates (hs : HyperbolicStructure T K)
    {ρ η r M greenBound blockQ derivativeBound latticeQ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (blockN : ℕ) where
  lattice : SelectedAnchorBlockLatticeEstimates (T := T) (K := K) hs
    (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
    (blockQ := blockQ) (derivativeBound := derivativeBound) (latticeQ := latticeQ)
    hx blockN
  forward_time_le : ∀ n a m : ℕ, m ≤ blockN → ∀ vs : E d,
    vs ∈ hs.stable (localTubeAnchorSeq hx n) →
      ‖anchorDerivativeProduct (T := T) hx n (a * blockN + m) vs‖ ≤
        derivativeBound ^ m * (latticeQ ^ a * ‖vs‖)
  backward_time_le : ∀ n a m : ℕ, m ≤ blockN → ∀ vu : E d,
    vu ∈ hs.unstable (localTubeAnchorSeq hx (n + (a * blockN + m))) →
      ‖anchorInverseDerivativeProduct (T := T) hx n (a * blockN + m) vu‖ ≤
        derivativeBound ^ m * (latticeQ ^ a * ‖vu‖)
  time_decomp : ∀ t : ℕ, t = (t / blockN) * blockN + t % blockN
  time_remainder_lt : ∀ t : ℕ, t % blockN < blockN

theorem selectedAnchorArbitraryTimeEstimates_of_lattice
    (hs : HyperbolicStructure T K)
    {ρ η r M greenBound blockQ derivativeBound latticeQ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) {blockN : ℕ}
    (lattice : SelectedAnchorBlockLatticeEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := blockQ) (derivativeBound := derivativeBound) (latticeQ := latticeQ)
      hx blockN) :
    SelectedAnchorArbitraryTimeEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := blockQ) (derivativeBound := derivativeBound) (latticeQ := latticeQ)
      hx blockN := by
  refine
    { lattice := lattice
      forward_time_le := ?_
      backward_time_le := ?_
      time_decomp := ?_
      time_remainder_lt := ?_ }
  · intro n a m hm vs hvs
    let w : E d := anchorDerivativeProduct (T := T) hx n (a * blockN) vs
    have hsplit :
        ‖anchorDerivativeProduct (T := T) hx n (a * blockN + m) vs‖ =
          ‖anchorDerivativeProduct (T := T) hx (n + a * blockN) m w‖ := by
      dsimp [w]
      rw [anchorDerivativeProduct_split_apply]
    have hlattice : ‖w‖ ≤ latticeQ ^ a * ‖vs‖ := by
      dsimp [w]
      exact lattice.forward_lattice_le n a vs hvs
    calc
      ‖anchorDerivativeProduct (T := T) hx n (a * blockN + m) vs‖ =
          ‖anchorDerivativeProduct (T := T) hx (n + a * blockN) m w‖ := hsplit
      _ ≤ derivativeBound ^ m * ‖w‖ :=
        lattice.remainder.strict.forward_inside_bound (n + a * blockN) m hm w
      _ ≤ derivativeBound ^ m * (latticeQ ^ a * ‖vs‖) :=
        mul_le_mul_of_nonneg_left hlattice
          (pow_nonneg lattice.remainder.strict.derivativeBound_nonneg m)
  · intro n a m hm vu hvu
    let w : E d := anchorInverseDerivativeProduct (T := T) hx (n + m) (a * blockN) vu
    have hvu' :
        vu ∈ hs.unstable (localTubeAnchorSeq hx ((n + m) + a * blockN)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvu
    have hlattice : ‖w‖ ≤ latticeQ ^ a * ‖vu‖ := by
      dsimp [w]
      exact lattice.backward_lattice_le (n + m) a vu hvu'
    have hsplit :
        ‖anchorInverseDerivativeProduct (T := T) hx n (a * blockN + m) vu‖ =
          ‖anchorInverseDerivativeProduct (T := T) hx n m w‖ := by
      dsimp [w]
      rw [Nat.add_comm (a * blockN) m]
      rw [anchorInverseDerivativeProduct_split_apply]
    calc
      ‖anchorInverseDerivativeProduct (T := T) hx n (a * blockN + m) vu‖ =
          ‖anchorInverseDerivativeProduct (T := T) hx n m w‖ := hsplit
      _ ≤ derivativeBound ^ m * ‖w‖ :=
        lattice.remainder.strict.backward_inside_bound n m hm w
      _ ≤ derivativeBound ^ m * (latticeQ ^ a * ‖vu‖) :=
        mul_le_mul_of_nonneg_left hlattice
          (pow_nonneg lattice.remainder.strict.derivativeBound_nonneg m)
  · intro t
    simpa [Nat.mul_comm] using lattice.remainder.time_decomp t
  · intro t
    exact lattice.remainder.time_remainder_lt t

theorem selectedAnchor_forward_time_decomp_le
    (hs : HyperbolicStructure T K)
    {ρ η r M greenBound blockQ derivativeBound latticeQ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) {blockN : ℕ}
    (arb : SelectedAnchorArbitraryTimeEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := blockQ) (derivativeBound := derivativeBound) (latticeQ := latticeQ)
      hx blockN)
    {n t : ℕ} {vs : E d}
    (hvs : vs ∈ hs.stable (localTubeAnchorSeq hx n)) :
    ‖anchorDerivativeProduct (T := T) hx n t vs‖ ≤
      derivativeBound ^ (t % blockN) * (latticeQ ^ (t / blockN) * ‖vs‖) := by
  have ht := arb.time_decomp t
  calc
    ‖anchorDerivativeProduct (T := T) hx n t vs‖ =
        ‖anchorDerivativeProduct (T := T) hx n ((t / blockN) * blockN + t % blockN) vs‖ := by
      exact congrArg (fun s : ℕ => ‖anchorDerivativeProduct (T := T) hx n s vs‖) ht
    _ ≤ derivativeBound ^ (t % blockN) * (latticeQ ^ (t / blockN) * ‖vs‖) :=
      arb.forward_time_le n (t / blockN) (t % blockN)
        (le_of_lt (arb.time_remainder_lt t)) vs hvs

theorem selectedAnchor_backward_time_decomp_le
    (hs : HyperbolicStructure T K)
    {ρ η r M greenBound blockQ derivativeBound latticeQ : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) {blockN : ℕ}
    (arb : SelectedAnchorArbitraryTimeEstimates (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound)
      (blockQ := blockQ) (derivativeBound := derivativeBound) (latticeQ := latticeQ)
      hx blockN)
    {n t : ℕ} {vu : E d}
    (hvu : vu ∈ hs.unstable (localTubeAnchorSeq hx (n + t))) :
    ‖anchorInverseDerivativeProduct (T := T) hx n t vu‖ ≤
      derivativeBound ^ (t % blockN) * (latticeQ ^ (t / blockN) * ‖vu‖) := by
  have ht := arb.time_decomp t
  have hindex : n + t = n + ((t / blockN) * blockN + t % blockN) :=
    congrArg (fun s : ℕ => n + s) ht
  have hvu' :
      vu ∈ hs.unstable
        (localTubeAnchorSeq hx (n + ((t / blockN) * blockN + t % blockN))) := by
    simpa [hindex] using hvu
  calc
    ‖anchorInverseDerivativeProduct (T := T) hx n t vu‖ =
        ‖anchorInverseDerivativeProduct (T := T) hx n
          ((t / blockN) * blockN + t % blockN) vu‖ := by
      exact congrArg (fun s : ℕ => ‖anchorInverseDerivativeProduct (T := T) hx n s vu‖) ht
    _ ≤ derivativeBound ^ (t % blockN) * (latticeQ ^ (t / blockN) * ‖vu‖) :=
      arb.backward_time_le n (t / blockN) (t % blockN)
        (le_of_lt (arb.time_remainder_lt t)) vu hvu'

structure SelectedAnchorBlockDichotomy (hs : HyperbolicStructure T K)
    {ρ η r M greenBound : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) (blockN : ℕ) where
  inputs : SelectedAnchorBlockSolverInputs (T := T) (K := K) hs
    (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound) hx blockN
  solver : AnchorLinearSolver (T := T) (K := K) hx greenBound

def anchorLinearSolver_of_selectedAnchorBlockDichotomy
    (hs : HyperbolicStructure T K) {ρ η r M greenBound : ℝ} {x : ℕ → E d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ) {blockN : ℕ}
    (hd : SelectedAnchorBlockDichotomy (T := T) (K := K) hs
      (ρ := ρ) (η := η) (r := r) (M := M) (greenBound := greenBound) hx blockN) :
    AnchorLinearSolver (T := T) (K := K) hx greenBound :=
  hd.solver

noncomputable def anchorSolverMap {ρ greenBound : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ}
    (solver : AnchorLinearSolver (T := T) (K := K) hx greenBound)
    (defect remainder : CorrectionSeq d) : CorrectionSeq d :=
  solver.solve (-defect + remainder)

theorem anchorSolverMap_mem_correctionBall {ρ greenBound α ε η : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ}
    (solver : AnchorLinearSolver (T := T) (K := K) hx greenBound)
    (hgreen_nonneg : 0 ≤ greenBound) (hη_nonneg : 0 ≤ η)
    {defect remainder u : CorrectionSeq d}
    (hdefect : ‖defect‖ ≤ ε) (hremainder : ‖remainder‖ ≤ η * ‖u‖)
    (hu : u ∈ correctionBall (d := d) α)
    (hbudget : greenBound * (ε + η * α) ≤ α) :
    anchorSolverMap (T := T) (K := K) solver defect remainder ∈ correctionBall (d := d) α := by
  have hu_norm : ‖u‖ ≤ α := hu
  have hrem_alpha : ‖remainder‖ ≤ η * α :=
    hremainder.trans (mul_le_mul_of_nonneg_left hu_norm hη_nonneg)
  have hforcing : ‖-defect + remainder‖ ≤ ε + η * α := by
    calc
      ‖-defect + remainder‖ ≤ ‖-defect‖ + ‖remainder‖ := norm_add_le (-defect) remainder
      _ = ‖defect‖ + ‖remainder‖ := by rw [norm_neg]
      _ ≤ ε + η * α := add_le_add hdefect hrem_alpha
  exact (solver.bound (-defect + remainder)).trans
    ((mul_le_mul_of_nonneg_left hforcing hgreen_nonneg).trans hbudget)

theorem anchorSolverMap_sub_norm_le {ρ greenBound η : ℝ} {x : ℕ → E d}
    {hx : ∀ n : ℕ, x n ∈ localTube K ρ}
    (solver : AnchorLinearSolver (T := T) (K := K) hx greenBound)
    (hgreen_nonneg : 0 ≤ greenBound) {defect remU remV u v : CorrectionSeq d}
    (hremainder_lipschitz : ‖remU - remV‖ ≤ η * ‖u - v‖) :
    ‖anchorSolverMap (T := T) (K := K) solver defect remU -
        anchorSolverMap (T := T) (K := K) solver defect remV‖ ≤
      greenBound * η * ‖u - v‖ := by
  have hforcing :
      (-defect + remU) - (-defect + remV) = remU - remV := by
    abel
  calc
    ‖anchorSolverMap (T := T) (K := K) solver defect remU -
        anchorSolverMap (T := T) (K := K) solver defect remV‖ ≤
        greenBound * ‖(-defect + remU) - (-defect + remV)‖ := by
      simpa [anchorSolverMap] using solver.lipschitz (-defect + remU) (-defect + remV)
    _ = greenBound * ‖remU - remV‖ := by rw [hforcing]
    _ ≤ greenBound * (η * ‖u - v‖) :=
      mul_le_mul_of_nonneg_left hremainder_lipschitz hgreen_nonneg
    _ = greenBound * η * ‖u - v‖ := by ring

theorem correctionNonlinearRemainder_norm_lt_of_correctionBall
    {ρ α η : ℝ} {x : ℕ → E d} {u : CorrectionSeq d}
    (hx : ∀ n : ℕ, x n ∈ localTube K ρ)
    (hu : u ∈ correctionBall (d := d) α) (hη_pos : 0 < η)
    (htrial_rem : ∀ n : ℕ,
      ‖T (x n + u n) - T (localTubeAnchorSeq hx n) -
        fderiv ℝ (T : E d → E d) (localTubeAnchorSeq hx n)
          ((x n + u n) - localTubeAnchorSeq hx n)‖ ≤
        η * ‖(x n + u n) - localTubeAnchorSeq hx n‖)
    (n : ℕ) :
    ‖correctionNonlinearRemainder (T := T) (K := K) (x := x) (u := fun n => u n) hx n‖ <
      η * (ρ + α) := by
  have hclose : ‖(x n + u n) - localTubeAnchorSeq hx n‖ < ρ + α := by
    have hdecomp :
        (x n + u n) - localTubeAnchorSeq hx n =
          (x n - localTubeAnchorSeq hx n) + u n := by
      abel
    calc
      ‖(x n + u n) - localTubeAnchorSeq hx n‖ =
          ‖(x n - localTubeAnchorSeq hx n) + u n‖ := by rw [hdecomp]
      _ ≤ ‖x n - localTubeAnchorSeq hx n‖ + ‖u n‖ :=
          norm_add_le (x n - localTubeAnchorSeq hx n) (u n)
      _ < ρ + α := by
          exact add_lt_add_of_lt_of_le (localTubeAnchorSeq_close hx n)
            (correctionBall_apply_norm_le (d := d) hu n)
  have hmul : η * ‖(x n + u n) - localTubeAnchorSeq hx n‖ < η * (ρ + α) :=
    mul_lt_mul_of_pos_left hclose hη_pos
  exact lt_of_le_of_lt (by
    simpa [correctionNonlinearRemainder] using htrial_rem n) hmul

theorem exactCorrectionRecurrence_iff_residual_eq (T : E d → E d) {x u : ℕ → E d} :
    ExactCorrectionRecurrence T x u ↔
      ∀ n : ℕ, correctionResidual T x u n = u (n + 1) := by
  constructor
  · intro hrec n
    dsimp [correctionResidual]
    rw [hrec n]
    abel
  · intro hres n
    have hn := hres n
    dsimp [correctionResidual] at hn
    calc
      T (x n + u n) = x (n + 1) + (T (x n + u n) - x (n + 1)) := by
        abel
      _ = x (n + 1) + u (n + 1) := by rw [hn]

theorem exactCorrectionRecurrence_of_anchorSolverMap_fixed {ρ greenBound : ℝ}
    {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ}
    (solver : AnchorLinearSolver (T := T) (K := K) hx greenBound)
    {defect remainder u : CorrectionSeq d}
    (hfixed : anchorSolverMap (T := T) (K := K) solver defect remainder = u)
    (hresidual : ∀ n : ℕ,
      correctionResidual (T : E d → E d) x (fun n => u n) n =
        anchorDerivative (T := T) hx n (u n) - defect n + remainder n) :
    ExactCorrectionRecurrence (T : E d → E d) x (fun n => u n) := by
  rw [exactCorrectionRecurrence_iff_residual_eq]
  intro n
  have hpoint :
      u (n + 1) = anchorDerivative (T := T) hx n (u n) - defect n + remainder n := by
    rw [← hfixed]
    simpa [anchorSolverMap, sub_eq_add_neg, add_assoc] using
      solver.recurrence (-defect + remainder) n
  rw [hresidual n]
  exact hpoint.symm

theorem exists_correction_recurrence_of_anchorLinearSolver {ρ greenBound α ε η : ℝ}
    {x : ℕ → E d} {hx : ∀ n : ℕ, x n ∈ localTube K ρ}
    (solver : AnchorLinearSolver (T := T) (K := K) hx greenBound)
    (hα_nonneg : 0 ≤ α) (hgreen_nonneg : 0 ≤ greenBound) (hη_nonneg : 0 ≤ η)
    (hgreen_eta_le : greenBound * η ≤ (1 / 2 : ℝ))
    {defect : CorrectionSeq d} (hdefect : ‖defect‖ ≤ ε)
    (R : ∀ u : CorrectionSeq d, u ∈ correctionBall (d := d) α → CorrectionSeq d)
    (hR_norm : ∀ u hu, ‖R u hu‖ ≤ η * ‖u‖)
    (hR_lipschitz : ∀ u hu v hv, ‖R u hu - R v hv‖ ≤ η * ‖u - v‖)
    (hbudget : greenBound * (ε + η * α) ≤ α)
    (hresidual : ∀ u hu n,
      correctionResidual (T : E d → E d) x (fun n => u n) n =
        anchorDerivative (T := T) hx n (u n) - defect n + (R u hu) n) :
    ∃ u : CorrectionSeq d, u ∈ correctionBall (d := d) α ∧
      ExactCorrectionRecurrence (T : E d → E d) x (fun n => u n) := by
  let Ball := {u : CorrectionSeq d // u ∈ correctionBall (d := d) α}
  have hzero_mem : (0 : CorrectionSeq d) ∈ correctionBall (d := d) α := by
    dsimp [correctionBall]
    simpa using hα_nonneg
  haveI : Nonempty Ball := ⟨⟨0, hzero_mem⟩⟩
  haveI : CompleteSpace Ball :=
    (isComplete_correctionBall (d := d) α).completeSpace_coe
  let F : Ball → Ball := fun u =>
    ⟨anchorSolverMap (T := T) (K := K) solver defect (R u u.property),
      anchorSolverMap_mem_correctionBall (T := T) (K := K) solver
        hgreen_nonneg hη_nonneg hdefect (hR_norm u u.property) u.property hbudget⟩
  let q : NNReal := ⟨(1 / 2 : ℝ), by norm_num⟩
  have hq_coe : (q : ℝ) = (1 / 2 : ℝ) := by
    rfl
  have hq_lt_one : q < 1 := by
    change (q : ℝ) < (1 : ℝ)
    rw [hq_coe]
    norm_num
  have hcontract : ContractingWith q F := by
    refine ⟨hq_lt_one, ?_⟩
    refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    have hnorm :
        ‖anchorSolverMap (T := T) (K := K) solver defect (R u u.property) -
            anchorSolverMap (T := T) (K := K) solver defect (R v v.property)‖ ≤
          greenBound * η * ‖(u : CorrectionSeq d) - v‖ :=
      anchorSolverMap_sub_norm_le (T := T) (K := K) solver hgreen_nonneg
        (hremainder_lipschitz := hR_lipschitz u u.property v v.property)
    have hhalf :
        ‖anchorSolverMap (T := T) (K := K) solver defect (R u u.property) -
            anchorSolverMap (T := T) (K := K) solver defect (R v v.property)‖ ≤
          (q : ℝ) * ‖(u : CorrectionSeq d) - v‖ := by
      calc
        ‖anchorSolverMap (T := T) (K := K) solver defect (R u u.property) -
            anchorSolverMap (T := T) (K := K) solver defect (R v v.property)‖ ≤
            greenBound * η * ‖(u : CorrectionSeq d) - v‖ := hnorm
        _ = (greenBound * η) * ‖(u : CorrectionSeq d) - v‖ := by ring
        _ ≤ (1 / 2 : ℝ) * ‖(u : CorrectionSeq d) - v‖ :=
          mul_le_mul_of_nonneg_right hgreen_eta_le (norm_nonneg _)
        _ = (q : ℝ) * ‖(u : CorrectionSeq d) - v‖ := by rw [hq_coe]
    have hleft :
        dist (F u) (F v) =
          ‖anchorSolverMap (T := T) (K := K) solver defect (R u u.property) -
            anchorSolverMap (T := T) (K := K) solver defect (R v v.property)‖ := by
      change
        dist (anchorSolverMap (T := T) (K := K) solver defect (R u u.property))
            (anchorSolverMap (T := T) (K := K) solver defect (R v v.property)) =
          ‖anchorSolverMap (T := T) (K := K) solver defect (R u u.property) -
            anchorSolverMap (T := T) (K := K) solver defect (R v v.property)‖
      rw [dist_eq_norm]
    have hright : dist u v = ‖(u : CorrectionSeq d) - v‖ := by
      change dist (u : CorrectionSeq d) (v : CorrectionSeq d) = ‖(u : CorrectionSeq d) - v‖
      rw [dist_eq_norm]
    rw [hleft, hright]
    exact hhalf
  let uBall : Ball := ContractingWith.fixedPoint F hcontract
  have hfixed := hcontract.fixedPoint_isFixedPt
  have hfixed_val :
      anchorSolverMap (T := T) (K := K) solver defect (R uBall uBall.property) = uBall := by
    exact congrArg Subtype.val hfixed
  refine ⟨uBall, uBall.property, ?_⟩
  exact exactCorrectionRecurrence_of_anchorSolverMap_fixed (T := T) (K := K) solver
    hfixed_val (hresidual uBall uBall.property)

theorem shadowing_from_correction_recurrence (T : E d ≃ₜ E d) {δ : ℝ}
    {x u : ℕ → E d}
    (hrec : ExactCorrectionRecurrence (T : E d → E d) x u)
    (hubound : ∀ n : ℕ, ‖u n‖ < δ) :
    ∃ y : E d, ∀ n : ℕ, ‖x n - ((T : E d → E d)^[n]) y‖ < δ := by
  refine ⟨x 0 + u 0, ?_⟩
  have horbit : ∀ n : ℕ, ((T : E d → E d)^[n]) (x 0 + u 0) = x n + u n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        exact hrec n
  intro n
  rw [horbit n]
  have hdiff : x n - (x n + u n) = -u n := by
    abel
  rw [hdiff, norm_neg]
  exact hubound n

structure NonemptyAnalyticEstimates (T : E d ≃ₜ E d) (K : Set (E d))
    (hKc : IsCompact K) (hKne : K.Nonempty) (hs : HyperbolicStructure T K) where
  projectionBounds : UniformProjectionBounds T K hKc hKne hs
  remainderEstimates : UniformFirstOrderRemainderEstimates T K hKc hs
  neighbourhood : Set (E d)
  isOpen_neighbourhood : IsOpen neighbourhood
  subset_neighbourhood : K ⊆ neighbourhood
  shadows_pseudo_orbits :
    ∀ δ > 0, ∃ ε > 0, ∀ x : ℕ → E d,
      (∀ n, x n ∈ neighbourhood) → IsPseudoOrbit (T : E d → E d) ε x →
      ∃ y : E d, ∀ n : ℕ, ‖x n - ((T : E d → E d)^[n]) y‖ < δ

def ShadowsLocalPseudoOrbitsAtRadius (T : E d ≃ₜ E d) (K : Set (E d))
    (ρ : ℝ) : Prop :=
  ∀ δ > 0, ∃ ε > 0, ∀ x : ℕ → E d,
    (∀ n, x n ∈ localTube K ρ) → IsPseudoOrbit (T : E d → E d) ε x →
    ∃ y : E d, ∀ n : ℕ, ‖x n - ((T : E d → E d)^[n]) y‖ < δ

def nonemptyAnalyticEstimates_of_localTube_shadowing
    {hKc : IsCompact K} {hKne : K.Nonempty} {hs : HyperbolicStructure T K}
    (ρ : ℝ) (hρ : 0 < ρ)
    (hProjection : UniformProjectionBounds T K hKc hKne hs)
    (hRemainder : UniformFirstOrderRemainderEstimates T K hKc hs)
    (hshadow : ShadowsLocalPseudoOrbitsAtRadius T K ρ) :
    NonemptyAnalyticEstimates T K hKc hKne hs := by
  refine
    { projectionBounds := hProjection
      remainderEstimates := hRemainder
      neighbourhood := localTube K ρ
      isOpen_neighbourhood := isOpen_localTube K ρ
      subset_neighbourhood := subset_localTube K hρ
      shadows_pseudo_orbits := hshadow }

theorem hasShadowing_of_nonemptyAnalyticEstimates {hKc : IsCompact K} {hKne : K.Nonempty}
    {hs : HyperbolicStructure T K} (hest : NonemptyAnalyticEstimates T K hKc hKne hs) :
    HasShadowing (T : E d → E d) K := by
  exact ⟨hest.neighbourhood, hest.isOpen_neighbourhood, hest.subset_neighbourhood,
    hest.shadows_pseudo_orbits⟩

end Submission.Shadowing
