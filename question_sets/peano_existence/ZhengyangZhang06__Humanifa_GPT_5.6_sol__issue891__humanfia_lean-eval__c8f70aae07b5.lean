import Mathlib
import Submission.Helpers

open Filter Function Metric Set
open scoped BoundedContinuousFunction ContDiff NNReal Topology

namespace Submission

theorem peano_existence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} (hf : Continuous f) (x₀ : E) :
    ∃ a : ℝ, 0 < a ∧ ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Ioo (-a) a, HasDerivAt α (f (α t)) t := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E

  -- First replace `f` by a bounded, uniformly continuous vector field that
  -- agrees with it on the unit ball about the initial point.
  let φ : ContDiffBump x₀ := ⟨1, 2, by norm_num, by norm_num⟩
  let F : E → E := fun x ↦ φ x • f x
  have hF_cont : Continuous F := φ.continuous.smul hf
  have hF_support : HasCompactSupport F := by
    dsimp only [F]
    exact φ.hasCompactSupport.smul_right
  have hF_uniform : UniformContinuous F :=
    hF_support.uniformContinuous_of_continuous hF_cont
  obtain ⟨C, hC⟩ := hF_cont.bounded_above_of_compact_support hF_support
  have hC_nonneg : 0 ≤ C := (norm_nonneg (F x₀)).trans (hC x₀)
  have hF_eq_on_ball {x : E} (hx : x ∈ closedBall x₀ 1) : F x = f x := by
    have hφ : φ x = 1 := φ.one_of_mem_closedBall (by simpa [φ] using hx)
    simp [F, hφ]

  -- Smooth approximations exist uniformly on the whole space because `F` is
  -- uniformly continuous.  Their norms have one common bound.
  have h_smooth_approx (n : ℕ) :
      ∃ g : E → E, ContDiff ℝ ∞ g ∧
        ∀ x, dist (g x) (F x) < 1 / ((n : ℝ) + 1) :=
    hF_uniform.exists_contDiff_dist_le (one_div_pos.mpr (by positivity))
  choose g hg hgf using h_smooth_approx
  have h_error_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hg_norm (n : ℕ) (x : E) : ‖g n x‖ ≤ C + 2 := by
    calc
      ‖g n x‖ ≤ ‖g n x - F x‖ + ‖F x‖ := norm_le_norm_sub_add _ _
      _ = dist (g n x) (F x) + ‖F x‖ := by simp only [dist_eq_norm]
      _ ≤ 1 / ((n : ℝ) + 1) + C :=
        add_le_add (hgf n x).le (hC x)
      _ ≤ 1 + C := add_le_add (h_error_le_one n) le_rfl
      _ ≤ C + 2 := by linarith

  let L : ℝ≥0 := ⟨C + 2, by linarith⟩
  let τ : ℝ := (C + 2)⁻¹
  have hτ : 0 < τ := by
    dsimp only [τ]
    positivity
  have hnegττ : -τ ≤ τ := by linarith
  let t₀ : Icc (-τ) τ := ⟨0, by constructor <;> linarith⟩
  have hmul :
      (L : ℝ) * max (τ - (t₀ : ℝ)) ((t₀ : ℝ) - (-τ)) ≤
        ((1 : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ) := by
    simp only [t₀, sub_zero, zero_sub, neg_neg, max_self,
      NNReal.coe_one, NNReal.coe_zero]
    change (C + 2) * (C + 2)⁻¹ ≤ 1
    rw [mul_inv_cancel₀ (by linarith : C + 2 ≠ 0)]

  -- Each smooth field is Lipschitz on the compact unit ball.  Picard--Lindelöf
  -- therefore supplies a solution on the same interval for every approximation.
  have h_lipschitz (n : ℕ) :
      ∃ K : ℝ≥0, LipschitzOnWith K (g n) (closedBall x₀ 1) := by
    exact (hg n).contDiffOn.exists_lipschitzOnWith (by simp)
      (convex_closedBall x₀ 1) (isCompact_closedBall x₀ 1)
  choose K hK using h_lipschitz
  have hpl (n : ℕ) :
      IsPicardLindelof (fun _ : ℝ ↦ g n) t₀ x₀ 1 0 L (K n) :=
    IsPicardLindelof.of_time_independent
      (fun x _ ↦ by change ‖g n x‖ ≤ C + 2; exact hg_norm n x) (hK n) hmul
  have hcurve (n : ℕ) :
      ∃ γ : ODE.FunSpace t₀ x₀ 0 L,
        IsFixedPt (ODE.FunSpace.next (hpl n) (mem_closedBall_self le_rfl)) γ :=
    ODE.FunSpace.exists_isFixedPt_next (hpl n) (mem_closedBall_self le_rfl)
  choose γ hγ using hcurve
  have hγ_integral (n : ℕ) (t : Icc (-τ) τ) :
      γ n t = x₀ + ∫ s in 0..(t : ℝ), g n ((γ n).compProj s) := by
    have h :=
      (ODE.FunSpace.isFixedPt_next_iff (hpl n) (mem_closedBall_self le_rfl)).1 (hγ n) t
    simpa only [ODE.picard_apply, t₀, Subtype.coe_mk] using h

  -- Regard the approximate solutions as bounded continuous functions.  Their
  -- common Lipschitz modulus and compact range give a uniformly convergent
  -- subsequence by Arzelà--Ascoli.
  let u (n : ℕ) : Icc (-τ) τ →ᵇ E :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t ↦ γ n t, (γ n).lipschitzWith.continuous⟩
  let A : Set (Icc (-τ) τ →ᵇ E) := range u
  have hA_range (v : Icc (-τ) τ →ᵇ E) (t : Icc (-τ) τ) (hv : v ∈ A) :
      v t ∈ closedBall x₀ 1 := by
    rcases hv with ⟨n, rfl⟩
    simpa [u] using (γ n).mem_closedBall hmul
  have hA_equi : Equicontinuous ((↑) : A → Icc (-τ) τ → E) := by
    apply Metric.equicontinuous_of_continuity_modulus
      (fun r : ℝ ↦ (L : ℝ) * r)
    · have hc : ContinuousAt (fun r : ℝ ↦ (L : ℝ) * r) 0 := by fun_prop
      change Tendsto (fun r : ℝ ↦ (L : ℝ) * r) (𝓝 0) (𝓝 ((L : ℝ) * 0)) at hc
      simpa only [mul_zero] using hc
    · intro x y v
      rcases v.property with ⟨n, hn⟩
      rw [← hn]
      simpa [u] using (γ n).lipschitzWith.dist_le_mul x y
  have hA_compact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall x₀ 1)
      (isCompact_closedBall x₀ 1) A hA_range hA_equi
  obtain ⟨β, _, σ, hσ, hβ_lim⟩ :=
    hA_compact.tendsto_subseq (x := u)
      (fun n ↦ subset_closure (show u n ∈ A from ⟨n, rfl⟩))

  have hu_lim :
      TendstoUniformly (fun n (t : Icc (-τ) τ) ↦ u (σ n) t) (fun t ↦ β t) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hβ_lim (Metric.ball_mem_nhds β hε)] with n hn
    change dist (u (σ n)) β < ε at hn
    intro t
    calc
      dist (β t) (u (σ n) t) = dist (u (σ n) t) (β t) := dist_comm _ _
      _ ≤ dist (u (σ n)) β :=
        BoundedContinuousFunction.dist_coe_le_dist t
      _ < ε := by simpa only [mem_ball] using hn
  have hβ_ball (t : Icc (-τ) τ) : β t ∈ closedBall x₀ 1 := by
    exact isClosed_closedBall.mem_of_tendsto (hu_lim.tendsto_at t)
      (Filter.Eventually.of_forall fun n ↦ by
        simpa [u] using (γ (σ n)).mem_closedBall hmul)

  let p : ℝ → Icc (-τ) τ :=
    projIcc (-τ) τ (le_trans t₀.2.1 t₀.2.2)
  let α : ℝ → E := fun t ↦ β (p t)
  have hα_cont : Continuous α := β.continuous.comp continuous_projIcc
  have hα_ball (t : ℝ) : α t ∈ closedBall x₀ 1 := by
    simpa [α] using hβ_ball (p t)
  have hγ_ext_lim :
      TendstoUniformly (fun n s ↦ (γ (σ n)).compProj s) α atTop := by
    have hγ_sub_lim :
        TendstoUniformly
          (fun n (t : Icc (-τ) τ) ↦ γ (σ n) t) (fun t ↦ β t) atTop := by
      simpa [u] using hu_lim
    have h := hγ_sub_lim.comp p
    change TendstoUniformly
      (fun n s ↦ γ (σ n) (p s)) (fun s ↦ β (p s)) atTop at h
    exact h
  have hFγ_ext_lim :
      TendstoUniformly
        (fun n s ↦ F ((γ (σ n)).compProj s)) (fun s ↦ F (α s)) atTop := by
    have h := hF_uniform.comp_tendstoUniformly hγ_ext_lim
    change TendstoUniformly
      (fun n s ↦ F ((γ (σ n)).compProj s)) (fun s ↦ F (α s)) atTop at h
    exact h

  have herror_lim :
      TendstoUniformly
        (fun n s ↦ g (σ n) ((γ (σ n)).compProj s) -
          F ((γ (σ n)).compProj s))
        (fun _ ↦ (0 : E)) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have heps :
        Tendsto (fun n : ℕ ↦ 1 / (((σ n : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hσ.tendsto_atTop
    filter_upwards [heps (Iio_mem_nhds hε)] with n hn
    intro s
    calc
      dist (0 : E)
          (g (σ n) ((γ (σ n)).compProj s) - F ((γ (σ n)).compProj s)) =
          dist (g (σ n) ((γ (σ n)).compProj s))
            (F ((γ (σ n)).compProj s)) := by
              simp only [dist_eq_norm, zero_sub, norm_neg]
      _ < 1 / (((σ n : ℕ) : ℝ) + 1) := hgf (σ n) _
      _ < ε := hn
  have hintegrand_lim :
      TendstoUniformly
        (fun n s ↦ g (σ n) ((γ (σ n)).compProj s))
        (fun s ↦ F (α s)) atTop := by
    have h := herror_lim.add hFγ_ext_lim
    change TendstoUniformly
      (fun n s ↦
        (g (σ n) ((γ (σ n)).compProj s) - F ((γ (σ n)).compProj s)) +
          F ((γ (σ n)).compProj s))
      (fun s ↦ (0 : E) + F (α s)) atTop at h
    simpa only [sub_add_cancel, zero_add] using h
  have hintegral_lim (t : ℝ) :
      Tendsto
        (fun n ↦ ∫ s in 0..t, g (σ n) ((γ (σ n)).compProj s))
        atTop (𝓝 (∫ s in 0..t, F (α s))) := by
    apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    · exact Filter.Eventually.of_forall fun n ↦
        ((hg (σ n)).continuous.comp (γ (σ n)).continuous_compProj).continuousOn
    · exact hintegrand_lim.tendstoUniformlyOn

  -- Passing the fixed-point integral equations to the uniform limit produces
  -- an integral equation for `α`.
  have hβ_integral (t : Icc (-τ) τ) :
      β t = x₀ + ∫ s in 0..(t : ℝ), F (α s) := by
    have hleft : Tendsto (fun n ↦ γ (σ n) t) atTop (𝓝 (β t)) := by
      simpa [u] using hu_lim.tendsto_at t
    have hright :
        Tendsto
          (fun n ↦ x₀ + ∫ s in 0..(t : ℝ), g (σ n) ((γ (σ n)).compProj s))
          atTop (𝓝 (x₀ + ∫ s in 0..(t : ℝ), F (α s))) :=
      tendsto_const_nhds.add (hintegral_lim t)
    have hright' : Tendsto (fun n ↦ γ (σ n) t) atTop
        (𝓝 (x₀ + ∫ s in 0..(t : ℝ), F (α s))) :=
      Filter.Tendsto.congr'
        (Filter.Eventually.of_forall fun n ↦ (hγ_integral (σ n) t).symm) hright
    exact tendsto_nhds_unique hleft hright'
  have hα_integral (t : ℝ) (ht : t ∈ Icc (-τ) τ) :
      α t = x₀ + ∫ s in 0..t, F (α s) := by
    simpa [α, p, projIcc_of_mem hnegττ ht] using hβ_integral ⟨t, ht⟩
  have hα_zero : α 0 = x₀ := by
    have hzero : (0 : ℝ) ∈ Icc (-τ) τ := by constructor <;> linarith
    simpa using hα_integral 0 hzero

  refine ⟨τ, hτ, α, hα_zero, ?_⟩
  intro t ht
  have hFα_cont : Continuous (fun s ↦ F (α s)) := hF_cont.comp hα_cont
  have hlocal :
      α =ᶠ[𝓝 t] fun u ↦ x₀ + ∫ s in 0..u, F (α s) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
    exact hα_integral u hu
  have hdint :
      HasDerivAt (fun u ↦ ∫ s in 0..u, F (α s)) (F (α t)) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hFα_cont.intervalIntegrable 0 t)
      hFα_cont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hFα_cont.continuousAt
  have hdα : HasDerivAt α (F (α t)) t :=
    by simpa only [zero_add] using
      ((hasDerivAt_const t x₀).add hdint).congr_of_eventuallyEq hlocal
  exact hdα.congr_deriv (hF_eq_on_ball (hα_ball t))

end Submission
