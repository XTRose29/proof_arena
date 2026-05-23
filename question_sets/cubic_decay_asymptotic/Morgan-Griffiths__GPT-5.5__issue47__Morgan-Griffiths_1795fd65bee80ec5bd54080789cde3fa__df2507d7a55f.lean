/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: cubic_decay_asymptotic
user: Morgan-Griffiths
model: GPT-5.5
submission_repo: Morgan-Griffiths/1795fd65bee80ec5bd54080789cde3fa
submission_ref: df2507d7a55fa45e93a751ede355a1e9766cb789
issue_number: 47
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Submission

open Filter Topology

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

open Lean Elab Command in
elab "#load_cubic_decay_extra_imports" : command => do
  unsafe Lean.enableInitializersExecution
  let opts ← getOptions
  let imports : Array Import := #[
    { module := `Mathlib.Analysis.Calculus.Deriv.Basic },
    { module := `Mathlib.Analysis.SpecialFunctions.Pow.Real },
    { module := `Mathlib.Analysis.Calculus.Deriv.Mul },
    { module := `Mathlib.Analysis.SpecialFunctions.Pow.Deriv },
    { module := `Mathlib.Analysis.Calculus.MeanValue },
    { module := `Mathlib.Analysis.ODE.Gronwall }]
  let env' ← importModules imports opts (loadExts := true)
  setEnv env'
#load_cubic_decay_extra_imports

open Filter Topology
open Set
open scoped NNReal

/-- The explicit solution of `u' = -u^3` with initial value `u 0 = 1`. -/
noncomputable def modelSol (t : ℝ) : ℝ :=
  (1 + 2 * t) ^ (-(1 : ℝ) / 2)

/-- The explicit solution has value `1` at the initial point. -/
lemma modelSol_zero : modelSol 0 = 1 := by
  simp [modelSol]

/-- The explicit solution satisfies the cubic-decay ODE on the nonnegative half-line. -/
lemma modelSol_hasDerivAt_of_nonneg (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt modelSol (-(modelSol t) ^ 3) t := by
  unfold modelSol
  have hb : 0 < 1 + 2 * t := by positivity
  have hlin : HasDerivAt (fun x : ℝ => 1 + 2 * x) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).const_add (1 : ℝ)
  convert hlin.rpow_const (p := (-(1 : ℝ) / 2)) (Or.inl hb.ne') using 1
  · rw [show ((1 + 2 * t) ^ (-(1 : ℝ) / 2)) ^ 3 =
        ((1 + 2 * t) ^ (-(1 : ℝ) / 2)) ^ (3 : ℕ) by rfl]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hb)]
    ring_nf

/-- The explicit solution satisfies the cubic-decay ODE at every positive time. -/
lemma modelSol_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt modelSol (-(modelSol t) ^ 3) t :=
  modelSol_hasDerivAt_of_nonneg t ht.le

/-- A function satisfying the derivative hypothesis is continuous on each `[0,T]`,
using the assumed right-continuity at `0`. -/
lemma continuousOn_y_Icc_zero {y : ℝ → ℝ}
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) (T : ℝ) :
    ContinuousOn y (Set.Icc 0 T) := by
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hx0 | rfl
  · exact (hy_diff x hx0).continuousAt.continuousWithinAt
  · exact hy_cont.mono (by intro z hz; exact hz.1)

/-- The explicit solution is continuous on each `[0,T]`. -/
lemma continuousOn_modelSol_Icc_zero (T : ℝ) :
    ContinuousOn modelSol (Set.Icc 0 T) := by
  intro x hx
  exact (modelSol_hasDerivAt_of_nonneg x hx.1).continuousAt.continuousWithinAt

/-- On a bounded interval in phase space, the vector field `x ↦ -x^3` is Lipschitz. -/
lemma neg_cubic_lipschitzOn_Icc (M : ℝ) :
    LipschitzOnWith ⟨3 * M ^ 2, by positivity⟩
      (fun x : ℝ => - x ^ 3) (Set.Icc (-M) M) := by
  refine (convex_Icc (-M) M).lipschitzOnWith_of_nnnorm_deriv_le (𝕜 := ℝ) ?_ ?_
  · intro x hx
    fun_prop
  · intro x hx
    have hderiv : deriv (fun x : ℝ => - x ^ 3) x = - (3 * x ^ 2) := by
      have h : HasDerivAt (fun x : ℝ => - x ^ 3) (-(3 * x ^ 2)) x := by
        convert ((hasDerivAt_id x).pow 3).neg using 1
        · simp [id]
      exact h.deriv
    rw [← NNReal.coe_le_coe]
    rw [hderiv]
    simp only [NNReal.coe_mk, nnnorm, norm_neg, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ 3 * x ^ 2)]
    change 3 * x ^ 2 ≤ 3 * M ^ 2
    nlinarith [sq_le_sq' hx.1 hx.2]

/-- On each compact interval `[0,T]`, both the solution and the explicit model have a common
uniform bound. -/
lemma exists_common_bound_on_Icc_zero {y : ℝ → ℝ}
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0) (T : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      (∀ x ∈ Set.Icc 0 T, ‖y x‖ ≤ M) ∧
      (∀ x ∈ Set.Icc 0 T, ‖modelSol x‖ ≤ M) := by
  have hcy : ContinuousOn y (Set.Icc 0 T) :=
    continuousOn_y_Icc_zero hy_diff hy_cont T
  have hcg : ContinuousOn modelSol (Set.Icc 0 T) :=
    continuousOn_modelSol_Icc_zero T
  obtain ⟨Cy, hCy⟩ :=
    (CompactIccSpace.isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hcy
  obtain ⟨Cg, hCg⟩ :=
    (CompactIccSpace.isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hcg
  refine ⟨max (max Cy Cg) 1, by positivity, ?_, ?_⟩
  · intro x hx
    exact (hCy x hx).trans
      (le_trans (le_max_left Cy Cg) (le_max_left (max Cy Cg) (1 : ℝ)))
  · intro x hx
    exact (hCg x hx).trans
      (le_trans (le_max_right Cy Cg) (le_max_left (max Cy Cg) (1 : ℝ)))

/-- Uniqueness on `(0,∞)`: any solution with the given one-sided initial value agrees with the
explicit model at every positive time.  The proof compares the two trajectories on `[a,T]`
using Grönwall's inequality and then lets `a → 0+`. -/
lemma y_eq_modelSol_of_pos {y : ℝ → ℝ}
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) {T : ℝ} (hT : 0 < T) :
    y T = modelSol T := by
  obtain ⟨M, _hMpos, hMy, hMg⟩ :=
    exists_common_bound_on_Icc_zero hy_diff hy_cont T
  let K : ℝ≥0 := ⟨3 * M ^ 2, by positivity⟩
  have hcy0 : ContinuousOn y (Set.Icc 0 T) :=
    continuousOn_y_Icc_zero hy_diff hy_cont T
  have hcg0 : ContinuousOn modelSol (Set.Icc 0 T) :=
    continuousOn_modelSol_Icc_zero T
  have h_est (a : ℝ) (ha : 0 < a) (haT : a < T) :
      dist (y T) (modelSol T) ≤
        dist (y a) (modelSol a) * Real.exp ((K : ℝ) * (T - a)) := by
    have hcy : ContinuousOn y (Set.Icc a T) := by
      refine hcy0.mono ?_
      intro x hx
      exact ⟨le_trans ha.le hx.1, hx.2⟩
    have hcg : ContinuousOn modelSol (Set.Icc a T) := by
      refine hcg0.mono ?_
      intro x hx
      exact ⟨le_trans ha.le hx.1, hx.2⟩
    have hv : ∀ t ∈ Set.Ico a T,
        LipschitzOnWith K ((fun _ x : ℝ => - x ^ 3) t) (Set.Icc (-M) M) := by
      intro t ht
      exact neg_cubic_lipschitzOn_Icc M
    have hf' : ∀ t ∈ Set.Ico a T,
        HasDerivWithinAt y ((fun _ x : ℝ => - x ^ 3) t (y t)) (Set.Ici t) t := by
      intro t ht
      exact (hy_diff t (lt_of_lt_of_le ha ht.1)).hasDerivWithinAt
    have hg' : ∀ t ∈ Set.Ico a T,
        HasDerivWithinAt modelSol
          ((fun _ x : ℝ => - x ^ 3) t (modelSol t)) (Set.Ici t) t := by
      intro t ht
      exact (modelSol_hasDerivAt t (lt_of_lt_of_le ha ht.1)).hasDerivWithinAt
    have hfs : ∀ t ∈ Set.Ico a T, y t ∈ Set.Icc (-M) M := by
      intro t ht
      have ht0T : t ∈ Set.Icc 0 T :=
        ⟨(lt_of_lt_of_le ha ht.1).le, ht.2.le⟩
      have hb := hMy t ht0T
      rw [Real.norm_eq_abs] at hb
      exact abs_le.mp hb
    have hgs : ∀ t ∈ Set.Ico a T, modelSol t ∈ Set.Icc (-M) M := by
      intro t ht
      have ht0T : t ∈ Set.Icc 0 T :=
        ⟨(lt_of_lt_of_le ha ht.1).le, ht.2.le⟩
      have hb := hMg t ht0T
      rw [Real.norm_eq_abs] at hb
      exact abs_le.mp hb
    have hode := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ x : ℝ => - x ^ 3) (s := fun _ : ℝ => Set.Icc (-M) M)
      (K := K) (a := a) (b := T) (δ := dist (y a) (modelSol a))
      hv hcy hf' hfs hcg hg' hgs (le_rfl)
    simpa [K] using hode T ⟨haT.le, le_rfl⟩
  have hy_tend : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hc : ContinuousWithinAt y (Set.Ioi (0 : ℝ)) 0 :=
      hy_cont.mono (by intro x hx; exact (Set.mem_Ioi.mp hx).le)
    simpa [ContinuousWithinAt, hy0] using hc
  have hg_tend : Tendsto modelSol (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcont0 : ContinuousAt modelSol 0 :=
      (modelSol_hasDerivAt_of_nonneg 0 le_rfl).continuousAt
    have h := hcont0.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [modelSol_zero] using h
  have hdist_tend :
      Tendsto (fun a : ℝ => dist (y a) (modelSol a)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [dist_self] using hy_tend.dist hg_tend
  have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Filter.tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hexp_tend :
      Tendsto (fun a : ℝ => Real.exp ((K : ℝ) * (T - a))) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.exp ((K : ℝ) * T))) := by
    have harg :
        Tendsto (fun a : ℝ => (K : ℝ) * (T - a)) (𝓝[>] (0 : ℝ))
          (𝓝 ((K : ℝ) * T)) := by
      simpa using (hid.const_sub T).const_mul (K : ℝ)
    simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp harg
  have hrhs_tend :
      Tendsto
        (fun a : ℝ => dist (y a) (modelSol a) * Real.exp ((K : ℝ) * (T - a)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hdist_tend.mul hexp_tend
  have h_event : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      dist (y T) (modelSol T) ≤
        dist (y a) (modelSol a) * Real.exp ((K : ℝ) * (T - a)) := by
    have hpos : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
    have hlt : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < T :=
      (eventually_lt_nhds hT).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [hpos, hlt] with a ha haT
    exact h_est a ha haT
  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hle0 : dist (y T) (modelSol T) ≤ 0 := by
    simpa using le_of_tendsto_of_tendsto tendsto_const_nhds hrhs_tend h_event
  exact dist_eq_zero.mp (le_antisymm hle0 dist_nonneg)

/-- For nonnegative `t`, the model solution times `sqrt t` is a square root of the rational
expression `t / (1 + 2t)`. -/
lemma modelSol_mul_sqrt_eq_sqrt_ratio (t : ℝ) (ht : 0 ≤ t) :
    modelSol t * Real.sqrt t = Real.sqrt (t / (1 + 2 * t)) := by
  unfold modelSol
  have hb : 0 < 1 + 2 * t := by positivity
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring]
  rw [Real.rpow_neg (le_of_lt hb)]
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_div ht]
  field_simp [(Real.sqrt_pos_of_pos hb).ne']

/-- The square-root rational expression has the required limit at infinity. -/
lemma tendsto_sqrt_ratio :
    Tendsto (fun t : ℝ => Real.sqrt (t / (1 + 2 * t))) atTop
      (𝓝 (1 / Real.sqrt 2)) := by
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hden : Tendsto (fun t : ℝ => t⁻¹ + 2) atTop (𝓝 (0 + 2 : ℝ)) :=
    hinv.add tendsto_const_nhds
  have hratio' :
      Tendsto (fun t : ℝ => (t⁻¹ + 2)⁻¹) atTop (𝓝 ((0 + 2 : ℝ)⁻¹)) :=
    hden.inv₀ (by norm_num)
  have heq :
      (fun t : ℝ => (t⁻¹ + 2)⁻¹) =ᶠ[atTop]
        (fun t : ℝ => t / (1 + 2 * t)) := by
    filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp [ht]
  have hratio : Tendsto (fun t : ℝ => t / (1 + 2 * t)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := hratio'.congr' heq
    simpa using h
  have hsqrt :
      Tendsto (fun t : ℝ => Real.sqrt (t / (1 + 2 * t))) atTop
        (𝓝 (Real.sqrt (1 / 2 : ℝ))) := by
    simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  have hconst : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    simp
  simpa [hconst] using hsqrt

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/
theorem cubic_decay_asymptotic (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) :=
/-ResultProofBegin-/by
  have h_y_model :
      (fun t : ℝ => y t * Real.sqrt t) =ᶠ[atTop]
        (fun t : ℝ => modelSol t * Real.sqrt t) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [y_eq_modelSol_of_pos hy_diff hy_cont hy0 ht]
  have h_model_sqrt :
      (fun t : ℝ => modelSol t * Real.sqrt t) =ᶠ[atTop]
        (fun t : ℝ => Real.sqrt (t / (1 + 2 * t))) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact modelSol_mul_sqrt_eq_sqrt_ratio t ht
  have h_model_lim :
      Tendsto (fun t : ℝ => modelSol t * Real.sqrt t) atTop
        (𝓝 (1 / Real.sqrt 2)) :=
    tendsto_sqrt_ratio.congr' h_model_sqrt.symm
  exact h_model_lim.congr' h_y_model.symm
/-ResultProofEnd-/
/-ResultEnd-/
end Submission