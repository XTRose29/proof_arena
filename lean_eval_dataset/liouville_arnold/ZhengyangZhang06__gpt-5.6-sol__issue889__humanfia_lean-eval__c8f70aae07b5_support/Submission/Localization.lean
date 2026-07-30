import Submission.Flow

namespace Submission.Helpers

open Function Manifold Set Topology
open scoped ContDiff Manifold NNReal Topology

section Cutoff

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compact set inside an open set in a finite-dimensional vector space admits a globally smooth,
compactly supported cutoff which is one on a neighborhood of the compact set and whose topological
support lies in the prescribed open set. -/
theorem exists_contDiff_cutoff {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀ᶠ x in 𝓝ˢ K, ρ x = 1) ∧ tsupport ρ ⊆ U := by
  obtain ⟨C, hCcompact, hKC, hCU⟩ := exists_compact_between hK hU hKU
  obtain ⟨ρ, hρone, hρzero, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      𝓘(ℝ, E) hK.isClosed hKC (n := (⊤ : WithTop ℕ))
  have hρsmooth : ContDiff ℝ ∞ (ρ : E → ℝ) := ρ.contMDiff.contDiff
  have hsupp : Function.support (ρ : E → ℝ) ⊆ C := by
    intro x hx
    by_contra hxC
    exact hx (hρzero x hxC)
  have htsupp : tsupport (ρ : E → ℝ) ⊆ C :=
    closure_minimal hsupp hCcompact.isClosed
  have hρcompact : HasCompactSupport (ρ : E → ℝ) :=
    IsCompact.of_isClosed_subset hCcompact isClosed_closure htsupp
  exact ⟨ρ, hρsmooth, hρcompact, hρone, htsupp.trans hCU⟩

omit [FiniteDimensional ℝ E] in
/-- Multiplying a vector field smooth on `U` by a globally smooth scalar whose topological support
is contained in `U` produces a globally smooth vector field, even if the original field is
arbitrary outside `U`. -/
theorem contDiff_smul_of_tsupport_subset {U : Set E} (hU : IsOpen U)
    {ρ : E → ℝ} {X : E → V} (hρ : ContDiff ℝ ∞ ρ)
    (hρU : tsupport ρ ⊆ U) (hX : ContDiffOn ℝ ∞ X U) :
    ContDiff ℝ ∞ (fun x ↦ ρ x • X x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hρ.contDiffAt.smul ((hX x hx).contDiffAt (hU.mem_nhds hx))
  · have hxt : x ∉ tsupport ρ := fun h ↦ hx (hρU h)
    have hzero : ρ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxt
    have hlocalzero : (fun y ↦ ρ y • X y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hzero] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hlocalzero

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem hasCompactSupport_smul_left {ρ : E → ℝ} {X : E → V}
    (hρ : HasCompactSupport ρ) :
    HasCompactSupport (fun x ↦ ρ x • X x) := by
  apply IsCompact.of_isClosed_subset hρ isClosed_closure
  apply closure_mono
  intro x hx
  change ρ x ≠ 0
  intro hρx
  apply hx
  simp [hρx]

omit [FiniteDimensional ℝ E] in
/-- A twice continuously differentiable compactly supported vector field is globally bounded and
globally Lipschitz. -/
theorem exists_lipschitzWith_and_bound_of_contDiff_hasCompactSupport
    {X : E → V} (hX : ContDiff ℝ 2 X) (hXcompact : HasCompactSupport X) :
    ∃ K L : ℝ≥0, LipschitzWith K X ∧ ∀ x, ‖X x‖ ≤ L := by
  obtain ⟨B, hB⟩ := hX.continuous.bounded_above_of_compact_support hXcompact
  let L : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hbound (x : E) : ‖X x‖ ≤ L := hB x |>.trans (le_max_left _ _)
  have hDX : ContDiff ℝ 1 (fderiv ℝ X) :=
    hX.fderiv_right (m := 1) (by norm_num)
  obtain ⟨A, hA⟩ := hDX.continuous.bounded_above_of_compact_support
    (hXcompact.fderiv ℝ)
  let K : ℝ≥0 := ⟨max A 0, le_max_right _ _⟩
  have hderiv (x : E) : ‖fderiv ℝ X x‖₊ ≤ K := by
    exact_mod_cast (hA x).trans (le_max_left _ _)
  exact ⟨K, L,
    lipschitzWith_of_nnnorm_fderiv_le (hX.differentiable (by norm_num)) hderiv, hbound⟩

end Cutoff

end Submission.Helpers
