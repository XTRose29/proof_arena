import Submission.Localization

namespace Submission.Helpers

open Function Set Topology
open scoped ContDiff NNReal Topology

section Conservation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {U : Set E} {f ρ : E → ℝ} {X : E → E} {K L : ℝ≥0}

/-- A localized vector field preserves a first integral. Outside the localization set its
trajectories are stationary, so no regularity of the first integral is needed there. -/
theorem localized_first_integral
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hρU : tsupport ρ ⊆ U)
    (hzero : ∀ y ∈ U, fderiv ℝ f y (ρ y • X y) = 0)
    (hWlip : LipschitzWith K fun y ↦ ρ y • X y)
    (hWbound : ∀ y, ‖ρ y • X y‖ ≤ L) (x : E) (t : ℝ) :
    f (globalIntegralCurve hWlip hWbound x t) = f x := by
  let W : E → E := fun y ↦ ρ y • X y
  let γ : ℝ → E := globalIntegralCurve hWlip hWbound x
  have hγ (s : ℝ) : HasDerivAt γ (W (γ s)) s := by
    exact globalIntegralCurve_hasDerivAt hWlip hWbound x s
  have hcomp (s : ℝ) : HasDerivAt (fun u ↦ f (γ u)) 0 s := by
    by_cases hs : γ s ∈ U
    · have hf' : DifferentiableAt ℝ f (γ s) :=
        ((hf (γ s) hs).contDiffAt (hU.mem_nhds hs)).differentiableAt (by norm_num)
      simpa [Function.comp_def, W, hzero (γ s) hs] using
        hf'.hasFDerivAt.comp_hasDerivAt s (hγ s)
    · have hnot : γ s ∉ tsupport ρ := fun h ↦ hs (hρU h)
      have hρzero : ρ (γ s) = 0 := notMem_support.mp (fun h ↦ hnot (subset_closure h))
      have hWzero : W (γ s) = 0 := by simp [W, hρzero]
      have hconst (u : ℝ) : γ u = γ s := by
        exact globalIntegralCurve_eq_of_apply_eq_zero hWlip hWbound x hWzero u
      have heq : (fun u ↦ f (γ u)) = fun _ ↦ f (γ s) := by
        funext u
        rw [hconst u]
      rw [heq]
      exact hasDerivAt_const (x := s) (c := f (γ s))
  have hconst := is_const_of_deriv_eq_zero
    (fun s ↦ (hcomp s).differentiableAt) (fun s ↦ (hcomp s).deriv) t 0
  simpa [γ] using hconst

end Conservation

section CompleteField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Quantitative data sufficient to integrate a vector field for all real times. -/
structure CompleteFieldData (X : E → E) where
  K : ℝ≥0
  L : ℝ≥0
  lipschitzWith : LipschitzWith K X
  norm_le : ∀ x, ‖X x‖ ≤ L

namespace CompleteFieldData

/-- The global flow determined by complete-field data. -/
noncomputable def flow {X : E → E} (d : CompleteFieldData X) : Flow ℝ E :=
  flowOfLipschitzBounded d.lipschitzWith d.norm_le

@[simp]
theorem flow_apply {X : E → E} (d : CompleteFieldData X) (t : ℝ) (x : E) :
    d.flow t x = globalIntegralCurve d.lipschitzWith d.norm_le x t := rfl

theorem flow_hasDerivAt {X : E → E} (d : CompleteFieldData X) (x : E) (t : ℝ) :
    HasDerivAt (fun s ↦ d.flow s x) (X (d.flow t x)) t :=
  flowOfLipschitzBounded_hasDerivAt d.lipschitzWith d.norm_le x t

end CompleteFieldData

omit [CompleteSpace E] in
theorem nonempty_completeFieldData_of_contDiff_hasCompactSupport {X : E → E}
    (hX : ContDiff ℝ 2 X) (hXcompact : HasCompactSupport X) :
    Nonempty (CompleteFieldData X) := by
  obtain ⟨K, L, hK, hL⟩ :=
    exists_lipschitzWith_and_bound_of_contDiff_hasCompactSupport hX hXcompact
  exact ⟨⟨K, L, hK, hL⟩⟩

end CompleteField

section LiouvilleSystem

open LeanEval.Geometry.LiouvilleArnold

/-- A compactly supported localization of a standard Hamiltonian vector field. -/
noncomputable def localizedHamiltonian {n : ℕ} (ρ : E n → ℝ) (f : E n → ℝ) : E n → E n :=
  fun x ↦ ρ x • hamiltonianVector f x

theorem contDiff_localizedHamiltonian {n : ℕ} {ρ : E n → ℝ} {f : E n → ℝ}
    {U : Set (E n)} (hU : IsOpen U) (hρ : ContDiff ℝ ∞ ρ)
    (hρU : tsupport ρ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (localizedHamiltonian ρ f) := by
  exact contDiff_smul_of_tsupport_subset hU hρ hρU
    (contDiffOn_hamiltonianVector hf hU)

theorem hasCompactSupport_localizedHamiltonian {n : ℕ} {ρ : E n → ℝ}
    {f : E n → ℝ} (hρ : HasCompactSupport ρ) :
    HasCompactSupport (localizedHamiltonian ρ f) := by
  exact hasCompactSupport_smul_left hρ

theorem nonempty_completeFieldData_localizedHamiltonian {n : ℕ} {ρ : E n → ℝ}
    {f : E n → ℝ} {U : Set (E n)} (hU : IsOpen U) (hρ : ContDiff ℝ ∞ ρ)
    (hρcompact : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    Nonempty (CompleteFieldData (localizedHamiltonian ρ f)) := by
  apply nonempty_completeFieldData_of_contDiff_hasCompactSupport
  · exact (contDiff_localizedHamiltonian hU hρ hρU hf).of_le
      (ENat.LEInfty.out (m := (2 : ℕ∞ω)))
  · exact hasCompactSupport_localizedHamiltonian hρcompact

theorem localizedHamiltonian_firstIntegral {n : ℕ} (F : Fin n → E n → ℝ)
    {U : Set (E n)} (hU : IsOpen U) (hLI : IsLiouvilleIntegrable F U)
    {ρ : E n → ℝ} (hρU : tsupport ρ ⊆ U) (i j : Fin n)
    (d : CompleteFieldData (localizedHamiltonian ρ (F i))) (x : E n) (t : ℝ) :
    F j (d.flow t x) = F j x := by
  apply localized_first_integral hU
    ((hLI.1 j).of_le (ENat.LEInfty.out (m := (1 : ℕ∞ω)))) hρU
    (K := d.K) (L := d.L) (X := hamiltonianVector (F i))
  · intro y hy
    simp [fderiv_hamiltonianVector, hLI.2.1 i j y hy]
  · exact d.lipschitzWith
  · exact d.norm_le

theorem localizedHamiltonian_flow_invariant_levelSet {n : ℕ}
    (F : Fin n → E n → ℝ) {U : Set (E n)} (hU : IsOpen U)
    (hLI : IsLiouvilleIntegrable F U) (c : Fin n → ℝ)
    {ρ : E n → ℝ} (hρU : tsupport ρ ⊆ U) (i : Fin n)
    (d : CompleteFieldData (localizedHamiltonian ρ (F i))) :
    IsInvariant d.flow (levelSet F c) := by
  intro t x hx j
  rw [localizedHamiltonian_firstIntegral F hU hLI hρU i j d x t]
  exact hx j

end LiouvilleSystem

end Submission.Helpers
