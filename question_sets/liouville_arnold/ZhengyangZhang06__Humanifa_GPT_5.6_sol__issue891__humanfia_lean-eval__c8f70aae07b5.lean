import ChallengeDeps
import Submission.OrbitChart

open LeanEval.Geometry.LiouvilleArnold
open Set
open scoped ContDiff Topology

namespace Submission

theorem liouville_arnold {n : ℕ} (F : Fin n → E n → ℝ) (U : Set (E n)) (_hU : IsOpen U)
    (_hLI : IsLiouvilleIntegrable F U)
    (c : Fin n → ℝ)
    (_hMc_sub : levelSet F c ⊆ U)
    (_hMc_compact : IsCompact (levelSet F c))
    (_hMc_connected : IsConnected (levelSet F c)) :
    Nonempty ((levelSet F c) ≃ₜ (Fin n → AddCircle (1 : ℝ))) := by
  letI : CompactSpace (levelSet F c) :=
    isCompact_iff_compactSpace.mp _hMc_compact
  letI : ConnectedSpace (levelSet F c) :=
    Subtype.connectedSpace _hMc_connected
  obtain ⟨ρ, hρsmooth, hρcompact, hρone, hρU⟩ :=
    Helpers.exists_contDiff_cutoff _hMc_compact _hU _hMc_sub
  let X : Fin n → E n → E n := fun i ↦
    Helpers.localizedHamiltonian ρ (F i)
  have hXsmooth (i : Fin n) : ContDiff ℝ ∞ (X i) := by
    simpa [X] using Helpers.contDiff_localizedHamiltonian
      _hU hρsmooth hρU (_hLI.1 i)
  have hXcompact (i : Fin n) : HasCompactSupport (X i) := by
    simpa [X] using
      (Helpers.hasCompactSupport_localizedHamiltonian (f := F i) hρcompact)
  let d₂ : ∀ i, Helpers.C2CompleteFieldData (X i) := fun i ↦
    Classical.choice (Helpers.C2CompleteFieldData.nonempty_of_contDiff_hasCompactSupport
      ((hXsmooth i).of_le (ENat.LEInfty.out (m := (3 : ℕ∞ω)))) (hXcompact i))
  let d : ∀ i, Helpers.CompleteFieldData (X i) := fun i ↦
    (d₂ i).toCompleteFieldData
  have hM₂ (i : Fin n) : IsInvariant (d₂ i).flow (levelSet F c) := by
    simpa [X] using Helpers.localizedHamiltonian_flow_invariant_levelSet
      F _hU _hLI c hρU i (d₂ i).toCompleteFieldData
  have hM (i : Fin n) : IsInvariant (d i).flow (levelSet F c) := by
    simpa [d] using hM₂ i
  have hρlevel (z : E n) (hz : z ∈ levelSet F c) : ρ z = 1 :=
    hρone.self_of_nhdsSet z hz
  have hXeq (i : Fin n) (z : E n) (hz : z ∈ levelSet F c) :
      X i z = Helpers.hamiltonianVector (F i) z := by
    simp [X, Helpers.localizedHamiltonian, hρlevel z hz]
  have hXcont (i : Fin n) : Continuous (X i) := (hXsmooth i).continuous
  have hbracket (i j : Fin n) (z : E n) (hz : z ∈ levelSet F c) :
      VectorField.lieBracket ℝ (X i) (X j) z = 0 := by
    have hρz : ∀ᶠ y in 𝓝 z, ρ y = 1 :=
      eventually_nhdsSet_iff_forall.mp hρone z hz
    have hi : X i =ᶠ[𝓝 z] Helpers.hamiltonianVector (F i) := by
      filter_upwards [hρz] with y hy
      simp [X, Helpers.localizedHamiltonian, hy]
    have hj : X j =ᶠ[𝓝 z] Helpers.hamiltonianVector (F j) := by
      filter_upwards [hρz] with y hy
      simp [X, Helpers.localizedHamiltonian, hy]
    rw [VectorField.lieBracket, hi.fderiv_eq, hj.fderiv_eq,
      hi.self_of_nhds, hj.self_of_nhds]
    simpa [VectorField.lieBracket] using
      (Helpers.lieBracket_hamiltonianVector_eq_zero_on _hU
        (_hLI.1 i) (_hLI.1 j) (fun y hy ↦ _hLI.2.1 i j y hy)
        (_hMc_sub hz))
  have hflowcomm₂ (i j : Fin n) (s t : ℝ) (z : E n)
      (hz : z ∈ levelSet F c) :
      (d₂ i).flow s ((d₂ j).flow t z) =
        (d₂ j).flow t ((d₂ i).flow s z) := by
    exact (d₂ j).flows_commute_on (d₂ i) (hM₂ j) (hM₂ i)
      (hbracket j i) s t hz
  have hflowcomm (i j : Fin n) (s t : ℝ) (z : E n)
      (hz : z ∈ levelSet F c) :
      (d i).flow s ((d j).flow t z) =
        (d j).flow t ((d i).flow s z) := by
    simpa [d] using hflowcomm₂ i j s t z hz
  let φ := Helpers.piFlow (Helpers.restrictedFlows d hM)
    (Helpers.restrictedFlows_commute d hM hflowcomm)
  apply Helpers.nonempty_homeomorph_torus_of_local_homeomorph_orbits φ
  intro x
  exact Helpers.piFlow_restricted_isLocalHomeomorph
    F U _hU _hLI c _hMc_sub d hM hflowcomm hXcont hXeq x

end Submission
