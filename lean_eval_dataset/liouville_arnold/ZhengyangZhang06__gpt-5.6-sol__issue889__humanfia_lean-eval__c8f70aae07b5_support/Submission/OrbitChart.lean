import Submission.Chart

namespace Submission.Helpers

open Function Module Set Topology
open scoped ContDiff NNReal Topology BigOperators

open LeanEval.Geometry.LiouvilleArnold

section HamiltonianOrbitChart

/-- Hamiltonian combinations tangent to a common level set lie in the kernel of its joint
differential. -/
theorem jointDifferential_familyCombination_hamiltonian_eq_zero {n : ℕ}
    (F : Fin n → E n → ℝ) (x : E n)
    (hcomm : ∀ i j, poissonBracket (F i) (F j) x = 0) (a : Fin n → ℝ) :
    jointDifferential F x
      (familyCombinationOn Finset.univ (fun i ↦ hamiltonianVector (F i) x) a) = 0 := by
  ext j
  simp [familyCombinationOn_apply, fderiv_hamiltonianVector, hcomm]

/-- The derivative of Hamiltonian orbit coordinates on a regular level. -/
noncomputable def hamiltonianCoordinateDerivative {n : ℕ}
    (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (transverseCoordinates F x hF).comp
    (familyCombinationOn Finset.univ fun i ↦ hamiltonianVector (F i) x)

/-- Independence of the integrals makes the Hamiltonian orbit-coordinate derivative
injective. -/
theorem hamiltonianCoordinateDerivative_injective {n : ℕ}
    (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hcomm : ∀ i j, poissonBracket (F i) (F j) x = 0) :
    Function.Injective (hamiltonianCoordinateDerivative F x hF) := by
  apply (injective_iff_map_eq_zero
    (hamiltonianCoordinateDerivative F x hF).toLinearMap).mpr
  intro a ha
  let H := familyCombinationOn Finset.univ
    (fun i ↦ hamiltonianVector (F i) x)
  have hker : H a ∈ (jointDifferential F x).ker := by
    change jointDifferential F x (H a) = 0
    exact jointDifferential_familyCombination_hamiltonian_eq_zero F x hcomm a
  have hcoord : transverseCoordinates F x hF (H a) = 0 := by
    change transverseCoordinates F x hF (H a) = 0 at ha
    exact ha
  have hproj : (jointDifferential F x).ker.orthogonalProjectionOnto (H a) =
      (⟨H a, hker⟩ : (jointDifferential F x).ker) := by
    simpa using (jointDifferential F x).ker.orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨H a, hker⟩ : (jointDifferential F x).ker)
  have hsub : (⟨H a, hker⟩ : (jointDifferential F x).ker) = 0 := by
    apply (jointKernelEquiv F x hF).injective
    change (jointKernelEquiv F x hF)
      ((jointDifferential F x).ker.orthogonalProjectionOnto (H a)) = 0 at hcoord
    rw [hproj] at hcoord
    simpa using hcoord
  have hzero : H a = 0 := congrArg Subtype.val hsub
  have hLI := linearIndependent_hamiltonianVector F x hF
  rw [Fintype.linearIndependent_iff] at hLI
  funext i
  apply hLI a _ i
  simpa [H, familyCombinationOn_apply] using hzero

theorem hamiltonianCoordinateDerivative_surjective {n : ℕ}
    (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hcomm : ∀ i j, poissonBracket (F i) (F j) x = 0) :
    Function.Surjective (hamiltonianCoordinateDerivative F x hF) := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
    (hamiltonianCoordinateDerivative_injective F x hF hcomm)

/-- The Hamiltonian orbit-coordinate derivative as a continuous linear equivalence. -/
noncomputable def hamiltonianCoordinateEquiv {n : ℕ}
    (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hcomm : ∀ i j, poissonBracket (F i) (F j) x = 0) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  (LinearEquiv.ofBijective (hamiltonianCoordinateDerivative F x hF).toLinearMap
    ⟨hamiltonianCoordinateDerivative_injective F x hF hcomm,
      hamiltonianCoordinateDerivative_surjective F x hF hcomm⟩).toContinuousLinearEquiv

@[simp]
theorem hamiltonianCoordinateEquiv_toContinuousLinearMap {n : ℕ}
    (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hcomm : ∀ i j, poissonBracket (F i) (F j) x = 0) :
    (hamiltonianCoordinateEquiv F x hF hcomm).toContinuousLinearMap =
      hamiltonianCoordinateDerivative F x hF := by
  ext a
  rfl

variable {n : ℕ} {X : Fin n → E n → E n}

/-- In level-set coordinates, the joint orbit has the canonical Hamiltonian derivative. -/
theorem transverse_piFlow_hasStrictFDerivAt
    (F : Fin n → E n → ℝ) (c : Fin n → ℝ)
    (d : ∀ i, CompleteFieldData (X i))
    (hM : ∀ i, IsInvariant (d i).flow (levelSet F c))
    (hflowcomm : ∀ i j s t, ∀ z ∈ levelSet F c,
      (d i).flow s ((d j).flow t z) = (d j).flow t ((d i).flow s z))
    (hXcont : ∀ i, Continuous (X i))
    (hXeq : ∀ i z, z ∈ levelSet F c → X i z = hamiltonianVector (F i) z)
    (x : levelSet F c) (t : Fin n → ℝ)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i)
      ((piFlow (restrictedFlows d hM)
        (restrictedFlows_commute d hM hflowcomm)) t x : levelSet F c)) :
    HasStrictFDerivAt
      (fun q : Fin n → ℝ ↦
        transverseCoordinates F
          ((piFlow (restrictedFlows d hM)
            (restrictedFlows_commute d hM hflowcomm)) t x : levelSet F c) hF
          (((piFlow (restrictedFlows d hM)
            (restrictedFlows_commute d hM hflowcomm)) q x : levelSet F c) : E n))
      (hamiltonianCoordinateDerivative F
        ((piFlow (restrictedFlows d hM)
          (restrictedFlows_commute d hM hflowcomm)) t x : levelSet F c) hF) t := by
  let φ := piFlow (restrictedFlows d hM)
    (restrictedFlows_commute d hM hflowcomm)
  let y : levelSet F c := φ t x
  have horbit := piFlow_restricted_hasStrictFDerivAt d hM hflowcomm hXcont x t
  have hcomp := (transverseCoordinates F (y : E n) hF).hasStrictFDerivAt.comp t horbit
  have hderiv : (transverseCoordinates F (y : E n) hF).comp
      (familyCombinationOn Finset.univ fun i ↦ X i (y : E n)) =
      hamiltonianCoordinateDerivative F (y : E n) hF := by
    ext a
    simp [hamiltonianCoordinateDerivative, familyCombinationOn_apply,
      hXeq, y]
  rw [hderiv] at hcomp
  simpa [φ, y, Function.comp_def] using hcomp

/-- The restricted joint Hamiltonian flow has locally homeomorphic orbit maps. -/
theorem piFlow_restricted_isLocalHomeomorph
    (F : Fin n → E n → ℝ) (U : Set (E n)) (hU : IsOpen U)
    (hLI : IsLiouvilleIntegrable F U) (c : Fin n → ℝ)
    (hlevelU : levelSet F c ⊆ U)
    (d : ∀ i, CompleteFieldData (X i))
    (hM : ∀ i, IsInvariant (d i).flow (levelSet F c))
    (hflowcomm : ∀ i j s t, ∀ z ∈ levelSet F c,
      (d i).flow s ((d j).flow t z) = (d j).flow t ((d i).flow s z))
    (hXcont : ∀ i, Continuous (X i))
    (hXeq : ∀ i z, z ∈ levelSet F c → X i z = hamiltonianVector (F i) z)
    (x : levelSet F c) :
    IsLocalHomeomorph (fun t : Fin n → ℝ ↦
      (piFlow (restrictedFlows d hM)
        (restrictedFlows_commute d hM hflowcomm)) t x) := by
  let φ := piFlow (restrictedFlows d hM)
    (restrictedFlows_commute d hM hflowcomm)
  apply IsLocalHomeomorph.mk
  intro t
  let y : levelSet F c := φ t x
  have hyU : (y : E n) ∈ U := hlevelU y.property
  have hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) (y : E n) :=
    hLI.2.2 (y : E n) hyU
  have hsmooth : ∀ i, ContDiffAt ℝ 1 (F i) (y : E n) := fun i ↦
    ((hLI.1 i (y : E n) hyU).contDiffAt (hU.mem_nhds hyU)).of_le (by norm_num)
  have hpoisson : ∀ i j, poissonBracket (F i) (F j) (y : E n) = 0 := fun i j ↦
    hLI.2.1 i j (y : E n) hyU
  let e := levelSetOpenPartialHomeomorph F c (y : E n) y.property hF hsmooth
  let A := hamiltonianCoordinateEquiv F (y : E n) hF hpoisson
  have hstrict : HasStrictFDerivAt
      (fun q : Fin n → ℝ ↦ transverseCoordinates F (y : E n) hF (φ q x : E n))
      A.toContinuousLinearMap t := by
    rw [hamiltonianCoordinateEquiv_toContinuousLinearMap]
    exact transverse_piFlow_hasStrictFDerivAt F c d hM hflowcomm hXcont hXeq x t hF
  let p := hstrict.toOpenPartialHomeomorph
    (fun q : Fin n → ℝ ↦ transverseCoordinates F (y : E n) hF (φ q x : E n))
  let orbit : (Fin n → ℝ) → levelSet F c := fun q ↦ φ q x
  have horbit : Continuous orbit := φ.continuous continuous_id continuous_const
  let s : Set (Fin n → ℝ) := orbit ⁻¹' e.source
  have hs : IsOpen s := e.open_source.preimage horbit
  let r := (p.restrOpen s hs).trans e.symm
  have hySource : y ∈ e.source :=
    self_mem_levelSetOpenPartialHomeomorph_source F c (y : E n) y.property hF hsmooth
  have htSource : t ∈ r.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hySource⟩
    · change p t ∈ e.target
      have hemap := e.map_source hySource
      simpa [p, e, y, φ] using hemap
  refine ⟨r, htSource, ?_⟩
  intro q hq
  have hq' : q ∈ (p.restrOpen s hs).source := by
    simpa using hq.1
  rw [OpenPartialHomeomorph.restrOpen_source] at hq'
  have hqSource : orbit q ∈ e.source := hq'.2
  change orbit q = e.symm (p q)
  have heq : p q = e (orbit q) := by
    rfl
  rw [heq]
  exact (e.left_inv hqSource).symm

end HamiltonianOrbitChart

end Submission.Helpers
