import Mathlib

namespace Submission.Helpers

noncomputable section

open scoped BigOperators ENNReal Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The finite Hilbert-space amplification used in the double commutant argument. -/
abbrev AmplificationSpace (ι : Type*) := PiLp 2 fun _ : ι => H

/-- Apply the same operator in every coordinate of a finite Hilbert-space amplification. -/
def amplification {ι : Type*} [Fintype ι] (A : H →L[ℂ] H) :
    AmplificationSpace (H := H) ι →L[ℂ] AmplificationSpace (H := H) ι :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  e.symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.piMap (fun _ : ι => A) ∘L e.toContinuousLinearMap

@[simp]
lemma amplification_apply {ι : Type*} [Fintype ι] (A : H →L[ℂ] H)
    (x : AmplificationSpace (H := H) ι) (i : ι) :
    amplification A x i = A (x i) :=
  rfl

/-- The adjoint of a diagonal amplification is the diagonal amplification of the adjoint. -/
lemma amplification_adjoint {ι : Type*} [Fintype ι] [CompleteSpace H]
    (A : H →L[ℂ] H) :
    amplification A.adjoint =
      (ContinuousLinearMap.adjoint
        (𝕜 := ℂ)
        (E := AmplificationSpace (H := H) ι)
        (F := AmplificationSpace (H := H) ι)) (amplification A) := by
  apply (ContinuousLinearMap.eq_adjoint_iff
    (𝕜 := ℂ)
    (E := AmplificationSpace (H := H) ι)
    (F := AmplificationSpace (H := H) ι)
    (amplification A.adjoint) (amplification A)).mpr
  intro x y
  simp only [PiLp.inner_apply, amplification_apply]
  exact Finset.sum_congr rfl fun i _ => A.adjoint_inner_left (y i) (x i)

/-- Insert a vector into one coordinate of a finite Hilbert-space amplification. -/
def amplificationSingle {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    H →L[ℂ] AmplificationSpace (H := H) ι :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  e.symm.toContinuousLinearMap ∘L ContinuousLinearMap.single ℂ (fun _ : ι => H) i

@[simp]
lemma amplificationSingle_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (x : H) (j : ι) :
    amplificationSingle i x j = if j = i then x else 0 := by
  simp [amplificationSingle]

lemma amplification_amplificationSingle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : H →L[ℂ] H) (i : ι) (x : H) :
    amplification A (amplificationSingle i x) = amplificationSingle i (A x) := by
  ext j
  by_cases hji : j = i <;> simp [hji]

lemma sum_amplificationSingle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : AmplificationSpace (H := H) ι) :
    ∑ i, amplificationSingle i (x i) = x := by
  ext i
  simp

/-- The `(i,j)` matrix entry of an operator on a finite amplification. -/
def block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : AmplificationSpace (H := H) ι →L[ℂ] AmplificationSpace (H := H) ι)
    (i j : ι) : H →L[ℂ] H :=
  PiLp.proj 2 (fun _ : ι => H) i ∘L P ∘L amplificationSingle j

@[simp]
lemma block_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : AmplificationSpace (H := H) ι →L[ℂ] AmplificationSpace (H := H) ι)
    (i j : ι) (x : H) :
    block P i j x = P (amplificationSingle j x) i :=
  rfl

lemma apply_eq_sum_blocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : AmplificationSpace (H := H) ι →L[ℂ] AmplificationSpace (H := H) ι)
    (x : AmplificationSpace (H := H) ι) (i : ι) :
    P x i = ∑ j, block P i j (x j) := by
  conv_lhs => rw [← sum_amplificationSingle x]
  simp [block]

/-- The linear map whose range is the orbit of a vector under diagonal amplification. -/
def orbitMap {ι : Type*} [Fintype ι]
    (x : AmplificationSpace (H := H) ι) :
    (H →L[ℂ] H) →ₗ[ℂ] AmplificationSpace (H := H) ι where
  toFun A := amplification A x
  map_add' A B := by ext; simp
  map_smul' c A := by ext; simp

section Complete

variable [CompleteSpace H]

/-- The algebraic orbit submodule of `x` under `S`. -/
def orbit {ι : Type*} [Fintype ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : AmplificationSpace (H := H) ι) :
    Submodule ℂ (AmplificationSpace (H := H) ι) :=
  S.toSubmodule.map (orbitMap x)

lemma orbit_invariant {ι : Type*} [Fintype ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : AmplificationSpace (H := H) ι) {A : H →L[ℂ] H} (hA : A ∈ S) :
    orbit S x ∈ Module.End.invtSubmodule (amplification A).toLinearMap := by
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  rintro _ ⟨B, hB, rfl⟩
  refine ⟨A * B, S.mul_mem hA hB, ?_⟩
  ext i
  rfl

lemma cyclicSubspace_invariant {ι : Type*} [Fintype ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : AmplificationSpace (H := H) ι) {A : H →L[ℂ] H} (hA : A ∈ S) :
    (orbit S x).topologicalClosure ∈
      Module.End.invtSubmodule (amplification A).toLinearMap :=
  Submodule.topologicalClosure_mem_invtSubmodule (orbit_invariant S x hA)

/-- Orthogonal projection onto the closure of the amplified orbit. -/
def cyclicProjection {ι : Type*} [Fintype ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : AmplificationSpace (H := H) ι) :
    AmplificationSpace (H := H) ι →L[ℂ] AmplificationSpace (H := H) ι :=
  (orbit S x).closure.toSubmodule.starProjection

lemma cyclicProjection_commutes {ι : Type*} [Fintype ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : AmplificationSpace (H := H) ι) {A : H →L[ℂ] H} (hA : A ∈ S) :
    Commute (cyclicProjection S x) (amplification A) := by
  refine (ContinuousLinearMap.IsIdempotentElem.commute_iff
    (orbit S x).closure.toSubmodule.isIdempotentElem_starProjection).mpr ⟨?_, ?_⟩
  · rw [Submodule.range_starProjection]
    change (orbit S x).topologicalClosure ∈
      Module.End.invtSubmodule (amplification A).toLinearMap
    exact cyclicSubspace_invariant S x hA
  · rw [Submodule.ker_starProjection]
    apply ContinuousLinearMap.orthogonal_mem_invtSubmodule
    change (orbit S x).topologicalClosure ∈
      Module.End.invtSubmodule
        ((ContinuousLinearMap.adjoint
          (𝕜 := ℂ)
          (E := AmplificationSpace (H := H) ι)
          (F := AmplificationSpace (H := H) ι)) (amplification A)).toLinearMap
    rw [← amplification_adjoint]
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      cyclicSubspace_invariant S x (star_mem hA)

lemma cyclicProjection_block_commutes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : AmplificationSpace (H := H) ι) {A : H →L[ℂ] H} (hA : A ∈ S)
    (i j : ι) :
    Commute (block (cyclicProjection S x) i j) A := by
  rw [commute_iff_eq]
  ext z
  have h := DFunLike.congr_fun (cyclicProjection_commutes S x hA).eq
    (amplificationSingle j z)
  have h' := congr_arg (fun y => y i) h
  simpa only [mul_apply_eq_comp, amplification_amplificationSingle,
    amplification_apply, block_apply] using h'

lemma cyclicProjection_block_mem_centralizer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : AmplificationSpace (H := H) ι) (i j : ι) :
    block (cyclicProjection S x) i j ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
  intro A hA
  exact (cyclicProjection_block_commutes S x hA i j).eq.symm

lemma cyclicProjection_commutes_of_mem_doubleCentralizer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : AmplificationSpace (H := H) ι) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    Commute (cyclicProjection S x) (amplification T) := by
  rw [commute_iff_eq]
  ext y i
  change cyclicProjection S x (amplification T y) i =
    T (cyclicProjection S x y i)
  rw [apply_eq_sum_blocks, apply_eq_sum_blocks]
  simp only [amplification_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj := hT (block (cyclicProjection S x) i j)
    (cyclicProjection_block_mem_centralizer S x i j)
  simpa only [mul_apply_eq_comp] using
    DFunLike.congr_fun hj (y j)

lemma amplification_mem_cyclicClosure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : AmplificationSpace (H := H) ι) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    amplification T x ∈ (orbit S x).closure := by
  have hxOrbit : x ∈ orbit S x := by
    refine ⟨1, S.one_mem, ?_⟩
    ext i
    simp [orbitMap]
  have hxClosure : x ∈ (orbit S x).closure :=
    (orbit S x).le_topologicalClosure hxOrbit
  apply Submodule.starProjection_eq_self_iff.mp
  calc
    cyclicProjection S x (amplification T x) =
        amplification T (cyclicProjection S x x) :=
      DFunLike.congr_fun
        (cyclicProjection_commutes_of_mem_doubleCentralizer S x hT).eq x
    _ = amplification T x := by
      simpa only [cyclicProjection] using
        congrArg (amplification T)
          (Submodule.starProjection_eq_self_iff.mpr hxClosure)

/-- Every operator in the double commutant is in the strong-operator closure of `S`. -/
lemma toPointwise_mem_closure_of_mem_doubleCentralizer
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H T ∈
      closure
        (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
          (S : Set (H →L[ℂ] H))) := by
  classical
  rw [mem_closure_iff_nhds_zero]
  intro U hU
  rcases PointwiseConvergenceCLM.hasBasis_nhds_zero.mem_iff.mp hU with
    ⟨⟨X, V⟩, ⟨hX, hV⟩, hXV⟩
  letI : Finite X := hX
  letI : Fintype X := Fintype.ofFinite X
  let ξ : AmplificationSpace (H := H) X :=
    WithLp.toLp 2 fun i : X => (i : H)
  let W : Set (AmplificationSpace (H := H) X) := {y | ∀ i, y i ∈ V}
  have hW : W ∈ 𝓝 0 := by
    have hWi (i : X) : {y : AmplificationSpace (H := H) X | y i ∈ V} ∈ 𝓝 0 := by
      exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : X => H) i).continuous.continuousAt.preimage_mem_nhds
        (by simpa using hV)
    simpa only [W, Set.mem_setOf_eq, Set.setOf_forall] using
      (Filter.iInter_mem.2 hWi)
  have hcyclic := amplification_mem_cyclicClosure S ξ hT
  change amplification T ξ ∈ (orbit S ξ).topologicalClosure at hcyclic
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hcyclic
  rcases mem_closure_iff_nhds_zero.mp hcyclic W hW with ⟨y, hy, hyW⟩
  rcases hy with ⟨B, hB, rfl⟩
  refine ⟨ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H B,
    ⟨B, hB, rfl⟩, hXV ?_⟩
  intro z hz
  have hzW := hyW ⟨z, hz⟩
  change amplification B ξ ⟨z, hz⟩ - amplification T ξ ⟨z, hz⟩ ∈ V at hzW
  change B z - T z ∈ V
  simpa only [amplification_apply, ξ, PiLp.toLp_apply] using hzW

/-- Strong-operator closedness forces equality with the double commutant. -/
lemma doubleCentralizer_eq_of_isClosed_pointwise
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : IsClosed
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        (S : Set (H →L[ℂ] H)))) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S := by
  apply Set.Subset.antisymm
  · intro T hT
    have hClosure := toPointwise_mem_closure_of_mem_doubleCentralizer S hT
    rw [hS.closure_eq] at hClosure
    rcases hClosure with ⟨B, hB, hBT⟩
    change B = T at hBT
    exact hBT ▸ hB
  · exact Set.subset_centralizer_centralizer

end Complete

/-- The type-copy equivalence carries centralizers to centralizers. -/
lemma image_centralizer_ofCLM (s : Set (H →L[ℂ] H)) :
    ContinuousLinearMapWOT.ofCLM '' Set.centralizer s =
      Set.centralizer (ContinuousLinearMapWOT.ofCLM '' s) := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩ C ⟨D, hD, rfl⟩
    apply ContinuousLinearMapWOT.toCLM_injective
    simpa only [ContinuousLinearMapWOT.toCLM_mul] using hB D hD
  · intro hA
    refine ⟨A.toCLM, ?_, rfl⟩
    intro D hD
    have h := hA (ContinuousLinearMapWOT.ofCLM D) ⟨D, hD, rfl⟩
    have h' := congrArg
      (fun E : ContinuousLinearMapWOT (RingHom.id ℂ) H H => E.toCLM) h
    simpa only [ContinuousLinearMapWOT.toCLM_mul] using h'

lemma isClosed_image_centralizer_ofCLM (s : Set (H →L[ℂ] H)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' Set.centralizer s) := by
  rw [image_centralizer_ofCLM]
  exact Set.isClosed_centralizer _

/-- The identity from the strong operator topology to the weak operator topology. -/
def pointwiseToWOT :
    PointwiseConvergenceCLM (RingHom.id ℂ) H H →L[ℂ]
      ContinuousLinearMapWOT (RingHom.id ℂ) H H where
  toFun A := ContinuousLinearMapWOT.ofCLM A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro x y
    exact y.cont.comp (continuous_eval_const x)

section Complete

variable [CompleteSpace H]

lemma preimage_image_ofCLM
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    pointwiseToWOT ⁻¹' (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        (S : Set (H →L[ℂ] H)) := by
  ext A
  constructor
  · rintro ⟨B, hB, hBA⟩
    change ContinuousLinearMapWOT.ofCLM B = ContinuousLinearMapWOT.ofCLM A at hBA
    exact ⟨B, hB, ContinuousLinearMapWOT.ofCLM_injective hBA⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨B, hB, rfl⟩

lemma isClosed_pointwise_of_isClosed_wot
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : IsClosed (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H)))) :
    IsClosed
      (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        (S : Set (H →L[ℂ] H))) := by
  rw [← preimage_image_ofCLM]
  exact hS.preimage pointwiseToWOT.continuous

lemma isClosed_wot_of_doubleCentralizer_eq
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hS : Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H))) := by
  rw [← hS]
  exact isClosed_image_centralizer_ofCLM
    (Set.centralizer (S : Set (H →L[ℂ] H)))

end Complete

end

end Submission.Helpers
