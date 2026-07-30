import Mathlib
import ChallengeDeps
import Submission.Polytope

open Set
open unitInterval Geometry
open scoped Topology

namespace Submission.Helpers

open _root_.FamiliesOfMapsB01

section PartitionOfUnity

variable {ι X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The finitely many partition functions with nonempty topological support. -/
noncomputable def activeIndices (ρ : PartitionOfUnity ι X univ) : Finset ι :=
  ρ.locallyFinite_tsupport.finite_nonempty_of_compact.toFinset

@[simp]
theorem mem_activeIndices_iff (ρ : PartitionOfUnity ι X univ) (i : ι) :
    i ∈ activeIndices ρ ↔ (tsupport (ρ i)).Nonempty :=
  Set.Finite.mem_toFinset _

theorem eq_zero_of_not_mem_activeIndices (ρ : PartitionOfUnity ι X univ) {i : ι}
    (hi : i ∉ activeIndices ρ) (x : X) : ρ i x = 0 := by
  by_contra hix
  apply hi
  rw [mem_activeIndices_iff]
  exact ⟨x, subset_tsupport (ρ i) hix⟩

theorem finsupport_subset_activeIndices (ρ : PartitionOfUnity ι X univ) (x : X) :
    ρ.finsupport x ⊆ activeIndices ρ := by
  intro i hi
  rw [mem_activeIndices_iff]
  refine ⟨x, subset_tsupport (ρ i) ?_⟩
  simpa only [ρ.mem_finsupport, Function.mem_support] using hi

theorem sum_activeIndices_eq_one (ρ : PartitionOfUnity ι X univ) (x : X) :
    ∑ i ∈ activeIndices ρ, ρ i x = 1 :=
  ρ.sum_finsupport' (mem_univ x) (finsupport_subset_activeIndices ρ x)

theorem activeIndices_cover (ρ : PartitionOfUnity ι X univ) {U : ι → Set X}
    (hρ : ρ.IsSubordinate U) : ⋃ i ∈ activeIndices ρ, U i = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := ρ.exists_pos (mem_univ x)
  rw [mem_iUnion]
  refine ⟨i, ?_⟩
  rw [mem_iUnion]
  refine ⟨mem_activeIndices_iff ρ i |>.2 ?_, hρ i ?_⟩
  · exact ⟨x, subset_tsupport (ρ i) hi.ne'⟩
  · exact subset_tsupport (ρ i) hi.ne'

end PartitionOfUnity

section Supported

variable {P R X T : Type*} {S : Set X}

/-- Reparametrizing a supported family preserves its support. -/
theorem supported_comp_param (f : P × X → T) (u : R × X → P)
    (hf : Supported f S) :
    Supported (fun q : R × X => f (u q, q.2)) S := by
  intro r r' x hx
  exact hf (u (r, x)) (u (r', x)) x hx

/-- A family is supported wherever its parameter map can vary. -/
theorem supported_comp_of_param_eq (f : P × X → T) (u : R × X → P)
    (hu : ∀ r r' : R, ∀ x ∉ S, u (r, x) = u (r', x)) :
    Supported (fun q : R × X => f (u q, q.2)) S := by
  intro r r' x hx
  change f (u (r, x), x) = f (u (r', x), x)
  rw [hu r r' x hx]

theorem adaptedTo_of_param_eq {ι : Type*} (U : ι → Set X) (k : ℕ)
    (A : Finset ι) (hA : A.card ≤ k) (f : P × X → T) (u : R × X → P)
    (hu : ∀ r r' : R, ∀ x ∉ ⋃ i ∈ A, U i, u (r, x) = u (r', x)) :
    AdaptedTo U k (fun q : R × X => f (u q, q.2)) :=
  ⟨A, hA, supported_comp_of_param_eq f u hu⟩

end Supported

section Fragmentation

variable {k : ℕ} {ι X : Type*} [TopologicalSpace X]
  {P : Set (Fin k → ℝ)} (U : ι → Set X)

/-- A face-preserving parameter deformation with the cellwise support bound
needed in the continuous part of Lemma B.0.1. -/
structure Fragmentation where
  subdivision : Subdivision P
  parameter : C(I × P × X, P)
  parameter_zero : ∀ p : P, ∀ x : X, parameter (0, p, x) = p
  cellwise : ∀ D ∈ subdivision.complex.facets,
    ∃ A : Finset ι, A.card ≤ k ∧
      ∀ p p' : closedCell P D, ∀ x ∉ ⋃ i ∈ A, U i,
        parameter (1, p.1, x) = parameter (1, p'.1, x)
  preserves_boundary : ∀ Q : Set P, IsBoundarySubpolyhedron Q →
    ∀ t : I, ∀ p : Q, ∀ x : X, parameter (t, p.1, x) ∈ Q

namespace Fragmentation

variable {U}

def postcompose {T : Type*} [TopologicalSpace T] (d : Fragmentation (P := P) U)
    (f : C(P × X, T)) : C(I × P × X, T) :=
  f.comp <| ContinuousMap.prodMk d.parameter (ContinuousMap.snd.comp ContinuousMap.snd)

@[simp]
theorem postcompose_apply {T : Type*} [TopologicalSpace T]
    (d : Fragmentation (P := P) U)
    (f : C(P × X, T)) (q : I × P × X) :
    d.postcompose f q = f (d.parameter q, q.2.2) :=
  rfl

theorem postcompose_zero {T : Type*} [TopologicalSpace T]
    (d : Fragmentation (P := P) U)
    (f : C(P × X, T)) (p : P) (x : X) :
    d.postcompose f (0, p, x) = f (p, x) := by
  simp [d.parameter_zero]

theorem postcompose_adapted {T : Type*} [TopologicalSpace T]
    (d : Fragmentation (P := P) U)
    (f : C(P × X, T)) (D : Finset (Fin k → ℝ))
    (hD : D ∈ d.subdivision.complex.facets) :
    AdaptedTo U k
      (fun q : closedCell P D × X => d.postcompose f (1, q.1.1, q.2)) := by
  obtain ⟨A, hA, hparam⟩ := d.cellwise D hD
  refine ⟨A, hA, ?_⟩
  intro p p' x hx
  change f (d.parameter (1, p.1, x), x) = f (d.parameter (1, p'.1, x), x)
  rw [hparam p p' x hx]

theorem postcompose_supported {T : Type*} [TopologicalSpace T]
    (d : Fragmentation (P := P) U)
    (f : C(P × X, T)) (S : Set X) (hf : Supported (f := f.toFun) S) :
    Supported (fun q : (I × P) × X => d.postcompose f (q.1.1, q.1.2, q.2)) S := by
  change Supported
    (fun q : (I × P) × X => f (d.parameter (q.1.1, q.1.2, q.2), q.2)) S
  exact supported_comp_param f.toFun
    (fun q : (I × P) × X => d.parameter (q.1.1, q.1.2, q.2)) hf

theorem postcompose_supported_boundary {T : Type*} [TopologicalSpace T]
    (d : Fragmentation (P := P) U) (f : C(P × X, T)) (Q : Set P)
    (hQ : IsBoundarySubpolyhedron Q) (S : Set X)
    (hf : Supported (fun q : Q × X => f (q.1.1, q.2)) S) :
    Supported (fun q : (I × Q) × X => d.postcompose f (q.1.1, q.1.2.1, q.2)) S := by
  let u : (I × Q) × X → Q := fun q =>
    ⟨d.parameter (q.1.1, q.1.2.1, q.2), d.preserves_boundary Q hQ q.1.1 q.1.2 q.2⟩
  have h := supported_comp_param
    (fun q : Q × X => f (q.1.1, q.2)) u hf
  simpa [u] using h

theorem result {T : Type*} [TopologicalSpace T] (d : Fragmentation (P := P) U)
    (f : C(P × X, T)) :
    ∃ F : C(I × P × X, T),
      (∀ p : P, ∀ x : X, F (0, p, x) = f (p, x)) ∧
      (∃ K : Subdivision P,
         ∀ D ∈ K.complex.facets,
            AdaptedTo U k
              (fun q : closedCell P D × X => F (1, q.1.1, q.2))) ∧
      (∀ S : Set X, Supported (f := f.toFun) S →
          Supported (fun q : (I × P) × X => F (q.1.1, q.1.2, q.2)) S) ∧
      (∀ Q : Set P, IsBoundarySubpolyhedron Q →
        ∀ S' : Set X,
          Supported (fun q : Q × X => f (q.1.1, q.2)) S' →
            Supported (fun q : (I × Q) × X => F (q.1.1, q.1.2.1, q.2)) S') := by
  refine ⟨d.postcompose f, d.postcompose_zero f, ?_, d.postcompose_supported f, ?_⟩
  · exact ⟨d.subdivision, d.postcompose_adapted f⟩
  · exact d.postcompose_supported_boundary f

end Fragmentation

end Fragmentation

section VariableSlices

variable {P X T : Type*} [MetricSpace P] [MetricSpace X] [MetricSpace T]

theorem inverseSlice_lipschitz (f : P × X → T) (slice : P → (X ≃ₜ T))
    (h_slice_eq : ∀ p : P, ∀ x : X, f (p, x) = slice p x)
    (L : NNReal) (hf_joint : LipschitzWith L f)
    (hf_slice_inv : ∀ p : P, LipschitzWith L (slice p).symm) (y : T) :
    LipschitzWith (L * L) (fun p : P => (slice p).symm y) := by
  apply LipschitzWith.of_dist_le_mul
  intro p p'
  let z : X := (slice p').symm y
  calc
    dist ((slice p).symm y) ((slice p').symm y) =
        dist ((slice p).symm y) ((slice p).symm (slice p z)) := by simp [z]
    _ ≤ L * dist y (slice p z) := (hf_slice_inv p).dist_le_mul _ _
    _ = L * dist (f (p', z)) (f (p, z)) := by simp [h_slice_eq, z]
    _ ≤ L * (L * dist (p', z) (p, z)) := by
      gcongr
      exact hf_joint.dist_le_mul _ _
    _ = (L * L) * dist p p' := by
      simp [Prod.dist_eq, dist_comm, mul_assoc]

theorem variableSliceHomeomorph [CompactSpace X] [Nonempty X]
    (f : P × X → T) (slice : P → (X ≃ₜ T))
    (h_slice_eq : ∀ p : P, ∀ x : X, f (p, x) = slice p x)
    (L C : NNReal) (hf_joint : LipschitzWith L f)
    (hf_slice_inv : ∀ p : P, LipschitzWith L (slice p).symm)
    (g : X → P) (hg : LipschitzWith C g) (hsmall : L * L * C < 1) :
    ∃ e : X ≃ₜ T,
      (∀ x : X, e x = f (g x, x)) ∧
      LipschitzWith (L * max C 1) e ∧
      LipschitzWith (L / (1 - L * L * C)) e.symm := by
  let q : NNReal := L * L * C
  let forward : X → T := fun x => f (g x, x)
  let fixedMap : T → X → X := fun y x => (slice (g x)).symm y
  have hfixedMap (y : T) : ContractingWith q (fixedMap y) := by
    refine ⟨hsmall, ?_⟩
    simpa [q, fixedMap, Function.comp_def, mul_assoc] using
      (inverseSlice_lipschitz f slice h_slice_eq L hf_joint hf_slice_inv y).comp hg
  let inverse : T → X := fun y => (hfixedMap y).fixedPoint (fixedMap y)
  have hinverse_fixed (y : T) : Function.IsFixedPt (fixedMap y) (inverse y) := by
    exact (hfixedMap y).fixedPoint_isFixedPt
  have hforward_lipschitz : LipschitzWith (L * max C 1) forward := by
    simpa [forward, Function.comp_def] using hf_joint.comp (hg.prodMk LipschitzWith.id)
  have hinverse_lipschitz : LipschitzWith (L / (1 - q)) inverse := by
    apply LipschitzWith.of_dist_le_mul
    intro y y'
    have hdist : ∀ z : X, dist (fixedMap y z) (fixedMap y' z) ≤ L * dist y y' := by
      intro z
      exact (hf_slice_inv (g z)).dist_le_mul _ _
    have hle := (hfixedMap y).fixedPoint_lipschitz_in_map (hfixedMap y') hdist
    change dist (inverse y) (inverse y') ≤
      ((L / (1 - q) : NNReal) : ℝ) * dist y y'
    calc
      dist (inverse y) (inverse y') ≤
          (L : ℝ) * dist y y' / (1 - (q : ℝ)) := by
        simpa [inverse] using hle
      _ = ((L / (1 - q) : NNReal) : ℝ) * dist y y' := by
        rw [NNReal.coe_div, NNReal.coe_sub hsmall.le]
        simp only [q, NNReal.coe_mul, NNReal.coe_one]
        ring
  have hleft : Function.LeftInverse inverse forward := by
    intro x
    have hx : Function.IsFixedPt (fixedMap (forward x)) x := by
      change fixedMap (forward x) x = x
      simp [fixedMap, forward, h_slice_eq]
    exact ((hfixedMap (forward x)).fixedPoint_unique hx).symm
  have hright : Function.RightInverse inverse forward := by
    intro y
    have hfix := hinverse_fixed y
    change forward (inverse y) = y
    calc
      forward (inverse y) = slice (g (inverse y)) (inverse y) := by
        simp [forward, h_slice_eq]
      _ = slice (g (inverse y)) (fixedMap y (inverse y)) := by rw [hfix.eq]
      _ = y := by simp [fixedMap]
  let e : X ≃ₜ T :=
    { toEquiv :=
        { toFun := forward
          invFun := inverse
          left_inv := hleft
          right_inv := hright }
      continuous_toFun := hforward_lipschitz.continuous
      continuous_invFun := hinverse_lipschitz.continuous }
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    rfl
  · exact hforward_lipschitz
  · change LipschitzWith (L / (1 - L * L * C)) inverse
    simpa [q] using hinverse_lipschitz

end VariableSlices

section ControlledFragmentation

variable {k : ℕ} {ι X : Type*} [MetricSpace X]
  {P : Set (Fin k → ℝ)} (U : ι → Set X) (C : NNReal)

/-- A fragmentation whose parameter deformation varies uniformly Lipschitzly
in the source-space variable. -/
structure ControlledFragmentation extends Fragmentation (P := P) U where
  parameter_lipschitz : ∀ t : I, ∀ p : P,
    LipschitzWith C (fun x : X => parameter (t, p, x))

namespace ControlledFragmentation

variable {U C}

noncomputable def sliceAt [CompactSpace X] [Nonempty X]
    (d : ControlledFragmentation (P := P) U C)
    {T : Type*} [MetricSpace T] (f : P × X → T)
    (slice : P → (X ≃ₜ T))
    (h_slice_eq : ∀ p : P, ∀ x : X, f (p, x) = slice p x)
    (L : NNReal) (hf_joint : LipschitzWith L f)
    (hf_slice_inv : ∀ p : P, LipschitzWith L (slice p).symm)
    (hsmall : L * L * C < 1) (tp : I × P) : X ≃ₜ T :=
  Classical.choose <| variableSliceHomeomorph f slice h_slice_eq L C hf_joint
    hf_slice_inv (fun x => d.parameter (tp.1, tp.2, x))
      (d.parameter_lipschitz tp.1 tp.2) hsmall

theorem sliceAt_spec [CompactSpace X] [Nonempty X]
    (d : ControlledFragmentation (P := P) U C)
    {T : Type*} [MetricSpace T] (f : P × X → T)
    (slice : P → (X ≃ₜ T))
    (h_slice_eq : ∀ p : P, ∀ x : X, f (p, x) = slice p x)
    (L : NNReal) (hf_joint : LipschitzWith L f)
    (hf_slice_inv : ∀ p : P, LipschitzWith L (slice p).symm)
    (hsmall : L * L * C < 1) (tp : I × P) :
    (∀ x : X, d.sliceAt f slice h_slice_eq L hf_joint hf_slice_inv hsmall tp x =
      f (d.parameter (tp.1, tp.2, x), x)) ∧
    LipschitzWith (L * max C 1)
      (d.sliceAt f slice h_slice_eq L hf_joint hf_slice_inv hsmall tp) ∧
    LipschitzWith (L / (1 - L * L * C))
      (d.sliceAt f slice h_slice_eq L hf_joint hf_slice_inv hsmall tp).symm :=
  Classical.choose_spec <| variableSliceHomeomorph f slice h_slice_eq L C hf_joint
    hf_slice_inv (fun x => d.parameter (tp.1, tp.2, x))
      (d.parameter_lipschitz tp.1 tp.2) hsmall

theorem result [CompactSpace X] [Nonempty X]
    (d : ControlledFragmentation (P := P) U C)
    {T : Type*} [MetricSpace T] (f : C(P × X, T))
    (slice : P → (X ≃ₜ T))
    (h_slice_eq : ∀ p : P, ∀ x : X, f (p, x) = slice p x)
    (L : NNReal) (hf_joint : LipschitzWith L f.toFun)
    (hf_slice_inv : ∀ p : P, LipschitzWith L (slice p).symm)
    (hsmall : L * L * C < 1) :
    ∃ F : C(I × P × X, T), ∃ L' : NNReal, ∃ Slice : I × P → (X ≃ₜ T),
      (∀ p : P, ∀ x : X, F (0, p, x) = f (p, x)) ∧
      (∀ t : I, ∀ p : P, ∀ x : X, F (t, p, x) = Slice (t, p) x) ∧
      (∃ K : Subdivision P,
         ∀ D ∈ K.complex.facets,
            AdaptedTo U k
              (fun q : closedCell P D × X => F (1, q.1.1, q.2))) ∧
      (∀ S : Set X, Supported (f := f.toFun) S →
          Supported (fun q : (I × P) × X => F (q.1.1, q.1.2, q.2)) S) ∧
      (∀ Q : Set P, IsBoundarySubpolyhedron Q →
        ∀ S' : Set X,
          Supported (fun q : Q × X => f (q.1.1, q.2)) S' →
            Supported (fun q : (I × Q) × X => F (q.1.1, q.1.2.1, q.2)) S') ∧
      (∀ tp : I × P, LipschitzWith L' (Slice tp)) ∧
      (∀ tp : I × P, LipschitzWith L' (Slice tp).symm) := by
  let base := d.toFragmentation
  let Slice : I × P → (X ≃ₜ T) :=
    fun tp => d.sliceAt f.toFun slice h_slice_eq L hf_joint hf_slice_inv hsmall tp
  let L' := max (L * max C 1) (L / (1 - L * L * C))
  refine ⟨base.postcompose f, L', Slice, base.postcompose_zero f, ?_, ?_,
    base.postcompose_supported f, base.postcompose_supported_boundary f, ?_, ?_⟩
  · intro t p x
    exact (d.sliceAt_spec f.toFun slice h_slice_eq L hf_joint hf_slice_inv hsmall
      (t, p)).1 x |>.symm
  · exact ⟨base.subdivision, base.postcompose_adapted f⟩
  · intro tp
    exact (d.sliceAt_spec f.toFun slice h_slice_eq L hf_joint hf_slice_inv hsmall tp).2.1.weaken
      (le_max_left _ _)
  · intro tp
    exact (d.sliceAt_spec f.toFun slice h_slice_eq L hf_joint hf_slice_inv hsmall tp).2.2.weaken
      (le_max_right _ _)

end ControlledFragmentation

end ControlledFragmentation

end Submission.Helpers
