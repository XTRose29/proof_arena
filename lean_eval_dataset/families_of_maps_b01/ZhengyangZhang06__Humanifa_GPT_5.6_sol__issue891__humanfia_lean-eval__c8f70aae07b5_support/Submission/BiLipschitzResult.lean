import Submission.ControlledConstruction

open Set Geometry
open unitInterval
open scoped Topology

namespace Submission.BiLipschitzResult

open _root_.FamiliesOfMapsB01
open Helpers FragmentationConstruction PartitionWeights
open LipschitzWeights ControlledConstruction GridDeformation

variable {k : ℕ}

theorem empty_result
    {X T : Type*} [MetricSpace X] [MetricSpace T] [CompactSpace X] [IsEmpty X]
    {P : Set (Fin k → ℝ)} (hP : IsPolyhedron P)
    {ι : Type*} (U : ι → Set X)
    (f : C(P × X, T)) (slice : P → (X ≃ₜ T)) (L : NNReal)
    (hf_slice_inv : ∀ p : P, LipschitzWith L (slice p).symm) :
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
  obtain ⟨S, hPS⟩ := hP
  obtain ⟨F, hzero, hadapt, hsupported, hboundary⟩ :=
    (emptyFragmentation S hPS U).result f
  refine ⟨F, L, (fun tp => slice tp.2), hzero, ?_, hadapt,
    hsupported, hboundary, ?_, ?_⟩
  · intro t p x
    exact isEmptyElim x
  · intro tp x
    exact isEmptyElim x
  · intro tp
    exact hf_slice_inv tp.2

theorem nonempty_result
    {X T : Type*} [MetricSpace X] [MetricSpace T] [CompactSpace X] [Nonempty X]
    {P : Set (Fin k → ℝ)} (hP : IsPolyhedron P)
    {ι : Type*}
    (U : ι → Set X) (hUopen : ∀ α, IsOpen (U α))
    (ρ : PartitionOfUnity ι X univ) (hρ : ρ.IsSubordinate U)
    (f : C(P × X, T))
    (slice : P → (X ≃ₜ T))
    (h_slice_eq : ∀ p : P, ∀ x : X, f (p, x) = slice p x)
    (L : NNReal)
    (hf_joint : LipschitzWith L f.toFun)
    (hf_slice_inv : ∀ p : P, LipschitzWith L (slice p).symm) :
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
  obtain ⟨S, hPS⟩ := hP
  subst P
  let D : CoverData ι X :=
    { U := U
      isOpen := hUopen
      rho := ρ
      subordinate := hρ }
  let M := repetitionCount D S L
  have hM : 0 < M := repetitionCount_pos D S L
  let W := repeatedWeightSystem D M hM
  have hn : 0 < M * m D := Nat.mul_pos hM (m_pos D)
  let K := blockLipschitzConstant D M
  have hW : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      LipschitzWith K (fun x => cdf (W.weight x) s) := by
    intro s hs0 hs1
    simpa only [K, W] using repeatedCdf_lipschitz D M hM s ⟨hs0, hs1⟩
  let d := controlledFragmentation W S hn K hW
  have hsmall :
      L * L *
          (decodeConstant S * (K + K)) < 1 := by
    simpa only [K, M] using repeated_control_small D S L
  exact d.result f slice h_slice_eq L hf_joint hf_slice_inv hsmall

theorem result
    {X T : Type*} [MetricSpace X] [MetricSpace T] [CompactSpace X]
    {P : Set (Fin k → ℝ)} (hP : IsPolyhedron P)
    {ι : Type*}
    (U : ι → Set X) (hUopen : ∀ α, IsOpen (U α))
    (ρ : PartitionOfUnity ι X univ) (hρ : ρ.IsSubordinate U)
    (f : C(P × X, T))
    (slice : P → (X ≃ₜ T))
    (h_slice_eq : ∀ p : P, ∀ x : X, f (p, x) = slice p x)
    (L : NNReal)
    (hf_joint : LipschitzWith L f.toFun)
    (hf_slice_inv : ∀ p : P, LipschitzWith L (slice p).symm) :
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
  rcases isEmpty_or_nonempty X with hX | hX
  · letI : IsEmpty X := hX
    exact empty_result hP U f slice L hf_slice_inv
  · letI : Nonempty X := hX
    exact nonempty_result hP U hUopen ρ hρ f slice h_slice_eq L hf_joint hf_slice_inv

end Submission.BiLipschitzResult
