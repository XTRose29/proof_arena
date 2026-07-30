import Submission.FragmentationConstruction

open Set Geometry
open unitInterval
open scoped Topology

namespace Submission.PartitionWeights

open _root_.FamiliesOfMapsB01
open Helpers FragmentationConstruction
open Polytope

variable {k : ℕ} {ι X : Type*} [TopologicalSpace X] [CompactSpace X]

noncomputable def ofPartitionOfUnity (U : ι → Set X)
    (ρ : PartitionOfUnity ι X univ) (hρ : ρ.IsSubordinate U) :
    WeightSystem U (activeIndices ρ).card where
  label j := ((activeIndices ρ).equivFin.symm j).1
  weight x j := ρ (((activeIndices ρ).equivFin.symm j).1) x
  continuous_weight j := (ρ (((activeIndices ρ).equivFin.symm j).1)).continuous
  nonneg x j := ρ.nonneg _ _
  sum_eq_one x := by
    calc
      ∑ j, ρ (((activeIndices ρ).equivFin.symm j).1) x =
          ∑ i : activeIndices ρ, ρ i.1 x := by
        exact (activeIndices ρ).equivFin.symm.sum_comp
          (fun i : activeIndices ρ => ρ i.1 x)
      _ = ∑ i ∈ activeIndices ρ, ρ i x := by
        rw [← Finset.attach_eq_univ]
        exact Finset.sum_attach (activeIndices ρ) (fun i => ρ i x)
      _ = 1 := sum_activeIndices_eq_one ρ x
  zero_outside j x hx := by
    by_contra hne
    apply hx
    exact hρ _ (subset_tsupport _ hne)

noncomputable def emptyFragmentation
    {P : Set (Fin k → ℝ)} (S : Finset (Fin k → ℝ))
    (hP : P = convexHull ℝ (S : Set (Fin k → ℝ)))
    (U : ι → Set X) [IsEmpty X] : Helpers.Fragmentation (P := P) U where
  subdivision :=
    { complex := barycentricComplex S
      faces_finite := barycentricComplex_faces_finite S
      space_eq := by rw [barycentricComplex_space, ← hP] }
  parameter :=
    { toFun := fun q => q.2.1
      continuous_toFun := continuous_fst.comp continuous_snd }
  parameter_zero := by
    intro p x
    exact isEmptyElim x
  cellwise := by
    intro D hD
    refine ⟨∅, by simp, ?_⟩
    intro p p' x hx
    exact isEmptyElim x
  preserves_boundary := by
    intro Q hQ t p x
    exact isEmptyElim x

theorem continuous_result
    {P : Set (Fin k → ℝ)} (hP : IsPolyhedron P)
    (U : ι → Set X) (ρ : PartitionOfUnity ι X univ)
    (hρ : ρ.IsSubordinate U) {T : Type*} [TopologicalSpace T]
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
  obtain ⟨S, hPS⟩ := hP
  rcases isEmpty_or_nonempty X with hX | hX
  · letI : IsEmpty X := hX
    exact (emptyFragmentation S hPS U).result f
  · letI : Nonempty X := hX
    let W := ofPartitionOfUnity U ρ hρ
    have hn : 0 < (activeIndices ρ).card := W.positive_card
    subst P
    exact (fragmentation W S hn).result f

end Submission.PartitionWeights
