import Submission.HomologyDomination

namespace Submission.Helpers.DehnSommerville

open LeanEval.Combinatorics.DehnSommerville
open Set
open CarrierProto

noncomputable section

namespace FinitePolyhedron

/-! ### Relabeling finite complexes -/

noncomputable def relabelForwardCarrier
    {V E : Type*} [Fintype V] [LinearOrder V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (C : FiniteGeometricComplex E)
    (e : V ≃ GeometricVertex C)
    (hfaces : ∀ s : Finset V,
      s.map e.toEmbedding ∈ (abstractComplex C).faces ↔ s ∈ K.faces) :
    FaceCarrier K (abstractComplex C) where
  face := fun s => ⟨s.1.map e.toEmbedding, (hfaces s.1).mpr s.2⟩
  mono := by
    intro s t hst
    exact Finset.map_subset_map.mpr hst

noncomputable def relabelBackwardCarrier
    {V E : Type*} [Fintype V] [LinearOrder V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (C : FiniteGeometricComplex E)
    (e : V ≃ GeometricVertex C)
    (hfaces : ∀ s : Finset V,
      s.map e.toEmbedding ∈ (abstractComplex C).faces ↔ s ∈ K.faces) :
    FaceCarrier (abstractComplex C) K where
  face := fun s => by
    let t := s.1.map e.symm.toEmbedding
    refine ⟨t, ?_⟩
    apply (hfaces t).mp
    have ht : t.map e.toEmbedding = s.1 := by
      ext x
      simp [t]
    rw [ht]
    exact s.2
  mono := by
    intro s t hst
    exact Finset.map_subset_map.mpr hst

noncomputable def relabelForwardChainMap
    {V E : Type*} [Fintype V] [LinearOrder V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (C : FiniteGeometricComplex E)
    (e : V ≃ GeometricVertex C)
    (hfaces : ∀ s : Finset V,
      s.map e.toEmbedding ∈ (abstractComplex C).faces ↔ s ∈ K.faces) :
    AugChainMap K (abstractComplex C) :=
  carriedAugChainMap (relabelForwardCarrier K C e hfaces)

noncomputable def relabelBackwardChainMap
    {V E : Type*} [Fintype V] [LinearOrder V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (C : FiniteGeometricComplex E)
    (e : V ≃ GeometricVertex C)
    (hfaces : ∀ s : Finset V,
      s.map e.toEmbedding ∈ (abstractComplex C).faces ↔ s ∈ K.faces) :
    AugChainMap (abstractComplex C) K :=
  carriedAugChainMap (relabelBackwardCarrier K C e hfaces)

noncomputable def relabelChainHomotopyEquiv
    {V E : Type*} [Fintype V] [LinearOrder V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (C : FiniteGeometricComplex E)
    (e : V ≃ GeometricVertex C)
    (hfaces : ∀ s : Finset V,
      s.map e.toEmbedding ∈ (abstractComplex C).faces ↔ s ∈ K.faces) :
    AugChainHomotopyEquiv K (abstractComplex C) := by
  let A := relabelForwardCarrier K C e hfaces
  let B := relabelBackwardCarrier K C e hfaces
  let f := relabelForwardChainMap K C e hfaces
  let g := relabelBackwardChainMap K C e hfaces
  have hgf : CarriedBy (identityFaceCarrier K) (g.comp f) := by
    apply carriedBy_monoCarrier (A := faceCarrierComp B A)
    · intro s x hx
      obtain ⟨v, hv, hvx⟩ := Finset.mem_map.mp hx
      obtain ⟨u, hu, huv⟩ := Finset.mem_map.mp hv
      have hxu : x = u := by
        calc
          x = e.symm.toEmbedding v := hvx.symm
          _ = e.symm.toEmbedding (e.toEmbedding u) := congrArg _ huv.symm
          _ = u := by
            change e.symm (e u) = u
            exact e.symm_apply_apply u
      exact hxu ▸ hu
    · exact carriedBy_comp (carriedAugChainMap_carriedBy A)
        (carriedAugChainMap_carriedBy B)
  have hfg : CarriedBy (identityFaceCarrier (abstractComplex C)) (f.comp g) := by
    apply carriedBy_monoCarrier (A := faceCarrierComp A B)
    · intro s x hx
      obtain ⟨v, hv, hvx⟩ := Finset.mem_map.mp hx
      obtain ⟨u, hu, huv⟩ := Finset.mem_map.mp hv
      have hxu : x = u := by
        calc
          x = e.toEmbedding v := hvx.symm
          _ = e.toEmbedding (e.symm.toEmbedding u) := congrArg _ huv.symm
          _ = u := by
            change e (e.symm u) = u
            exact e.apply_symm_apply u
      exact hxu ▸ hu
    · exact carriedBy_comp (carriedAugChainMap_carriedBy B)
        (carriedAugChainMap_carriedBy A)
  exact
    { hom := f
      inv := g
      inv_hom := carrierHomotopy (identityFaceCarrier K) _ _ hgf
        (identityAugChainMap_carriedBy K)
      hom_inv := carrierHomotopy (identityFaceCarrier (abstractComplex C)) _ _ hfg
        (identityAugChainMap_carriedBy (abstractComplex C)) }

/-! ### The canonical realization -/

noncomputable def canonicalFiniteComplex {d : ℕ} (X : FiniteSimplicialSphere d) :
    FiniteGeometricComplex (Vertex X → ℝ) where
  K := canonicalComplex X
  finite_faces := finite_canonicalComplex_faces X

def canonicalGeometricVertex {d : ℕ} (X : FiniteSimplicialSphere d)
    (v : Vertex X) : GeometricVertex (canonicalFiniteComplex X) :=
  ⟨canonicalVertex X v, by
    change canonicalVertex X v ∈ (canonicalComplex X).vertices
    rw [Geometry.SimplicialComplex.vertices_eq]
    have hvvertices : v.1 ∈ X.K.vertices := v.2
    rw [Geometry.SimplicialComplex.vertices_eq] at hvvertices
    obtain ⟨t, ht⟩ := mem_iUnion.mp hvvertices
    obtain ⟨htface, hvt⟩ := mem_iUnion.mp ht
    have hsingle : ({v.1} : Finset _) ∈ X.K.faces :=
      X.K.down_closed htface (Finset.singleton_subset_iff.mpr hvt)
        (Finset.singleton_nonempty _)
    have hsingleton : ({v} : Finset (Vertex X)) ∈ (vertexComplex X).faces := by
      rw [mem_vertexComplex_faces]
      simpa [vertexEmbedding] using hsingle
    have hface : ({canonicalVertex X v} : Finset (Vertex X → ℝ)) ∈
        (canonicalComplex X).faces :=
      mem_canonicalComplex_faces.mpr ⟨{v}, hsingleton, by simp⟩
    exact mem_iUnion₂_of_mem hface (Finset.mem_singleton_self _)⟩

lemma canonicalGeometricVertex_injective {d : ℕ} (X : FiniteSimplicialSphere d) :
    Function.Injective (canonicalGeometricVertex X) := by
  intro v w h
  apply canonicalVertex_injective X
  exact congrArg Subtype.val h

def canonicalVertexEmbedding {d : ℕ} (X : FiniteSimplicialSphere d) :
    Vertex X ↪ (Vertex X → ℝ) :=
  ⟨canonicalVertex X, canonicalVertex_injective X⟩

lemma canonicalGeometricVertex_surjective {d : ℕ} (X : FiniteSimplicialSphere d) :
    Function.Surjective (canonicalGeometricVertex X) := by
  intro w
  have hw : w.1 ∈ (canonicalComplex X).vertices := w.2
  rw [Geometry.SimplicialComplex.vertices_eq] at hw
  obtain ⟨s, hs⟩ := mem_iUnion.mp hw
  obtain ⟨hsface, hws⟩ := mem_iUnion.mp hs
  obtain ⟨τ, _hτ, hsτ⟩ := mem_canonicalComplex_faces.mp hsface
  rw [hsτ] at hws
  obtain ⟨v, _hv, hvw⟩ := Finset.mem_image.mp hws
  refine ⟨v, ?_⟩
  apply Subtype.ext
  exact hvw

noncomputable def canonicalVertexEquiv {d : ℕ} (X : FiniteSimplicialSphere d) :
    Vertex X ≃ GeometricVertex (canonicalFiniteComplex X) :=
  Equiv.ofBijective (canonicalGeometricVertex X)
    ⟨canonicalGeometricVertex_injective X, canonicalGeometricVertex_surjective X⟩

@[simp]
lemma canonicalVertexEquiv_val {d : ℕ} (X : FiniteSimplicialSphere d)
    (v : Vertex X) :
    ((canonicalVertexEquiv X v : GeometricVertex (canonicalFiniteComplex X)) :
      Vertex X → ℝ) = canonicalVertex X v :=
  rfl

lemma image_canonicalVertexEquiv_mem_faces_iff {d : ℕ}
    (X : FiniteSimplicialSphere d) (s : Finset (Vertex X)) :
    s.map (canonicalVertexEquiv X).toEmbedding ∈
        (abstractComplex (canonicalFiniteComplex X)).faces ↔
      s ∈ (vertexComplex X).faces := by
  rw [mem_abstractComplex_faces]
  have hmap : (s.map (canonicalVertexEquiv X).toEmbedding).map
      (geometricVertexEmbedding (canonicalFiniteComplex X)) =
      s.map (canonicalVertexEmbedding X) := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hvx⟩ := Finset.mem_map.mp hx
      obtain ⟨u, hu, huv⟩ := Finset.mem_map.mp hv
      apply Finset.mem_map.mpr
      refine ⟨u, hu, ?_⟩
      rw [← hvx, ← huv]
      rfl
    · intro hx
      obtain ⟨u, hu, hux⟩ := Finset.mem_map.mp hx
      apply Finset.mem_map.mpr
      refine ⟨canonicalVertexEquiv X u,
        Finset.mem_map.mpr ⟨u, hu, rfl⟩, ?_⟩
      rw [← hux]
      rfl
  rw [hmap]
  change s.map (canonicalVertexEmbedding X) ∈ (canonicalComplex X).faces ↔ _
  rw [mem_canonicalComplex_faces]
  constructor
  · rintro ⟨t, ht, hst⟩
    have hts : t = s := by
      apply Finset.map_injective (canonicalVertexEmbedding X)
      have hst' : t.map (canonicalVertexEmbedding X) =
          s.map (canonicalVertexEmbedding X) := by
        ext x
        simpa [canonicalVertexEmbedding] using
          Finset.ext_iff.mp hst.symm x
      exact hst'
    rwa [← hts]
  · intro hs
    refine ⟨s, hs, ?_⟩
    ext x
    simp [canonicalVertexEmbedding]

noncomputable def canonicalRelabelEquiv {d : ℕ} (X : FiniteSimplicialSphere d) :
    AugChainHomotopyEquiv (vertexComplex X)
      (abstractComplex (canonicalFiniteComplex X)) :=
  relabelChainHomotopyEquiv (vertexComplex X) (canonicalFiniteComplex X)
    (canonicalVertexEquiv X) (image_canonicalVertexEquiv_mem_faces_iff X)

lemma chainEulerQ_canonical_eq_vertexComplex {d : ℕ}
    (X : FiniteSimplicialSphere d) :
    chainEulerQ (abstractComplex (canonicalFiniteComplex X)) =
      chainEulerQ (vertexComplex X) :=
  (chainEulerQ_eq_of_homotopyEquiv (canonicalRelabelEquiv X)).symm

/-! ### Face sums in the original vertex labels -/

abbrev OriginalAugmentedFace {d : ℕ} (X : FiniteSimplicialSphere d) :=
  augmentedFaces X

noncomputable instance {d : ℕ} (X : FiniteSimplicialSphere d) :
    Fintype (OriginalAugmentedFace X) :=
  (finite_augmentedFaces X).fintype

def vertexAugmentedFaceToOriginal {d : ℕ} (X : FiniteSimplicialSphere d) :
    AugmentedAbstractFace (vertexComplex X) → OriginalAugmentedFace X :=
  fun s => ⟨s.1.map (vertexEmbedding X), by
    rcases s.2 with hempty | hs
    · simp [hempty, augmentedFaces]
    · exact mem_augmentedFaces.mpr (Or.inr hs)⟩

lemma vertexAugmentedFaceToOriginal_injective {d : ℕ}
    (X : FiniteSimplicialSphere d) :
    Function.Injective (vertexAugmentedFaceToOriginal X) := by
  intro s t h
  apply Subtype.ext
  apply Finset.map_injective (vertexEmbedding X)
  exact congrArg Subtype.val h

lemma vertexAugmentedFaceToOriginal_surjective {d : ℕ}
    (X : FiniteSimplicialSphere d) :
    Function.Surjective (vertexAugmentedFaceToOriginal X) := by
  intro s
  rcases mem_augmentedFaces.mp s.2 with hempty | hs
  ·
    refine ⟨⟨∅, Or.inl rfl⟩, ?_⟩
    apply Subtype.ext
    change (∅ : Finset (EuclideanSpace ℝ (Fin d))) = s.1
    exact hempty.symm
  · let t := liftFace X s.1 hs
    have ht : t ∈ (vertexComplex X).faces := liftFace_mem_vertexComplex X s.1 hs
    refine ⟨⟨t, Or.inr ht⟩, ?_⟩
    apply Subtype.ext
    exact map_liftFace X s.1 hs

noncomputable def vertexAugmentedFaceEquivOriginal {d : ℕ}
    (X : FiniteSimplicialSphere d) :
    AugmentedAbstractFace (vertexComplex X) ≃ OriginalAugmentedFace X :=
  Equiv.ofBijective (vertexAugmentedFaceToOriginal X)
    ⟨vertexAugmentedFaceToOriginal_injective X,
      vertexAugmentedFaceToOriginal_surjective X⟩

lemma vertexAugmentedFaceEquivOriginal_card {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (s : AugmentedAbstractFace (vertexComplex X)) :
    (vertexAugmentedFaceEquivOriginal X s).1.card = s.1.card := by
  change (s.1.map (vertexEmbedding X)).card = s.1.card
  rw [Finset.card_map]

lemma chainEulerQ_vertexComplex_eq_originalFaceSum {d : ℕ}
    (X : FiniteSimplicialSphere d) :
    chainEulerQ (vertexComplex X) =
      ∑ s : OriginalAugmentedFace X, (-1 : ℚ) ^ s.1.card := by
  rw [chainEulerQ_eq_augmentedAbstractFaceSum]
  exact Fintype.sum_equiv (vertexAugmentedFaceEquivOriginal X)
    (fun s : AugmentedAbstractFace (vertexComplex X) => (-1 : ℚ) ^ s.1.card)
    (fun s : OriginalAugmentedFace X => (-1 : ℚ) ^ s.1.card)
    (fun s => by rw [vertexAugmentedFaceEquivOriginal_card])

lemma originalFaceSum_eq_augmentedEulerSum_cast {d : ℕ}
    (X : FiniteSimplicialSphere d) :
    (∑ s : OriginalAugmentedFace X, (-1 : ℚ) ^ s.1.card) =
      (augmentedEulerSum X : ℚ) := by
  rw [augmentedEulerSum]
  push_cast
  let e : {s // s ∈ augmentedFaceFinset X} ↪ OriginalAugmentedFace X :=
    ⟨fun s => ⟨s.1, mem_augmentedFaceFinset.mp s.2⟩,
      fun s t h => Subtype.ext
        (congrArg (fun z : OriginalAugmentedFace X => z.1) h)⟩
  let A : Finset (OriginalAugmentedFace X) :=
    (augmentedFaceFinset X).attach.map e
  have hA : A = Finset.univ := by
    ext s
    simp only [Finset.mem_univ, iff_true]
    rw [Finset.mem_map]
    let t : {u // u ∈ augmentedFaceFinset X} :=
      ⟨s.1, mem_augmentedFaceFinset.mpr s.2⟩
    refine ⟨t, by simp [t], ?_⟩
    apply Subtype.ext
    rfl
  rw [← hA]
  rw [Finset.sum_map]
  simpa [e] using (Finset.sum_attach (augmentedFaceFinset X)
    (fun s => (-1 : ℚ) ^ s.card))

lemma chainEulerQ_canonical_eq_augmentedEulerSum_cast {d : ℕ}
    (X : FiniteSimplicialSphere d) :
    chainEulerQ (abstractComplex (canonicalFiniteComplex X)) =
      (augmentedEulerSum X : ℚ) := by
  rw [chainEulerQ_canonical_eq_vertexComplex,
    chainEulerQ_vertexComplex_eq_originalFaceSum,
    originalFaceSum_eq_augmentedEulerSum_cast]

/-! ### Canonical face deletions -/

noncomputable def canonicalDeletionComplex {d : ℕ}
    (X : FiniteSimplicialSphere d) (τ : Finset (Vertex X)) :
    Geometry.SimplicialComplex ℝ (Vertex X → ℝ) where
  faces := {s | s ∈ (canonicalComplex X).faces ∧
    ¬τ.image (canonicalVertex X) ⊆ s}
  indep := fun hs => (canonicalComplex X).indep hs.1
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(canonicalComplex X).nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    refine ⟨(canonicalComplex X).down_closed hs.1 hts ht, ?_⟩
    intro hτt
    exact hs.2 (hτt.trans hts)
  inter_subset_convexHull := fun hs ht =>
    (canonicalComplex X).inter_subset_convexHull hs.1 ht.1

@[simp]
lemma mem_canonicalDeletionComplex_faces {d : ℕ}
    {X : FiniteSimplicialSphere d} {τ : Finset (Vertex X)}
    {s : Finset (Vertex X → ℝ)} :
    s ∈ (canonicalDeletionComplex X τ).faces ↔
      s ∈ (canonicalComplex X).faces ∧
        ¬τ.image (canonicalVertex X) ⊆ s :=
  Iff.rfl

lemma finite_canonicalDeletionComplex_faces {d : ℕ}
    (X : FiniteSimplicialSphere d) (τ : Finset (Vertex X)) :
    (canonicalDeletionComplex X τ).faces.Finite :=
  (finite_canonicalComplex_faces X).subset fun _ hs => hs.1

noncomputable def canonicalDeletionFiniteComplex {d : ℕ}
    (X : FiniteSimplicialSphere d) (τ : Finset (Vertex X)) :
    FiniteGeometricComplex (Vertex X → ℝ) where
  K := canonicalDeletionComplex X τ
  finite_faces := finite_canonicalDeletionComplex_faces X τ

end FinitePolyhedron

end

end Submission.Helpers.DehnSommerville
