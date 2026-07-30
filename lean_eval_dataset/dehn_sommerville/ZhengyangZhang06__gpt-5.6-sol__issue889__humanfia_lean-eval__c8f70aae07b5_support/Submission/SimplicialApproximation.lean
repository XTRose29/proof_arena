import Submission.Carrier

namespace Submission.Helpers.DehnSommerville

open Set
open CarrierProto
open unitInterval

noncomputable section

namespace FinitePolyhedron

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev GeometricVertex (C : FiniteGeometricComplex E) := C.K.vertices

lemma finite_geometricVertices (C : FiniteGeometricComplex E) :
    C.K.vertices.Finite := by
  rw [Geometry.SimplicialComplex.vertices_eq]
  exact C.finite_faces.biUnion fun s _ => s.finite_toSet

noncomputable instance geometricVertexFintype (C : FiniteGeometricComplex E) :
    Fintype (GeometricVertex C) :=
  (finite_geometricVertices C).fintype

noncomputable instance geometricVertexLinearOrder (C : FiniteGeometricComplex E) :
    LinearOrder (GeometricVertex C) :=
  LinearOrder.lift' (Fintype.equivFin (GeometricVertex C))
    (Fintype.equivFin (GeometricVertex C)).injective

def geometricVertexEmbedding (C : FiniteGeometricComplex E) :
    GeometricVertex C ↪ E :=
  ⟨Subtype.val, Subtype.val_injective⟩

def abstractComplex (C : FiniteGeometricComplex E) :
    PreAbstractSimplicialComplex (GeometricVertex C) where
  faces := {s | s.map (geometricVertexEmbedding C) ∈ C.K.faces}
  isRelLowerSet_faces := by
    intro s hs
    constructor
    · exact Finset.map_nonempty.mp (C.K.nonempty_of_mem_faces hs)
    · intro t hts ht
      exact C.K.down_closed hs (Finset.map_subset_map.mpr hts)
        (Finset.map_nonempty.mpr ht)

@[simp]
lemma mem_abstractComplex_faces {C : FiniteGeometricComplex E}
    {s : Finset (GeometricVertex C)} :
    s ∈ (abstractComplex C).faces ↔
      s.map (geometricVertexEmbedding C) ∈ C.K.faces :=
  Iff.rfl

def vertexPoint (C : FiniteGeometricComplex E) (v : GeometricVertex C) : C.K.space :=
  ⟨v.1, C.K.vertices_subset_space v.2⟩

lemma isCompact_space (C : FiniteGeometricComplex E) : IsCompact C.K.space := by
  rw [Geometry.SimplicialComplex.space]
  exact C.finite_faces.isCompact_biUnion fun s _ =>
    s.finite_toSet.isCompact_convexHull ℝ

def faceVertexEmbedding (C : FiniteGeometricComplex E) (G : GeometricFace C) :
    G.1 ↪ GeometricVertex C where
  toFun := fun x => ⟨x.1, by
    change x.1 ∈ C.K.vertices
    rw [Geometry.SimplicialComplex.vertices_eq]
    exact mem_iUnion₂_of_mem G.2 x.2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : GeometricVertex C => (z : E)) h

def liftGeometricFace (C : FiniteGeometricComplex E) (G : GeometricFace C) :
    Finset (GeometricVertex C) :=
  G.1.attach.map (faceVertexEmbedding C G)

lemma map_liftGeometricFace (C : FiniteGeometricComplex E) (G : GeometricFace C) :
    (liftGeometricFace C G).map (geometricVertexEmbedding C) = G.1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hvx⟩ := Finset.mem_map.mp hx
    obtain ⟨a, ha, hav⟩ := Finset.mem_map.mp hv
    have hav' : (a : E) = (v : E) :=
      congrArg (fun z : GeometricVertex C => (z : E)) hav
    have hvx' : (v : E) = x := by
      simpa [geometricVertexEmbedding] using hvx
    rw [← hvx', ← hav']
    exact a.2
  · intro hx
    let a : G.1 := ⟨x, hx⟩
    let v : GeometricVertex C := faceVertexEmbedding C G a
    apply Finset.mem_map.mpr
    refine ⟨v, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨a, Finset.mem_attach _ _, rfl⟩
    · rfl

lemma liftGeometricFace_mem (C : FiniteGeometricComplex E) (G : GeometricFace C) :
    liftGeometricFace C G ∈ (abstractComplex C).faces := by
  rw [mem_abstractComplex_faces, map_liftGeometricFace]
  exact G.2

def faceUnionWithout (C : FiniteGeometricComplex E) (v : GeometricVertex C) : Set E :=
  ⋃ G : GeometricFace C,
    if (v : E) ∈ G.1 then ∅ else convexHull ℝ (G.1 : Set E)

lemma isClosed_faceUnionWithout [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) (v : GeometricVertex C) :
    IsClosed (faceUnionWithout C v) := by
  apply isClosed_iUnion_of_finite
  intro G
  split_ifs
  · exact isClosed_empty
  · exact G.1.finite_toSet.isClosed_convexHull ℝ

def openStar (C : FiniteGeometricComplex E) (v : GeometricVertex C) : Set C.K.space :=
  {x | x.1 ∉ faceUnionWithout C v}

@[simp]
lemma mem_openStar_iff (C : FiniteGeometricComplex E) (v : GeometricVertex C)
    (x : C.K.space) :
    x ∈ openStar C v ↔ x.1 ∉ faceUnionWithout C v :=
  Iff.rfl

lemma isOpen_openStar [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) (v : GeometricVertex C) :
    IsOpen (openStar C v) := by
  change IsOpen ((Subtype.val ⁻¹' faceUnionWithout C v)ᶜ)
  exact (isClosed_faceUnionWithout C v).preimage continuous_subtype_val |>.isOpen_compl

lemma faceCenterPoint_mem_openStar [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) (G : GeometricFace C)
    {v : GeometricVertex C} (hv : (v : E) ∈ G.1) :
    (⟨faceCenter C G,
      C.K.convexHull_subset_space G.2 (faceCenter_mem C G)⟩ : C.K.space) ∈
      openStar C v := by
  intro h
  rw [faceUnionWithout] at h
  obtain ⟨H, hH⟩ := mem_iUnion.mp h
  split_ifs at hH with hvH
  · exact hH.elim
  · have hinter : faceCenter C G ∈
        convexHull ℝ ((G.1 ∩ H.1 : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using
        C.K.inter_subset_convexHull G.2 H.2 ⟨faceCenter_mem C G, hH⟩
    have hsub := face_subset_of_center_mem_convexHull C G
      (s := G.1 ∩ H.1) Finset.inter_subset_left hinter
    exact hvH (Finset.inter_subset_right (hsub hv))

lemma vertexPoint_mem_openStar [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) (v : GeometricVertex C) :
    vertexPoint C v ∈ openStar C v := by
  have hvfaces : v.1 ∈ ⋃ s ∈ C.K.faces, (s : Set E) := by
    simpa only [← Geometry.SimplicialComplex.vertices_eq] using v.2
  obtain ⟨s, hs⟩ := mem_iUnion.mp hvfaces
  obtain ⟨hsface, hvs⟩ := mem_iUnion.mp hs
  let G : GeometricFace C :=
    ⟨{v.1}, C.K.down_closed hsface
      (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty _)⟩
  have hcenter := faceCenterPoint_mem_openStar C G (v := v) (by simp [G])
  have hc : faceCenter C G = v.1 := by
    change ({v.1} : Finset E).centroid ℝ id = v.1
    rw [Finset.centroid_singleton]
    rfl
  have hp : (⟨faceCenter C G,
      C.K.convexHull_subset_space G.2 (faceCenter_mem C G)⟩ : C.K.space) =
      vertexPoint C v := Subtype.ext hc
  rw [hp] at hcenter
  exact hcenter

lemma exists_minimal_face (C : FiniteGeometricComplex E) (x : C.K.space) :
    ∃ G : GeometricFace C,
      x.1 ∈ convexHull ℝ (G.1 : Set E) ∧
      ∀ H : GeometricFace C,
        x.1 ∈ convexHull ℝ (H.1 : Set E) → G.1.card ≤ H.1.card := by
  let candidates : Finset (GeometricFace C) :=
    Finset.univ.filter fun G => x.1 ∈ convexHull ℝ (G.1 : Set E)
  have hcandidates : candidates.Nonempty := by
    obtain ⟨s, hs, hxs⟩ := C.K.mem_space_iff.mp x.2
    exact ⟨⟨s, hs⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxs⟩⟩
  obtain ⟨G, hG, hmin⟩ := candidates.exists_min_image (fun H => H.1.card) hcandidates
  refine ⟨G, (Finset.mem_filter.mp hG).2, ?_⟩
  intro H hxH
  exact hmin H (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxH⟩)

lemma exists_openStar [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) (x : C.K.space) :
    ∃ v : GeometricVertex C, x ∈ openStar C v := by
  obtain ⟨G, hxG, hmin⟩ := exists_minimal_face C x
  obtain ⟨v, hvG⟩ := C.K.nonempty_of_mem_faces G.2
  let v' : GeometricVertex C :=
    ⟨v, by
      change v ∈ C.K.vertices
      rw [Geometry.SimplicialComplex.vertices_eq]
      exact mem_iUnion₂_of_mem G.2 hvG⟩
  refine ⟨v', ?_⟩
  intro hx
  rw [faceUnionWithout] at hx
  obtain ⟨H, hxH⟩ := mem_iUnion.mp hx
  split_ifs at hxH with hvH
  · exact hxH.elim
  · have hinter : x.1 ∈ convexHull ℝ ((G.1 ∩ H.1 : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using
        C.K.inter_subset_convexHull G.2 H.2 ⟨hxG, hxH⟩
    have hne : (G.1 ∩ H.1).Nonempty := by
      by_contra hne
      have hempty : G.1 ∩ H.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hempty] at hinter
      simp at hinter
    let J : GeometricFace C :=
      ⟨G.1 ∩ H.1, C.K.down_closed G.2 Finset.inter_subset_left hne⟩
    have hle := hmin J hinter
    have hlt : J.1.card < G.1.card := by
      apply Finset.card_lt_card
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro hGI
      have hvI : v ∈ G.1 ∩ H.1 := hGI hvG
      exact hvH (Finset.mem_inter.mp hvI).2
    omega

lemma iUnion_openStar_eq_univ [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) :
    (⋃ v : GeometricVertex C, openStar C v) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨v, hv⟩ := exists_openStar C x
  exact mem_iUnion.mpr ⟨v, hv⟩

lemma face_of_common_openStar [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) {s : Finset (GeometricVertex C)}
    (hs : s.Nonempty) {x : C.K.space}
    (hx : ∀ v ∈ s, x ∈ openStar C v) :
    s ∈ (abstractComplex C).faces := by
  obtain ⟨G, hG, hxG⟩ := C.K.mem_space_iff.mp x.2
  rw [mem_abstractComplex_faces]
  apply C.K.down_closed hG
  · intro y hy
    obtain ⟨v, hvs, rfl⟩ := Finset.mem_map.mp hy
    by_contra hvG
    exact (hx v hvs) <| by
      rw [faceUnionWithout]
      refine mem_iUnion.mpr ⟨⟨G, hG⟩, ?_⟩
      change (v : E) ∉ G at hvG
      rw [if_neg hvG]
      exact hxG
  · exact Finset.map_nonempty.mpr hs

lemma dist_vertexPoint_le_mesh [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) {v : GeometricVertex C}
    {x : C.K.space} (hx : x ∈ openStar C v) :
    dist x (vertexPoint C v) ≤ complexMesh C := by
  obtain ⟨G, hG, hxG⟩ := C.K.mem_space_iff.mp x.2
  have hvG : (v : E) ∈ G := by
    by_contra hvG
    exact hx <| by
      rw [faceUnionWithout]
      refine mem_iUnion.mpr ⟨⟨G, hG⟩, ?_⟩
      rw [if_neg hvG]
      exact hxG
  calc
    dist x (vertexPoint C v) = dist x.1 v.1 := rfl
    _ ≤ Metric.diam (convexHull ℝ (G : Set E)) := by
      exact Metric.dist_le_diam_of_mem
        (isBounded_convexHull.mpr G.finite_toSet.isBounded)
        hxG (subset_convexHull ℝ (G : Set E) hvG)
    _ = Metric.diam (G : Set E) := convexHull_diam (G : Set E)
    _ = faceDiameter C ⟨G, hG⟩ := rfl
    _ ≤ complexMesh C := faceDiameter_le_complexMesh C ⟨G, hG⟩

structure SimplicialVertexMap (C : FiniteGeometricComplex E)
    (D : FiniteGeometricComplex F) where
  toFun : GeometricVertex C → GeometricVertex D
  maps_face : ∀ {s : Finset (GeometricVertex C)},
    s ∈ (abstractComplex C).faces →
      s.image toFun ∈ (abstractComplex D).faces

instance (C : FiniteGeometricComplex E) (D : FiniteGeometricComplex F) :
    CoeFun (SimplicialVertexMap C D)
      (fun _ => GeometricVertex C → GeometricVertex D) :=
  ⟨SimplicialVertexMap.toFun⟩

def SimplicialVertexMap.faceCarrier
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (φ : SimplicialVertexMap C D) :
    FaceCarrier (abstractComplex C) (abstractComplex D) where
  face := fun s => ⟨s.1.image φ, φ.maps_face s.2⟩
  mono := by
    intro s t hst x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨v, hst hv, rfl⟩

noncomputable def SimplicialVertexMap.chainMap
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (φ : SimplicialVertexMap C D) :
    AugChainMap (abstractComplex C) (abstractComplex D) :=
  carriedAugChainMap φ.faceCarrier

def SimplicialVertexMap.Approximates
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (φ : SimplicialVertexMap C D) (f : C.K.space → D.K.space) : Prop :=
  ∀ v, MapsTo f (openStar C v) (openStar D (φ v))

lemma maps_face_of_approximates [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (φ : GeometricVertex C → GeometricVertex D)
    (f : C.K.space → D.K.space)
    (hφ : ∀ v, MapsTo f (openStar C v) (openStar D (φ v)))
    {s : Finset (GeometricVertex C)} (hs : s ∈ (abstractComplex C).faces) :
    s.image φ ∈ (abstractComplex D).faces := by
  let G : GeometricFace C :=
    ⟨s.map (geometricVertexEmbedding C), hs⟩
  let x : C.K.space :=
    ⟨faceCenter C G, C.K.convexHull_subset_space G.2 (faceCenter_mem C G)⟩
  have hsne : s.Nonempty := ((abstractComplex C).isRelLowerSet_faces hs).1
  apply face_of_common_openStar D (Finset.image_nonempty.mpr hsne)
  intro w hw
  obtain ⟨v, hvs, rfl⟩ := Finset.mem_image.mp hw
  apply hφ v
  apply faceCenterPoint_mem_openStar C G
  rw [show G.1 = s.map (geometricVertexEmbedding C) from rfl]
  exact Finset.mem_map.mpr ⟨v, hvs, rfl⟩

noncomputable def approximationVertex [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (f : C.K.space → D.K.space) (δ : ℝ)
    (hcover : ∀ x : C.K.space, ∃ w : GeometricVertex D,
      Metric.ball x δ ⊆ f ⁻¹' openStar D w)
    (v : GeometricVertex C) : GeometricVertex D :=
  Classical.choose (hcover (vertexPoint C v))

lemma approximationVertex_spec [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (f : C.K.space → D.K.space) (δ : ℝ)
    (hcover : ∀ x : C.K.space, ∃ w : GeometricVertex D,
      Metric.ball x δ ⊆ f ⁻¹' openStar D w)
    (v : GeometricVertex C) :
    Metric.ball (vertexPoint C v) δ ⊆
      f ⁻¹' openStar D (approximationVertex f δ hcover v) :=
  Classical.choose_spec (hcover (vertexPoint C v))

noncomputable def simplicialApproximationOfCover
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (f : C.K.space → D.K.space) (δ : ℝ)
    (hcover : ∀ x : C.K.space, ∃ w : GeometricVertex D,
      Metric.ball x δ ⊆ f ⁻¹' openStar D w)
    (hmesh : complexMesh C < δ) :
    SimplicialVertexMap C D := by
  let φ := approximationVertex f δ hcover
  exact
    { toFun := φ
      maps_face := by
        apply maps_face_of_approximates φ f
        intro v x hx
        apply approximationVertex_spec f δ hcover v
        rw [Metric.mem_ball]
        exact (dist_vertexPoint_le_mesh C hx).trans_lt hmesh }

lemma simplicialApproximationOfCover_approximates
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (f : C.K.space → D.K.space) (δ : ℝ)
    (hcover : ∀ x : C.K.space, ∃ w : GeometricVertex D,
      Metric.ball x δ ⊆ f ⁻¹' openStar D w)
    (hmesh : complexMesh C < δ) :
    (simplicialApproximationOfCover f δ hcover hmesh).Approximates f := by
  intro v x hx
  apply approximationVertex_spec f δ hcover v
  rw [Metric.mem_ball]
  exact (dist_vertexPoint_le_mesh C hx).trans_lt hmesh

lemma exists_starCoverRadius [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (f : C.K.space → D.K.space) (hf : Continuous f) :
    ∃ δ > 0, ∀ x : C.K.space, ∃ w : GeometricVertex D,
      Metric.ball x δ ⊆ f ⁻¹' openStar D w := by
  letI : CompactSpace C.K.space :=
    isCompact_iff_compactSpace.mp (isCompact_space C)
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric
    (s := Set.univ) isCompact_univ
    (c := fun w : GeometricVertex D => f ⁻¹' openStar D w)
    (fun w => (isOpen_openStar D w).preimage hf)
    (by
      intro x _
      obtain ⟨w, hw⟩ := exists_openStar D (f x)
      exact mem_iUnion.mpr ⟨w, hw⟩)
  exact ⟨δ, hδ, fun x => hcover x (Set.mem_univ x)⟩

/-! ### Geometric and abstract barycentric subdivision -/

def abstractFaceToGeometricFace (C : FiniteGeometricComplex E) :
    ComplexFace (abstractComplex C) → GeometricFace C :=
  fun s => ⟨s.1.map (geometricVertexEmbedding C), s.2⟩

def geometricFaceToAbstractFace (C : FiniteGeometricComplex E) :
    GeometricFace C → ComplexFace (abstractComplex C) :=
  fun G => ⟨liftGeometricFace C G, liftGeometricFace_mem C G⟩

lemma lift_map_abstractFace (C : FiniteGeometricComplex E)
    (s : ComplexFace (abstractComplex C)) :
    liftGeometricFace C (abstractFaceToGeometricFace C s) = s.1 := by
  apply Finset.map_injective (geometricVertexEmbedding C)
  rw [map_liftGeometricFace]
  rfl

noncomputable def abstractFaceEquivGeometricFace (C : FiniteGeometricComplex E) :
    ComplexFace (abstractComplex C) ≃ GeometricFace C where
  toFun := abstractFaceToGeometricFace C
  invFun := geometricFaceToAbstractFace C
  left_inv := by
    intro s
    apply Subtype.ext
    exact lift_map_abstractFace C s
  right_inv := by
    intro G
    apply Subtype.ext
    exact map_liftGeometricFace C G

lemma singleton_faceCenter_mem_barycentricComplex
    (C : FiniteGeometricComplex E) (G : GeometricFace C) :
    {faceCenter C G} ∈ (barycentricComplex C).faces := by
  refine ⟨{G}, ?_, ?_⟩
  · refine ⟨Finset.singleton_nonempty G, ?_⟩
    simp
  · ext x
    simp [chainCenters]

def faceCenterVertex (C : FiniteGeometricComplex E) (G : GeometricFace C) :
    GeometricVertex (barycentricSubdivision C) :=
  ⟨faceCenter C G, by
    change faceCenter C G ∈ (barycentricComplex C).vertices
    rw [Geometry.SimplicialComplex.vertices_eq]
    exact mem_iUnion₂_of_mem (singleton_faceCenter_mem_barycentricComplex C G)
      (Finset.mem_singleton_self _)⟩

lemma faceCenterVertex_injective (C : FiniteGeometricComplex E) :
    Function.Injective (faceCenterVertex C) := by
  intro G H h
  apply faceCenter_injective C
  exact congrArg Subtype.val h

lemma faceCenterVertex_surjective (C : FiniteGeometricComplex E) :
    Function.Surjective (faceCenterVertex C) := by
  intro v
  have hv : v.1 ∈ (barycentricComplex C).vertices := v.2
  rw [Geometry.SimplicialComplex.vertices_eq] at hv
  obtain ⟨s, hs⟩ := mem_iUnion.mp hv
  obtain ⟨hsface, hvs⟩ := mem_iUnion.mp hs
  obtain ⟨c, hc, hsc⟩ :=
    (mem_barycentricComplex_faces C s).mp hsface
  rw [hsc] at hvs
  obtain ⟨G, hGc, hGv⟩ := (mem_chainCenters C c v.1).mp hvs
  refine ⟨G, ?_⟩
  apply Subtype.ext
  exact hGv

noncomputable def geometricFaceEquivBarycentricVertex
    (C : FiniteGeometricComplex E) :
    GeometricFace C ≃ GeometricVertex (barycentricSubdivision C) :=
  Equiv.ofBijective (faceCenterVertex C)
    ⟨faceCenterVertex_injective C, faceCenterVertex_surjective C⟩

noncomputable def subdivisionVertexEquiv (C : FiniteGeometricComplex E) :
    ComplexFace (abstractComplex C) ≃
      GeometricVertex (barycentricSubdivision C) :=
  (abstractFaceEquivGeometricFace C).trans
    (geometricFaceEquivBarycentricVertex C)

@[simp]
lemma subdivisionVertexEquiv_val (C : FiniteGeometricComplex E)
    (s : ComplexFace (abstractComplex C)) :
    ((subdivisionVertexEquiv C s :
      GeometricVertex (barycentricSubdivision C)) : E) =
        faceCenter C (abstractFaceToGeometricFace C s) :=
  rfl

lemma isAbstractFaceChain_iff_isFaceChain
    (C : FiniteGeometricComplex E)
    (c : Finset (ComplexFace (abstractComplex C))) :
    IsAbstractFaceChain (abstractComplex C) c ↔
      IsFaceChain C (c.image (abstractFaceEquivGeometricFace C)) := by
  constructor
  · intro hc
    refine ⟨Finset.image_nonempty.mpr hc.1, ?_⟩
    intro F hF G hG
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hG
    rcases hc.2 s hs t ht with hst | hts
    · left
      exact Finset.map_subset_map.mpr hst
    · right
      exact Finset.map_subset_map.mpr hts
  · intro hc
    refine ⟨?_, ?_⟩
    · by_contra h
      have : c = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst c
      simpa using hc.1
    · intro s hs t ht
      have hs' : abstractFaceEquivGeometricFace C s ∈
          c.image (abstractFaceEquivGeometricFace C) := Finset.mem_image.mpr
        ⟨s, hs, rfl⟩
      have ht' : abstractFaceEquivGeometricFace C t ∈
          c.image (abstractFaceEquivGeometricFace C) := Finset.mem_image.mpr
        ⟨t, ht, rfl⟩
      rcases hc.2 _ hs' _ ht' with hst | hts
      · left
        exact Finset.map_subset_map.mp hst
      · right
        exact Finset.map_subset_map.mp hts

lemma map_subdivisionVertices_eq_chainCenters
    (C : FiniteGeometricComplex E)
    (c : Finset (ComplexFace (abstractComplex C))) :
    (c.image (subdivisionVertexEquiv C)).map
        (geometricVertexEmbedding (barycentricSubdivision C)) =
      chainCenters C (c.image (abstractFaceEquivGeometricFace C)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hvx⟩ := Finset.mem_map.mp hx
    obtain ⟨s, hs, hsv⟩ := Finset.mem_image.mp hv
    apply (mem_chainCenters C _ x).mpr
    refine ⟨abstractFaceEquivGeometricFace C s,
      Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    rw [← hvx, ← hsv]
    rfl
  · intro hx
    obtain ⟨G, hG, hGx⟩ := (mem_chainCenters C _ x).mp hx
    obtain ⟨s, hs, hsG⟩ := Finset.mem_image.mp hG
    apply Finset.mem_map.mpr
    refine ⟨subdivisionVertexEquiv C s,
      Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    rw [← hGx, ← hsG]
    rfl

lemma image_subdivisionVertexEquiv_mem_faces_iff
    (C : FiniteGeometricComplex E)
    (c : Finset (ComplexFace (abstractComplex C))) :
    c.image (subdivisionVertexEquiv C) ∈
        (abstractComplex (barycentricSubdivision C)).faces ↔
      c ∈ (barycentricAbstract (abstractComplex C)).faces := by
  rw [mem_abstractComplex_faces, map_subdivisionVertices_eq_chainCenters]
  change chainCenters C (c.image (abstractFaceEquivGeometricFace C)) ∈
      (barycentricComplex C).faces ↔ _
  rw [mem_barycentricComplex_faces]
  constructor
  · rintro ⟨g, hg, hgc⟩
    have hcgeom : IsFaceChain C
        (c.image (abstractFaceEquivGeometricFace C)) := by
      have hinj : Function.Injective (faceCenter C) := faceCenter_injective C
      have heq : g = c.image (abstractFaceEquivGeometricFace C) := by
        apply Finset.image_injective hinj
        simpa [chainCenters] using hgc.symm
      rwa [← heq]
    exact (isAbstractFaceChain_iff_isFaceChain C c).mpr hcgeom
  · intro hc
    refine ⟨c.image (abstractFaceEquivGeometricFace C),
      (isAbstractFaceChain_iff_isFaceChain C c).mp hc, rfl⟩

noncomputable def subdivisionRelabelForwardCarrier
    (C : FiniteGeometricComplex E) :
    FaceCarrier (barycentricAbstract (abstractComplex C))
      (abstractComplex (barycentricSubdivision C)) where
  face := fun c =>
    ⟨c.1.image (subdivisionVertexEquiv C),
      (image_subdivisionVertexEquiv_mem_faces_iff C c.1).mpr c.2⟩
  mono := by
    intro s t hst x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨v, hst hv, rfl⟩

lemma image_equiv_symm_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (s : Finset β) :
    (s.image e.symm).image e = s := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    have hzy : z = y := by
      rw [← hxy, ← hzx, e.apply_symm_apply]
    exact hzy ▸ hz
  · intro hy
    exact Finset.mem_image.mpr
      ⟨e.symm y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

noncomputable def subdivisionRelabelBackwardCarrier
    (C : FiniteGeometricComplex E) :
    FaceCarrier (abstractComplex (barycentricSubdivision C))
      (barycentricAbstract (abstractComplex C)) where
  face := fun s => by
    let c := s.1.image (subdivisionVertexEquiv C).symm
    refine ⟨c, ?_⟩
    apply (image_subdivisionVertexEquiv_mem_faces_iff C c).mp
    have hc : c.image (subdivisionVertexEquiv C) = s.1 := by
      exact image_equiv_symm_image (subdivisionVertexEquiv C) s.1
    rw [hc]
    exact s.2
  mono := by
    intro s t hst x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨v, hst hv, rfl⟩

noncomputable def subdivisionRelabelForwardChainMap
    (C : FiniteGeometricComplex E) :
    AugChainMap (barycentricAbstract (abstractComplex C))
      (abstractComplex (barycentricSubdivision C)) :=
  carriedAugChainMap (subdivisionRelabelForwardCarrier C)

noncomputable def subdivisionRelabelBackwardChainMap
    (C : FiniteGeometricComplex E) :
    AugChainMap (abstractComplex (barycentricSubdivision C))
      (barycentricAbstract (abstractComplex C)) :=
  carriedAugChainMap (subdivisionRelabelBackwardCarrier C)

/-! ### Chain-homotopy utilities -/

lemma augChainMap_ext
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {f g : AugChainMap K L} (h : ∀ n, f.map n = g.map n) : f = g := by
  cases f with
  | mk fmap fmap_boundary fmap_empty =>
      cases g with
      | mk gmap gmap_boundary gmap_empty =>
          have hmap : fmap = gmap := funext h
          subst gmap
          rfl

lemma augChainMap_comp_assoc
    {V W U T : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W] [Fintype U] [LinearOrder U]
    [Fintype T] [LinearOrder T]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {M : PreAbstractSimplicialComplex U}
    {N : PreAbstractSimplicialComplex T}
    (h : AugChainMap M N) (g : AugChainMap L M) (f : AugChainMap K L) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply augChainMap_ext
  intro n
  apply LinearMap.ext
  intro x
  rfl

lemma augChainMap_id_comp
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    (f : AugChainMap K L) : (AugChainMap.id L).comp f = f := by
  apply augChainMap_ext
  intro n
  apply LinearMap.ext
  intro x
  rfl

lemma augChainMap_comp_id
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    (f : AugChainMap K L) : f.comp (AugChainMap.id K) = f := by
  apply augChainMap_ext
  intro n
  apply LinearMap.ext
  intro x
  rfl

def faceCarrierComp
    {V W U : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W] [Fintype U] [LinearOrder U]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {M : PreAbstractSimplicialComplex U}
    (B : FaceCarrier L M) (A : FaceCarrier K L) : FaceCarrier K M where
  face := fun s => B.face (A.face s)
  mono := fun hst => B.mono (A.mono hst)

lemma carriedBy_comp
    {V W U : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W] [Fintype U] [LinearOrder U]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {M : PreAbstractSimplicialComplex U}
    {A : FaceCarrier K L} {B : FaceCarrier L M}
    {f : AugChainMap K L} {g : AugChainMap L M}
    (hf : CarriedBy A f) (hg : CarriedBy B g) :
    CarriedBy (faceCarrierComp B A) (g.comp f) := by
  intro n s
  change SupportedIn (B.face (A.face (nonemptyFaceOfAug s))).1
    (g.map (n + 1) (f.map (n + 1) (Finsupp.single s 1)))
  exact carriedBy_map_supported hg (hf n s)

lemma carriedBy_monoCarrier
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {A B : FaceCarrier K L} {f : AugChainMap K L}
    (hAB : ∀ s, (A.face s).1 ⊆ (B.face s).1)
    (hf : CarriedBy A f) : CarriedBy B f := by
  intro n s
  exact supportedIn_mono (hAB _) (hf n s)

noncomputable def augChainHomotopyTrans
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {f g h : AugChainMap K L}
    (H : AugChainHomotopy f g) (G : AugChainHomotopy g h) :
    AugChainHomotopy f h where
  hom := fun n => H.hom n + G.hom n
  hom_zero := by
    intro x
    rw [LinearMap.add_apply, map_add, H.hom_zero, G.hom_zero]
    module
  hom_succ := by
    intro n x
    rw [LinearMap.add_apply, map_add, LinearMap.add_apply]
    calc
      boundary L (n + 1) (H.hom (n + 1) x) +
            boundary L (n + 1) (G.hom (n + 1) x) +
          (H.hom n (boundary K n x) + G.hom n (boundary K n x)) =
          (boundary L (n + 1) (H.hom (n + 1) x) +
            H.hom n (boundary K n x)) +
          (boundary L (n + 1) (G.hom (n + 1) x) +
            G.hom n (boundary K n x)) := by module
      _ = (f.map (n + 1) x - g.map (n + 1) x) +
          (g.map (n + 1) x - h.map (n + 1) x) := by
        rw [H.hom_succ, G.hom_succ]
      _ = f.map (n + 1) x - h.map (n + 1) x := by module

noncomputable def augChainHomotopyCongr
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {f g f' g' : AugChainMap K L}
    (H : AugChainHomotopy f g) (hf : f' = f) (hg : g' = g) :
    AugChainHomotopy f' g' := by
  subst f'
  subst g'
  exact H

noncomputable def augChainHomotopyPostcomp
    {V W U : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W] [Fintype U] [LinearOrder U]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {M : PreAbstractSimplicialComplex U}
    {f g : AugChainMap K L} (H : AugChainHomotopy f g)
    (k : AugChainMap L M) :
    AugChainHomotopy (k.comp f) (k.comp g) where
  hom := fun n => (k.map (n + 1)).comp (H.hom n)
  hom_zero := by
    intro x
    rw [LinearMap.comp_apply, k.map_boundary, H.hom_zero, map_sub]
    rfl
  hom_succ := by
    intro n x
    rw [LinearMap.comp_apply, k.map_boundary, LinearMap.comp_apply,
      ← map_add, H.hom_succ, map_sub]
    rfl

noncomputable def augChainHomotopyPrecomp
    {V W U : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W] [Fintype U] [LinearOrder U]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {M : PreAbstractSimplicialComplex U}
    {f g : AugChainMap L M} (H : AugChainHomotopy f g)
    (k : AugChainMap K L) :
    AugChainHomotopy (f.comp k) (g.comp k) where
  hom := fun n => (H.hom n).comp (k.map n)
  hom_zero := by
    intro x
    rw [LinearMap.comp_apply, H.hom_zero]
    rfl
  hom_succ := by
    intro n x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    change boundary M (n + 1) (H.hom (n + 1) (k.map (n + 1) x)) +
        H.hom n (k.map n (boundary K n x)) =
      f.map (n + 1) (k.map (n + 1) x) -
        g.map (n + 1) (k.map (n + 1) x)
    rw [← k.map_boundary]
    exact H.hom_succ n (k.map (n + 1) x)

lemma image_equiv_image_symm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (s : Finset α) :
    (s.image e).image e.symm = s := by
  simpa using image_equiv_symm_image e.symm s

lemma subdivisionRelabel_inv_hom_carried
    (C : FiniteGeometricComplex E) :
    CarriedBy (identityFaceCarrier (barycentricAbstract (abstractComplex C)))
      ((subdivisionRelabelBackwardChainMap C).comp
        (subdivisionRelabelForwardChainMap C)) := by
  apply carriedBy_monoCarrier
    (A := faceCarrierComp (subdivisionRelabelBackwardCarrier C)
      (subdivisionRelabelForwardCarrier C))
  · intro s
    change ((s.1.image (subdivisionVertexEquiv C)).image
      (subdivisionVertexEquiv C).symm) ⊆ s.1
    rw [image_equiv_image_symm]
  · exact carriedBy_comp
      (carriedAugChainMap_carriedBy (subdivisionRelabelForwardCarrier C))
      (carriedAugChainMap_carriedBy (subdivisionRelabelBackwardCarrier C))

lemma subdivisionRelabel_hom_inv_carried
    (C : FiniteGeometricComplex E) :
    CarriedBy (identityFaceCarrier
      (abstractComplex (barycentricSubdivision C)))
      ((subdivisionRelabelForwardChainMap C).comp
        (subdivisionRelabelBackwardChainMap C)) := by
  apply carriedBy_monoCarrier
    (A := faceCarrierComp (subdivisionRelabelForwardCarrier C)
      (subdivisionRelabelBackwardCarrier C))
  · intro s
    change ((s.1.image (subdivisionVertexEquiv C).symm).image
      (subdivisionVertexEquiv C)) ⊆ s.1
    rw [image_equiv_symm_image]
  · exact carriedBy_comp
      (carriedAugChainMap_carriedBy (subdivisionRelabelBackwardCarrier C))
      (carriedAugChainMap_carriedBy (subdivisionRelabelForwardCarrier C))

noncomputable def subdivisionRelabelChainHomotopyEquiv
    (C : FiniteGeometricComplex E) :
    AugChainHomotopyEquiv (barycentricAbstract (abstractComplex C))
      (abstractComplex (barycentricSubdivision C)) where
  hom := subdivisionRelabelForwardChainMap C
  inv := subdivisionRelabelBackwardChainMap C
  inv_hom := carrierHomotopy
    (identityFaceCarrier (barycentricAbstract (abstractComplex C))) _ _
    (subdivisionRelabel_inv_hom_carried C)
    (identityAugChainMap_carriedBy (barycentricAbstract (abstractComplex C)))
  hom_inv := carrierHomotopy
    (identityFaceCarrier (abstractComplex (barycentricSubdivision C))) _ _
    (subdivisionRelabel_hom_inv_carried C)
    (identityAugChainMap_carriedBy
      (abstractComplex (barycentricSubdivision C)))

noncomputable def augChainHomotopyRefl
    {V W : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    (f : AugChainMap K L) : AugChainHomotopy f f where
  hom := fun _ => 0
  hom_zero := by simp
  hom_succ := by simp

noncomputable def augChainHomotopyEquivTrans
    {V W U : Type*} [Fintype V] [LinearOrder V]
    [Fintype W] [LinearOrder W] [Fintype U] [LinearOrder U]
    {K : PreAbstractSimplicialComplex V}
    {L : PreAbstractSimplicialComplex W}
    {M : PreAbstractSimplicialComplex U}
    (e : AugChainHomotopyEquiv K L) (f : AugChainHomotopyEquiv L M) :
    AugChainHomotopyEquiv K M where
  hom := f.hom.comp e.hom
  inv := e.inv.comp f.inv
  inv_hom := by
    let H := augChainHomotopyPostcomp
      (augChainHomotopyPrecomp f.inv_hom e.hom) e.inv
    have H' : AugChainHomotopy
        ((e.inv.comp f.inv).comp (f.hom.comp e.hom))
        (e.inv.comp e.hom) := augChainHomotopyCongr H (by
          apply augChainMap_ext
          intro n
          apply LinearMap.ext
          intro x
          rfl) (by
          apply augChainMap_ext
          intro n
          apply LinearMap.ext
          intro x
          rfl)
    exact augChainHomotopyTrans H' e.inv_hom
  hom_inv := by
    let H := augChainHomotopyPostcomp
      (augChainHomotopyPrecomp e.hom_inv f.inv) f.hom
    have H' : AugChainHomotopy
        ((f.hom.comp e.hom).comp (e.inv.comp f.inv))
        (f.hom.comp f.inv) := augChainHomotopyCongr H (by
          apply augChainMap_ext
          intro n
          apply LinearMap.ext
          intro x
          rfl) (by
          apply augChainMap_ext
          intro n
          apply LinearMap.ext
          intro x
          rfl)
    exact augChainHomotopyTrans H' f.hom_inv

noncomputable def geometricSubdivisionChainHomotopyEquiv
    (C : FiniteGeometricComplex E) :
    AugChainHomotopyEquiv (abstractComplex C)
      (abstractComplex (barycentricSubdivision C)) :=
  augChainHomotopyEquivTrans
    (subdivisionChainHomotopyEquiv (abstractComplex C))
    (subdivisionRelabelChainHomotopyEquiv C)

noncomputable def identityChainHomotopyEquiv
    {V : Type*} [Fintype V] [LinearOrder V]
    (K : PreAbstractSimplicialComplex V) : AugChainHomotopyEquiv K K where
  hom := AugChainMap.id K
  inv := AugChainMap.id K
  inv_hom := augChainHomotopyCongr
    (augChainHomotopyRefl (AugChainMap.id K))
    (augChainMap_id_comp (AugChainMap.id K)) rfl
  hom_inv := augChainHomotopyCongr
    (augChainHomotopyRefl (AugChainMap.id K))
    (augChainMap_id_comp (AugChainMap.id K)) rfl

noncomputable def iteratedSubdivisionChainHomotopyEquiv
    (C : FiniteGeometricComplex E) :
    (n : ℕ) → AugChainHomotopyEquiv (abstractComplex C)
      (abstractComplex (iteratedSubdivision C n))
  | 0 => identityChainHomotopyEquiv (abstractComplex C)
  | n + 1 =>
      augChainHomotopyEquivTrans
        (iteratedSubdivisionChainHomotopyEquiv C n)
        (geometricSubdivisionChainHomotopyEquiv (iteratedSubdivision C n))

/-! ### Functoriality and contiguity -/

def SimplicialVertexMap.comp
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {A : FiniteGeometricComplex G}
    (ψ : SimplicialVertexMap D A) (φ : SimplicialVertexMap C D) :
    SimplicialVertexMap C A where
  toFun := fun v => ψ (φ v)
  maps_face := by
    intro s hs
    have hφ := φ.maps_face hs
    have hψ := ψ.maps_face hφ
    simpa [Finset.image_image, Function.comp_def] using hψ

lemma simplicialVertexMap_comp_chain_carried
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {A : FiniteGeometricComplex G}
    (ψ : SimplicialVertexMap D A) (φ : SimplicialVertexMap C D) :
    CarriedBy (ψ.comp φ).faceCarrier (ψ.chainMap.comp φ.chainMap) := by
  apply carriedBy_monoCarrier
    (A := faceCarrierComp ψ.faceCarrier φ.faceCarrier)
  · intro s x hx
    obtain ⟨w, hw, hwx⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
    apply Finset.mem_image.mpr
    refine ⟨v, hv, ?_⟩
    rw [← hwx, ← hvw]
    rfl
  · exact carriedBy_comp (carriedAugChainMap_carriedBy φ.faceCarrier)
      (carriedAugChainMap_carriedBy ψ.faceCarrier)

noncomputable def simplicialVertexMap_comp_chainHomotopy
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {A : FiniteGeometricComplex G}
    (ψ : SimplicialVertexMap D A) (φ : SimplicialVertexMap C D) :
    AugChainHomotopy (ψ.chainMap.comp φ.chainMap) (ψ.comp φ).chainMap :=
  carrierHomotopy (ψ.comp φ).faceCarrier _ _
    (simplicialVertexMap_comp_chain_carried ψ φ)
    (carriedAugChainMap_carriedBy (ψ.comp φ).faceCarrier)

noncomputable def approximationUnionCarrier
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (φ ψ : SimplicialVertexMap C D) (f : C.K.space → D.K.space)
    (hφ : φ.Approximates f) (hψ : ψ.Approximates f) :
    FaceCarrier (abstractComplex C) (abstractComplex D) where
  face := fun s => by
    let G : GeometricFace C :=
      ⟨s.1.map (geometricVertexEmbedding C), s.2⟩
    let x : C.K.space :=
      ⟨faceCenter C G, C.K.convexHull_subset_space G.2 (faceCenter_mem C G)⟩
    refine ⟨s.1.image φ ∪ s.1.image ψ, ?_⟩
    have hsne : s.1.Nonempty :=
      ((abstractComplex C).isRelLowerSet_faces s.2).1
    apply face_of_common_openStar D
      ((Finset.image_nonempty.mpr hsne).mono Finset.subset_union_left)
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      apply hφ v
      apply faceCenterPoint_mem_openStar C G
      exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      apply hψ v
      apply faceCenterPoint_mem_openStar C G
      exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
  mono := by
    intro s t hst x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · apply Finset.mem_union_left
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨v, hst hv, rfl⟩
    · apply Finset.mem_union_right
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨v, hst hv, rfl⟩

lemma first_approximation_carriedBy_union
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (φ ψ : SimplicialVertexMap C D) (f : C.K.space → D.K.space)
    (hφ : φ.Approximates f) (hψ : ψ.Approximates f) :
    CarriedBy (approximationUnionCarrier φ ψ f hφ hψ) φ.chainMap := by
  apply carriedBy_monoCarrier (A := φ.faceCarrier)
  · intro s
    exact Finset.subset_union_left
  · exact carriedAugChainMap_carriedBy φ.faceCarrier

lemma second_approximation_carriedBy_union
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (φ ψ : SimplicialVertexMap C D) (f : C.K.space → D.K.space)
    (hφ : φ.Approximates f) (hψ : ψ.Approximates f) :
    CarriedBy (approximationUnionCarrier φ ψ f hφ hψ) ψ.chainMap := by
  apply carriedBy_monoCarrier (A := ψ.faceCarrier)
  · intro s
    exact Finset.subset_union_right
  · exact carriedAugChainMap_carriedBy ψ.faceCarrier

noncomputable def approximations_chainHomotopy
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (φ ψ : SimplicialVertexMap C D) (f : C.K.space → D.K.space)
    (hφ : φ.Approximates f) (hψ : ψ.Approximates f) :
    AugChainHomotopy φ.chainMap ψ.chainMap :=
  carrierHomotopy (approximationUnionCarrier φ ψ f hφ hψ) _ _
    (first_approximation_carriedBy_union φ ψ f hφ hψ)
    (second_approximation_carriedBy_union φ ψ f hφ hψ)

/-! ### Simplicial approximation of a homotopy -/

def intervalLeft (q : ℕ) (i : Fin (q + 1)) : I :=
  ⟨(i : ℝ) / (q + 1 : ℝ), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < q + 1)).mpr
      exact_mod_cast Nat.le_of_lt i.isLt⟩

def intervalRight (q : ℕ) (i : Fin (q + 1)) : I :=
  ⟨(i + 1 : ℕ) / (q + 1 : ℝ), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < q + 1)).mpr
      exact_mod_cast i.isLt⟩

lemma intervalRight_sub_intervalLeft (q : ℕ) (i : Fin (q + 1)) :
    ((intervalRight q i : I) : ℝ) - ((intervalLeft q i : I) : ℝ) =
      1 / (q + 1 : ℝ) := by
  dsimp [intervalRight, intervalLeft]
  have hne : (q + 1 : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

lemma intervalLeft_zero (q : ℕ) :
    intervalLeft q (0 : Fin (q + 1)) = 0 := by
  apply Subtype.ext
  simp [intervalLeft]

lemma intervalRight_last (q : ℕ) :
    intervalRight q (Fin.last q) = 1 := by
  apply Subtype.ext
  have hne : (q + 1 : ℝ) ≠ 0 := by positivity
  simp [intervalRight, hne]

lemma intervalRight_eq_nextLeft (q k : ℕ) (hk : k < q) :
    intervalRight q ⟨k, hk.trans (Nat.lt_succ_self q)⟩ =
      intervalLeft q ⟨k + 1, Nat.succ_lt_succ hk⟩ := by
  apply Subtype.ext
  rfl

lemma exists_homotopyStarCoverRadius
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {f g : C(C.K.space, D.K.space)} (H : ContinuousMap.Homotopy f g) :
    ∃ δ > 0, ∀ z : I × C.K.space, ∃ w : GeometricVertex D,
      Metric.ball z δ ⊆ H ⁻¹' openStar D w := by
  letI : CompactSpace C.K.space :=
    isCompact_iff_compactSpace.mp (isCompact_space C)
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric
    (s := Set.univ) isCompact_univ
    (c := fun w : GeometricVertex D => H ⁻¹' openStar D w)
    (fun w => (isOpen_openStar D w).preimage H.continuous)
    (by
      intro z _
      obtain ⟨w, hw⟩ := exists_openStar D (H z)
      exact mem_iUnion.mpr ⟨w, hw⟩)
  exact ⟨δ, hδ, fun z => hcover z (Set.mem_univ z)⟩

noncomputable def homotopyIntervalVertex
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {f g : C(C.K.space, D.K.space)} (H : ContinuousMap.Homotopy f g)
    (δ : ℝ)
    (hcover : ∀ z : I × C.K.space, ∃ w : GeometricVertex D,
      Metric.ball z δ ⊆ H ⁻¹' openStar D w)
    (q : ℕ) (i : Fin (q + 1)) (v : GeometricVertex C) :
    GeometricVertex D :=
  Classical.choose (hcover (intervalLeft q i, vertexPoint C v))

lemma homotopyIntervalVertex_spec
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {f g : C(C.K.space, D.K.space)} (H : ContinuousMap.Homotopy f g)
    (δ : ℝ)
    (hcover : ∀ z : I × C.K.space, ∃ w : GeometricVertex D,
      Metric.ball z δ ⊆ H ⁻¹' openStar D w)
    (q : ℕ) (i : Fin (q + 1))
    (hstep : 1 / (q + 1 : ℝ) < δ)
    (hmesh : complexMesh C < δ)
    (v : GeometricVertex C) (t : I)
    (htl : intervalLeft q i ≤ t) (htr : t ≤ intervalRight q i)
    {x : C.K.space} (hx : x ∈ openStar C v) :
    H (t, x) ∈ openStar D (homotopyIntervalVertex H δ hcover q i v) := by
  apply Classical.choose_spec
    (hcover (intervalLeft q i, vertexPoint C v))
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  constructor
  · change dist (t : ℝ) (intervalLeft q i : ℝ) < δ
    have htl' : (intervalLeft q i : ℝ) ≤ (t : ℝ) := htl
    have htr' : (t : ℝ) ≤ (intervalRight q i : ℝ) := htr
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htl')]
    calc
      (t : ℝ) - (intervalLeft q i : ℝ) ≤
          (intervalRight q i : ℝ) - (intervalLeft q i : ℝ) :=
        sub_le_sub_right htr' _
      _ = 1 / (q + 1 : ℝ) := intervalRight_sub_intervalLeft q i
      _ < δ := hstep
  · exact (dist_vertexPoint_le_mesh C hx).trans_lt hmesh

lemma intervalLeft_le_intervalRight (q : ℕ) (i : Fin (q + 1)) :
    intervalLeft q i ≤ intervalRight q i := by
  change (intervalLeft q i : ℝ) ≤ (intervalRight q i : ℝ)
  apply sub_nonneg.mp
  rw [intervalRight_sub_intervalLeft]
  positivity

noncomputable def homotopyIntervalMap
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {f g : C(C.K.space, D.K.space)} (H : ContinuousMap.Homotopy f g)
    (δ : ℝ)
    (hcover : ∀ z : I × C.K.space, ∃ w : GeometricVertex D,
      Metric.ball z δ ⊆ H ⁻¹' openStar D w)
    (q : ℕ) (i : Fin (q + 1))
    (hstep : 1 / (q + 1 : ℝ) < δ)
    (hmesh : complexMesh C < δ) : SimplicialVertexMap C D where
  toFun := homotopyIntervalVertex H δ hcover q i
  maps_face := by
    apply maps_face_of_approximates
      (homotopyIntervalVertex H δ hcover q i)
      (fun x => H (intervalLeft q i, x))
    intro v x hx
    exact homotopyIntervalVertex_spec H δ hcover q i hstep hmesh v
      (intervalLeft q i) le_rfl (intervalLeft_le_intervalRight q i) hx

lemma homotopyIntervalMap_approximates
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {f g : C(C.K.space, D.K.space)} (H : ContinuousMap.Homotopy f g)
    (δ : ℝ)
    (hcover : ∀ z : I × C.K.space, ∃ w : GeometricVertex D,
      Metric.ball z δ ⊆ H ⁻¹' openStar D w)
    (q : ℕ) (i : Fin (q + 1))
    (hstep : 1 / (q + 1 : ℝ) < δ)
    (hmesh : complexMesh C < δ) (t : I)
    (htl : intervalLeft q i ≤ t) (htr : t ≤ intervalRight q i) :
    (homotopyIntervalMap H δ hcover q i hstep hmesh).Approximates
      (fun x => H (t, x)) := by
  intro v x hx
  exact homotopyIntervalVertex_spec H δ hcover q i hstep hmesh v t htl htr hx

noncomputable def adjacentIntervalMaps_chainHomotopy
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {f g : C(C.K.space, D.K.space)} (H : ContinuousMap.Homotopy f g)
    (δ : ℝ)
    (hcover : ∀ z : I × C.K.space, ∃ w : GeometricVertex D,
      Metric.ball z δ ⊆ H ⁻¹' openStar D w)
    (q k : ℕ) (hk : k < q)
    (hstep : 1 / (q + 1 : ℝ) < δ)
    (hmesh : complexMesh C < δ) :
    AugChainHomotopy
      (homotopyIntervalMap H δ hcover q
        ⟨k, hk.trans (Nat.lt_succ_self q)⟩ hstep hmesh).chainMap
      (homotopyIntervalMap H δ hcover q
        ⟨k + 1, Nat.succ_lt_succ hk⟩ hstep hmesh).chainMap := by
  let i : Fin (q + 1) := ⟨k, hk.trans (Nat.lt_succ_self q)⟩
  let j : Fin (q + 1) := ⟨k + 1, Nat.succ_lt_succ hk⟩
  let t := intervalRight q i
  have hij : intervalLeft q j = t := by
    exact (intervalRight_eq_nextLeft q k hk).symm
  have hi : (homotopyIntervalMap H δ hcover q i hstep hmesh).Approximates
      (fun x => H (t, x)) :=
    homotopyIntervalMap_approximates H δ hcover q i hstep hmesh t
      (intervalLeft_le_intervalRight q i) le_rfl
  have hj : (homotopyIntervalMap H δ hcover q j hstep hmesh).Approximates
      (fun x => H (t, x)) := by
    apply homotopyIntervalMap_approximates H δ hcover q j hstep hmesh t
    · rw [hij]
    · rw [← hij]
      exact intervalLeft_le_intervalRight q j
  exact approximations_chainHomotopy _ _ (fun x => H (t, x)) hi hj

lemma nonempty_intervalMaps_chainHomotopy_to
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {f g : C(C.K.space, D.K.space)} (H : ContinuousMap.Homotopy f g)
    (δ : ℝ)
    (hcover : ∀ z : I × C.K.space, ∃ w : GeometricVertex D,
      Metric.ball z δ ⊆ H ⁻¹' openStar D w)
    (q : ℕ) (hstep : 1 / (q + 1 : ℝ) < δ)
    (hmesh : complexMesh C < δ) :
    ∀ (k : ℕ) (hk : k < q + 1), Nonempty
      (AugChainHomotopy
        (homotopyIntervalMap H δ hcover q (0 : Fin (q + 1))
          hstep hmesh).chainMap
        (homotopyIntervalMap H δ hcover q ⟨k, hk⟩ hstep hmesh).chainMap) := by
  intro k
  induction k with
  | zero =>
      intro hk
      have hi : (⟨0, hk⟩ : Fin (q + 1)) = 0 := Fin.ext rfl
      rw [hi]
      exact ⟨augChainHomotopyRefl _⟩
  | succ k ih =>
      intro hk
      have hkq : k < q := by omega
      have hk' : k < q + 1 := by omega
      obtain ⟨Hprev⟩ := ih hk'
      let Hnext := adjacentIntervalMaps_chainHomotopy H δ hcover q k hkq
        hstep hmesh
      exact ⟨augChainHomotopyTrans Hprev Hnext⟩

lemma exists_endpointApproximations_chainHomotopy
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {f g : C(C.K.space, D.K.space)} (H : ContinuousMap.Homotopy f g)
    (δ : ℝ) (hδ : 0 < δ)
    (hcover : ∀ z : I × C.K.space, ∃ w : GeometricVertex D,
      Metric.ball z δ ⊆ H ⁻¹' openStar D w)
    (hmesh : complexMesh C < δ) :
    ∃ φ ψ : SimplicialVertexMap C D,
      φ.Approximates f ∧ ψ.Approximates g ∧
        Nonempty (AugChainHomotopy φ.chainMap ψ.chainMap) := by
  obtain ⟨q, hstep⟩ := exists_nat_one_div_lt hδ
  let φ := homotopyIntervalMap H δ hcover q (0 : Fin (q + 1)) hstep hmesh
  let ψ := homotopyIntervalMap H δ hcover q (Fin.last q) hstep hmesh
  have hφraw : φ.Approximates (fun x => H (0, x)) := by
    apply homotopyIntervalMap_approximates H δ hcover q
      (0 : Fin (q + 1)) hstep hmesh 0
    · rw [intervalLeft_zero]
    · rw [← intervalLeft_zero q]
      exact intervalLeft_le_intervalRight q 0
  have hφ : φ.Approximates f := by
    intro v x hx
    rw [← H.map_zero_left x]
    exact hφraw v hx
  have hψraw : ψ.Approximates (fun x => H (1, x)) := by
    apply homotopyIntervalMap_approximates H δ hcover q
      (Fin.last q) hstep hmesh 1
    · rw [← intervalRight_last q]
      exact intervalLeft_le_intervalRight q (Fin.last q)
    · rw [intervalRight_last]
  have hψ : ψ.Approximates g := by
    intro v x hx
    rw [← H.map_one_left x]
    exact hψraw v hx
  obtain ⟨Hchain⟩ := nonempty_intervalMaps_chainHomotopy_to
    H δ hcover q hstep hmesh q (Nat.lt_succ_self q)
  have hi : (⟨q, Nat.lt_succ_self q⟩ : Fin (q + 1)) = Fin.last q := Fin.ext rfl
  rw [hi] at Hchain
  exact ⟨φ, ψ, hφ, hψ, ⟨Hchain⟩⟩

/-! ### Transport to an iterated subdivision -/

def subdivisionToOriginalSpace (C : FiniteGeometricComplex E) (n : ℕ) :
    (iteratedSubdivision C n).K.space → C.K.space :=
  fun x => ⟨x.1, by
    rw [← iteratedSubdivision_space C n]
    exact x.2⟩

def originalToSubdivisionSpace (C : FiniteGeometricComplex E) (n : ℕ) :
    C.K.space → (iteratedSubdivision C n).K.space :=
  fun x => ⟨x.1, by
    rw [iteratedSubdivision_space C n]
    exact x.2⟩

lemma continuous_subdivisionToOriginalSpace
    (C : FiniteGeometricComplex E) (n : ℕ) :
    Continuous (subdivisionToOriginalSpace C n) :=
  Continuous.subtype_mk continuous_subtype_val _

lemma continuous_originalToSubdivisionSpace
    (C : FiniteGeometricComplex E) (n : ℕ) :
    Continuous (originalToSubdivisionSpace C n) :=
  Continuous.subtype_mk continuous_subtype_val _

def subdivisionToOriginalContinuousMap
    (C : FiniteGeometricComplex E) (n : ℕ) :
    C((iteratedSubdivision C n).K.space, C.K.space) :=
  ⟨subdivisionToOriginalSpace C n, continuous_subdivisionToOriginalSpace C n⟩

noncomputable def subdivisionSpaceHomeomorph
    (C : FiniteGeometricComplex E) (n : ℕ) :
    (iteratedSubdivision C n).K.space ≃ₜ C.K.space where
  toFun := subdivisionToOriginalSpace C n
  invFun := originalToSubdivisionSpace C n
  left_inv := fun _x => Subtype.ext rfl
  right_inv := fun _x => Subtype.ext rfl
  continuous_toFun := continuous_subdivisionToOriginalSpace C n
  continuous_invFun := continuous_originalToSubdivisionSpace C n

lemma dist_subdivisionToOriginalSpace
    (C : FiniteGeometricComplex E) (n : ℕ)
    (x y : (iteratedSubdivision C n).K.space) :
    dist (subdivisionToOriginalSpace C n x)
      (subdivisionToOriginalSpace C n y) = dist x y :=
  rfl

lemma exists_subdivisionApproximation
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    (f : C.K.space → D.K.space) (hf : Continuous f) :
    ∃ n : ℕ, ∃ φ : SimplicialVertexMap (iteratedSubdivision C n) D,
      φ.Approximates (fun x => f (subdivisionToOriginalSpace C n x)) := by
  obtain ⟨δ, hδ, hcover⟩ := exists_starCoverRadius f hf
  obtain ⟨n, hmesh⟩ := exists_iteratedSubdivision_mesh_lt C hδ
  let Cn := iteratedSubdivision C n
  let fn : Cn.K.space → D.K.space :=
    fun x => f (subdivisionToOriginalSpace C n x)
  have hcoverN : ∀ x : Cn.K.space, ∃ w : GeometricVertex D,
      Metric.ball x δ ⊆ fn ⁻¹' openStar D w := by
    intro x
    obtain ⟨w, hw⟩ := hcover (subdivisionToOriginalSpace C n x)
    refine ⟨w, ?_⟩
    intro y hy
    apply hw
    rw [Metric.mem_ball, dist_subdivisionToOriginalSpace]
    exact hy
  let φ := simplicialApproximationOfCover fn δ hcoverN hmesh
  exact ⟨n, φ, simplicialApproximationOfCover_approximates
    fn δ hcoverN hmesh⟩

noncomputable def homotopyOnSubdivision
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {f g : C(C.K.space, D.K.space)} (H : ContinuousMap.Homotopy f g)
    (n : ℕ) : ContinuousMap.Homotopy
      (f.comp (subdivisionToOriginalContinuousMap C n))
      (g.comp (subdivisionToOriginalContinuousMap C n)) where
  toFun := fun z => H (z.1, subdivisionToOriginalSpace C n z.2)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk
      ((continuous_subdivisionToOriginalSpace C n).comp continuous_snd))
  map_zero_left := by
    intro x
    exact H.map_zero_left (subdivisionToOriginalSpace C n x)
  map_one_left := by
    intro x
    exact H.map_one_left (subdivisionToOriginalSpace C n x)

lemma exists_subdivisionEndpointApproximations_chainHomotopy
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : FiniteGeometricComplex E} {D : FiniteGeometricComplex F}
    {f g : C(C.K.space, D.K.space)} (H : ContinuousMap.Homotopy f g) :
    ∃ n : ℕ, ∃ φ ψ : SimplicialVertexMap (iteratedSubdivision C n) D,
      φ.Approximates
          (fun x => f (subdivisionToOriginalSpace C n x)) ∧
        ψ.Approximates
          (fun x => g (subdivisionToOriginalSpace C n x)) ∧
        Nonempty (AugChainHomotopy φ.chainMap ψ.chainMap) := by
  obtain ⟨δ, hδ, hcover⟩ := exists_homotopyStarCoverRadius H
  obtain ⟨n, hmesh⟩ := exists_iteratedSubdivision_mesh_lt C hδ
  let Cn := iteratedSubdivision C n
  let Hn := homotopyOnSubdivision H n
  have hcoverN : ∀ z : I × Cn.K.space, ∃ w : GeometricVertex D,
      Metric.ball z δ ⊆ Hn ⁻¹' openStar D w := by
    intro z
    obtain ⟨w, hw⟩ := hcover (z.1, subdivisionToOriginalSpace C n z.2)
    refine ⟨w, ?_⟩
    intro y hy
    apply hw
    rw [Metric.mem_ball, Prod.dist_eq] at hy
    rw [Metric.mem_ball, Prod.dist_eq]
    change max (dist y.1 z.1)
      (dist (subdivisionToOriginalSpace C n y.2)
        (subdivisionToOriginalSpace C n z.2)) < δ
    rw [dist_subdivisionToOriginalSpace]
    exact hy
  obtain ⟨φ, ψ, hφ, hψ, hchain⟩ :=
    exists_endpointApproximations_chainHomotopy Hn δ hδ hcoverN hmesh
  exact ⟨n, φ, ψ, hφ, hψ, hchain⟩

/-! ### The geometric projection carrier -/

noncomputable def geometricProjectionCarrier
    (C : FiniteGeometricComplex E) :
    FaceCarrier (abstractComplex (barycentricSubdivision C))
      (abstractComplex C) :=
  faceCarrierComp (barycentricProjectionCarrier (abstractComplex C))
    (subdivisionRelabelBackwardCarrier C)

lemma geometricSubdivision_inv_carried
    (C : FiniteGeometricComplex E) :
    CarriedBy (geometricProjectionCarrier C)
      (geometricSubdivisionChainHomotopyEquiv C).inv := by
  exact carriedBy_comp
    (carriedAugChainMap_carriedBy (subdivisionRelabelBackwardCarrier C))
    (carriedAugChainMap_carriedBy
      (barycentricProjectionCarrier (abstractComplex C)))

lemma geometricProjectionCarrier_vertex_mem_convexHull
    (C : FiniteGeometricComplex E)
    (s : ComplexFace (abstractComplex (barycentricSubdivision C)))
    {v : GeometricVertex (barycentricSubdivision C)} (hv : v ∈ s.1) :
    (v : E) ∈ convexHull ℝ
      (((geometricProjectionCarrier C).face s).1.map
        (geometricVertexEmbedding C) : Set E) := by
  let c := (subdivisionRelabelBackwardCarrier C).face s
  let a : ComplexFace (abstractComplex C) :=
    (subdivisionVertexEquiv C).symm v
  have ha : a ∈ c.1 := by
    change (subdivisionVertexEquiv C).symm v ∈
      s.1.image (subdivisionVertexEquiv C).symm
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hatop : a.1 ⊆ ((barycentricProjectionCarrier
      (abstractComplex C)).face c).1 :=
    le_abstractChainTop c.1 c.2 a ha
  have hcenter : faceCenter C (abstractFaceToGeometricFace C a) ∈
      convexHull ℝ
        ((abstractFaceToGeometricFace C a).1 : Set E) :=
    faceCenter_mem C (abstractFaceToGeometricFace C a)
  have hmono : (abstractFaceToGeometricFace C a).1 ⊆
      ((abstractFaceToGeometricFace C
        ((barycentricProjectionCarrier (abstractComplex C)).face c)).1) :=
    Finset.map_subset_map.mpr hatop
  have hvcenter : (v : E) =
      faceCenter C (abstractFaceToGeometricFace C a) := by
    change (v : E) = ((subdivisionVertexEquiv C a :
      GeometricVertex (barycentricSubdivision C)) : E)
    rw [Equiv.apply_symm_apply]
  rw [hvcenter]
  exact convexHull_mono hmono hcenter

noncomputable def iteratedProjectionCarrier (C : FiniteGeometricComplex E) :
    (n : ℕ) → FaceCarrier (abstractComplex (iteratedSubdivision C n))
      (abstractComplex C)
  | 0 => identityFaceCarrier (abstractComplex C)
  | n + 1 => faceCarrierComp (iteratedProjectionCarrier C n)
      (geometricProjectionCarrier (iteratedSubdivision C n))

lemma iteratedSubdivision_inv_carried (C : FiniteGeometricComplex E) :
    ∀ n : ℕ, CarriedBy (iteratedProjectionCarrier C n)
      (iteratedSubdivisionChainHomotopyEquiv C n).inv := by
  intro n
  induction n with
  | zero => exact identityAugChainMap_carriedBy (abstractComplex C)
  | succ n ih =>
      exact carriedBy_comp
        (geometricSubdivision_inv_carried (iteratedSubdivision C n)) ih

lemma iteratedProjectionCarrier_vertex_mem_convexHull
    (C : FiniteGeometricComplex E) :
    ∀ (n : ℕ) (s : ComplexFace (abstractComplex (iteratedSubdivision C n)))
      {v : GeometricVertex (iteratedSubdivision C n)}, v ∈ s.1 →
      (v : E) ∈ convexHull ℝ
        (((iteratedProjectionCarrier C n).face s).1.map
          (geometricVertexEmbedding C) : Set E) := by
  intro n
  induction n with
  | zero =>
      intro s v hv
      exact subset_convexHull ℝ _
        (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
  | succ n ih =>
      intro s v hv
      let T := (geometricProjectionCarrier
        (iteratedSubdivision C n)).face s
      have hvT : (v : E) ∈ convexHull ℝ
          (T.1.map (geometricVertexEmbedding (iteratedSubdivision C n)) : Set E) :=
        geometricProjectionCarrier_vertex_mem_convexHull
          (iteratedSubdivision C n) s hv
      apply (convexHull_min (s :=
          (T.1.map (geometricVertexEmbedding (iteratedSubdivision C n)) : Set E))
        (t := convexHull ℝ
          (((iteratedProjectionCarrier C n).face T).1.map
            (geometricVertexEmbedding C) : Set E)) ?_
        (convex_convexHull ℝ _)) hvT
      intro x hx
      rw [Finset.coe_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      exact ih T hu

lemma approximation_chainMap_carriedBy_iteratedProjection
    [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) (n : ℕ)
    (θ : SimplicialVertexMap (iteratedSubdivision C n) C)
    (hθ : θ.Approximates (subdivisionToOriginalSpace C n)) :
    CarriedBy (iteratedProjectionCarrier C n) θ.chainMap := by
  apply carriedBy_monoCarrier (A := θ.faceCarrier)
  · intro s w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    by_contra hnot
    have hopen := hθ v (vertexPoint_mem_openStar (iteratedSubdivision C n) v)
    apply hopen
    rw [faceUnionWithout]
    refine mem_iUnion.mpr
      ⟨abstractFaceToGeometricFace C ((iteratedProjectionCarrier C n).face s), ?_⟩
    rw [if_neg]
    · exact iteratedProjectionCarrier_vertex_mem_convexHull C n s hv
    · intro hmem
      obtain ⟨u, hu, huv⟩ := Finset.mem_map.mp hmem
      apply hnot
      have huv' : u = θ v := Subtype.ext huv
      exact huv' ▸ hu
  · exact carriedAugChainMap_carriedBy θ.faceCarrier

noncomputable def approximationProjection_chainHomotopy
    [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) (n : ℕ)
    (θ : SimplicialVertexMap (iteratedSubdivision C n) C)
    (hθ : θ.Approximates (subdivisionToOriginalSpace C n)) :
    AugChainHomotopy θ.chainMap
      (iteratedSubdivisionChainHomotopyEquiv C n).inv :=
  carrierHomotopy (iteratedProjectionCarrier C n) _ _
    (approximation_chainMap_carriedBy_iteratedProjection C n θ hθ)
    (iteratedSubdivision_inv_carried C n)

noncomputable def approximationSubdivision_chainHomotopy_id
    [FiniteDimensional ℝ E]
    (C : FiniteGeometricComplex E) (n : ℕ)
    (θ : SimplicialVertexMap (iteratedSubdivision C n) C)
    (hθ : θ.Approximates (subdivisionToOriginalSpace C n)) :
    AugChainHomotopy
      (θ.chainMap.comp (iteratedSubdivisionChainHomotopyEquiv C n).hom)
      (AugChainMap.id (abstractComplex C)) :=
  augChainHomotopyTrans
    (augChainHomotopyPrecomp
      (approximationProjection_chainHomotopy C n θ hθ)
      (iteratedSubdivisionChainHomotopyEquiv C n).hom)
    (iteratedSubdivisionChainHomotopyEquiv C n).inv_hom

/-! ### One-sided chain domination -/

lemma exists_augChainDomination_of_homotopy
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (C : FiniteGeometricComplex E) (D : FiniteGeometricComplex F)
    (f : C(C.K.space, D.K.space)) (g : C(D.K.space, C.K.space))
    (H : ContinuousMap.Homotopy (g.comp f) (ContinuousMap.id C.K.space)) :
    ∃ Fmap : AugChainMap (abstractComplex C) (abstractComplex D),
      ∃ Gmap : AugChainMap (abstractComplex D) (abstractComplex C),
        Nonempty (AugChainHomotopy (Gmap.comp Fmap)
          (AugChainMap.id (abstractComplex C))) := by
  obtain ⟨m, ψ, hψ⟩ := exists_subdivisionApproximation g g.continuous
  let Dm := iteratedSubdivision D m
  let fm : C(C.K.space, Dm.K.space) :=
    ⟨fun x => originalToSubdivisionSpace D m (f x),
      (continuous_originalToSubdivisionSpace D m).comp f.continuous⟩
  obtain ⟨δf, hδf, hcoverf⟩ := exists_starCoverRadius fm fm.continuous
  obtain ⟨δH, hδH, hcoverH⟩ := exists_homotopyStarCoverRadius H
  have hmin : 0 < min δf δH := lt_min hδf hδH
  obtain ⟨n, hmesh⟩ := exists_iteratedSubdivision_mesh_lt C hmin
  let Cn := iteratedSubdivision C n
  have hmeshf : complexMesh Cn < δf := hmesh.trans_le (min_le_left _ _)
  have hmeshH : complexMesh Cn < δH := hmesh.trans_le (min_le_right _ _)
  let fn : Cn.K.space → Dm.K.space :=
    fun x => fm (subdivisionToOriginalSpace C n x)
  have hcoverfN : ∀ x : Cn.K.space, ∃ w : GeometricVertex Dm,
      Metric.ball x δf ⊆ fn ⁻¹' openStar Dm w := by
    intro x
    obtain ⟨w, hw⟩ := hcoverf (subdivisionToOriginalSpace C n x)
    refine ⟨w, ?_⟩
    intro y hy
    apply hw
    rw [Metric.mem_ball, dist_subdivisionToOriginalSpace]
    exact hy
  let φ := simplicialApproximationOfCover fn δf hcoverfN hmeshf
  have hφ : φ.Approximates fn :=
    simplicialApproximationOfCover_approximates fn δf hcoverfN hmeshf
  let Hn := homotopyOnSubdivision H n
  have hcoverHN : ∀ z : I × Cn.K.space, ∃ w : GeometricVertex C,
      Metric.ball z δH ⊆ Hn ⁻¹' openStar C w := by
    intro z
    obtain ⟨w, hw⟩ := hcoverH (z.1, subdivisionToOriginalSpace C n z.2)
    refine ⟨w, ?_⟩
    intro y hy
    apply hw
    rw [Metric.mem_ball, Prod.dist_eq] at hy
    rw [Metric.mem_ball, Prod.dist_eq]
    change max (dist y.1 z.1)
      (dist (subdivisionToOriginalSpace C n y.2)
        (subdivisionToOriginalSpace C n z.2)) < δH
    rw [dist_subdivisionToOriginalSpace]
    exact hy
  obtain ⟨α, θ, hα, hθ, ⟨Hαθ⟩⟩ :=
    exists_endpointApproximations_chainHomotopy Hn δH hδH hcoverHN hmeshH
  let A := ψ.comp φ
  have hA : A.Approximates
      (fun x => (g.comp f) (subdivisionToOriginalSpace C n x)) := by
    intro v x hx
    have hfx := hφ v hx
    have hgfx := hψ (φ v) hfx
    exact hgfx
  have HAα : AugChainHomotopy A.chainMap α.chainMap :=
    approximations_chainHomotopy A α
      (fun x => (g.comp f) (subdivisionToOriginalSpace C n x)) hA hα
  let SC := (iteratedSubdivisionChainHomotopyEquiv C n).hom
  let SD := (iteratedSubdivisionChainHomotopyEquiv D m).hom
  let PD := (iteratedSubdivisionChainHomotopyEquiv D m).inv
  let Fmap : AugChainMap (abstractComplex C) (abstractComplex D) :=
    PD.comp (φ.chainMap.comp SC)
  let Gmap : AugChainMap (abstractComplex D) (abstractComplex C) :=
    ψ.chainMap.comp SD
  have HAid : AugChainHomotopy (A.chainMap.comp SC)
      (AugChainMap.id (abstractComplex C)) :=
    augChainHomotopyTrans
      (augChainHomotopyPrecomp HAα SC)
      (augChainHomotopyTrans
        (augChainHomotopyPrecomp Hαθ SC)
        (approximationSubdivision_chainHomotopy_id C n θ hθ))
  have HcancelBase := (iteratedSubdivisionChainHomotopyEquiv D m).hom_inv
  let Hcancel := augChainHomotopyPostcomp
    (augChainHomotopyPrecomp HcancelBase (φ.chainMap.comp SC)) ψ.chainMap
  have Hcancel' : AugChainHomotopy (Gmap.comp Fmap)
      ((ψ.chainMap.comp φ.chainMap).comp SC) :=
    augChainHomotopyCongr Hcancel (by
      apply augChainMap_ext
      intro k
      apply LinearMap.ext
      intro x
      rfl) (by
      apply augChainMap_ext
      intro k
      apply LinearMap.ext
      intro x
      rfl)
  have Hcomp : AugChainHomotopy
      ((ψ.chainMap.comp φ.chainMap).comp SC) (A.chainMap.comp SC) :=
    augChainHomotopyPrecomp
      (simplicialVertexMap_comp_chainHomotopy ψ φ) SC
  exact ⟨Fmap, Gmap,
    ⟨augChainHomotopyTrans Hcancel'
      (augChainHomotopyTrans Hcomp HAid)⟩⟩

end FinitePolyhedron

end

end Submission.Helpers.DehnSommerville
