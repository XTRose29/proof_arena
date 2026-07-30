import Submission.LinkHomology

namespace Submission.Helpers.DehnSommerville

open LeanEval.Combinatorics.DehnSommerville
open scoped ContinuousMap

noncomputable section

/-! ### A canonical coordinate realization -/

/-- The abstract complex obtained by replacing each geometric vertex by its subtype. -/
def vertexComplex {d : ℕ} (X : FiniteSimplicialSphere d) :
    PreAbstractSimplicialComplex (Vertex X) where
  faces := {τ | τ.map (vertexEmbedding X) ∈ X.K.faces}
  isRelLowerSet_faces := by
    intro τ hτ
    constructor
    · exact Finset.map_nonempty.mp (X.K.nonempty_of_mem_faces hτ)
    · intro υ hυτ hυ
      exact X.K.down_closed hτ (Finset.map_subset_map.mpr hυτ)
        (Finset.map_nonempty.mpr hυ)

@[simp]
lemma mem_vertexComplex_faces {d : ℕ} {X : FiniteSimplicialSphere d}
    {τ : Finset (Vertex X)} :
    τ ∈ (vertexComplex X).faces ↔ τ.map (vertexEmbedding X) ∈ X.K.faces :=
  Iff.rfl

/-- The standard basis point corresponding to a vertex. -/
def canonicalVertex {d : ℕ} (X : FiniteSimplicialSphere d) (v : Vertex X) :
    Vertex X → ℝ :=
  Pi.single v 1

lemma canonicalVertex_injective {d : ℕ} (X : FiniteSimplicialSphere d) :
    Function.Injective (canonicalVertex X) := by
  intro v w hvw
  by_contra hne
  have h := congrFun hvw v
  simp [canonicalVertex, hne] at h

/-- The canonical geometric realization of the face complex in barycentric coordinates. -/
noncomputable def canonicalComplex {d : ℕ} (X : FiniteSimplicialSphere d) :
    Geometry.SimplicialComplex ℝ (Vertex X → ℝ) := by
  classical
  exact Geometry.SimplicialComplex.ofAffineIndependent
    ((vertexComplex X).map (canonicalVertex X))
    ((Pi.linearIndependent_single_one (Vertex X) ℝ).affineIndependent.range.mono (by
      intro w hw
      simp only [Set.mem_iUnion, Finset.mem_coe] at hw
      obtain ⟨_, ⟨_, _, rfl⟩, hw⟩ := hw
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨v, rfl⟩))

lemma mem_canonicalComplex_faces {d : ℕ} {X : FiniteSimplicialSphere d}
    {s : Finset (Vertex X → ℝ)} :
    s ∈ (canonicalComplex X).faces ↔
      ∃ τ ∈ (vertexComplex X).faces, s = τ.image (canonicalVertex X) := by
  classical
  change s ∈ ((vertexComplex X).map (canonicalVertex X)).faces ↔ _
  simp [PreAbstractSimplicialComplex.map, eq_comm]

/-- Evaluation of barycentric coordinates at the original geometric vertices. -/
def canonicalEval {d : ℕ} (X : FiniteSimplicialSphere d) :
    (Vertex X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  Fintype.linearCombination ℝ fun v => (v : EuclideanSpace ℝ (Fin d))

@[simp]
lemma canonicalEval_canonicalVertex {d : ℕ} (X : FiniteSimplicialSphere d)
    (v : Vertex X) :
    canonicalEval X (canonicalVertex X v) = (v : EuclideanSpace ℝ (Fin d)) := by
  classical
  simp [canonicalEval, canonicalVertex, Fintype.linearCombination_apply_single]

lemma mem_vertices_of_mem_face {d : ℕ} (X : FiniteSimplicialSphere d)
    {s : Finset (EuclideanSpace ℝ (Fin d))} (hs : s ∈ X.K.faces)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ s) : x ∈ X.K.vertices := by
  exact X.K.down_closed hs (Finset.singleton_subset_iff.mpr hx)
    (Finset.singleton_nonempty x)

/-- Lift a geometric face to the finite vertex subtype. -/
def liftFace {d : ℕ} (X : FiniteSimplicialSphere d)
    (s : Finset (EuclideanSpace ℝ (Fin d))) (hs : s ∈ X.K.faces) :
    Finset (Vertex X) :=
  s.attach.map
    ⟨fun x => ⟨x.val, mem_vertices_of_mem_face X hs x.property⟩,
      fun _ _ h => by
        apply Subtype.ext
        exact congrArg (fun z : Vertex X => (z : EuclideanSpace ℝ (Fin d))) h⟩

lemma map_liftFace {d : ℕ} (X : FiniteSimplicialSphere d)
    (s : Finset (EuclideanSpace ℝ (Fin d))) (hs : s ∈ X.K.faces) :
    (liftFace X s hs).map (vertexEmbedding X) = s := by
  ext x
  simp [liftFace, vertexEmbedding]
  exact fun hx => mem_vertices_of_mem_face X hs hx

lemma liftFace_mem_vertexComplex {d : ℕ} (X : FiniteSimplicialSphere d)
    (s : Finset (EuclideanSpace ℝ (Fin d))) (hs : s ∈ X.K.faces) :
    liftFace X s hs ∈ (vertexComplex X).faces := by
  rw [mem_vertexComplex_faces, map_liftFace X s hs]
  exact hs

lemma canonicalEval_image_faceVertices {d : ℕ} (X : FiniteSimplicialSphere d)
    (τ : Finset (Vertex X)) :
    canonicalEval X '' (τ.image (canonicalVertex X) : Set (Vertex X → ℝ)) =
      (τ.map (vertexEmbedding X) : Set (EuclideanSpace ℝ (Fin d))) := by
  classical
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Finset.mem_coe] at hw ⊢
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rw [canonicalEval_canonicalVertex]
    exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
  · intro hx
    rw [Finset.mem_coe] at hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
    exact ⟨canonicalVertex X v,
      by
        rw [Finset.mem_coe]
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩,
      canonicalEval_canonicalVertex X v⟩

lemma canonicalEval_image_convexHull {d : ℕ} (X : FiniteSimplicialSphere d)
    (τ : Finset (Vertex X)) :
    canonicalEval X ''
        convexHull ℝ (τ.image (canonicalVertex X) : Set (Vertex X → ℝ)) =
      convexHull ℝ (τ.map (vertexEmbedding X) : Set (EuclideanSpace ℝ (Fin d))) := by
  rw [(canonicalEval X).image_convexHull, canonicalEval_image_faceVertices]

lemma mem_convexHull_canonicalFace_iff {d : ℕ} (X : FiniteSimplicialSphere d)
    (τ : Finset (Vertex X)) (w : Vertex X → ℝ) :
    w ∈ convexHull ℝ (τ.image (canonicalVertex X) : Set (Vertex X → ℝ)) ↔
      (∀ v, 0 ≤ w v) ∧ (∀ v, v ∉ τ → w v = 0) ∧ ∑ v, w v = 1 := by
  classical
  constructor
  · intro hw
    constructor
    · intro v
      apply (convexHull_min (s := (τ.image (canonicalVertex X) : Set (Vertex X → ℝ)))
        (t := {z | 0 ≤ z v}) ?_ (convex_halfSpace_ge (LinearMap.proj v).isLinear 0)) hw
      intro z hz
      rw [Finset.mem_coe] at hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      by_cases huv : u = v <;> simp [canonicalVertex, huv]
    constructor
    · intro v hv
      apply (convexHull_min (s := (τ.image (canonicalVertex X) : Set (Vertex X → ℝ)))
        (t := {z | z v = 0}) ?_ (convex_hyperplane (LinearMap.proj v).isLinear 0)) hw
      intro z hz
      rw [Finset.mem_coe] at hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      have huv : u ≠ v := fun h => hv (h ▸ hu)
      simp [canonicalVertex, huv]
    · let total : (Vertex X → ℝ) →ₗ[ℝ] ℝ :=
        Fintype.linearCombination ℝ fun _ => (1 : ℝ)
      have ht := (convexHull_min (s := (τ.image (canonicalVertex X) : Set (Vertex X → ℝ)))
        (t := {z | total z = 1}) ?_ (convex_hyperplane total.isLinear 1)) hw
      · simpa [total, Fintype.linearCombination_apply] using ht
      · intro z hz
        rw [Finset.mem_coe] at hz
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
        simp [total, canonicalVertex, Fintype.linearCombination_apply]
  · rintro ⟨hnonneg, hzero, hsum⟩
    have hsumτ : ∑ v ∈ τ, w v = 1 := by
      rw [← hsum]
      exact Finset.sum_subset (Finset.subset_univ τ) (fun v _ hv => hzero v hv)
    have hw' : τ.centerMass w (canonicalVertex X) = w := by
      rw [τ.centerMass_eq_of_sum_1 _ hsumτ]
      funext v
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hv : v ∈ τ
      · rw [Finset.sum_eq_single v]
        · simp [canonicalVertex]
        · intro u _ huv
          change w u * (Pi.single u (1 : ℝ) : Vertex X → ℝ) v = 0
          rw [Pi.single_eq_of_ne huv.symm]
          simp
        · exact fun h => (h hv).elim
      · rw [Finset.sum_eq_zero]
        · exact (hzero v hv).symm
        · intro u hu
          have hvu : v ≠ u := fun h => hv (h ▸ hu)
          change w u * (Pi.single u (1 : ℝ) : Vertex X → ℝ) v = 0
          rw [Pi.single_eq_of_ne hvu]
          simp
    rw [← hw']
    exact τ.centerMass_mem_convexHull (fun v hv => hnonneg v) (by simp [hsumτ])
      (fun v hv => by
        rw [Finset.mem_coe]
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩)

lemma canonicalEval_injectiveOn_face {d : ℕ} (X : FiniteSimplicialSphere d)
    (τ : Finset (Vertex X)) (hτ : τ ∈ (vertexComplex X).faces) :
    Set.InjOn (canonicalEval X)
      (convexHull ℝ (τ.image (canonicalVertex X) : Set (Vertex X → ℝ))) := by
  classical
  intro w hw z hz hwz
  obtain ⟨_, hwzero, hwsum⟩ := (mem_convexHull_canonicalFace_iff X τ w).mp hw
  obtain ⟨_, hzzero, hzsum⟩ := (mem_convexHull_canonicalFace_iff X τ z).mp hz
  have hwsumτ : ∑ v ∈ τ, w v = 1 := by
    rw [← hwsum]
    exact Finset.sum_subset (Finset.subset_univ τ) (fun v _ hv => hwzero v hv)
  have hzsumτ : ∑ v ∈ τ, z v = 1 := by
    rw [← hzsum]
    exact Finset.sum_subset (Finset.subset_univ τ) (fun v _ hv => hzzero v hv)
  have hwsum' : ∑ v : τ, w v = 1 := by
    rw [← Finset.sum_subtype τ (by simp)]
    exact hwsumτ
  have hzsum' : ∑ v : τ, z v = 1 := by
    rw [← Finset.sum_subtype τ (by simp)]
    exact hzsumτ
  let e : τ ↪ (τ.map (vertexEmbedding X)) :=
    ⟨fun v => ⟨v.1.1, Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩,
      fun a b hab => by
        apply Subtype.ext
        apply (vertexEmbedding X).injective
        exact congrArg (fun q : (τ.map (vertexEmbedding X)) => q.1) hab⟩
  have hind : AffineIndependent ℝ
      (fun v : τ => (v.1 : EuclideanSpace ℝ (Fin d))) := by
    simpa [e, Function.comp_def] using (X.K.indep hτ).comp_embedding e
  have hwcomb : Finset.univ.affineCombination ℝ
      (fun v : τ => (v.1 : EuclideanSpace ℝ (Fin d))) (fun v => w v.1) =
      canonicalEval X w := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hwsum']
    rw [canonicalEval, Fintype.linearCombination_apply]
    calc
      (∑ v : τ, w v.1 • (v.1 : EuclideanSpace ℝ (Fin d))) =
          ∑ v ∈ τ, w v • (v : EuclideanSpace ℝ (Fin d)) :=
        (Finset.sum_subtype τ (fun _ => Iff.rfl)
          (fun v => w v • (v : EuclideanSpace ℝ (Fin d)))).symm
      _ = ∑ v, w v • (v : EuclideanSpace ℝ (Fin d)) :=
        Finset.sum_subset (Finset.subset_univ τ)
          (fun v _ hv => by rw [hwzero v hv, zero_smul])
  have hzcomb : Finset.univ.affineCombination ℝ
      (fun v : τ => (v.1 : EuclideanSpace ℝ (Fin d))) (fun v => z v.1) =
      canonicalEval X z := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hzsum']
    rw [canonicalEval, Fintype.linearCombination_apply]
    calc
      (∑ v : τ, z v.1 • (v.1 : EuclideanSpace ℝ (Fin d))) =
          ∑ v ∈ τ, z v • (v : EuclideanSpace ℝ (Fin d)) :=
        (Finset.sum_subtype τ (fun _ => Iff.rfl)
          (fun v => z v • (v : EuclideanSpace ℝ (Fin d)))).symm
      _ = ∑ v, z v • (v : EuclideanSpace ℝ (Fin d)) :=
        Finset.sum_subset (Finset.subset_univ τ)
          (fun v _ hv => by rw [hzzero v hv, zero_smul])
  have heq : ∀ v : τ, w v = z v := by
    have h := (hind.affineCombination_eq_iff_eq hwsum' hzsum').mp
      (hwcomb.trans (hwz.trans hzcomb.symm))
    exact fun v => h v (Finset.mem_univ v)
  funext v
  by_cases hv : v ∈ τ
  · exact heq ⟨v, hv⟩
  · rw [hwzero v hv, hzzero v hv]

lemma convexHull_canonicalFace_mono {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ υ : Finset (Vertex X)} (hτυ : τ ⊆ υ) :
    convexHull ℝ (τ.image (canonicalVertex X) : Set (Vertex X → ℝ)) ⊆
      convexHull ℝ (υ.image (canonicalVertex X) : Set (Vertex X → ℝ)) := by
  apply convexHull_mono
  intro w hw
  rw [Finset.mem_coe] at hw ⊢
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  exact Finset.mem_image.mpr ⟨v, hτυ hv, rfl⟩

lemma canonicalEval_injectiveOn_space {d : ℕ} (X : FiniteSimplicialSphere d) :
    Set.InjOn (canonicalEval X) (canonicalComplex X).space := by
  intro w hw z hz hwz
  rw [Geometry.SimplicialComplex.mem_space_iff] at hw hz
  obtain ⟨sw, hsw, hw⟩ := hw
  obtain ⟨sz, hsz, hz⟩ := hz
  obtain ⟨τ, hτ, rfl⟩ := mem_canonicalComplex_faces.mp hsw
  obtain ⟨υ, hυ, rfl⟩ := mem_canonicalComplex_faces.mp hsz
  have hw' : canonicalEval X w ∈ convexHull ℝ
      (τ.map (vertexEmbedding X) : Set (EuclideanSpace ℝ (Fin d))) := by
    rw [← canonicalEval_image_convexHull X τ]
    exact ⟨w, hw, rfl⟩
  have hz' : canonicalEval X z ∈ convexHull ℝ
      (υ.map (vertexEmbedding X) : Set (EuclideanSpace ℝ (Fin d))) := by
    rw [← canonicalEval_image_convexHull X υ]
    exact ⟨z, hz, rfl⟩
  have hinter : canonicalEval X w ∈ convexHull ℝ
      ((τ.map (vertexEmbedding X) ∩ υ.map (vertexEmbedding X) :
        Finset (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d))) :=
    by
      simpa only [Finset.coe_inter] using
        X.K.inter_subset_convexHull hτ hυ ⟨hw', hwz ▸ hz'⟩
  let ρ := τ ∩ υ
  have hmapρ : ρ.map (vertexEmbedding X) =
      τ.map (vertexEmbedding X) ∩ υ.map (vertexEmbedding X) := by
    exact Finset.map_inter τ υ
  have hinter' : canonicalEval X w ∈ convexHull ℝ
      (ρ.map (vertexEmbedding X) : Set (EuclideanSpace ℝ (Fin d))) := by
    rw [hmapρ]
    exact hinter
  rw [← canonicalEval_image_convexHull X ρ] at hinter'
  obtain ⟨r, hr, her⟩ := hinter'
  have hrτ : r ∈ convexHull ℝ
      (τ.image (canonicalVertex X) : Set (Vertex X → ℝ)) :=
    convexHull_canonicalFace_mono X Finset.inter_subset_left hr
  have hrυ : r ∈ convexHull ℝ
      (υ.image (canonicalVertex X) : Set (Vertex X → ℝ)) :=
    convexHull_canonicalFace_mono X Finset.inter_subset_right hr
  have hwr : w = r :=
    canonicalEval_injectiveOn_face X τ hτ hw hrτ her.symm
  have hzr : z = r :=
    canonicalEval_injectiveOn_face X υ hυ hz hrυ (hwz.symm.trans her.symm)
  exact hwr.trans hzr.symm

lemma canonicalEval_image_space {d : ℕ} (X : FiniteSimplicialSphere d) :
    canonicalEval X '' (canonicalComplex X).space = X.K.space := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Geometry.SimplicialComplex.mem_space_iff] at hw ⊢
    obtain ⟨s, hs, hw⟩ := hw
    obtain ⟨τ, hτ, rfl⟩ := mem_canonicalComplex_faces.mp hs
    refine ⟨τ.map (vertexEmbedding X), hτ, ?_⟩
    rw [← canonicalEval_image_convexHull X τ]
    exact ⟨w, hw, rfl⟩
  · intro hx
    rw [Geometry.SimplicialComplex.mem_space_iff] at hx
    obtain ⟨s, hs, hx⟩ := hx
    let τ := liftFace X s hs
    have hτ : τ ∈ (vertexComplex X).faces := liftFace_mem_vertexComplex X s hs
    have hface : τ.image (canonicalVertex X) ∈ (canonicalComplex X).faces :=
      mem_canonicalComplex_faces.mpr ⟨τ, hτ, rfl⟩
    have hx' : x ∈ convexHull ℝ
        (τ.map (vertexEmbedding X) : Set (EuclideanSpace ℝ (Fin d))) := by
      rw [show τ.map (vertexEmbedding X) = s from map_liftFace X s hs]
      exact hx
    rw [← canonicalEval_image_convexHull X τ] at hx'
    obtain ⟨w, hw, rfl⟩ := hx'
    exact ⟨w, (canonicalComplex X).convexHull_subset_space hface hw, rfl⟩

lemma finite_canonicalComplex_faces {d : ℕ} (X : FiniteSimplicialSphere d) :
    (canonicalComplex X).faces.Finite := by
  classical
  have hvertex : (vertexComplex X).faces.Finite := Set.toFinite _
  refine (hvertex.image fun τ => τ.image (canonicalVertex X)).subset ?_
  intro s hs
  obtain ⟨τ, hτ, rfl⟩ := mem_canonicalComplex_faces.mp hs
  exact ⟨τ, hτ, rfl⟩

lemma isCompact_canonicalComplex_space {d : ℕ} (X : FiniteSimplicialSphere d) :
    IsCompact (canonicalComplex X).space := by
  rw [Geometry.SimplicialComplex.space]
  exact (finite_canonicalComplex_faces X).isCompact_biUnion fun s _ =>
    s.finite_toSet.isCompact_convexHull ℝ

/-- Evaluation restricted to the canonical and original underlying spaces. -/
def canonicalEvalOnSpace {d : ℕ} (X : FiniteSimplicialSphere d) :
    (canonicalComplex X).space → X.K.space :=
  fun w => ⟨canonicalEval X w.1, by
    rw [← canonicalEval_image_space X]
    exact ⟨w.1, w.2, rfl⟩⟩

lemma continuous_canonicalEvalOnSpace {d : ℕ} (X : FiniteSimplicialSphere d) :
    Continuous (canonicalEvalOnSpace X) := by
  apply Continuous.subtype_mk
  exact (canonicalEval X).continuous_of_finiteDimensional.comp continuous_subtype_val

lemma canonicalEvalOnSpace_bijective {d : ℕ} (X : FiniteSimplicialSphere d) :
    Function.Bijective (canonicalEvalOnSpace X) := by
  constructor
  · intro w z hwz
    apply Subtype.ext
    apply canonicalEval_injectiveOn_space X w.2 z.2
    exact congrArg Subtype.val hwz
  · intro x
    have hx : x.1 ∈ canonicalEval X '' (canonicalComplex X).space := by
      rw [canonicalEval_image_space X]
      exact x.2
    obtain ⟨w, hw, hwx⟩ := hx
    exact ⟨⟨w, hw⟩, Subtype.ext hwx⟩

/-- The canonical barycentric-coordinate realization is homeomorphic to the
original geometric realization. -/
noncomputable def canonicalSpaceHomeomorph {d : ℕ} (X : FiniteSimplicialSphere d) :
    (canonicalComplex X).space ≃ₜ X.K.space := by
  letI : CompactSpace (canonicalComplex X).space :=
    isCompact_iff_compactSpace.mp (isCompact_canonicalComplex_space X)
  exact (isHomeomorph_iff_continuous_bijective.mpr
    ⟨continuous_canonicalEvalOnSpace X, canonicalEvalOnSpace_bijective X⟩).homeomorph
      (canonicalEvalOnSpace X)

/-- The sphere homeomorphism transported to canonical coordinates. -/
noncomputable def canonicalSphereHomeomorph {d : ℕ} (X : FiniteSimplicialSphere d) :
    (canonicalComplex X).space ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  (canonicalSpaceHomeomorph X).trans X.sphere_homeomorph.some

/-! ### Puncturing at a face barycenter -/

/-- The barycenter of a face in canonical coordinates. -/
def faceBarycenter {d : ℕ} (X : FiniteSimplicialSphere d)
    (τ : Finset (Vertex X)) : Vertex X → ℝ :=
  fun v => if v ∈ τ then (τ.card : ℝ)⁻¹ else 0

@[simp]
lemma faceBarycenter_apply_of_mem {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} {v : Vertex X} (hv : v ∈ τ) :
    faceBarycenter X τ v = (τ.card : ℝ)⁻¹ := by
  simp [faceBarycenter, hv]

@[simp]
lemma faceBarycenter_apply_of_notMem {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} {v : Vertex X} (hv : v ∉ τ) :
    faceBarycenter X τ v = 0 := by
  simp [faceBarycenter, hv]

lemma sum_faceBarycenter {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτne : τ.Nonempty) :
    ∑ v, faceBarycenter X τ v = 1 := by
  classical
  rw [show (∑ v, faceBarycenter X τ v) =
      ∑ v ∈ τ, (τ.card : ℝ)⁻¹ by simp [faceBarycenter]]
  simp [hτne.ne_empty]

lemma faceBarycenter_mem_convexHull {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτne : τ.Nonempty) :
    faceBarycenter X τ ∈
      convexHull ℝ (τ.image (canonicalVertex X) : Set (Vertex X → ℝ)) := by
  rw [mem_convexHull_canonicalFace_iff X τ]
  exact ⟨fun v => by
      by_cases hv : v ∈ τ
      · simp [faceBarycenter, hv]
      · simp [faceBarycenter, hv],
    fun v hv => faceBarycenter_apply_of_notMem X hv,
    sum_faceBarycenter X hτne⟩

/-- The barycenter as a point of the canonical realization. -/
def faceBarycenterPoint {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces) :
    (canonicalComplex X).space :=
  ⟨faceBarycenter X τ, (canonicalComplex X).convexHull_subset_space
    (mem_canonicalComplex_faces.mpr ⟨τ, hτ, rfl⟩)
    (faceBarycenter_mem_convexHull X
      ((vertexComplex X).isRelLowerSet_faces hτ).1)⟩

/-- Stereographic projection identifies a sphere punctured at any point with
the orthogonal complement of that point. -/
noncomputable def puncturedSphereHomeomorph {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : Metric.sphere (0 : E) 1) :
    ({q}ᶜ : Set (Metric.sphere (0 : E) 1)) ≃ₜ (ℝ ∙ (q : E))ᗮ := by
  let hv : ‖(q : E)‖ = 1 := norm_eq_of_mem_sphere q
  let e := stereographic hv
  have hsource : e.source = ({q}ᶜ : Set (Metric.sphere (0 : E) 1)) := by
    rw [stereographic_source]
  have htarget : e.target = (Set.univ : Set (ℝ ∙ (q : E))ᗮ) :=
    stereographic_target hv
  exact (Homeomorph.setCongr hsource.symm).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr htarget).trans (Homeomorph.Set.univ _)))

lemma contractibleSpace_puncturedSphere {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : Metric.sphere (0 : E) 1) :
    ContractibleSpace ({q}ᶜ : Set (Metric.sphere (0 : E) 1)) :=
  (puncturedSphereHomeomorph q).contractibleSpace

/-- The canonical realization punctured at a face barycenter is contractible. -/
lemma contractibleSpace_canonical_punctured {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces) :
    ContractibleSpace
      ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) := by
  let e := canonicalSphereHomeomorph X
  let p := faceBarycenterPoint X hτ
  let q := e p
  haveI : ContractibleSpace ({q}ᶜ : Set (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1)) := contractibleSpace_puncturedSphere q
  exact (e.subtype (p := fun x => x ∈ ({p}ᶜ : Set _))
    (q := fun y => y ∈ ({q}ᶜ : Set _)) (fun x => by simp [p, q])).contractibleSpace

/-! ### Radial retraction onto a face deletion -/

/-- The minimum coordinate on a nonempty face. -/
def faceMin {d : ℕ} (X : FiniteSimplicialSphere d)
    (τ : Finset (Vertex X)) (hτne : τ.Nonempty) (w : Vertex X → ℝ) : ℝ :=
  τ.inf' hτne fun v => w v

lemma continuous_faceMin {d : ℕ} (X : FiniteSimplicialSphere d)
    (τ : Finset (Vertex X)) (hτne : τ.Nonempty) :
    Continuous (faceMin X τ hτne) := by
  exact Continuous.finset_inf'_apply hτne fun v _ => continuous_apply v

lemma faceMin_le {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτne : τ.Nonempty) (w : Vertex X → ℝ)
    {v : Vertex X} (hv : v ∈ τ) :
    faceMin X τ hτne w ≤ w v := by
  exact Finset.inf'_le _ hv

lemma faceMin_nonneg {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτne : τ.Nonempty) {w : Vertex X → ℝ}
    (hw : ∀ v, 0 ≤ w v) :
    0 ≤ faceMin X τ hτne w := by
  exact Finset.le_inf' hτne _ fun v _ => hw v

lemma exists_faceMin_eq {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτne : τ.Nonempty) (w : Vertex X → ℝ) :
    ∃ v ∈ τ, w v = faceMin X τ hτne w := by
  obtain ⟨v, hv, hmin⟩ := τ.exists_min_image (fun u => w u) hτne
  refine ⟨v, hv, le_antisymm ?_ ?_⟩
  · exact Finset.le_inf' hτne _ hmin
  · exact Finset.inf'_le _ hv

/-- Canonical deletion points are those where at least one coordinate of `τ`
vanishes. -/
def canonicalDeletionSet {d : ℕ} (X : FiniteSimplicialSphere d)
    (τ : Finset (Vertex X)) (hτne : τ.Nonempty) :
    Set (canonicalComplex X).space :=
  {w | faceMin X τ hτne w.1 = 0}

lemma mem_canonicalDeletionSet_iff {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτne : τ.Nonempty)
    (w : (canonicalComplex X).space) :
    w ∈ canonicalDeletionSet X τ hτne ↔ ∃ v ∈ τ, w.1 v = 0 := by
  constructor
  · intro hw
    obtain ⟨v, hv, hmin⟩ := exists_faceMin_eq X hτne w.1
    exact ⟨v, hv, hmin.trans hw⟩
  · rintro ⟨v, hv, hwv⟩
    change faceMin X τ hτne w.1 = 0
    apply le_antisymm
    · simpa [hwv] using faceMin_le X hτne w.1 hv
    · obtain ⟨s, hs, hws⟩ := (canonicalComplex X).mem_space_iff.mp w.2
      obtain ⟨υ, _, rfl⟩ := mem_canonicalComplex_faces.mp hs
      exact faceMin_nonneg X hτne
        ((mem_convexHull_canonicalFace_iff X υ w.1).mp hws).1

lemma canonicalSpace_nonneg {d : ℕ} (X : FiniteSimplicialSphere d)
    (w : (canonicalComplex X).space) (v : Vertex X) : 0 ≤ w.1 v := by
  obtain ⟨s, hs, hws⟩ := (canonicalComplex X).mem_space_iff.mp w.2
  obtain ⟨τ, _, rfl⟩ := mem_canonicalComplex_faces.mp hs
  exact ((mem_convexHull_canonicalFace_iff X τ w.1).mp hws).1 v

lemma canonicalSpace_sum {d : ℕ} (X : FiniteSimplicialSphere d)
    (w : (canonicalComplex X).space) : ∑ v, w.1 v = 1 := by
  obtain ⟨s, hs, hws⟩ := (canonicalComplex X).mem_space_iff.mp w.2
  obtain ⟨τ, _, rfl⟩ := mem_canonicalComplex_faces.mp hs
  exact ((mem_convexHull_canonicalFace_iff X τ w.1).mp hws).2.2

lemma card_mul_faceMin_le_one {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτne : τ.Nonempty)
    (w : (canonicalComplex X).space) :
    (τ.card : ℝ) * faceMin X τ hτne w.1 ≤ 1 := by
  have hminsum : (∑ _v ∈ τ, faceMin X τ hτne w.1) ≤ ∑ v ∈ τ, w.1 v := by
    exact Finset.sum_le_sum fun v hv => faceMin_le X hτne w.1 hv
  have hsumle : (∑ v ∈ τ, w.1 v) ≤ ∑ v, w.1 v := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ τ)
      (fun v _ _ => canonicalSpace_nonneg X w v)
  simpa [canonicalSpace_sum X w, mul_comm] using hminsum.trans hsumle

lemma eq_faceBarycenter_of_card_mul_faceMin_eq_one {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτne : τ.Nonempty) (w : (canonicalComplex X).space)
    (heq : (τ.card : ℝ) * faceMin X τ hτne w.1 = 1) :
    w.1 = faceBarycenter X τ := by
  let m := faceMin X τ hτne w.1
  have hsumle : (∑ v ∈ τ, w.1 v) ≤ 1 := by
    simpa [canonicalSpace_sum X w] using
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ τ)
        (fun v _ _ => canonicalSpace_nonneg X w v))
  have hminsum : (τ.card : ℝ) * m ≤ ∑ v ∈ τ, w.1 v := by
    simpa [m, mul_comm] using
      (Finset.sum_le_sum fun v hv => faceMin_le X hτne w.1 hv)
  have hsumτ : ∑ v ∈ τ, w.1 v = 1 := le_antisymm hsumle (heq ▸ hminsum)
  have hdiffsum : ∑ v ∈ τ, (w.1 v - m) = 0 := by
    calc
      (∑ v ∈ τ, (w.1 v - m)) =
          (∑ v ∈ τ, w.1 v) - (τ.card : ℝ) * m := by
        rw [Finset.sum_sub_distrib]
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = 0 := by rw [hsumτ]; linarith [heq]
  have hdiffzero : ∀ v ∈ τ, w.1 v - m = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun v hv => sub_nonneg.mpr (faceMin_le X hτne w.1 hv))).mp hdiffsum
  have houtsum : ∑ v ∈ Finset.univ \ τ, w.1 v = 0 := by
    have hsplit : (∑ v ∈ Finset.univ \ τ, w.1 v) +
        (∑ v ∈ τ, w.1 v) = ∑ v, w.1 v :=
      Finset.sum_sdiff (Finset.subset_univ τ)
    rw [canonicalSpace_sum X w, hsumτ] at hsplit
    linarith
  have houtzero : ∀ v ∈ Finset.univ \ τ, w.1 v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => canonicalSpace_nonneg X w v)).mp houtsum
  have hcard : (τ.card : ℝ) ≠ 0 := by
    exact_mod_cast hτne.card_ne_zero
  have hm : m = (τ.card : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    apply (eq_div_iff hcard).mpr
    simpa [mul_comm] using heq
  funext v
  by_cases hv : v ∈ τ
  · rw [faceBarycenter_apply_of_mem X hv, ← hm]
    exact sub_eq_zero.mp (hdiffzero v hv)
  · rw [faceBarycenter_apply_of_notMem X hv]
    exact houtzero v (by simp [hv])

lemma radialDenom_pos {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces)
    (w : ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space)) :
    0 < 1 - (τ.card : ℝ) *
      faceMin X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1.1 := by
  let hτne := ((vertexComplex X).isRelLowerSet_faces hτ).1
  have hnonneg : 0 ≤ 1 - (τ.card : ℝ) * faceMin X τ hτne w.1.1 := by
    linarith [card_mul_faceMin_le_one X hτne w.1]
  have hne : 1 - (τ.card : ℝ) * faceMin X τ hτne w.1.1 ≠ 0 := by
    intro hzero
    have heq : (τ.card : ℝ) * faceMin X τ hτne w.1.1 = 1 := by linarith
    have hw := eq_faceBarycenter_of_card_mul_faceMin_eq_one X hτne w.1 heq
    exact w.2 (Subtype.ext hw)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Radial projection away from the barycenter, written in coordinates. -/
def radialRetractCoords {d : ℕ} (X : FiniteSimplicialSphere d)
    (τ : Finset (Vertex X)) (hτne : τ.Nonempty)
    (w : Vertex X → ℝ) : Vertex X → ℝ :=
  fun v =>
    (w v - if v ∈ τ then faceMin X τ hτne w else 0) /
      (1 - (τ.card : ℝ) * faceMin X τ hτne w)

lemma radialRetractCoords_nonneg {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces)
    (w : ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space))
    (v : Vertex X) :
    0 ≤ radialRetractCoords X τ
      ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1.1 v := by
  let hτne := ((vertexComplex X).isRelLowerSet_faces hτ).1
  apply div_nonneg
  · by_cases hv : v ∈ τ
    · simp only [if_pos hv]
      exact sub_nonneg.mpr (faceMin_le X hτne w.1.1 hv)
    · simp only [if_neg hv, sub_zero]
      exact canonicalSpace_nonneg X w.1 v
  · exact (radialDenom_pos X hτ w).le

lemma sum_radialRetractCoords {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces)
    (w : ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space)) :
    ∑ v, radialRetractCoords X τ
      ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1.1 v = 1 := by
  classical
  let hτne := ((vertexComplex X).isRelLowerSet_faces hτ).1
  let m := faceMin X τ hτne w.1.1
  let den := 1 - (τ.card : ℝ) * m
  have hden : den ≠ 0 := (radialDenom_pos X hτ w).ne'
  change (∑ v, (w.1.1 v - if v ∈ τ then m else 0) / den) = 1
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  have hite : (∑ v, if v ∈ τ then m else 0) = (τ.card : ℝ) * m := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [canonicalSpace_sum X w.1, hite]
  exact div_self hden

lemma exists_radialRetractCoords_eq_zero {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces)
    (w : ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space)) :
    ∃ v ∈ τ, radialRetractCoords X τ
      ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1.1 v = 0 := by
  let hτne := ((vertexComplex X).isRelLowerSet_faces hτ).1
  obtain ⟨v, hv, hmin⟩ := exists_faceMin_eq X hτne w.1.1
  refine ⟨v, hv, ?_⟩
  simp [radialRetractCoords, hv, hmin]

lemma radialRetractCoords_eq_self_of_faceMin_eq_zero {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτne : τ.Nonempty) (w : Vertex X → ℝ)
    (hw : faceMin X τ hτne w = 0) :
    radialRetractCoords X τ hτne w = w := by
  funext v
  simp [radialRetractCoords, hw]

lemma radialRetractCoords_mem_space {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces)
    (w : ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space)) :
    radialRetractCoords X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1.1 ∈
      (canonicalComplex X).space := by
  let hτne := ((vertexComplex X).isRelLowerSet_faces hτ).1
  obtain ⟨s, hs, hws⟩ := (canonicalComplex X).mem_space_iff.mp w.1.2
  obtain ⟨υ, hυ, rfl⟩ := mem_canonicalComplex_faces.mp hs
  have hwprops := (mem_convexHull_canonicalFace_iff X υ w.1.1).mp hws
  let m := faceMin X τ hτne w.1.1
  by_cases hm : m = 0
  · rw [radialRetractCoords_eq_self_of_faceMin_eq_zero X hτne w.1.1 hm]
    exact w.1.2
  · have hmpos : 0 < m := lt_of_le_of_ne
        (faceMin_nonneg X hτne hwprops.1) (Ne.symm hm)
    have hτυ : τ ⊆ υ := by
      intro v hvτ
      by_contra hvυ
      have hwv := hwprops.2.1 v hvυ
      have hmle := faceMin_le X hτne w.1.1 hvτ
      linarith
    apply (canonicalComplex X).convexHull_subset_space
      (mem_canonicalComplex_faces.mpr ⟨υ, hυ, rfl⟩)
    rw [mem_convexHull_canonicalFace_iff X υ]
    exact ⟨radialRetractCoords_nonneg X hτ w,
      fun v hvυ => by
        have hvτ : v ∉ τ := fun hv => hvυ (hτυ hv)
        simp [radialRetractCoords, hwprops.2.1 v hvυ, hvτ],
      sum_radialRetractCoords X hτ w⟩

lemma continuous_radialRetractCoords {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces) :
    Continuous fun w : ({faceBarycenterPoint X hτ}ᶜ :
        Set (canonicalComplex X).space) =>
      radialRetractCoords X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1.1 := by
  apply continuous_pi
  intro v
  apply Continuous.div
  · apply Continuous.sub
    · exact continuous_apply v |>.comp (continuous_subtype_val.comp continuous_subtype_val)
    · by_cases hv : v ∈ τ
      · simpa only [if_pos hv, Function.comp_def] using (continuous_faceMin X τ
          ((vertexComplex X).isRelLowerSet_faces hτ).1).comp
            (continuous_subtype_val.comp continuous_subtype_val)
      · simpa [hv] using (continuous_const : Continuous fun _ :
          ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) => (0 : ℝ))
  · exact continuous_const.sub
      (continuous_const.mul ((continuous_faceMin X τ
        ((vertexComplex X).isRelLowerSet_faces hτ).1).comp
          (continuous_subtype_val.comp continuous_subtype_val)))
  · intro w
    exact (radialDenom_pos X hτ w).ne'

lemma radialRetractCoords_mem_convexHull {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces)
    (w : ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space))
    {υ : Finset (Vertex X)}
    (hw : w.1.1 ∈ convexHull ℝ
      (υ.image (canonicalVertex X) : Set (Vertex X → ℝ))) :
    radialRetractCoords X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1.1 ∈
      convexHull ℝ (υ.image (canonicalVertex X) : Set (Vertex X → ℝ)) := by
  let hτne := ((vertexComplex X).isRelLowerSet_faces hτ).1
  have hwprops := (mem_convexHull_canonicalFace_iff X υ w.1.1).mp hw
  let m := faceMin X τ hτne w.1.1
  by_cases hm : m = 0
  · rw [radialRetractCoords_eq_self_of_faceMin_eq_zero X hτne w.1.1 hm]
    exact hw
  · have hmpos : 0 < m := lt_of_le_of_ne
        (faceMin_nonneg X hτne hwprops.1) (Ne.symm hm)
    have hτυ : τ ⊆ υ := by
      intro v hvτ
      by_contra hvυ
      have hwv := hwprops.2.1 v hvυ
      have hmle := faceMin_le X hτne w.1.1 hvτ
      linarith
    rw [mem_convexHull_canonicalFace_iff X υ]
    exact ⟨radialRetractCoords_nonneg X hτ w,
      fun v hvυ => by
        have hvτ : v ∉ τ := fun hv => hvυ (hτυ hv)
        simp [radialRetractCoords, hwprops.2.1 v hvυ, hvτ],
      sum_radialRetractCoords X hτ w⟩

/-- The radial projection as a continuous map from the punctured realization
to the canonical deletion. -/
noncomputable def radialRetract {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces) :
    ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) →
      canonicalDeletionSet X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 :=
  fun w =>
    ⟨⟨radialRetractCoords X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1.1,
      radialRetractCoords_mem_space X hτ w⟩,
    (mem_canonicalDeletionSet_iff X
      ((vertexComplex X).isRelLowerSet_faces hτ).1 _).mpr
        (exists_radialRetractCoords_eq_zero X hτ w)⟩

lemma continuous_radialRetract {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces) :
    Continuous (radialRetract X hτ) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact continuous_radialRetractCoords X hτ

/-- Inclusion of the deletion in the punctured realization. -/
def deletionInclusion {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces) :
    canonicalDeletionSet X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 →
      ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) :=
  fun w => ⟨w.1, by
    obtain ⟨v, hv, hwv⟩ :=
      (mem_canonicalDeletionSet_iff X
        ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1).mp w.2
    intro h
    have heq : w.1 = faceBarycenterPoint X hτ := Set.mem_singleton_iff.mp h
    have hcoord := congrArg
      (fun z : (canonicalComplex X).space => z.1 v) heq
    have hcard : (τ.card : ℝ) ≠ 0 := by
      exact_mod_cast ((vertexComplex X).isRelLowerSet_faces hτ).1.card_ne_zero
    rw [hwv] at hcoord
    change 0 = faceBarycenter X τ v at hcoord
    rw [faceBarycenter_apply_of_mem X hv] at hcoord
    exact (inv_ne_zero hcard) hcoord.symm⟩

lemma continuous_deletionInclusion {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces) :
    Continuous (deletionInclusion X hτ) := by
  exact Continuous.subtype_mk continuous_subtype_val _

lemma radialRetract_deletionInclusion {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces)
    (w : canonicalDeletionSet X τ ((vertexComplex X).isRelLowerSet_faces hτ).1) :
    radialRetract X hτ (deletionInclusion X hτ w) = w := by
  apply Subtype.ext
  apply Subtype.ext
  exact radialRetractCoords_eq_self_of_faceMin_eq_zero X
    ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1.1 w.2

/-- The straight-line homotopy from the radial projection back to the
identity, inside the simplex containing the input point. -/
def radialHomotopyCoords {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces)
    (t : Set.Icc (0 : ℝ) 1)
    (w : ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space)) :
    Vertex X → ℝ :=
  t.1 • w.1.1 + (1 - t.1) •
    radialRetractCoords X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 w.1.1

lemma radialHomotopyCoords_mem_space {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces)
    (t : Set.Icc (0 : ℝ) 1)
    (w : ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space)) :
    radialHomotopyCoords X hτ t w ∈ (canonicalComplex X).space := by
  obtain ⟨s, hs, hws⟩ := (canonicalComplex X).mem_space_iff.mp w.1.2
  obtain ⟨υ, hυ, rfl⟩ := mem_canonicalComplex_faces.mp hs
  have hr := radialRetractCoords_mem_convexHull X hτ w hws
  apply (canonicalComplex X).convexHull_subset_space
    (mem_canonicalComplex_faces.mpr ⟨υ, hυ, rfl⟩)
  exact (convex_convexHull ℝ _)
    hws hr t.2.1 (sub_nonneg.mpr t.2.2) (by ring)

lemma radialHomotopyCoords_ne_barycenter {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces)
    (t : Set.Icc (0 : ℝ) 1)
    (w : ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space)) :
    radialHomotopyCoords X hτ t w ≠ faceBarycenter X τ := by
  let hτne := ((vertexComplex X).isRelLowerSet_faces hτ).1
  let m := faceMin X τ hτne w.1.1
  obtain ⟨v, hv, hmin⟩ := exists_faceMin_eq X hτne w.1.1
  have hmnonneg : 0 ≤ m := faceMin_nonneg X hτne (canonicalSpace_nonneg X w.1)
  have hcardpos : 0 < (τ.card : ℝ) := by
    exact_mod_cast hτne.card_pos
  have hm_lt : m < (τ.card : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hcardpos).mpr
    have hden := radialDenom_pos X hτ w
    change 0 < 1 - (τ.card : ℝ) * m at hden
    nlinarith
  have htm : t.1 * m ≤ m := by
    simpa using mul_le_mul_of_nonneg_right t.2.2 hmnonneg
  have hrzero : radialRetractCoords X τ hτne w.1.1 v = 0 := by
    simp [radialRetractCoords, hv, hmin]
  intro heq
  have hcoord := congrFun heq v
  have hleft : radialHomotopyCoords X hτ t w v = t.1 * m := by
    change t.1 * w.1.1 v + (1 - t.1) *
      radialRetractCoords X τ hτne w.1.1 v = t.1 * m
    rw [hmin, hrzero]
    ring
  rw [hleft, faceBarycenter_apply_of_mem X hv] at hcoord
  linarith

/-- The radial homotopy as a point of the punctured realization. -/
def radialHomotopyPoint {d : ℕ} (X : FiniteSimplicialSphere d)
    {τ : Finset (Vertex X)} (hτ : τ ∈ (vertexComplex X).faces)
    (p : Set.Icc (0 : ℝ) 1 ×
      ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space)) :
    ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) :=
  ⟨⟨radialHomotopyCoords X hτ p.1 p.2,
      radialHomotopyCoords_mem_space X hτ p.1 p.2⟩,
    by
      intro h
      have heq := congrArg
        (fun z : (canonicalComplex X).space => z.1) (Set.mem_singleton_iff.mp h)
      exact radialHomotopyCoords_ne_barycenter X hτ p.1 p.2 heq⟩

lemma continuous_radialHomotopyPoint {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces) :
    Continuous (radialHomotopyPoint X hτ) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  let ht : Continuous fun p : Set.Icc (0 : ℝ) 1 ×
      ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) => p.1.1 :=
    continuous_subtype_val.comp continuous_fst
  let hwv : Continuous fun p : Set.Icc (0 : ℝ) 1 ×
      ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) => p.2.1.1 v :=
    (continuous_apply v).comp
      ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd)
  let hrv : Continuous fun p : Set.Icc (0 : ℝ) 1 ×
      ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) =>
        radialRetractCoords X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 p.2.1.1 v :=
    (continuous_apply v).comp ((continuous_radialRetractCoords X hτ).comp continuous_snd)
  change Continuous fun p : Set.Icc (0 : ℝ) 1 ×
      ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) =>
    p.1.1 * p.2.1.1 v + (1 - p.1.1) *
      radialRetractCoords X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 p.2.1.1 v
  exact (ht.mul hwv).add ((continuous_const.sub ht).mul hrv)

noncomputable def radialRetractContinuousMap {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces) :
    C(({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space),
      canonicalDeletionSet X τ ((vertexComplex X).isRelLowerSet_faces hτ).1) :=
  ⟨radialRetract X hτ, continuous_radialRetract X hτ⟩

noncomputable def deletionInclusionContinuousMap {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces) :
    C(canonicalDeletionSet X τ ((vertexComplex X).isRelLowerSet_faces hτ).1,
      ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space)) :=
  ⟨deletionInclusion X hτ, continuous_deletionInclusion X hτ⟩

noncomputable def radialHomotopy {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces) :
    ContinuousMap.Homotopy
      ((deletionInclusionContinuousMap X hτ).comp
        (radialRetractContinuousMap X hτ))
      (ContinuousMap.id _) where
  toFun := radialHomotopyPoint X hτ
  continuous_toFun := continuous_radialHomotopyPoint X hτ
  map_zero_left w := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp [radialHomotopyPoint, radialHomotopyCoords,
      deletionInclusionContinuousMap, radialRetractContinuousMap,
      deletionInclusion, radialRetract]
    simp
  map_one_left w := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp [radialHomotopyPoint, radialHomotopyCoords]
    simp

/-- The punctured realization and its face deletion are homotopy equivalent. -/
noncomputable def canonicalPuncturedHomotopyEquivDeletion {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces) :
    ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) ≃ₕ
      canonicalDeletionSet X τ ((vertexComplex X).isRelLowerSet_faces hτ).1 where
  toFun := radialRetractContinuousMap X hτ
  invFun := deletionInclusionContinuousMap X hτ
  left_inv := ⟨radialHomotopy X hτ⟩
  right_inv := by
    have heq : (radialRetractContinuousMap X hτ).comp
        (deletionInclusionContinuousMap X hτ) = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro w
      exact radialRetract_deletionInclusion X hτ w
    rw [heq]

lemma contractibleSpace_canonicalDeletionSet {d : ℕ}
    (X : FiniteSimplicialSphere d) {τ : Finset (Vertex X)}
    (hτ : τ ∈ (vertexComplex X).faces) :
    ContractibleSpace
      (canonicalDeletionSet X τ ((vertexComplex X).isRelLowerSet_faces hτ).1) := by
  letI : ContractibleSpace
      ({faceBarycenterPoint X hτ}ᶜ : Set (canonicalComplex X).space) :=
    contractibleSpace_canonical_punctured X hτ
  exact (canonicalPuncturedHomotopyEquivDeletion X hτ).symm.contractibleSpace

end

end Submission.Helpers.DehnSommerville
