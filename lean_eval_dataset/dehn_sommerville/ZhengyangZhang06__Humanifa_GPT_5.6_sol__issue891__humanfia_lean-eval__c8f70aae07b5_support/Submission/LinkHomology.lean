import Submission.Helpers

namespace Submission.Helpers.DehnSommerville

open LeanEval.Combinatorics.DehnSommerville
open CategoryTheory Limits Simplicial Opposite

noncomputable section

lemma finite_vertices {d : ℕ} (X : FiniteSimplicialSphere d) : X.K.vertices.Finite := by
  rw [Geometry.SimplicialComplex.vertices_eq]
  exact X.finite_faces.biUnion fun s _ => s.finite_toSet

abbrev Vertex {d : ℕ} (X : FiniteSimplicialSphere d) := X.K.vertices

noncomputable instance vertexFintype {d : ℕ} (X : FiniteSimplicialSphere d) :
    Fintype (Vertex X) :=
  (finite_vertices X).fintype

noncomputable instance vertexLinearOrder {d : ℕ} (X : FiniteSimplicialSphere d) :
    LinearOrder (Vertex X) :=
  LinearOrder.lift' (Fintype.equivFin (Vertex X)) (Fintype.equivFin (Vertex X)).injective

lemma linkFaces_down_closed {d : ℕ} (X : FiniteSimplicialSphere d)
    {σ τ υ : Finset (EuclideanSpace ℝ (Fin d))}
    (hτ : τ ∈ linkFaces X σ) (hυτ : υ ⊆ τ) : υ ∈ linkFaces X σ := by
  refine ⟨augmentedFaces_down_closed X hτ.1 hυτ, hτ.2.1.mono_right hυτ, ?_⟩
  exact augmentedFaces_down_closed X hτ.2.2 (Finset.union_subset_union_right hυτ)

def vertexEmbedding {d : ℕ} (X : FiniteSimplicialSphere d) :
    Vertex X ↪ EuclideanSpace ℝ (Fin d) :=
  ⟨Subtype.val, Subtype.val_injective⟩

def vertexLinkFaces {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) : Set (Finset (Vertex X)) :=
  {τ | τ.map (vertexEmbedding X) ∈ linkFaces X σ}

lemma vertexLinkFaces_down_closed {d : ℕ} (X : FiniteSimplicialSphere d)
    {σ : Finset (EuclideanSpace ℝ (Fin d))} {τ υ : Finset (Vertex X)}
    (hτ : τ ∈ vertexLinkFaces X σ) (hυτ : υ ⊆ τ) : υ ∈ vertexLinkFaces X σ := by
  exact linkFaces_down_closed X hτ (Finset.map_subset_map.2 hυτ)

def simplexVertexFinset {d : ℕ} (X : FiniteSimplicialSphere d)
    {n : SimplexCategoryᵒᵖ} (s : (nerve (Vertex X)).obj n) : Finset (Vertex X) :=
  Finset.univ.image s.obj

lemma simplexVertexFinset_map_subset {d : ℕ} (X : FiniteSimplicialSphere d)
    {U V : SimplexCategoryᵒᵖ} (f : U ⟶ V) (s : (nerve (Vertex X)).obj U) :
    simplexVertexFinset X ((nerve (Vertex X)).map f s) ⊆ simplexVertexFinset X s := by
  intro x hx
  simp only [simplexVertexFinset, Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
  rcases hx with ⟨i, rfl⟩
  exact ⟨(SimplexCategory.toCat.map f.unop).toFunctor.obj i, rfl⟩

def linkSSet {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) : (nerve (Vertex X)).Subcomplex where
  obj _ := {s | simplexVertexFinset X s ∈ vertexLinkFaces X σ}
  map f _s hs := vertexLinkFaces_down_closed X hs (simplexVertexFinset_map_subset X f _s)

def vertexLinkFacesOfCard {d n : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) : Set (Finset (Vertex X)) :=
  {τ | τ ∈ vertexLinkFaces X σ ∧ τ.card = n}

lemma simplexVertexFinset_card_of_nonDegenerate {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (s : (linkSSet X σ : SSet).nonDegenerate n) :
    (simplexVertexFinset X s.val.val).card = n + 1 := by
  let t : (nerve (Vertex X)) _⦋n⦌ := s.val.val
  change (Finset.univ.image t.obj).card = n + 1
  rw [Finset.card_image_of_injective]
  · simp
  · rw [← PartialOrder.mem_nerve_nonDegenerate_iff_injective]
    change s.val.val ∈ (nerve (Vertex X)).nonDegenerate n
    exact (SSet.Subcomplex.mem_nonDegenerate_iff (linkSSet X σ) s.val).1 s.property

def nonDegenerateToFace {d n : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (s : (linkSSet X σ : SSet).nonDegenerate n) :
    vertexLinkFacesOfCard (n := n + 1) X σ :=
  ⟨simplexVertexFinset X s.val.val, s.val.property,
    simplexVertexFinset_card_of_nonDegenerate X σ s⟩

def faceToNerveSimplex {d n : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (τ : vertexLinkFacesOfCard (n := n + 1) X σ) :
    (nerve (Vertex X)) _⦋n⦌ :=
  (τ.val.orderEmbOfFin τ.property.2).monotone.functor

lemma simplexVertexFinset_faceToNerveSimplex {d n : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (τ : vertexLinkFacesOfCard (n := n + 1) X σ) :
    simplexVertexFinset X (faceToNerveSimplex X σ τ) = τ.val := by
  ext x
  simp only [simplexVertexFinset, faceToNerveSimplex, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.orderEmbOfFin_mem τ.val τ.property.2 i
  · intro hx
    let y : τ.val := ⟨x, hx⟩
    refine ⟨(τ.val.orderIsoOfFin τ.property.2).symm y, ?_⟩
    exact congrArg Subtype.val ((τ.val.orderIsoOfFin τ.property.2).apply_symm_apply y)

def faceToNonDegenerate {d n : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (τ : vertexLinkFacesOfCard (n := n + 1) X σ) :
    (linkSSet X σ : SSet).nonDegenerate n := by
  let s := faceToNerveSimplex X σ τ
  have hs : s ∈ (linkSSet X σ).obj (op ⦋n⦌) := by
    change simplexVertexFinset X s ∈ vertexLinkFaces X σ
    rw [simplexVertexFinset_faceToNerveSimplex X σ τ]
    exact τ.property.1
  let s' : (linkSSet X σ : SSet) _⦋n⦌ := ⟨s, hs⟩
  refine ⟨s', (SSet.Subcomplex.mem_nonDegenerate_iff (linkSSet X σ) s').2 ?_⟩
  apply (PartialOrder.mem_nerve_nonDegenerate_iff_injective _).2
  exact (τ.val.orderEmbOfFin τ.property.2).injective

lemma nonDegenerateToFace_faceToNonDegenerate {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (τ : vertexLinkFacesOfCard (n := n + 1) X σ) :
    nonDegenerateToFace X σ (faceToNonDegenerate X σ τ) = τ := by
  apply Subtype.ext
  exact simplexVertexFinset_faceToNerveSimplex X σ τ

lemma faceToNonDegenerate_nonDegenerateToFace {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (s : (linkSSet X σ : SSet).nonDegenerate n) :
    faceToNonDegenerate X σ (nonDegenerateToFace X σ s) = s := by
  apply Subtype.ext
  apply Subtype.ext
  apply CategoryTheory.nerve.ext_of_isThin
  have hsnd : Function.Injective s.val.val.obj := by
    rw [← PartialOrder.mem_nerve_nonDegenerate_iff_injective]
    exact (SSet.Subcomplex.mem_nonDegenerate_iff (linkSSet X σ) s.val).1 s.property
  have hsmono : StrictMono s.val.val.obj :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val.val).1
      ((SSet.Subcomplex.mem_nonDegenerate_iff (linkSSet X σ) s.val).1 s.property)
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    change s.val.val.obj i ∈ simplexVertexFinset X s.val.val
    simp [simplexVertexFinset]
  · simpa using hsmono

noncomputable def nonDegenerateEquivFacesOfCard {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    (linkSSet X σ : SSet).nonDegenerate n ≃
      vertexLinkFacesOfCard (n := n + 1) X σ where
  toFun := nonDegenerateToFace X σ
  invFun := faceToNonDegenerate X σ
  left_inv := faceToNonDegenerate_nonDegenerateToFace X σ
  right_inv := nonDegenerateToFace_faceToNonDegenerate X σ

lemma mem_vertices_of_mem_linkFaces {d : ℕ} (X : FiniteSimplicialSphere d)
    {σ τ : Finset (EuclideanSpace ℝ (Fin d))} (hτ : τ ∈ linkFaces X σ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ τ) : x ∈ X.K.vertices := by
  have hτne : τ ≠ ∅ := fun h => by simp [h] at hx
  have hτface : τ ∈ X.K.faces := (mem_augmentedFaces.mp hτ.1).resolve_left hτne
  exact X.K.down_closed hτface (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)

def liftLinkFace {d : ℕ} (X : FiniteSimplicialSphere d)
    {σ : Finset (EuclideanSpace ℝ (Fin d))}
    (τ : Finset (EuclideanSpace ℝ (Fin d))) (hτ : τ ∈ linkFaces X σ) :
    Finset (Vertex X) :=
  τ.attach.map
    ⟨fun x => ⟨x.val, mem_vertices_of_mem_linkFaces X hτ x.property⟩,
      fun _ _ h => by
        apply Subtype.ext
        exact congrArg (fun z : Vertex X => (z : EuclideanSpace ℝ (Fin d))) h⟩

lemma map_liftLinkFace {d : ℕ} (X : FiniteSimplicialSphere d)
    {σ : Finset (EuclideanSpace ℝ (Fin d))}
    (τ : Finset (EuclideanSpace ℝ (Fin d))) (hτ : τ ∈ linkFaces X σ) :
    (liftLinkFace X τ hτ).map (vertexEmbedding X) = τ := by
  ext x
  simp [liftLinkFace, vertexEmbedding]
  exact fun hx => mem_vertices_of_mem_linkFaces X hτ hx

def vertexLinkFacesToLinkFaces {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) : vertexLinkFaces X σ → linkFaces X σ :=
  fun τ => ⟨τ.val.map (vertexEmbedding X), τ.property⟩

lemma vertexLinkFacesToLinkFaces_bijective {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Function.Bijective (vertexLinkFacesToLinkFaces X σ) := by
  constructor
  · intro τ υ h
    apply Subtype.ext
    exact Finset.map_injective (vertexEmbedding X) (congrArg Subtype.val h)
  · intro τ
    let υ : Finset (Vertex X) := liftLinkFace X τ.val τ.property
    have hυ : υ ∈ vertexLinkFaces X σ := by
      change υ.map (vertexEmbedding X) ∈ linkFaces X σ
      rw [map_liftLinkFace X τ.val τ.property]
      exact τ.property
    refine ⟨⟨υ, hυ⟩, ?_⟩
    apply Subtype.ext
    exact map_liftLinkFace X τ.val τ.property

noncomputable def vertexLinkFacesEquivLinkFaces {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    vertexLinkFaces X σ ≃ linkFaces X σ :=
  Equiv.ofBijective (vertexLinkFacesToLinkFaces X σ)
    (vertexLinkFacesToLinkFaces_bijective X σ)

def linkFacesOfCard {d n : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Set (Finset (EuclideanSpace ℝ (Fin d))) :=
  {τ | τ ∈ linkFaces X σ ∧ τ.card = n}

def vertexLinkFacesOfCardToLinkFacesOfCard {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    vertexLinkFacesOfCard (n := n) X σ → linkFacesOfCard (n := n) X σ :=
  fun τ => ⟨τ.val.map (vertexEmbedding X), τ.property.1, by simpa using τ.property.2⟩

def linkFacesOfCardToVertexLinkFacesOfCard {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    linkFacesOfCard (n := n) X σ → vertexLinkFacesOfCard (n := n) X σ :=
  fun τ => ⟨liftLinkFace X τ.val τ.property.1, by
    constructor
    · change (liftLinkFace X τ.val τ.property.1).map (vertexEmbedding X) ∈ linkFaces X σ
      rw [map_liftLinkFace X τ.val τ.property.1]
      exact τ.property.1
    · rw [← Finset.card_map (vertexEmbedding X), map_liftLinkFace X τ.val τ.property.1]
      exact τ.property.2⟩

noncomputable def vertexLinkFacesOfCardEquivLinkFacesOfCard {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    vertexLinkFacesOfCard (n := n) X σ ≃ linkFacesOfCard (n := n) X σ where
  toFun := vertexLinkFacesOfCardToLinkFacesOfCard X σ
  invFun := linkFacesOfCardToVertexLinkFacesOfCard X σ
  left_inv τ := by
    apply Subtype.ext
    apply Finset.map_injective (vertexEmbedding X)
    exact map_liftLinkFace X (τ.val.map (vertexEmbedding X)) τ.property.1
  right_inv τ := by
    apply Subtype.ext
    exact map_liftLinkFace X τ.val τ.property.1

noncomputable def nonDegenerateEquivLinkFacesOfCard {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    (linkSSet X σ : SSet).nonDegenerate n ≃ linkFacesOfCard (n := n + 1) X σ :=
  (nonDegenerateEquivFacesOfCard X σ).trans
    (vertexLinkFacesOfCardEquivLinkFacesOfCard X σ)

lemma natCard_nonDegenerate_linkSSet {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Nat.card ((linkSSet X σ : SSet).nonDegenerate n) =
      (linkFacesOfCard (n := n + 1) X σ).ncard := by
  rw [Nat.card_congr (nonDegenerateEquivLinkFacesOfCard X σ)]
  exact Nat.card_coe_set_eq _

lemma finite_linkFacesOfCard {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    (linkFacesOfCard (n := n) X σ).Finite :=
  (finite_linkFaces X σ).subset fun _ h => h.1

instance finite_nonDegenerate_linkSSet {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Finite ((linkSSet X σ : SSet).nonDegenerate n) := by
  letI : Fintype (linkFacesOfCard (n := n + 1) X σ) :=
    (finite_linkFacesOfCard X σ).fintype
  exact Finite.of_equiv _ (nonDegenerateEquivLinkFacesOfCard X σ).symm

instance linkSSet_hasDimensionLT {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    (linkSSet X σ : SSet).HasDimensionLT (d + 1) where
  degenerate_eq_top n hn := by
    ext s
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    rw [SSet.mem_degenerate_iff_notMem_nonDegenerate]
    intro hs
    let τ := nonDegenerateEquivLinkFacesOfCard X σ ⟨s, hs⟩
    have hτface : τ.val ∈ X.K.faces := by
      have hτne : τ.val ≠ ∅ := by
        intro h
        have := τ.property.2
        rw [h, Finset.card_empty] at this
        omega
      exact (mem_augmentedFaces.mp τ.property.1.1).resolve_left hτne
    have hcard := face_card_le_dim_succ X hτface
    have hτcard : τ.val.card = n + 1 := τ.property.2
    omega

instance finite_linkSSet {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    SSet.Finite (linkSSet X σ : SSet) :=
  SSet.finite_of_hasDimensionLT _ (d + 1) fun _ _ => inferInstance

lemma card_le_dim_succ_of_mem_linkFaces {d : ℕ}
    (X : FiniteSimplicialSphere d)
    {σ τ : Finset (EuclideanSpace ℝ (Fin d))} (hτ : τ ∈ linkFaces X σ) :
    τ.card ≤ d + 1 := by
  by_cases h : τ = ∅
  · simp [h]
  · exact face_card_le_dim_succ X ((mem_augmentedFaces.mp hτ.1).resolve_left h)

lemma card_filter_linkFaceFinset {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    ((linkFaceFinset X σ).filter fun τ => τ.card = n).card =
      (linkFacesOfCard (n := n) X σ).ncard := by
  rw [Set.ncard_eq_toFinset_card (linkFacesOfCard (n := n) X σ)
    (finite_linkFacesOfCard X σ)]
  congr 1
  ext τ
  simp [linkFacesOfCard, linkFaceFinset]

lemma sum_linkFaces_grouped_by_card {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    linkEulerSum X σ =
      ∑ n ∈ Finset.range (d + 2),
        (-1 : ℤ) ^ n * (linkFacesOfCard (n := n) X σ).ncard := by
  rw [linkEulerSum]
  change (∑ τ ∈ linkFaceFinset X σ, (-1 : ℤ) ^ τ.card) = _
  have hmaps : ∀ τ ∈ linkFaceFinset X σ, τ.card ∈ Finset.range (d + 2) := by
    intro τ hτ
    rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr
      (card_le_dim_succ_of_mem_linkFaces X (mem_linkFaceFinset.mp hτ))
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := Finset.range (d + 2)) (g := Finset.card) hmaps]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.sum_congr rfl fun τ hτ => by
    rw [(Finset.mem_filter.mp hτ).2]]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul]
  rw [card_filter_linkFaceFinset X σ]
  ring

lemma linkFacesOfCard_zero {d : ℕ} (X : FiniteSimplicialSphere d)
    {σ : Finset (EuclideanSpace ℝ (Fin d))} (hσ : σ ∈ augmentedFaces X) :
    linkFacesOfCard (n := 0) X σ = {∅} := by
  ext τ
  constructor
  · intro hτ
    rw [Set.mem_singleton_iff]
    exact Finset.card_eq_zero.mp hτ.2
  · intro hτ
    rw [Set.mem_singleton_iff] at hτ
    subst τ
    exact ⟨⟨by simp [augmentedFaces], by simp, by simpa using hσ⟩, by simp⟩

lemma linkEulerSum_eq_normalizedCounts {d : ℕ}
    (X : FiniteSimplicialSphere d) {σ : Finset (EuclideanSpace ℝ (Fin d))}
    (hσ : σ ∈ augmentedFaces X) :
    linkEulerSum X σ = 1 -
      ∑ n ∈ Finset.range (d + 1),
        (-1 : ℤ) ^ n * Nat.card ((linkSSet X σ : SSet).nonDegenerate n) := by
  rw [sum_linkFaces_grouped_by_card X σ, Finset.sum_range_succ']
  have hzero : (linkFacesOfCard (n := 0) X σ).ncard = 1 := by
    rw [linkFacesOfCard_zero X hσ]
    simp
  rw [hzero]
  norm_num
  calc
    (∑ n ∈ Finset.range (d + 1),
        (-1 : ℤ) ^ (n + 1) * (linkFacesOfCard (n := n + 1) X σ).ncard) + 1 =
        (∑ n ∈ Finset.range (d + 1),
          -((-1 : ℤ) ^ n * Nat.card ((linkSSet X σ : SSet).nonDegenerate n))) + 1 := by
      apply congrArg (fun z : ℤ => z + 1)
      apply Finset.sum_congr rfl
      intro n _hn
      rw [natCard_nonDegenerate_linkSSet X σ]
      rw [pow_succ]
      ring
    _ = 1 - ∑ n ∈ Finset.range (d + 1),
        (-1 : ℤ) ^ n * Nat.card ((linkSSet X σ : SSet).nonDegenerate n) := by
      rw [Finset.sum_neg_distrib]
      ring

abbrev rationalModule : ModuleCat ℚ := ModuleCat.of ℚ ℚ

noncomputable def normalizedChainIsoFinsupp {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    ((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X n ≅
      ModuleCat.of ℚ (((linkSSet X σ : SSet).nonDegenerate n) →₀ ℚ) :=
  ((linkSSet X σ : SSet).isColimitCofanNormalizedChainComplex rationalModule n)
    |>.coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℚ ℚ
        ((linkSSet X σ : SSet).nonDegenerate n))

noncomputable def normalizedChainLinearEquivFinsupp {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    ((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X n ≃ₗ[ℚ]
      (((linkSSet X σ : SSet).nonDegenerate n) →₀ ℚ) :=
  LinearEquiv.ofBijective (normalizedChainIsoFinsupp X σ).hom.hom
    (ConcreteCategory.bijective_of_isIso (normalizedChainIsoFinsupp X σ).hom)

noncomputable instance finiteDimensional_normalizedChainComplex {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    FiniteDimensional ℚ
      (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X n) := by
  letI : Fintype ((linkSSet X σ : SSet).nonDegenerate n) := Fintype.ofFinite _
  exact FiniteDimensional.of_injective
    (normalizedChainLinearEquivFinsupp X σ).toLinearMap
    (normalizedChainLinearEquivFinsupp X σ).injective

lemma finrank_normalizedChainComplex {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Module.finrank ℚ
      (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X n) =
      Nat.card ((linkSSet X σ : SSet).nonDegenerate n) := by
  letI : Fintype ((linkSSet X σ : SSet).nonDegenerate n) := Fintype.ofFinite _
  rw [(normalizedChainLinearEquivFinsupp X σ).finrank_eq]
  rw [Module.finrank_finsupp_self]
  exact Fintype.card_eq_nat_card

lemma normalizedChain_finrankSupport_subset {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    GradedObject.finrankSupport
      (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X) ⊆
        (Finset.range (d + 1) : Set ℕ) := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range] at hn
  have hzero := (linkSSet X σ : SSet).isZero_normalizedChainComplex_X_of_hasDimensionLT
    rationalModule n (d + 1) (Nat.le_of_not_gt hn)
  letI : Subsingleton
      (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X n) :=
    ModuleCat.subsingleton_of_isZero hzero
  exact Module.finrank_zero_of_subsingleton

lemma downNat_eulerCharSign (n : ℕ) :
    ((ComplexShape.down ℕ).χ n : ℤ) = (-1 : ℤ) ^ n := by
  change (↑((-1 : ℤˣ) ^ n) : ℤ) = (-1 : ℤ) ^ n
  exact Units.val_pow_eq_pow_val (-1 : ℤˣ) n

noncomputable def moduleIsoLinearEquiv {R : Type*} [Ring R]
    {M N : ModuleCat R} (e : M ≅ N) : M ≃ₗ[R] N :=
  LinearEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)

lemma finrank_shortComplex_middle {S : ShortComplex (ModuleCat ℚ)} [S.HasHomology]
    [FiniteDimensional ℚ S.X₁] [FiniteDimensional ℚ S.X₂] :
    Module.finrank ℚ S.X₂ =
      Module.finrank ℚ S.homology +
        Module.finrank ℚ (LinearMap.range S.f.hom) +
          Module.finrank ℚ (LinearMap.range S.g.hom) := by
  have hquot := (LinearMap.range S.moduleCatToCycles).finrank_quotient_add_finrank
  have hhom := (moduleIsoLinearEquiv S.moduleCatHomologyIso).finrank_eq
  have hto := S.moduleCatToCycles.finrank_range_add_finrank_ker
  have hf := S.f.hom.finrank_range_add_finrank_ker
  have hker : LinearMap.ker S.moduleCatToCycles = LinearMap.ker S.f.hom := by
    exact LinearMap.ker_codRestrict _ _ _
  have hkerRank : Module.finrank ℚ (LinearMap.ker S.moduleCatToCycles) =
      Module.finrank ℚ (LinearMap.ker S.f.hom) :=
    congrArg (fun W : Submodule ℚ S.X₁ => Module.finrank ℚ W) hker
  have hrange : Module.finrank ℚ (LinearMap.range S.moduleCatToCycles) =
      Module.finrank ℚ (LinearMap.range S.f.hom) := by
    omega
  have hquot' : Module.finrank ℚ S.moduleCatLeftHomologyData.H +
      Module.finrank ℚ (LinearMap.range S.moduleCatToCycles) =
        Module.finrank ℚ (LinearMap.ker S.g.hom) := by
    exact hquot
  have hg := S.g.hom.finrank_range_add_finrank_ker
  calc
    Module.finrank ℚ S.X₂ =
        Module.finrank ℚ (LinearMap.range S.g.hom) +
          Module.finrank ℚ (LinearMap.ker S.g.hom) := hg.symm
    _ = Module.finrank ℚ (LinearMap.range S.g.hom) +
        (Module.finrank ℚ S.moduleCatLeftHomologyData.H +
          Module.finrank ℚ (LinearMap.range S.f.hom)) := by
      rw [← hrange]
      rw [hquot']
    _ = Module.finrank ℚ S.homology +
        Module.finrank ℚ (LinearMap.range S.f.hom) +
          Module.finrank ℚ (LinearMap.range S.g.hom) := by
      rw [hhom]
      omega

def linkBoundaryRank {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) (n : ℕ) : ℕ :=
  Module.finrank ℚ (LinearMap.range
    (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).d (n + 1) n).hom)

lemma finrank_linkChain_raw {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Module.finrank ℚ
        (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X n) =
      Module.finrank ℚ
          (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).homology n) +
        Module.finrank ℚ (LinearMap.range
          (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).d
            ((ComplexShape.down ℕ).prev n) n).hom) +
        Module.finrank ℚ (LinearMap.range
          (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).d
            n ((ComplexShape.down ℕ).next n)).hom) := by
  letI : FiniteDimensional ℚ
      (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).sc n).X₁ := by
    rw [HomologicalComplex.shortComplexFunctor_obj_X₁, ChainComplex.prev]
    infer_instance
  letI : FiniteDimensional ℚ
      (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).sc n).X₂ := by
    rw [HomologicalComplex.shortComplexFunctor_obj_X₂]
    infer_instance
  have h := finrank_shortComplex_middle
    (S := ((linkSSet X σ : SSet).normalizedChainComplex rationalModule).sc n)
  dsimp only [HomologicalComplex.homology, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor] at h ⊢
  convert h using 1
  · exact congrArg (fun M : ModuleCat ℚ => Module.finrank ℚ M)
      (HomologicalComplex.shortComplexFunctor'_obj_X₂
        (ModuleCat ℚ) (ComplexShape.down ℕ) _ _ _ _).symm
  · let C := (linkSSet X σ : SSet).normalizedChainComplex rationalModule
    let T := (HomologicalComplex.shortComplexFunctor'
      (ModuleCat ℚ) (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev n)
        n ((ComplexShape.down ℕ).next n)).obj C
    have hfcat : T.f = C.d ((ComplexShape.down ℕ).prev n) n := by
      simp [T, C]
    have hgcat : T.g = C.d n ((ComplexShape.down ℕ).next n) := by
      simp [T, C]
    have hf := congrArg
      (fun f : T.X₁ ⟶ T.X₂ => Module.finrank ℚ (LinearMap.range f.hom)) hfcat
    have hg := congrArg
      (fun f : T.X₂ ⟶ T.X₃ => Module.finrank ℚ (LinearMap.range f.hom)) hgcat
    dsimp only [T, C] at hf hg
    congr 1

lemma finrank_linkChain_zero {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Module.finrank ℚ
        (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X 0) =
      Module.finrank ℚ
          (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).homology 0) +
        linkBoundaryRank X σ 0 := by
  have h := finrank_linkChain_raw (n := 0) X σ
  rw [ChainComplex.prev, ChainComplex.next_nat_zero] at h
  have hd00 :
      ((linkSSet X σ : SSet).normalizedChainComplex rationalModule).d 0 0 = 0 :=
    HomologicalComplex.shape _ _ _ (by simp)
  have hd00' :
      (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).d 0 0).hom = 0 :=
    congrArg ModuleCat.Hom.hom hd00
  rw [hd00', LinearMap.range_zero, finrank_bot, add_zero] at h
  simpa only [linkBoundaryRank] using h

lemma finrank_linkChain_succ {d n : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Module.finrank ℚ
        (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X (n + 1)) =
      Module.finrank ℚ
          (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).homology (n + 1)) +
        linkBoundaryRank X σ (n + 1) + linkBoundaryRank X σ n := by
  have h := finrank_linkChain_raw (n := n + 1) X σ
  rw [ChainComplex.prev, ChainComplex.next_nat_succ] at h
  simpa only [linkBoundaryRank, Nat.add_assoc] using h

lemma linkBoundaryRank_top {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    linkBoundaryRank X σ d = 0 := by
  have hzero := (linkSSet X σ : SSet).isZero_normalizedChainComplex_X_of_hasDimensionLT
    rationalModule (d + 1) (d + 1)
  have hd :
      ((linkSSet X σ : SSet).normalizedChainComplex rationalModule).d (d + 1) d = 0 :=
    hzero.eq_zero_of_src _
  have hd' :
      (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).d (d + 1) d).hom = 0 :=
    congrArg ModuleCat.Hom.hom hd
  rw [linkBoundaryRank, hd', LinearMap.range_zero, finrank_bot]

lemma sum_linkBoundaryRanks_eq_zero {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    (∑ n ∈ Finset.range d, (-1 : ℤ) ^ (n + 1) *
      (linkBoundaryRank X σ (n + 1) + linkBoundaryRank X σ n)) +
        linkBoundaryRank X σ 0 = 0 := by
  have htop :
      (∑ n ∈ Finset.range (d + 1),
        (-1 : ℤ) ^ n * linkBoundaryRank X σ n) =
      ∑ n ∈ Finset.range d, (-1 : ℤ) ^ n * linkBoundaryRank X σ n := by
    rw [Finset.sum_range_succ, linkBoundaryRank_top X σ]
    simp
  calc
    (∑ n ∈ Finset.range d, (-1 : ℤ) ^ (n + 1) *
        (linkBoundaryRank X σ (n + 1) + linkBoundaryRank X σ n)) +
        linkBoundaryRank X σ 0 =
      ((∑ n ∈ Finset.range d, (-1 : ℤ) ^ (n + 1) *
        linkBoundaryRank X σ (n + 1)) + linkBoundaryRank X σ 0) +
      ∑ n ∈ Finset.range d, (-1 : ℤ) ^ (n + 1) *
        linkBoundaryRank X σ n := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      ring
    _ = (∑ n ∈ Finset.range (d + 1),
        (-1 : ℤ) ^ n * linkBoundaryRank X σ n) +
      ∑ n ∈ Finset.range d, (-1 : ℤ) ^ (n + 1) *
        linkBoundaryRank X σ n := by
      rw [Finset.sum_range_succ']
      norm_num
    _ = (∑ n ∈ Finset.range (d + 1),
        (-1 : ℤ) ^ n * linkBoundaryRank X σ n) +
      ∑ n ∈ Finset.range d,
        -((-1 : ℤ) ^ n * linkBoundaryRank X σ n) := by
      apply congrArg (fun z : ℤ =>
        (∑ n ∈ Finset.range (d + 1),
          (-1 : ℤ) ^ n * linkBoundaryRank X σ n) + z)
      apply Finset.sum_congr rfl
      intro n _hn
      rw [pow_succ]
      ring
    _ = 0 := by
      rw [Finset.sum_neg_distrib, htop]
      ring

lemma chainEulerSum_eq_homologySum {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    (∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n *
      Module.finrank ℚ
        (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X n)) =
    ∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n *
      Module.finrank ℚ
        (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).homology n) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  rw [finrank_linkChain_zero X σ]
  push_cast
  norm_num
  rw [← sub_eq_zero]
  calc
    ((∑ n ∈ Finset.range d, (-1 : ℤ) ^ (n + 1) *
        Module.finrank ℚ
          (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).X (n + 1))) +
        (Module.finrank ℚ
          (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).homology 0) +
            linkBoundaryRank X σ 0)) -
      ((∑ n ∈ Finset.range d, (-1 : ℤ) ^ (n + 1) *
        Module.finrank ℚ
          (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).homology (n + 1))) +
        Module.finrank ℚ
          (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).homology 0)) =
      (∑ n ∈ Finset.range d, (-1 : ℤ) ^ (n + 1) *
        (linkBoundaryRank X σ (n + 1) + linkBoundaryRank X σ n)) +
          linkBoundaryRank X σ 0 := by
      simp_rw [finrank_linkChain_succ X σ]
      push_cast
      simp_rw [mul_add, Finset.sum_add_distrib]
      ring
    _ = 0 := sum_linkBoundaryRanks_eq_zero X σ

lemma normalizedHomology_finrankSupport_subset {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    GradedObject.finrankSupport
      (fun n => ((linkSSet X σ : SSet).normalizedChainComplex rationalModule).homology n) ⊆
        (Finset.range (d + 1) : Set ℕ) := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range] at hn
  have hX := (linkSSet X σ : SSet).isZero_normalizedChainComplex_X_of_hasDimensionLT
    rationalModule n (d + 1) (Nat.le_of_not_gt hn)
  have hH := (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology
  letI : Subsingleton
      (((linkSSet X σ : SSet).normalizedChainComplex rationalModule).homology n) :=
    ModuleCat.subsingleton_of_isZero hH
  exact Module.finrank_zero_of_subsingleton

lemma linkChain_eulerChar_eq_homologyEulerChar {d : ℕ}
    (X : FiniteSimplicialSphere d) (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    HomologicalComplex.eulerChar
        ((linkSSet X σ : SSet).normalizedChainComplex rationalModule) =
      HomologicalComplex.homologyEulerChar
        ((linkSSet X σ : SSet).normalizedChainComplex rationalModule) := by
  rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset
    _ (Finset.range (d + 1)) (normalizedChain_finrankSupport_subset X σ)]
  rw [HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
    _ (Finset.range (d + 1)) (normalizedHomology_finrankSupport_subset X σ)]
  simp_rw [downNat_eulerCharSign]
  exact chainEulerSum_eq_homologySum X σ

lemma linkEulerSum_eq_one_sub_chainEulerChar {d : ℕ}
    (X : FiniteSimplicialSphere d) {σ : Finset (EuclideanSpace ℝ (Fin d))}
    (hσ : σ ∈ augmentedFaces X) :
    linkEulerSum X σ = 1 -
      HomologicalComplex.eulerChar
        ((linkSSet X σ : SSet).normalizedChainComplex rationalModule) := by
  rw [linkEulerSum_eq_normalizedCounts X hσ]
  rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset
    _ (Finset.range (d + 1)) (normalizedChain_finrankSupport_subset X σ)]
  apply congrArg (fun z : ℤ => 1 - z)
  apply Finset.sum_congr rfl
  intro n _hn
  rw [finrank_normalizedChainComplex X σ]
  rw [downNat_eulerCharSign]

lemma linkEulerSum_eq_one_sub_homologyEulerChar {d : ℕ}
    (X : FiniteSimplicialSphere d) {σ : Finset (EuclideanSpace ℝ (Fin d))}
    (hσ : σ ∈ augmentedFaces X) :
    linkEulerSum X σ = 1 -
      HomologicalComplex.homologyEulerChar
        ((linkSSet X σ : SSet).normalizedChainComplex rationalModule) := by
  rw [linkEulerSum_eq_one_sub_chainEulerChar X hσ,
    linkChain_eulerChar_eq_homologyEulerChar X σ]

noncomputable def boundaryNonDegenerateEquiv {q n : ℕ} (h : n < q) :
    (SSet.boundary q : SSet).nonDegenerate n ≃ (Δ[q] : SSet).nonDegenerate n where
  toFun s := ⟨s.val.val,
    (SSet.Subcomplex.mem_nonDegenerate_iff (SSet.boundary q) s.val).1 s.property⟩
  invFun s := by
    let x : (SSet.boundary q : SSet) _⦋n⦌ := ⟨s.val, by
      rw [SSet.boundary_obj_eq_univ n q h]
      simp⟩
    exact ⟨x, (SSet.Subcomplex.mem_nonDegenerate_iff (SSet.boundary q) x).2 s.property⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl

lemma natCard_boundary_nonDegenerate {q n : ℕ} (h : n < q) :
    Nat.card ((SSet.boundary q : SSet).nonDegenerate n) =
      (q + 1).choose (n + 1) := by
  rw [Nat.card_congr (boundaryNonDegenerateEquiv h)]
  rw [Nat.card_congr SSet.stdSimplex.nonDegenerateEquiv']
  change Nat.card (Set.powersetCard (Fin (q + 1)) (n + 1)) = _
  rw [Set.powersetCard.card]
  simp

noncomputable def sSetNormalizedChainIsoFinsupp (Y : SSet) (n : ℕ) :
    (Y.normalizedChainComplex rationalModule).X n ≅
      ModuleCat.of ℚ (Y.nonDegenerate n →₀ ℚ) :=
  (Y.isColimitCofanNormalizedChainComplex rationalModule n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℚ ℚ (Y.nonDegenerate n))

noncomputable def sSetNormalizedChainLinearEquivFinsupp (Y : SSet) (n : ℕ) :
    (Y.normalizedChainComplex rationalModule).X n ≃ₗ[ℚ]
      (Y.nonDegenerate n →₀ ℚ) :=
  moduleIsoLinearEquiv (sSetNormalizedChainIsoFinsupp Y n)

lemma finrank_sSetNormalizedChainComplex (Y : SSet) (n : ℕ)
    [Finite (Y.nonDegenerate n)] :
    Module.finrank ℚ ((Y.normalizedChainComplex rationalModule).X n) =
      Nat.card (Y.nonDegenerate n) := by
  letI : Fintype (Y.nonDegenerate n) := Fintype.ofFinite _
  rw [(sSetNormalizedChainLinearEquivFinsupp Y n).finrank_eq]
  rw [Module.finrank_finsupp_self]
  exact Fintype.card_eq_nat_card

lemma alternating_choose_shift (q : ℕ) :
    (∑ n ∈ Finset.range q, (-1 : ℤ) ^ n * (q + 1).choose (n + 1)) =
      1 - (-1 : ℤ) ^ q := by
  have h := Int.alternating_sum_range_choose_eq_choose (n := q) (m := q)
  rw [Finset.sum_range_succ'] at h
  norm_num at h
  calc
    (∑ n ∈ Finset.range q, (-1 : ℤ) ^ n * (q + 1).choose (n + 1)) =
        -(∑ n ∈ Finset.range q,
          (-1 : ℤ) ^ (n + 1) * (q + 1).choose (n + 1)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [pow_succ]
      ring
    _ = 1 - (-1 : ℤ) ^ q := by
      omega

lemma boundaryNormalizedChain_finrankSupport_subset (q : ℕ) :
    GradedObject.finrankSupport
      (((SSet.boundary q : SSet).normalizedChainComplex rationalModule).X) ⊆
        (Finset.range q : Set ℕ) := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range] at hn
  have hzero := (SSet.boundary q : SSet).isZero_normalizedChainComplex_X_of_hasDimensionLT
    rationalModule n q (Nat.le_of_not_gt hn)
  letI : Subsingleton
      (((SSet.boundary q : SSet).normalizedChainComplex rationalModule).X n) :=
    ModuleCat.subsingleton_of_isZero hzero
  exact Module.finrank_zero_of_subsingleton

lemma boundaryChain_eulerChar (q : ℕ) :
    HomologicalComplex.eulerChar
        ((SSet.boundary q : SSet).normalizedChainComplex rationalModule) =
      1 - (-1 : ℤ) ^ q := by
  rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset
    _ (Finset.range q) (boundaryNormalizedChain_finrankSupport_subset q)]
  calc
    (∑ n ∈ Finset.range q,
        ((ComplexShape.down ℕ).χ n : ℤ) *
          Module.finrank ℚ
            (((SSet.boundary q : SSet).normalizedChainComplex rationalModule).X n)) =
        ∑ n ∈ Finset.range q,
          (-1 : ℤ) ^ n * (q + 1).choose (n + 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [downNat_eulerCharSign]
      rw [finrank_sSetNormalizedChainComplex]
      rw [natCard_boundary_nonDegenerate (Finset.mem_range.mp hn)]
    _ = 1 - (-1 : ℤ) ^ q := alternating_choose_shift q

def HasLocalSphereHomologyEuler {d : ℕ} (X : FiniteSimplicialSphere d) : Prop :=
  ∀ σ ∈ augmentedFaces X,
    HomologicalComplex.homologyEulerChar
        ((linkSSet X σ : SSet).normalizedChainComplex rationalModule) =
      1 - ((-1 : ℤ) ^ d * (-1 : ℤ) ^ σ.card)

lemma hasSignedEulerianLinks_of_hasLocalSphereHomologyEuler {d : ℕ}
    (X : FiniteSimplicialSphere d) (hX : HasLocalSphereHomologyEuler X) :
    HasSignedEulerianLinks X := by
  intro σ hσ
  rw [linkEulerSum_eq_one_sub_homologyEulerChar X hσ, hX σ hσ]
  ring

end

end Submission.Helpers.DehnSommerville
