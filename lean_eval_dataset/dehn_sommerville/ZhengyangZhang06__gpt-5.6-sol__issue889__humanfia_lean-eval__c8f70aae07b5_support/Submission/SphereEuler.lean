import Submission.EulerModels

namespace Submission.Helpers.DehnSommerville

open LeanEval.Combinatorics.DehnSommerville
open Set
open CarrierProto
open scoped ContinuousMap

noncomputable section

namespace FinitePolyhedron

/-! ### A finite affine-simplex model of the sphere -/

def simplexBoundaryAbstract (d : ℕ) :
    PreAbstractSimplicialComplex (Fin (d + 1)) where
  faces := {s | s.Nonempty ∧ s ≠ Finset.univ}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, ?_⟩
    intro htuniv
    apply hs.2
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    exact hts (by simp [htuniv])

@[simp]
lemma mem_simplexBoundaryAbstract_faces {d : ℕ} {s : Finset (Fin (d + 1))} :
    s ∈ (simplexBoundaryAbstract d).faces ↔
      s.Nonempty ∧ s ≠ Finset.univ :=
  Iff.rfl

noncomputable def sphereAffineBasis (d : ℕ) :
    AffineBasis (Fin (d + 1)) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (d + 1)) (k := ℝ) (P := EuclideanSpace ℝ (Fin d)) (by simp)).some

noncomputable def simplexBoundaryComplex (d : ℕ) :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin d)) := by
  classical
  exact Geometry.SimplicialComplex.ofAffineIndependent
    ((simplexBoundaryAbstract d).map (sphereAffineBasis d))
    ((sphereAffineBasis d).ind.range.mono (by
      intro x hx
      simp only [Set.mem_iUnion, Finset.mem_coe] at hx
      obtain ⟨_, ⟨_, _, rfl⟩, hx⟩ := hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl⟩))

lemma mem_simplexBoundaryComplex_faces {d : ℕ}
    {s : Finset (EuclideanSpace ℝ (Fin d))} :
    s ∈ (simplexBoundaryComplex d).faces ↔
      ∃ t : Finset (Fin (d + 1)),
        t.Nonempty ∧ t ≠ Finset.univ ∧
          s = t.image (sphereAffineBasis d) := by
  classical
  change s ∈ ((simplexBoundaryAbstract d).map (sphereAffineBasis d)).faces ↔ _
  simp only [PreAbstractSimplicialComplex.map, Set.mem_image,
    mem_simplexBoundaryAbstract_faces]
  constructor
  · rintro ⟨t, ⟨htne, htproper⟩, rfl⟩
    exact ⟨t, htne, htproper, rfl⟩
  · rintro ⟨t, htne, htproper, rfl⟩
    exact ⟨t, ⟨htne, htproper⟩, rfl⟩

lemma finite_simplexBoundaryComplex_faces (d : ℕ) :
    (simplexBoundaryComplex d).faces.Finite := by
  classical
  change ((simplexBoundaryAbstract d).faces.image
    (fun s => s.image (sphereAffineBasis d))).Finite
  exact Set.toFinite _

noncomputable def simplexBoundaryFiniteComplex (d : ℕ) :
    FiniteGeometricComplex (EuclideanSpace ℝ (Fin d)) where
  K := simplexBoundaryComplex d
  finite_faces := finite_simplexBoundaryComplex_faces d

/-! ### Euler characteristic as a geometric face sum -/

noncomputable def augmentedAbstractFaceEquivOptionGeometricFace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) :
    AugmentedAbstractFace (abstractComplex C) ≃ Option (GeometricFace C) where
  toFun s := if hs : s.1 = ∅ then none else
    some (abstractFaceEquivGeometricFace C ⟨s.1, s.2.resolve_left hs⟩)
  invFun o := match o with
    | none => ⟨∅, Or.inl rfl⟩
    | some G =>
        let s := (abstractFaceEquivGeometricFace C).symm G
        ⟨s.1, Or.inr s.2⟩
  left_inv s := by
    by_cases hs : s.1 = ∅
    · apply Subtype.ext
      simp [hs]
    · apply Subtype.ext
      simp [hs]
  right_inv o := by
    cases o with
    | none => simp
    | some G =>
        let s := (abstractFaceEquivGeometricFace C).symm G
        let a : AugmentedAbstractFace (abstractComplex C) := ⟨s.1, Or.inr s.2⟩
        have hsne : a.1 ≠ ∅ :=
          Finset.nonempty_iff_ne_empty.mp
            ((abstractComplex C).isRelLowerSet_faces s.2).1
        change (if h : a.1 = ∅ then none else
          some (abstractFaceEquivGeometricFace C ⟨a.1, a.2.resolve_left h⟩)) = some G
        rw [dif_neg hsne]
        congr 1
        have ha : (⟨a.1, a.2.resolve_left hsne⟩ :
            ComplexFace (abstractComplex C)) = s := by
          apply Subtype.ext
          rfl
        rw [ha]
        exact (abstractFaceEquivGeometricFace C).apply_symm_apply G

def optionGeometricFaceCard
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : FiniteGeometricComplex E} : Option (GeometricFace C) → ℕ
  | none => 0
  | some G => G.1.card

lemma augmentedAbstractFaceEquivOptionGeometricFace_card
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E)
    (s : AugmentedAbstractFace (abstractComplex C)) :
    s.1.card = optionGeometricFaceCard
      (augmentedAbstractFaceEquivOptionGeometricFace C s) := by
  by_cases hs : s.1 = ∅
  · simp [augmentedAbstractFaceEquivOptionGeometricFace, optionGeometricFaceCard, hs]
  · simp [augmentedAbstractFaceEquivOptionGeometricFace, optionGeometricFaceCard, hs,
      abstractFaceEquivGeometricFace, abstractFaceToGeometricFace]

lemma chainEulerQ_eq_optionGeometricFaceSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) :
    chainEulerQ (abstractComplex C) =
      ∑ o : Option (GeometricFace C),
        (-1 : ℚ) ^ optionGeometricFaceCard o := by
  rw [chainEulerQ_eq_augmentedAbstractFaceSum]
  exact Fintype.sum_equiv (augmentedAbstractFaceEquivOptionGeometricFace C)
    (fun s : AugmentedAbstractFace (abstractComplex C) => (-1 : ℚ) ^ s.1.card)
    (fun o : Option (GeometricFace C) =>
      (-1 : ℚ) ^ optionGeometricFaceCard o)
    (fun s => by rw [augmentedAbstractFaceEquivOptionGeometricFace_card])

def simplexFaceIndices {d : ℕ}
    (G : GeometricFace (simplexBoundaryFiniteComplex d)) :
    Finset (Fin (d + 1)) :=
  Finset.univ.filter fun i => sphereAffineBasis d i ∈ G.1

lemma simplexFaceIndices_image {d : ℕ} (t : Finset (Fin (d + 1))) :
    Finset.univ.filter (fun i => sphereAffineBasis d i ∈
      t.image (sphereAffineBasis d)) = t := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    exact (sphereAffineBasis d).ind.injective hji ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

lemma simplexFaceIndices_spec {d : ℕ}
    (G : GeometricFace (simplexBoundaryFiniteComplex d)) :
    (simplexFaceIndices G).Nonempty ∧
      simplexFaceIndices G ≠ Finset.univ ∧
      G.1 = (simplexFaceIndices G).image (sphereAffineBasis d) := by
  obtain ⟨t, htne, htproper, hG⟩ :=
    mem_simplexBoundaryComplex_faces.mp G.2
  have hind : simplexFaceIndices G = t := by
    rw [simplexFaceIndices, hG, simplexFaceIndices_image]
  rw [hind]
  exact ⟨htne, htproper, hG⟩

lemma empty_ne_univ_fin_succ (d : ℕ) :
    (∅ : Finset (Fin (d + 1))) ≠ Finset.univ := by
  intro h
  have hu : (Finset.univ : Finset (Fin (d + 1))).Nonempty := Finset.univ_nonempty
  rw [← h] at hu
  simp at hu

noncomputable def optionBoundaryFaceToProperFinset (d : ℕ) :
    Option (GeometricFace (simplexBoundaryFiniteComplex d)) →
      {t : Finset (Fin (d + 1)) // t ≠ Finset.univ}
  | none => ⟨∅, empty_ne_univ_fin_succ d⟩
  | some G => ⟨simplexFaceIndices G, (simplexFaceIndices_spec G).2.1⟩

noncomputable def properFinsetToBoundaryFace (d : ℕ)
    (t : {t : Finset (Fin (d + 1)) // t ≠ Finset.univ}) (ht : t.1 ≠ ∅) :
    GeometricFace (simplexBoundaryFiniteComplex d) := by
  refine ⟨t.1.image (sphereAffineBasis d), ?_⟩
  change t.1.image (sphereAffineBasis d) ∈ (simplexBoundaryComplex d).faces
  exact mem_simplexBoundaryComplex_faces.mpr
    ⟨t.1, Finset.nonempty_iff_ne_empty.mpr ht, t.2, rfl⟩

noncomputable def properFinsetToOptionBoundaryFace (d : ℕ)
    (t : {t : Finset (Fin (d + 1)) // t ≠ Finset.univ}) :
    Option (GeometricFace (simplexBoundaryFiniteComplex d)) :=
  if ht : t.1 = ∅ then none else some (properFinsetToBoundaryFace d t ht)

noncomputable def optionBoundaryFaceEquivProperFinset (d : ℕ) :
    Option (GeometricFace (simplexBoundaryFiniteComplex d)) ≃
      {t : Finset (Fin (d + 1)) // t ≠ Finset.univ} where
  toFun := optionBoundaryFaceToProperFinset d
  invFun := properFinsetToOptionBoundaryFace d
  left_inv o := by
    cases o with
    | none => simp [properFinsetToOptionBoundaryFace, optionBoundaryFaceToProperFinset]
    | some G =>
        have hspec := simplexFaceIndices_spec G
        change (if ht : simplexFaceIndices G = ∅ then none else
          some (properFinsetToBoundaryFace d
            ⟨simplexFaceIndices G, hspec.2.1⟩ ht)) = some G
        rw [dif_neg (Finset.nonempty_iff_ne_empty.mp hspec.1)]
        congr 1
        apply Subtype.ext
        exact hspec.2.2.symm
  right_inv t := by
    by_cases ht : t.1 = ∅
    · rw [properFinsetToOptionBoundaryFace, dif_pos ht]
      apply Subtype.ext
      exact ht.symm
    · rw [properFinsetToOptionBoundaryFace, dif_neg ht]
      apply Subtype.ext
      exact simplexFaceIndices_image t.1

lemma optionBoundaryFaceEquivProperFinset_card (d : ℕ)
    (o : Option (GeometricFace (simplexBoundaryFiniteComplex d))) :
    optionGeometricFaceCard o = (optionBoundaryFaceEquivProperFinset d o).1.card := by
  cases o with
  | none => rfl
  | some G =>
      change G.1.card = (simplexFaceIndices G).card
      rw [(simplexFaceIndices_spec G).2.2, Finset.card_image_of_injective _
        (sphereAffineBasis d).ind.injective]

noncomputable def properFinsetEquivPowersetErase (d : ℕ) :
    {t : Finset (Fin (d + 1)) // t ≠ Finset.univ} ≃
      {t : Finset (Fin (d + 1)) //
        t ∈ (Finset.univ : Finset (Fin (d + 1))).powerset.erase Finset.univ} where
  toFun t := ⟨t.1, by simp [t.2]⟩
  invFun t := ⟨t.1, by simpa using (Finset.mem_erase.mp t.2).1⟩
  left_inv t := by apply Subtype.ext; rfl
  right_inv t := by apply Subtype.ext; rfl

lemma chainEulerQ_simplexBoundary (d : ℕ) :
    chainEulerQ (abstractComplex (simplexBoundaryFiniteComplex d)) = (-1 : ℚ) ^ d := by
  rw [chainEulerQ_eq_optionGeometricFaceSum]
  calc
    (∑ o : Option (GeometricFace (simplexBoundaryFiniteComplex d)),
        (-1 : ℚ) ^ optionGeometricFaceCard o) =
        ∑ t : {t : Finset (Fin (d + 1)) // t ≠ Finset.univ},
          (-1 : ℚ) ^ t.1.card := by
      exact Fintype.sum_equiv (optionBoundaryFaceEquivProperFinset d)
        (fun o : Option (GeometricFace (simplexBoundaryFiniteComplex d)) =>
          (-1 : ℚ) ^ optionGeometricFaceCard o)
        (fun t : {t : Finset (Fin (d + 1)) // t ≠ Finset.univ} =>
          (-1 : ℚ) ^ t.1.card)
        (fun o => by rw [optionBoundaryFaceEquivProperFinset_card])
    _ = ∑ t : {t : Finset (Fin (d + 1)) //
          t ∈ (Finset.univ : Finset (Fin (d + 1))).powerset.erase Finset.univ},
          (-1 : ℚ) ^ t.1.card := by
      exact Fintype.sum_equiv (properFinsetEquivPowersetErase d)
        (fun t : {t : Finset (Fin (d + 1)) // t ≠ Finset.univ} =>
          (-1 : ℚ) ^ t.1.card)
        (fun t : {t : Finset (Fin (d + 1)) //
          t ∈ (Finset.univ : Finset (Fin (d + 1))).powerset.erase Finset.univ} =>
          (-1 : ℚ) ^ t.1.card)
        (fun _ => rfl)
    _ = ∑ t ∈ (Finset.univ : Finset (Fin (d + 1))).powerset.erase Finset.univ,
          (-1 : ℚ) ^ t.card := by
      let s := (Finset.univ : Finset (Fin (d + 1))).powerset.erase Finset.univ
      change (∑ t : {t : Finset (Fin (d + 1)) // t ∈ s},
        (-1 : ℚ) ^ t.1.card) = ∑ t ∈ s, (-1 : ℚ) ^ t.card
      rw [show (Finset.univ : Finset {t : Finset (Fin (d + 1)) // t ∈ s}) =
          s.attach by ext t; simp]
      exact Finset.sum_attach s (fun t => (-1 : ℚ) ^ t.card)
    _ = (-1 : ℚ) ^ d := by
      let u : Finset (Fin (d + 1)) := Finset.univ
      have hu : u.Nonempty := Finset.univ_nonempty
      have hzeroInt : (∑ t ∈ u.powerset, (-1 : ℤ) ^ t.card) = 0 :=
        Finset.sum_powerset_neg_one_pow_card_of_nonempty hu
      have hzero : (∑ t ∈ u.powerset, (-1 : ℚ) ^ t.card) = 0 := by
        exact_mod_cast hzeroInt
      have herase := Finset.sum_erase_add u.powerset
        (fun t : Finset (Fin (d + 1)) => (-1 : ℚ) ^ t.card)
        (Finset.mem_powerset_self u)
      rw [hzero] at herase
      change (∑ t ∈ u.powerset.erase u, (-1 : ℚ) ^ t.card) = _
      have hcard : u.card = d + 1 := by simp [u]
      rw [hcard] at herase
      rw [pow_succ] at herase
      linarith

lemma simplexBoundaryComplex_space (d : ℕ) :
    (simplexBoundaryComplex d).space =
      frontier (convexHull ℝ (Set.range (sphereAffineBasis d))) := by
  classical
  let b := sphereAffineBasis d
  have hcompact : IsCompact (convexHull ℝ (Set.range b)) :=
    (Set.finite_range b).isCompact_convexHull ℝ
  rw [hcompact.isClosed.frontier_eq, b.interior_convexHull]
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := (simplexBoundaryComplex d).mem_space_iff.mp hx
    obtain ⟨t, htne, htproper, rfl⟩ := mem_simplexBoundaryComplex_faces.mp hs
    have hfull : x ∈ convexHull ℝ (Set.range b) := by
      apply convexHull_mono _ hxs
      intro y hy
      rw [Finset.mem_coe] at hy
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨i, rfl⟩
    have himiss : ∃ i, i ∉ t := by
      by_contra h
      push Not at h
      exact htproper (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨i, hi⟩ := himiss
    have hcoord : b.coord i x = 0 := by
      apply (convexHull_min (s := (t.image b : Set _)) (t := {y | b.coord i y = 0}) ?_
        ((convex_singleton 0).affine_preimage (b.coord i))) hxs
      intro y hy
      rw [Finset.mem_coe] at hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact b.coord_apply_ne (fun h => hi (h ▸ hj))
    exact ⟨hfull, by
      simp only [Set.mem_setOf_eq, not_forall]
      exact ⟨i, by simp [hcoord]⟩⟩
  · rintro ⟨hfull, hinterior⟩
    rw [Set.mem_setOf_eq] at hinterior
    have hnonneg : ∀ i, 0 ≤ b.coord i x := by
      rw [b.convexHull_eq_nonneg_coord] at hfull
      exact hfull
    push Not at hinterior
    obtain ⟨i, hi⟩ := hinterior
    have hcoord : b.coord i x = 0 := le_antisymm hi (hnonneg i)
    let t : Finset (Fin (d + 1)) := Finset.univ.erase i
    have hsum : ∑ j ∈ t, b.coord j x = 1 := by
      rw [show t = Finset.univ.erase i by rfl, Finset.sum_erase]
      · exact b.sum_coord_apply_eq_one x
      · exact hcoord
    have htne : t.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro ht
      rw [ht] at hsum
      simp at hsum
    have htproper : t ≠ Finset.univ := by
      intro ht
      have : i ∈ t := by rw [ht]; simp
      have hi : i ∉ t := by simp [t]
      exact hi this
    apply (simplexBoundaryComplex d).convexHull_subset_space
      (mem_simplexBoundaryComplex_faces.mpr ⟨t, htne, htproper, rfl⟩)
    have hsum_eq : (∑ j ∈ t, b.coord j x • b j) = x := by
      calc
        (∑ j ∈ t, b.coord j x • b j) =
            ∑ j, b.coord j x • b j := by
          rw [show t = Finset.univ.erase i by rfl, Finset.sum_erase]
          simp [hcoord]
        _ = x := b.linear_combination_coord_eq_self x
    have hmem := t.centerMass_mem_convexHull
      (s := (↑(t.image b) : Set _)) (w := fun j => b.coord j x) (z := b)
      (fun j _ => hnonneg j) (by rw [hsum]; norm_num)
      (fun j hj => Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    rw [← affineCombination_eq_centerMass hsum,
      Finset.affineCombination_eq_linear_combination t b _ hsum,
      hsum_eq] at hmem
    exact hmem

noncomputable def simplexBoundarySphereHomeomorph (d : ℕ) :
    (simplexBoundaryComplex d).space ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  let b := sphereAffineBasis d
  let hex :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_convexHull ℝ (Set.range b))
      ⟨Finset.univ.centroid ℝ b, b.centroid_mem_interior_convexHull⟩
      ((Set.finite_range b).isCompact_convexHull ℝ).isBounded
  let h := hex.choose
  have hf := hex.choose_spec.2.2
  exact (Homeomorph.setCongr (simplexBoundaryComplex_space d)).trans
    ((h.image (frontier (convexHull ℝ (Set.range b)))).trans
      (Homeomorph.setCongr hf))

noncomputable def canonicalSimplexBoundaryHomeomorph {d : ℕ}
    (X : FiniteSimplicialSphere d) :
    (canonicalFiniteComplex X).K.space ≃ₜ
      (simplexBoundaryFiniteComplex d).K.space :=
  (canonicalSphereHomeomorph X).trans (simplexBoundarySphereHomeomorph d).symm

lemma augmentedEulerSum_eq_neg_one_pow {d : ℕ}
    (X : FiniteSimplicialSphere d) :
    augmentedEulerSum X = (-1 : ℤ) ^ d := by
  have h := chainEulerQ_eq_of_topologicalHomotopyEquiv
    (canonicalFiniteComplex X) (simplexBoundaryFiniteComplex d)
    (canonicalSimplexBoundaryHomeomorph X).toHomotopyEquiv
  rw [chainEulerQ_canonical_eq_augmentedEulerSum_cast,
    chainEulerQ_simplexBoundary] at h
  exact_mod_cast h

/-! ### Original-coordinate face deletions -/

noncomputable def originalDeletionComplex {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin d)) where
  faces := {G | G ∈ X.K.faces ∧ ¬σ ⊆ G}
  indep := fun hG => X.K.indep hG.1
  isRelLowerSet_faces := by
    intro G hG
    refine ⟨X.K.nonempty_of_mem_faces hG.1, ?_⟩
    intro F hFG hF
    refine ⟨X.K.down_closed hG.1 hFG hF, ?_⟩
    intro hσF
    exact hG.2 (hσF.trans hFG)
  inter_subset_convexHull := fun hG hF =>
    X.K.inter_subset_convexHull hG.1 hF.1

@[simp]
lemma mem_originalDeletionComplex_faces {d : ℕ}
    {X : FiniteSimplicialSphere d}
    {σ G : Finset (EuclideanSpace ℝ (Fin d))} :
    G ∈ (originalDeletionComplex X σ).faces ↔
      G ∈ X.K.faces ∧ ¬σ ⊆ G :=
  Iff.rfl

lemma finite_originalDeletionComplex_faces {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    (originalDeletionComplex X σ).faces.Finite :=
  X.finite_faces.subset fun _ hG => hG.1

noncomputable def originalDeletionFiniteComplex {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    FiniteGeometricComplex (EuclideanSpace ℝ (Fin d)) where
  K := originalDeletionComplex X σ
  finite_faces := finite_originalDeletionComplex_faces X σ

abbrev OriginalDeletionFace {d : ℕ} (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :=
  {G : Finset (EuclideanSpace ℝ (Fin d)) // G ∈ deletionFaceFinset X σ}

noncomputable def optionOriginalDeletionFaceToDeletionFace {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) (hσne : σ.Nonempty) :
    Option (GeometricFace (originalDeletionFiniteComplex X σ)) →
      OriginalDeletionFace X σ
  | none => ⟨∅, mem_deletionFaceFinset.mpr ⟨by simp [augmentedFaces], by
      intro hσ
      obtain ⟨v, hv⟩ := hσne
      simpa using hσ hv⟩⟩
  | some G => ⟨G.1, by
      apply mem_deletionFaceFinset.mpr
      have hG := G.2
      change G.1 ∈ X.K.faces ∧ ¬σ ⊆ G.1 at hG
      exact ⟨mem_augmentedFaces.mpr (Or.inr hG.1), hG.2⟩⟩

noncomputable def deletionFaceToGeometricFace {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (G : OriginalDeletionFace X σ) (hG : G.1 ≠ ∅) :
    GeometricFace (originalDeletionFiniteComplex X σ) := by
  refine ⟨G.1, ?_⟩
  change G.1 ∈ X.K.faces ∧ ¬σ ⊆ G.1
  have hmem := mem_deletionFaceFinset.mp G.2
  exact ⟨(mem_augmentedFaces.mp hmem.1).resolve_left hG, hmem.2⟩

noncomputable def deletionFaceToOptionOriginalDeletionFace {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (G : OriginalDeletionFace X σ) :
    Option (GeometricFace (originalDeletionFiniteComplex X σ)) :=
  if hG : G.1 = ∅ then none else some (deletionFaceToGeometricFace X σ G hG)

noncomputable def optionOriginalDeletionFaceEquiv {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) (hσne : σ.Nonempty) :
    Option (GeometricFace (originalDeletionFiniteComplex X σ)) ≃
      OriginalDeletionFace X σ where
  toFun := optionOriginalDeletionFaceToDeletionFace X σ hσne
  invFun := deletionFaceToOptionOriginalDeletionFace X σ
  left_inv o := by
    cases o with
    | none => simp [optionOriginalDeletionFaceToDeletionFace,
        deletionFaceToOptionOriginalDeletionFace]
    | some G =>
        have hGne : G.1 ≠ ∅ := Finset.nonempty_iff_ne_empty.mp
          ((originalDeletionComplex X σ).nonempty_of_mem_faces G.2)
        change (if h : G.1 = ∅ then none else
          some (deletionFaceToGeometricFace X σ
            (optionOriginalDeletionFaceToDeletionFace X σ hσne (some G)) h)) = some G
        rw [dif_neg hGne]
        congr 1
  right_inv G := by
    by_cases hG : G.1 = ∅
    · rw [deletionFaceToOptionOriginalDeletionFace, dif_pos hG]
      apply Subtype.ext
      exact hG.symm
    · rw [deletionFaceToOptionOriginalDeletionFace, dif_neg hG]
      apply Subtype.ext
      rfl

lemma optionOriginalDeletionFaceEquiv_card {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) (hσne : σ.Nonempty)
    (o : Option (GeometricFace (originalDeletionFiniteComplex X σ))) :
    optionGeometricFaceCard o =
      (optionOriginalDeletionFaceEquiv X σ hσne o).1.card := by
  cases o <;> rfl

lemma chainEulerQ_originalDeletion_eq_cast {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) (hσne : σ.Nonempty) :
    chainEulerQ (abstractComplex (originalDeletionFiniteComplex X σ)) =
      (deletionEulerSum X σ : ℚ) := by
  rw [chainEulerQ_eq_optionGeometricFaceSum]
  calc
    (∑ o : Option (GeometricFace (originalDeletionFiniteComplex X σ)),
        (-1 : ℚ) ^ optionGeometricFaceCard o) =
        ∑ G : OriginalDeletionFace X σ, (-1 : ℚ) ^ G.1.card := by
      exact Fintype.sum_equiv (optionOriginalDeletionFaceEquiv X σ hσne)
        (fun o : Option (GeometricFace (originalDeletionFiniteComplex X σ)) =>
          (-1 : ℚ) ^ optionGeometricFaceCard o)
        (fun G : OriginalDeletionFace X σ => (-1 : ℚ) ^ G.1.card)
        (fun o => by rw [optionOriginalDeletionFaceEquiv_card])
    _ = ∑ G ∈ deletionFaceFinset X σ, (-1 : ℚ) ^ G.card := by
      let s := deletionFaceFinset X σ
      change (∑ G : {G : Finset (EuclideanSpace ℝ (Fin d)) // G ∈ s},
        (-1 : ℚ) ^ G.1.card) = ∑ G ∈ s, (-1 : ℚ) ^ G.card
      rw [show (Finset.univ :
          Finset {G : Finset (EuclideanSpace ℝ (Fin d)) // G ∈ s}) = s.attach by
        ext G
        simp]
      exact Finset.sum_attach s (fun G => (-1 : ℚ) ^ G.card)
    _ = (deletionEulerSum X σ : ℚ) := by
      rw [deletionEulerSum]
      push_cast
      rfl

lemma canonicalDeletionSet_iff_originalDeletionSpace {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (hσ : σ ∈ X.K.faces)
    (w : (canonicalComplex X).space) :
    w ∈ canonicalDeletionSet X (liftFace X σ hσ)
        ((vertexComplex X).isRelLowerSet_faces
          (liftFace_mem_vertexComplex X σ hσ)).1 ↔
      (canonicalSpaceHomeomorph X w).1 ∈
        (originalDeletionComplex X σ).space := by
  classical
  let τ := liftFace X σ hσ
  have hτ : τ ∈ (vertexComplex X).faces := liftFace_mem_vertexComplex X σ hσ
  have hτne : τ.Nonempty := ((vertexComplex X).isRelLowerSet_faces hτ).1
  constructor
  · intro hw
    obtain ⟨v, hvτ, hwv⟩ := (mem_canonicalDeletionSet_iff X hτne w).mp hw
    obtain ⟨s, hs, hws⟩ := (canonicalComplex X).mem_space_iff.mp w.2
    obtain ⟨υ, hυ, rfl⟩ := mem_canonicalComplex_faces.mp hs
    have hwprops := (mem_convexHull_canonicalFace_iff X υ w.1).mp hws
    let t := υ.erase v
    have htne : t.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro ht
      have hallzero : ∀ u, w.1 u = 0 := by
        intro u
        by_cases huv : u = v
        · simpa [huv] using hwv
        · apply hwprops.2.1 u
          intro huυ
          have hut : u ∈ t := Finset.mem_erase.mpr ⟨huv, huυ⟩
          rw [ht] at hut
          simp at hut
      have hsum := canonicalSpace_sum X w
      simp_rw [hallzero] at hsum
      simp at hsum
    have htface : t ∈ (vertexComplex X).faces :=
      ((vertexComplex X).isRelLowerSet_faces hυ).2
        (Finset.erase_subset _ _) htne
    have hwt : w.1 ∈ convexHull ℝ
        (t.image (canonicalVertex X) : Set (Vertex X → ℝ)) := by
      rw [mem_convexHull_canonicalFace_iff X t]
      refine ⟨hwprops.1, ?_, hwprops.2.2⟩
      intro u hut
      by_cases huv : u = v
      · simpa [huv] using hwv
      · apply hwprops.2.1 u
        intro huυ
        exact hut (Finset.mem_erase.mpr ⟨huv, huυ⟩)
    have heval : canonicalEval X w.1 ∈ convexHull ℝ
        (t.map (vertexEmbedding X) : Set (EuclideanSpace ℝ (Fin d))) := by
      rw [← canonicalEval_image_convexHull X t]
      exact ⟨w.1, hwt, rfl⟩
    have htX : t.map (vertexEmbedding X) ∈ X.K.faces := htface
    have hnot : ¬σ ⊆ t.map (vertexEmbedding X) := by
      intro hsub
      have hvσ : (v : EuclideanSpace ℝ (Fin d)) ∈ σ := by
        rw [← map_liftFace X σ hσ]
        exact Finset.mem_map.mpr ⟨v, hvτ, rfl⟩
      have hvmap := hsub hvσ
      obtain ⟨u, hu, huv⟩ := Finset.mem_map.mp hvmap
      have huv' : u = v := (vertexEmbedding X).injective huv
      have hvt : v ∈ t := huv' ▸ hu
      exact (by simp [t] : v ∉ t) hvt
    change canonicalEval X w.1 ∈ (originalDeletionComplex X σ).space
    exact (originalDeletionComplex X σ).convexHull_subset_space
      ⟨htX, hnot⟩ heval
  · intro hw
    change canonicalEval X w.1 ∈ (originalDeletionComplex X σ).space at hw
    obtain ⟨G, hG, hwG⟩ := (originalDeletionComplex X σ).mem_space_iff.mp hw
    let υ := liftFace X G hG.1
    have hυ : υ ∈ (vertexComplex X).faces := liftFace_mem_vertexComplex X G hG.1
    have hwG' : canonicalEval X w.1 ∈ convexHull ℝ
        (υ.map (vertexEmbedding X) : Set (EuclideanSpace ℝ (Fin d))) := by
      rw [map_liftFace X G hG.1]
      exact hwG
    rw [← canonicalEval_image_convexHull X υ] at hwG'
    obtain ⟨z, hz, hzeval⟩ := hwG'
    have hzspace : z ∈ (canonicalComplex X).space :=
      (canonicalComplex X).convexHull_subset_space
        (mem_canonicalComplex_faces.mpr ⟨υ, hυ, rfl⟩) hz
    have hzw : z = w.1 :=
      canonicalEval_injectiveOn_space X hzspace w.2 hzeval
    have hwυ : w.1 ∈ convexHull ℝ
        (υ.image (canonicalVertex X) : Set (Vertex X → ℝ)) := by
      rwa [← hzw]
    obtain ⟨p, hpσ, hpG⟩ := Set.not_subset.mp hG.2
    have hpτ : p ∈ (liftFace X σ hσ).map (vertexEmbedding X) := by
      rw [map_liftFace X σ hσ]
      exact hpσ
    obtain ⟨v, hvτ, hvp⟩ := Finset.mem_map.mp hpτ
    have hvυ : v ∉ υ := by
      intro hv
      apply hpG
      rw [← hvp, ← map_liftFace X G hG.1]
      exact Finset.mem_map.mpr ⟨v, hv, rfl⟩
    apply (mem_canonicalDeletionSet_iff X hτne w).mpr
    exact ⟨v, hvτ,
      ((mem_convexHull_canonicalFace_iff X υ w.1).mp hwυ).2.1 v hvυ⟩

lemma originalDeletion_space_subset {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    (originalDeletionComplex X σ).space ⊆ X.K.space := by
  intro x hx
  obtain ⟨G, hG, hxG⟩ := (originalDeletionComplex X σ).mem_space_iff.mp hx
  exact X.K.convexHull_subset_space hG.1 hxG

noncomputable def originalDeletionNestedHomeomorph {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d))) :
    {x : X.K.space // x.1 ∈ (originalDeletionComplex X σ).space} ≃ₜ
      (originalDeletionComplex X σ).space where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, originalDeletion_space_subset X σ x.2⟩, x.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

noncomputable def originalDeletionSpaceHomeomorph {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (hσ : σ ∈ X.K.faces) :
    (originalDeletionComplex X σ).space ≃ₜ
      canonicalDeletionSet X (liftFace X σ hσ)
        ((vertexComplex X).isRelLowerSet_faces
          (liftFace_mem_vertexComplex X σ hσ)).1 :=
  (originalDeletionNestedHomeomorph X σ).symm.trans
    ((canonicalSpaceHomeomorph X).subtype
      (canonicalDeletionSet_iff_originalDeletionSpace X σ hσ)).symm

lemma contractibleSpace_originalDeletion {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (hσ : σ ∈ X.K.faces) :
    ContractibleSpace (originalDeletionComplex X σ).space := by
  let hτ := liftFace_mem_vertexComplex X σ hσ
  letI : ContractibleSpace
      (canonicalDeletionSet X (liftFace X σ hσ)
        ((vertexComplex X).isRelLowerSet_faces hτ).1) :=
    contractibleSpace_canonicalDeletionSet X hτ
  exact (originalDeletionSpaceHomeomorph X σ hσ).contractibleSpace

/-! ### A one-point comparison complex -/

def pointAbstractComplex (p : ℝ) : PreAbstractSimplicialComplex ℝ where
  faces := {s | s = {p}}
  isRelLowerSet_faces := by
    intro s hs
    rw [Set.mem_setOf_eq] at hs
    subst s
    refine ⟨by simp, ?_⟩
    intro t ht hne
    rw [Set.mem_setOf_eq]
    apply Finset.Subset.antisymm ht
    rw [Finset.singleton_subset_iff]
    obtain ⟨x, hx⟩ := hne
    have hxp : x = p := by simpa using ht hx
    simpa [hxp] using hx

@[simp]
lemma mem_pointAbstractComplex_faces (p : ℝ) (s : Finset ℝ) :
    s ∈ (pointAbstractComplex p).faces ↔ s = {p} :=
  Iff.rfl

noncomputable def pointComplex (p : ℝ) :
    Geometry.SimplicialComplex ℝ ℝ := by
  classical
  let A := pointAbstractComplex p
  letI : Subsingleton (⋃ s ∈ A.faces, (s : Set ℝ)) := by
    constructor
    intro x y
    apply Subtype.ext
    have hx : x.1 = p := by simpa [A, pointAbstractComplex] using x.2
    have hy : y.1 = p := by simpa [A, pointAbstractComplex] using y.2
    exact hx.trans hy.symm
  exact Geometry.SimplicialComplex.ofAffineIndependent A
    (affineIndependent_of_subsingleton ℝ _)

@[simp]
lemma mem_pointComplex_faces (p : ℝ) (s : Finset ℝ) :
    s ∈ (pointComplex p).faces ↔ s = {p} := by
  change s ∈ (pointAbstractComplex p).faces ↔ s = {p}
  rfl

noncomputable def pointFiniteComplex (p : ℝ) : FiniteGeometricComplex ℝ where
  K := pointComplex p
  finite_faces := by
    rw [show (pointComplex p).faces =
        ({({p} : Finset ℝ)} : Set (Finset ℝ)) by
      ext s
      simp [mem_pointComplex_faces]]
    exact Set.finite_singleton ({p} : Finset ℝ)

lemma pointComplex_space (p : ℝ) :
    (pointComplex p).space = ({p} : Set ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := (pointComplex p).mem_space_iff.mp hx
    rw [mem_pointComplex_faces] at hs
    subst s
    simpa [convexHull_singleton] using hxs
  · intro hx
    have hxp : x = p := by simpa using hx
    subst x
    apply (pointComplex p).convexHull_subset_space
      (mem_pointComplex_faces p {p} |>.mpr rfl)
    simp [convexHull_singleton]

noncomputable instance uniqueGeometricFace_pointFiniteComplex (p : ℝ) :
    Unique (GeometricFace (pointFiniteComplex p)) where
  default := ⟨{p}, mem_pointComplex_faces p {p} |>.mpr rfl⟩
  uniq G := Subtype.ext ((mem_pointComplex_faces p G.1).mp G.2)

lemma chainEulerQ_pointFiniteComplex (p : ℝ) :
    chainEulerQ (abstractComplex (pointFiniteComplex p)) = 0 := by
  rw [chainEulerQ_eq_optionGeometricFaceSum, Fintype.sum_option,
    Fintype.sum_unique]
  have hdefault : (default : GeometricFace (pointFiniteComplex p)).1 = {p} :=
    (mem_pointComplex_faces p _).mp
      (default : GeometricFace (pointFiniteComplex p)).2
  simp only [optionGeometricFaceCard]
  rw [hdefault]
  norm_num

instance contractibleSpace_pointComplex (p : ℝ) :
    ContractibleSpace (pointComplex p).space := by
  rw [pointComplex_space]
  infer_instance

lemma chainEulerQ_originalDeletion_eq_zero {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (hσ : σ ∈ X.K.faces) :
    chainEulerQ (abstractComplex (originalDeletionFiniteComplex X σ)) = 0 := by
  letI : ContractibleSpace (originalDeletionComplex X σ).space :=
    contractibleSpace_originalDeletion X σ hσ
  have h := chainEulerQ_eq_of_topologicalHomotopyEquiv
    (originalDeletionFiniteComplex X σ) (pointFiniteComplex 0)
    (ContractibleSpace.hequiv
      (originalDeletionComplex X σ).space (pointComplex 0).space).some
  rw [chainEulerQ_pointFiniteComplex] at h
  exact h

lemma deletionEulerSum_eq_zero {d : ℕ}
    (X : FiniteSimplicialSphere d)
    (σ : Finset (EuclideanSpace ℝ (Fin d)))
    (hσ : σ ∈ augmentedFaces X) (hσne : σ.Nonempty) :
    deletionEulerSum X σ = 0 := by
  have hσface : σ ∈ X.K.faces :=
    (mem_augmentedFaces.mp hσ).resolve_left
      (Finset.nonempty_iff_ne_empty.mp hσne)
  have hchain := chainEulerQ_originalDeletion_eq_zero X σ hσface
  rw [chainEulerQ_originalDeletion_eq_cast X σ hσne] at hchain
  exact_mod_cast hchain

lemma hasSphereDeletionEuler (d : ℕ) (X : FiniteSimplicialSphere d) :
    HasSphereDeletionEuler X :=
  ⟨augmentedEulerSum_eq_neg_one_pow X,
    fun σ hσ hσne => deletionEulerSum_eq_zero X σ hσ hσne⟩

end FinitePolyhedron

end

end Submission.Helpers.DehnSommerville
