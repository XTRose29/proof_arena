import Submission.DeletionTopology

namespace Submission.Helpers.DehnSommerville

open LeanEval.Combinatorics.DehnSommerville
open Set

noncomputable section

/-! ### Centroids of simplices -/

/-- The centroid of an affinely independent nonempty finite set lies in the
intrinsic interior of its convex hull. -/
lemma centroid_mem_intrinsicInterior_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset E) (hs : s.Nonempty)
    (hi : AffineIndependent ℝ ((↑) : s → E)) :
    s.centroid ℝ id ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  let A : AffineSubspace ℝ E := affineSpan ℝ (s : Set E)
  let p : s → A := fun x => ⟨x.1, subset_affineSpan ℝ (s : Set E) x.2⟩
  let a0 : A := p ⟨hs.choose, hs.choose_spec⟩
  letI : Nonempty A := ⟨a0⟩
  have hp_ind : AffineIndependent ℝ p := by
    apply AffineIndependent.of_comp (AffineSubspace.subtype A)
    simpa [p, A, Function.comp_def] using hi
  have hp_span : affineSpan ℝ (Set.range p) = ⊤ := by
    have hmap : (affineSpan ℝ (Set.range p)).map (AffineSubspace.subtype A) = A := by
      rw [AffineSubspace.map_span]
      change affineSpan ℝ ((fun x : A => (x : E)) '' Set.range p) = A
      have himage : ((fun x : A => (x : E)) '' Set.range p) = (s : Set E) := by
        ext x
        constructor
        · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
          exact z.property
        · intro hx
          exact ⟨p ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      rw [himage]
    ext x
    constructor
    · intro _
      simp
    · intro _
      have hx : (x : E) ∈ (affineSpan ℝ (Set.range p)).map
          (AffineSubspace.subtype A) := by
        rw [hmap]
        exact x.property
      obtain ⟨y, hy, hxy⟩ := hx
      have hyx : y = x := Subtype.ext hxy
      change y ∈ affineSpan ℝ (Set.range p) at hy
      exact hyx ▸ hy
  let e := AffineIsometryEquiv.constVSub ℝ a0
  let p' : s → A.direction := fun x => e (p x)
  have hp'_ind : AffineIndependent ℝ p' := by
    exact (e.toAffineEquiv.affineIndependent_iff).2 hp_ind
  have hp'_span : affineSpan ℝ (Set.range p') = ⊤ := by
    have h := e.toAffineEquiv.toAffineMap.span_eq_top_of_surjective
      e.surjective hp_span
    have hrange : Set.range p' = e '' Set.range p := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨p y, ⟨y, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    rw [hrange]
    exact h
  let b : AffineBasis s ℝ A.direction :=
    { toFun := p'
      ind' := hp'_ind
      tot' := hp'_span }
  have hb := b.centroid_mem_interior_convexHull
  let z : A.direction := (Finset.univ : Finset s).centroid ℝ p'
  have hz : z ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range p')) := by
    exact interior_subset_intrinsicInterior hb
  let f : A.direction →ᵃⁱ[ℝ] E := A.subtypeₐᵢ.comp e.symm.toAffineIsometry
  have hze0 : f z ∈ intrinsicInterior ℝ (f '' convexHull ℝ (Set.range p')) := by
    have himage := Set.mem_image_of_mem f hz
    rw [f.intrinsicInterior_image]
    exact himage
  have hset : f '' convexHull ℝ (Set.range p') = convexHull ℝ (s : Set E) := by
    change f.toAffineMap '' convexHull ℝ (Set.range p') = convexHull ℝ (s : Set E)
    rw [f.toAffineMap.image_convexHull]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
      have hfa : f.toAffineMap (p' a) = (a : E) := by
        simp [f, p', p]
      rw [hfa]
      exact a.property
    · intro hx
      exact ⟨p' ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, by
        simp [f, p', p]⟩
  rw [hset] at hze0
  have hcoord : f z = s.centroid ℝ id := by
    rw [← Finset.centroid_univ (k := ℝ) s]
    change f ((Finset.univ : Finset s).affineCombination ℝ p'
      ((Finset.univ : Finset s).centroidWeights ℝ)) =
        (Finset.univ : Finset s).affineCombination ℝ (fun x : s => (x : E))
          ((Finset.univ : Finset s).centroidWeights ℝ)
    have hw : ∑ x ∈ (Finset.univ : Finset s),
        (Finset.univ : Finset s).centroidWeights ℝ x = 1 := by
      exact (Finset.univ : Finset s).sum_centroidWeights_eq_one_of_nonempty ℝ
        ⟨⟨hs.choose, hs.choose_spec⟩, Finset.mem_univ _⟩
    change f.toAffineMap ((Finset.univ : Finset s).affineCombination ℝ p'
      ((Finset.univ : Finset s).centroidWeights ℝ)) = _
    rw [Finset.map_affineCombination (Finset.univ : Finset s) p' _ hw f.toAffineMap]
    have hfun : f.toAffineMap ∘ p' = fun x : s => (x : E) := by
      funext x
      simp [f, p', p]
    rw [hfun]
  rwa [← hcoord]

/-! ### Finite geometric complexes and their face centers -/

/-- A geometric simplicial complex together with finiteness of its face set. -/
structure FiniteGeometricComplex (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  K : Geometry.SimplicialComplex ℝ E
  finite_faces : K.faces.Finite

/-- The type of nonempty faces of a finite geometric complex. -/
abbrev GeometricFace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) := C.K.faces

noncomputable instance {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) : Fintype (GeometricFace C) :=
  C.finite_faces.fintype

noncomputable instance {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) : LinearOrder (GeometricFace C) :=
  LinearOrder.lift' (Fintype.equivFin (GeometricFace C))
    (Fintype.equivFin (GeometricFace C)).injective

/-- The centroid used as the barycentric-subdivision vertex of a face. -/
def faceCenter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) (F : GeometricFace C) : E :=
  F.1.centroid ℝ id

lemma faceCenter_mem_intrinsicInterior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) (F : GeometricFace C) :
    faceCenter C F ∈ intrinsicInterior ℝ (convexHull ℝ (F.1 : Set E)) := by
  exact centroid_mem_intrinsicInterior_convexHull F.1
    (C.K.nonempty_of_mem_faces F.2) (C.K.indep F.2)

lemma faceCenter_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) (F : GeometricFace C) :
    faceCenter C F ∈ convexHull ℝ (F.1 : Set E) :=
  intrinsicInterior_subset (faceCenter_mem_intrinsicInterior C F)

/-- A simplex centroid is not in the affine span of a proper collection of
its vertices. -/
lemma centroid_not_mem_affineSpan_proper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset E)
    (hi : AffineIndependent ℝ ((↑) : s → E))
    {t : Set s} (ht : t ≠ Set.univ) :
    s.centroid ℝ id ∉ affineSpan ℝ (((↑) : s → E) '' t) := by
  rw [← Finset.centroid_univ (k := ℝ) s]
  intro h
  have hproper : t ⊂ Set.univ := Set.ssubset_univ_iff.mpr ht
  obtain ⟨i, _, hi_not⟩ := Set.exists_of_ssubset hproper
  have hsum : ∑ j ∈ (Finset.univ : Finset s),
      (Finset.univ : Finset s).centroidWeights ℝ j = 1 :=
    (Finset.univ : Finset s).sum_centroidWeights_eq_one_of_nonempty ℝ
      ⟨i, Finset.mem_univ i⟩
  have hzero := hi.eq_zero_of_affineCombination_mem_affineSpan hsum h
    (Finset.mem_univ i) hi_not
  have hcard : ((Fintype.card s : ℝ)) ≠ 0 := by
    letI : Nonempty s := ⟨i⟩
    exact_mod_cast (Fintype.card_pos.ne')
  exact (inv_ne_zero hcard) hzero

lemma face_subset_of_center_mem_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) (F : GeometricFace C)
    {s : Finset E} (hsF : s ⊆ F.1)
    (hcenter : faceCenter C F ∈ convexHull ℝ (s : Set E)) :
    F.1 ⊆ s := by
  by_contra hnot
  have hproper : ({x : F.1 | (x : E) ∈ s} : Set F.1) ≠ Set.univ := by
    intro h
    apply hnot
    intro x hx
    have hx' : (⟨x, hx⟩ : F.1) ∈ ({x : F.1 | (x : E) ∈ s} : Set F.1) := by
      rw [h]
      trivial
    exact hx'
  apply centroid_not_mem_affineSpan_proper F.1 (C.K.indep F.2) hproper
  apply (convexHull_min (s := (s : Set E)) (t := affineSpan ℝ
      (((↑) : F.1 → E) '' ({x : F.1 | (x : E) ∈ s} : Set F.1))) ?_
      (AffineSubspace.convex _)) hcenter
  intro x hx
  exact subset_affineSpan ℝ _ ⟨⟨x, hsF hx⟩, hx, rfl⟩

lemma faceCenter_injective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) :
    Function.Injective (faceCenter C) := by
  classical
  intro F G hFG
  have hcenterF : faceCenter C F ∈ convexHull ℝ (F.1 ∩ G.1 : Set E) := by
    apply C.K.inter_subset_convexHull F.2 G.2
    exact ⟨faceCenter_mem C F, hFG ▸ faceCenter_mem C G⟩
  have hcenterG : faceCenter C G ∈ convexHull ℝ (F.1 ∩ G.1 : Set E) := by
    rw [← hFG]
    exact hcenterF
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · have hcenterF' : faceCenter C F ∈
        convexHull ℝ ((F.1 ∩ G.1 : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using hcenterF
    exact (face_subset_of_center_mem_convexHull C F
      (s := F.1 ∩ G.1) Finset.inter_subset_left hcenterF').trans Finset.inter_subset_right
  · have hcenterG' : faceCenter C G ∈
        convexHull ℝ ((F.1 ∩ G.1 : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using hcenterG
    exact (face_subset_of_center_mem_convexHull C G
      (s := F.1 ∩ G.1) Finset.inter_subset_right hcenterG').trans Finset.inter_subset_left

/-! ### Face chains -/

/-- A point carrying a nonzero coefficient in a vanishing affine relation
lies in the affine span of the other points in that relation. -/
theorem mem_affineSpan_erase_of_weightedVSub_eq_zero
    {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq J] (p : J → E) (s : Finset J) (w : J → ℝ) {i : J}
    (hi : i ∈ s) (hwi : w i ≠ 0) (hsum : ∑ j ∈ s, w j = 0)
    (hweighted : s.weightedVSub p w = 0) :
    p i ∈ affineSpan ℝ (p '' (s.erase i : Set J)) := by
  classical
  let t := s.erase i
  let p' : t → E := fun j => p j
  let w' : t → ℝ := fun j => -(w i)⁻¹ * w j
  have hsum_erase : ∑ j ∈ s.erase i, w j = -w i := by
    rw [Finset.sum_erase_eq_sub hi, hsum, zero_sub]
  have hw' : ∑ j, w' j = 1 := by
    rw [Finset.univ_eq_attach]
    simp only [w', Finset.sum_attach, ← Finset.mul_sum, t, hsum_erase]
    field_simp
  have hlinear : ∑ j ∈ s, w j • p j = 0 := by
    simpa only [Finset.weightedVSub_eq_linear_combination s hsum] using hweighted
  have hip : w i • p i = -∑ j ∈ s.erase i, w j • p j := by
    have herase : ∑ j ∈ s.erase i, w j • p j = -(w i • p i) := by
      rw [Finset.sum_erase_eq_sub hi, hlinear, zero_sub]
    calc
      w i • p i = -(-(w i • p i)) := by simp
      _ = -∑ j ∈ s.erase i, w j • p j :=
        congrArg (fun z : E => -z) herase.symm
  have hp' : p i = ∑ j, w' j • p' j := by
    rw [Finset.univ_eq_attach]
    simp only [w', p', t]
    calc
      p i = (w i)⁻¹ • (w i • p i) := by rw [inv_smul_smul₀ hwi]
      _ = (w i)⁻¹ • (-∑ j ∈ s.erase i, w j • p j) := by rw [hip]
      _ = ∑ j ∈ s.erase i, (-(w i)⁻¹ * w j) • p j := by
        rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [smul_smul]
        simp only [neg_smul, neg_mul]
      _ = ∑ j ∈ (s.erase i).attach, (-(w i)⁻¹ * w j) • p j := by
        exact (Finset.sum_attach (s.erase i)
          (fun j : J => (-(w i)⁻¹ * w j) • p j)).symm
  have hmem : p i ∈ affineSpan ℝ (Set.range p') := by
    rw [hp', ← Finset.affineCombination_eq_linear_combination Finset.univ p' w' hw']
    exact affineCombination_mem_affineSpan hw' p'
  have hrange : Set.range p' = p '' (t : Set J) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  rw [hrange] at hmem
  exact hmem

/-- A nonempty finite collection of faces linearly ordered by inclusion. -/
def IsFaceChain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    (c : Finset (GeometricFace C)) : Prop :=
  c.Nonempty ∧ ∀ F ∈ c, ∀ G ∈ c, F ≤ G ∨ G ≤ F

/-- The geometric vertices associated with a chain of faces. -/
noncomputable def chainCenters {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    (c : Finset (GeometricFace C)) : Finset E := by
  classical
  exact c.image (faceCenter C)

@[simp]
lemma mem_chainCenters {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    (c : Finset (GeometricFace C)) (x : E) :
    x ∈ chainCenters C c ↔ ∃ F ∈ c, faceCenter C F = x := by
  classical
  simp [chainCenters]

lemma faceCenter_not_mem_affineSpan_of_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) {F G : GeometricFace C} (hFG : F < G) :
    faceCenter C G ∉ affineSpan ℝ (F.1 : Set E) := by
  let t : Set G.1 := {x | (x : E) ∈ F.1}
  have ht : t ≠ Set.univ := by
    intro ht
    apply hFG.ne
    apply Subtype.ext
    apply Finset.Subset.antisymm hFG.le
    intro x hx
    have hx' : (⟨x, hx⟩ : G.1) ∈ t := by
      rw [ht]
      trivial
    exact hx'
  have himage : (((↑) : G.1 → E) '' t) = (F.1 : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hFG.le hx⟩, hx, rfl⟩
  change G.1.centroid ℝ id ∉ affineSpan ℝ (F.1 : Set E)
  intro h
  apply centroid_not_mem_affineSpan_proper G.1 (C.K.indep G.2) ht
  rw [himage]
  exact h

lemma affineIndependent_centers_of_isFaceChain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) (c : Finset (GeometricFace C))
    (hc : IsFaceChain C c) :
    AffineIndependent ℝ (fun F : c => faceCenter C F.1) := by
  classical
  letI : DecidableLE c := Classical.decRel (fun F G : c => F ≤ G)
  letI : DecidableLT c := Classical.decRel (fun F G : c => F < G)
  letI : LinearOrder c := Relation.linearOrderOfSymmGen fun F G =>
    hc.2 F.1 F.2 G.1 G.2
  intro s w hsum hweighted i hi
  by_contra hwi
  let support := s.filter fun j => w j ≠ 0
  have hisupport : i ∈ support := Finset.mem_filter.mpr ⟨hi, hwi⟩
  have hsupport : support.Nonempty := ⟨i, hisupport⟩
  let m : c := support.max' hsupport
  have hm_support : m ∈ support := support.max'_mem hsupport
  have hwm : w m ≠ 0 := (Finset.mem_filter.mp hm_support).2
  have hsum_support : ∑ j ∈ support, w j = 0 := by
    change ∑ j ∈ s.filter (fun j => w j ≠ 0), w j = 0
    rw [Finset.sum_filter_ne_zero]
    exact hsum
  have hweighted_support :
      support.weightedVSub (fun F : c => faceCenter C F.1) w = 0 := by
    change (s.filter fun j => w j ≠ 0).weightedVSub
      (fun F : c => faceCenter C F.1) w = 0
    rw [Finset.weightedVSub_filter_of_ne, hweighted]
    intro j hj hwj
    exact hwj
  have hmspan := mem_affineSpan_erase_of_weightedVSub_eq_zero
    (fun F : c => faceCenter C F.1) support w hm_support hwm
      hsum_support hweighted_support
  have hrest : (support.erase m).Nonempty := by
    by_contra hrest
    have hsubset : support ⊆ {m} := by
      intro j hj
      simp only [Finset.mem_singleton]
      by_contra hjm
      exact hrest ⟨j, Finset.mem_erase.mpr ⟨hjm, hj⟩⟩
    have heq : support = {m} := Finset.Subset.antisymm hsubset
      (Finset.singleton_subset_iff.mpr hm_support)
    apply hwm
    simpa [heq] using hsum_support
  let g : c := (support.erase m).max' hrest
  have hg_rest : g ∈ support.erase m := (support.erase m).max'_mem hrest
  have hg_support : g ∈ support := Finset.mem_of_mem_erase hg_rest
  have hgm_ne : g ≠ m := Finset.ne_of_mem_erase hg_rest
  have hgm : g.1 < m.1 := by
    refine lt_of_le_of_ne ?_ ?_
    · exact support.le_max' g hg_support
    · exact fun h => hgm_ne (Subtype.ext h)
  have himage :
      (fun F : c => faceCenter C F.1) '' (support.erase m : Set c) ⊆
        convexHull ℝ (g.1.1 : Set E) := by
    rintro _ ⟨j, hj, rfl⟩
    have hjg : j ≤ g := (support.erase m).le_max' j hj
    exact (convexHull_mono hjg : convexHull ℝ (j.1.1 : Set E) ⊆
      convexHull ℝ (g.1.1 : Set E)) (faceCenter_mem C j.1)
  have hmspan' : faceCenter C m.1 ∈ affineSpan ℝ (g.1.1 : Set E) := by
    rw [← affineSpan_convexHull]
    exact affineSpan_mono ℝ himage hmspan
  exact faceCenter_not_mem_affineSpan_of_lt C hgm hmspan'

/-- Erase one face from a face chain. -/
noncomputable def eraseFace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    (c : Finset (GeometricFace C)) (H : GeometricFace C) :
    Finset (GeometricFace C) := by
  classical
  exact c.erase H

@[simp]
lemma mem_eraseFace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    (c : Finset (GeometricFace C)) (H F : GeometricFace C) :
    F ∈ eraseFace C c H ↔ F ≠ H ∧ F ∈ c := by
  classical
  simp [eraseFace]

lemma IsFaceChain.subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {C : FiniteGeometricComplex E}
    {c d : Finset (GeometricFace C)} (hc : IsFaceChain C c)
    (hd : d.Nonempty) (hdc : d ⊆ c) : IsFaceChain C d := by
  refine ⟨hd, ?_⟩
  intro F hF G hG
  exact hc.2 F (hdc hF) G (hdc hG)

lemma chainCenters_mono {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    {c d : Finset (GeometricFace C)} (hcd : c ⊆ d) :
    chainCenters C c ⊆ chainCenters C d := by
  intro x hx
  obtain ⟨F, hFc, rfl⟩ := (mem_chainCenters C c x).mp hx
  exact (mem_chainCenters C d (faceCenter C F)).mpr ⟨F, hcd hFc, rfl⟩

set_option maxHeartbeats 1000000 in
/-- A point in a chain simplex has a highest face with positive
barycentric coefficient. -/
lemma exists_maximal_chain_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) (c : Finset (GeometricFace C))
    (hc : IsFaceChain C c) {x : E}
    (hx : x ∈ convexHull ℝ (chainCenters C c : Set E)) :
    ∃ H : GeometricFace C, H ∈ c ∧
      (x = faceCenter C H ∨
        ∃ (a : ℝ) (y : E) (G : GeometricFace C),
          0 < a ∧ a < 1 ∧ G ∈ c ∧ G < H ∧
          y ∈ convexHull ℝ (chainCenters C (eraseFace C c H) : Set E) ∧
          y ∈ convexHull ℝ (G.1 : Set E) ∧
          x = a • faceCenter C H + (1 - a) • y) := by
  classical
  letI : DecidableLE c := Classical.decRel (fun F G : c => F ≤ G)
  letI : DecidableLT c := Classical.decRel (fun F G : c => F < G)
  letI : LinearOrder c := Relation.linearOrderOfSymmGen fun F G =>
    hc.2 F.1 F.2 G.1 G.2
  obtain ⟨w, hw₀, hw₁, hwcenter⟩ := Finset.mem_convexHull'.mp hx
  let wt : c → ℝ := fun F => w (faceCenter C F.1)
  have hwt₀ (F : c) : 0 ≤ wt F := by
    apply hw₀
    exact (mem_chainCenters C c (faceCenter C F.1)).mpr ⟨F.1, F.2, rfl⟩
  have hsum_base : ∑ F ∈ c, w (faceCenter C F) = 1 := by
    rw [← hw₁, chainCenters, Finset.sum_image]
    exact (faceCenter_injective C).injOn
  have hsum : ∑ F, wt F = 1 := by
    calc
      ∑ F, wt F = ∑ F ∈ c.attach, w (faceCenter C F.1) := by
        rw [Finset.univ_eq_attach]
      _ = ∑ F ∈ c, w (faceCenter C F) :=
        Finset.sum_attach c fun F : GeometricFace C => w (faceCenter C F)
      _ = 1 := hsum_base
  have hcenter_base : ∑ F ∈ c, w (faceCenter C F) • faceCenter C F = x := by
    rw [← hwcenter, chainCenters, Finset.sum_image]
    exact (faceCenter_injective C).injOn
  have hcenter : ∑ F, wt F • faceCenter C F.1 = x := by
    calc
      ∑ F, wt F • faceCenter C F.1 =
          ∑ F ∈ c.attach, w (faceCenter C F.1) • faceCenter C F.1 := by
        rw [Finset.univ_eq_attach]
      _ = ∑ F ∈ c, w (faceCenter C F) • faceCenter C F :=
        Finset.sum_attach c fun F : GeometricFace C =>
          w (faceCenter C F) • faceCenter C F
      _ = x := hcenter_base
  let support : Finset c := Finset.univ.filter fun F => 0 < wt F
  have hsupport : support.Nonempty := by
    by_contra hsupp
    have hzero : ∀ F : c, wt F = 0 := by
      intro F
      apply le_antisymm
      · apply not_lt.mp
        intro hpos
        exact hsupp ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩⟩
      · exact hwt₀ F
    have : ∑ F, wt F = 0 := by simp [hzero]
    linarith
  let Hc : c := support.max' hsupport
  let H : GeometricFace C := Hc.1
  have hHsupport : Hc ∈ support := support.max'_mem hsupport
  have hHc : H ∈ c := Hc.2
  have ha_pos : 0 < wt Hc := (Finset.mem_filter.mp hHsupport).2
  have hzero_out (F : c) (hF : F ∉ support) : wt F = 0 := by
    apply le_antisymm
    · exact not_lt.mp fun hpos => hF <|
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
    · exact hwt₀ F
  have hsum_support : ∑ F ∈ support, wt F = 1 := by
    calc
      ∑ F ∈ support, wt F = ∑ F ∈ Finset.univ, wt F :=
        Finset.sum_subset (Finset.subset_univ _) fun F _ hF => hzero_out F hF
      _ = 1 := by simpa using hsum
  have hcenter_support : ∑ F ∈ support, wt F • faceCenter C F.1 = x := by
    calc
      ∑ F ∈ support, wt F • faceCenter C F.1 =
          ∑ F ∈ Finset.univ, wt F • faceCenter C F.1 :=
        Finset.sum_subset (Finset.subset_univ _) fun F _ hF => by
          rw [hzero_out F hF, zero_smul]
      _ = x := by simpa using hcenter
  by_cases hrest : (support.erase Hc).Nonempty
  · let Gc : c := (support.erase Hc).max' hrest
    let G : GeometricFace C := Gc.1
    have hGrest : Gc ∈ support.erase Hc := (support.erase Hc).max'_mem hrest
    have hGsupport : Gc ∈ support := Finset.mem_of_mem_erase hGrest
    have hGH_ne : Gc ≠ Hc := Finset.ne_of_mem_erase hGrest
    have hGH : G < H := by
      refine lt_of_le_of_ne (support.le_max' Gc hGsupport) ?_
      exact fun h => hGH_ne (Subtype.ext h)
    have hsum_rest : ∑ F ∈ support.erase Hc, wt F = 1 - wt Hc := by
      rw [Finset.sum_erase_eq_sub hHsupport, hsum_support]
    have hsum_rest_pos : 0 < ∑ F ∈ support.erase Hc, wt F := by
      refine lt_of_lt_of_le ((Finset.mem_filter.mp hGsupport).2) ?_
      exact Finset.single_le_sum (fun F hF => hwt₀ F) hGrest
    have ha_lt : wt Hc < 1 := by linarith
    let nw : c → ℝ := fun F => wt F / (1 - wt Hc)
    have hnw₀ (F : c) (hF : F ∈ support.erase Hc) : 0 ≤ nw F := by
      exact div_nonneg (hwt₀ F) (sub_nonneg.mpr ha_lt.le)
    have hnwsum : ∑ F ∈ support.erase Hc, nw F = 1 := by
      simp only [nw, ← Finset.sum_div, hsum_rest]
      exact div_self (sub_ne_zero.mpr (ne_of_gt ha_lt))
    let y : E := ∑ F ∈ support.erase Hc, nw F • faceCenter C F.1
    have hyhull : y ∈
        convexHull ℝ (chainCenters C (eraseFace C c H) : Set E) := by
      apply (convex_convexHull ℝ
        (chainCenters C (eraseFace C c H) : Set E)).sum_mem hnw₀ hnwsum
      intro F hF
      apply subset_convexHull
      rw [Finset.mem_coe, mem_chainCenters]
      refine ⟨F.1, ?_, rfl⟩
      apply (mem_eraseFace C c H F.1).mpr
      refine ⟨?_, F.2⟩
      intro hFH
      apply Finset.ne_of_mem_erase hF
      apply Subtype.ext
      simpa only [H] using hFH
    have hyG : y ∈ convexHull ℝ (G.1 : Set E) := by
      apply (convex_convexHull ℝ (G.1 : Set E)).sum_mem hnw₀ hnwsum
      intro F hF
      have hFGc : F ≤ Gc := (support.erase Hc).le_max' F hF
      exact (convexHull_mono hFGc : convexHull ℝ (F.1.1 : Set E) ⊆
        convexHull ℝ (G.1 : Set E)) (faceCenter_mem C F.1)
    have hyscale : (1 - wt Hc) • y =
        ∑ F ∈ support.erase Hc, wt F • faceCenter C F.1 := by
      dsimp [y]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      simp only [nw, smul_smul]
      field_simp [sub_ne_zero.mpr (ne_of_gt ha_lt)]
    have hxdecomp : x =
        wt Hc • faceCenter C H + (1 - wt Hc) • y := by
      rw [hyscale, ← hcenter_support, ← Finset.sum_erase_add _ _ hHsupport]
      simp only [H, add_comm]
    exact ⟨H, hHc, Or.inr ⟨wt Hc, y, G, ha_pos, ha_lt, Gc.2,
      hGH, hyhull, hyG, hxdecomp⟩⟩
  · have hsubset : support ⊆ {Hc} := by
      intro F hF
      simp only [Finset.mem_singleton]
      by_contra hFH
      exact hrest ⟨F, Finset.mem_erase.mpr ⟨hFH, hF⟩⟩
    have heq : support = {Hc} := Finset.Subset.antisymm hsubset
      (Finset.singleton_subset_iff.mpr hHsupport)
    have ha_one : wt Hc = 1 := by simpa [heq] using hsum_support
    have hxcenter : x = faceCenter C H := by
      simpa [heq, ha_one, H] using hcenter_support.symm
    exact ⟨H, hHc, Or.inl hxcenter⟩

/-- Unless a point is the centroid of a simplex, it is a convex
combination of that centroid and a point in a proper facet. -/
lemma exists_centroid_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (s : Finset E) (hs : s.Nonempty) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) (hne : x ≠ s.centroid ℝ id) :
    ∃ v ∈ s, (s.erase v).Nonempty ∧
      ∃ (a : ℝ) (y : E), 0 ≤ a ∧ a < 1 ∧
        y ∈ convexHull ℝ ((s.erase v : Finset E) : Set E) ∧
        x = a • s.centroid ℝ id + (1 - a) • y := by
  classical
  obtain ⟨w, hw₀, hw₁, hwcenter⟩ := Finset.mem_convexHull'.mp hx
  obtain ⟨v, hv, hvmin⟩ := Finset.exists_min_image s w hs
  let m : ℝ := w v
  let n : ℝ := s.card
  let a : ℝ := n * m
  have hm₀ : 0 ≤ m := hw₀ v hv
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast hs.card_pos
  have hsum_const_le : ∑ u ∈ s, m ≤ ∑ u ∈ s, w u := by
    apply Finset.sum_le_sum
    intro u hu
    exact hvmin u hu
  have hconst : ∑ u ∈ s, m = n * m := by
    simp [n]
  have ha_le : a ≤ 1 := by
    rw [hconst, hw₁] at hsum_const_le
    exact hsum_const_le
  have ha_ne : a ≠ 1 := by
    intro ha
    have hsum_eq : ∑ u ∈ s, m = ∑ u ∈ s, w u := by
      rw [hconst, hw₁]
      exact ha
    have hall : ∀ u ∈ s, m = w u :=
      (Finset.sum_eq_sum_iff_of_le fun u hu => hvmin u hu).mp hsum_eq
    have hm : m = (s.card : ℝ)⁻¹ := by
      have hnne : n ≠ 0 := ne_of_gt hnpos
      dsimp [a] at ha
      dsimp [n] at hnne ⊢
      rw [inv_eq_one_div]
      apply (eq_div_iff hnne).mpr
      nlinarith
    apply hne
    rw [← hwcenter]
    rw [Finset.centroid_def,
      Finset.affineCombination_eq_linear_combination _ _ _
        (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
    apply Finset.sum_congr rfl
    intro u hu
    rw [← hall u hu, hm]
    rfl
  have ha_lt : a < 1 := lt_of_le_of_ne ha_le ha_ne
  have herase : (s.erase v).Nonempty := by
    by_contra he
    have hsub : s ⊆ {v} := by
      intro u hu
      simp only [Finset.mem_singleton]
      by_contra huv
      exact he ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩⟩
    have hsone : s = {v} := Finset.Subset.antisymm hsub
      (Finset.singleton_subset_iff.mpr hv)
    subst s
    have hxv : x = v := by simpa using hx
    apply hne
    rw [hxv]
    exact (Finset.centroid_singleton (k := ℝ) id v).symm
  let q : E → ℝ := fun u => (w u - m) / (1 - a)
  have hq₀ (u : E) (hu : u ∈ s.erase v) : 0 ≤ q u := by
    apply div_nonneg
    · exact sub_nonneg.mpr (hvmin u (Finset.mem_of_mem_erase hu))
    · exact sub_nonneg.mpr ha_lt.le
  have hsum_sub : ∑ u ∈ s, (w u - m) = 1 - a := by
    rw [Finset.sum_sub_distrib, hw₁, hconst]
  have hsum_erase_sub : ∑ u ∈ s.erase v, (w u - m) = 1 - a := by
    calc
      ∑ u ∈ s.erase v, (w u - m) =
          ∑ u ∈ s.erase v, (w u - m) + (w v - m) := by simp [m]
      _ = ∑ u ∈ s, (w u - m) := Finset.sum_erase_add _ _ hv
      _ = 1 - a := hsum_sub
  have hqsum : ∑ u ∈ s.erase v, q u = 1 := by
    simp only [q, ← Finset.sum_div, hsum_erase_sub]
    exact div_self (sub_ne_zero.mpr (ne_of_gt ha_lt))
  let y : E := ∑ u ∈ s.erase v, q u • u
  have hy : y ∈ convexHull ℝ ((s.erase v : Finset E) : Set E) := by
    rw [Finset.mem_convexHull']
    exact ⟨q, hq₀, hqsum, rfl⟩
  have hcentroid : s.centroid ℝ id =
      ∑ u ∈ s, (s.card : ℝ)⁻¹ • u := by
    rw [Finset.centroid_def,
      Finset.affineCombination_eq_linear_combination _ _ _
        (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
    rfl
  have hyscale : (1 - a) • y = ∑ u ∈ s, (w u - m) • u := by
    dsimp [y]
    rw [Finset.smul_sum]
    calc
      ∑ u ∈ s.erase v, (1 - a) • q u • u =
          ∑ u ∈ s.erase v, (w u - m) • u := by
        apply Finset.sum_congr rfl
        intro u hu
        simp only [q, smul_smul]
        field_simp [sub_ne_zero.mpr (ne_of_gt ha_lt)]
      _ = ∑ u ∈ s, (w u - m) • u := by
        calc
          ∑ u ∈ s.erase v, (w u - m) • u =
              ∑ u ∈ s.erase v, (w u - m) • u + (w v - m) • v := by
            simp [m]
          _ = ∑ u ∈ s, (w u - m) • u := Finset.sum_erase_add _ _ hv
  have hacenter : a • s.centroid ℝ id = ∑ u ∈ s, m • u := by
    rw [hcentroid, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    simp only [smul_smul]
    have hnne : n ≠ 0 := ne_of_gt hnpos
    dsimp [a, n] at hnne ⊢
    congr 1
    field_simp [hnne]
  refine ⟨v, hv, herase, a, y, mul_nonneg (by positivity) hm₀,
    ha_lt, hy, ?_⟩
  rw [hacenter, hyscale, ← hwcenter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← add_smul]
  congr 1
  ring

/-- Every point of an original simplex lies in a simplex spanned by a
chain of its nonempty faces. -/
lemma exists_faceChain_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) (F : GeometricFace C) {x : E}
    (hx : x ∈ convexHull ℝ (F.1 : Set E)) :
    ∃ c : Finset (GeometricFace C), IsFaceChain C c ∧
      (∀ G ∈ c, G ≤ F) ∧ x ∈ convexHull ℝ (chainCenters C c : Set E) := by
  classical
  let P : Finset E → Prop := fun s =>
    ∀ (hs : s ∈ C.K.faces) (x : E), x ∈ convexHull ℝ (s : Set E) →
      ∃ c : Finset (GeometricFace C), IsFaceChain C c ∧
        (∀ G ∈ c, G ≤ (⟨s, hs⟩ : GeometricFace C)) ∧
        x ∈ convexHull ℝ (chainCenters C c : Set E)
  have hP : ∀ s, (∀ t ⊂ s, P t) → P s := by
    intro s ih hs x hx
    let Fs : GeometricFace C := ⟨s, hs⟩
    by_cases hxc : x = faceCenter C Fs
    · let c : Finset (GeometricFace C) := {Fs}
      refine ⟨c, ?_, ?_, ?_⟩
      · refine ⟨Finset.singleton_nonempty Fs, ?_⟩
        intro G hG H hH
        simp only [c, Finset.mem_singleton] at hG hH
        subst G
        subst H
        exact Or.inl le_rfl
      · intro G hG
        simp only [c, Finset.mem_singleton] at hG
        subst G
        exact le_rfl
      · rw [hxc]
        apply subset_convexHull
        rw [Finset.mem_coe, mem_chainCenters]
        exact ⟨Fs, by simp [c], rfl⟩
    · obtain ⟨v, hv, herase, a, y, ha₀, ha₁, hy, hxy⟩ :=
        exists_centroid_decomposition s (C.K.nonempty_of_mem_faces hs) hx hxc
      let t := s.erase v
      have hts : t ⊂ s := by
        refine ⟨Finset.erase_subset v s, ?_⟩
        intro hst
        have : v ∈ s.erase v := hst hv
        exact (Finset.notMem_erase v s) this
      have htface : t ∈ C.K.faces :=
        C.K.down_closed hs (Finset.erase_subset v s) herase
      obtain ⟨c, hc, hcsub, hyc⟩ := ih t hts htface y hy
      let d : Finset (GeometricFace C) := insert Fs c
      have htFs : (⟨t, htface⟩ : GeometricFace C) < Fs := by
        exact hts
      have hchain : IsFaceChain C d := by
        refine ⟨⟨Fs, Finset.mem_insert_self Fs c⟩, ?_⟩
        intro G hG H hH
        simp only [d, Finset.mem_insert] at hG hH
        rcases hG with rfl | hGc
        · rcases hH with rfl | hHc
          · exact Or.inl le_rfl
          · exact Or.inr ((hcsub H hHc).trans htFs.le)
        · rcases hH with rfl | hHc
          · exact Or.inl ((hcsub G hGc).trans htFs.le)
          · exact hc.2 G hGc H hHc
      refine ⟨d, hchain, ?_, ?_⟩
      · intro G hG
        simp only [d, Finset.mem_insert] at hG
        rcases hG with rfl | hGc
        · exact le_rfl
        · exact (hcsub G hGc).trans htFs.le
      · rw [hxy]
        have hcenter : faceCenter C Fs ∈
            convexHull ℝ (chainCenters C d : Set E) := by
          apply subset_convexHull
          rw [Finset.mem_coe, mem_chainCenters]
          exact ⟨Fs, Finset.mem_insert_self Fs c, rfl⟩
        have hy' : y ∈ convexHull ℝ (chainCenters C d : Set E) := by
          apply convexHull_mono _ hyc
          intro z hz
          rw [Finset.mem_coe] at hz ⊢
          exact chainCenters_mono C (Finset.subset_insert Fs c) hz
        exact (convex_convexHull ℝ (chainCenters C d : Set E))
          hcenter hy' ha₀ (sub_nonneg.mpr ha₁.le) (by ring)
  exact Finset.strongInductionOn (p := P) F.1 hP F.2 x hx

/-- A positive coefficient on a face centroid makes every vertex of that
face occur in the minimal simplex containing the resulting point. -/
lemma face_subset_of_pos_center_combo_mem_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) (F : GeometricFace C)
    {s : Finset E} (hsF : s ⊆ F.1) {a : ℝ} {y : E}
    (ha : 0 < a) (ha1 : a ≤ 1)
    (hy : y ∈ convexHull ℝ (F.1 : Set E))
    (hx : a • faceCenter C F + (1 - a) • y ∈ convexHull ℝ (s : Set E)) :
    F.1 ⊆ s := by
  classical
  obtain ⟨w, hw₀, hw₁, hwcenter⟩ := Finset.mem_convexHull'.mp hy
  let q : F.1 → ℝ := fun v =>
    a * (F.1.card : ℝ)⁻¹ + (1 - a) * w v.1
  have hcardpos : 0 < (F.1.card : ℝ) := by
    exact_mod_cast (C.K.nonempty_of_mem_faces F.2).card_pos
  have hcardne : (F.1.card : ℝ) ≠ 0 := ne_of_gt hcardpos
  have hq₀ (v : F.1) : 0 ≤ q v := by
    apply add_nonneg
    · exact mul_nonneg ha.le (inv_nonneg.mpr hcardpos.le)
    · exact mul_nonneg (sub_nonneg.mpr ha1) (hw₀ v.1 v.2)
  have hqpos (v : F.1) : 0 < q v := by
    have hfirst : 0 < a * (F.1.card : ℝ)⁻¹ :=
      mul_pos ha (inv_pos.mpr hcardpos)
    exact add_pos_of_pos_of_nonneg hfirst
      (mul_nonneg (sub_nonneg.mpr ha1) (hw₀ v.1 v.2))
  have hsumw : ∑ v : F.1, w v.1 = 1 := by
    rw [← Finset.sum_subtype F.1 (by simp)]
    exact hw₁
  have hsumconst : ∑ _v : F.1, a * (F.1.card : ℝ)⁻¹ = a := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    field_simp [hcardne]
  have hqsum : ∑ v : F.1, q v = 1 := by
    change ∑ v : F.1,
      (a * (F.1.card : ℝ)⁻¹ + (1 - a) * w v.1) = 1
    rw [Finset.sum_add_distrib, hsumconst, ← Finset.mul_sum, hsumw]
    ring
  have hcentroid : faceCenter C F =
      ∑ v : F.1, (F.1.card : ℝ)⁻¹ • (v.1 : E) := by
    change F.1.centroid ℝ id = _
    rw [Finset.centroid_def,
      Finset.affineCombination_eq_linear_combination _ _ _
        (F.1.sum_centroidWeights_eq_one_of_nonempty ℝ
          (C.K.nonempty_of_mem_faces F.2))]
    rw [Finset.univ_eq_attach, Finset.sum_attach]
    rfl
  have hy' : y = ∑ v : F.1, w v.1 • (v.1 : E) := by
    calc
      y = ∑ v ∈ F.1, w v • v := hwcenter.symm
      _ = ∑ v : F.1, w v.1 • (v.1 : E) :=
        Finset.sum_subtype F.1 (by simp) fun v => w v • v
  have hcombo : Finset.univ.affineCombination ℝ
      (fun v : F.1 => (v.1 : E)) q =
      a • faceCenter C F + (1 - a) • y := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hqsum,
      hcentroid, hy', Finset.smul_sum, Finset.smul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [q, add_smul, mul_smul]
  intro v hvF
  by_contra hvs
  let t : Set F.1 := {u | (u.1 : E) ∈ s}
  have hmem : Finset.univ.affineCombination ℝ
      (fun u : F.1 => (u.1 : E)) q ∈
      affineSpan ℝ ((fun u : F.1 => (u.1 : E)) '' t) := by
    rw [hcombo]
    apply (convexHull_min (s := (s : Set E))
      (t := affineSpan ℝ ((fun u : F.1 => (u.1 : E)) '' t)) ?_
      (AffineSubspace.convex _)) hx
    intro z hz
    exact subset_affineSpan ℝ _ ⟨⟨z, hsF hz⟩, hz, rfl⟩
  let vi : F.1 := ⟨v, hvF⟩
  have hvit : vi ∉ t := hvs
  have hzero := (C.K.indep F.2).eq_zero_of_affineCombination_mem_affineSpan
    hqsum hmem (Finset.mem_univ vi) hvit
  exact (ne_of_gt (hqpos vi)) hzero

lemma faceCenter_ne_combo_of_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) {F G : GeometricFace C}
    (hFG : F < G) {a : ℝ} (ha : a < 1) {y : E}
    (hyF : y ∈ convexHull ℝ (F.1 : Set E)) :
    faceCenter C G ≠ a • faceCenter C G + (1 - a) • y := by
  intro h
  have hscale : (1 - a) • faceCenter C G = (1 - a) • y := by
    calc
      (1 - a) • faceCenter C G = faceCenter C G - a • faceCenter C G := by module
      _ = (a • faceCenter C G + (1 - a) • y) - a • faceCenter C G := by
        nth_rw 1 [h]
      _ = (1 - a) • y := by module
  have hcy : faceCenter C G = y :=
    smul_right_injective E (sub_ne_zero.mpr (ne_of_gt ha)) hscale
  apply faceCenter_not_mem_affineSpan_of_lt C hFG
  rw [← affineSpan_convexHull]
  exact subset_affineSpan ℝ _ (hcy ▸ hyF)

/-- Radial decompositions from a face centroid to proper subfaces are
unique. -/
lemma radial_chain_decomposition_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) (F : GeometricFace C)
    {F' G' : GeometricFace C} (hF'F : F' < F) (hG'F : G' < F)
    {a b : ℝ} {y z : E} (ha₁ : a < 1) (hb₁ : b < 1)
    (hy : y ∈ convexHull ℝ (F'.1 : Set E))
    (hz : z ∈ convexHull ℝ (G'.1 : Set E))
    (heq : a • faceCenter C F + (1 - a) • y =
      b • faceCenter C F + (1 - b) • z) :
    a = b ∧ y = z := by
  have hyF : y ∈ convexHull ℝ (F.1 : Set E) :=
    convexHull_mono hF'F.le hy
  have hzF : z ∈ convexHull ℝ (F.1 : Set E) :=
    convexHull_mono hG'F.le hz
  have not_lt_ab : ¬ a < b := by
    intro hab
    let r : ℝ := (b - a) / (1 - a)
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt ha₁)
    have hr₀ : 0 < r := div_pos (sub_pos.mpr hab) (sub_pos.mpr ha₁)
    have hr₁ : r ≤ 1 := by
      apply (div_le_one (sub_pos.mpr ha₁)).mpr
      linarith
    have hmulr : (1 - a) * r = b - a := by
      dsimp [r]
      field_simp [hden]
    have hmul1r : (1 - a) * (1 - r) = 1 - b := by
      rw [mul_sub, mul_one, hmulr]
      ring
    have hscaled : (1 - a) • y =
        (b - a) • faceCenter C F + (1 - b) • z := by
      calc
        (1 - a) • y =
            (a • faceCenter C F + (1 - a) • y) -
              a • faceCenter C F := by module
        _ = (b • faceCenter C F + (1 - b) • z) -
              a • faceCenter C F := by rw [heq]
        _ = (b - a) • faceCenter C F + (1 - b) • z := by module
    have hyr : y = r • faceCenter C F + (1 - r) • z := by
      apply (smul_right_injective E hden)
      change (1 - a) • y =
        (1 - a) • (r • faceCenter C F + (1 - r) • z)
      rw [smul_add, smul_smul, smul_smul, hmulr, hmul1r]
      exact hscaled
    have hrmem : r • faceCenter C F + (1 - r) • z ∈
        convexHull ℝ (F'.1 : Set E) := by
      rw [← hyr]
      exact hy
    have hfull := face_subset_of_pos_center_combo_mem_convexHull C F
      hF'F.le hr₀ hr₁ hzF hrmem
    exact hF'F.ne (Subtype.ext (Finset.Subset.antisymm hF'F.le hfull))
  have not_lt_ba : ¬ b < a := by
    intro hba
    let r : ℝ := (a - b) / (1 - b)
    have hden : 1 - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hb₁)
    have hr₀ : 0 < r := div_pos (sub_pos.mpr hba) (sub_pos.mpr hb₁)
    have hr₁ : r ≤ 1 := by
      apply (div_le_one (sub_pos.mpr hb₁)).mpr
      linarith
    have hmulr : (1 - b) * r = a - b := by
      dsimp [r]
      field_simp [hden]
    have hmul1r : (1 - b) * (1 - r) = 1 - a := by
      rw [mul_sub, mul_one, hmulr]
      ring
    have hscaled : (1 - b) • z =
        (a - b) • faceCenter C F + (1 - a) • y := by
      calc
        (1 - b) • z =
            (b • faceCenter C F + (1 - b) • z) -
              b • faceCenter C F := by module
        _ = (a • faceCenter C F + (1 - a) • y) -
              b • faceCenter C F := by rw [← heq]
        _ = (a - b) • faceCenter C F + (1 - a) • y := by module
    have hzr : z = r • faceCenter C F + (1 - r) • y := by
      apply (smul_right_injective E hden)
      change (1 - b) • z =
        (1 - b) • (r • faceCenter C F + (1 - r) • y)
      rw [smul_add, smul_smul, smul_smul, hmulr, hmul1r]
      exact hscaled
    have hrmem : r • faceCenter C F + (1 - r) • y ∈
        convexHull ℝ (G'.1 : Set E) := by
      rw [← hzr]
      exact hz
    have hfull := face_subset_of_pos_center_combo_mem_convexHull C F
      hG'F.le hr₀ hr₁ hyF hrmem
    exact hG'F.ne (Subtype.ext (Finset.Subset.antisymm hG'F.le hfull))
  have hab : a = b := le_antisymm (not_lt.mp not_lt_ba) (not_lt.mp not_lt_ab)
  subst b
  refine ⟨rfl, ?_⟩
  have hscale : (1 - a) • y = (1 - a) • z := by
    exact add_left_cancel heq
  exact (smul_right_injective E (sub_ne_zero.mpr (ne_of_gt ha₁))) hscale

lemma mem_face_of_chain_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) (H : GeometricFace C) {x : E}
    (hdec : x = faceCenter C H ∨
      ∃ (a : ℝ) (y : E) (G : GeometricFace C),
        0 < a ∧ a < 1 ∧ G < H ∧
        y ∈ convexHull ℝ (G.1 : Set E) ∧
        x = a • faceCenter C H + (1 - a) • y) :
    x ∈ convexHull ℝ (H.1 : Set E) := by
  rcases hdec with h | ⟨a, y, G, ha₀, ha₁, hGH, hy, hxy⟩
  · rw [h]
    exact faceCenter_mem C H
  · rw [hxy]
    exact (convex_convexHull ℝ (H.1 : Set E)) (faceCenter_mem C H)
      (convexHull_mono hGH.le hy) ha₀.le (sub_nonneg.mpr ha₁.le) (by ring)

lemma face_subset_of_chain_decomposition_mem_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) (H : GeometricFace C) {x : E}
    {s : Finset E} (hsH : s ⊆ H.1)
    (hdec : x = faceCenter C H ∨
      ∃ (a : ℝ) (y : E) (G : GeometricFace C),
        0 < a ∧ a < 1 ∧ G < H ∧
        y ∈ convexHull ℝ (G.1 : Set E) ∧
        x = a • faceCenter C H + (1 - a) • y)
    (hx : x ∈ convexHull ℝ (s : Set E)) : H.1 ⊆ s := by
  rcases hdec with h | ⟨a, y, G, ha₀, ha₁, hGH, hy, hxy⟩
  · apply face_subset_of_center_mem_convexHull C H hsH
    rw [← h]
    exact hx
  · apply face_subset_of_pos_center_combo_mem_convexHull C H hsH
      ha₀ ha₁.le (convexHull_mono hGH.le hy)
    rw [← hxy]
    exact hx

/-- Convex hulls of two face-chain simplices meet only along their
common centroid vertices. -/
theorem convexHull_chainCenters_inter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E)
    (c d : Finset (GeometricFace C)) (hc : IsFaceChain C c)
    (hd : IsFaceChain C d) :
    convexHull ℝ (chainCenters C c : Set E) ∩
        convexHull ℝ (chainCenters C d : Set E) ⊆
      convexHull ℝ ((chainCenters C c : Set E) ∩
        (chainCenters C d : Set E)) := by
  classical
  intro x hx
  obtain ⟨F, hFc, hdecF⟩ := exists_maximal_chain_decomposition C c hc hx.1
  obtain ⟨G, hGd, hdecG⟩ := exists_maximal_chain_decomposition C d hd hx.2
  let decF : Prop := x = faceCenter C F ∨
      ∃ (a : ℝ) (y : E) (F' : GeometricFace C),
        0 < a ∧ a < 1 ∧ F' < F ∧
        y ∈ convexHull ℝ (F'.1 : Set E) ∧
        x = a • faceCenter C F + (1 - a) • y
  have hdecF' : decF := by
    rcases hdecF with h | ⟨a, y, F', ha₀, ha₁, hF'c, hF'F, hyc, hyF', hxy⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, y, F', ha₀, ha₁, hF'F, hyF', hxy⟩
  let decG : Prop := x = faceCenter C G ∨
      ∃ (a : ℝ) (y : E) (G' : GeometricFace C),
        0 < a ∧ a < 1 ∧ G' < G ∧
        y ∈ convexHull ℝ (G'.1 : Set E) ∧
        x = a • faceCenter C G + (1 - a) • y
  have hdecG' : decG := by
    rcases hdecG with h | ⟨a, y, G', ha₀, ha₁, hG'd, hG'G, hyd, hyG', hxy⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, y, G', ha₀, ha₁, hG'G, hyG', hxy⟩
  have hxF : x ∈ convexHull ℝ (F.1 : Set E) :=
    mem_face_of_chain_decomposition C F hdecF'
  have hxG : x ∈ convexHull ℝ (G.1 : Set E) :=
    mem_face_of_chain_decomposition C G hdecG'
  have hxinter : x ∈ convexHull ℝ ((F.1 ∩ G.1 : Finset E) : Set E) := by
    simpa only [Finset.coe_inter] using
      C.K.inter_subset_convexHull F.2 G.2 ⟨hxF, hxG⟩
  have hFsub : F.1 ⊆ F.1 ∩ G.1 :=
    face_subset_of_chain_decomposition_mem_convexHull C F Finset.inter_subset_left
      hdecF' hxinter
  have hGsub : G.1 ⊆ F.1 ∩ G.1 :=
    face_subset_of_chain_decomposition_mem_convexHull C G Finset.inter_subset_right
      hdecG' hxinter
  have hFG : F = G := by
    apply Subtype.ext
    exact Finset.Subset.antisymm (hFsub.trans Finset.inter_subset_right)
      (hGsub.trans Finset.inter_subset_left)
  subst G
  have hcenter_mem : faceCenter C F ∈
      (chainCenters C c : Set E) ∩ (chainCenters C d : Set E) :=
    ⟨Finset.mem_coe.mpr <| (mem_chainCenters C c (faceCenter C F)).mpr ⟨F, hFc, rfl⟩,
      Finset.mem_coe.mpr <| (mem_chainCenters C d (faceCenter C F)).mpr ⟨F, hGd, rfl⟩⟩
  rcases hdecF with hxc | ⟨a, y, F', ha₀, ha₁, hF'c, hF'F, hyc, hyF', hxy⟩
  · rcases hdecG with hxc' | ⟨b, z, G', hb₀, hb₁, hG'd, hG'F, hzd, hzG', hxz⟩
    · rw [hxc]
      exact subset_convexHull ℝ _ hcenter_mem
    · exfalso
      exact faceCenter_ne_combo_of_lt C hG'F hb₁ hzG' (hxc.symm.trans hxz)
  · rcases hdecG with hxc' | ⟨b, z, G', hb₀, hb₁, hG'd, hG'F, hzd, hzG', hxz⟩
    · exfalso
      exact faceCenter_ne_combo_of_lt C hF'F ha₁ hyF' (hxc'.symm.trans hxy)
    · obtain ⟨hab, hyz⟩ := radial_chain_decomposition_unique C F
        hF'F hG'F ha₁ hb₁ hyF' hzG' (hxy.symm.trans hxz)
      subst b
      subst z
      have hce_nonempty : (eraseFace C c F).Nonempty := by
        by_contra hne
        have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
        rw [hempty, chainCenters, Finset.image_empty, Finset.coe_empty,
          convexHull_empty] at hyc
        exact hyc
      have hde_nonempty : (eraseFace C d F).Nonempty := by
        by_contra hne
        have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
        rw [hempty, chainCenters, Finset.image_empty, Finset.coe_empty,
          convexHull_empty] at hzd
        exact hzd
      have hce : IsFaceChain C (eraseFace C c F) :=
        hc.subset hce_nonempty (Finset.erase_subset F c)
      have hde : IsFaceChain C (eraseFace C d F) :=
        hd.subset hde_nonempty (Finset.erase_subset F d)
      have hy_small := convexHull_chainCenters_inter C
        (eraseFace C c F) (eraseFace C d F) hce hde ⟨hyc, hzd⟩
      have hinter_subset :
          (chainCenters C (eraseFace C c F) : Set E) ∩
              (chainCenters C (eraseFace C d F) : Set E) ⊆
            (chainCenters C c : Set E) ∩ (chainCenters C d : Set E) := by
        intro q hq
        exact
          ⟨Finset.mem_coe.mpr <| chainCenters_mono C (Finset.erase_subset F c)
              (Finset.mem_coe.mp hq.1),
            Finset.mem_coe.mpr <| chainCenters_mono C (Finset.erase_subset F d)
              (Finset.mem_coe.mp hq.2)⟩
      have hy_big : y ∈ convexHull ℝ
          ((chainCenters C c : Set E) ∩ (chainCenters C d : Set E)) :=
        convexHull_mono hinter_subset hy_small
      rw [hxy]
      exact (convex_convexHull ℝ
        ((chainCenters C c : Set E) ∩ (chainCenters C d : Set E)))
          (subset_convexHull ℝ _ hcenter_mem) hy_big
          ha₀.le (sub_nonneg.mpr ha₁.le) (by ring)
termination_by c.card + d.card
decreasing_by
  classical
  simp only [eraseFace]
  exact Nat.add_lt_add (Finset.card_erase_lt_of_mem hFc)
    (Finset.card_erase_lt_of_mem hGd)

/-! ### The barycentric subdivision complex -/

noncomputable def restrictChain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    (c : Finset (GeometricFace C)) (s : Finset E) :
    Finset (GeometricFace C) := by
  classical
  exact c.filter fun F => faceCenter C F ∈ s

@[simp]
lemma mem_restrictChain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    (c : Finset (GeometricFace C)) (s : Finset E) (F : GeometricFace C) :
    F ∈ restrictChain C c s ↔ F ∈ c ∧ faceCenter C F ∈ s := by
  classical
  simp [restrictChain]

lemma restrictChain_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    (c : Finset (GeometricFace C)) (s : Finset E) : restrictChain C c s ⊆ c := by
  intro F hF
  exact (mem_restrictChain C c s F).mp hF |>.1

lemma restrictChain_nonempty {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    {c : Finset (GeometricFace C)} {s : Finset E} (hs : s.Nonempty)
    (hsc : s ⊆ chainCenters C c) : (restrictChain C c s).Nonempty := by
  obtain ⟨x, hxs⟩ := hs
  obtain ⟨F, hFc, hFx⟩ := (mem_chainCenters C c x).mp (hsc hxs)
  exact ⟨F, (mem_restrictChain C c s F).mpr ⟨hFc, hFx ▸ hxs⟩⟩

lemma chainCenters_restrictChain {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    {c : Finset (GeometricFace C)} {s : Finset E} (hsc : s ⊆ chainCenters C c) :
    chainCenters C (restrictChain C c s) = s := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨F, hF, hFx⟩ := (mem_chainCenters C (restrictChain C c s) x).mp hx
    exact hFx ▸ (mem_restrictChain C c s F).mp hF |>.2
  · intro hx
    obtain ⟨F, hFc, hFx⟩ := (mem_chainCenters C c x).mp (hsc hx)
    exact (mem_chainCenters C (restrictChain C c s) x).mpr
      ⟨F, (mem_restrictChain C c s F).mpr ⟨hFc, hFx ▸ hx⟩, hFx⟩

lemma affineIndependent_chainCenters {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    (c : Finset (GeometricFace C)) (hc : IsFaceChain C c) :
    AffineIndependent ℝ ((↑) : chainCenters C c → E) := by
  have h := (affineIndependent_centers_of_isFaceChain C c hc).range
  have hrange : Set.range (fun F : c => faceCenter C F.1) =
      (chainCenters C c : Set E) := by
    ext x
    constructor
    · rintro ⟨F, rfl⟩
      exact Finset.mem_coe.mpr <|
        (mem_chainCenters C c (faceCenter C F.1)).mpr ⟨F.1, F.2, rfl⟩
    · intro hx
      obtain ⟨F, hFc, hFx⟩ := (mem_chainCenters C c x).mp (Finset.mem_coe.mp hx)
      exact ⟨⟨F, hFc⟩, hFx⟩
  refine h.mono ?_
  simpa only [hrange] using (Set.Subset.rfl :
    (Set.range fun F : c => faceCenter C F.1) ⊆
      Set.range fun F : c => faceCenter C F.1)

/-- The barycentric subdivision of a finite geometric complex. -/
noncomputable def barycentricComplex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) :
    Geometry.SimplicialComplex ℝ E := by
  classical
  exact
    { faces := {s | ∃ c : Finset (GeometricFace C),
        IsFaceChain C c ∧ s = chainCenters C c}
      isRelLowerSet_faces := by
        rintro s ⟨c, hc, rfl⟩
        constructor
        · rw [chainCenters]
          exact Finset.image_nonempty.mpr hc.1
        · intro t hts ht
          let d := restrictChain C c t
          have hdne : d.Nonempty := restrictChain_nonempty C ht hts
          have hd : IsFaceChain C d := hc.subset hdne (restrictChain_subset C c t)
          exact ⟨d, hd, (chainCenters_restrictChain C hts).symm⟩
      indep := by
        rintro s ⟨c, hc, rfl⟩
        exact affineIndependent_chainCenters C c hc
      inter_subset_convexHull := by
        rintro s t ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
        simpa only [Finset.coe_inter] using
          convexHull_chainCenters_inter C c d hc hd }

@[simp]
lemma mem_barycentricComplex_faces {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) (s : Finset E) :
    s ∈ (barycentricComplex C).faces ↔
      ∃ c : Finset (GeometricFace C), IsFaceChain C c ∧ s = chainCenters C c :=
  Iff.rfl

lemma finite_barycentricComplex_faces {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) :
    (barycentricComplex C).faces.Finite := by
  classical
  let V : Finset E := Finset.univ.image (faceCenter C)
  refine V.powerset.finite_toSet.subset ?_
  intro s hs
  obtain ⟨c, _hc, rfl⟩ := hs
  apply Finset.mem_powerset.mpr
  intro x hx
  obtain ⟨F, _hFc, rfl⟩ := (mem_chainCenters C c x).mp hx
  exact Finset.mem_image.mpr ⟨F, Finset.mem_univ F, rfl⟩

lemma barycentricComplex_space {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) :
    (barycentricComplex C).space = C.K.space := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Geometry.SimplicialComplex.mem_space_iff] at hx ⊢
    obtain ⟨s, ⟨c, hc, rfl⟩, hxs⟩ := hx
    obtain ⟨H, hHc, hdec⟩ := exists_maximal_chain_decomposition C c hc hxs
    refine ⟨H.1, H.2, ?_⟩
    rcases hdec with h | ⟨a, y, G, ha₀, ha₁, hGc, hGH, hyc, hyG, hxy⟩
    · rw [h]
      exact faceCenter_mem C H
    · rw [hxy]
      exact (convex_convexHull ℝ (H.1 : Set E)) (faceCenter_mem C H)
        (convexHull_mono hGH.le hyG) ha₀.le (sub_nonneg.mpr ha₁.le) (by ring)
  · intro x hx
    rw [Geometry.SimplicialComplex.mem_space_iff] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    let F : GeometricFace C := ⟨s, hs⟩
    obtain ⟨c, hc, _hcF, hxc⟩ := exists_faceChain_cover C F hxs
    exact ⟨chainCenters C c, ⟨c, hc, rfl⟩, hxc⟩

/-- Barycentric subdivision bundled again as a finite complex. -/
noncomputable def barycentricSubdivision {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) :
    FiniteGeometricComplex E where
  K := barycentricComplex C
  finite_faces := finite_barycentricComplex_faces C

/-! ### Mesh contraction -/

lemma centroid_eq_inv_smul_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset E) (hs : s.Nonempty) :
    s.centroid ℝ id = (s.card : ℝ)⁻¹ • ∑ x ∈ s, x := by
  rw [Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rfl

lemma dist_centroid_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : Finset E} (hA : A.Nonempty) (hAB : A ⊆ B) :
    dist (A.centroid ℝ id) (B.centroid ℝ id) ≤
      ((B.card - 1 : ℕ) : ℝ) / B.card * Metric.diam (B : Set E) := by
  classical
  have hB : B.Nonempty := hA.mono hAB
  by_cases hD : (B \ A).Nonempty
  · let cA : E := A.centroid ℝ id
    let cB : E := B.centroid ℝ id
    let cD : E := (B \ A).centroid ℝ id
    let n : ℝ := B.card
    let k : ℝ := A.card
    let l : ℝ := (B \ A).card
    have hnpos : 0 < n := by
      dsimp [n]
      exact_mod_cast hB.card_pos
    have hkpos : 0 < k := by
      dsimp [k]
      exact_mod_cast hA.card_pos
    have hlpos : 0 < l := by
      dsimp [l]
      exact_mod_cast hD.card_pos
    have hcard : l + k = n := by
      dsimp [l, k, n]
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hAB
    have hcA : cA = k⁻¹ • ∑ x ∈ A, x := by
      exact centroid_eq_inv_smul_sum A hA
    have hcB : cB = n⁻¹ • ∑ x ∈ B, x := by
      exact centroid_eq_inv_smul_sum B hB
    have hcD : cD = l⁻¹ • ∑ x ∈ B \ A, x := by
      exact centroid_eq_inv_smul_sum (B \ A) hD
    have hsum : ∑ x ∈ B \ A, x + ∑ x ∈ A, x = ∑ x ∈ B, x :=
      Finset.sum_sdiff hAB
    have hcBcombo : cB = (k / n) • cA + (l / n) • cD := by
      rw [hcA, hcB, hcD]
      have hnne : n ≠ 0 := ne_of_gt hnpos
      have hkne : k ≠ 0 := ne_of_gt hkpos
      have hlne : l ≠ 0 := ne_of_gt hlpos
      rw [smul_smul, smul_smul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      field_simp [hnne, hkne, hlne]
      rw [← hsum]
      module
    have hcoeff : k / n + l / n = 1 := by
      rw [← add_div, add_comm k l, hcard]
      exact div_self (ne_of_gt hnpos)
    have hscalar : 1 - k / n = l / n := by linarith
    have hdist : dist cA cB = (l / n) * dist cA cD := by
      rw [dist_eq_norm, hcBcombo]
      have hnonneg : 0 ≤ l / n := div_nonneg hlpos.le hnpos.le
      calc
        ‖cA - ((k / n) • cA + (l / n) • cD)‖ =
            ‖(l / n) • (cA - cD)‖ := by
          congr 1
          calc
            cA - ((k / n) • cA + (l / n) • cD) =
                (1 - k / n) • cA - (l / n) • cD := by module
            _ = (l / n) • (cA - cD) := by rw [hscalar]; module
        _ = (l / n) * ‖cA - cD‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        _ = (l / n) * dist cA cD := by rw [dist_eq_norm]
    have hcAmem : cA ∈ convexHull ℝ (B : Set E) :=
      convexHull_mono hAB (A.centroid_mem_convexHull hA)
    have hcDmem : cD ∈ convexHull ℝ (B : Set E) :=
      convexHull_mono (Finset.sdiff_subset : B \ A ⊆ B)
        ((B \ A).centroid_mem_convexHull hD)
    have hdiam : dist cA cD ≤ Metric.diam (B : Set E) := by
      have h := Metric.dist_le_diam_of_mem
        (isBounded_convexHull.mpr B.finite_toSet.isBounded) hcAmem hcDmem
      rwa [convexHull_diam] at h
    have hlNat : (B \ A).card ≤ B.card - 1 := by
      have hkNat : 0 < A.card := hA.card_pos
      have hcardNat := Finset.card_sdiff_add_card_eq_card hAB
      omega
    have hl : l ≤ ((B.card - 1 : ℕ) : ℝ) := by
      dsimp [l]
      exact_mod_cast hlNat
    rw [hdist]
    calc
      (l / n) * dist cA cD ≤ (l / n) * Metric.diam (B : Set E) :=
        mul_le_mul_of_nonneg_left hdiam (div_nonneg hlpos.le hnpos.le)
      _ ≤ (((B.card - 1 : ℕ) : ℝ) / n) * Metric.diam (B : Set E) := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hl hnpos.le) Metric.diam_nonneg
      _ = ((B.card - 1 : ℕ) : ℝ) / B.card * Metric.diam (B : Set E) := by
        rfl
  · have hBA : B ⊆ A := by
      intro x hxB
      by_contra hxA
      exact hD ⟨x, Finset.mem_sdiff.mpr ⟨hxB, hxA⟩⟩
    have hEq : A = B := Finset.Subset.antisymm hAB hBA
    subst B
    rw [dist_self]
    exact mul_nonneg (div_nonneg (by positivity) (by positivity)) Metric.diam_nonneg

def faceDiameter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E)
    (F : GeometricFace C) : ℝ := Metric.diam (F.1 : Set E)

noncomputable def complexMesh {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) : ℝ := by
  let s : Finset ℝ := insert 0 (Finset.univ.image (faceDiameter C))
  exact s.max' ⟨0, Finset.mem_insert_self 0 _⟩

lemma complexMesh_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) : 0 ≤ complexMesh C := by
  classical
  dsimp [complexMesh]
  apply Finset.le_max'
  exact Finset.mem_insert_self 0 _

lemma faceDiameter_le_complexMesh {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : FiniteGeometricComplex E) (F : GeometricFace C) :
    faceDiameter C F ≤ complexMesh C := by
  classical
  dsimp [complexMesh]
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨F, Finset.mem_univ F, rfl⟩)

def subdivisionRatio (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : ℝ :=
  (Module.finrank ℝ E : ℝ) / (Module.finrank ℝ E + 1)

lemma subdivisionRatio_nonneg (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : 0 ≤ subdivisionRatio E := by
  exact div_nonneg (by positivity) (by positivity)

lemma subdivisionRatio_lt_one (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : subdivisionRatio E < 1 := by
  apply (div_lt_one (by positivity : (0 : ℝ) < Module.finrank ℝ E + 1)).mpr
  exact_mod_cast Nat.lt_succ_self (Module.finrank ℝ E)

lemma face_card_ratio_le_subdivisionRatio
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (C : FiniteGeometricComplex E)
    (F : GeometricFace C) :
    ((F.1.card - 1 : ℕ) : ℝ) / F.1.card ≤ subdivisionRatio E := by
  have hcardposNat : 0 < F.1.card := (C.K.nonempty_of_mem_faces F.2).card_pos
  have hcardpos : 0 < (F.1.card : ℝ) := by exact_mod_cast hcardposNat
  have hdimpos : 0 < (Module.finrank ℝ E + 1 : ℝ) := by positivity
  have hcard0 := (C.K.indep F.2).card_le_finrank_succ
  rw [Fintype.card_coe] at hcard0
  have hcard : F.1.card ≤ Module.finrank ℝ E + 1 :=
    hcard0.trans (Nat.add_le_add_right
      (vectorSpan ℝ (Set.range ((↑) : F.1 → E))).finrank_le 1)
  have hcardR : (F.1.card : ℝ) ≤ (Module.finrank ℝ E + 1 : ℝ) := by
    exact_mod_cast hcard
  rw [subdivisionRatio]
  apply (div_le_div_iff₀ hcardpos hdimpos).mpr
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hcardposNat.ne')]
  push_cast
  nlinarith

lemma chainCenters_diam_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (C : FiniteGeometricComplex E)
    (c : Finset (GeometricFace C)) (hc : IsFaceChain C c) :
    Metric.diam (chainCenters C c : Set E) ≤
      subdivisionRatio E * complexMesh C := by
  apply Metric.diam_le_of_forall_dist_le
    (mul_nonneg (subdivisionRatio_nonneg E) (complexMesh_nonneg C))
  intro x hx y hy
  rw [Finset.mem_coe] at hx hy
  obtain ⟨F, hFc, hFx⟩ := (mem_chainCenters C c x).mp hx
  obtain ⟨G, hGc, hGy⟩ := (mem_chainCenters C c y).mp hy
  subst x
  subst y
  rcases hc.2 F hFc G hGc with hFG | hGF
  · calc
      dist (faceCenter C F) (faceCenter C G) ≤
          ((G.1.card - 1 : ℕ) : ℝ) / G.1.card * faceDiameter C G := by
        exact dist_centroid_le (C.K.nonempty_of_mem_faces F.2) hFG
      _ ≤ subdivisionRatio E * faceDiameter C G := by
        exact mul_le_mul_of_nonneg_right
          (face_card_ratio_le_subdivisionRatio C G) Metric.diam_nonneg
      _ ≤ subdivisionRatio E * complexMesh C := by
        exact mul_le_mul_of_nonneg_left (faceDiameter_le_complexMesh C G)
          (subdivisionRatio_nonneg E)
  · rw [dist_comm]
    calc
      dist (faceCenter C G) (faceCenter C F) ≤
          ((F.1.card - 1 : ℕ) : ℝ) / F.1.card * faceDiameter C F := by
        exact dist_centroid_le (C.K.nonempty_of_mem_faces G.2) hGF
      _ ≤ subdivisionRatio E * faceDiameter C F := by
        exact mul_le_mul_of_nonneg_right
          (face_card_ratio_le_subdivisionRatio C F) Metric.diam_nonneg
      _ ≤ subdivisionRatio E * complexMesh C := by
        exact mul_le_mul_of_nonneg_left (faceDiameter_le_complexMesh C F)
          (subdivisionRatio_nonneg E)

lemma complexMesh_barycentricSubdivision_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (C : FiniteGeometricComplex E) :
    complexMesh (barycentricSubdivision C) ≤
      subdivisionRatio E * complexMesh C := by
  classical
  unfold complexMesh
  rw [Finset.max'_le_iff]
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hr
  rcases hr with rfl | ⟨F, rfl⟩
  · exact mul_nonneg (subdivisionRatio_nonneg E) (complexMesh_nonneg C)
  · change Metric.diam (F.1 : Set E) ≤ subdivisionRatio E * complexMesh C
    have hface := F.2
    change F.1 ∈ (barycentricComplex C).faces at hface
    obtain ⟨c, hc, hFc⟩ := hface
    rw [hFc]
    exact chainCenters_diam_le C c hc

noncomputable def iteratedSubdivision
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) : ℕ → FiniteGeometricComplex E
  | 0 => C
  | n + 1 => barycentricSubdivision (iteratedSubdivision C n)

@[simp]
lemma iteratedSubdivision_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) : iteratedSubdivision C 0 = C := rfl

@[simp]
lemma iteratedSubdivision_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) (n : ℕ) :
    iteratedSubdivision C (n + 1) =
      barycentricSubdivision (iteratedSubdivision C n) := rfl

lemma iteratedSubdivision_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FiniteGeometricComplex E) (n : ℕ) :
    (iteratedSubdivision C n).K.space = C.K.space := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedSubdivision_succ]
      change (barycentricComplex (iteratedSubdivision C n)).space = C.K.space
      rw [barycentricComplex_space, ih]

lemma complexMesh_iteratedSubdivision_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (C : FiniteGeometricComplex E) (n : ℕ) :
    complexMesh (iteratedSubdivision C n) ≤
      (subdivisionRatio E) ^ n * complexMesh C := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        complexMesh (iteratedSubdivision C (n + 1)) ≤
            subdivisionRatio E * complexMesh (iteratedSubdivision C n) :=
          complexMesh_barycentricSubdivision_le _
        _ ≤ subdivisionRatio E *
            ((subdivisionRatio E) ^ n * complexMesh C) :=
          mul_le_mul_of_nonneg_left ih (subdivisionRatio_nonneg E)
        _ = (subdivisionRatio E) ^ (n + 1) * complexMesh C := by
          rw [pow_succ]
          ring

lemma exists_iteratedSubdivision_mesh_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (C : FiniteGeometricComplex E)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ n : ℕ, complexMesh (iteratedSubdivision C n) < eps := by
  by_cases hm : complexMesh C = 0
  · exact ⟨0, by simpa [hm] using heps⟩
  · have hmpos : 0 < complexMesh C :=
      lt_of_le_of_ne (complexMesh_nonneg C) (Ne.symm hm)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (div_pos heps hmpos) (subdivisionRatio_lt_one E)
    refine ⟨n, (complexMesh_iteratedSubdivision_le C n).trans_lt ?_⟩
    apply (lt_div_iff₀ hmpos).mp at hn
    simpa [mul_comm, mul_left_comm, mul_assoc] using hn

end

end Submission.Helpers.DehnSommerville
