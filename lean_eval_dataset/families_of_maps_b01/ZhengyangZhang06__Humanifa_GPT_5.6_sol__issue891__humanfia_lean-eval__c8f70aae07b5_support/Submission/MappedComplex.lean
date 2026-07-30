import Submission.RankGrid

open Set Geometry

namespace Submission.MappedComplex

open Polytope Polytope.ExposedFace
open ChainCoordinates GridComplex GridDeformation RankGrid

variable {k n : ℕ}

/-- The ambient linear map underlying `rankDecode`. -/
noncomputable def rankDecodeLinear (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c) :
    (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun w := ∑ j, w j • rankVertex S c hc j
  map_add' w z := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a w := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, smul_smul,
      Finset.smul_sum]

@[simp]
theorem rankDecodeLinear_apply (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (w : Fin (k + 1) → ℝ) :
    rankDecodeLinear S c hc w = ∑ j, w j • rankVertex S c hc j :=
  rfl

@[simp]
theorem rankDecode_eq_linear (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (w : stdSimplex ℝ (Fin (k + 1))) :
    rankDecode S c hc w = rankDecodeLinear S c hc w.1 :=
  rfl

/-- Coordinates are supported on the affine ranks occurring in a chain. -/
def SupportedOnRanks (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (w : Fin (k + 1) → ℝ) : Prop :=
  ∀ j, (∀ F : c, rankIndex S F.1 ≠ j) → w j = 0

theorem supportedOnRanks_of_mem_rankFace (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) {w : Fin (k + 1) → ℝ}
    (hw : w ∈ rankFace S c) : SupportedOnRanks S c w := by
  intro j hj
  exact hw.2 j fun F hF => hj ⟨F, hF⟩

theorem sum_rankCoordinates (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (w : Fin (k + 1) → ℝ)
    (hsupport : SupportedOnRanks S c w) :
    ∑ F : c, w (rankIndex S F.1) = ∑ j, w j := by
  classical
  let e : c ↪ Fin (k + 1) :=
    ⟨fun F => rankIndex S F.1, fun F G h => by
      apply Subtype.ext
      exact rankIndex_injective_on_chain S c hc F.2 G.2 h⟩
  have heinj : Function.Injective fun F : c => rankIndex S F.1 := e.injective
  calc
    ∑ F : c, w (rankIndex S F.1) =
        ∑ j ∈ Finset.univ.image (fun F : c => rankIndex S F.1), w j := by
      rw [Finset.sum_image]
      exact heinj.injOn
    _ = ∑ j, w j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _hj hjimage
      apply hsupport j
      intro F hF
      apply hjimage
      exact Finset.mem_image.mpr ⟨F, Finset.mem_univ _, hF⟩

theorem rankDecodeLinear_eq_sum_chain (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (w : Fin (k + 1) → ℝ) (hsupport : SupportedOnRanks S c w) :
    rankDecodeLinear S c hc w =
      ∑ F : c, w (rankIndex S F.1) • F.1.center S := by
  classical
  let e : c ↪ Fin (k + 1) :=
    ⟨fun F => rankIndex S F.1, fun F G h => by
      apply Subtype.ext
      exact rankIndex_injective_on_chain S c hc F.2 G.2 h⟩
  have heinj : Function.Injective fun F : c => rankIndex S F.1 := e.injective
  rw [rankDecodeLinear_apply]
  symm
  calc
    ∑ F : c, w (rankIndex S F.1) • F.1.center S =
        ∑ j ∈ Finset.univ.image (fun F : c => rankIndex S F.1),
          w j • rankVertex S c hc j := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro F _hF
        rw [rankVertex_rank S c hc F]
      · exact heinj.injOn
    _ = ∑ j, w j • rankVertex S c hc j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _hj hjimage
      have hwj : w j = 0 := by
        apply hsupport j
        intro F hF
        apply hjimage
        exact Finset.mem_image.mpr ⟨F, Finset.mem_univ _, hF⟩
      simp [hwj]

theorem rankDecodeLinear_injective_of_sum_eq_one
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S))
    (hc : IsChain S c) {w z : Fin (k + 1) → ℝ}
    (hw_sum : ∑ j, w j = 1) (hz_sum : ∑ j, z j = 1)
    (hw_support : SupportedOnRanks S c w)
    (hz_support : SupportedOnRanks S c z)
    (hdecode : rankDecodeLinear S c hc w = rankDecodeLinear S c hc z) :
    w = z := by
  classical
  let wc : c → ℝ := fun F => w (rankIndex S F.1)
  let zc : c → ℝ := fun F => z (rankIndex S F.1)
  have hwc_sum : ∑ F, wc F = 1 := by
    rw [show (∑ F, wc F) = ∑ j, w j from sum_rankCoordinates S c hc w hw_support,
      hw_sum]
  have hzc_sum : ∑ F, zc F = 1 := by
    rw [show (∑ F, zc F) = ∑ j, z j from sum_rankCoordinates S c hc z hz_support,
      hz_sum]
  have hcomb : Finset.univ.affineCombination ℝ
      (fun F : c => F.1.center S) wc =
      Finset.univ.affineCombination ℝ (fun F : c => F.1.center S) zc := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hwc_sum,
      Finset.affineCombination_eq_linear_combination _ _ _ hzc_sum]
    rw [← rankDecodeLinear_eq_sum_chain S c hc w hw_support,
      ← rankDecodeLinear_eq_sum_chain S c hc z hz_support]
    exact hdecode
  have hcoords : wc = zc := by
    apply funext
    intro F
    exact ((affineIndependent_centers_of_isChain S c hc).affineCombination_eq_iff_eq
      hwc_sum hzc_sum).mp hcomb F (Finset.mem_univ F)
  funext j
  by_cases hj : ∃ F : c, rankIndex S F.1 = j
  · obtain ⟨F, rfl⟩ := hj
    exact congrFun hcoords F
  · have hj' : ∀ F : c, rankIndex S F.1 ≠ j := fun F hF => hj ⟨F, hF⟩
    rw [hw_support j hj', hz_support j hj']

theorem sum_affineCombination_coordinates_eq_one
    {α : Type*} [Fintype α] (p : α → Fin (k + 1) → ℝ)
    (hp : ∀ i, ∑ j, p i j = 1) (a : α → ℝ) (ha : ∑ i, a i = 1) :
    ∑ j, (Finset.univ.affineCombination ℝ p a) j = 1 := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ ha]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    ∑ j, ∑ i, a i * p i j = ∑ i, ∑ j, a i * p i j := Finset.sum_comm
    _ = ∑ i, a i * ∑ j, p i j := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ = ∑ i, a i := by simp [hp]
    _ = 1 := ha

theorem supportedOnRanks_affineCombination
    {α : Type*} [Fintype α] (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (p : α → Fin (k + 1) → ℝ)
    (hp : ∀ i, SupportedOnRanks S c (p i)) (a : α → ℝ)
    (ha : ∑ i, a i = 1) :
    SupportedOnRanks S c (Finset.univ.affineCombination ℝ p a) := by
  intro j hj
  rw [Finset.affineCombination_eq_linear_combination _ _ _ ha]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [hp i j hj, mul_zero]

theorem affineIndependent_rankDecode_of_subset_rankFace
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S))
    (hc : IsChain S c) (s : Finset (WeightSpace k))
    (hsind : AffineIndependent ℝ ((↑) : s → WeightSpace k))
    (hsrank : (s : Set (WeightSpace k)) ⊆ rankFace S c) :
    AffineIndependent ℝ
      (fun w : s => rankDecodeLinear S c hc w.1) := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro a b ha hb hab
  let p : s → WeightSpace k := (↑)
  let wa := Finset.univ.affineCombination ℝ p a
  let wb := Finset.univ.affineCombination ℝ p b
  have hp_sum : ∀ i, ∑ j, p i j = 1 := by
    intro i
    exact (hsrank i.2).1.2
  have hp_support : ∀ i, SupportedOnRanks S c (p i) := by
    intro i
    exact supportedOnRanks_of_mem_rankFace S c (hsrank i.2)
  have hwa_sum : ∑ j, wa j = 1 :=
    sum_affineCombination_coordinates_eq_one p hp_sum a ha
  have hwb_sum : ∑ j, wb j = 1 :=
    sum_affineCombination_coordinates_eq_one p hp_sum b hb
  have hwa_support : SupportedOnRanks S c wa :=
    supportedOnRanks_affineCombination S c p hp_support a ha
  have hwb_support : SupportedOnRanks S c wb :=
    supportedOnRanks_affineCombination S c p hp_support b hb
  have hdecode : rankDecodeLinear S c hc wa = rankDecodeLinear S c hc wb := by
    calc
      rankDecodeLinear S c hc wa =
          Finset.univ.affineCombination ℝ
            (fun i : s => rankDecodeLinear S c hc (p i)) a := by
        exact Finset.univ.map_affineCombination p a ha
          (rankDecodeLinear S c hc).toAffineMap
      _ = Finset.univ.affineCombination ℝ
            (fun i : s => rankDecodeLinear S c hc (p i)) b := hab
      _ = rankDecodeLinear S c hc wb := by
        symm
        exact Finset.univ.map_affineCombination p b hb
          (rankDecodeLinear S c hc).toAffineMap
  have hwab : wa = wb := rankDecodeLinear_injective_of_sum_eq_one
    S c hc hwa_sum hwb_sum hwa_support hwb_support hdecode
  exact (affineIndependent_iff_eq_of_fintype_affineCombination_eq (k := ℝ) p).mp hsind
    a b ha hb hwab

theorem rankDecodeLinear_injOn_rankFace
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S))
    (hc : IsChain S c) :
    Set.InjOn (rankDecodeLinear S c hc) (rankFace S c) := by
  intro w hw z hz hdecode
  exact rankDecodeLinear_injective_of_sum_eq_one S c hc
    hw.1.2 hz.1.2
    (supportedOnRanks_of_mem_rankFace S c hw)
    (supportedOnRanks_of_mem_rankFace S c hz) hdecode

theorem rankCoordinates_rankDecode_of_mem_rankFace
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S))
    (hc : IsChain S c) (w : WeightSpace k) (hw : w ∈ rankFace S c) :
    rankCoordinates S c hc
      ⟨rankDecodeLinear S c hc w,
        rankDecode_mem_chain S c hc ⟨w, hw.1⟩⟩ = ⟨w, hw.1⟩ := by
  apply Subtype.ext
  apply rankDecodeLinear_injOn_rankFace S c hc
  · exact rankWeights_mem_rankFace S c
      ((chainHomeomorph S c hc).symm
        ⟨rankDecodeLinear S c hc w,
          rankDecode_mem_chain S c hc ⟨w, hw.1⟩⟩)
  · exact hw
  · rw [← rankDecode_eq_linear]
    exact rankDecode_rankCoordinates S c hc
      ⟨rankDecodeLinear S c hc w,
        rankDecode_mem_chain S c hc ⟨w, hw.1⟩⟩

/-- Decode the vertices of a rank-grid simplex into the corresponding
polytope chain simplex. -/
noncomputable def mappedFace (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (s : Finset (WeightSpace k)) : Finset (Fin k → ℝ) := by
  classical
  exact s.image (rankDecodeLinear S c hc)

@[simp]
theorem mem_mappedFace (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (s : Finset (WeightSpace k)) (x : Fin k → ℝ) :
    x ∈ mappedFace S c hc s ↔
      ∃ w ∈ s, rankDecodeLinear S c hc w = x := by
  classical
  simp [mappedFace]

theorem mappedFace_nonempty (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    {s : Finset (WeightSpace k)} (hs : s.Nonempty) :
    (mappedFace S c hc s).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr hs

theorem affineIndependent_mappedFace (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (s : Finset (WeightSpace k))
    (hsind : AffineIndependent ℝ ((↑) : s → WeightSpace k))
    (hsrank : (s : Set (WeightSpace k)) ⊆ rankFace S c) :
    AffineIndependent ℝ ((↑) : mappedFace S c hc s → Fin k → ℝ) := by
  classical
  have hdec := affineIndependent_rankDecode_of_subset_rankFace S c hc s hsind hsrank
  let e : s ≃ mappedFace S c hc s :=
    Equiv.ofBijective
      (fun w : s =>
        (⟨rankDecodeLinear S c hc w.1,
          (mem_mappedFace S c hc s _).mpr ⟨w.1, w.2, rfl⟩⟩ :
          mappedFace S c hc s))
      ⟨by
        intro w z hwz
        apply Subtype.ext
        apply rankDecodeLinear_injOn_rankFace S c hc (hsrank w.2) (hsrank z.2)
        exact congrArg Subtype.val hwz,
        by
          intro x
          obtain ⟨w, hws, hwx⟩ := (mem_mappedFace S c hc s x.1).mp x.2
          refine ⟨⟨w, hws⟩, Subtype.ext ?_⟩
          exact hwx⟩
  have h := hdec.comp_embedding e.symm.toEmbedding
  convert h using 1
  funext x
  change x.1 = rankDecodeLinear S c hc (e.symm x).1
  exact congrArg Subtype.val (e.apply_symm_apply x) |>.symm

theorem convexHull_mappedFace (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (s : Finset (WeightSpace k)) :
    convexHull ℝ (mappedFace S c hc s : Set (Fin k → ℝ)) =
      rankDecodeLinear S c hc ''
        convexHull ℝ (s : Set (WeightSpace k)) := by
  classical
  rw [mappedFace, Finset.coe_image]
  exact (rankDecodeLinear S c hc).image_convexHull _ |>.symm

/-- The prefix-grid triangulation of one barycentric chain simplex,
decoded back into the original parameter space. -/
noncomputable def localMappedComplex (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S))
    (hc : IsChain S c) : SimplicialComplex ℝ (Fin k → ℝ) where
  faces := {D | ∃ s : Finset (WeightSpace k),
    s ∈ (rankSubcomplex hn S c).faces ∧ D = mappedFace S c hc s}
  isRelLowerSet_faces := by
    rintro D ⟨s, hs, rfl⟩
    constructor
    · exact mappedFace_nonempty S c hc
        ((rankSubcomplex hn S c).nonempty_of_mem_faces hs)
    · intro T hTD hT
      let u := s.filter fun w => rankDecodeLinear S c hc w ∈ T
      have hu_subset : u ⊆ s := Finset.filter_subset _ _
      have hu_nonempty : u.Nonempty := by
        obtain ⟨x, hxT⟩ := hT
        have hxD := hTD hxT
        obtain ⟨w, hws, hwx⟩ := (mem_mappedFace S c hc s x).mp hxD
        refine ⟨w, Finset.mem_filter.mpr ⟨hws, ?_⟩⟩
        rwa [hwx]
      have hu_face : u ∈ (rankSubcomplex hn S c).faces :=
        (rankSubcomplex hn S c).down_closed hs hu_subset hu_nonempty
      refine ⟨u, hu_face, ?_⟩
      ext x
      constructor
      · intro hxT
        have hxD := hTD hxT
        obtain ⟨w, hws, hwx⟩ := (mem_mappedFace S c hc s x).mp hxD
        exact (mem_mappedFace S c hc u x).mpr
          ⟨w, Finset.mem_filter.mpr ⟨hws, hwx ▸ hxT⟩, hwx⟩
      · intro hx
        obtain ⟨w, hwu, hwx⟩ := (mem_mappedFace S c hc u x).mp hx
        exact hwx ▸ (Finset.mem_filter.mp hwu).2
  indep := by
    rintro D ⟨s, hs, rfl⟩
    exact affineIndependent_mappedFace S c hc s
      ((rankSubcomplex hn S c).indep hs)
      ((mem_rankSubcomplex_faces hn S c s).mp hs).2
  inter_subset_convexHull := by
    rintro D E ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ x hx
    rw [convexHull_mappedFace, convexHull_mappedFace] at hx
    obtain ⟨w, hws, hwx⟩ := hx.1
    obtain ⟨z, hzt, hzx⟩ := hx.2
    have hsrank := (mem_rankSubcomplex_faces hn S c s).mp hs |>.2
    have htrank := (mem_rankSubcomplex_faces hn S c t).mp ht |>.2
    have hwrank : w ∈ rankFace S c :=
      convexHull_min hsrank (convex_rankFace S c) hws
    have hzrank : z ∈ rankFace S c :=
      convexHull_min htrank (convex_rankFace S c) hzt
    have hwz : w = z := rankDecodeLinear_injOn_rankFace S c hc
      hwrank hzrank (hwx.trans hzx.symm)
    subst z
    have hwinter := (gridComplex hn).inter_subset_convexHull
      ((mem_rankSubcomplex_faces hn S c s).mp hs).1
      ((mem_rankSubcomplex_faces hn S c t).mp ht).1 ⟨hws, hzt⟩
    have hxsmall : x ∈ convexHull ℝ
        (mappedFace S c hc (s ∩ t) : Set (Fin k → ℝ)) := by
      rw [convexHull_mappedFace]
      exact ⟨w, by simpa only [Finset.coe_inter] using hwinter, hwx⟩
    apply convexHull_mono ?_ hxsmall
    intro y hy
    obtain ⟨q, hq, hqy⟩ := (mem_mappedFace S c hc (s ∩ t) y).mp
      (Finset.mem_coe.mp hy)
    have hqs := (Finset.mem_inter.mp hq).1
    have hqt := (Finset.mem_inter.mp hq).2
    exact
      ⟨Finset.mem_coe.mpr <| (mem_mappedFace S c hc s y).mpr ⟨q, hqs, hqy⟩,
        Finset.mem_coe.mpr <| (mem_mappedFace S c hc t y).mpr ⟨q, hqt, hqy⟩⟩

@[simp]
theorem mem_localMappedComplex_faces (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S))
    (hc : IsChain S c) (D : Finset (Fin k → ℝ)) :
    D ∈ (localMappedComplex hn S c hc).faces ↔
      ∃ s : Finset (WeightSpace k),
        s ∈ (rankSubcomplex hn S c).faces ∧ D = mappedFace S c hc s :=
  Iff.rfl

theorem localMappedComplex_faces_finite (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S))
    (hc : IsChain S c) :
    (localMappedComplex hn S c hc).faces.Finite := by
  have h := (rankSubcomplex_faces_finite hn S c).image
    (mappedFace S c hc)
  apply h.subset
  intro D hD
  obtain ⟨s, hs, rfl⟩ := (mem_localMappedComplex_faces hn S c hc D).mp hD
  exact ⟨s, hs, rfl⟩

@[simp]
theorem localMappedComplex_space (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S))
    (hc : IsChain S c) :
    (localMappedComplex hn S c hc).space =
      convexHull ℝ (chainVertices S c : Set (Fin k → ℝ)) := by
  apply Subset.antisymm
  · intro x hx
    rw [SimplicialComplex.mem_space_iff] at hx
    obtain ⟨D, hD, hxD⟩ := hx
    obtain ⟨s, hs, rfl⟩ := (mem_localMappedComplex_faces hn S c hc D).mp hD
    rw [convexHull_mappedFace] at hxD
    obtain ⟨w, hws, rfl⟩ := hxD
    have hsrank := (mem_rankSubcomplex_faces hn S c s).mp hs |>.2
    have hwrank : w ∈ rankFace S c :=
      convexHull_min hsrank (convex_rankFace S c) hws
    exact rankDecode_mem_chain S c hc ⟨w, hwrank.1⟩
  · intro x hx
    let p : convexHull ℝ (chainVertices S c : Set (Fin k → ℝ)) := ⟨x, hx⟩
    let w := rankCoordinates S c hc p
    have hwrank : (w : WeightSpace k) ∈ rankFace S c := by
      exact rankWeights_mem_rankFace S c ((chainHomeomorph S c hc).symm p)
    have hwspace : (w : WeightSpace k) ∈ (rankSubcomplex hn S c).space := by
      rw [rankSubcomplex_space hn S c]
      exact hwrank
    rw [SimplicialComplex.mem_space_iff] at hwspace ⊢
    obtain ⟨s, hs, hws⟩ := hwspace
    refine ⟨mappedFace S c hc s,
      (mem_localMappedComplex_faces hn S c hc _).mpr ⟨s, hs, rfl⟩, ?_⟩
    rw [convexHull_mappedFace]
    refine ⟨w.1, hws, ?_⟩
    exact rankDecode_rankCoordinates S c hc p

/-- A coordinate face of the standard simplex, specified by the set of
coordinates allowed to be nonzero. -/
def coordinateFace (R : Set (Fin (k + 1))) : Set (WeightSpace k) :=
  stdSimplex ℝ (Fin (k + 1)) ∩ {w | ∀ j, j ∉ R → w j = 0}

theorem mem_coordinateFace_iff (R : Set (Fin (k + 1))) (w : WeightSpace k) :
    w ∈ coordinateFace R ↔
      w ∈ stdSimplex ℝ (Fin (k + 1)) ∧ ∀ j, j ∉ R → w j = 0 :=
  Iff.rfl

theorem convex_coordinateFace (R : Set (Fin (k + 1))) :
    Convex ℝ (coordinateFace R) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_stdSimplex ℝ (Fin (k + 1))) hx.1 hy.1 ha hb hab, ?_⟩
  intro j hj
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hx.2 j hj, hy.2 j hj,
    smul_zero, smul_zero, add_zero]

theorem isExtreme_coordinateFace (R : Set (Fin (k + 1))) :
    IsExtreme ℝ (stdSimplex ℝ (Fin (k + 1))) (coordinateFace R) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hxseg
  refine ⟨hx, ?_⟩
  intro j hj
  have hzj : z j = 0 := hz.2 j hj
  obtain ⟨a, b, ha, hb, hab, hcombo⟩ := hxseg
  have hcoord := congrArg (fun w : WeightSpace k => w j) hcombo
  change a * x j + b * y j = z j at hcoord
  have hxj := hx.1 j
  have hyj := hy.1 j
  nlinarith

/-- Decoded rank-grid simplices from two barycentric chain simplices meet
only along their common decoded vertices. -/
theorem cross_inter_subset (hn : 0 < n)
    (S : Finset (Fin k → ℝ))
    (c d : Finset (ExposedFace S)) (hc : IsChain S c) (hd : IsChain S d)
    {s t : Finset (WeightSpace k)}
    (hs : s ∈ (rankSubcomplex hn S c).faces)
    (ht : t ∈ (rankSubcomplex hn S d).faces) :
    convexHull ℝ (mappedFace S c hc s : Set (Fin k → ℝ)) ∩
        convexHull ℝ (mappedFace S d hd t : Set (Fin k → ℝ)) ⊆
      convexHull ℝ
        (mappedFace S c hc s ∩ mappedFace S d hd t : Set (Fin k → ℝ)) := by
  classical
  intro x hx
  rw [convexHull_mappedFace, convexHull_mappedFace] at hx
  obtain ⟨w, hws, hwx⟩ := hx.1
  obtain ⟨z, hzt, hzx⟩ := hx.2
  have hsrank := (mem_rankSubcomplex_faces hn S c s).mp hs |>.2
  have htrank := (mem_rankSubcomplex_faces hn S d t).mp ht |>.2
  have hwrank : w ∈ rankFace S c :=
    convexHull_min hsrank (convex_rankFace S c) hws
  have hzrank : z ∈ rankFace S d :=
    convexHull_min htrank (convex_rankFace S d) hzt
  let pc : convexHull ℝ (chainVertices S c : Set (Fin k → ℝ)) :=
    ⟨rankDecodeLinear S c hc w, rankDecode_mem_chain S c hc ⟨w, hwrank.1⟩⟩
  have hdecode : rankDecodeLinear S c hc w = rankDecodeLinear S d hd z :=
    hwx.trans hzx.symm
  have hpd : pc.1 ∈ convexHull ℝ (chainVertices S d : Set (Fin k → ℝ)) := by
    rw [show pc.1 = rankDecodeLinear S d hd z from hdecode]
    exact rankDecode_mem_chain S d hd ⟨z, hzrank.1⟩
  have hpointD :
      (⟨pc.1, hpd⟩ : convexHull ℝ (chainVertices S d : Set (Fin k → ℝ))) =
        ⟨rankDecodeLinear S d hd z,
          rankDecode_mem_chain S d hd ⟨z, hzrank.1⟩⟩ := by
    apply Subtype.ext
    exact hdecode
  have hwz : w = z := by
    have hcoord := rankCoordinates_eq_of_mem S c d hc hd pc hpd
    have hwcoord := rankCoordinates_rankDecode_of_mem_rankFace S c hc w hwrank
    have hzcoord := rankCoordinates_rankDecode_of_mem_rankFace S d hd z hzrank
    have hsub : (⟨w, hwrank.1⟩ : stdSimplex ℝ (Fin (k + 1))) =
        ⟨z, hzrank.1⟩ := calc
      (⟨w, hwrank.1⟩ : stdSimplex ℝ (Fin (k + 1))) =
          rankCoordinates S c hc pc := hwcoord.symm
      _ = rankCoordinates S d hd ⟨pc.1, hpd⟩ := hcoord
      _ = rankCoordinates S d hd
          ⟨rankDecodeLinear S d hd z,
            rankDecode_mem_chain S d hd ⟨z, hzrank.1⟩⟩ := by rw [hpointD]
      _ = ⟨z, hzrank.1⟩ := hzcoord
    exact congrArg Subtype.val hsub
  subst z
  obtain ⟨u, q, g, hcoordC, _hcoordD, hvertices⟩ :=
    exists_common_rank_representation S c d hc hd pc hpd
  have hwmap : (⟨w, hwrank.1⟩ : stdSimplex ℝ (Fin (k + 1))) =
      stdSimplex.map g q := by
    rw [← hcoordC]
    exact (rankCoordinates_rankDecode_of_mem_rankFace S c hc w hwrank).symm
  have hwsupport : ∀ j, j ∉ Set.range g → w j = 0 := by
    intro j hj
    have hzero := map_eq_zero_of_not_mem_range g q j hj
    rw [← hwmap] at hzero
    exact hzero
  have hwinter := (gridComplex hn).inter_subset_convexHull
    ((mem_rankSubcomplex_faces hn S c s).mp hs).1
    ((mem_rankSubcomplex_faces hn S d t).mp ht).1 ⟨hws, hzt⟩
  have hwinter' : w ∈ convexHull ℝ (s ∩ t : Set (WeightSpace k)) := by
    simpa only [Finset.coe_inter] using hwinter
  let R : Set (Fin (k + 1)) := Set.range g
  let A : Set (WeightSpace k) := convexHull ℝ (s ∩ t : Set (WeightSpace k))
  let F : Set (WeightSpace k) := A ∩ coordinateFace R
  have hAstd : A ⊆ stdSimplex ℝ (Fin (k + 1)) := by
    apply convexHull_min
    · intro v hv
      exact (hsrank hv.1).1
    · exact convex_stdSimplex ℝ (Fin (k + 1))
  have hFconv : Convex ℝ F :=
    (convex_convexHull ℝ (s ∩ t : Set (WeightSpace k))).inter
      (convex_coordinateFace R)
  have hFext : IsExtreme ℝ A F := by
    refine ⟨inter_subset_left, ?_⟩
    intro a ha b hb z hz hzseg
    have haStd : a ∈ stdSimplex ℝ (Fin (k + 1)) := hAstd ha
    have hbStd : b ∈ stdSimplex ℝ (Fin (k + 1)) := hAstd hb
    have haFace := (isExtreme_coordinateFace R).left_mem_of_mem_openSegment
      haStd hbStd hz.2 hzseg
    exact ⟨ha, haFace⟩
  let v : Finset (WeightSpace k) := Polytope.faceVertices (s ∩ t) F
  have hgen : convexHull ℝ (v : Set (WeightSpace k)) = F := by
    exact convexHull_filter_mem_extreme (s ∩ t) hFconv <| by
      simpa only [A, Finset.coe_inter] using hFext
  have hwF : w ∈ F := by
    refine ⟨hwinter', hwrank.1, ?_⟩
    exact hwsupport
  have hwv : w ∈ convexHull ℝ (v : Set (WeightSpace k)) := by
    rw [hgen]
    exact hwF
  have hxv : x ∈ convexHull ℝ
      (mappedFace S c hc v : Set (Fin k → ℝ)) := by
    rw [convexHull_mappedFace]
    exact ⟨w, hwv, hwx⟩
  apply convexHull_mono ?_ hxv
  intro y hy
  obtain ⟨r, hrv, hry⟩ := (mem_mappedFace S c hc v y).mp
    (Finset.mem_coe.mp hy)
  have hrinfo := (mem_faceVertices (s ∩ t) F r).mp hrv
  have hrst := Finset.mem_inter.mp hrinfo.1
  have hrface : r ∈ coordinateFace R := hrinfo.2.2
  let wr : stdSimplex ℝ (Fin (k + 1)) := ⟨r, hrface.1⟩
  have hrdecode : rankDecodeLinear S c hc r = rankDecodeLinear S d hd r := by
    change rankDecode S c hc wr = rankDecode S d hd wr
    apply rankDecode_eq_of_supported_on_common S c d hc hd g
    · intro a
      exact (hvertices a).1.trans (hvertices a).2.symm
    · intro j hj
      exact hrface.2 j hj
  exact
    ⟨Finset.mem_coe.mpr <| (mem_mappedFace S c hc s y).mpr
        ⟨r, hrst.1, hry⟩,
      Finset.mem_coe.mpr <| (mem_mappedFace S d hd t y).mpr
        ⟨r, hrst.2, hrdecode.symm.trans hry⟩⟩

abbrev ChainIndex (S : Finset (Fin k → ℝ)) :=
  {c : Finset (ExposedFace S) // IsChain S c}

/-- The compatible union of the decoded rank-grid triangulations over all
barycentric chain simplices of a polytope. -/
noncomputable def mappedComplex (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) : SimplicialComplex ℝ (Fin k → ℝ) where
  faces := ⋃ C : ChainIndex S, (localMappedComplex hn S C.1 C.2).faces
  isRelLowerSet_faces := by
    intro D hD
    obtain ⟨C, hDC⟩ := Set.mem_iUnion.mp hD
    have hrel := (localMappedComplex hn S C.1 C.2).isRelLowerSet_faces hDC
    refine ⟨hrel.1, ?_⟩
    intro T hTD hT
    exact Set.mem_iUnion.mpr ⟨C, hrel.2 hTD hT⟩
  indep := by
    intro D hD
    obtain ⟨C, hDC⟩ := Set.mem_iUnion.mp hD
    exact (localMappedComplex hn S C.1 C.2).indep hDC
  inter_subset_convexHull := by
    intro D E hD hE
    obtain ⟨C, hDC⟩ := Set.mem_iUnion.mp hD
    obtain ⟨J, hEJ⟩ := Set.mem_iUnion.mp hE
    obtain ⟨s, hs, rfl⟩ := (mem_localMappedComplex_faces hn S C.1 C.2 D).mp hDC
    obtain ⟨t, ht, rfl⟩ := (mem_localMappedComplex_faces hn S J.1 J.2 E).mp hEJ
    exact cross_inter_subset hn S C.1 J.1 C.2 J.2 hs ht

@[simp]
theorem mem_mappedComplex_faces (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) (D : Finset (Fin k → ℝ)) :
    D ∈ (mappedComplex hn S).faces ↔
      ∃ C : ChainIndex S, D ∈ (localMappedComplex hn S C.1 C.2).faces := by
  simp [mappedComplex]

theorem mappedComplex_faces_finite (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) :
    (mappedComplex hn S).faces.Finite := by
  rw [mappedComplex]
  exact Set.finite_iUnion fun C => localMappedComplex_faces_finite hn S C.1 C.2

@[simp]
theorem mappedComplex_space (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) :
    (mappedComplex hn S).space = convexHull ℝ (S : Set (Fin k → ℝ)) := by
  apply Subset.antisymm
  · intro x hx
    rw [SimplicialComplex.mem_space_iff] at hx
    obtain ⟨D, hD, hxD⟩ := hx
    obtain ⟨C, hDC⟩ := (mem_mappedComplex_faces hn S D).mp hD
    have hxchain : x ∈ convexHull ℝ
        (chainVertices S C.1 : Set (Fin k → ℝ)) := by
      rw [← localMappedComplex_space hn S C.1 C.2]
      exact (localMappedComplex hn S C.1 C.2).convexHull_subset_space hDC hxD
    apply convexHull_min ?_ (convex_convexHull ℝ (S : Set (Fin k → ℝ))) hxchain
    intro y hy
    obtain ⟨F, _hFC, rfl⟩ :=
      (mem_chainVertices S C.1 y).mp (Finset.mem_coe.mp hy)
    exact F.extreme_carrier.subset (F.center_mem S)
  · intro x hx
    have hxbary : x ∈ (barycentricComplex S).space := by
      rw [barycentricComplex_space]
      exact hx
    rw [SimplicialComplex.mem_space_iff] at hxbary ⊢
    obtain ⟨D, hD, hxD⟩ := hxbary
    obtain ⟨c, hc, rfl⟩ := hD
    let C : ChainIndex S := ⟨c, hc⟩
    have hxlocal : x ∈ (localMappedComplex hn S c hc).space := by
      rw [localMappedComplex_space]
      exact hxD
    rw [SimplicialComplex.mem_space_iff] at hxlocal
    obtain ⟨T, hT, hxT⟩ := hxlocal
    exact ⟨T, (mem_mappedComplex_faces hn S T).mpr ⟨C, hT⟩, hxT⟩

open _root_.FamiliesOfMapsB01 in
/-- The decoded rank-grid complex is a finite subdivision of the original
finite convex hull. -/
noncomputable def mappedSubdivision (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) :
    Subdivision (convexHull ℝ (S : Set (Fin k → ℝ))) where
  complex := mappedComplex hn S
  faces_finite := mappedComplex_faces_finite hn S
  space_eq := mappedComplex_space hn S

end Submission.MappedComplex
