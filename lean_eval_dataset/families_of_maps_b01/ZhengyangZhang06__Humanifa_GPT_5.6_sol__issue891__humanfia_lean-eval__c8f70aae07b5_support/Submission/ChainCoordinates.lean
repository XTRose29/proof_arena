import Submission.GridComplex
import Submission.SimplexCoordinates

open Set Geometry

namespace Submission.ChainCoordinates

open Polytope Polytope.ExposedFace SimplexCoordinates

variable {k : ℕ}

theorem range_chainCenters (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) :
    Set.range (fun F : c => F.1.center S) =
      (chainVertices S c : Set (Fin k → ℝ)) := by
  ext x
  constructor
  · rintro ⟨F, rfl⟩
    exact Finset.mem_coe.mpr <|
      (mem_chainVertices S c (F.1.center S)).mpr ⟨F.1, F.2, rfl⟩
  · intro hx
    obtain ⟨F, hFc, hFx⟩ :=
      (mem_chainVertices S c x).mp (Finset.mem_coe.mp hx)
    exact ⟨⟨F, hFc⟩, hFx⟩

/-- Barycentric coordinates on a simplex coming from a chain of exposed
faces. -/
noncomputable def chainHomeomorph (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c) :
    stdSimplex ℝ c ≃ₜ convexHull ℝ (chainVertices S c : Set (Fin k → ℝ)) := by
  let h := homeomorphOf (fun F : c => F.1.center S)
    (affineIndependent_centers_of_isChain S c hc)
  exact h.trans <| Homeomorph.setCongr <|
    congrArg (convexHull ℝ) (range_chainCenters S c)

@[simp]
theorem chainHomeomorph_apply (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c) (w : stdSimplex ℝ c) :
    (chainHomeomorph S c hc w : Fin k → ℝ) =
      combinationOf (fun F : c => F.1.center S) w :=
  rfl

/-- Embed chain barycentric weights into the common coordinate indexed by
affine face rank. -/
noncomputable def rankWeightsFun (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (w : stdSimplex ℝ c) : Fin (k + 1) → ℝ :=
  fun j => ∑ F : c, if rankIndex S F.1 = j then w.1 F else 0

theorem rankWeightsFun_nonneg (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (w : stdSimplex ℝ c) (j : Fin (k + 1)) :
    0 ≤ rankWeightsFun S c w j := by
  unfold rankWeightsFun
  apply Finset.sum_nonneg
  intro F _hF
  split_ifs
  · exact w.2.1 F
  · exact le_rfl

theorem sum_rankWeightsFun (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (w : stdSimplex ℝ c) :
    ∑ j, rankWeightsFun S c w j = 1 := by
  classical
  calc
    ∑ j, rankWeightsFun S c w j =
        ∑ j, ∑ F : c, if rankIndex S F.1 = j then w.1 F else 0 := rfl
    _ = ∑ F : c, ∑ j, if rankIndex S F.1 = j then w.1 F else 0 :=
      Finset.sum_comm
    _ = ∑ F : c, w.1 F := by
      apply Finset.sum_congr rfl
      intro F _hF
      simp
    _ = 1 := w.2.2

noncomputable def rankWeights (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (w : stdSimplex ℝ c) :
    stdSimplex ℝ (Fin (k + 1)) :=
  ⟨rankWeightsFun S c w, rankWeightsFun_nonneg S c w, sum_rankWeightsFun S c w⟩

@[simp]
theorem rankWeights_apply (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (w : stdSimplex ℝ c) (j : Fin (k + 1)) :
    rankWeights S c w j = rankWeightsFun S c w j :=
  rfl

theorem continuous_rankWeights (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) : Continuous (rankWeights S c) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  unfold rankWeightsFun
  apply continuous_finsetSum
  intro F _hF
  split_ifs
  · exact (continuous_apply F).comp continuous_subtype_val
  · exact continuous_const

theorem rankWeights_eq_map (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (w : stdSimplex ℝ c) :
    rankWeights S c w = stdSimplex.map (fun F : c => rankIndex S F.1) w := by
  classical
  apply Subtype.ext
  funext j
  change (∑ F : c, if rankIndex S F.1 = j then w.1 F else 0) =
    (FunOnFinite.linearMap ℝ ℝ (fun F : c => rankIndex S F.1) w.1) j
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter]

theorem rankWeights_apply_rank (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (w : stdSimplex ℝ c) (F : c) :
    rankWeights S c w (rankIndex S F.1) = w F := by
  classical
  change ∑ G : c, (if rankIndex S G.1 = rankIndex S F.1 then w.1 G else 0) = w.1 F
  calc
    (∑ G : c, if rankIndex S G.1 = rankIndex S F.1 then w.1 G else 0) =
        (if rankIndex S F.1 = rankIndex S F.1 then w.1 F else 0) := by
      apply Fintype.sum_eq_single F
      intro G hGF
      have hrank : rankIndex S G.1 ≠ rankIndex S F.1 := by
        intro h
        apply hGF
        apply Subtype.ext
        exact rankIndex_injective_on_chain S c hc G.2 F.2 h
      simp [hrank]
    _ = w.1 F := by simp

theorem rankWeights_eq_zero_of_not_rank (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (w : stdSimplex ℝ c) (j : Fin (k + 1))
    (hj : ∀ F : c, rankIndex S F.1 ≠ j) :
    rankWeights S c w j = 0 := by
  classical
  change ∑ F : c, (if rankIndex S F.1 = j then w.1 F else 0) = 0
  apply Finset.sum_eq_zero
  intro F _hF
  simp [hj F]

/-- The vertex of a chain occupying a rank, with an arbitrary chain vertex
used at ranks absent from the chain. -/
noncomputable def rankVertex (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c) (j : Fin (k + 1)) :
    Fin k → ℝ := by
  classical
  if h : ∃ F : c, rankIndex S F.1 = j then
    exact (Classical.choose h).1.center S
  else
    exact hc.1.choose.center S

theorem rankVertex_mem_chainVertices (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c) (j : Fin (k + 1)) :
    rankVertex S c hc j ∈ chainVertices S c := by
  classical
  unfold rankVertex
  split_ifs with h
  · let F : c := Classical.choose h
    exact (mem_chainVertices S c (F.1.center S)).mpr ⟨F.1, F.2, rfl⟩
  · exact (mem_chainVertices S c (hc.1.choose.center S)).mpr
      ⟨hc.1.choose, hc.1.choose_spec, rfl⟩

theorem rankVertex_rank (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c) (F : c) :
    rankVertex S c hc (rankIndex S F.1) = F.1.center S := by
  classical
  unfold rankVertex
  split_ifs with h
  · let G : c := Classical.choose h
    have hG : rankIndex S G.1 = rankIndex S F.1 := Classical.choose_spec h
    have hGF : G = F := by
      apply Subtype.ext
      exact rankIndex_injective_on_chain S c hc G.2 F.2 hG
    simp [G, hGF]
  · exact (h ⟨F, rfl⟩).elim

/-- Decode common rank coordinates using the vertices of a fixed chain. -/
noncomputable def rankDecode (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (w : stdSimplex ℝ (Fin (k + 1))) : Fin k → ℝ :=
  combinationOf (rankVertex S c hc) w

theorem continuous_rankDecode (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c) :
    Continuous (rankDecode S c hc) :=
  continuous_combinationOf (rankVertex S c hc)

theorem rankDecode_mem_chain (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (w : stdSimplex ℝ (Fin (k + 1))) :
    rankDecode S c hc w ∈ convexHull ℝ (chainVertices S c : Set (Fin k → ℝ)) := by
  apply convexHull_mono ?_ (combinationOf_mem (rankVertex S c hc) w)
  rintro _ ⟨j, rfl⟩
  exact Finset.mem_coe.mpr (rankVertex_mem_chainVertices S c hc j)

theorem rankDecode_rankWeights (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c) (w : stdSimplex ℝ c) :
    rankDecode S c hc (rankWeights S c w) =
      combinationOf (fun F : c => F.1.center S) w := by
  classical
  unfold rankDecode combinationOf
  calc
    ∑ j, rankWeights S c w j • rankVertex S c hc j =
        ∑ j, (∑ F : c, if rankIndex S F.1 = j then w.1 F else 0) •
          rankVertex S c hc j := rfl
    _ = ∑ j, ∑ F : c,
        (if rankIndex S F.1 = j then w.1 F else 0) • rankVertex S c hc j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_smul]
    _ = ∑ F : c, ∑ j,
        (if rankIndex S F.1 = j then w.1 F else 0) • rankVertex S c hc j :=
      Finset.sum_comm
    _ = ∑ F : c, w.1 F • F.1.center S := by
      apply Finset.sum_congr rfl
      intro F _hF
      simp [rankVertex_rank S c hc F]

/-- Recover the unique face of a chain from one of its barycentric vertices. -/
noncomputable def faceOfVertex (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (x : chainVertices S c) : c :=
  ⟨Classical.choose ((mem_chainVertices S c x.1).mp x.2),
    (Classical.choose_spec ((mem_chainVertices S c x.1).mp x.2)).1⟩

theorem center_faceOfVertex (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (x : chainVertices S c) :
    (faceOfVertex S c x).1.center S = x.1 :=
  (Classical.choose_spec ((mem_chainVertices S c x.1).mp x.2)).2

theorem faceOfVertex_injective (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) : Function.Injective (faceOfVertex S c) := by
  intro x y hxy
  apply Subtype.ext
  rw [← center_faceOfVertex S c x, ← center_faceOfVertex S c y, hxy]

/-- Common rank coordinates of a point in a chain simplex. -/
noncomputable def rankCoordinates (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (p : convexHull ℝ (chainVertices S c : Set (Fin k → ℝ))) :
    stdSimplex ℝ (Fin (k + 1)) :=
  rankWeights S c ((chainHomeomorph S c hc).symm p)

theorem continuous_rankCoordinates (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c) :
    Continuous (rankCoordinates S c hc) :=
  (continuous_rankWeights S c).comp (chainHomeomorph S c hc).symm.continuous

theorem rankDecode_rankCoordinates (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (hc : IsChain S c)
    (p : convexHull ℝ (chainVertices S c : Set (Fin k → ℝ))) :
    rankDecode S c hc (rankCoordinates S c hc p) = p.1 := by
  rw [rankCoordinates, rankDecode_rankWeights]
  have h := congrArg Subtype.val ((chainHomeomorph S c hc).apply_symm_apply p)
  simpa only [chainHomeomorph_apply] using h

theorem rankCoordinates_eq_of_mem (S : Finset (Fin k → ℝ))
    (c d : Finset (ExposedFace S)) (hc : IsChain S c) (hd : IsChain S d)
    (p : convexHull ℝ (chainVertices S c : Set (Fin k → ℝ)))
    (hpd : p.1 ∈ convexHull ℝ (chainVertices S d : Set (Fin k → ℝ))) :
    rankCoordinates S c hc p =
      rankCoordinates S d hd ⟨p.1, hpd⟩ := by
  classical
  let u := chainVertices S c ∩ chainVertices S d
  have hpu : p.1 ∈ convexHull ℝ (u : Set (Fin k → ℝ)) := by
    have h := convexHull_chainVertices_inter S c d hc hd ⟨p.2, hpd⟩
    simpa only [u, Finset.coe_inter] using h
  have hu : AffineIndependent ℝ ((↑) : u → Fin k → ℝ) :=
    (affineIndependent_chainVertices S c hc).mono fun _ hx =>
      (Finset.mem_inter.mp hx).1
  let q : stdSimplex ℝ u :=
    (SimplexCoordinates.homeomorph u hu).symm ⟨p.1, hpu⟩
  let fc : u → c := fun x =>
    faceOfVertex S c ⟨x.1, Finset.mem_inter.mp x.2 |>.1⟩
  let fd : u → d := fun x =>
    faceOfVertex S d ⟨x.1, Finset.mem_inter.mp x.2 |>.2⟩
  let wc : stdSimplex ℝ c := (chainHomeomorph S c hc).symm p
  let wd : stdSimplex ℝ d :=
    (chainHomeomorph S d hd).symm ⟨p.1, hpd⟩
  have hqcomb : combinationOf ((↑) : u → Fin k → ℝ) q = p.1 := by
    change SimplexCoordinates.combination u q = p.1
    have h := congrArg Subtype.val
      ((SimplexCoordinates.homeomorph u hu).apply_symm_apply ⟨p.1, hpu⟩)
    simpa only [SimplexCoordinates.homeomorph_apply] using h
  have hwc : wc = stdSimplex.map fc q := by
    apply injective_combinationOf (fun F : c => F.1.center S)
      (affineIndependent_centers_of_isChain S c hc)
    have hccomb : combinationOf (fun F : c => F.1.center S) wc = p.1 := by
      have h := congrArg Subtype.val ((chainHomeomorph S c hc).apply_symm_apply p)
      simpa only [wc, chainHomeomorph_apply] using h
    rw [hccomb, combinationOf_map]
    symm
    calc
      combinationOf ((fun F : c => F.1.center S) ∘ fc) q =
          combinationOf ((↑) : u → Fin k → ℝ) q := by
        congr 1
        funext x
        exact center_faceOfVertex S c ⟨x.1, Finset.mem_inter.mp x.2 |>.1⟩
      _ = p.1 := hqcomb
  have hwd : wd = stdSimplex.map fd q := by
    apply injective_combinationOf (fun F : d => F.1.center S)
      (affineIndependent_centers_of_isChain S d hd)
    have hdcomb : combinationOf (fun F : d => F.1.center S) wd = p.1 := by
      have h := congrArg Subtype.val
        ((chainHomeomorph S d hd).apply_symm_apply ⟨p.1, hpd⟩)
      simpa only [wd, chainHomeomorph_apply] using h
    rw [hdcomb, combinationOf_map]
    symm
    calc
      combinationOf ((fun F : d => F.1.center S) ∘ fd) q =
          combinationOf ((↑) : u → Fin k → ℝ) q := by
        congr 1
        funext x
        exact center_faceOfVertex S d ⟨x.1, Finset.mem_inter.mp x.2 |>.2⟩
      _ = p.1 := hqcomb
  change rankWeights S c wc = rankWeights S d wd
  rw [hwc, hwd,
    rankWeights_eq_map, rankWeights_eq_map,
    stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  congr 1
  funext x
  have hfaces : (fc x).1 = (fd x).1 := by
    apply center_injective S
    rw [center_faceOfVertex S c ⟨x.1, Finset.mem_inter.mp x.2 |>.1⟩,
      center_faceOfVertex S d ⟨x.1, Finset.mem_inter.mp x.2 |>.2⟩]
  exact congrArg (rankIndex S) hfaces

theorem exists_common_rank_representation (S : Finset (Fin k → ℝ))
    (c d : Finset (ExposedFace S)) (hc : IsChain S c) (hd : IsChain S d)
    (p : convexHull ℝ (chainVertices S c : Set (Fin k → ℝ)))
    (hpd : p.1 ∈ convexHull ℝ (chainVertices S d : Set (Fin k → ℝ))) :
    ∃ (u : Finset (Fin k → ℝ)) (q : stdSimplex ℝ u) (g : u → Fin (k + 1)),
      rankCoordinates S c hc p = stdSimplex.map g q ∧
      rankCoordinates S d hd ⟨p.1, hpd⟩ = stdSimplex.map g q ∧
      ∀ x : u,
        rankVertex S c hc (g x) = x.1 ∧ rankVertex S d hd (g x) = x.1 := by
  classical
  let u := chainVertices S c ∩ chainVertices S d
  have hpu : p.1 ∈ convexHull ℝ (u : Set (Fin k → ℝ)) := by
    have h := convexHull_chainVertices_inter S c d hc hd ⟨p.2, hpd⟩
    simpa only [u, Finset.coe_inter] using h
  have hu : AffineIndependent ℝ ((↑) : u → Fin k → ℝ) :=
    (affineIndependent_chainVertices S c hc).mono fun _ hx =>
      (Finset.mem_inter.mp hx).1
  let q : stdSimplex ℝ u :=
    (SimplexCoordinates.homeomorph u hu).symm ⟨p.1, hpu⟩
  let fc : u → c := fun x =>
    faceOfVertex S c ⟨x.1, Finset.mem_inter.mp x.2 |>.1⟩
  let fd : u → d := fun x =>
    faceOfVertex S d ⟨x.1, Finset.mem_inter.mp x.2 |>.2⟩
  let g : u → Fin (k + 1) := fun x => rankIndex S (fc x).1
  let wc : stdSimplex ℝ c := (chainHomeomorph S c hc).symm p
  have hqcomb : combinationOf ((↑) : u → Fin k → ℝ) q = p.1 := by
    change SimplexCoordinates.combination u q = p.1
    have h := congrArg Subtype.val
      ((SimplexCoordinates.homeomorph u hu).apply_symm_apply ⟨p.1, hpu⟩)
    simpa only [SimplexCoordinates.homeomorph_apply] using h
  have hwc : wc = stdSimplex.map fc q := by
    apply injective_combinationOf (fun F : c => F.1.center S)
      (affineIndependent_centers_of_isChain S c hc)
    have hccomb : combinationOf (fun F : c => F.1.center S) wc = p.1 := by
      have h := congrArg Subtype.val ((chainHomeomorph S c hc).apply_symm_apply p)
      simpa only [wc, chainHomeomorph_apply] using h
    rw [hccomb, combinationOf_map]
    symm
    calc
      combinationOf ((fun F : c => F.1.center S) ∘ fc) q =
          combinationOf ((↑) : u → Fin k → ℝ) q := by
        congr 1
        funext x
        exact center_faceOfVertex S c ⟨x.1, Finset.mem_inter.mp x.2 |>.1⟩
      _ = p.1 := hqcomb
  have hcoordC : rankCoordinates S c hc p = stdSimplex.map g q := by
    change rankWeights S c wc = stdSimplex.map g q
    rw [hwc, rankWeights_eq_map, stdSimplex.map_comp_apply]
    rfl
  have hcoordD : rankCoordinates S d hd ⟨p.1, hpd⟩ = stdSimplex.map g q := by
    rw [← hcoordC]
    exact (rankCoordinates_eq_of_mem S c d hc hd p hpd).symm
  refine ⟨u, q, g, hcoordC, hcoordD, ?_⟩
  intro x
  have hfaces : (fc x).1 = (fd x).1 := by
    apply center_injective S
    rw [center_faceOfVertex S c ⟨x.1, Finset.mem_inter.mp x.2 |>.1⟩,
      center_faceOfVertex S d ⟨x.1, Finset.mem_inter.mp x.2 |>.2⟩]
  constructor
  · change rankVertex S c hc (rankIndex S (fc x).1) = x.1
    rw [rankVertex_rank S c hc (fc x)]
    exact center_faceOfVertex S c ⟨x.1, Finset.mem_inter.mp x.2 |>.1⟩
  · change rankVertex S d hd (rankIndex S (fc x).1) = x.1
    rw [congrArg (rankIndex S) hfaces, rankVertex_rank S d hd (fd x)]
    exact center_faceOfVertex S d ⟨x.1, Finset.mem_inter.mp x.2 |>.2⟩

theorem map_eq_zero_of_not_mem_range {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (w : stdSimplex ℝ α) (j : β) (hj : j ∉ Set.range f) :
    stdSimplex.map f w j = 0 := by
  classical
  change (FunOnFinite.linearMap ℝ ℝ f w.1) j = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro x hx
  exact (hj ⟨x, (Finset.mem_filter.mp hx).2⟩).elim

theorem rankDecode_eq_of_supported_on_common {α : Type*} [Fintype α]
    (S : Finset (Fin k → ℝ))
    (c d : Finset (ExposedFace S)) (hc : IsChain S c) (hd : IsChain S d)
    (g : α → Fin (k + 1))
    (hvertices : ∀ x : α,
      rankVertex S c hc (g x) = rankVertex S d hd (g x))
    (w : stdSimplex ℝ (Fin (k + 1)))
    (hsupport : ∀ j, j ∉ Set.range g → w j = 0) :
    rankDecode S c hc w = rankDecode S d hd w := by
  classical
  unfold rankDecode combinationOf
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hj : j ∈ Set.range g
  · obtain ⟨x, rfl⟩ := hj
    rw [hvertices x]
  · have hz : w.1 j = 0 := hsupport j hj
    rw [hz, zero_smul, zero_smul]

end Submission.ChainCoordinates
