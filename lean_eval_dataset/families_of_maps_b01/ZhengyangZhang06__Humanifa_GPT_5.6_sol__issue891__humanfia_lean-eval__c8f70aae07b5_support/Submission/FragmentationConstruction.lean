import Submission.MappedComplex
import Submission.Helpers

open Set Geometry
open unitInterval
open scoped Topology

namespace Submission.FragmentationConstruction

open _root_.FamiliesOfMapsB01
open Helpers
open Polytope Polytope.ExposedFace
open ChainCoordinates GridComplex GridDeformation RankGrid MappedComplex

variable {k n : ℕ} {ι X : Type*} [TopologicalSpace X]

/-- A finite collection of nonnegative weights subordinate to labelled
members of an open cover. -/
structure WeightSystem (U : ι → Set X) (n : ℕ) where
  label : Fin n → ι
  weight : X → Fin n → ℝ
  continuous_weight : ∀ j, Continuous fun x => weight x j
  nonneg : ∀ x j, 0 ≤ weight x j
  sum_eq_one : ∀ x, ∑ j, weight x j = 1
  zero_outside : ∀ j x, x ∉ U (label j) → weight x j = 0

namespace WeightSystem

variable {U : ι → Set X}

theorem positive_card [Nonempty X] (W : WeightSystem U n) : 0 < n := by
  obtain ⟨x⟩ := ‹Nonempty X›
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  simpa using sum_eq_one W x

end WeightSystem

section Chains

variable (S : Finset (Fin k → ℝ))

theorem chainHull_subset_polytope (C : ChainIndex S) :
    convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) ⊆
      convexHull ℝ (S : Set (Fin k → ℝ)) := by
  apply convexHull_min
  · intro x hx
    obtain ⟨F, _hFC, rfl⟩ :=
      (mem_chainVertices S C.1 x).mp (Finset.mem_coe.mp hx)
    exact F.extreme_carrier.subset (F.center_mem S)
  · exact convex_convexHull ℝ (S : Set (Fin k → ℝ))

noncomputable def chainChoice
    (p : convexHull ℝ (S : Set (Fin k → ℝ))) :
    {C : ChainIndex S //
      p.1 ∈ convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ))} := by
  have hp : p.1 ∈ (barycentricComplex S).space := by
    rw [barycentricComplex_space]
    exact p.2
  have hchoice : ∃ C : ChainIndex S,
      p.1 ∈ convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) := by
    rw [SimplicialComplex.mem_space_iff] at hp
    obtain ⟨D, ⟨c, hc, rfl⟩, hpD⟩ := hp
    exact ⟨⟨c, hc⟩, hpD⟩
  exact ⟨Classical.choose hchoice, Classical.choose_spec hchoice⟩

end Chains

section Endpoint

variable {U : ι → Set X} (W : WeightSystem U n)
variable (S : Finset (Fin k → ℝ))

noncomputable def endpointOnChain (C : ChainIndex S)
    (q : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) × X) :
    Fin k → ℝ :=
  rankDecode S C.1 C.2 <|
    redistribute (W.weight q.2) (W.nonneg q.2) (W.sum_eq_one q.2) <|
      rankCoordinates S C.1 C.2 q.1

theorem continuous_endpointOnChain (C : ChainIndex S) :
    Continuous (endpointOnChain W S C) := by
  let coord : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) × X →
      stdSimplex ℝ (Fin (k + 1)) := fun q => rankCoordinates S C.1 C.2 q.1
  have hcoord : Continuous coord :=
    (continuous_rankCoordinates S C.1 C.2).comp continuous_fst
  have hredistribute : Continuous fun q : X × stdSimplex ℝ (Fin (k + 1)) =>
      redistribute (W.weight q.1) (W.nonneg q.1) (W.sum_eq_one q.1) q.2 :=
    continuous_redistribute_family W.weight W.continuous_weight W.nonneg W.sum_eq_one
  exact (continuous_rankDecode S C.1 C.2).comp <|
    hredistribute.comp (continuous_snd.prodMk hcoord)

theorem endpointOnChain_mem (C : ChainIndex S)
    (q : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) × X) :
    endpointOnChain W S C q ∈
      convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) :=
  rankDecode_mem_chain S C.1 C.2 _

theorem endpointOnChain_eq_of_mem (C J : ChainIndex S)
    (p : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)))
    (hpJ : p.1 ∈ convexHull ℝ (chainVertices S J.1 : Set (Fin k → ℝ)))
    (x : X) :
    endpointOnChain W S C (p, x) =
      endpointOnChain W S J (⟨p.1, hpJ⟩, x) := by
  obtain ⟨u, q, g, hcoordC, hcoordJ, hvertices⟩ :=
    exists_common_rank_representation S C.1 J.1 C.2 J.2 p hpJ
  let w := redistribute (W.weight x) (W.nonneg x) (W.sum_eq_one x)
      (rankCoordinates S C.1 C.2 p)
  have hcoord : rankCoordinates S C.1 C.2 p =
      rankCoordinates S J.1 J.2 ⟨p.1, hpJ⟩ := by
    rw [hcoordC, hcoordJ]
  have hsupport : ∀ j, j ∉ Set.range g → w j = 0 := by
    intro j hj
    apply redistribute_eq_zero_of_eq_zero
    rw [hcoordC]
    exact map_eq_zero_of_not_mem_range g q j hj
  change rankDecode S C.1 C.2 w = rankDecode S J.1 J.2
    (redistribute (W.weight x) (W.nonneg x) (W.sum_eq_one x)
      (rankCoordinates S J.1 J.2 ⟨p.1, hpJ⟩))
  rw [← hcoord]
  apply rankDecode_eq_of_supported_on_common S C.1 J.1 C.2 J.2 g
  · intro a
    exact (hvertices a).1.trans (hvertices a).2.symm
  · exact hsupport

noncomputable def endpointAmbient
    (q : convexHull ℝ (S : Set (Fin k → ℝ)) × X) : Fin k → ℝ :=
  let C := (chainChoice S q.1).1
  endpointOnChain W S C
    (⟨q.1.1, (chainChoice S q.1).2⟩, q.2)

theorem endpointAmbient_eq_on_chain (C : ChainIndex S)
    (p : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ))) (x : X) :
    endpointAmbient W S
      (⟨p.1, chainHull_subset_polytope S C p.2⟩, x) =
      endpointOnChain W S C (p, x) := by
  let J := (chainChoice S
    ⟨p.1, chainHull_subset_polytope S C p.2⟩).1
  let pJ : convexHull ℝ (chainVertices S J.1 : Set (Fin k → ℝ)) :=
    ⟨p.1, (chainChoice S
      ⟨p.1, chainHull_subset_polytope S C p.2⟩).2⟩
  change endpointOnChain W S J (pJ, x) = endpointOnChain W S C (p, x)
  exact (endpointOnChain_eq_of_mem W S C J p pJ.2 x).symm

theorem endpointAmbient_mem (q : convexHull ℝ (S : Set (Fin k → ℝ)) × X) :
    endpointAmbient W S q ∈ convexHull ℝ (S : Set (Fin k → ℝ)) := by
  let C := (chainChoice S q.1).1
  apply chainHull_subset_polytope S C
  exact endpointOnChain_mem W S C
    (⟨q.1.1, (chainChoice S q.1).2⟩, q.2)

def chainDomain (C : ChainIndex S) :
    Set (convexHull ℝ (S : Set (Fin k → ℝ)) × X) :=
  {q | q.1.1 ∈ convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ))}

theorem isClosed_chainDomain (C : ChainIndex S) :
    IsClosed (chainDomain S C :
      Set (convexHull ℝ (S : Set (Fin k → ℝ)) × X)) := by
  exact (chainVertices S C.1).finite_toSet.isClosed_convexHull ℝ |>.preimage
    (continuous_subtype_val.comp continuous_fst)

theorem continuousOn_endpointAmbient_chainDomain (C : ChainIndex S) :
    ContinuousOn (endpointAmbient W S) (chainDomain S C) := by
  rw [continuousOn_iff_continuous_restrict]
  let e : chainDomain S C →
      convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) × X := fun q =>
    (⟨q.1.1.1, q.2⟩, q.1.2)
  have he : Continuous e := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    · exact continuous_snd.comp continuous_subtype_val
  have hlocal := (continuous_endpointOnChain W S C).comp he
  convert hlocal using 1
  funext q
  exact endpointAmbient_eq_on_chain W S C
    ⟨q.1.1.1, q.2⟩ q.1.2

omit [TopologicalSpace X] in
theorem iUnion_chainDomain :
    (⋃ C : ChainIndex S, chainDomain (X := X) S C) =
      (univ : Set (convexHull ℝ (S : Set (Fin k → ℝ)) × X)) := by
  apply eq_univ_of_forall
  intro q
  apply Set.mem_iUnion.mpr
  exact ⟨(chainChoice S q.1).1, (chainChoice S q.1).2⟩

theorem continuous_endpointAmbient : Continuous (endpointAmbient W S) := by
  apply (locallyFinite_of_finite
    (fun C : ChainIndex S => chainDomain (X := X) S C)).continuous
    (iUnion_chainDomain (X := X) S)
  · exact isClosed_chainDomain S
  · exact continuousOn_endpointAmbient_chainDomain W S

noncomputable def endpoint :
    C(convexHull ℝ (S : Set (Fin k → ℝ)) × X,
      convexHull ℝ (S : Set (Fin k → ℝ))) where
  toFun q := ⟨endpointAmbient W S q, endpointAmbient_mem W S q⟩
  continuous_toFun := (continuous_endpointAmbient W S).subtype_mk _

@[simp]
theorem endpoint_apply
    (q : convexHull ℝ (S : Set (Fin k → ℝ)) × X) :
    (endpoint W S q : Fin k → ℝ) = endpointAmbient W S q :=
  rfl

theorem endpointOnChain_mem_exposedFace (C : ChainIndex S)
    (H : ExposedFace S)
    (p : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)))
    (hpH : p.1 ∈ H) (x : X) :
    endpointOnChain W S C (p, x) ∈ H := by
  let sH := chainVerticesInFace S H C.1
  have hpSmall : p.1 ∈ convexHull ℝ (sH : Set (Fin k → ℝ)) := by
    rw [← convexHull_chainVertices_inter_face S H C.1]
    exact ⟨p.2, hpH⟩
  have hsHne : sH.Nonempty := convexHull_nonempty_iff.mp ⟨p.1, hpSmall⟩
  have hsHsub : sH ⊆ chainVertices S C.1 := by
    intro y hy
    exact (mem_chainVerticesInFace S H C.1 y).mp hy |>.1
  let d := restrictChain S C.1 sH
  have hdne : d.Nonempty := restrictChain_nonempty S hsHne hsHsub
  have hd : IsChain S d := C.2.subset S hdne (restrictChain_subset S C.1 sH)
  have hverts : chainVertices S d = sH := chainVertices_restrictChain S hsHsub
  have hpD : p.1 ∈ convexHull ℝ (chainVertices S d : Set (Fin k → ℝ)) := by
    rw [hverts]
    exact hpSmall
  let J : ChainIndex S := ⟨d, hd⟩
  rw [endpointOnChain_eq_of_mem W S C J p hpD x]
  have hendD := endpointOnChain_mem W S J (⟨p.1, hpD⟩, x)
  change endpointOnChain W S J (⟨p.1, hpD⟩, x) ∈
    convexHull ℝ (chainVertices S d : Set (Fin k → ℝ)) at hendD
  have hendSmall : endpointOnChain W S J (⟨p.1, hpD⟩, x) ∈
      convexHull ℝ (sH : Set (Fin k → ℝ)) := hverts ▸ hendD
  exact convexHull_min
    (fun y hy => (mem_chainVerticesInFace S H C.1 y).mp (Finset.mem_coe.mp hy) |>.2)
    H.convex_carrier hendSmall

theorem endpoint_mem_exposedFace (H : ExposedFace S)
    (p : convexHull ℝ (S : Set (Fin k → ℝ))) (hpH : p.1 ∈ H) (x : X) :
    (endpoint W S (p, x) : Fin k → ℝ) ∈ H := by
  let C := (chainChoice S p).1
  let pc : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) :=
    ⟨p.1, (chainChoice S p).2⟩
  rw [show endpoint W S (p, x) =
      ⟨endpointOnChain W S C (pc, x),
        chainHull_subset_polytope S C (endpointOnChain_mem W S C (pc, x))⟩ by
    apply Subtype.ext
    exact endpointAmbient_eq_on_chain W S C pc x]
  exact endpointOnChain_mem_exposedFace W S C H pc hpH x

noncomputable def parameter :
    C(I × convexHull ℝ (S : Set (Fin k → ℝ)) × X,
      convexHull ℝ (S : Set (Fin k → ℝ))) where
  toFun q :=
    ⟨(1 - (q.1 : ℝ)) • q.2.1.1 + (q.1 : ℝ) • (endpoint W S (q.2.1, q.2.2)).1,
      (convex_convexHull ℝ (S : Set (Fin k → ℝ))) q.2.1.2
        (endpoint W S (q.2.1, q.2.2)).2
        (sub_nonneg.mpr q.1.2.2) q.1.2.1 (by ring)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have ht : Continuous fun q : I ×
        convexHull ℝ (S : Set (Fin k → ℝ)) × X => (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hp : Continuous fun q : I ×
        convexHull ℝ (S : Set (Fin k → ℝ)) × X => q.2.1.1 :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    have hend : Continuous fun q : I ×
        convexHull ℝ (S : Set (Fin k → ℝ)) × X =>
          (endpoint W S q.2 : Fin k → ℝ) :=
      continuous_subtype_val.comp ((endpoint W S).continuous.comp continuous_snd)
    exact (continuous_const.sub ht).smul hp |>.add (ht.smul hend)

@[simp]
theorem parameter_zero
    (p : convexHull ℝ (S : Set (Fin k → ℝ))) (x : X) :
    parameter W S (0, p, x) = p := by
  apply Subtype.ext
  simp [parameter]

@[simp]
theorem parameter_one
    (p : convexHull ℝ (S : Set (Fin k → ℝ))) (x : X) :
    parameter W S (1, p, x) = endpoint W S (p, x) := by
  apply Subtype.ext
  simp [parameter]

theorem endpoint_cellwise (hn : 0 < n)
    (D : Finset (Fin k → ℝ)) (hD : D ∈ (mappedComplex hn S).facets) :
    ∃ A : Finset ι, A.card ≤ k ∧
      ∀ p p' : closedCell (convexHull ℝ (S : Set (Fin k → ℝ))) D,
        ∀ x ∉ ⋃ i ∈ A, U i,
          endpoint W S (p.1, x) = endpoint W S (p'.1, x) := by
  classical
  have hDface := (mappedComplex hn S).facets_subset hD
  obtain ⟨C, hDC⟩ := (mem_mappedComplex_faces hn S D).mp hDface
  obtain ⟨s, hs, rfl⟩ :=
    (mem_localMappedComplex_faces hn S C.1 C.2 D).mp hDC
  have hsgrid := (mem_rankSubcomplex_faces hn S C.1 s).mp hs |>.1
  obtain ⟨b, hsb⟩ := (mem_gridComplex_faces hn s).mp hsgrid
  let A : Finset ι := b.indices.image W.label
  refine ⟨A, (Finset.card_image_le.trans b.card_indices_le), ?_⟩
  intro p p' x hx
  have hpimage : p.1.1 ∈ convexHull ℝ
      (mappedFace S C.1 C.2 s : Set (Fin k → ℝ)) := p.2
  have hp'image : p'.1.1 ∈ convexHull ℝ
      (mappedFace S C.1 C.2 s : Set (Fin k → ℝ)) := p'.2
  rw [convexHull_mappedFace] at hpimage hp'image
  obtain ⟨w, hws, hwp⟩ := hpimage
  obtain ⟨z, hzs, hzp⟩ := hp'image
  have hsrank := (mem_rankSubcomplex_faces hn S C.1 s).mp hs |>.2
  have hwrank : w ∈ rankFace S C.1 :=
    convexHull_min hsrank (convex_rankFace S C.1) hws
  have hzrank : z ∈ rankFace S C.1 :=
    convexHull_min hsrank (convex_rankFace S C.1) hzs
  let ww : stdSimplex ℝ (Fin (k + 1)) := ⟨w, hwrank.1⟩
  let zz : stdSimplex ℝ (Fin (k + 1)) := ⟨z, hzrank.1⟩
  let pc : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) :=
    ⟨rankDecodeLinear S C.1 C.2 w, rankDecode_mem_chain S C.1 C.2 ww⟩
  let pc' : convexHull ℝ (chainVertices S C.1 : Set (Fin k → ℝ)) :=
    ⟨rankDecodeLinear S C.1 C.2 z, rankDecode_mem_chain S C.1 C.2 zz⟩
  have hpPoly : p.1 =
      ⟨pc.1, chainHull_subset_polytope S C pc.2⟩ := by
    apply Subtype.ext
    exact hwp.symm
  have hp'Poly : p'.1 =
      ⟨pc'.1, chainHull_subset_polytope S C pc'.2⟩ := by
    apply Subtype.ext
    exact hzp.symm
  have hglobal : (endpoint W S (p.1, x) : Fin k → ℝ) =
      endpointOnChain W S C (pc, x) := by
    rw [hpPoly]
    exact endpointAmbient_eq_on_chain W S C pc x
  have hglobal' : (endpoint W S (p'.1, x) : Fin k → ℝ) =
      endpointOnChain W S C (pc', x) := by
    rw [hp'Poly]
    exact endpointAmbient_eq_on_chain W S C pc' x
  have hlocal : endpointOnChain W S C (pc, x) =
      rankDecode S C.1 C.2
        (redistribute (W.weight x) (W.nonneg x) (W.sum_eq_one x) ww) := by
    unfold endpointOnChain
    rw [show rankCoordinates S C.1 C.2 pc = ww from
      rankCoordinates_rankDecode_of_mem_rankFace S C.1 C.2 w hwrank]
  have hlocal' : endpointOnChain W S C (pc', x) =
      rankDecode S C.1 C.2
        (redistribute (W.weight x) (W.nonneg x) (W.sum_eq_one x) zz) := by
    unfold endpointOnChain
    rw [show rankCoordinates S C.1 C.2 pc' = zz from
      rankCoordinates_rankDecode_of_mem_rankFace S C.1 C.2 z hzrank]
  have hcell : convexHull ℝ (s : Set (WeightSpace k)) ⊆ weightCell b := by
    obtain ⟨q, hq, rfl⟩ := hsb
    exact convexHull_chainVertices_subset_weightCell hn b q
  have hwwCell : MemGridCell b ww :=
    (mem_weightCell_coe_iff b ww).mp (hcell hws)
  have hzzCell : MemGridCell b zz :=
    (mem_weightCell_coe_iff b zz).mp (hcell hzs)
  have hzero : ∀ a, W.weight x (b a) = 0 := by
    intro a
    apply W.zero_outside
    intro hxin
    apply hx
    apply Set.mem_iUnion.mpr
    refine ⟨W.label (b a), ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨?_, hxin⟩
    apply Finset.mem_image.mpr
    refine ⟨b a, ?_, rfl⟩
    simp [GridCell.indices]
  have hredistribute := redistribute_eq_of_mem_gridCell
    (W.weight x) (W.nonneg x) (W.sum_eq_one x) b hzero hwwCell hzzCell
  apply Subtype.ext
  rw [hglobal, hglobal', hlocal, hlocal', hredistribute]

theorem parameter_preserves_boundary
    (Q : Set (convexHull ℝ (S : Set (Fin k → ℝ))))
    (hQ : IsBoundarySubpolyhedron Q)
    (t : I) (p : Q) (x : X) :
    parameter W S (t, p.1, x) ∈ Q := by
  let R : Set (Fin k → ℝ) :=
    ((↑) : convexHull ℝ (S : Set (Fin k → ℝ)) → Fin k → ℝ) '' Q
  let H : ExposedFace S :=
    { carrier := R
      nonempty := ⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩
      convex_carrier := by
        obtain ⟨T, hT⟩ := hQ.1
        rw [show R = convexHull ℝ (T : Set (Fin k → ℝ)) from hT]
        exact convex_convexHull ℝ (T : Set (Fin k → ℝ))
      extreme_carrier := hQ.2.2 }
  have hpH : p.1.1 ∈ H := ⟨p.1, p.2, rfl⟩
  have hendH : (endpoint W S (p.1, x) : Fin k → ℝ) ∈ H :=
    endpoint_mem_exposedFace W S H p.1 hpH x
  have hparamH : (parameter W S (t, p.1, x) : Fin k → ℝ) ∈ H := by
    exact H.convex_carrier hpH hendH (sub_nonneg.mpr t.2.2) t.2.1 (by ring)
  obtain ⟨q, hqQ, hqeq⟩ := hparamH
  have heq : parameter W S (t, p.1, x) = q := by
    apply Subtype.ext
    exact hqeq.symm
  rw [heq]
  exact hqQ

noncomputable def fragmentation (hn : 0 < n) :
    Helpers.Fragmentation (P := convexHull ℝ (S : Set (Fin k → ℝ))) U where
  subdivision := mappedSubdivision hn S
  parameter := parameter W S
  parameter_zero := parameter_zero W S
  cellwise := by
    intro D hD
    obtain ⟨A, hA, hcell⟩ := endpoint_cellwise W S hn D hD
    refine ⟨A, hA, ?_⟩
    intro p p' x hx
    simpa only [parameter_one] using hcell p p' x hx
  preserves_boundary := by
    intro Q hQ t p x
    exact parameter_preserves_boundary W S Q hQ t p x

end Endpoint

end Submission.FragmentationConstruction
