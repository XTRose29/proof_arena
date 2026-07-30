import Submission.OrdinaryAdjacentEdgesSimultaneousBigonGeometryData
import Submission.OrdinaryAdjacentEdgesProtectedTrimmedPresentation
import Submission.OrdinaryAdjacentEdgesConcreteCollarGeometry
import Submission.OrdinaryAdjacentEdgesTerminalCollarCompatibility
import Submission.PolygonalArcEndpointIsolationExists
import Submission.PlaneDrawingEndpointLocalGermCover
import Submission.PlanarFiniteRayCappedSideSectors
import Submission.BigonRerouteLocalSegmentDirection
import Submission.PolygonalArcCompactAvoidanceScale
import Mathlib.Tactic

open Classical
noncomputable section

set_option maxHeartbeats 80000000

-- [TABLET NODE: OrdinaryAdjacentEdgesSimultaneousBigonGeometryExists]
lemma OrdinaryAdjacentEdgesSimultaneousBigonGeometryExists
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (u : V) (firstEdge secondEdge : G.edgeFinset)
    (firstArc secondArc : PolygonalArc)
    (x y : EuclideanSpace ℝ (Fin 2))
    (FirstCut : PolygonalArcPointCutData firstArc x)
    (SecondCut : PolygonalArcPointCutData secondArc x)
    (A B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (Tail : BigonRerouteOrderedBetaTailData
      G D secondEdge u y B Bplus Rbeta H)
    (retainedArc : G.edgeFinset → PolygonalArc)
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (hclean : ∀ (e f : G.edgeFinset)
      (p : EuclideanSpace ℝ (Fin 2)), e ≠ f →
        p ∈ (D.edgeArc e).relativeInterior →
          p ∈ (D.edgeArc f).relativeInterior →
            ∃ i j : ℕ,
              ∃ (hi : i + 1 < (D.edgeArc e).vertices.length)
                (hj : j + 1 < (D.edgeArc f).vertices.length),
                p ∈ openSegment ℝ (D.edgeArc e).vertices[i]
                    (D.edgeArc e).vertices[i + 1] ∧
                  p ∈ openSegment ℝ (D.edgeArc f).vertices[j]
                    (D.edgeArc f).vertices[j + 1] ∧
                    ¬ ∃ c : ℝ,
                      (D.edgeArc f).vertices[j + 1] -
                          (D.edgeArc f).vertices[j] =
                        c • ((D.edgeArc e).vertices[i + 1] -
                          (D.edgeArc e).vertices[i]))
    (hedges : firstEdge ≠ secondEdge)
    (hfirstCarrier : firstArc.carrier = (D.edgeArc firstEdge).carrier)
    (hfirstRelative : firstArc.relativeInterior =
      (D.edgeArc firstEdge).relativeInterior)
    (hfirstSource : firstArc.source = D.vertexPlacement u)
    (hsecondCarrier : secondArc.carrier = (D.edgeArc secondEdge).carrier)
    (hsecondRelative : secondArc.relativeInterior =
      (D.edgeArc secondEdge).relativeInterior)
    (hsecondSource : secondArc.source = D.vertexPlacement u)
    (hxFirst : x ∈ (D.edgeArc firstEdge).relativeInterior)
    (hxSecond : x ∈ (D.edgeArc secondEdge).relativeInterior)
    (hySecond : y ∈ (D.edgeArc secondEdge).relativeInterior)
    (hyx : y ≠ x)
    (hA : A = FirstCut.prefixArc.carrier)
    (hB : B = SecondCut.prefixArc.carrier)
    (hBplus : Bplus = segment ℝ x y)
    (hAB : A ∩ B = ({D.vertexPlacement u, x} : Set _))
    (hBBplus : B ∩ Bplus = ({x} : Set _))
    (hBplusBall : Bplus ⊆ Metric.ball x Disk.radius)
    (hRbeta : Rbeta =
      (D.edgeArc secondEdge).carrier \ ((B ∪ Bplus) \ ({y} : Set _)))
    (hH : H =
      (⋃ edge : G.edgeFinset,
        if edge = firstEdge then
          (D.edgeArc edge).carrier \
            (A \ ({D.vertexPlacement u, x} : Set _))
        else if edge = secondEdge then
          (D.edgeArc edge).carrier \
            ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
              (Bplus \ ({x, y} : Set _)))
        else (D.edgeArc edge).carrier) ∪
      {p | ∃ v : V, v ≠ u ∧ p = D.vertexPlacement v})
    (hATail : Disjoint A Tail.tailArc.carrier)
    (hretained : retainedArc = fun e =>
      if e = firstEdge then FirstCut.suffixArc
      else if e = secondEdge then Tail.tailArc
      else D.edgeArc e)
    (hXASpec : ∀ p, p ∈ XA ↔
      p ∈ A \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H)
    (hFirstPrefixTransfer : ∀ p i
        (hi : i + 1 < (D.edgeArc firstEdge).vertices.length),
      p ∈ openSegment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] →
      p ∈ FirstCut.prefixArc.carrier → p ≠ x →
      ∃ j : ℕ, ∃ hj : j + 1 < FirstCut.prefixArc.vertices.length,
        p ∈ openSegment ℝ FirstCut.prefixArc.vertices[j]
            FirstCut.prefixArc.vertices[j + 1] ∧
          ∃ scale : ℝ, scale ≠ 0 ∧
            FirstCut.prefixArc.vertices[j + 1] -
                FirstCut.prefixArc.vertices[j] =
              scale • ((D.edgeArc firstEdge).vertices[i + 1] -
                (D.edgeArc firstEdge).vertices[i]))
    (hDiskEdges : (Disk.firstEdge = firstEdge ∧ Disk.secondEdge = secondEdge) ∨
      (Disk.firstEdge = secondEdge ∧ Disk.secondEdge = firstEdge))
    (i j : ℕ)
    (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
    (hj : j + 1 < (D.edgeArc secondEdge).vertices.length)
    (hxOpenFirst : x ∈ openSegment ℝ (D.edgeArc firstEdge).vertices[i]
      (D.edgeArc firstEdge).vertices[i + 1])
    (hxOpenSecond : x ∈ openSegment ℝ (D.edgeArc secondEdge).vertices[j]
      (D.edgeArc secondEdge).vertices[j + 1])
    (hnonparallel : ¬ ∃ c : ℝ,
      (D.edgeArc secondEdge).vertices[j + 1] -
          (D.edgeArc secondEdge).vertices[j] =
        c • ((D.edgeArc firstEdge).vertices[i + 1] -
          (D.edgeArc firstEdge).vertices[i])) :
    Nonempty (OrdinaryAdjacentEdgesSimultaneousBigonGeometryData
      G D u firstEdge secondEdge x y A B Bplus Rbeta H
      (FirstCut.prefixArc) XA hx Disk) := by
-- BODY
  classical
  let Aarc := FirstCut.prefixArc
  have hAarcSource : Aarc.source = D.vertexPlacement u := by
    dsimp [Aarc]
    rw [FirstCut.prefix_source, hfirstSource]
  have hAarcTarget : Aarc.target = x := by
    dsimp [Aarc]
    exact FirstCut.prefix_target
  obtain ⟨Kclean, hKcarrier, hKsegments, hKpoints, hKvertices,
      hKevent⟩ :=
    OrdinaryAdjacentEdgesProtectedTrimmedPresentation G D u firstEdge
      secondEdge firstArc x y FirstCut A B Bplus Rbeta H Tail retainedArc XA
      hclean hedges hfirstCarrier hfirstRelative hfirstSource hxFirst hA
      hRbeta hH hATail hretained hXASpec hFirstPrefixTransfer
  have hBadFinite : ((Kclean.points : Set
      (EuclideanSpace ℝ (Fin 2)))).Finite := Kclean.points.finite_toSet
  have open_not_vertices (Q : PolygonalArc)
      (p : EuclideanSpace ℝ (Fin 2)) (k : ℕ)
      (hk : k + 1 < Q.vertices.length)
      (hp : p ∈ openSegment ℝ Q.vertices[k] Q.vertices[k + 1]) :
      p ∉ Q.vertices := by
    intro hpv
    rcases List.getElem_of_mem hpv with ⟨m, hm, hmp⟩
    by_cases hmk : m = k
    · subst m
      have hne : Q.vertices[k] ≠ Q.vertices[k + 1] := by
        intro heq
        have := (Q.simple_vertices.getElem_inj_iff
          (i := k) (j := k + 1) (hi := by omega) (hj := hk)).1 heq
        omega
      exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (hmp ▸ hp))
    · by_cases hmks : m = k + 1
      · subst m
        have hne : Q.vertices[k] ≠ Q.vertices[k + 1] := by
          intro heq
          have := (Q.simple_vertices.getElem_inj_iff
            (i := k) (j := k + 1) (hi := by omega) (hj := hk)).1 heq
          omega
        exact hne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 (hmp ▸ hp))
      · exact Q.vertices_avoid_nonincident_interiors hk hm hmk hmks (hmp ▸ hp)
  have open_index_unique (Q : PolygonalArc) :
      ∀ z a b (ha : a + 1 < Q.vertices.length)
        (hb : b + 1 < Q.vertices.length),
        z ∈ openSegment ℝ Q.vertices[a] Q.vertices[a + 1] →
        z ∈ openSegment ℝ Q.vertices[b] Q.vertices[b + 1] → a = b := by
    intro z a b ha hb hza hzb
    rcases lt_trichotomy a b with hab' | rfl | hba
    · have hzInter : z ∈ segment ℝ Q.vertices[a] Q.vertices[a + 1] ∩
          segment ℝ Q.vertices[b] Q.vertices[b + 1] :=
        ⟨openSegment_subset_segment ℝ _ _ hza,
          openSegment_subset_segment ℝ _ _ hzb⟩
      rw [Q.segment_intersections ha hb hab'] at hzInter
      by_cases hadj : b = a + 1
      · have hzbLeft : z ≠ Q.vertices[b] := by
          intro h
          have hne : Q.vertices[b] ≠ Q.vertices[b + 1] := by
            intro heq
            have := (Q.simple_vertices.getElem_inj_iff
              (i := b) (j := b + 1) (hi := by omega) (hj := hb)).1 heq
            omega
          exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (h ▸ hzb))
        exact False.elim (hzbLeft (by simpa [hadj] using hzInter))
      · simpa [hadj] using hzInter
    · rfl
    · have hzInter : z ∈ segment ℝ Q.vertices[b] Q.vertices[b + 1] ∩
          segment ℝ Q.vertices[a] Q.vertices[a + 1] :=
        ⟨openSegment_subset_segment ℝ _ _ hzb,
          openSegment_subset_segment ℝ _ _ hza⟩
      rw [Q.segment_intersections hb ha hba] at hzInter
      by_cases hadj : a = b + 1
      · have hzaLeft : z ≠ Q.vertices[a] := by
          intro h
          have hne : Q.vertices[a] ≠ Q.vertices[a + 1] := by
            intro heq
            have := (Q.simple_vertices.getElem_inj_iff
              (i := a) (j := a + 1) (hi := by omega) (hj := ha)).1 heq
            omega
          exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (h ▸ hza))
        exact False.elim (hzaLeft (by simpa [hadj] using hzInter))
      · simpa [hadj] using hzInter
  have second_branch_local (Br : OrdinaryCrossingLocalBranchData
      (D.edgeArc secondEdge) x Disk.radius) :
      Metric.closedBall x Disk.radius ∩ (D.edgeArc secondEdge).carrier =
        Metric.closedBall x Disk.radius ∩
          segment ℝ (D.edgeArc secondEdge).vertices[j]
            (D.edgeArc secondEdge).vertices[j + 1] := by
    rcases Br.center_case with hsame | hvert
    · rcases hsame with ⟨hafter, hxOpenBranch⟩
      have hbefore : Br.beforeIndex = j :=
        open_index_unique (D.edgeArc secondEdge) x Br.beforeIndex j
          Br.beforeIndex_valid hj hxOpenBranch hxOpenSecond
      rw [Br.closedBall_carrier_eq]
      simp only [hafter, hbefore, Set.union_self]
    · rcases hvert with ⟨hafter, hxVertex⟩
      exfalso
      have hafterValid : Br.afterIndex < (D.edgeArc secondEdge).vertices.length := by
        rw [hafter]
        exact Br.beforeIndex_valid
      exact (open_not_vertices (D.edgeArc secondEdge) x j hj hxOpenSecond)
        (by rw [hxVertex]; exact List.getElem_mem hafterValid)
  have second_disk_local :
      Metric.closedBall x Disk.radius ∩ (D.edgeArc secondEdge).carrier =
        Metric.closedBall x Disk.radius ∩
          segment ℝ (D.edgeArc secondEdge).vertices[j]
            (D.edgeArc secondEdge).vertices[j + 1] := by
    rcases hDiskEdges with hlabels | hlabels
    · have hlocal := second_branch_local (hlabels.2 ▸ Disk.secondBranch)
      simpa [hlabels.2] using hlocal
    · have hlocal := second_branch_local (hlabels.1 ▸ Disk.firstBranch)
      simpa [hlabels.1] using hlocal
  have event_data : ∀ p, p ∈ XA →
      p ∉ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2))) ∧
      ∃ j : ℕ, ∃ hj : j + 1 < Aarc.vertices.length,
        p ∈ openSegment ℝ Aarc.vertices[j] Aarc.vertices[j + 1] ∧
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ Kclean.segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
          (¬ ∃ c : ℝ, s.2 - s.1 =
            c • (Aarc.vertices[j + 1] - Aarc.vertices[j])) ∧
          (∀ t, t ∈ Kclean.segments →
            p ∈ openSegment ℝ t.1 t.2 → t = s) ∧
          ∀ upper : ℝ, 0 < upper →
            ∃ r : ℝ, 0 < r ∧ r < upper ∧
              Metric.ball p r ∩ H =
                Metric.ball p r ∩ segment ℝ s.1 s.2 ∧
              Metric.ball p r ∩ Rbeta = ∅ := by
    simpa [Aarc] using hKevent
  let eventIndex : EuclideanSpace ℝ (Fin 2) → ℕ := fun p =>
    if hp : p ∈ XA then Classical.choose (event_data p hp).2 else 0
  have eventIndex_spec (p) (hp : p ∈ XA) :
      ∃ hj : eventIndex p + 1 < Aarc.vertices.length,
        p ∈ openSegment ℝ Aarc.vertices[eventIndex p]
          Aarc.vertices[eventIndex p + 1] ∧
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ Kclean.segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
          (¬ ∃ c : ℝ, s.2 - s.1 =
            c • (Aarc.vertices[eventIndex p + 1] -
              Aarc.vertices[eventIndex p])) ∧
          (∀ t, t ∈ Kclean.segments →
            p ∈ openSegment ℝ t.1 t.2 → t = s) ∧
          ∀ upper : ℝ, 0 < upper →
            ∃ r : ℝ, 0 < r ∧ r < upper ∧
              Metric.ball p r ∩ H =
                Metric.ball p r ∩ segment ℝ s.1 s.2 ∧
              Metric.ball p r ∩ Rbeta = ∅ := by
    simpa only [eventIndex, dif_pos hp] using
      (Classical.choose_spec (event_data p hp).2)
  let otherSegments : EuclideanSpace ℝ (Fin 2) →
      Set (EuclideanSpace ℝ (Fin 2)) := fun p =>
    ⋃ k : Fin (Aarc.vertices.length - 1),
      if k.1 = eventIndex p then ∅
      else segment ℝ Aarc.vertices[k.1] Aarc.vertices[k.1 + 1]
  have otherSegments_compact (p) : IsCompact (otherSegments p) := by
    dsimp [otherSegments]
    apply isCompact_iUnion
    intro k
    split_ifs
    · exact isCompact_empty
    · rw [segment_eq_image' ℝ]
      exact isCompact_Icc.image (by fun_prop)
  have event_not_other (p) (hp : p ∈ XA) : p ∉ otherSegments p := by
    obtain ⟨hj, hpOpen, _⟩ := eventIndex_spec p hp
    intro hpOther
    simp only [otherSegments, Set.mem_iUnion] at hpOther
    rcases hpOther with ⟨k, hpOther⟩
    split_ifs at hpOther with hkEq
    · exact hpOther
    · have hk : k.1 + 1 < Aarc.vertices.length := by
        have hlen := Aarc.length_ge_two
        have hklt := k.2
        omega
      have hpOwner : p ∈ segment ℝ Aarc.vertices[eventIndex p]
          Aarc.vertices[eventIndex p + 1] :=
        openSegment_subset_segment ℝ _ _ hpOpen
      rcases lt_trichotomy k.1 (eventIndex p) with hlt | heq | hgt
      · have hinter := Aarc.segment_intersections hk hj hlt
        have hpInter : p ∈
            segment ℝ Aarc.vertices[k.1] Aarc.vertices[k.1 + 1] ∩
              segment ℝ Aarc.vertices[eventIndex p]
                Aarc.vertices[eventIndex p + 1] := ⟨hpOther, hpOwner⟩
        rw [hinter] at hpInter
        split_ifs at hpInter with hadj
        · have hpVertex : p = Aarc.vertices[eventIndex p] := by simpa using hpInter
          exact (open_not_vertices Aarc p (eventIndex p) hj hpOpen)
            (by rw [hpVertex]; exact List.getElem_mem (by omega))
        · exact hpInter
      · exact hkEq heq
      · have hinter := Aarc.segment_intersections hj hk hgt
        have hpInter : p ∈
            segment ℝ Aarc.vertices[eventIndex p]
                Aarc.vertices[eventIndex p + 1] ∩
              segment ℝ Aarc.vertices[k.1] Aarc.vertices[k.1 + 1] :=
          ⟨hpOwner, hpOther⟩
        rw [hinter] at hpInter
        split_ifs at hpInter with hadj
        · have hpVertex : p = Aarc.vertices[k.1] := by simpa using hpInter
          exact (open_not_vertices Aarc p (eventIndex p) hj hpOpen)
            (by rw [hpVertex]; exact List.getElem_mem (by omega))
        · exact hpInter
  have hAarcCarrier : Aarc.carrier = A := by
    simpa [Aarc] using hA.symm
  have event_mem_A (p) (hp : p ∈ XA) :
      p ∈ A \ ({D.vertexPlacement u, x} : Set _) := (hXASpec p).1 hp |>.1
  have event_mem_Aarc_relative (p) (hp : p ∈ XA) :
      p ∈ Aarc.relativeInterior := by
    obtain ⟨hj, hpOpen, _⟩ := eventIndex_spec p hp
    exact PolygonalArcOpenSegmentSubsetRelativeInterior Aarc (eventIndex p) hj hpOpen
  have event_mem_first_relative (p) (hp : p ∈ XA) :
      p ∈ (D.edgeArc firstEdge).relativeInterior := by
    have hpAarc := event_mem_Aarc_relative p hp
    rw [Aarc.relativeInterior_eq] at hpAarc
    have hpCarrier : p ∈ firstArc.carrier :=
      FirstCut.prefix_carrier_subset (hAarcCarrier ▸ (event_mem_A p hp).1)
    rw [hfirstRelative.symm, firstArc.relativeInterior_eq]
    refine ⟨hpCarrier, ?_⟩
    intro hpEnds
    rcases hpEnds with hpSource | hpTarget
    · have : p = Aarc.source := by simpa [Aarc, FirstCut.prefix_source] using hpSource
      exact hpAarc.2 (by simp [this])
    · have hpSuffix : p ∈ FirstCut.suffixArc.carrier := by
        rw [hpTarget]
        have ht := FirstCut.suffix_target
        rw [← ht]
        rw [FirstCut.suffixArc.carrier_eq]
        have hlast : FirstCut.suffixArc.vertices.length - 2 + 1 <
            FirstCut.suffixArc.vertices.length := by
          have hlen := FirstCut.suffixArc.length_ge_two
          omega
        refine ⟨FirstCut.suffixArc.vertices.length - 2, hlast, ?_⟩
        have htargetIdx : FirstCut.suffixArc.vertices.length - 1 <
            FirstCut.suffixArc.vertices.length := by omega
        have htargetVertex :
            FirstCut.suffixArc.vertices[FirstCut.suffixArc.vertices.length - 1] =
              FirstCut.suffixArc.target := by
          have hget := FirstCut.suffixArc.target_eq_last
          rw [List.getLast?_eq_getElem?] at hget
          rw [List.getElem?_eq_getElem htargetIdx] at hget
          exact Option.some.inj hget
        have hidx : FirstCut.suffixArc.vertices.length - 2 + 1 =
            FirstCut.suffixArc.vertices.length - 1 := by omega
        simpa [hidx, htargetVertex] using
          (right_mem_segment ℝ
            FirstCut.suffixArc.vertices[FirstCut.suffixArc.vertices.length - 2]
            FirstCut.suffixArc.vertices[FirstCut.suffixArc.vertices.length - 1])
      have hpBoth : p ∈ FirstCut.prefixArc.carrier ∩ FirstCut.suffixArc.carrier :=
        ⟨hAarcCarrier ▸ (event_mem_A p hp).1, hpSuffix⟩
      have hpx : p = x := by
        have : p ∈ ({x} : Set _) := FirstCut.carrier_intersection ▸ hpBoth
        simpa using this
      exact (event_mem_A p hp).2 (by simp [hpx])
  have event_not_B (p) (hp : p ∈ XA) : p ∉ B := by
    intro hpB
    have hpAB : p ∈ A ∩ B := ⟨(event_mem_A p hp).1, hpB⟩
    have hpEnds : p ∈ ({D.vertexPlacement u, x} : Set _) := hAB ▸ hpAB
    exact (event_mem_A p hp).2 hpEnds
  have hBplusSecondSegment : Bplus ⊆
      segment ℝ (D.edgeArc secondEdge).vertices[j]
        (D.edgeArc secondEdge).vertices[j + 1] := by
    rw [hBplus]
    have hxSeg : x ∈ segment ℝ (D.edgeArc secondEdge).vertices[j]
        (D.edgeArc secondEdge).vertices[j + 1] :=
      openSegment_subset_segment ℝ _ _ hxOpenSecond
    have hySeg : y ∈ segment ℝ (D.edgeArc secondEdge).vertices[j]
        (D.edgeArc secondEdge).vertices[j + 1] := by
      have hyBall : y ∈ Metric.closedBall x Disk.radius :=
        Metric.ball_subset_closedBall
          (hBplusBall (by simpa [hBplus] using right_mem_segment ℝ x y))
      have hyCarrier : y ∈ (D.edgeArc secondEdge).carrier :=
        ((D.edgeArc secondEdge).relativeInterior_eq ▸ hySecond).1
      have hyLocal : y ∈ Metric.closedBall x Disk.radius ∩
          (D.edgeArc secondEdge).carrier := ⟨hyBall, hyCarrier⟩
      rw [second_disk_local] at hyLocal
      exact hyLocal.2
    exact (convex_segment _ _).segment_subset hxSeg hySeg
  have hBplusSecondCarrier : Bplus ⊆ (D.edgeArc secondEdge).carrier := by
    intro z hz
    rw [(D.edgeArc secondEdge).carrier_eq]
    exact ⟨j, hj, hBplusSecondSegment hz⟩
  have event_not_Bplus (p) (hp : p ∈ XA) : p ∉ Bplus := by
    intro hpBplus
    have hpFirst := event_mem_first_relative p hp
    have hpSecondCarrier := hBplusSecondCarrier hpBplus
    have hpSecond : p ∈ (D.edgeArc secondEdge).relativeInterior := by
      rw [(D.edgeArc secondEdge).relativeInterior_eq]
      refine ⟨hpSecondCarrier, ?_⟩
      intro hpEnds
      rcases D.edgeArc_endpoints secondEdge with ⟨a, b, _hab, _he, hends⟩
      rcases hends with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩ <;>
        rcases hpEnds with hpS | hpT
      · rw [hpS, hsource] at hpFirst
        exact D.no_vertex_in_edge_interior a firstEdge hpFirst
      · rw [hpT, htarget] at hpFirst
        exact D.no_vertex_in_edge_interior b firstEdge hpFirst
      · rw [hpS, hsource] at hpFirst
        exact D.no_vertex_in_edge_interior b firstEdge hpFirst
      · rw [hpT, htarget] at hpFirst
        exact D.no_vertex_in_edge_interior a firstEdge hpFirst
    have hpBall : p ∈ Metric.closedBall x Disk.radius :=
      Metric.ball_subset_closedBall (hBplusBall hpBplus)
    have hpx : p = x := by
      rcases hDiskEdges with hlabels | hlabels
      · have hpDiskFirst : p ∈ (D.edgeArc Disk.firstEdge).relativeInterior := by
          simpa [hlabels.1] using hpFirst
        have hpDiskSecond : p ∈ (D.edgeArc Disk.secondEdge).relativeInterior := by
          simpa [hlabels.2] using hpSecond
        exact Disk.pair_meets_only_at_center hpBall hpDiskFirst hpDiskSecond
      · have hpDiskFirst : p ∈ (D.edgeArc Disk.firstEdge).relativeInterior := by
          simpa [hlabels.1] using hpSecond
        have hpDiskSecond : p ∈ (D.edgeArc Disk.secondEdge).relativeInterior := by
          simpa [hlabels.2] using hpFirst
        exact Disk.pair_meets_only_at_center hpBall hpDiskFirst hpDiskSecond
    exact (event_mem_A p hp).2 (by simp [hpx])
  let eventForbidden : EuclideanSpace ℝ (Fin 2) →
      Set (EuclideanSpace ℝ (Fin 2)) := fun p =>
    ((XA.erase p : Finset (EuclideanSpace ℝ (Fin 2))) : Set _) ∪
      (Aarc.vertices.toFinset : Set _) ∪ B ∪ Bplus ∪
        (Kclean.points : Set _) ∪ otherSegments p
  have hBcompact : IsCompact B := by
    rw [hB]
    exact PolygonalArcCarrierCompact SecondCut.prefixArc
  have hBplusCompact : IsCompact Bplus := by
    rw [hBplus]
    rw [segment_eq_image' ℝ]
    exact isCompact_Icc.image (by fun_prop)
  have eventForbidden_compact (p) : IsCompact (eventForbidden p) := by
    dsimp [eventForbidden]
    exact (((Set.Finite.isCompact (Finset.finite_toSet (XA.erase p))).union
      (Set.Finite.isCompact Aarc.vertices.toFinset.finite_toSet)).union
      hBcompact).union hBplusCompact |>.union hBadFinite.isCompact |>.union
        (otherSegments_compact p)
  have event_not_forbidden (p) (hp : p ∈ XA) : p ∉ eventForbidden p := by
    intro hpF
    rcases hpF with (((((hpErase | hpVertices) | hpB) | hpBplus) | hpBad) | hpOther)
    · exact (Finset.mem_erase.mp hpErase).1 rfl
    · obtain ⟨hj, hpOpen, _⟩ := eventIndex_spec p hp
      exact (open_not_vertices Aarc p (eventIndex p) hj hpOpen)
        (by simpa using hpVertices)
    · exact event_not_B p hp hpB
    · exact event_not_Bplus p hp hpBplus
    · exact (event_data p hp).1 hpBad
    · exact event_not_other p hp hpOther
  have eventClearance_exists (p) (hp : p ∈ XA) :
      ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ (eventForbidden p)ᶜ := by
    have hpCompl : p ∈ (eventForbidden p)ᶜ := event_not_forbidden p hp
    have hnhds : (eventForbidden p)ᶜ ∈ nhds p :=
      (eventForbidden_compact p).isClosed.isOpen_compl.mem_nhds hpCompl
    exact Metric.mem_nhds_iff.mp hnhds
  let eventClearance : EuclideanSpace ℝ (Fin 2) → ℝ := fun p =>
    if hp : p ∈ XA then Classical.choose (eventClearance_exists p hp) else 1
  have eventClearance_spec (p) (hp : p ∈ XA) :
      0 < eventClearance p ∧
        Metric.ball p (eventClearance p) ⊆ (eventForbidden p)ᶜ := by
    simpa only [eventClearance, dif_pos hp] using
      (Classical.choose_spec (eventClearance_exists p hp))
  have eventPackage_exists (p) (hp : p ∈ XA) :
      ∃ r : ℝ,
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          0 < r ∧ r < eventClearance p / 4 ∧
          s ∈ Kclean.segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
          Metric.ball p r ∩ H = Metric.ball p r ∩ segment ℝ s.1 s.2 ∧
          Metric.ball p r ∩ Rbeta = ∅ := by
    obtain ⟨_hj, _hpOpen, s, hsK, hps, _hnonparallel,
      _hunique, hlocal⟩ := eventIndex_spec p hp
    have hupper : 0 < eventClearance p / 4 := by
      have := (eventClearance_spec p hp).1
      positivity
    obtain ⟨r, hr, hrlt, hHlocal, hRlocal⟩ := hlocal _ hupper
    exact ⟨r, s, hr, hrlt, hsK, hps, hHlocal, hRlocal⟩
  let eventRadius : EuclideanSpace ℝ (Fin 2) → ℝ := fun p =>
    if hp : p ∈ XA then Classical.choose (eventPackage_exists p hp) else 1
  let eventSegment : EuclideanSpace ℝ (Fin 2) →
      EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
    fun p => if hp : p ∈ XA then
      Classical.choose (Classical.choose_spec (eventPackage_exists p hp))
    else (0, 0)
  have eventPackage_spec (p) (hp : p ∈ XA) :
      0 < eventRadius p ∧ eventRadius p < eventClearance p / 4 ∧
      eventSegment p ∈ Kclean.segments ∧
      p ∈ openSegment ℝ (eventSegment p).1 (eventSegment p).2 ∧
      Metric.ball p (eventRadius p) ∩ H =
        Metric.ball p (eventRadius p) ∩
          segment ℝ (eventSegment p).1 (eventSegment p).2 ∧
      Metric.ball p (eventRadius p) ∩ Rbeta = ∅ := by
    simpa only [eventRadius, eventSegment, dif_pos hp] using
      (Classical.choose_spec
        (Classical.choose_spec (eventPackage_exists p hp)))
  have eventRadius_lt_clearance (p) (hp : p ∈ XA) :
      eventRadius p < eventClearance p := by
    have hpos := (eventClearance_spec p hp).1
    have hlt := (eventPackage_spec p hp).2.1
    linarith
  have event_closedBall_avoids_forbidden (p) (hp : p ∈ XA) :
      Disjoint (Metric.closedBall p (eventRadius p)) (eventForbidden p) := by
    rw [Set.disjoint_left]
    intro z hzBall hzForbidden
    have hzOpen : z ∈ Metric.ball p (eventClearance p) :=
      Metric.closedBall_subset_ball (eventRadius_lt_clearance p hp) hzBall
    exact (eventClearance_spec p hp).2 hzOpen hzForbidden
  have event_pairwise (p q) (hp : p ∈ XA) (hq : q ∈ XA) (hpq : p ≠ q) :
      Disjoint (Metric.closedBall p (eventRadius p))
        (Metric.closedBall q (eventRadius q)) := by
    rw [Set.disjoint_left]
    intro z hzp hzq
    have hqForbidden : q ∈ eventForbidden p := by
      exact Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inl (Finset.mem_erase.mpr ⟨hpq.symm, hq⟩)))))
    have hpForbidden : p ∈ eventForbidden q := by
      exact Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inl (Finset.mem_erase.mpr ⟨hpq, hp⟩)))))
    have hclearP : eventClearance p ≤ dist p q := by
      by_contra hnot
      have hqBall : q ∈ Metric.ball p (eventClearance p) := by
        rw [Metric.mem_ball, dist_comm]
        exact lt_of_not_ge hnot
      exact (eventClearance_spec p hp).2 hqBall hqForbidden
    have hclearQ : eventClearance q ≤ dist p q := by
      by_contra hnot
      have hpBall : p ∈ Metric.ball q (eventClearance q) := by
        rw [Metric.mem_ball]
        exact lt_of_not_ge hnot
      exact (eventClearance_spec q hq).2 hpBall hpForbidden
    have hrp := (eventPackage_spec p hp).2.1
    have hrq := (eventPackage_spec q hq).2.1
    have hzpDist : dist p z ≤ eventRadius p := by
      simpa [Metric.mem_closedBall, dist_comm] using hzp
    have hzqDist : dist z q ≤ eventRadius q := by
      simpa [Metric.mem_closedBall] using hzq
    have htri := dist_triangle p z q
    have hpqPos : 0 < dist p q := dist_pos.mpr hpq
    linarith
  have event_away_vertices (p) (hp : p ∈ XA) (z)
      (hz : z ∈ Aarc.vertices) :
      z ∉ Metric.closedBall p (eventRadius p) := by
    intro hzBall
    have hzForbidden : z ∈ eventForbidden p := by
      exact Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inr (by simpa using hz)))))
    exact Set.disjoint_left.mp (event_closedBall_avoids_forbidden p hp)
      hzBall hzForbidden
  have branch_local (Br : OrdinaryCrossingLocalBranchData
      (D.edgeArc firstEdge) x Disk.radius) :
      Metric.closedBall x Disk.radius ∩ (D.edgeArc firstEdge).carrier =
        Metric.closedBall x Disk.radius ∩
          segment ℝ (D.edgeArc firstEdge).vertices[i]
            (D.edgeArc firstEdge).vertices[i + 1] := by
    rcases Br.center_case with hsame | hvert
    · rcases hsame with ⟨hafter, hxOpenBranch⟩
      have hbefore : Br.beforeIndex = i :=
        open_index_unique (D.edgeArc firstEdge) x Br.beforeIndex i
          Br.beforeIndex_valid hi hxOpenBranch hxOpenFirst
      rw [Br.closedBall_carrier_eq]
      simp only [hafter, hbefore, Set.union_self]
    · rcases hvert with ⟨hafter, hxVertex⟩
      exfalso
      have hafterValid : Br.afterIndex < (D.edgeArc firstEdge).vertices.length := by
        rw [hafter]
        exact Br.beforeIndex_valid
      exact (open_not_vertices (D.edgeArc firstEdge) x i hi hxOpenFirst)
        (by rw [hxVertex]; exact List.getElem_mem hafterValid)
  have first_disk_local :
      Metric.closedBall x Disk.radius ∩ (D.edgeArc firstEdge).carrier =
        Metric.closedBall x Disk.radius ∩
          segment ℝ (D.edgeArc firstEdge).vertices[i]
            (D.edgeArc firstEdge).vertices[i + 1] := by
    rcases hDiskEdges with hlabels | hlabels
    · have h := branch_local (hlabels.1 ▸ Disk.firstBranch)
      simpa [hlabels.1] using h
    · have h := branch_local (hlabels.2 ▸ Disk.secondBranch)
      simpa [hlabels.2] using h
  let itarget : ℕ := Aarc.vertices.length - 1
  have hitarget : itarget < Aarc.vertices.length := by
    dsimp [itarget]
    have hlen := Aarc.length_ge_two
    omega
  let jlast : ℕ := Aarc.vertices.length - 2
  have hjlast : jlast + 1 < Aarc.vertices.length := by
    dsimp [jlast]
    have hlen := Aarc.length_ge_two
    omega
  have hjlast_target : jlast + 1 = itarget := by
    dsimp [jlast, itarget]
    omega
  have htargetVertex : Aarc.vertices[itarget] = x := by
    have hget := Aarc.target_eq_last
    rw [List.getLast?_eq_getElem?] at hget
    rw [List.getElem?_eq_getElem hitarget] at hget
    have := Option.some.inj hget
    simpa [hAarcTarget] using this
  let d : EuclideanSpace ℝ (Fin 2) := Aarc.vertices[jlast] - x
  have hd : d ≠ 0 := by
    dsimp [d]
    intro hd0
    have heq : Aarc.vertices[jlast] = Aarc.vertices[itarget] := by
      rw [htargetVertex]
      exact sub_eq_zero.mp hd0
    have hidx := (Aarc.simple_vertices.getElem_inj_iff
      (i := jlast) (j := itarget) (hi := by omega) (hj := hitarget)).1 heq
    dsimp [jlast, itarget] at hidx
    omega
  have hlastSegmentFirst :
      Metric.ball x Disk.radius ∩
          segment ℝ Aarc.vertices[jlast] Aarc.vertices[itarget] ⊆
        segment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] := by
    intro z hz
    have hzAarc : z ∈ Aarc.carrier := by
      rw [Aarc.carrier_eq]
      exact ⟨jlast, hjlast, by simpa [hjlast_target] using hz.2⟩
    have hzFirst : z ∈ (D.edgeArc firstEdge).carrier := by
      have hzFirstArc := FirstCut.prefix_carrier_subset hzAarc
      simpa [hfirstCarrier] using hzFirstArc
    have hzClosed : z ∈ Metric.closedBall x Disk.radius :=
      Metric.ball_subset_closedBall hz.1
    have hzLocal : z ∈ Metric.closedBall x Disk.radius ∩
        (D.edgeArc firstEdge).carrier := ⟨hzClosed, hzFirst⟩
    exact (by rw [first_disk_local] at hzLocal; exact hzLocal.2)
  have hlastScale : ∃ scaleA : ℝ, scaleA ≠ 0 ∧
      d = scaleA • ((D.edgeArc firstEdge).vertices[i + 1] -
        (D.edgeArc firstEdge).vertices[i]) := by
    have hprevNe : Aarc.vertices[jlast] ≠ Aarc.vertices[itarget] := by
      intro heq
      apply hd
      dsimp [d]
      rw [heq, htargetVertex]
      simp
    obtain ⟨t, ht, hdir⟩ :=
      BigonRerouteLocalSegmentDirection Aarc.vertices[jlast]
        Aarc.vertices[itarget] (D.edgeArc firstEdge).vertices[i]
        (D.edgeArc firstEdge).vertices[i + 1] x hprevNe
        (by simpa [htargetVertex] using
          (right_mem_segment ℝ Aarc.vertices[jlast] Aarc.vertices[itarget]))
        (openSegment_subset_segment ℝ _ _ hxOpenFirst)
        Disk.radius Disk.firstBranch.radius_pos hlastSegmentFirst
    refine ⟨-t, neg_ne_zero.mpr ht, ?_⟩
    dsimp [d]
    rw [htargetVertex] at hdir
    simpa using congrArg Neg.neg hdir
  have hsecondScale : ∃ scaleB : ℝ, scaleB ≠ 0 ∧
      y - x = scaleB • ((D.edgeArc secondEdge).vertices[j + 1] -
        (D.edgeArc secondEdge).vertices[j]) := by
    apply BigonRerouteLocalSegmentDirection x y
      (D.edgeArc secondEdge).vertices[j]
      (D.edgeArc secondEdge).vertices[j + 1] x hyx.symm
      (left_mem_segment ℝ x y)
      (openSegment_subset_segment ℝ _ _ hxOpenSecond) 1 (by norm_num)
    intro z hz
    exact hBplusSecondSegment (by simpa [hBplus] using hz.2)
  have hlinear : LinearIndependent ℝ ![d, y - x] := by
    rw [LinearIndependent.pair_iff' hd]
    intro c hcol
    obtain ⟨scaleA, hscaleA, hdscale⟩ := hlastScale
    obtain ⟨scaleB, hscaleB, hyscale⟩ := hsecondScale
    apply hnonparallel
    refine ⟨c * scaleA / scaleB, ?_⟩
    rw [hyscale, hdscale] at hcol
    have hEq : scaleB •
        ((D.edgeArc secondEdge).vertices[j + 1] -
          (D.edgeArc secondEdge).vertices[j]) =
        (c * scaleA) •
          ((D.edgeArc firstEdge).vertices[i + 1] -
            (D.edgeArc firstEdge).vertices[i]) := by
      simpa [smul_smul] using hcol.symm
    apply (smul_right_injective (EuclideanSpace ℝ (Fin 2)) hscaleB)
    calc
      scaleB • ((D.edgeArc secondEdge).vertices[j + 1] -
          (D.edgeArc secondEdge).vertices[j]) =
          (c * scaleA) • ((D.edgeArc firstEdge).vertices[i + 1] -
            (D.edgeArc firstEdge).vertices[i]) := hEq
      _ = scaleB • ((c * scaleA / scaleB) •
          ((D.edgeArc firstEdge).vertices[i + 1] -
            (D.edgeArc firstEdge).vertices[i])) := by
        rw [smul_smul]
        congr 1
        field_simp [hscaleB]
  let mu : ℝ := inner ℝ (y - x) d / (‖d‖ ^ 2)
  let nuRaw : ℝ := inner ℝ (y - x) (PlanarRot90 d) / (‖d‖ ^ 2)
  have hyDecompRaw : y - x = mu • d + nuRaw • PlanarRot90 d := by
    simpa [mu, nuRaw] using PlanarRot90Decomposition d (y - x) hd
  have hnuRaw : nuRaw ≠ 0 := by
    intro hzero
    have hcol : y - x = mu • d := by simpa [hzero] using hyDecompRaw
    have hp := hlinear
    rw [LinearIndependent.pair_iff' hd] at hp
    exact hp mu hcol.symm
  let positiveSide : Prop := 0 < nuRaw
  let n : EuclideanSpace ℝ (Fin 2) :=
    if positiveSide then PlanarRot90 d else -PlanarRot90 d
  let nu : ℝ := if positiveSide then nuRaw else -nuRaw
  have hnu : 0 < nu := by
    dsimp [nu, positiveSide]
    split_ifs with hpos
    · exact hpos
    · exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hnuRaw)
  have hyDecomp : y - x = mu • d + nu • n := by
    dsimp [n, nu, positiveSide]
    split_ifs with hpos
    · exact hyDecompRaw
    · simpa using hyDecompRaw
  have hdn : inner ℝ d n = 0 := by
    dsimp [n, positiveSide]
    split_ifs
    · exact PlanarRot90Orthogonal d
    · rw [inner_neg_right, PlanarRot90Orthogonal]
      simp
  have hnd : inner ℝ n d = 0 := by
    rw [real_inner_comm]
    exact hdn
  have hdd : inner ℝ d d = ‖d‖ ^ 2 := real_inner_self_eq_norm_sq d
  have hnn : inner ℝ n n = ‖d‖ ^ 2 := by
    dsimp [n, positiveSide]
    split_ifs
    · rw [real_inner_self_eq_norm_sq, PlanarRot90Norm]
    · rw [real_inner_self_eq_norm_sq, norm_neg, PlanarRot90Norm]
  let K1 : ℝ := nu / (8 * (|mu| + 1))
  have hK1 : 0 < K1 := by
    dsimp [K1]
    positivity
  have hsource0 : Aarc.vertices[0] = Aarc.source := by
    have h0 : 0 < Aarc.vertices.length := by omega
    have hget := Aarc.source_eq_head
    rw [List.head?_eq_getElem?] at hget
    rw [List.getElem?_eq_getElem h0] at hget
    exact Option.some.inj hget
  have hfirstAarc : 0 + 1 < Aarc.vertices.length := by omega
  let d0 : EuclideanSpace ℝ (Fin 2) := Aarc.vertices[1] - Aarc.source
  have hd0 : d0 ≠ 0 := by
    dsimp [d0]
    intro hzero
    have heq : Aarc.vertices[1] = Aarc.vertices[0] := by
      rw [hsource0]
      exact sub_eq_zero.mp hzero
    have hidx := (Aarc.simple_vertices.getElem_inj_iff
      (i := 1) (j := 0) (hi := by omega) (hj := by omega)).1 heq
    omega
  have hsourceInStored : D.vertexPlacement u ∈ (D.edgeArc firstEdge).carrier := by
    have hsAarc : Aarc.source ∈ Aarc.carrier := by
      rw [Aarc.carrier_eq]
      refine ⟨0, hfirstAarc, ?_⟩
      simpa [hsource0] using
        (left_mem_segment ℝ Aarc.vertices[0] Aarc.vertices[1])
    have hsFirst := FirstCut.prefix_carrier_subset hsAarc
    simpa [hAarcSource, hfirstCarrier] using hsFirst
  have hsourceStoredEndpoint :
      D.vertexPlacement u = (D.edgeArc firstEdge).source ∨
        D.vertexPlacement u = (D.edgeArc firstEdge).target := by
    by_contra hnot
    have hnotSource : D.vertexPlacement u ≠ (D.edgeArc firstEdge).source :=
      fun h => hnot (Or.inl h)
    have hnotTarget : D.vertexPlacement u ≠ (D.edgeArc firstEdge).target :=
      fun h => hnot (Or.inr h)
    have hrel : D.vertexPlacement u ∈ (D.edgeArc firstEdge).relativeInterior := by
      rw [(D.edgeArc firstEdge).relativeInterior_eq]
      exact ⟨hsourceInStored, by simp [hnotSource, hnotTarget]⟩
    exact D.no_vertex_in_edge_interior u firstEdge hrel
  obtain ⟨rhoInitial, rhoTerminal, hrhoInitial, hrhoTerminal,
      initialDirections, terminalDirections, hnoInitial, hnoTerminal,
      hcoverInitial, hcoverTerminal⟩ :=
    PlaneDrawingEndpointLocalGermCover G D firstEdge (D.edgeArc firstEdge) rfl
  have positive_direction_scale
      (storedDir : EuclideanSpace ℝ (Fin 2))
      (storedRadius : ℝ) (hstoredRadius : 0 < storedRadius)
      (hray : Metric.ball (D.vertexPlacement u) storedRadius ∩
          (D.edgeArc firstEdge).carrier ⊆
        {q | ∃ c : ℝ, 0 ≤ c ∧
          q = D.vertexPlacement u + c • storedDir}) :
      ∃ a : ℝ, 0 < a ∧ d0 = a • storedDir := by
    have hnormd0 : 0 < ‖d0‖ := norm_pos_iff.mpr hd0
    let s : ℝ := min (1 / 2) (storedRadius / (2 * ‖d0‖))
    have hs : 0 < s := by
      dsimp [s]
      exact lt_min (by norm_num) (by positivity)
    have hslt : s < 1 := by
      have := min_le_left (1 / 2 : ℝ) (storedRadius / (2 * ‖d0‖))
      linarith
    let q : EuclideanSpace ℝ (Fin 2) :=
      AffineMap.lineMap Aarc.source Aarc.vertices[1] s
    have hqFormula : q = Aarc.source + s • d0 := by
      dsimp [q, d0]
      rw [AffineMap.lineMap_apply_module]
      module
    have hqSegment : q ∈ segment ℝ Aarc.vertices[0] Aarc.vertices[1] := by
      rw [segment_eq_image_lineMap]
      refine ⟨s, ⟨hs.le, hslt.le⟩, ?_⟩
      dsimp [q]
      rw [hsource0]
    have hqAarc : q ∈ Aarc.carrier := by
      rw [Aarc.carrier_eq]
      exact ⟨0, hfirstAarc, hqSegment⟩
    have hqStored : q ∈ (D.edgeArc firstEdge).carrier := by
      have := FirstCut.prefix_carrier_subset hqAarc
      simpa [hfirstCarrier] using this
    have hsdist : s * ‖d0‖ < storedRadius := by
      have hsle := min_le_right (1 / 2 : ℝ)
        (storedRadius / (2 * ‖d0‖))
      have hhalf : storedRadius / 2 < storedRadius := by linarith
      calc
        s * ‖d0‖ ≤ (storedRadius / (2 * ‖d0‖)) * ‖d0‖ :=
          mul_le_mul_of_nonneg_right hsle (norm_nonneg _)
        _ = storedRadius / 2 := by field_simp [hnormd0.ne']
        _ < storedRadius := hhalf
    have hqBall : q ∈ Metric.ball (D.vertexPlacement u) storedRadius := by
      rw [Metric.mem_ball]
      rw [hAarcSource.symm, hqFormula, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs]
      exact hsdist
    obtain ⟨c, hc, hqRay⟩ := hray ⟨hqBall, hqStored⟩
    have hqNe : q ≠ Aarc.source := by
      intro heq
      rw [hqFormula] at heq
      have hsmul : s • d0 = 0 := by
        have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) =>
          z - Aarc.source) heq
        simpa using this
      exact hd0 (smul_eq_zero.mp hsmul |>.resolve_left hs.ne')
    have hcpos : 0 < c := by
      rcases hc.eq_or_lt with rfl | hcpos
      · exfalso
        apply hqNe
        simpa [hAarcSource] using hqRay
      · exact hcpos
    refine ⟨c / s, by positivity, ?_⟩
    have heq : s • d0 = c • storedDir := by
      have hworld : Aarc.source + s • d0 =
          Aarc.source + c • storedDir :=
        hqFormula.symm.trans (by simpa [hAarcSource] using hqRay)
      have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) =>
        z - Aarc.source) hworld
      simpa [hAarcSource] using this
    apply (smul_right_injective (EuclideanSpace ℝ (Fin 2)) hs.ne')
    calc
      s • d0 = c • storedDir := heq
      _ = s • ((c / s) • storedDir) := by
        rw [smul_smul]
        congr 1
        field_simp [hs.ne']
  have source_germ_package :
      ∃ sourceRadius : ℝ,
        ∃ sourceDirections : Finset (EuclideanSpace ℝ (Fin 2)),
          0 < sourceRadius ∧
          (∀ v ∈ sourceDirections,
            ¬ ∃ a : ℝ, 0 < a ∧ v = a • d0) ∧
          (Metric.ball (D.vertexPlacement u) sourceRadius ∩
              OrdinaryDrawingImageWithoutEdge G D firstEdge ⊆
            ({D.vertexPlacement u} : Set _) ∪
              ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ sourceDirections},
                {q | ∃ c : ℝ, 0 ≤ c ∧
                  q = D.vertexPlacement u + c • v.1}) ∧
          (Metric.ball (D.vertexPlacement u) sourceRadius ∩
              (D.edgeArc firstEdge).carrier ⊆
            {q | ∃ c : ℝ, 0 ≤ c ∧ q = D.vertexPlacement u + c • d0}) := by
    rcases hsourceStoredEndpoint with hsrc | htgt
    · let hfirstStored : 1 < (D.edgeArc firstEdge).vertices.length :=
        Nat.lt_of_succ_le (D.edgeArc firstEdge).length_ge_two
      have hcoverInitialU := hcoverInitial
      rw [← hsrc] at hcoverInitialU
      let storedDir := (D.edgeArc firstEdge).vertices[1]'hfirstStored -
        (D.edgeArc firstEdge).source
      obtain ⟨rayRadius, hrayRadius, hray⟩ :=
        PolygonalArcSourceEndpointRayCover (D.edgeArc firstEdge)
      have hray' : Metric.ball (D.vertexPlacement u) rayRadius ∩
          (D.edgeArc firstEdge).carrier ⊆
        {q | ∃ c : ℝ, 0 ≤ c ∧
          q = D.vertexPlacement u + c • storedDir} := by
        simpa [storedDir, hsrc] using hray
      obtain ⟨a, ha, hd0scale⟩ :=
        positive_direction_scale storedDir rayRadius hrayRadius hray'
      refine ⟨min rhoInitial rayRadius, initialDirections,
        lt_min hrhoInitial hrayRadius, ?_, ?_, ?_⟩
      · intro v hv
        intro hvd0
        rcases hvd0 with ⟨b, hb, hvb⟩
        exact hnoInitial v hv ⟨b * a, mul_pos hb ha, by
          rw [hvb, hd0scale, smul_smul]⟩
      · intro q hq
        exact hcoverInitialU
          ⟨Metric.ball_subset_ball (min_le_left _ _) hq.1, hq.2⟩
      · rintro q ⟨hqBall, hqEdge⟩
        obtain ⟨c, hc, hq⟩ := hray' ⟨
          Metric.ball_subset_ball (min_le_right _ _) hqBall, hqEdge⟩
        refine ⟨c / a, div_nonneg hc ha.le, ?_⟩
        have ha0 : a ≠ 0 := ha.ne'
        calc
          q = D.vertexPlacement u + c • storedDir := hq
          _ = D.vertexPlacement u + (c / a) • d0 := by
            rw [hd0scale, smul_smul]
            congr 1
            field_simp [ha0]
    · let hprevStored : (D.edgeArc firstEdge).vertices.length - 2 <
          (D.edgeArc firstEdge).vertices.length := by
          have hlen := (D.edgeArc firstEdge).length_ge_two
          omega
      have hcoverTerminalU := hcoverTerminal
      rw [← htgt] at hcoverTerminalU
      let storedDir :=
        (D.edgeArc firstEdge).vertices[
          (D.edgeArc firstEdge).vertices.length - 2]'hprevStored -
            (D.edgeArc firstEdge).target
      obtain ⟨rayRadius, hrayRadius, hray⟩ :=
        PolygonalArcTargetEndpointRayCover (D.edgeArc firstEdge)
      have hray' : Metric.ball (D.vertexPlacement u) rayRadius ∩
          (D.edgeArc firstEdge).carrier ⊆
        {q | ∃ c : ℝ, 0 ≤ c ∧
          q = D.vertexPlacement u + c • storedDir} := by
        simpa [storedDir, htgt] using hray
      obtain ⟨a, ha, hd0scale⟩ :=
        positive_direction_scale storedDir rayRadius hrayRadius hray'
      refine ⟨min rhoTerminal rayRadius, terminalDirections,
        lt_min hrhoTerminal hrayRadius, ?_, ?_, ?_⟩
      · intro v hv
        intro hvd0
        rcases hvd0 with ⟨b, hb, hvb⟩
        exact hnoTerminal v hv ⟨b * a, mul_pos hb ha, by
          rw [hvb, hd0scale, smul_smul]⟩
      · intro q hq
        exact hcoverTerminalU
          ⟨Metric.ball_subset_ball (min_le_left _ _) hq.1, hq.2⟩
      · rintro q ⟨hqBall, hqEdge⟩
        obtain ⟨c, hc, hq⟩ := hray' ⟨
          Metric.ball_subset_ball (min_le_right _ _) hqBall, hqEdge⟩
        refine ⟨c / a, div_nonneg hc ha.le, ?_⟩
        have ha0 : a ≠ 0 := ha.ne'
        calc
          q = D.vertexPlacement u + c • storedDir := hq
          _ = D.vertexPlacement u + (c / a) • d0 := by
            rw [hd0scale, smul_smul]
            congr 1
            field_simp [ha0]
  obtain ⟨sourceRadius, sourceDirections, hsourceRadius,
      hsourceNoPos, hsourceCover, hsourceEdgeCover⟩ := source_germ_package
  obtain ⟨sourceKappa, hsourceKappa, hsourceSectors⟩ :=
    PlanarFiniteRayCappedSideSectors sourceDirections
      (D.vertexPlacement u) d0 sourceRadius hd0 hsourceRadius hsourceNoPos
  let K0 : ℝ := sourceKappa / 2
  have hK0 : 0 < K0 := by dsimp [K0]; linarith
  obtain ⟨r0Base, r1Base, hIsoBase⟩ :=
    PolygonalArcEndpointIsolationExists Aarc
  let EventClosed : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ XA},
      Metric.closedBall p.1 (eventRadius p.1)
  have hEventClosedCompact : IsCompact EventClosed := by
    dsimp [EventClosed]
    exact isCompact_iUnion (fun p => isCompact_closedBall p.1 (eventRadius p.1))
  have hsourceNotEventClosed : D.vertexPlacement u ∉ EventClosed := by
    intro hs
    rcases Set.mem_iUnion.mp hs with ⟨p, hsBall⟩
    have hsourceVertex : D.vertexPlacement u ∈ Aarc.vertices := by
      rw [← hAarcSource, ← hsource0]
      exact List.getElem_mem (by omega)
    exact event_away_vertices p.1 p.2 (D.vertexPlacement u) hsourceVertex hsBall
  have htargetNotEventClosed : x ∉ EventClosed := by
    intro hs
    rcases Set.mem_iUnion.mp hs with ⟨p, hsBall⟩
    have hxVertex : x ∈ Aarc.vertices := by
      rw [← htargetVertex]
      exact List.getElem_mem hitarget
    exact event_away_vertices p.1 p.2 x hxVertex hsBall
  have endpointEventClearance (z : EuclideanSpace ℝ (Fin 2))
      (hz : z ∉ EventClosed) :
      ∃ eps : ℝ, 0 < eps ∧ Metric.ball z eps ⊆ EventClosedᶜ := by
    exact Metric.mem_nhds_iff.mp
      (hEventClosedCompact.isClosed.isOpen_compl.mem_nhds hz)
  obtain ⟨sourceEventEps, hsourceEventEps, hsourceEventBall⟩ :=
    endpointEventClearance (D.vertexPlacement u) hsourceNotEventClosed
  obtain ⟨targetEventEps, htargetEventEps, htargetEventBall⟩ :=
    endpointEventClearance x htargetNotEventClosed
  have hnormd : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hDiskRadius : 0 < Disk.radius := Disk.firstBranch.radius_pos
  have hyBplus : y ∈ Bplus := by
    rw [hBplus]
    exact right_mem_segment ℝ x y
  have hyDisk : y ∈ Metric.ball x Disk.radius := hBplusBall hyBplus
  have hyDist : dist x y < Disk.radius := by
    simpa [dist_comm] using hyDisk
  let rhoTerm : ℝ := (dist x y + Disk.radius) / 2
  have hyRhoTerm : dist x y < rhoTerm := by
    dsimp [rhoTerm]
    linarith
  have hrhoTermDisk : rhoTerm < Disk.radius := by
    dsimp [rhoTerm]
    linarith
  have hrhoTerm : 0 < rhoTerm := lt_trans (dist_pos.mpr hyx.symm) hyRhoTerm
  let terminalRadiusCap : ℝ :=
    min (rhoTerm / (8 * ‖d‖)) (rhoTerm / 8)
  have hterminalRadiusCap : 0 < terminalRadiusCap := by
    dsimp [terminalRadiusCap]
    positivity
  let r0 : ℝ := min r0Base (min sourceRadius (sourceEventEps / 2))
  let r1 : ℝ := min r1Base (min terminalRadiusCap (targetEventEps / 2))
  have hr0 : 0 < r0 := by
    dsimp [r0]
    exact lt_min hIsoBase.source_pos
      (lt_min hsourceRadius (half_pos hsourceEventEps))
  have hr1 : 0 < r1 := by
    dsimp [r1]
    exact lt_min hIsoBase.target_pos
      (lt_min hterminalRadiusCap (half_pos htargetEventEps))
  have hr0Base : r0 ≤ r0Base := by exact min_le_left _ _
  have hr1Base : r1 ≤ r1Base := by exact min_le_left _ _
  have hr0Source : r0 ≤ sourceRadius := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hr1Cap : r1 ≤ terminalRadiusCap := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hr0Event : r0 < sourceEventEps := by
    have hle : r0 ≤ sourceEventEps / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hr1Event : r1 < targetEventEps := by
    have hle : r1 ≤ targetEventEps / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hIso : PolygonalArcEndpointIsolation Aarc r0 r1 := by
    refine
      { source_pos := hr0
        target_pos := hr1
        source_lt_initial_length := hr0Base.trans_lt
          hIsoBase.source_lt_initial_length
        target_lt_terminal_length := hr1Base.trans_lt
          hIsoBase.target_lt_terminal_length
        endpoint_closedBalls_disjoint :=
          hIsoBase.endpoint_closedBalls_disjoint.mono
            (Metric.closedBall_subset_closedBall hr0Base)
            (Metric.closedBall_subset_closedBall hr1Base)
        source_closedBall_carrier_subset_initial_segment := ?_
        target_closedBall_carrier_subset_terminal_segment := ?_ }
    · exact fun ⦃z⦄ hz =>
        hIsoBase.source_closedBall_carrier_subset_initial_segment
          ⟨Metric.closedBall_subset_closedBall hr0Base hz.1, hz.2⟩
    · exact fun ⦃z⦄ hz =>
        hIsoBase.target_closedBall_carrier_subset_terminal_segment
          ⟨Metric.closedBall_subset_closedBall hr1Base hz.1, hz.2⟩
  have event_away_sourceBall (p) (hp : p ∈ XA) :
      Disjoint (Metric.closedBall p (eventRadius p))
        (Metric.closedBall (D.vertexPlacement u) r0) := by
    rw [Set.disjoint_left]
    intro z hzp hzs
    have hzsOpen : z ∈ Metric.ball (D.vertexPlacement u) sourceEventEps :=
      Metric.closedBall_subset_ball hr0Event hzs
    have hzEvent : z ∈ EventClosed :=
      Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hzp⟩
    exact hsourceEventBall hzsOpen hzEvent
  have event_away_targetBall (p) (hp : p ∈ XA) :
      Disjoint (Metric.closedBall p (eventRadius p))
        (Metric.closedBall x r1) := by
    rw [Set.disjoint_left]
    intro z hzp hzt
    have hztOpen : z ∈ Metric.ball x targetEventEps :=
      Metric.closedBall_subset_ball hr1Event hzt
    have hzEvent : z ∈ EventClosed :=
      Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hzp⟩
    exact htargetEventBall hztOpen hzEvent
  have hKcompact : IsCompact H := by
    rw [← hKcarrier, Kclean.carrier_eq]
    apply hBadFinite.isCompact.union
    apply isCompact_iUnion
    intro s
    rw [segment_eq_image' ℝ]
    exact isCompact_Icc.image (by fun_prop)
  have hRbetaCompact : IsCompact Rbeta := by
    rw [← Tail.carrier_eq]
    exact PolygonalArcCarrierCompact Tail.tailArc
  have hBadSubsetH : (Kclean.points : Set
      (EuclideanSpace ℝ (Fin 2))) ⊆ H := by
    intro z hz
    rw [← hKcarrier, Kclean.carrier_eq]
    exact Or.inl hz
  let sourceLocalRadius : ℝ := min sourceRadius (r0 / 2)
  have hsourceLocalRadius : 0 < sourceLocalRadius := by
    dsimp [sourceLocalRadius]
    exact lt_min hsourceRadius (half_pos hr0)
  let EndpointEventOpen : Set (EuclideanSpace ℝ (Fin 2)) :=
    Metric.ball (D.vertexPlacement u) sourceLocalRadius ∪
      Metric.ball x rhoTerm ∪
      ⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ XA},
        Metric.ball p.1 (eventRadius p.1)
  have hEndpointEventOpen : IsOpen EndpointEventOpen := by
    dsimp [EndpointEventOpen]
    exact (Metric.isOpen_ball.union Metric.isOpen_ball).union
      (isOpen_iUnion (fun p => Metric.isOpen_ball))
  let OldCore : Set (EuclideanSpace ℝ (Fin 2)) :=
    B ∪ Bplus ∪ Rbeta ∪ H
  have hOldCoreCompact : IsCompact OldCore := by
    dsimp [OldCore]
    exact ((hBcompact.union hBplusCompact).union hRbetaCompact).union hKcompact
  let FarOld : Set (EuclideanSpace ℝ (Fin 2)) :=
    OldCore \ EndpointEventOpen
  have hFarOldCompact : IsCompact FarOld :=
    hOldCoreCompact.diff hEndpointEventOpen
  have A_nonendpoint_first_relative (z : EuclideanSpace ℝ (Fin 2))
      (hzA : z ∈ A) (hzEnds : z ∉ ({D.vertexPlacement u, x} : Set _)) :
      z ∈ (D.edgeArc firstEdge).relativeInterior := by
    have hzAarc : z ∈ Aarc.carrier := hAarcCarrier.symm ▸ hzA
    have hzAarcRel : z ∈ Aarc.relativeInterior := by
      rw [Aarc.relativeInterior_eq]
      simpa [hAarcSource, hAarcTarget] using And.intro hzAarc hzEnds
    have hzFirstCarrier : z ∈ firstArc.carrier :=
      FirstCut.prefix_carrier_subset hzAarc
    rw [hfirstRelative.symm, firstArc.relativeInterior_eq]
    refine ⟨hzFirstCarrier, ?_⟩
    intro hzFirstEnds
    rcases hzFirstEnds with hzSource | hzTarget
    · exact hzEnds (by simpa [hfirstSource] using Or.inl hzSource)
    · have hzSuffix : z ∈ FirstCut.suffixArc.carrier := by
        rw [hzTarget, ← FirstCut.suffix_target]
        rw [FirstCut.suffixArc.carrier_eq]
        let klast := FirstCut.suffixArc.vertices.length - 2
        have hklast : klast + 1 < FirstCut.suffixArc.vertices.length := by
          dsimp [klast]
          have hlen := FirstCut.suffixArc.length_ge_two
          omega
        refine ⟨klast, hklast, ?_⟩
        have htargetIdx : FirstCut.suffixArc.vertices.length - 1 <
            FirstCut.suffixArc.vertices.length := by omega
        have htargetVertex :
            FirstCut.suffixArc.vertices[FirstCut.suffixArc.vertices.length - 1] =
              FirstCut.suffixArc.target := by
          have hget := FirstCut.suffixArc.target_eq_last
          rw [List.getLast?_eq_getElem?] at hget
          rw [List.getElem?_eq_getElem htargetIdx] at hget
          exact Option.some.inj hget
        have hidx : klast + 1 = FirstCut.suffixArc.vertices.length - 1 := by
          dsimp [klast]
          omega
        simpa [hidx, htargetVertex] using
          (right_mem_segment ℝ FirstCut.suffixArc.vertices[klast]
            FirstCut.suffixArc.vertices[klast + 1])
      have hzBoth : z ∈ FirstCut.prefixArc.carrier ∩
          FirstCut.suffixArc.carrier := ⟨hzAarc, hzSuffix⟩
      have hzx : z = x := by
        have : z ∈ ({x} : Set _) := FirstCut.carrier_intersection ▸ hzBoth
        simpa using this
      exact hzEnds (by simp [hzx])
  have hABplusOnly : A ∩ Bplus ⊆ ({x} : Set _) := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx]
    have hzNotSource : z ≠ D.vertexPlacement u := by
      intro hzu
      have hzBall := hBplusBall hz.2
      have hzClosed := Metric.ball_subset_closedBall hzBall
      exact Disk.no_vertex_in_closedBall u (by simpa [hzu] using hzClosed)
    have hzEnds : z ∉ ({D.vertexPlacement u, x} : Set _) := by
      simp [hzNotSource, hzx]
    have hzFirst := A_nonendpoint_first_relative z hz.1 hzEnds
    have hzSecondCarrier := hBplusSecondCarrier hz.2
    have hzSecond : z ∈ (D.edgeArc secondEdge).relativeInterior := by
      rw [(D.edgeArc secondEdge).relativeInterior_eq]
      refine ⟨hzSecondCarrier, ?_⟩
      intro hzEdgeEnds
      rcases D.edgeArc_endpoints secondEdge with
        ⟨a, b, _hab, _he, hends⟩
      rcases hends with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩ <;>
        rcases hzEdgeEnds with hzS | hzT
      · rw [hzS, hsource] at hzFirst
        exact D.no_vertex_in_edge_interior a firstEdge hzFirst
      · rw [hzT, htarget] at hzFirst
        exact D.no_vertex_in_edge_interior b firstEdge hzFirst
      · rw [hzS, hsource] at hzFirst
        exact D.no_vertex_in_edge_interior b firstEdge hzFirst
      · rw [hzT, htarget] at hzFirst
        exact D.no_vertex_in_edge_interior a firstEdge hzFirst
    have hzClosed : z ∈ Metric.closedBall x Disk.radius :=
      Metric.ball_subset_closedBall (hBplusBall hz.2)
    have : z = x := by
      rcases hDiskEdges with hlabels | hlabels
      · exact Disk.pair_meets_only_at_center hzClosed
          (by simpa [hlabels.1] using hzFirst)
          (by simpa [hlabels.2] using hzSecond)
      · exact Disk.pair_meets_only_at_center hzClosed
          (by simpa [hlabels.1] using hzSecond)
          (by simpa [hlabels.2] using hzFirst)
    exact False.elim (hzx this)
  have hFarOldDisjoint : Disjoint FarOld Aarc.carrier := by
    rw [Set.disjoint_left]
    intro z hzFar hzAarc
    have hzA : z ∈ A := hAarcCarrier ▸ hzAarc
    have hzNotOpen := hzFar.2
    rcases hzFar.1 with ((hzB | hzBplus) | hzRbeta) | hzH
    · have hzEnds : z ∈ ({D.vertexPlacement u, x} : Set _) := by
        have : z ∈ A ∩ B := ⟨hzA, hzB⟩
        simpa [hAB] using this
      have hzEnds' : z = D.vertexPlacement u ∨ z = x := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzEnds
      rcases hzEnds' with hzu | hzx
      · subst z
        exact hzNotOpen
          (Or.inl (Or.inl (Metric.mem_ball_self hsourceLocalRadius)))
      · subst z
        exact hzNotOpen (Or.inl (Or.inr (Metric.mem_ball_self hrhoTerm)))
    · have hzx : z = x := by
        have : z ∈ ({x} : Set _) := hABplusOnly ⟨hzA, hzBplus⟩
        simpa using this
      subst z
      exact hzNotOpen (Or.inl (Or.inr (Metric.mem_ball_self hrhoTerm)))
    · have hzTail : z ∈ Tail.tailArc.carrier := by
        simpa [Tail.carrier_eq] using hzRbeta
      exact Set.disjoint_left.mp hATail hzA hzTail
    · by_cases hzEnds : z ∈ ({D.vertexPlacement u, x} : Set _)
      · have hzEnds' : z = D.vertexPlacement u ∨ z = x := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzEnds
        rcases hzEnds' with hzu | hzx
        · subst z
          exact hzNotOpen
            (Or.inl (Or.inl (Metric.mem_ball_self hsourceLocalRadius)))
        · subst z
          exact hzNotOpen (Or.inl (Or.inr (Metric.mem_ball_self hrhoTerm)))
      · have hzXA : z ∈ XA := (hXASpec z).2 ⟨⟨hzA, hzEnds⟩, hzH⟩
        apply hzNotOpen
        exact Or.inr (Set.mem_iUnion.mpr
          ⟨⟨z, hzXA⟩, Metric.mem_ball_self (eventPackage_spec z hzXA).1⟩)
  obtain ⟨etaSep, hetaSep, hetaAvoid⟩ :=
    PolygonalArcCompactAvoidanceScale Aarc FarOld hFarOldCompact
      hFarOldDisjoint
  let radiusValues : Finset ℝ := XA.image eventRadius
  have radiusValues_nonempty (hXA : XA.Nonempty) : radiusValues.Nonempty := by
    rcases hXA with ⟨p, hp⟩
    exact ⟨eventRadius p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  let eventMin : ℝ := if hXA : XA.Nonempty then
      radiusValues.min' (radiusValues_nonempty hXA) else 1
  have heventMin : 0 < eventMin := by
    dsimp [eventMin]
    split_ifs with hXA
    · have hmem := Finset.min'_mem radiusValues (radiusValues_nonempty hXA)
      rcases Finset.mem_image.mp hmem with ⟨p, hp, heq⟩
      simpa [heq] using (eventPackage_spec p hp).1
    · norm_num
  have heventMin_le (p) (hp : p ∈ XA) : eventMin ≤ eventRadius p := by
    dsimp [eventMin]
    rw [dif_pos ⟨p, hp⟩]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  let eta : ℝ := min etaSep
    (min (eventMin / 4)
      (min ((Disk.radius - rhoTerm) / 4) (sourceLocalRadius / 4)))
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min hetaSep
      (lt_min (by positivity) (lt_min (by linarith) (by positivity)))
  have heta_le_sep : eta ≤ etaSep := min_le_left _ _
  have heta_event (p) (hp : p ∈ XA) : eta < eventRadius p := by
    have hle : eta ≤ eventMin / 4 :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hminle := heventMin_le p hp
    have hrpos := (eventPackage_spec p hp).1
    linarith
  have heta_terminal_gap : eta < Disk.radius - rhoTerm := by
    have hle : eta ≤ (Disk.radius - rhoTerm) / 4 :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have heta_source_gap : eta < sourceLocalRadius := by
    have hle : eta ≤ sourceLocalRadius / 4 :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  obtain ⟨controlRadii, middleSegments, forbiddenMargins, compatibleTubes,
      vertexLocalPieces, localSideData, S, hConcrete⟩ :=
    OrdinaryAdjacentEdgesConcreteCollarGeometry Aarc eta r0 r1 K0 K1
      heta hIso hK0 hK1
  dsimp only at hConcrete
  rcases hConcrete with
    ⟨hControlSource, hControlTarget, hActualK0, hActualK1,
      hControlAwaySource, hControlAwayTarget, hSourceOmit, hTargetOmit,
      hSourceCone, hTargetCone, hCollarEq, hLeftEq, hRightEq, hCollarNear,
      hSourceCoreEq, hSourceLeftEq, hSourceRightEq,
      hTargetCoreEq, hTargetLeftEq, hTargetRightEq⟩
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  let actualK0 := compatibleTubes.initialConeBound 0 hfirstAarc
  let actualK1 := compatibleTubes.terminalConeBound jlast hjlast
  have hActualK0Pos : 0 < actualK0 :=
    compatibleTubes.initialConeBound_pos 0 hfirstAarc
  have hActualK1Pos : 0 < actualK1 :=
    compatibleTubes.terminalConeBound_pos jlast hjlast
  have hControlSourcePos : 0 < controlRadii.radius ⟨0, by omega⟩ :=
    controlRadii.radius_pos ⟨0, by omega⟩
  have hControlSourceLe : controlRadii.radius ⟨0, by omega⟩ ≤ sourceRadius :=
    (le_of_lt hControlSource).trans hr0Source
  have hActualK0LeSource : actualK0 ≤ sourceKappa := by
    dsimp [actualK0, K0] at hActualK0 ⊢
    linarith
  obtain ⟨sourceLeftSector, sourceRightSector,
      hSourceLeftSectorEq, hSourceRightSectorEq,
      hSourceLeftOpen, hSourceRightOpen,
      hSourceLeftConvex, hSourceRightConvex,
      hSourceLeftBall, hSourceRightBall,
      hSourceLeftClosure, hSourceRightClosure,
      hSourceNotLeft, hSourceNotRight,
      hSourceLeftAvoid, hSourceRightAvoid⟩ :=
    hsourceSectors (controlRadii.radius ⟨0, by omega⟩) actualK0
      hControlSourcePos hControlSourceLe hActualK0Pos hActualK0LeSource
  let SelectedSide : Set (EuclideanSpace ℝ (Fin 2)) :=
    if positiveSide then S.rightStrip else S.leftStrip
  let StartSector : Set (EuclideanSpace ℝ (Fin 2)) :=
    if positiveSide then sourceRightSector else sourceLeftSector
  let targetIndex : Fin Aarc.vertices.length := ⟨itarget, hitarget⟩
  let Vin : Set (EuclideanSpace ℝ (Fin 2)) :=
    if positiveSide then localSideData.rightSidePiece targetIndex
    else localSideData.leftSidePiece targetIndex
  let cap : ℝ := controlRadii.radius targetIndex /
    dist Aarc.vertices[itarget] Aarc.vertices[jlast]
  have hTargetDist : dist Aarc.vertices[itarget] Aarc.vertices[jlast] = ‖d‖ := by
    simp [htargetVertex, d, dist_eq_norm, norm_sub_rev]
  have hControlTargetPos : 0 < controlRadii.radius targetIndex :=
    controlRadii.radius_pos targetIndex
  have hcap : 0 < cap := by
    dsimp [cap]
    rw [hTargetDist]
    positivity
  have hcapNorm : cap * ‖d‖ = controlRadii.radius targetIndex := by
    dsimp [cap]
    rw [hTargetDist]
    field_simp [hnormd.ne']
  have hcapRho : 2 * cap * ‖d‖ < rhoTerm := by
    have hrad : controlRadii.radius targetIndex < r1 := by
      simpa [targetIndex] using hControlTarget
    have hr1rho : r1 ≤ rhoTerm / 8 := by
      exact hr1Cap.trans (by simp [terminalRadiusCap])
    rw [mul_assoc, hcapNorm]
    linarith
  have hkappaSmall : actualK1 * (|mu| + 1) < nu / 4 := by
    have hnonneg : 0 < |mu| + 1 := by positivity
    calc
      actualK1 * (|mu| + 1) < K1 * (|mu| + 1) :=
        mul_lt_mul_of_pos_right (by simpa [actualK1] using hActualK1) hnonneg
      _ = nu / 8 := by
        dsimp [K1]
        field_simp [hnonneg.ne']
      _ < nu / 4 := by linarith
  let lambda : ℝ := min (1 / 2 : ℝ)
    (min (cap / (8 * (1 + |mu| + nu)))
      (rhoTerm / (2 * (‖d‖ + ‖y - x‖))))
  have hsumPos : 0 < 1 + |mu| + nu := by positivity
  have hnormSumPos : 0 < ‖d‖ + ‖y - x‖ := by positivity
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    exact lt_min (by norm_num)
      (lt_min (div_pos hcap (by positivity))
        (div_pos hrhoTerm (by positivity)))
  have hlambda_one : lambda < 1 := by
    have hle : lambda ≤ (1 / 2 : ℝ) := min_le_left _ _
    linarith
  have hsmallCap : 4 * lambda * (1 + |mu| + nu) < cap := by
    have hle : lambda ≤ cap / (8 * (1 + |mu| + nu)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hmul := mul_le_mul_of_nonneg_right hle hsumPos.le
    have hdenom : 0 < 8 * (1 + |mu| + nu) := by positivity
    have hcalc : cap / (8 * (1 + |mu| + nu)) *
        (1 + |mu| + nu) = cap / 8 := by
      field_simp [hsumPos.ne']
    rw [hcalc] at hmul
    linarith
  have hsmallRho : lambda * (‖d‖ + ‖y - x‖) < rhoTerm := by
    have hle : lambda ≤ rhoTerm / (2 * (‖d‖ + ‖y - x‖)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hmul := mul_le_mul_of_nonneg_right hle hnormSumPos.le
    have hcalc : rhoTerm / (2 * (‖d‖ + ‖y - x‖)) *
        (‖d‖ + ‖y - x‖) = rhoTerm / 2 := by
      field_simp [hnormSumPos.ne']
    rw [hcalc] at hmul
    linarith
  have segment_point_on_scaled_line
      (a b base z v : EuclideanSpace ℝ (Fin 2)) (scale : ℝ)
      (hbase : base ∈ segment ℝ a b) (hz : z ∈ segment ℝ a b)
      (hscale : v = scale • (b - a)) (hscale0 : scale ≠ 0) :
      ∃ c : ℝ, z = base + c • v := by
    rw [segment_eq_image_lineMap] at hbase hz
    rcases hbase with ⟨s, _hs, rfl⟩
    rcases hz with ⟨t, _ht, rfl⟩
    refine ⟨(t - s) / scale, ?_⟩
    simp only [AffineMap.lineMap_apply_module]
    rw [hscale]
    rw [smul_smul]
    have hscalar : (t - s) / scale * scale = t - s := by
      field_simp [hscale0]
    rw [hscalar]
    module
  have first_point_line (z : EuclideanSpace ℝ (Fin 2))
      (hzClosed : z ∈ Metric.closedBall x Disk.radius)
      (hzFirst : z ∈ (D.edgeArc firstEdge).carrier) :
      ∃ c : ℝ, z = x + c • d := by
    have hzSeg : z ∈ segment ℝ (D.edgeArc firstEdge).vertices[i]
        (D.edgeArc firstEdge).vertices[i + 1] := by
      have hzBoth : z ∈ Metric.closedBall x Disk.radius ∩
          (D.edgeArc firstEdge).carrier := ⟨hzClosed, hzFirst⟩
      rw [first_disk_local] at hzBoth
      exact hzBoth.2
    rcases hlastScale with ⟨scale, hscale0, hscale⟩
    exact segment_point_on_scaled_line _ _ x z d scale
      (openSegment_subset_segment ℝ _ _ hxOpenFirst) hzSeg hscale hscale0
  have second_point_line (z : EuclideanSpace ℝ (Fin 2))
      (hzClosed : z ∈ Metric.closedBall x Disk.radius)
      (hzSecond : z ∈ (D.edgeArc secondEdge).carrier) :
      ∃ c : ℝ, z = x + c • (y - x) := by
    have hzSeg : z ∈ segment ℝ (D.edgeArc secondEdge).vertices[j]
        (D.edgeArc secondEdge).vertices[j + 1] := by
      have hzBoth : z ∈ Metric.closedBall x Disk.radius ∩
          (D.edgeArc secondEdge).carrier := ⟨hzClosed, hzSecond⟩
      rw [second_disk_local] at hzBoth
      exact hzBoth.2
    rcases hsecondScale with ⟨scale, hscale0, hscale⟩
    exact segment_point_on_scaled_line _ _ x z (y - x) scale
      (openSegment_subset_segment ℝ _ _ hxOpenSecond) hzSeg hscale hscale0
  let Old : Set (EuclideanSpace ℝ (Fin 2)) := A ∪ B ∪ Bplus ∪ Rbeta ∪ H
  have old_point_edge_or_vertex (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ Old) :
      (∃ e : G.edgeFinset, z ∈ (D.edgeArc e).carrier) ∨
        ∃ v : V, z = D.vertexPlacement v := by
    rcases hz with (((hzA | hzB) | hzBplus) | hzRbeta) | hzH
    · exact Or.inl ⟨firstEdge, by
        have := FirstCut.prefix_carrier_subset (hA ▸ hzA)
        simpa [hfirstCarrier] using this⟩
    · exact Or.inl ⟨secondEdge, by
        have := SecondCut.prefix_carrier_subset (hB ▸ hzB)
        simpa [hsecondCarrier] using this⟩
    · exact Or.inl ⟨secondEdge, hBplusSecondCarrier hzBplus⟩
    · exact Or.inl ⟨secondEdge, (hRbeta ▸ hzRbeta).1⟩
    · rw [hH] at hzH
      rcases hzH with hzEdges | hzVertex
      · rcases Set.mem_iUnion.mp hzEdges with ⟨e, he⟩
        by_cases heFirst : e = firstEdge
        · subst e
          simp only [if_pos rfl] at he
          exact Or.inl ⟨firstEdge, he.1⟩
        · by_cases heSecond : e = secondEdge
          · subst e
            simp only [if_neg (Ne.symm hedges), if_pos rfl] at he
            exact Or.inl ⟨secondEdge, he.1⟩
          · simp only [if_neg heFirst, if_neg heSecond] at he
            exact Or.inl ⟨e, he⟩
      · rcases hzVertex with ⟨v, _hvu, rfl⟩
        exact Or.inr ⟨v, rfl⟩
  have hOldLocal : Metric.closedBall x rhoTerm ∩ Old ⊆
      {z | ∃ c : ℝ, z = x + c • d} ∪
        {z | ∃ c : ℝ, z = x + c • (y - x)} := by
    intro z hz
    have hzDisk : z ∈ Metric.closedBall x Disk.radius :=
      Metric.closedBall_subset_closedBall hrhoTermDisk.le hz.1
    rcases old_point_edge_or_vertex z hz.2 with ⟨e, hze⟩ | ⟨v, hzv⟩
    · have hzAll : z ∈ Metric.closedBall x Disk.radius ∩
          (⋃ e : G.edgeFinset, (D.edgeArc e).carrier) :=
        ⟨hzDisk, Set.mem_iUnion.mpr ⟨e, hze⟩⟩
      rw [Disk.exact_local_drawing_carrier] at hzAll
      rcases hzAll.2 with hzFirstDisk | hzSecondDisk
      · rcases hDiskEdges with hlabels | hlabels
        · exact Or.inl (first_point_line z hzDisk (by simpa [hlabels.1] using hzFirstDisk))
        · exact Or.inr (second_point_line z hzDisk (by simpa [hlabels.1] using hzFirstDisk))
      · rcases hDiskEdges with hlabels | hlabels
        · exact Or.inr (second_point_line z hzDisk (by simpa [hlabels.2] using hzSecondDisk))
        · exact Or.inl (first_point_line z hzDisk (by simpa [hlabels.2] using hzSecondDisk))
    · subst z
      exact False.elim (Disk.no_vertex_in_closedBall v hzDisk)
  have hSourceLeftPiece : sourceLeftSector =
      localSideData.leftSidePiece ⟨0, by omega⟩ := by
    rw [hSourceLeftSectorEq, hSourceLeftEq]
    simp only [hsource0, hAarcSource, d0, actualK0, dist_eq_norm, norm_sub_rev]
  have hSourceRightPiece : sourceRightSector =
      localSideData.rightSidePiece ⟨0, by omega⟩ := by
    rw [hSourceRightSectorEq, hSourceRightEq]
    simp only [hsource0, hAarcSource, d0, actualK0, dist_eq_norm, norm_sub_rev]
  have hTargetRightNormalized : localSideData.rightSidePiece targetIndex =
      (fun z : EuclideanSpace ℝ (Fin 2) =>
        x + z 0 • d + z 1 • PlanarRot90 d) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < cap ^ 2 ∧
          0 < z 1 ∧ z 1 < actualK1 * z 0} := by
    simpa [targetIndex, itarget, jlast, htargetVertex, d, cap, actualK1]
      using hTargetRightEq
  have hTargetLeftNormalized : localSideData.leftSidePiece targetIndex =
      (fun z : EuclideanSpace ℝ (Fin 2) =>
        x + z 0 • d + z 1 • PlanarRot90 d) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < cap ^ 2 ∧
          -actualK1 * z 0 < z 1 ∧ z 1 < 0} := by
    simpa [targetIndex, itarget, jlast, htargetVertex, d, cap, actualK1]
      using hTargetLeftEq
  have hVinEq : Vin =
      (fun z : EuclideanSpace ℝ (Fin 2) => x + z 0 • d + z 1 • n) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < cap ^ 2 ∧
          0 < z 1 ∧ z 1 < actualK1 * z 0} := by
    by_cases hpos : positiveSide
    · simpa [Vin, n, hpos] using hTargetRightNormalized
    · rw [show Vin = localSideData.leftSidePiece targetIndex by simp [Vin, hpos],
          hTargetLeftNormalized]
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        let w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z 0, -z 1]
        refine ⟨w, ?_, ?_⟩
        · dsimp [w]
          constructor
          · exact hz.1
          constructor
          · nlinarith [hz.2.1]
          constructor <;> linarith [hz.2.2.1, hz.2.2.2]
        · simp only [n, hpos, if_false, w, Matrix.cons_val_zero,
              Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul]
          module
      · rintro ⟨z, hz, rfl⟩
        let w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z 0, -z 1]
        refine ⟨w, ?_, ?_⟩
        · dsimp [w]
          constructor
          · exact hz.1
          constructor
          · nlinarith [hz.2.1]
          constructor <;> linarith [hz.2.2.1, hz.2.2.2]
        · simp only [n, hpos, if_false, w, Matrix.cons_val_zero,
              Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul]
          module
  have hVinOpen : IsOpen Vin := by
    by_cases hpos : positiveSide
    · simpa [Vin, hpos] using localSideData.rightSidePiece_open targetIndex
    · simpa [Vin, hpos] using localSideData.leftSidePiece_open targetIndex
  have hVinSelected : Vin ⊆ SelectedSide := by
    intro z hz
    by_cases hpos : positiveSide
    · simp only [SelectedSide, if_pos hpos]
      rw [hRightEq]
      exact Or.inr (Set.mem_iUnion.mpr ⟨targetIndex, by simpa [Vin, hpos] using hz⟩)
    · simp only [SelectedSide, if_neg hpos]
      rw [hLeftEq]
      exact Or.inr (Set.mem_iUnion.mpr ⟨targetIndex, by simpa [Vin, hpos] using hz⟩)
  have hStartSubset : StartSector ⊆ SelectedSide := by
    intro z hz
    by_cases hpos : positiveSide
    · simp only [SelectedSide, if_pos hpos]
      rw [hRightEq]
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨0, by omega⟩,
        by simpa [StartSector, hpos, hSourceRightPiece] using hz⟩)
    · simp only [SelectedSide, if_neg hpos]
      rw [hLeftEq]
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨0, by omega⟩,
        by simpa [StartSector, hpos, hSourceLeftPiece] using hz⟩)
  have hNear : ∃ eps : ℝ, 0 < eps ∧
      SelectedSide ∩ Metric.ball x eps ⊆ Vin := by
    refine ⟨controlRadii.radius targetIndex, hControlTargetPos, ?_⟩
    intro q hq
    have hqTargetDisk : q ∈ vertexLocalPieces.vertexDisk targetIndex := by
      rw [vertexLocalPieces.vertexDisk_eq]
      simpa [targetIndex, htargetVertex] using hq.2
    have hqTargetClosed : q ∈
        Metric.closedBall Aarc.vertices[targetIndex.1]
          (controlRadii.radius targetIndex) :=
      vertexLocalPieces.vertexDisk_subset_closed_control_disk targetIndex hqTargetDisk
    have tube_nonterminal_impossible (k : ℕ)
        (hk : k + 1 < Aarc.vertices.length) (hklast : k ≠ jlast)
        (hqTube : q ∈ sep.tube k hk) : False := by
      have hkTarget : targetIndex.1 ≠ k := by
        dsimp [targetIndex, itarget, jlast] at *
        omega
      have hkTargetSucc : targetIndex.1 ≠ k + 1 := by
        dsimp [targetIndex, itarget, jlast] at *
        omega
      exact Set.disjoint_left.mp
        (vertexLocalPieces.vertexDisk_disjoint_nonincident_tubes
          targetIndex k hk hkTarget hkTargetSucc) hqTargetDisk hqTube
    have vertex_nontarget_impossible (idx : Fin Aarc.vertices.length)
        (hne : idx ≠ targetIndex)
        (hqPiece : q ∈ localSideData.vertexCollar idx) : False := by
      have hqDisk := localSideData.vertexCollar_subset_vertexDisk idx hqPiece
      exact Set.disjoint_left.mp
        (vertexLocalPieces.vertexDisk_disjoint_other_control_disks hne)
          hqDisk hqTargetClosed
    by_cases hpos : positiveSide
    · have hqRight : q ∈ S.rightStrip := by
        simpa only [SelectedSide, if_pos hpos] using hq.1
      rw [hRightEq] at hqRight
      rcases hqRight with hqHalf | hqPiece
      · rcases Set.mem_iUnion.mp hqHalf with ⟨k, hkUnion⟩
        rcases Set.mem_iUnion.mp hkUnion with ⟨hk, hqHalf⟩
        by_cases hklast : k = jlast
        · subst k
          have hqAttach : q ∈
              vertexLocalPieces.incomingRightAttachment jlast hjlast := by
            rw [vertexLocalPieces.incomingRightAttachment_eq]
            exact ⟨by simpa [targetIndex, hjlast_target] using hqTargetDisk,
              by simpa [sep] using hqHalf⟩
          have hqVin := localSideData.incomingRightAttachment_subset_rightSidePiece
            jlast hjlast hqAttach
          simpa [Vin, hpos, targetIndex, hjlast_target] using hqVin
        · exact False.elim (tube_nonterminal_impossible k hk hklast
            (sep.rightHalf_subset_tube k hk (by simpa [sep] using hqHalf)))
      · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
        by_cases hidx : idx = targetIndex
        · subst idx
          simpa [Vin, hpos] using hqPiece
        · exact False.elim (vertex_nontarget_impossible idx hidx
            (localSideData.rightSidePiece_subset_vertexCollar idx hqPiece))
    · have hqLeft : q ∈ S.leftStrip := by
        simpa only [SelectedSide, if_neg hpos] using hq.1
      rw [hLeftEq] at hqLeft
      rcases hqLeft with hqHalf | hqPiece
      · rcases Set.mem_iUnion.mp hqHalf with ⟨k, hkUnion⟩
        rcases Set.mem_iUnion.mp hkUnion with ⟨hk, hqHalf⟩
        by_cases hklast : k = jlast
        · subst k
          have hqAttach : q ∈
              vertexLocalPieces.incomingLeftAttachment jlast hjlast := by
            rw [vertexLocalPieces.incomingLeftAttachment_eq]
            exact ⟨by simpa [targetIndex, hjlast_target] using hqTargetDisk,
              by simpa [sep] using hqHalf⟩
          have hqVin := localSideData.incomingLeftAttachment_subset_leftSidePiece
            jlast hjlast hqAttach
          simpa [Vin, hpos, targetIndex, hjlast_target] using hqVin
        · exact False.elim (tube_nonterminal_impossible k hk hklast
            (sep.leftHalf_subset_tube k hk (by simpa [sep] using hqHalf)))
      · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
        by_cases hidx : idx = targetIndex
        · subst idx
          simpa [Vin, hpos] using hqPiece
        · exact False.elim (vertex_nontarget_impossible idx hidx
            (localSideData.leftSidePiece_subset_vertexCollar idx hqPiece))
  have hyOld : y ∈ Old := by
    exact Or.inl (Or.inl (Or.inr hyBplus))
  have hyRho : y ∈ Metric.ball x rhoTerm := by
    simpa [Metric.mem_ball, dist_comm] using hyRhoTerm
  obtain ⟨k, hk, Q, Side, Bridge, terminalGate, sideSource,
      quadrantGate, h, predecessor, approach, lastGate,
      hQconvex, hQcompact, hxQ, hyQ, hxnotQ,
      hSideOpen, hSideConvex, hSideCompact,
      hBridgeOpen, hBridgeConvex, hBridgeCompact,
      hterminalSideClosure, hterminalNotSide,
      hsourceSideClosure, hsourceNotSide,
      hsourceBridgeClosure, hsourceNotBridge,
      hquadrantBridgeClosure, hquadrantNotBridge,
      hterminalNeSource, hsourceNeQuadrant,
      hterminalSourceSegment, hterminalSourceOpen,
      hsourceQuadrantSegment, hsourceQuadrantOpen,
      hquadrantQ, hquadrantNe,
      hsourceQuadrantQ, hSideBridgeClosure, hSideQClosure,
      hBridgeQClosure, hquadrantYSegment, hQBall, hQOld, hQBad,
      hSideBall, hBridgeBall, hCellsOld,
      hVinOpen', hVinConvex, hhVin, hhNeTerminal, hVinSelected',
      hxVinClosure, hNear', hVinBall, hVinQ, hVinOld,
      hterminalVinClosure, hterminalNotVin,
      hhTerminalSegment, hhTerminalOpen,
      hVinSideClosure, hVinBridgeClosure, hVinSide,
      hPredecessorSubset, hApproachSubset,
      hPredecessorTarget, hApproachSource, hPredecessorApproach,
      hApproachTarget, hApproachTerminal, hPredecessorTerminal,
      hSupporting, gateA, gateB, hgateA, hgateB, hgateEq,
      hterminalGateFormula⟩ :=
    OrdinaryAdjacentEdgesTerminalCollarCompatibility
      x y d n lambda mu nu actualK1 cap rhoTerm
      SelectedSide Vin Old (∅ : Finset (EuclideanSpace ℝ (Fin 2)))
      hlambda hlambda_one hnu hActualK1Pos hcap hkappaSmall hrhoTerm hd
      hdn hnd hdd hnn hyDecomp hlinear hVinEq hVinOpen hVinSelected hNear
      hyRho hsmallCap hcapRho hsmallRho hOldLocal hyOld (by simp)
  have left_half_convex (m : ℕ) (hm : m + 1 < Aarc.vertices.length) :
      Convex ℝ (sep.leftHalf m hm) := by
    rw [sep.leftHalf_eq]
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    rcases hz₁ with ⟨t₁, ht₁, s₁, hs₁, rfl⟩
    rcases hz₂ with ⟨t₂, ht₂, s₂, hs₂, rfl⟩
    refine ⟨a * t₁ + b * t₂,
      (convex_Ioo (sep.lowerParam m hm) (sep.upperParam m hm))
        ht₁ ht₂ ha hb hab,
      a * s₁ + b * s₂,
      (convex_Ioo 0 (sep.halfWidth m hm)) hs₁ hs₂ ha hb hab, ?_⟩
    simp only [AffineMap.lineMap_apply_module]
    have hb : b = 1 - a := by linarith
    subst b
    module
  have right_half_convex (m : ℕ) (hm : m + 1 < Aarc.vertices.length) :
      Convex ℝ (sep.rightHalf m hm) := by
    rw [sep.rightHalf_eq]
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    rcases hz₁ with ⟨t₁, ht₁, s₁, hs₁, rfl⟩
    rcases hz₂ with ⟨t₂, ht₂, s₂, hs₂, rfl⟩
    refine ⟨a * t₁ + b * t₂,
      (convex_Ioo (sep.lowerParam m hm) (sep.upperParam m hm))
        ht₁ ht₂ ha hb hab,
      a * s₁ + b * s₂,
      (convex_Ioo (-sep.halfWidth m hm) 0) hs₁ hs₂ ha hb hab, ?_⟩
    simp only [AffineMap.lineMap_apply_module]
    have hb : b = 1 - a := by linarith
    subst b
    module
  have event_selected_slice (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ XA) :
      SelectedSide ∩ Metric.ball p (eventRadius p) =
        (if positiveSide then sep.rightHalf (eventIndex p)
            (eventIndex_spec p hp).choose
          else sep.leftHalf (eventIndex p) (eventIndex_spec p hp).choose) ∩
      Metric.ball p (eventRadius p) := by
    have hjOwner := (eventIndex_spec p hp).choose
    apply Set.Subset.antisymm
    · rintro q ⟨hqSelected, hqBall⟩
      have hqdist : dist p q < eventRadius p := by
        simpa [Metric.mem_ball, dist_comm] using hqBall
      have vertex_piece_impossible
          (idx : Fin Aarc.vertices.length)
          (hqPiece : q ∈ localSideData.vertexCollar idx) : False := by
        have hqDisk := localSideData.vertexCollar_subset_vertexDisk idx hqPiece
        rw [vertexLocalPieces.vertexDisk_eq] at hqDisk
        have hqv : dist q Aarc.vertices[idx.1] <
            controlRadii.radius idx := by
          simpa [Metric.mem_ball] using hqDisk
        have hveta := controlRadii.radius_lt_eta idx
        have hreta := heta_event p hp
        have hrclear := (eventPackage_spec p hp).2.1
        have hvball : Aarc.vertices[idx.1] ∈
            Metric.ball p (eventClearance p) := by
          rw [Metric.mem_ball]
          calc
            dist Aarc.vertices[idx.1] p = dist p Aarc.vertices[idx.1] := dist_comm _ _
            _ ≤ dist p q + dist q Aarc.vertices[idx.1] := dist_triangle _ _ _
            _ < eventRadius p + eta := by linarith
            _ < eventClearance p := by linarith
        have hvForbidden : Aarc.vertices[idx.1] ∈ eventForbidden p := by
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
            (by simpa using List.getElem_mem idx.2)))))
        exact (eventClearance_spec p hp).2 hvball hvForbidden
      have half_index_eq
          (m : ℕ) (hm : m + 1 < Aarc.vertices.length)
          (s : ℝ) (hsabs : |s| < sep.halfWidth m hm)
          (t : ℝ) (ht : t ∈ Set.Ioo (sep.lowerParam m hm) (sep.upperParam m hm))
          (hqFormula : q = AffineMap.lineMap Aarc.vertices[m]
              Aarc.vertices[m + 1] t + s • sep.normal m hm) :
          m = eventIndex p := by
        by_contra hmOwner
        let center := AffineMap.lineMap Aarc.vertices[m] Aarc.vertices[m + 1] t
        have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
          exact ⟨(sep.lowerParam_pos m hm).le.trans ht.1.le,
            ht.2.le.trans (sep.upperParam_lt_one m hm).le⟩
        have hcenterSegment : center ∈ segment ℝ Aarc.vertices[m]
            Aarc.vertices[m + 1] := by
          rw [segment_eq_image_lineMap]
          exact ⟨t, ht01, rfl⟩
        have hqcenter : dist q center < eta := by
          rw [hqFormula, dist_eq_norm]
          have hsub : center + s • sep.normal m hm - center =
              s • sep.normal m hm := by abel
          rw [hsub, norm_smul, Real.norm_eq_abs]
          have hvertices : Aarc.vertices[m] ≠ Aarc.vertices[m + 1] := by
            intro heq
            have hidx := (Aarc.simple_vertices.getElem_inj_iff
              (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 heq
            omega
          have hnormpos : 0 < ‖sep.normal m hm‖ := by
            rw [sep.normal_norm_eq_segment_length m hm]
            exact dist_pos.mpr hvertices
          exact (mul_lt_mul_of_pos_right hsabs hnormpos).trans
            (sep.halfWidth_mul_normal_norm_lt_eta m hm)
        have hcenterBall : center ∈ Metric.ball p (eventClearance p) := by
          rw [Metric.mem_ball]
          calc
            dist center p = dist p center := dist_comm _ _
            _ ≤ dist p q + dist q center := dist_triangle _ _ _
            _ < eventRadius p + eta := by linarith
            _ < eventClearance p := by
              have hrclear := (eventPackage_spec p hp).2.1
              have hreta := heta_event p hp
              linarith
        have hcenterOther : center ∈ otherSegments p := by
          simp only [otherSegments, Set.mem_iUnion]
          let fm : Fin (Aarc.vertices.length - 1) := ⟨m, by omega⟩
          refine ⟨fm, ?_⟩
          simp only [fm, hmOwner, ↓reduceIte]
          exact hcenterSegment
        have hcenterForbidden : center ∈ eventForbidden p := by
          exact Or.inr hcenterOther
        exact (eventClearance_spec p hp).2 hcenterBall hcenterForbidden
      by_cases hpos : positiveSide
      · have hqRight : q ∈ S.rightStrip := by
          simpa only [SelectedSide, if_pos hpos] using hqSelected
        rw [hRightEq] at hqRight
        rcases hqRight with hqHalf | hqPiece
        · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
          rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
          rw [sep.rightHalf_eq] at hqHalf
          rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
          have hsabs : |s| < sep.halfWidth m hm := by
            rw [abs_of_neg hs.2]
            have hneg := neg_lt_neg hs.1
            simpa using hneg
          have hmOwner := half_index_eq m hm s hsabs t ht hqFormula
          subst m
          exact ⟨by simpa [hpos] using
            (show q ∈ sep.rightHalf (eventIndex p) hjOwner from
              (by rw [sep.rightHalf_eq]; exact ⟨t, ht, s, hs, hqFormula⟩)), hqBall⟩
        · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
          exact False.elim (vertex_piece_impossible idx
            (localSideData.rightSidePiece_subset_vertexCollar idx hqPiece))
      · have hqLeft : q ∈ S.leftStrip := by
          simpa only [SelectedSide, if_neg hpos] using hqSelected
        rw [hLeftEq] at hqLeft
        rcases hqLeft with hqHalf | hqPiece
        · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
          rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
          rw [sep.leftHalf_eq] at hqHalf
          rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
          have hsabs : |s| < sep.halfWidth m hm := by
            rw [abs_of_pos hs.1]
            exact hs.2
          have hmOwner := half_index_eq m hm s hsabs t ht hqFormula
          subst m
          exact ⟨by simpa [hpos] using
            (show q ∈ sep.leftHalf (eventIndex p) hjOwner from
              (by rw [sep.leftHalf_eq]; exact ⟨t, ht, s, hs, hqFormula⟩)), hqBall⟩
        · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
          exact False.elim (vertex_piece_impossible idx
            (localSideData.leftSidePiece_subset_vertexCollar idx hqPiece))
    · rintro q ⟨hqHalf, hqBall⟩
      refine ⟨?_, hqBall⟩
      by_cases hpos : positiveSide
      · simp only [SelectedSide, if_pos hpos]
        rw [hRightEq]
        exact Or.inl (Set.mem_iUnion.mpr ⟨eventIndex p,
          Set.mem_iUnion.mpr ⟨(eventIndex_spec p hp).choose,
            by simpa [hpos] using hqHalf⟩⟩)
      · simp only [SelectedSide, if_neg hpos]
        rw [hLeftEq]
        exact Or.inl (Set.mem_iUnion.mpr ⟨eventIndex p,
          Set.mem_iUnion.mpr ⟨(eventIndex_spec p hp).choose,
            by simpa [hpos] using hqHalf⟩⟩)
  have hEventLocal : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      0 < eventRadius p ∧
        Convex ℝ (SelectedSide ∩ Metric.ball p (eventRadius p)) ∧
          ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
            s ∈ Kclean.segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
              Metric.ball p (eventRadius p) ∩ H =
                Metric.ball p (eventRadius p) ∩ segment ℝ s.1 s.2 ∧
              Metric.ball p (eventRadius p) ∩ Rbeta = ∅ := by
    intro p hp
    refine ⟨(eventPackage_spec p hp).1, ?_, eventSegment p,
      (eventPackage_spec p hp).2.2.1,
      (eventPackage_spec p hp).2.2.2.1,
      (eventPackage_spec p hp).2.2.2.2.1,
      (eventPackage_spec p hp).2.2.2.2.2⟩
    rw [event_selected_slice p hp]
    by_cases hpos : positiveSide
    · simp only [if_pos hpos]
      exact (right_half_convex (eventIndex p) (eventIndex_spec p hp).choose).inter
        (convex_ball p (eventRadius p))
    · simp only [if_neg hpos]
      exact (left_half_convex (eventIndex p) (eventIndex_spec p hp).choose).inter
        (convex_ball p (eventRadius p))
  have hEventClean : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      p ∉ (Kclean.points : Set _) ∧
        ∃ m : ℕ, ∃ hm : m + 1 < Aarc.vertices.length,
          p ∈ openSegment ℝ Aarc.vertices[m] Aarc.vertices[m + 1] ∧
            ∃! s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
              s ∈ Kclean.segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
                ¬ ∃ c : ℝ, s.2 - s.1 =
                  c • (Aarc.vertices[m + 1] - Aarc.vertices[m]) := by
    intro p hp
    obtain ⟨hm, hpOpen, s, hsK, hps, hnonparallel, hunique, _hlocal⟩ :=
      eventIndex_spec p hp
    refine ⟨(event_data p hp).1, eventIndex p, hm, hpOpen, s,
      ⟨hsK, hps, hnonparallel⟩, ?_⟩
    intro t ht
    exact hunique t ht.1 ht.2.1
  have hStartOpen : IsOpen StartSector := by
    by_cases hpos : positiveSide
    · simpa [StartSector, hpos] using hSourceRightOpen
    · simpa [StartSector, hpos] using hSourceLeftOpen
  have hStartConvex : Convex ℝ StartSector := by
    by_cases hpos : positiveSide
    · simpa [StartSector, hpos] using hSourceRightConvex
    · simpa [StartSector, hpos] using hSourceLeftConvex
  have hStartBall : StartSector ⊆
      Metric.ball (D.vertexPlacement u) (controlRadii.radius ⟨0, by omega⟩) := by
    by_cases hpos : positiveSide
    · simpa [StartSector, hpos] using hSourceRightBall
    · simpa [StartSector, hpos] using hSourceLeftBall
  have hSourceStartClosure : D.vertexPlacement u ∈ closure StartSector := by
    by_cases hpos : positiveSide
    · simpa [StartSector, hpos] using hSourceRightClosure
    · simpa [StartSector, hpos] using hSourceLeftClosure
  have hSourceNotStart : D.vertexPlacement u ∉ StartSector := by
    by_cases hpos : positiveSide
    · simpa [StartSector, hpos] using hSourceNotRight
    · simpa [StartSector, hpos] using hSourceNotLeft
  have hStartAvoidRaySet :
      StartSector ∩
        (({D.vertexPlacement u} : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ sourceDirections},
            {q | ∃ c : ℝ, 0 ≤ c ∧
              q = D.vertexPlacement u + c • v.1}) = ∅ := by
    by_cases hpos : positiveSide
    · simpa [StartSector, hpos] using hSourceRightAvoid
    · simpa [StartSector, hpos] using hSourceLeftAvoid
  have hStartAvoidAxis :
      StartSector ∩
        {q | ∃ c : ℝ, 0 ≤ c ∧ q = D.vertexPlacement u + c • d0} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    rcases hq.2 with ⟨c, _hc, hqAxis⟩
    have axis_coefficient_zero :
        inner ℝ (q - D.vertexPlacement u) (PlanarRot90 d0) /
            (‖d0‖ ^ 2) = 0 := by
      rw [hqAxis]
      simp only [add_sub_cancel_left, inner_smul_left, PlanarRot90Orthogonal,
        mul_zero, zero_div]
    by_cases hpos : positiveSide
    · have hqSector : q ∈ sourceRightSector := by
        simpa [StartSector, hpos] using hq.1
      rw [hSourceRightSectorEq] at hqSector
      rcases hqSector with ⟨z, hz, hqFormula⟩
      have hrep : q - D.vertexPlacement u =
          z 0 • d0 + z 1 • PlanarRot90 d0 := by
        calc
          q - D.vertexPlacement u =
              (D.vertexPlacement u + z 0 • d0 + z 1 • PlanarRot90 d0) -
                D.vertexPlacement u :=
            congrArg (fun w => w - D.vertexPlacement u) hqFormula.symm
          _ = z 0 • d0 + z 1 • PlanarRot90 d0 := by abel
      have hcoeff := PlanarRot90CoefficientUniqueness
        (d := d0) (v := q - D.vertexPlacement u) hd0 hrep
      have hz1 : z 1 = 0 := hcoeff.2.trans axis_coefficient_zero
      linarith [hz.2.2.2]
    · have hqSector : q ∈ sourceLeftSector := by
        simpa [StartSector, hpos] using hq.1
      rw [hSourceLeftSectorEq] at hqSector
      rcases hqSector with ⟨z, hz, hqFormula⟩
      have hrep : q - D.vertexPlacement u =
          z 0 • d0 + z 1 • PlanarRot90 d0 := by
        calc
          q - D.vertexPlacement u =
              (D.vertexPlacement u + z 0 • d0 + z 1 • PlanarRot90 d0) -
                D.vertexPlacement u :=
            congrArg (fun w => w - D.vertexPlacement u) hqFormula.symm
          _ = z 0 • d0 + z 1 • PlanarRot90 d0 := by abel
      have hcoeff := PlanarRot90CoefficientUniqueness
        (d := d0) (v := q - D.vertexPlacement u) hd0 hrep
      have hz1 : z 1 = 0 := hcoeff.2.trans axis_coefficient_zero
      linarith [hz.2.2.1]
  have hStartAvoidFirstEdge :
      StartSector ∩ (D.edgeArc firstEdge).carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqSourceRadius : q ∈ Metric.ball (D.vertexPlacement u) sourceRadius :=
      Metric.ball_subset_ball hControlSourceLe (hStartBall hq.1)
    have hqAxis := hsourceEdgeCover ⟨hqSourceRadius, hq.2⟩
    exact Set.eq_empty_iff_forall_notMem.mp hStartAvoidAxis q ⟨hq.1, hqAxis⟩
  have hStartAvoidWithoutFirst :
      StartSector ∩ OrdinaryDrawingImageWithoutEdge G D firstEdge = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqSourceRadius : q ∈ Metric.ball (D.vertexPlacement u) sourceRadius :=
      Metric.ball_subset_ball hControlSourceLe (hStartBall hq.1)
    have hqRays := hsourceCover ⟨hqSourceRadius, hq.2⟩
    exact Set.eq_empty_iff_forall_notMem.mp hStartAvoidRaySet q ⟨hq.1, hqRays⟩
  have hStartAvoidOld :
      StartSector ∩ ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪
        (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqOld : q ∈ Old := by
      rcases hq.2 with hqOld | hqBad
      · exact hqOld
      · exact hBadSubsetH hqBad |> Or.inr
    rcases old_point_edge_or_vertex q hqOld with ⟨e, hqe⟩ | ⟨v, hqv⟩
    · by_cases he : e = firstEdge
      · subst e
        exact Set.eq_empty_iff_forall_notMem.mp hStartAvoidFirstEdge q ⟨hq.1, hqe⟩
      · have hqWithout : q ∈ OrdinaryDrawingImageWithoutEdge G D firstEdge := by
          exact Or.inr (Set.mem_iUnion.mpr ⟨⟨e, he⟩, hqe⟩)
        exact Set.eq_empty_iff_forall_notMem.mp hStartAvoidWithoutFirst q
          ⟨hq.1, hqWithout⟩
    · have hqWithout : q ∈ OrdinaryDrawingImageWithoutEdge G D firstEdge := by
        exact Or.inl ⟨v, hqv.symm⟩
      exact Set.eq_empty_iff_forall_notMem.mp hStartAvoidWithoutFirst q
        ⟨hq.1, hqWithout⟩
  have hStartClosureBall : closure StartSector ⊆
      Metric.closedBall (D.vertexPlacement u) r0 := by
    apply closure_minimal
    · exact hStartBall.trans
        (Metric.ball_subset_closedBall.trans
          (Metric.closedBall_subset_closedBall hControlSource.le))
    · exact Metric.isClosed_closedBall
  have hEventAvoidStart : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      Disjoint (Metric.closedBall p (eventRadius p)) (closure StartSector) := by
    intro p hp
    exact (event_away_sourceBall p hp).mono_right hStartClosureBall
  have hSelectedChoice :
      SelectedSide = S.leftStrip ∨ SelectedSide = S.rightStrip := by
    by_cases hpos : positiveSide
    · exact Or.inr (by simp [SelectedSide, hpos])
    · exact Or.inl (by simp [SelectedSide, hpos])
  have hSourceSelectedClosure :
      D.vertexPlacement u ∈ closure SelectedSide := by
    exact closure_mono hStartSubset hSourceStartClosure
  have hSelectedCollar : SelectedSide ⊆ S.collar := by
    rcases hSelectedChoice with hleft | hright
    · simpa [hleft] using S.left_subset_collar
    · simpa [hright] using S.right_subset_collar
  have hSelectedAvoidFar : Disjoint SelectedSide FarOld := by
    rw [Set.disjoint_left]
    intro z hzSelected hzFar
    obtain ⟨p, hpAarc, hzp⟩ := hCollarNear z (hSelectedCollar hzSelected)
    exact hetaAvoid z ⟨p, hpAarc, hzp.trans_le heta_le_sep⟩ hzFar
  have hVinControlBall :
      Vin ⊆ Metric.ball x (controlRadii.radius targetIndex) := by
    intro z hz
    have hzCollar : z ∈ localSideData.vertexCollar targetIndex := by
      by_cases hpos : positiveSide
      · exact localSideData.rightSidePiece_subset_vertexCollar targetIndex
          (by simpa [Vin, hpos] using hz)
      · exact localSideData.leftSidePiece_subset_vertexCollar targetIndex
          (by simpa [Vin, hpos] using hz)
    have hzDisk := localSideData.vertexCollar_subset_vertexDisk targetIndex hzCollar
    rw [vertexLocalPieces.vertexDisk_eq] at hzDisk
    simpa [targetIndex, htargetVertex] using hzDisk
  have hVinClosureTargetBall : closure Vin ⊆ Metric.closedBall x r1 := by
    apply closure_minimal
    · exact hVinControlBall.trans
        (Metric.ball_subset_closedBall.trans
          (Metric.closedBall_subset_closedBall hControlTarget.le))
    · exact Metric.isClosed_closedBall
  have hEventAvoidVin : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      Disjoint (Metric.closedBall p (eventRadius p)) (closure Vin) := by
    intro p hp
    exact (event_away_targetBall p hp).mono_right hVinClosureTargetBall
  have hFirstBranchNonempty : Nonempty
      (OrdinaryCrossingLocalBranchData
        (D.edgeArc firstEdge) x Disk.radius) := by
    rcases hDiskEdges with hlabels | hlabels
    · exact ⟨hlabels.1 ▸ Disk.firstBranch⟩
    · exact ⟨hlabels.2 ▸ Disk.secondBranch⟩
  let FirstBranch : OrdinaryCrossingLocalBranchData
      (D.edgeArc firstEdge) x Disk.radius := Classical.choice hFirstBranchNonempty
  have hFirstBranchIndices :
      FirstBranch.beforeIndex = i ∧ FirstBranch.afterIndex = i := by
    rcases FirstBranch.center_case with hsame | hvert
    · have hbefore : FirstBranch.beforeIndex = i :=
        open_index_unique (D.edgeArc firstEdge) x FirstBranch.beforeIndex i
          FirstBranch.beforeIndex_valid hi hsame.2 hxOpenFirst
      exact ⟨hbefore, hsame.1.trans hbefore⟩
    · exfalso
      have hafterValid : FirstBranch.afterIndex <
          (D.edgeArc firstEdge).vertices.length := by
        rw [hvert.1]
        exact FirstBranch.beforeIndex_valid
      exact (open_not_vertices (D.edgeArc firstEdge) x i hi hxOpenFirst)
        (by rw [hvert.2]; exact List.getElem_mem hafterValid)
  have endpoint_outside_closedBall
      (a g : EuclideanSpace ℝ (Fin 2)) (ha : a ≠ x)
      (hgOpen : g ∈ openSegment ℝ a x)
      (hgSphere : g ∈ Metric.sphere x Disk.radius) :
      a ∉ Metric.closedBall x Disk.radius := by
    rw [openSegment_eq_image_lineMap] at hgOpen
    rcases hgOpen with ⟨t, ht, rfl⟩
    intro haBall
    have hdistA : dist x a ≤ Disk.radius := by
      simpa [Metric.mem_closedBall, dist_comm] using haBall
    have hdistApos : 0 < dist x a := dist_pos.mpr ha.symm
    have hlineDist :
        dist (AffineMap.lineMap a x t) x = (1 - t) * dist x a := by
      rw [dist_eq_norm]
      have hdiff : AffineMap.lineMap a x t - x = (1 - t) • (a - x) := by
        simp only [AffineMap.lineMap_apply_module]
        module
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht.2)]
      rw [dist_eq_norm]
      simpa [norm_sub_rev] using rfl
    have hsphere : dist (AffineMap.lineMap a x t) x = Disk.radius := by
      exact Metric.mem_sphere.mp hgSphere
    rw [hlineDist] at hsphere
    have htDistPos : 0 < t * dist x a := mul_pos ht.1 hdistApos
    have himpossible : Disk.radius < Disk.radius := calc
      Disk.radius = (1 - t) * dist x a := hsphere.symm
      _ = dist x a - t * dist x a := by ring
      _ < dist x a := sub_lt_self _ htDistPos
      _ ≤ Disk.radius := hdistA
    exact (lt_irrefl _ himpossible)
  have hFirstLeftOutside :
      (D.edgeArc firstEdge).vertices[i] ∉
        Metric.closedBall x Disk.radius := by
    apply endpoint_outside_closedBall
    · intro heq
      have hne : (D.edgeArc firstEdge).vertices[i] ≠
          (D.edgeArc firstEdge).vertices[i + 1] := by
        intro hv
        have hidx := ((D.edgeArc firstEdge).simple_vertices.getElem_inj_iff
          (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 hv
        omega
      have hmem : (D.edgeArc firstEdge).vertices[i] ∈
          openSegment ℝ (D.edgeArc firstEdge).vertices[i]
            (D.edgeArc firstEdge).vertices[i + 1] := by
        have hmem' := hxOpenFirst
        rw [← heq] at hmem'
        exact hmem'
      exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hmem)
    · simpa [hFirstBranchIndices.1] using FirstBranch.beforeGate_open
    · exact FirstBranch.beforeGate_on_sphere
  have hFirstRightOutside :
      (D.edgeArc firstEdge).vertices[i + 1] ∉
        Metric.closedBall x Disk.radius := by
    apply endpoint_outside_closedBall
    · intro heq
      have hne : (D.edgeArc firstEdge).vertices[i] ≠
          (D.edgeArc firstEdge).vertices[i + 1] := by
        intro hv
        have hidx := ((D.edgeArc firstEdge).simple_vertices.getElem_inj_iff
          (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 hv
        omega
      have hmem : (D.edgeArc firstEdge).vertices[i + 1] ∈
          openSegment ℝ (D.edgeArc firstEdge).vertices[i]
            (D.edgeArc firstEdge).vertices[i + 1] := by
        have hmem' := hxOpenFirst
        rw [← heq] at hmem'
        exact hmem'
      exact hne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hmem)
    · simpa [openSegment_symm, hFirstBranchIndices.2] using
        FirstBranch.afterGate_open
    · exact FirstBranch.afterGate_on_sphere
  have Aarc_vertex_mem_carrier (idx : Fin Aarc.vertices.length) :
      Aarc.vertices[idx.1] ∈ Aarc.carrier := by
    rw [Aarc.carrier_eq]
    by_cases hlast : idx.1 + 1 = Aarc.vertices.length
    · refine ⟨idx.1 - 1, by omega, ?_⟩
      have hidx : idx.1 - 1 + 1 = idx.1 := by omega
      simpa [hidx] using
        (right_mem_segment ℝ Aarc.vertices[idx.1 - 1] Aarc.vertices[idx.1])
    · refine ⟨idx.1, by omega, left_mem_segment ℝ _ _⟩
  have hNonterminalVertexOutsideDisk (idx : Fin Aarc.vertices.length)
      (hne : idx ≠ targetIndex) :
      Aarc.vertices[idx.1] ∉ Metric.closedBall x Disk.radius := by
    intro hzBall
    have hzAarc := Aarc_vertex_mem_carrier idx
    have hzFirst : Aarc.vertices[idx.1] ∈ (D.edgeArc firstEdge).carrier := by
      have hzFirstArc := FirstCut.prefix_carrier_subset hzAarc
      simpa [hfirstCarrier] using hzFirstArc
    have hzSeg : Aarc.vertices[idx.1] ∈
        segment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] := by
      have hzBoth : Aarc.vertices[idx.1] ∈ Metric.closedBall x Disk.radius ∩
          (D.edgeArc firstEdge).carrier := ⟨hzBall, hzFirst⟩
      rw [first_disk_local] at hzBoth
      exact hzBoth.2
    have hzOpen : Aarc.vertices[idx.1] ∈
        openSegment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] := by
      rw [segment_eq_image_lineMap] at hzSeg
      rcases hzSeg with ⟨t, ht, hformula⟩
      rw [openSegment_eq_image_lineMap]
      refine ⟨t, ⟨?_, ?_⟩, hformula⟩
      · by_contra hnot
        have ht0 : t = 0 := le_antisymm (le_of_not_gt hnot) ht.1
        have hzLeft : Aarc.vertices[idx.1] =
            (D.edgeArc firstEdge).vertices[i] := by
          simpa [ht0] using hformula.symm
        exact hFirstLeftOutside (hzLeft ▸ hzBall)
      · by_contra hnot
        have ht1 : t = 1 := le_antisymm ht.2 (le_of_not_gt hnot)
        have hzRight : Aarc.vertices[idx.1] =
            (D.edgeArc firstEdge).vertices[i + 1] := by
          simpa [ht1] using hformula.symm
        exact hFirstRightOutside (hzRight ▸ hzBall)
    have hzNeX : Aarc.vertices[idx.1] ≠ x := by
      intro hzX
      apply hne
      apply Fin.ext
      have hvertexEq : Aarc.vertices[idx.1] = Aarc.vertices[targetIndex.1] := by
        simpa [targetIndex, htargetVertex] using hzX
      exact (Aarc.simple_vertices.getElem_inj_iff
        (hi := idx.2) (hj := targetIndex.2)).1 hvertexEq
    obtain ⟨m, hm, hzOpenAarc, _scale, _hscale, _hdir⟩ :=
      hFirstPrefixTransfer (Aarc.vertices[idx.1]) i hi hzOpen hzAarc hzNeX
    exact (open_not_vertices Aarc (Aarc.vertices[idx.1]) m hm hzOpenAarc)
      (List.getElem_mem idx.2)
  have hTerminalTubeOnly
      (q : EuclideanSpace ℝ (Fin 2))
      (hqBall : q ∈ Metric.closedBall x rhoTerm)
      (m : ℕ) (hm : m + 1 < Aarc.vertices.length)
      (hqTube : q ∈ sep.tube m hm) : m = jlast := by
    rw [sep.tube_eq] at hqTube
    rcases hqTube with ⟨t, ht, s, hs, hqFormula⟩
    let center := AffineMap.lineMap Aarc.vertices[m] Aarc.vertices[m + 1] t
    have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 := by
      exact ⟨(sep.lowerParam_pos m hm).trans_le ht.1.le,
        ht.2.trans (sep.upperParam_lt_one m hm)⟩
    have hcenterOpen : center ∈
        openSegment ℝ Aarc.vertices[m] Aarc.vertices[m + 1] := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨t, ht01, rfl⟩
    have hcenterAarc : center ∈ Aarc.carrier := by
      rw [Aarc.carrier_eq]
      exact ⟨m, hm, openSegment_subset_segment ℝ _ _ hcenterOpen⟩
    have hqCenter : dist q center < eta := by
      rw [hqFormula, dist_eq_norm]
      have hsub : center + s • sep.normal m hm - center =
          s • sep.normal m hm := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs]
      have hsabs : |s| < sep.halfWidth m hm := by
        exact abs_lt.mpr hs
      have hnormalPos : 0 < ‖sep.normal m hm‖ := by
        rw [sep.normal_norm_eq_segment_length m hm]
        exact dist_pos.mpr (by
          intro heq
          have hidx := (Aarc.simple_vertices.getElem_inj_iff
            (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 heq
          omega)
      exact (mul_lt_mul_of_pos_right hsabs hnormalPos).trans
        (sep.halfWidth_mul_normal_norm_lt_eta m hm)
    have hcenterDiskOpen : center ∈ Metric.ball x Disk.radius := by
      rw [Metric.mem_ball]
      have hqx : dist q x ≤ rhoTerm := by
        simpa [Metric.mem_closedBall] using hqBall
      calc
        dist center x ≤ dist center q + dist q x := dist_triangle _ _ _
        _ = dist q center + dist q x := by rw [dist_comm center q]
        _ < eta + rhoTerm := by linarith
        _ < Disk.radius := by linarith [heta_terminal_gap]
    have hcenterFirst : center ∈ (D.edgeArc firstEdge).carrier := by
      have := FirstCut.prefix_carrier_subset hcenterAarc
      simpa [hfirstCarrier] using this
    have hcenterDSeg : center ∈
        segment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] := by
      have hboth : center ∈ Metric.closedBall x Disk.radius ∩
          (D.edgeArc firstEdge).carrier :=
        ⟨Metric.ball_subset_closedBall hcenterDiskOpen, hcenterFirst⟩
      rw [first_disk_local] at hboth
      exact hboth.2
    have hcenterDOpen : center ∈
        openSegment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] := by
      rw [segment_eq_image_lineMap] at hcenterDSeg
      rcases hcenterDSeg with ⟨v, hv, hvFormula⟩
      rw [openSegment_eq_image_lineMap]
      refine ⟨v, ⟨?_, ?_⟩, hvFormula⟩
      · by_contra hnot
        have hv0 : v = 0 := le_antisymm (le_of_not_gt hnot) hv.1
        have hleft : center = (D.edgeArc firstEdge).vertices[i] := by
          simpa [hv0] using hvFormula.symm
        exact hFirstLeftOutside
          (hleft ▸ Metric.ball_subset_closedBall hcenterDiskOpen)
      · by_contra hnot
        have hv1 : v = 1 := le_antisymm hv.2 (le_of_not_gt hnot)
        have hright : center = (D.edgeArc firstEdge).vertices[i + 1] := by
          simpa [hv1] using hvFormula.symm
        exact hFirstRightOutside
          (hright ▸ Metric.ball_subset_closedBall hcenterDiskOpen)
    have hcenterNeX : center ≠ x := by
      intro heq
      exact (open_not_vertices Aarc center m hm hcenterOpen)
        (by rw [heq, ← htargetVertex]; exact List.getElem_mem hitarget)
    obtain ⟨owner, howner, hcenterOwner, scale, hscale, hdir⟩ :=
      hFirstPrefixTransfer center i hi hcenterDOpen hcenterAarc hcenterNeX
    have hownerEq : owner = m :=
      open_index_unique Aarc center owner m howner hm hcenterOwner hcenterOpen
    subst owner
    by_contra hmLast
    let leftIndex : Fin Aarc.vertices.length := ⟨m, by omega⟩
    let rightIndex : Fin Aarc.vertices.length := ⟨m + 1, hm⟩
    have hleftNeTarget : leftIndex ≠ targetIndex := by
      intro heq
      have : m = itarget := congrArg Fin.val heq
      omega
    have hrightNeTarget : rightIndex ≠ targetIndex := by
      intro heq
      have : m + 1 = itarget := congrArg Fin.val heq
      change m + 1 = Aarc.vertices.length - 1 at this
      change m ≠ Aarc.vertices.length - 2 at hmLast
      omega
    have hleftOutside := hNonterminalVertexOutsideDisk leftIndex hleftNeTarget
    have hrightOutside := hNonterminalVertexOutsideDisk rightIndex hrightNeTarget
    obtain ⟨scaleLast, hscaleLast, hdDir⟩ := hlastScale
    let ratio : ℝ := scale / scaleLast
    have hratio : ratio ≠ 0 := div_ne_zero hscale hscaleLast
    have hsegmentDir : Aarc.vertices[m + 1] - Aarc.vertices[m] = ratio • d := by
      rw [hdir, hdDir]
      dsimp [ratio]
      rw [smul_smul]
      congr 1
      field_simp [hscaleLast]
    obtain ⟨c, hcenterLine⟩ :=
      first_point_line center (Metric.ball_subset_closedBall hcenterDiskOpen)
        hcenterFirst
    let ca : ℝ := c - t * ratio
    let cb : ℝ := c + (1 - t) * ratio
    have hleftLine : Aarc.vertices[m] = x + ca • d := by
      have hlineMap : center = Aarc.vertices[m] +
          t • (Aarc.vertices[m + 1] - Aarc.vertices[m]) := by
        dsimp [center]
        simp only [AffineMap.lineMap_apply_module]
        module
      rw [hcenterLine, hsegmentDir] at hlineMap
      dsimp [ca]
      rw [smul_smul] at hlineMap
      calc
        Aarc.vertices[m] =
            (Aarc.vertices[m] + (t * ratio) • d) - (t * ratio) • d := by module
        _ = (x + c • d) - (t * ratio) • d := by rw [← hlineMap]
        _ = x + (c - t * ratio) • d := by module
    have hrightLine : Aarc.vertices[m + 1] = x + cb • d := by
      rw [← sub_add_cancel Aarc.vertices[m + 1] Aarc.vertices[m],
        hsegmentDir, hleftLine]
      dsimp [ca, cb]
      module
    have hcenterDist : |c| * ‖d‖ < Disk.radius := by
      have := hcenterDiskOpen
      rw [Metric.mem_ball, hcenterLine, dist_eq_norm] at this
      simpa [norm_smul, Real.norm_eq_abs] using this
    have hleftDist : Disk.radius < |ca| * ‖d‖ := by
      have hnot := hleftOutside
      rw [Metric.mem_closedBall, hleftLine, dist_eq_norm] at hnot
      simpa [norm_smul, Real.norm_eq_abs] using lt_of_not_ge hnot
    have hrightDist : Disk.radius < |cb| * ‖d‖ := by
      have hnot := hrightOutside
      rw [Metric.mem_closedBall, hrightLine, dist_eq_norm] at hnot
      simpa [norm_smul, Real.norm_eq_abs] using lt_of_not_ge hnot
    have hcConvex : c = (1 - t) * ca + t * cb := by
      dsimp [ca, cb]
      ring
    have htPos : 0 < t := (sep.lowerParam_pos m hm).trans ht.1
    have htOne : t < 1 := ht.2.trans (sep.upperParam_lt_one m hm)
    have hopposite : (ca < 0 ∧ 0 < cb) ∨ (cb < 0 ∧ 0 < ca) := by
      by_cases hca : 0 ≤ ca
      · by_cases hcb : 0 ≤ cb
        · rw [abs_of_nonneg hca] at hleftDist
          rw [abs_of_nonneg hcb] at hrightDist
          have htNonneg : 0 ≤ t := le_of_lt htPos
          have honeSubNonneg : 0 ≤ 1 - t := by linarith
          have hcNonneg : 0 ≤ c := by
            rw [hcConvex]
            exact add_nonneg (mul_nonneg honeSubNonneg hca)
              (mul_nonneg htNonneg hcb)
          rw [abs_of_nonneg hcNonneg] at hcenterDist
          have hleftWeighted := mul_le_mul_of_nonneg_left
            (le_of_lt hleftDist) honeSubNonneg
          have hrightWeighted := mul_le_mul_of_nonneg_left
            (le_of_lt hrightDist) htNonneg
          have hcLower : Disk.radius ≤ c * ‖d‖ := by
            rw [hcConvex]
            calc
              Disk.radius = (1 - t) * Disk.radius + t * Disk.radius := by ring
              _ ≤ (1 - t) * (ca * ‖d‖) + t * (cb * ‖d‖) :=
                add_le_add hleftWeighted hrightWeighted
              _ = ((1 - t) * ca + t * cb) * ‖d‖ := by ring
          exact (not_lt_of_ge hcLower hcenterDist).elim
        · exact Or.inr ⟨lt_of_not_ge hcb, by
              rw [abs_of_nonneg hca] at hleftDist
              have hprod : 0 < ca * ‖d‖ := lt_trans hDiskRadius hleftDist
              rcases (mul_pos_iff.mp hprod) with h | h
              · exact h.1
              · exact (not_lt_of_ge hca h.1).elim⟩
      · by_cases hcb : 0 ≤ cb
        · exact Or.inl ⟨lt_of_not_ge hca, by
              rw [abs_of_nonneg hcb] at hrightDist
              have hprod : 0 < cb * ‖d‖ := lt_trans hDiskRadius hrightDist
              rcases (mul_pos_iff.mp hprod) with h | h
              · exact h.1
              · exact (not_lt_of_ge hcb h.1).elim⟩
        · rw [abs_of_neg (lt_of_not_ge hca)] at hleftDist
          rw [abs_of_neg (lt_of_not_ge hcb)] at hrightDist
          have htNonneg : 0 ≤ t := le_of_lt htPos
          have honeSubNonneg : 0 ≤ 1 - t := by linarith
          have hcNonpos : c ≤ 0 := by
            rw [hcConvex]
            exact add_nonpos
              (mul_nonpos_of_nonneg_of_nonpos honeSubNonneg (le_of_lt (lt_of_not_ge hca)))
              (mul_nonpos_of_nonneg_of_nonpos htNonneg (le_of_lt (lt_of_not_ge hcb)))
          rw [abs_of_nonpos hcNonpos] at hcenterDist
          have hleftWeighted := mul_le_mul_of_nonneg_left
            (le_of_lt hleftDist) honeSubNonneg
          have hrightWeighted := mul_le_mul_of_nonneg_left
            (le_of_lt hrightDist) htNonneg
          have hcLower : Disk.radius ≤ -c * ‖d‖ := by
            rw [hcConvex]
            calc
              Disk.radius = (1 - t) * Disk.radius + t * Disk.radius := by ring
              _ ≤ (1 - t) * (-ca * ‖d‖) + t * (-cb * ‖d‖) :=
                add_le_add hleftWeighted hrightWeighted
              _ = -((1 - t) * ca + t * cb) * ‖d‖ := by ring
          exact (not_lt_of_ge hcLower hcenterDist).elim
    have hxOpenM : x ∈ openSegment ℝ Aarc.vertices[m] Aarc.vertices[m + 1] := by
      rw [openSegment_eq_image_lineMap]
      rcases hopposite with hop | hop
      · let v := -ca / (cb - ca)
        have hdenPos : 0 < cb - ca := sub_pos.mpr (lt_trans hop.1 hop.2)
        have hv : v ∈ Set.Ioo (0 : ℝ) 1 := by
          dsimp [v]
          exact ⟨div_pos (neg_pos.mpr hop.1) hdenPos,
            (div_lt_one hdenPos).2 (by linarith [hop.2])⟩
        refine ⟨v, hv, ?_⟩
        rw [hleftLine, hrightLine]
        dsimp [v]
        simp only [AffineMap.lineMap_apply_module]
        have hden : cb - ca ≠ 0 := hdenPos.ne'
        have hcoef :
            (1 - (-ca / (cb - ca))) * ca + (-ca / (cb - ca)) * cb = 0 := by
          field_simp [hden]
          ring
        calc
          (1 - (-ca / (cb - ca))) • (x + ca • d) +
                (-ca / (cb - ca)) • (x + cb • d) =
              x + (((1 - (-ca / (cb - ca))) * ca +
                (-ca / (cb - ca)) * cb) • d) := by module
          _ = x := by rw [hcoef, zero_smul, add_zero]
      · let v := ca / (ca - cb)
        have hdenPos : 0 < ca - cb := sub_pos.mpr (lt_trans hop.1 hop.2)
        have hv : v ∈ Set.Ioo (0 : ℝ) 1 := by
          dsimp [v]
          exact ⟨div_pos hop.2 hdenPos,
            (div_lt_one hdenPos).2 (by linarith [hop.1])⟩
        refine ⟨v, hv, ?_⟩
        rw [hleftLine, hrightLine]
        dsimp [v]
        simp only [AffineMap.lineMap_apply_module]
        have hden : ca - cb ≠ 0 := hdenPos.ne'
        have hcoef :
            (1 - (ca / (ca - cb))) * ca + (ca / (ca - cb)) * cb = 0 := by
          field_simp [hden]
          ring
        calc
          (1 - (ca / (ca - cb))) • (x + ca • d) +
                (ca / (ca - cb)) • (x + cb • d) =
              x + (((1 - (ca / (ca - cb))) * ca +
                (ca / (ca - cb)) * cb) • d) := by module
          _ = x := by rw [hcoef, zero_smul, add_zero]
    exact (open_not_vertices Aarc x m hm hxOpenM)
      (by rw [← htargetVertex]; exact List.getElem_mem hitarget)
  have hSelectedTerminalCone
      (q : EuclideanSpace ℝ (Fin 2))
      (hq : q ∈ SelectedSide ∩ Metric.closedBall x rhoTerm) :
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ b < actualK1 * a ∧
        q = x + a • d + b • n := by
    have vertex_index_target
        (idx : Fin Aarc.vertices.length)
        (hqPiece : q ∈ localSideData.vertexCollar idx) : idx = targetIndex := by
      by_contra hne
      have hqDisk := localSideData.vertexCollar_subset_vertexDisk idx hqPiece
      rw [vertexLocalPieces.vertexDisk_eq] at hqDisk
      have hqdist : dist q Aarc.vertices[idx.1] < eta := by
        have hrlt := controlRadii.radius_lt_eta idx
        simpa [Metric.mem_ball] using lt_trans
          (show dist q Aarc.vertices[idx.1] < controlRadii.radius idx by
            simpa [Metric.mem_ball] using hqDisk) hrlt
      have hvertexBall : Aarc.vertices[idx.1] ∈
          Metric.closedBall x Disk.radius := by
        rw [Metric.mem_closedBall]
        apply le_of_lt
        calc
          dist Aarc.vertices[idx.1] x ≤
              dist Aarc.vertices[idx.1] q + dist q x := dist_triangle _ _ _
          _ < eta + rhoTerm := add_lt_add_of_lt_of_le
            (by simpa [dist_comm] using hqdist) hq.2
          _ < Disk.radius := by linarith [heta_terminal_gap]
      exact hNonterminalVertexOutsideDisk idx hne hvertexBall
    have planarRot90_neg (v : EuclideanSpace ℝ (Fin 2)) :
        PlanarRot90 (-v) = -PlanarRot90 v := by
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;> simp [PlanarRot90]
    have hlastVertex : Aarc.vertices[jlast + 1] = x := by
      have hindex : Aarc.vertices[jlast + 1] = Aarc.vertices[itarget] := by
        congr
      exact hindex.trans htargetVertex
    have target_piece_coordinates
        (hqVin : q ∈ Vin) :
        ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ b < actualK1 * a ∧
          q = x + a • d + b • n := by
      rw [hVinEq] at hqVin
      rcases hqVin with ⟨z, hz, rfl⟩
      exact ⟨z 0, z 1, hz.1, hz.2.2.1, hz.2.2.2, rfl⟩
    by_cases hpos : positiveSide
    · have hqRight : q ∈ S.rightStrip := by
        simpa only [SelectedSide, if_pos hpos] using hq.1
      rw [hRightEq] at hqRight
      rcases hqRight with hqHalf | hqPiece
      · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
        rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
        have hmLast := hTerminalTubeOnly q hq.2 m hm
          (sep.rightHalf_subset_tube m hm hqHalf)
        subst m
        rw [sep.rightHalf_eq] at hqHalf
        rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
        let a := 1 - t
        let b := -s
        have ha : 0 < a := by
          dsimp [a]
          linarith [ht.2, sep.upperParam_lt_one jlast hjlast]
        have hb : 0 < b := by
          dsimp [b]
          exact neg_pos.mpr hs.2
        have hbBound : b < actualK1 * a := by
          have hw := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
            jlast hjlast
          have hone : 1 - sep.upperParam jlast hjlast < 1 - t := by linarith [ht.2]
          dsimp [a, b]
          calc
            -s < sep.halfWidth jlast hjlast := by linarith [hs.1]
            _ < actualK1 * (1 - sep.upperParam jlast hjlast) := hw
            _ < actualK1 * (1 - t) := mul_lt_mul_of_pos_left hone hActualK1Pos
        refine ⟨a, b, ha, hb, hbBound, ?_⟩
        have hnormal : sep.normal jlast hjlast =
            PlanarRot90 (Aarc.vertices[jlast + 1] - Aarc.vertices[jlast]) := by
          simpa only [PlanarRot90] using
            compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn
              jlast hjlast
        have hdiff : Aarc.vertices[jlast + 1] - Aarc.vertices[jlast] = -d := by
          rw [hlastVertex]
          dsimp [d]
          module
        rw [hnormal, hdiff, planarRot90_neg] at hqFormula
        simp only [AffineMap.lineMap_apply_module, hlastVertex] at hqFormula
        rw [hqFormula]
        dsimp [a, b, d, n]
        rw [if_pos hpos]
        module
      · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
        have hidx := vertex_index_target idx
          (localSideData.rightSidePiece_subset_vertexCollar idx hqPiece)
        subst idx
        apply target_piece_coordinates
        simpa [Vin, hpos] using hqPiece
    · have hqLeft : q ∈ S.leftStrip := by
        simpa only [SelectedSide, if_neg hpos] using hq.1
      rw [hLeftEq] at hqLeft
      rcases hqLeft with hqHalf | hqPiece
      · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
        rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
        have hmLast := hTerminalTubeOnly q hq.2 m hm
          (sep.leftHalf_subset_tube m hm hqHalf)
        subst m
        rw [sep.leftHalf_eq] at hqHalf
        rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
        let a := 1 - t
        let b := s
        have ha : 0 < a := by
          dsimp [a]
          linarith [ht.2, sep.upperParam_lt_one jlast hjlast]
        have hb : 0 < b := by exact hs.1
        have hbBound : b < actualK1 * a := by
          have hw := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
            jlast hjlast
          have hone : 1 - sep.upperParam jlast hjlast < 1 - t := by linarith [ht.2]
          dsimp [a, b]
          calc
            s < sep.halfWidth jlast hjlast := hs.2
            _ < actualK1 * (1 - sep.upperParam jlast hjlast) := hw
            _ < actualK1 * (1 - t) := mul_lt_mul_of_pos_left hone hActualK1Pos
        refine ⟨a, b, ha, hb, hbBound, ?_⟩
        have hnormal : sep.normal jlast hjlast =
            PlanarRot90 (Aarc.vertices[jlast + 1] - Aarc.vertices[jlast]) := by
          simpa only [PlanarRot90] using
            compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn
              jlast hjlast
        have hdiff : Aarc.vertices[jlast + 1] - Aarc.vertices[jlast] = -d := by
          rw [hlastVertex]
          dsimp [d]
          module
        rw [hnormal, hdiff, planarRot90_neg] at hqFormula
        simp only [AffineMap.lineMap_apply_module, hlastVertex] at hqFormula
        rw [hqFormula]
        dsimp [a, b, d, n]
        rw [if_neg hpos]
        module
      · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
        have hidx := vertex_index_target idx
          (localSideData.leftSidePiece_subset_vertexCollar idx hqPiece)
        subst idx
        apply target_piece_coordinates
        simpa [Vin, hpos] using hqPiece
  have hSelectedPositive : ∀ q ∈
      SelectedSide ∩ Metric.closedBall x rhoTerm,
      0 < actualK1 * inner ℝ (q - x) d - inner ℝ (q - x) n := by
    intro q hq
    obtain ⟨a, b, ha, hb, hbka, hqFormula⟩ := hSelectedTerminalCone q hq
    have hsub : x + a • d + b • n - x = a • d + b • n := by abel
    have hnormsq : 0 < ‖d‖ ^ 2 := sq_pos_of_pos hnormd
    have hphi :
        actualK1 * inner ℝ (q - x) d - inner ℝ (q - x) n =
          (actualK1 * a - b) * ‖d‖ ^ 2 := by
      rw [hqFormula, hsub]
      simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
        hdd, hnd, hdn, hnn, mul_zero, zero_add, add_zero]
      ring
    rw [hphi]
    exact mul_pos (sub_pos.mpr hbka) hnormsq
  have hSelectedAvoidTerminalClosures :
      SelectedSide ∩ (closure Side ∪ closure Bridge ∪ closure Q) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqBall : q ∈ Metric.closedBall x rhoTerm := by
      rcases hq.2 with (hqSide | hqBridge) | hqQ
      · exact Metric.ball_subset_closedBall (hSideBall hqSide)
      · exact Metric.ball_subset_closedBall (hBridgeBall hqBridge)
      · exact hQBall hqQ
    have hposPhi := hSelectedPositive q ⟨hq.1, hqBall⟩
    have hnonposPhi := hSupporting q hq.2
    linarith
  have hSelectedTerminalAvoidOld :
      (SelectedSide ∩ Metric.closedBall x rhoTerm) ∩ Old = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨a, b, ha, hb, hbka, hqCone⟩ :=
      hSelectedTerminalCone q hq.1
    have hqLocal := hOldLocal ⟨hq.1.2, hq.2⟩
    rcases hqLocal with ⟨c, hqLine⟩ | ⟨c, hqLine⟩
    · have hcoeff : b * ‖d‖ ^ 2 = 0 := by
        have heq : a • d + b • n = c • d := by
          calc
            a • d + b • n = (x + a • d + b • n) - x := by module
            _ = q - x := by rw [← hqCone]
            _ = (x + c • d) - x := by rw [hqLine]
            _ = c • d := by module
        calc
          b * ‖d‖ ^ 2 = inner ℝ (a • d + b • n) n := by
            simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
              hdn, hnn, mul_zero, zero_add]
          _ = inner ℝ (c • d) n := congrArg (fun z => inner ℝ z n) heq
          _ = 0 := by
            simp only [inner_smul_left_eq_smul, smul_eq_mul, hdn, mul_zero]
      nlinarith [sq_pos_of_pos hnormd]
    · have hcoeffD : a * ‖d‖ ^ 2 = c * mu * ‖d‖ ^ 2 := by
        have heq : a • d + b • n = c • (y - x) := by
          calc
            a • d + b • n = (x + a • d + b • n) - x := by module
            _ = q - x := by rw [← hqCone]
            _ = (x + c • (y - x)) - x := by rw [hqLine]
            _ = c • (y - x) := by module
        calc
          a * ‖d‖ ^ 2 = inner ℝ (a • d + b • n) d := by
            simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
              hdd, hnd, mul_zero, add_zero]
          _ = inner ℝ (c • (y - x)) d := congrArg (fun z => inner ℝ z d) heq
          _ = c * mu * ‖d‖ ^ 2 := by
            rw [hyDecomp]
            simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
              hdd, hnd, mul_zero, add_zero]
            ring
      have hcoeffN : b * ‖d‖ ^ 2 = c * nu * ‖d‖ ^ 2 := by
        have heq : a • d + b • n = c • (y - x) := by
          calc
            a • d + b • n = (x + a • d + b • n) - x := by module
            _ = q - x := by rw [← hqCone]
            _ = (x + c • (y - x)) - x := by rw [hqLine]
            _ = c • (y - x) := by module
        calc
          b * ‖d‖ ^ 2 = inner ℝ (a • d + b • n) n := by
            simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
              hdn, hnn, mul_zero, zero_add]
          _ = inner ℝ (c • (y - x)) n := congrArg (fun z => inner ℝ z n) heq
          _ = c * nu * ‖d‖ ^ 2 := by
            rw [hyDecomp]
            simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
              hdn, hnn, mul_zero, zero_add]
            ring
      have hnormsq := sq_pos_of_pos hnormd
      have haEq : a = c * mu := by nlinarith
      have hbEq : b = c * nu := by nlinarith
      have hc : 0 < c := by
        rw [hbEq] at hb
        rcases (mul_pos_iff.mp hb) with hcnu | hcnu
        · exact hcnu.1
        · exact (not_lt_of_ge (le_of_lt hnu) hcnu.2).elim
      have hkmu : actualK1 * mu < nu := by
        have habs := le_abs_self mu
        have hkpos := hActualK1Pos
        nlinarith [hkappaSmall]
      rw [haEq, hbEq] at hbka
      nlinarith
  have hsourceLocalLe : sourceLocalRadius ≤ sourceRadius := by
    exact min_le_left _ _
  obtain ⟨wideSourceLeft, wideSourceRight,
      hWideSourceLeftEq, hWideSourceRightEq,
      hWideSourceLeftOpen, hWideSourceRightOpen,
      hWideSourceLeftConvex, hWideSourceRightConvex,
      hWideSourceLeftBall, hWideSourceRightBall,
      hWideSourceLeftClosure, hWideSourceRightClosure,
      hWideSourceNotLeft, hWideSourceNotRight,
      hWideSourceLeftAvoid, hWideSourceRightAvoid⟩ :=
    hsourceSectors sourceLocalRadius actualK0 hsourceLocalRadius
      hsourceLocalLe hActualK0Pos hActualK0LeSource
  let WideSourceSector : Set (EuclideanSpace ℝ (Fin 2)) :=
    if positiveSide then wideSourceRight else wideSourceLeft
  have hNonSourceVertexOutsideR0 (idx : Fin Aarc.vertices.length)
      (hne : idx.1 ≠ 0) :
      Aarc.vertices[idx.1] ∉
        Metric.closedBall (D.vertexPlacement u) r0 := by
    intro hzBall
    have hzAarc := Aarc_vertex_mem_carrier idx
    have hzInitial : Aarc.vertices[idx.1] ∈
        segment ℝ Aarc.vertices[0] Aarc.vertices[1] := by
      have hz := hIso.source_closedBall_carrier_subset_initial_segment
        ⟨by simpa [hAarcSource] using hzBall, hzAarc⟩
      simpa [hsource0] using hz
    have hzNeSource : Aarc.vertices[idx.1] ≠ Aarc.vertices[0] := by
      intro heq
      have hidx := (Aarc.simple_vertices.getElem_inj_iff
        (i := idx.1) (j := 0) (hi := idx.2) (hj := by omega)).1 heq
      exact hne hidx
    have hzNeNext : Aarc.vertices[idx.1] ≠ Aarc.vertices[1] := by
      intro heq
      have hdistNext : dist Aarc.source Aarc.vertices[1] ≤ r0 := by
        have := hzBall
        rw [Metric.mem_closedBall] at this
        simpa [heq, hAarcSource, hsource0, dist_comm] using this
      exact (not_lt_of_ge hdistNext) hIso.source_lt_initial_length
    have hzOpen : Aarc.vertices[idx.1] ∈
        openSegment ℝ Aarc.vertices[0] Aarc.vertices[1] := by
      rw [segment_eq_image_lineMap] at hzInitial
      rcases hzInitial with ⟨t, ht, htFormula⟩
      rw [openSegment_eq_image_lineMap]
      refine ⟨t, ⟨?_, ?_⟩, htFormula⟩
      · by_contra hnot
        have ht0 : t = 0 := le_antisymm (le_of_not_gt hnot) ht.1
        exact hzNeSource (by simpa [ht0] using htFormula.symm)
      · by_contra hnot
        have ht1 : t = 1 := le_antisymm ht.2 (le_of_not_gt hnot)
        exact hzNeNext (by simpa [ht1] using htFormula.symm)
    exact (open_not_vertices Aarc (Aarc.vertices[idx.1]) 0 hfirstAarc hzOpen)
      (List.getElem_mem idx.2)
  have hSourceTubeOnly
      (q : EuclideanSpace ℝ (Fin 2))
      (hqBall : q ∈ Metric.ball (D.vertexPlacement u) sourceLocalRadius)
      (m : ℕ) (hm : m + 1 < Aarc.vertices.length)
      (hqTube : q ∈ sep.tube m hm) : m = 0 := by
    rw [sep.tube_eq] at hqTube
    rcases hqTube with ⟨t, ht, s, hs, hqFormula⟩
    let center := AffineMap.lineMap Aarc.vertices[m] Aarc.vertices[m + 1] t
    have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨(sep.lowerParam_pos m hm).trans_le ht.1.le,
        ht.2.trans (sep.upperParam_lt_one m hm)⟩
    have hcenterOpen : center ∈
        openSegment ℝ Aarc.vertices[m] Aarc.vertices[m + 1] := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨t, ht01, rfl⟩
    have hcenterAarc : center ∈ Aarc.carrier := by
      rw [Aarc.carrier_eq]
      exact ⟨m, hm, openSegment_subset_segment ℝ _ _ hcenterOpen⟩
    have hqCenter : dist q center < eta := by
      rw [hqFormula, dist_eq_norm]
      have hsub : center + s • sep.normal m hm - center =
          s • sep.normal m hm := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs]
      have hsabs : |s| < sep.halfWidth m hm := abs_lt.mpr hs
      have hnormalPos : 0 < ‖sep.normal m hm‖ := by
        rw [sep.normal_norm_eq_segment_length m hm]
        exact dist_pos.mpr (by
          intro heq
          have hidx := (Aarc.simple_vertices.getElem_inj_iff
            (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 heq
          omega)
      exact (mul_lt_mul_of_pos_right hsabs hnormalPos).trans
        (sep.halfWidth_mul_normal_norm_lt_eta m hm)
    have hcenterR0 : center ∈ Metric.ball (D.vertexPlacement u) r0 := by
      rw [Metric.mem_ball]
      have hqSource : dist q (D.vertexPlacement u) < sourceLocalRadius := by
        simpa [Metric.mem_ball] using hqBall
      have hsourceHalf : sourceLocalRadius ≤ r0 / 2 := min_le_right _ _
      calc
        dist center (D.vertexPlacement u) ≤
            dist center q + dist q (D.vertexPlacement u) := dist_triangle _ _ _
        _ = dist q center + dist q (D.vertexPlacement u) := by rw [dist_comm center q]
        _ < eta + sourceLocalRadius := by linarith
        _ < r0 := by linarith [heta_source_gap]
    have hcenterInitial : center ∈
        segment ℝ Aarc.vertices[0] Aarc.vertices[1] := by
      simpa [hsource0] using
        hIso.source_closedBall_carrier_subset_initial_segment
          ⟨Metric.ball_subset_closedBall (by simpa [hAarcSource] using hcenterR0),
            hcenterAarc⟩
    have hcenterInitialOpen : center ∈
        openSegment ℝ Aarc.vertices[0] Aarc.vertices[1] := by
      rw [segment_eq_image_lineMap] at hcenterInitial
      rcases hcenterInitial with ⟨v, hv, hvFormula⟩
      rw [openSegment_eq_image_lineMap]
      refine ⟨v, ⟨?_, ?_⟩, hvFormula⟩
      · by_contra hnot
        have hv0 : v = 0 := le_antisymm (le_of_not_gt hnot) hv.1
        have hc0 : center = Aarc.vertices[0] := by
          simpa [hv0] using hvFormula.symm
        exact (open_not_vertices Aarc center m hm hcenterOpen)
          (by rw [hc0]; exact List.getElem_mem (by omega))
      · by_contra hnot
        have hv1 : v = 1 := le_antisymm hv.2 (le_of_not_gt hnot)
        have hc1 : center = Aarc.vertices[1] := by
          simpa [hv1] using hvFormula.symm
        exact (open_not_vertices Aarc center m hm hcenterOpen)
          (by rw [hc1]; exact List.getElem_mem (by omega))
    exact open_index_unique Aarc center m 0 hm hfirstAarc hcenterOpen
      hcenterInitialOpen
  have source_coords_inside_cap
      (q : EuclideanSpace ℝ (Fin 2)) (a b : ℝ)
      (hqFormula : q = D.vertexPlacement u + a • d0 + b • PlanarRot90 d0)
      (hqBall : q ∈ Metric.ball (D.vertexPlacement u) sourceLocalRadius) :
      a ^ 2 + b ^ 2 <
        (sourceLocalRadius /
          ‖d0‖) ^ 2 := by
    have hqdist : dist (D.vertexPlacement u) q < sourceLocalRadius := by
      simpa [Metric.mem_ball, dist_comm] using hqBall
    have hvec : q - D.vertexPlacement u =
        a • d0 + b • PlanarRot90 d0 := by rw [hqFormula]; abel
    have hsquare : dist (D.vertexPlacement u) q ^ 2 =
        (a ^ 2 + b ^ 2) * ‖d0‖ ^ 2 := by
      rw [dist_eq_norm, norm_sub_rev, hvec]
      have horth : inner ℝ (a • d0) (b • PlanarRot90 d0) = 0 := by
        rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
        ring
      have hpyth :
          ‖a • d0 + b • PlanarRot90 d0‖ ^ 2 =
            ‖a • d0‖ ^ 2 + ‖b • PlanarRot90 d0‖ ^ 2 := by
        simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      rw [hpyth, norm_smul, norm_smul, PlanarRot90Norm]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have hnormd0 : 0 < ‖d0‖ := norm_pos_iff.mpr hd0
    have hrad := hsourceLocalRadius
    have hdistNonneg : 0 ≤ dist (D.vertexPlacement u) q := dist_nonneg
    have hsquareLt : dist (D.vertexPlacement u) q ^ 2 < sourceLocalRadius ^ 2 := by
      nlinarith
    rw [hsquare] at hsquareLt
    have hnorm0 : ‖d0‖ ≠ 0 := hnormd0.ne'
    field_simp [hnorm0]
    nlinarith
  have hSelectedSourceWide :
      SelectedSide ∩ Metric.ball (D.vertexPlacement u) sourceLocalRadius ⊆
        WideSourceSector := by
    intro q hq
    have vertex_index_source
        (idx : Fin Aarc.vertices.length)
        (hqPiece : q ∈ localSideData.vertexCollar idx) : idx.1 = 0 := by
      by_contra hne
      have hqDisk := localSideData.vertexCollar_subset_vertexDisk idx hqPiece
      rw [vertexLocalPieces.vertexDisk_eq] at hqDisk
      have hqdist : dist q Aarc.vertices[idx.1] < eta := by
        have hr := controlRadii.radius_lt_eta idx
        have hqd : dist q Aarc.vertices[idx.1] < controlRadii.radius idx := by
          simpa [Metric.mem_ball] using hqDisk
        linarith
      have hsourceHalf : sourceLocalRadius ≤ r0 / 2 := min_le_right _ _
      have hvertexBall : Aarc.vertices[idx.1] ∈
          Metric.closedBall (D.vertexPlacement u) r0 := by
        rw [Metric.mem_closedBall]
        have hsq : dist q (D.vertexPlacement u) < sourceLocalRadius := by
          simpa [Metric.mem_ball] using hq.2
        apply le_of_lt
        calc
          dist Aarc.vertices[idx.1] (D.vertexPlacement u) ≤
              dist Aarc.vertices[idx.1] q + dist q (D.vertexPlacement u) :=
                dist_triangle _ _ _
          _ = dist q Aarc.vertices[idx.1] + dist q (D.vertexPlacement u) := by
            rw [dist_comm Aarc.vertices[idx.1] q]
          _ < eta + sourceLocalRadius := by linarith
          _ < r0 := by linarith [heta_source_gap]
      exact hNonSourceVertexOutsideR0 idx hne hvertexBall
    by_cases hpos : positiveSide
    · have hqRight : q ∈ S.rightStrip := by
        simpa only [SelectedSide, if_pos hpos] using hq.1
      rw [hRightEq] at hqRight
      rw [show WideSourceSector = wideSourceRight by simp [WideSourceSector, hpos],
        hWideSourceRightEq]
      rcases hqRight with hqHalf | hqPiece
      · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
        rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
        have hm0 := hSourceTubeOnly q hq.2 m hm
          (sep.rightHalf_subset_tube m hm hqHalf)
        subst m
        rw [sep.rightHalf_eq] at hqHalf
        rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
        let z : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![t, s]
        have hqChart : q = D.vertexPlacement u + t • d0 + s • PlanarRot90 d0 := by
          rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn] at hqFormula
          calc
            q = AffineMap.lineMap Aarc.vertices[0] Aarc.vertices[1] t +
                s • PlanarRot90 (Aarc.vertices[1] - Aarc.vertices[0]) := hqFormula
            _ = D.vertexPlacement u + t • d0 + s • PlanarRot90 d0 := by
              simp only [AffineMap.lineMap_apply_module]
              dsimp [d0]
              rw [hsource0, hAarcSource]
              module
        refine ⟨z, ?_, ?_⟩
        · dsimp [z]
          refine ⟨(sep.lowerParam_pos 0 hfirstAarc).trans ht.1, ?_, ?_, hs.2⟩
          · exact source_coords_inside_cap q t s hqChart hq.2
          · have hw := compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam
              0 hfirstAarc
            have htLower : sep.lowerParam 0 hfirstAarc < t := ht.1
            have hkpos := hActualK0Pos
            calc
              -actualK0 * t < -actualK0 * sep.lowerParam 0 hfirstAarc := by
                nlinarith
              _ < -sep.halfWidth 0 hfirstAarc := by linarith
              _ < s := hs.1
        · simpa [z] using hqChart.symm
      · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
        have hidx0 := vertex_index_source idx
          (localSideData.rightSidePiece_subset_vertexCollar idx hqPiece)
        have hidx : idx = (⟨0, by omega⟩ : Fin Aarc.vertices.length) := Fin.ext hidx0
        rw [hidx] at hqPiece
        rw [← hSourceRightPiece, hSourceRightSectorEq] at hqPiece
        rcases hqPiece with ⟨z, hz, hqFormula⟩
        have hqChart : q =
            D.vertexPlacement u + z 0 • d0 + z 1 • PlanarRot90 d0 := by
          simpa [hsource0, hAarcSource, d0] using hqFormula.symm
        refine ⟨z, ⟨hz.1, source_coords_inside_cap q (z 0) (z 1)
          hqChart hq.2, hz.2.2.1, hz.2.2.2⟩, hqChart.symm⟩
    · have hqLeft : q ∈ S.leftStrip := by
        simpa only [SelectedSide, if_neg hpos] using hq.1
      rw [hLeftEq] at hqLeft
      rw [show WideSourceSector = wideSourceLeft by simp [WideSourceSector, hpos],
        hWideSourceLeftEq]
      rcases hqLeft with hqHalf | hqPiece
      · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
        rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
        have hm0 := hSourceTubeOnly q hq.2 m hm
          (sep.leftHalf_subset_tube m hm hqHalf)
        subst m
        rw [sep.leftHalf_eq] at hqHalf
        rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
        let z : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![t, s]
        have hqChart : q = D.vertexPlacement u + t • d0 + s • PlanarRot90 d0 := by
          rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn] at hqFormula
          calc
            q = AffineMap.lineMap Aarc.vertices[0] Aarc.vertices[1] t +
                s • PlanarRot90 (Aarc.vertices[1] - Aarc.vertices[0]) := hqFormula
            _ = D.vertexPlacement u + t • d0 + s • PlanarRot90 d0 := by
              simp only [AffineMap.lineMap_apply_module]
              dsimp [d0]
              rw [hsource0, hAarcSource]
              module
        refine ⟨z, ?_, ?_⟩
        · dsimp [z]
          refine ⟨(sep.lowerParam_pos 0 hfirstAarc).trans ht.1, ?_, hs.1, ?_⟩
          · exact source_coords_inside_cap q t s hqChart hq.2
          · have hw := compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam
              0 hfirstAarc
            have htLower : sep.lowerParam 0 hfirstAarc < t := ht.1
            have hkpos := hActualK0Pos
            calc
              s < sep.halfWidth 0 hfirstAarc := hs.2
              _ < actualK0 * sep.lowerParam 0 hfirstAarc := hw
              _ < actualK0 * t := mul_lt_mul_of_pos_left htLower hkpos
        · simpa [z] using hqChart.symm
      · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
        have hidx0 := vertex_index_source idx
          (localSideData.leftSidePiece_subset_vertexCollar idx hqPiece)
        have hidx : idx = (⟨0, by omega⟩ : Fin Aarc.vertices.length) := Fin.ext hidx0
        rw [hidx] at hqPiece
        rw [← hSourceLeftPiece, hSourceLeftSectorEq] at hqPiece
        rcases hqPiece with ⟨z, hz, hqFormula⟩
        have hqChart : q =
            D.vertexPlacement u + z 0 • d0 + z 1 • PlanarRot90 d0 := by
          simpa [hsource0, hAarcSource, d0] using hqFormula.symm
        refine ⟨z, ⟨hz.1, source_coords_inside_cap q (z 0) (z 1)
          hqChart hq.2, hz.2.2.1, hz.2.2.2⟩, hqChart.symm⟩
  have hWideSourceAvoidRays :
      WideSourceSector ∩
        (({D.vertexPlacement u} : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ sourceDirections},
            {q | ∃ c : ℝ, 0 ≤ c ∧
              q = D.vertexPlacement u + c • v.1}) = ∅ := by
    by_cases hpos : positiveSide
    · simpa [WideSourceSector, hpos] using hWideSourceRightAvoid
    · simpa [WideSourceSector, hpos] using hWideSourceLeftAvoid
  have hWideSourceAvoidAxis :
      WideSourceSector ∩
        {q | ∃ c : ℝ, 0 ≤ c ∧ q = D.vertexPlacement u + c • d0} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    rcases hq.2 with ⟨c, _hc, hqAxis⟩
    have axis_coefficient_zero :
        inner ℝ (q - D.vertexPlacement u) (PlanarRot90 d0) /
            (‖d0‖ ^ 2) = 0 := by
      rw [hqAxis]
      simp only [add_sub_cancel_left, inner_smul_left, PlanarRot90Orthogonal,
        mul_zero, zero_div]
    by_cases hpos : positiveSide
    · have hqSector : q ∈ wideSourceRight := by
        simpa [WideSourceSector, hpos] using hq.1
      rw [hWideSourceRightEq] at hqSector
      rcases hqSector with ⟨z, hz, hqFormula⟩
      have hrep : q - D.vertexPlacement u =
          z 0 • d0 + z 1 • PlanarRot90 d0 := by
        calc
          q - D.vertexPlacement u =
              (D.vertexPlacement u + z 0 • d0 + z 1 • PlanarRot90 d0) -
                D.vertexPlacement u :=
            congrArg (fun w => w - D.vertexPlacement u) hqFormula.symm
          _ = z 0 • d0 + z 1 • PlanarRot90 d0 := by abel
      have hcoeff := PlanarRot90CoefficientUniqueness
        (d := d0) (v := q - D.vertexPlacement u) hd0 hrep
      have hz1 : z 1 = 0 := hcoeff.2.trans axis_coefficient_zero
      linarith [hz.2.2.2]
    · have hqSector : q ∈ wideSourceLeft := by
        simpa [WideSourceSector, hpos] using hq.1
      rw [hWideSourceLeftEq] at hqSector
      rcases hqSector with ⟨z, hz, hqFormula⟩
      have hrep : q - D.vertexPlacement u =
          z 0 • d0 + z 1 • PlanarRot90 d0 := by
        calc
          q - D.vertexPlacement u =
              (D.vertexPlacement u + z 0 • d0 + z 1 • PlanarRot90 d0) -
                D.vertexPlacement u :=
            congrArg (fun w => w - D.vertexPlacement u) hqFormula.symm
          _ = z 0 • d0 + z 1 • PlanarRot90 d0 := by abel
      have hcoeff := PlanarRot90CoefficientUniqueness
        (d := d0) (v := q - D.vertexPlacement u) hd0 hrep
      have hz1 : z 1 = 0 := hcoeff.2.trans axis_coefficient_zero
      linarith [hz.2.2.1]
  have hSelectedSourceAvoidOld :
      (SelectedSide ∩ Metric.ball (D.vertexPlacement u) sourceLocalRadius) ∩
        Old = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqWide := hSelectedSourceWide hq.1
    have hqSourceRadius : q ∈ Metric.ball (D.vertexPlacement u) sourceRadius :=
      Metric.ball_subset_ball hsourceLocalLe hq.1.2
    rcases old_point_edge_or_vertex q hq.2 with ⟨e, hqe⟩ | ⟨v, hqv⟩
    · by_cases he : e = firstEdge
      · subst e
        have hqAxis := hsourceEdgeCover ⟨hqSourceRadius, hqe⟩
        exact Set.eq_empty_iff_forall_notMem.mp hWideSourceAvoidAxis q
          ⟨hqWide, hqAxis⟩
      · have hqWithout : q ∈ OrdinaryDrawingImageWithoutEdge G D firstEdge :=
          Or.inr (Set.mem_iUnion.mpr ⟨⟨e, he⟩, hqe⟩)
        have hqRays := hsourceCover ⟨hqSourceRadius, hqWithout⟩
        exact Set.eq_empty_iff_forall_notMem.mp hWideSourceAvoidRays q
          ⟨hqWide, hqRays⟩
    · have hqWithout : q ∈ OrdinaryDrawingImageWithoutEdge G D firstEdge :=
        Or.inl ⟨v, hqv.symm⟩
      have hqRays := hsourceCover ⟨hqSourceRadius, hqWithout⟩
      exact Set.eq_empty_iff_forall_notMem.mp hWideSourceAvoidRays q
        ⟨hqWide, hqRays⟩
  have hOldCoreSubsetOld : OldCore ⊆ Old := by
    intro q hq
    dsimp [OldCore] at hq
    dsimp [Old]
    rcases hq with ((hqB | hqBplus) | hqRbeta) | hqH
    · exact Or.inl (Or.inl (Or.inl (Or.inr hqB)))
    · exact Or.inl (Or.inl (Or.inr hqBplus))
    · exact Or.inl (Or.inr hqRbeta)
    · exact Or.inr hqH
  have hSelectedOldCoreLocalization :
      SelectedSide ∩ OldCore ⊆
        ⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
          Metric.ball p (eventRadius p) := by
    intro q hq
    by_cases hqOpen : q ∈ EndpointEventOpen
    · rcases hqOpen with (hqSource | hqTerminal) | hqEvent
      · have hqOld : q ∈ Old := by
          exact hOldCoreSubsetOld hq.2
        exact False.elim
          (Set.eq_empty_iff_forall_notMem.mp hSelectedSourceAvoidOld q
            ⟨⟨hq.1, hqSource⟩, hqOld⟩)
      · have hqOld : q ∈ Old := by
          exact hOldCoreSubsetOld hq.2
        exact False.elim
          (Set.eq_empty_iff_forall_notMem.mp hSelectedTerminalAvoidOld q
            ⟨⟨hq.1, Metric.ball_subset_closedBall hqTerminal⟩, hqOld⟩)
      · rcases Set.mem_iUnion.mp hqEvent with ⟨p, hqp⟩
        exact Set.mem_iUnion.mpr ⟨p.1,
          Set.mem_iUnion.mpr ⟨p.2, hqp⟩⟩
    · have hqFar : q ∈ FarOld := ⟨hq.2, hqOpen⟩
      exact False.elim (Set.disjoint_left.mp hSelectedAvoidFar hq.1 hqFar)
  have hSelectedMeetsHOnlyInEvents :
      SelectedSide ∩ H ⊆
        ⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
          Metric.ball p (eventRadius p) := by
    intro q hq
    apply hSelectedOldCoreLocalization
    exact ⟨hq.1, by dsimp [OldCore]; exact Or.inr hq.2⟩
  have hSelectedAvoidsOld :
      SelectedSide ∩ (B ∪ Bplus ∪ Rbeta ∪
        (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqCore : q ∈ OldCore := by
      dsimp [OldCore]
      rcases hq.2 with ((hqB | hqBplus) | hqRbeta) | hqBad
      · exact Or.inl (Or.inl (Or.inl hqB))
      · exact Or.inl (Or.inl (Or.inr hqBplus))
      · exact Or.inl (Or.inr hqRbeta)
      · exact Or.inr (hBadSubsetH hqBad)
    have hqEvent := hSelectedOldCoreLocalization ⟨hq.1, hqCore⟩
    rcases Set.mem_iUnion.mp hqEvent with ⟨p, hqEvent⟩
    rcases Set.mem_iUnion.mp hqEvent with ⟨hp, hqBall⟩
    rcases hq.2 with ((hqB | hqBplus) | hqRbeta) | hqBad
    · have hqForbidden : q ∈ eventForbidden p :=
        Or.inl (Or.inl (Or.inl (Or.inr hqB)))
      exact Set.disjoint_left.mp (event_closedBall_avoids_forbidden p hp)
        (Metric.ball_subset_closedBall hqBall) hqForbidden
    · have hqForbidden : q ∈ eventForbidden p :=
        Or.inl (Or.inl (Or.inr hqBplus))
      exact Set.disjoint_left.mp (event_closedBall_avoids_forbidden p hp)
        (Metric.ball_subset_closedBall hqBall) hqForbidden
    · have hqEmpty : q ∈
          Metric.ball p (eventRadius p) ∩ Rbeta := ⟨hqBall, hqRbeta⟩
      rw [(eventPackage_spec p hp).2.2.2.2.2] at hqEmpty
      exact hqEmpty
    · have hqForbidden : q ∈ eventForbidden p :=
        Or.inl (Or.inr hqBad)
      exact Set.disjoint_left.mp (event_closedBall_avoids_forbidden p hp)
        (Metric.ball_subset_closedBall hqBall) hqForbidden
  have hBadSubsetOld :
      (Kclean.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Old := by
    intro q hq
    exact Or.inr (hBadSubsetH hq)
  have hOldUnionBad :
      Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2))) = Old :=
    Set.union_eq_left.mpr hBadSubsetOld
  have hCellsAvoidActual :
      (closure Side ∪ closure Bridge) ∩
        (Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    rw [hOldUnionBad]
    simpa using hCellsOld
  have hVinAvoidActual :
      Vin ∩ (Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    rw [hOldUnionBad]
    simpa using hVinOld
  have hQSubsetDelta : Q ⊆ Metric.ball x Disk.radius := by
    intro q hq
    have hqClosed : q ∈ closure Q := subset_closure hq
    exact Metric.closedBall_subset_ball hrhoTermDisk (hQBall hqClosed)
  have hSideSubsetDelta : Side ⊆ Metric.ball x Disk.radius := by
    intro q hq
    exact Metric.ball_subset_ball hrhoTermDisk.le
      (hSideBall (subset_closure hq))
  have hBridgeSubsetDelta : Bridge ⊆ Metric.ball x Disk.radius := by
    intro q hq
    exact Metric.ball_subset_ball hrhoTermDisk.le
      (hBridgeBall (subset_closure hq))
  have hTerminalGateDelta : terminalGate ∈ Metric.ball x Disk.radius :=
    Metric.ball_subset_ball hrhoTermDisk.le (hSideBall hterminalSideClosure)
  have hSideSourceDelta : sideSource ∈ Metric.ball x Disk.radius :=
    Metric.ball_subset_ball hrhoTermDisk.le (hSideBall hsourceSideClosure)
  have hTerminalGateNotQ : terminalGate ∉ Q := by
    intro hgateQ
    have hgateInter : terminalGate ∈ closure Side ∩ closure Q :=
      ⟨hterminalSideClosure, subset_closure hgateQ⟩
    rw [hSideQClosure] at hgateInter
    exact hgateInter
  have hSideAvoidActual :
      (Side ∪ ({terminalGate, sideSource} : Set _)) ∩
        (Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqClosure : q ∈ closure Side ∪ closure Bridge := by
      rcases hq.1 with hqSide | hqGates
      · exact Or.inl (subset_closure hqSide)
      · rcases hqGates with hqGate | hqSource
        · exact Or.inl (hqGate ▸ hterminalSideClosure)
        · exact Or.inl (hqSource ▸ hsourceSideClosure)
    exact Set.eq_empty_iff_forall_notMem.mp hCellsAvoidActual q
      ⟨hqClosure, hq.2⟩
  have hBridgeAvoidActual :
      (Bridge ∪ ({sideSource, quadrantGate} : Set _)) ∩
        (Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqClosure : q ∈ closure Side ∪ closure Bridge := by
      rcases hq.1 with hqBridge | hqGates
      · exact Or.inr (subset_closure hqBridge)
      · rcases hqGates with hqSource | hqGate
        · exact Or.inr (hqSource ▸ hsourceBridgeClosure)
        · exact Or.inr (hqGate ▸ hquadrantBridgeClosure)
    exact Set.eq_empty_iff_forall_notMem.mp hCellsAvoidActual q
      ⟨hqClosure, hq.2⟩
  have hQuadrantOpenAvoidActual :
      openSegment ℝ quadrantGate y ∩
        (Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqQ : q ∈ Q := hquadrantYSegment
      (openSegment_subset_segment ℝ _ _ hq.1)
    have hqOld : q ∉ Old := by
      intro hqOld
      have hqy : q ∈ ({y} : Set _) := by
        rw [← hQOld]
        exact ⟨hqQ, hqOld⟩
      have : q = y := by simpa using hqy
      exact hquadrantNe
        ((right_mem_openSegment_iff (𝕜 := ℝ)).1 (this ▸ hq.1))
    exact hqOld (hOldUnionBad ▸ hq.2)
  have hhAvoidActual :
      h ∉ A ∪ B ∪ Bplus ∪ Rbeta ∪ H ∪
        (Kclean.points : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hh
    exact Set.eq_empty_iff_forall_notMem.mp hVinAvoidActual h
      ⟨hhVin, by simpa [Old, Set.union_assoc] using hh⟩
  have hVinAvoidOldActual :
      Vin ∩ ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪
        (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    simpa [Old, Set.union_assoc] using hVinAvoidActual
  have hSideAvoidOldActual :
      (Side ∪ ({terminalGate, sideSource} : Set _)) ∩
        ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪
          (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    simpa [Old, Set.union_assoc] using hSideAvoidActual
  have hBridgeAvoidOldActual :
      (Bridge ∪ ({sideSource, quadrantGate} : Set _)) ∩
        ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪
          (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    simpa [Old, Set.union_assoc] using hBridgeAvoidActual
  have hQuadrantOpenAvoidOldActual :
      openSegment ℝ quadrantGate y ∩
        ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪
          (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    simpa [Old, Set.union_assoc] using hQuadrantOpenAvoidActual
  have hVinSubsetDelta : Vin ⊆ Metric.ball x Disk.radius := by
    intro q hq
    exact Metric.ball_subset_ball hrhoTermDisk.le (hVinBall hq)
  have hTerminalSegmentMeetsSide :
      segment ℝ h terminalGate ∩ (Side ∪ ({terminalGate} : Set _)) =
        ({terminalGate} : Set _) := by
    apply Set.Subset.antisymm
    · intro q hq
      rcases hhTerminalSegment hq.1 with hqVin | hqGate
      · rcases hq.2 with hqSide | hqGate'
        · exact False.elim (Set.eq_empty_iff_forall_notMem.mp hVinSide q
            ⟨hqVin, hqSide⟩)
        · simpa using hqGate'
      · simpa using hqGate
    · intro q hq
      have hqGate : q = terminalGate := by simpa using hq
      subst q
      exact ⟨right_mem_segment ℝ _ _, Or.inr (by simp)⟩
  refine ⟨{
    Kclean := Kclean
    Bad := (Kclean.points : Set _)
    DeltaX := Metric.ball x Disk.radius
    eventRadius := eventRadius
    S := S
    SelectedSide := SelectedSide
    StartSector := StartSector
    Qx := Q
    TerminalSideRegion := Side
    TerminalBridgeRegion := Bridge
    terminalGate := terminalGate
    terminalSideSource := sideSource
    quadrantGate := quadrantGate
    h := h
    Vin := Vin
    predecessor := predecessor
    approach := approach
    lastGate := lastGate
    kclean_carrier := hKcarrier
    bad_eq_points := rfl
    deltaX_eq := rfl
    non_u_vertices_are_points := hKvertices
    event_clean_segments := hEventClean
    selected_side_choice := hSelectedChoice
    source_mem_selected_closure := hSourceSelectedClosure
    start_open := hStartOpen
    start_convex := hStartConvex
    start_subset_selected := hStartSubset
    source_mem_start_closure := hSourceStartClosure
    source_not_mem_start := hSourceNotStart
    start_avoids_old := by simpa [Old, Set.union_assoc] using hStartAvoidOld
    event_balls_avoid_start := hEventAvoidStart
    event_local_geometry := hEventLocal
    event_closedBalls_pairwise := event_pairwise
    selected_avoids_old := hSelectedAvoidsOld
    selected_avoids_terminal_closures := hSelectedAvoidTerminalClosures
    selected_meets_H_only_in_events := hSelectedMeetsHOnlyInEvents
    x_mem_deltaX := Metric.mem_ball_self hDiskRadius
    y_mem_deltaX := hyDisk
    bplus_subset_deltaX := hBplusBall
    q_subset_deltaX := hQSubsetDelta
    q_convex := hQconvex
    q_compact_closure := hQcompact
    x_mem_q_closure := hxQ
    q_has_nonterminal_point := ⟨quadrantGate, hquadrantQ, hquadrantNe⟩
    y_mem_q := hyQ
    x_not_mem_q := hxnotQ
    q_meets_old_only_at_y := by simpa [Old, Set.union_assoc] using hQOld
    terminal_side_open := hSideOpen
    terminal_side_convex := hSideConvex
    terminal_side_compact_closure := hSideCompact
    terminal_side_subset_deltaX := hSideSubsetDelta
    terminal_side_avoids_old := hSideAvoidOldActual
    terminal_gate_mem_deltaX := hTerminalGateDelta
    terminal_gate_mem_side_closure := hterminalSideClosure
    terminal_gate_not_mem_side := hterminalNotSide
    terminal_gate_not_mem_q := hTerminalGateNotQ
    terminal_side_source_mem_side_closure := hsourceSideClosure
    terminal_side_source_mem_deltaX := hSideSourceDelta
    terminal_side_source_not_mem_side := hsourceNotSide
    terminal_gate_ne_side_source := hterminalNeSource
    terminal_side_segment := hterminalSourceSegment
    terminal_side_open_segment := hterminalSourceOpen
    terminal_bridge_open := hBridgeOpen
    terminal_bridge_convex := hBridgeConvex
    terminal_bridge_compact_closure := hBridgeCompact
    terminal_bridge_subset_deltaX := hBridgeSubsetDelta
    terminal_bridge_avoids_old := hBridgeAvoidOldActual
    terminal_side_source_mem_bridge_closure := hsourceBridgeClosure
    terminal_side_source_not_mem_bridge := hsourceNotBridge
    quadrant_gate_mem_bridge_closure := hquadrantBridgeClosure
    quadrant_gate_not_mem_bridge := hquadrantNotBridge
    terminal_side_source_ne_quadrant_gate := hsourceNeQuadrant
    terminal_bridge_segment := hsourceQuadrantSegment
    terminal_bridge_open_segment := hsourceQuadrantOpen
    quadrant_gate_mem_q := hquadrantQ
    quadrant_gate_ne_y := hquadrantNe
    bridge_segment_meets_q_at_gate := hsourceQuadrantQ
    side_bridge_closures := hSideBridgeClosure
    side_q_closures_disjoint := hSideQClosure
    bridge_q_closures := hBridgeQClosure
    quadrant_to_y_segment := hquadrantYSegment
    quadrant_to_y_avoids_old := hQuadrantOpenAvoidOldActual
    predecessor_subset := hPredecessorSubset
    approach_subset := hApproachSubset
    predecessor_target := hPredecessorTarget
    approach_source := hApproachSource
    predecessor_approach_meet := hPredecessorApproach
    approach_target := hApproachTarget
    approach_meets_terminal_segment := hApproachTerminal
    predecessor_disjoint_terminal_segment := hPredecessorTerminal
    vin_open := hVinOpen'
    vin_convex := hVinConvex
    h_mem_vin := hhVin
    h_ne_terminal_gate := hhNeTerminal
    h_avoids_old := hhAvoidActual
    vin_subset_selected := hVinSelected'
    x_mem_vin_closure := hxVinClosure
    selected_near_x_subset_vin := hNear'
    vin_subset_deltaX := hVinSubsetDelta
    vin_q_disjoint := hVinQ
    vin_avoids_old := hVinAvoidOldActual
    terminal_gate_mem_vin_closure := hterminalVinClosure
    terminal_gate_not_mem_vin := hterminalNotVin
    h_to_terminal_gate_segment := hhTerminalSegment
    h_to_terminal_gate_open_segment := hhTerminalOpen
    h_to_terminal_gate_meets_side := hTerminalSegmentMeetsSide
    vin_side_closures := hVinSideClosure
    vin_bridge_closures_disjoint := hVinBridgeClosure
    vin_side_disjoint := hVinSide
    event_balls_avoid_vin := hEventAvoidVin
  }⟩
