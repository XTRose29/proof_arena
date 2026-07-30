import Submission.PolygonalArc
import Submission.PolygonalSideStrips
import Submission.FinitePointLineAvoidance
import Submission.ComplementComponent
import Submission.OpenConnectedComponentPolygonallyConnected
import Submission.PolygonalArcFinitePolygonalSet
import Submission.StraightSegmentPolygonalArc
import Submission.FinitePolygonalSetUnionOfFiniteIntersection
import Submission.FinitePolygonalSetSegmentIntersectionOfEndpointOffLines
import Submission.FinitePolygonalPerturbation
import Submission.PolygonalPathToPolygonalArc

set_option maxHeartbeats 800000

open Classical
noncomputable section

-- [TABLET NODE: EndpointSidePrefixCoreSimplePath]
lemma EndpointSidePrefixCoreSimplePath
    (Aarc predecessor approach : PolygonalArc)
    (S : PolygonalSideStrips Aarc)
    (SelectedSide StartSector Reserved :
      Set (EuclideanSpace ℝ (Fin 2)))
    (h terminalGate lastGate : EuclideanSpace ℝ (Fin 2)) :
    (SelectedSide = S.leftStrip ∨ SelectedSide = S.rightStrip) →
      IsOpen StartSector →
        Convex ℝ StartSector →
          StartSector ⊆ SelectedSide →
            Aarc.source ∈ closure StartSector →
              Aarc.source ∉ StartSector →
                predecessor.carrier ⊆ SelectedSide →
                  approach.carrier ⊆ SelectedSide →
                    predecessor.target = lastGate →
                      approach.source = lastGate →
                        predecessor.carrier ∩ approach.carrier =
                          ({lastGate} : Set (EuclideanSpace ℝ (Fin 2))) →
                          approach.target = h →
                            approach.carrier ∩ segment ℝ h terminalGate =
                              ({h} : Set (EuclideanSpace ℝ (Fin 2))) →
                              Disjoint predecessor.carrier
                                (segment ℝ h terminalGate) →
                                h ≠ terminalGate →
                                  openSegment ℝ h terminalGate ⊆ SelectedSide →
                                    SelectedSide ∩ Reserved =
                                      (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      ∃ P : PolygonalArc,
        P.source = Aarc.source ∧
          P.target = predecessor.source ∧
            P.carrier ⊆
              SelectedSide ∪
                ({Aarc.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
              P.relativeInterior ⊆ SelectedSide ∧
                P.relativeInterior ∩ Reserved =
                  (∅ : Set (EuclideanSpace ℝ (Fin 2))) ∧
                Set.Finite
                  (P.carrier ∩
                    (predecessor.carrier ∪ approach.carrier ∪
                      segment ℝ h terminalGate)) ∧
                  P.vertices.Nodup ∧
                    (∀ ⦃i j : ℕ⦄,
                      (hi : i + 1 < P.vertices.length) →
                        (hj : j + 1 < P.vertices.length) →
                          i < j →
                            (segment ℝ P.vertices[i] P.vertices[i + 1] ∩
                                segment ℝ P.vertices[j] P.vertices[j + 1]) =
                              if j = i + 1 then {P.vertices[j]} else ∅) ∧
                      (∀ ⦃i k : ℕ⦄,
                        (hi : i + 1 < P.vertices.length) →
                          (hk : k < P.vertices.length) →
                            k ≠ i → k ≠ i + 1 →
                              P.vertices[k] ∉
                                openSegment ℝ
                                  P.vertices[i] P.vertices[i + 1]) ∧
                        ∃ hfirst : 0 + 1 < P.vertices.length,
                          segment ℝ P.vertices[0] P.vertices[1] ⊆
                              StartSector ∪
                                ({Aarc.source} :
                                  Set (EuclideanSpace ℝ (Fin 2))) ∧
                            openSegment ℝ P.vertices[0] P.vertices[1] ⊆
                              StartSector := by
-- BODY
  intro hSelected hStartOpen hStartConvex hStartSubset hSourceClosure
    hSourceNotStart hPredecessorSide hApproachSide hPredecessorTarget
    hApproachSource hPredecessorApproach hApproachTarget hApproachIncoming
    hPredecessorIncoming hhNeGate hIncomingSide hSideReserved
  let E := EuclideanSpace ℝ (Fin 2)
  have arcSourceMemCarrier :
      ∀ Γ : PolygonalArc, Γ.source ∈ Γ.carrier := by
    intro Γ
    rw [Γ.carrier_eq]
    have hseg : 0 + 1 < Γ.vertices.length := Γ.length_ge_two
    refine ⟨0, hseg, ?_⟩
    have hzero : 0 < Γ.vertices.length := by omega
    have hsource : Γ.vertices[0]'hzero = Γ.source := by
      have hhead := Γ.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem hzero] at hhead
      exact Option.some.inj hhead
    rw [← hsource]
    exact left_mem_segment ℝ
      (Γ.vertices[0]'hzero) (Γ.vertices[1]'hseg)
  have hSelectedOpen : IsOpen SelectedSide := by
    rcases hSelected with hleft | hright
    · simpa [hleft] using S.left_open
    · simpa [hright] using S.right_open
  have hSelectedConnected : IsConnected SelectedSide := by
    rcases hSelected with hleft | hright
    · simpa [hleft] using S.left_connected
    · simpa [hright] using S.right_connected
  have hSelectedDisjointA : Disjoint SelectedSide Aarc.carrier := by
    rcases hSelected with hleft | hright
    · simpa [hleft] using S.left_disjoint_arc
    · simpa [hright] using S.right_disjoint_arc
  have hSourceNotSide : Aarc.source ∉ SelectedSide := by
    intro hs
    exact (Set.disjoint_left.mp hSelectedDisjointA hs)
      (arcSourceMemCarrier Aarc)
  obtain ⟨Kpredecessor, hKpredecessor⟩ :=
    PolygonalArcFinitePolygonalSet predecessor
  obtain ⟨Kapproach, hKapproach⟩ :=
    PolygonalArcFinitePolygonalSet approach
  have hfinitePredecessorApproach :
      Set.Finite (Kpredecessor.carrier ∩ Kapproach.carrier) := by
    rw [hKpredecessor, hKapproach, hPredecessorApproach]
    exact Set.finite_singleton lastGate
  obtain ⟨Kpa, hKpa⟩ :=
    FinitePolygonalSetUnionOfFiniteIntersection
      Kpredecessor Kapproach hfinitePredecessorApproach
  obtain ⟨incomingArc, hincomingSource, hincomingTarget,
      hincomingCarrier, _hincomingInterior⟩ :=
    StraightSegmentPolygonalArc h terminalGate hhNeGate
  obtain ⟨Kincoming, hKincoming⟩ :=
    PolygonalArcFinitePolygonalSet incomingArc
  have hfinitePaIncoming :
      Set.Finite (Kpa.carrier ∩ Kincoming.carrier) := by
    apply (Set.finite_singleton h).subset
    intro p hp
    rw [hKpa, hKpredecessor, hKapproach, hKincoming,
      hincomingCarrier] at hp
    rcases hp.1 with hpPredecessor | hpApproach
    · exact False.elim
        ((Set.disjoint_left.mp hPredecessorIncoming hpPredecessor) hp.2)
    · have hp' :
          p ∈ approach.carrier ∩ segment ℝ h terminalGate :=
        ⟨hpApproach, hp.2⟩
      rw [hApproachIncoming] at hp'
      simpa using hp'
  obtain ⟨K, hK⟩ :=
    FinitePolygonalSetUnionOfFiniteIntersection Kpa Kincoming
      hfinitePaIncoming
  have hKcarrier :
      K.carrier =
        predecessor.carrier ∪ approach.carrier ∪
          segment ℝ h terminalGate := by
    rw [hK, hKpa, hKpredecessor, hKapproach, hKincoming,
      hincomingCarrier]
  let supportLine : E × E → AffineSubspace ℝ E :=
    fun s => affineSpan ℝ ({s.1, s.2} : Set E)
  have supportLineData :
      ∀ s : E × E, s ∈ K.segments →
        ((supportLine s : Set E).Nonempty ∧
          Module.finrank ℝ (supportLine s).direction = 1) := by
    intro s hs
    constructor
    · exact ⟨s.1, left_mem_affineSpan_pair ℝ s.1 s.2⟩
    · dsimp [supportLine]
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton
        (sub_ne_zero.mpr (K.segment_nondegenerate s hs))
  let terminalLines : Finset (AffineSubspace ℝ E) :=
    K.segments.image supportLine
  have hterminalLines :
      ∀ line ∈ terminalLines,
        ((line : Set E).Nonempty ∧
          Module.finrank ℝ line.direction = 1) := by
    intro line hline
    rcases Finset.mem_image.mp hline with ⟨s, hs, rfl⟩
    exact supportLineData s hs
  have hStartNonempty : StartSector.Nonempty :=
    (show (closure StartSector).Nonempty from
      ⟨Aarc.source, hSourceClosure⟩).of_closure
  obtain ⟨a0, ha0Start, ha0Points, ha0Lines⟩ :=
    FinitePointLineAvoidance StartSector
      (insert Aarc.source (insert predecessor.source K.points))
      terminalLines hStartOpen hStartNonempty hterminalLines
  have ha0NeSource : a0 ≠ Aarc.source := by
    intro h
    exact hSourceNotStart (h ▸ ha0Start)
  have ha0NeTarget : a0 ≠ predecessor.source := by
    intro h
    apply ha0Points
    simp [h]
  have ha0NotK : a0 ∉ K.carrier := by
    intro ha0K
    rw [K.carrier_eq] at ha0K
    rcases ha0K with ha0Point | ha0Segment
    · exact ha0Points (by simp [ha0Point])
    · rcases Set.mem_iUnion.mp ha0Segment with ⟨s, ha0s⟩
      have ha0Support : a0 ∈ (supportLine s.1 : Set E) := by
        rw [segment_eq_image_lineMap] at ha0s
        rcases ha0s with ⟨t, _ht, rfl⟩
        exact AffineMap.lineMap_mem_affineSpan_pair t s.1.1 s.1.2
      apply ha0Lines (supportLine s.1)
      · exact Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩
      · exact ha0Support
  have ha0Side : a0 ∈ SelectedSide := hStartSubset ha0Start
  have hInitialOpen :
      openSegment ℝ Aarc.source a0 ⊆ StartSector := by
    have ha0Interior : a0 ∈ interior StartSector := by
      simpa [hStartOpen.interior_eq] using ha0Start
    simpa [hStartOpen.interior_eq] using
      hStartConvex.openSegment_closure_interior_subset_interior
        hSourceClosure ha0Interior
  have hInitial :
      segment ℝ Aarc.source a0 ⊆
        StartSector ∪ ({Aarc.source} : Set E) := by
    intro p hp
    by_cases hpSource : p = Aarc.source
    · exact Or.inr (by simpa [hpSource])
    by_cases hpa0 : p = a0
    · exact Or.inl (by simpa [hpa0] using ha0Start)
    · exact Or.inl
        (hInitialOpen
          (mem_openSegment_of_ne_left_right
            (Ne.symm hpSource) (Ne.symm hpa0) hp))
  have hInitialFinite :
      Set.Finite (segment ℝ Aarc.source a0 ∩ K.carrier) := by
    apply FinitePolygonalSetSegmentIntersectionOfEndpointOffLines K
      Aarc.source a0
    intro s hs
    exact ha0Lines (supportLine s)
      (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  have hPredecessorSourceSide :
      predecessor.source ∈ SelectedSide :=
    hPredecessorSide (arcSourceMemCarrier predecessor)
  obtain ⟨r, hrpos, hballSide⟩ :=
    Metric.isOpen_iff.mp hSelectedOpen predecessor.source
      hPredecessorSourceSide
  let protectedLine : AffineSubspace ℝ E :=
    affineSpan ℝ ({Aarc.source, a0} : Set E)
  let finalLines : Finset (AffineSubspace ℝ E) :=
    insert protectedLine terminalLines
  have hprotectedLine :
      ((protectedLine : Set E).Nonempty ∧
        Module.finrank ℝ protectedLine.direction = 1) := by
    constructor
    · exact ⟨Aarc.source,
        left_mem_affineSpan_pair ℝ Aarc.source a0⟩
    · dsimp [protectedLine]
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton (sub_ne_zero.mpr ha0NeSource.symm)
  have hfinalLines :
      ∀ line ∈ finalLines,
        ((line : Set E).Nonempty ∧
          Module.finrank ℝ line.direction = 1) := by
    intro line hline
    simp only [finalLines, Finset.mem_insert] at hline
    rcases hline with rfl | hline
    · exact hprotectedLine
    · exact hterminalLines line hline
  obtain ⟨b0, hb0Ball, hb0Points, hb0Lines⟩ :=
    FinitePointLineAvoidance (Metric.ball predecessor.source r)
      (insert predecessor.source (insert a0 K.points))
      finalLines (Metric.isOpen_ball) (Metric.nonempty_ball.2 hrpos)
      hfinalLines
  have hb0Side : b0 ∈ SelectedSide := hballSide hb0Ball
  have hb0NeTarget : b0 ≠ predecessor.source := by
    intro h
    exact hb0Points (by simp [h])
  have hb0NeA0 : b0 ≠ a0 := by
    intro h
    exact hb0Points (by simp [h])
  have hb0NotK : b0 ∉ K.carrier := by
    intro hb0K
    rw [K.carrier_eq] at hb0K
    rcases hb0K with hb0Point | hb0Segment
    · exact hb0Points (by simp [hb0Point])
    · rcases Set.mem_iUnion.mp hb0Segment with ⟨s, hb0s⟩
      have hb0Support : b0 ∈ (supportLine s.1 : Set E) := by
        rw [segment_eq_image_lineMap] at hb0s
        rcases hb0s with ⟨t, _ht, rfl⟩
        exact AffineMap.lineMap_mem_affineSpan_pair t s.1.1 s.1.2
      apply hb0Lines (supportLine s.1)
      · exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩)
      · exact hb0Support
  have hFinalSegment :
      segment ℝ b0 predecessor.source ⊆ SelectedSide := by
    have hcenter :
        predecessor.source ∈ Metric.ball predecessor.source r :=
      Metric.mem_ball_self hrpos
    intro p hp
    exact hballSide
      ((convex_ball predecessor.source r).segment_subset hb0Ball hcenter hp)
  have hFinalFinite :
      Set.Finite
        (segment ℝ b0 predecessor.source ∩ K.carrier) := by
    have hfinite :=
      FinitePolygonalSetSegmentIntersectionOfEndpointOffLines
        K predecessor.source b0 (by
          intro s hs
          exact hb0Lines (supportLine s)
            (Finset.mem_insert_of_mem
              (Finset.mem_image.mpr ⟨s, hs, rfl⟩)))
    simpa [segment_symm ℝ predecessor.source b0] using hfinite
  have hSelectedComponent :
      ComplementComponent SelectedSideᶜ SelectedSide := by
    refine ⟨hSelectedConnected.1, by simp, hSelectedConnected, ?_⟩
    intro C _hCnonempty hCsubset _hCconnected _hSelectedC
    simpa using hCsubset
  have hSelectedPolygonal :
      PolygonallyPathConnected SelectedSide :=
    OpenConnectedComponentPolygonallyConnected
      SelectedSide SelectedSide hSelectedOpen hSelectedComponent
  obtain ⟨middle0, hmiddle0Source, hmiddle0Target,
      hmiddle0Carrier⟩ :=
    hSelectedPolygonal ha0Side hb0Side
  obtain ⟨middle, hmiddleSource, hmiddleTarget, hmiddleCarrier,
      _hmiddleNear, hmiddleGeneral, _hmiddleAvoid⟩ :=
    FinitePolygonalPerturbation K SelectedSide middle0 ∅ 1
      hSelectedOpen hmiddle0Carrier
      ⟨by simpa [hmiddle0Source] using ha0Side,
        by simpa [hmiddle0Source] using ha0NotK⟩
      ⟨by simpa [hmiddle0Target] using hb0Side,
        by simpa [hmiddle0Target] using hb0NotK⟩
      (by norm_num) isCompact_empty (Set.empty_subset SelectedSideᶜ)
  have hmiddleFinite :
      Set.Finite (middle.carrier ∩ K.carrier) :=
    hmiddleGeneral.2.2.2.2
  let vertices : List E :=
    ([Aarc.source] ++ middle.vertices) ++ [predecessor.source]
  let edgeSet : Set E :=
    {p | ∃ i : ℕ, ∃ hi : i + 1 < vertices.length,
      p ∈ segment ℝ vertices[i] vertices[i + 1]}
  let whole : PolygonalPath :=
    { vertices := vertices
      vertices_nonempty := by simp [vertices]
      source := Aarc.source
      target := predecessor.source
      source_eq_head := by simp [vertices]
      target_eq_last := by
        simp [vertices, List.getLast?_eq_getLast_of_ne_nil]
      carrier :=
        ({Aarc.source, predecessor.source} : Set E) ∪ edgeSet
      carrier_eq := rfl }
  have hmiddleLength : 0 < middle.vertices.length :=
    List.length_pos_of_ne_nil middle.vertices_nonempty
  have hmiddleZero : middle.vertices[0] = a0 := by
    have hhead := middle.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem hmiddleLength] at hhead
    exact (Option.some.inj hhead).trans
      (hmiddleSource.trans hmiddle0Source)
  have hmiddleLast :
      middle.vertices[middle.vertices.length - 1] = b0 := by
    have hlast := middle.target_eq_last
    rw [List.getLast?_eq_getLast_of_ne_nil middle.vertices_nonempty] at hlast
    have hgetlast :
        middle.vertices.getLast middle.vertices_nonempty = middle.target :=
      Option.some.inj hlast
    simpa [List.getLast_eq_getElem,
      hmiddleTarget.trans hmiddle0Target] using hgetlast
  have hwholeVerticesLength :
      whole.vertices.length = middle.vertices.length + 2 := by
    simp [whole, vertices]
  have hwholeSource : whole.source = Aarc.source := rfl
  have hwholeTarget : whole.target = predecessor.source := rfl
  have hwholeLength : 2 ≤ whole.vertices.length := by
    rw [hwholeVerticesLength]
    omega
  have hwholeZero : whole.vertices[0] = Aarc.source := by
    simp [whole, vertices]
  have hwholeOne : whole.vertices[1] = a0 := by
    have honePrefix :
        1 < ([Aarc.source] ++ middle.vertices).length := by
      simp
      omega
    calc
      whole.vertices[1] =
          ([Aarc.source] ++ middle.vertices)[1] :=
        List.getElem_append_left
          (as := [Aarc.source] ++ middle.vertices)
          (bs := [predecessor.source]) (i := 1) honePrefix
      _ = middle.vertices[0] :=
        List.getElem_append_right (as := [Aarc.source])
          (bs := middle.vertices) (i := 1) (by simp)
      _ = a0 := hmiddleZero
  have hsegmentParts :
      ∀ i : ℕ, (hi : i + 1 < whole.vertices.length) →
        segment ℝ whole.vertices[i] whole.vertices[i + 1] ⊆
          segment ℝ Aarc.source a0 ∪
            (middle.carrier ∪ segment ℝ b0 predecessor.source) := by
    intro i hi p hp
    by_cases hiZero : i = 0
    · subst i
      have hp' :
          p ∈ segment ℝ whole.vertices[0] whole.vertices[1] := by
        simpa using hp
      have hsegEq :
          segment ℝ whole.vertices[0] whole.vertices[1] =
            segment ℝ Aarc.source a0 := by
        congr
      rw [hsegEq] at hp'
      exact Or.inl hp'
    · have hiPos : 0 < i := Nat.pos_of_ne_zero hiZero
      by_cases hiMiddle : i < middle.vertices.length
      · let k := i - 1
        have hk : k + 1 < middle.vertices.length := by
          dsimp [k]
          omega
        have hik : i = k + 1 := by
          dsimp [k]
          omega
        have hgetLeft : whole.vertices[i] = middle.vertices[k] := by
          have hiPrefix :
              i < ([Aarc.source] ++ middle.vertices).length := by
            simp
            omega
          calc
            whole.vertices[i] =
                ([Aarc.source] ++ middle.vertices)[i] :=
              List.getElem_append_left
                (as := [Aarc.source] ++ middle.vertices)
                (bs := [predecessor.source]) (i := i) hiPrefix
            _ = middle.vertices[i - 1] :=
              List.getElem_append_right (as := [Aarc.source])
                (bs := middle.vertices) (i := i) (by simp; omega)
            _ = middle.vertices[k] := by rfl
        have hgetRight : whole.vertices[i + 1] =
            middle.vertices[k + 1] := by
          have hiPrefix :
              i + 1 < ([Aarc.source] ++ middle.vertices).length := by
            simp
            omega
          calc
            whole.vertices[i + 1] =
                ([Aarc.source] ++ middle.vertices)[i + 1] :=
              List.getElem_append_left
                (as := [Aarc.source] ++ middle.vertices)
                (bs := [predecessor.source]) (i := i + 1) hiPrefix
            _ = middle.vertices[(i + 1) - 1] :=
              List.getElem_append_right (as := [Aarc.source])
                (bs := middle.vertices) (i := i + 1) (by simp)
            _ = middle.vertices[k + 1] := by
              congr
        apply Or.inr
        apply Or.inl
        rw [middle.carrier_eq]
        right
        exact ⟨k, hk, by simpa [hgetLeft, hgetRight] using hp⟩
      · have hiLast : i = middle.vertices.length := by
          rw [hwholeVerticesLength] at hi
          omega
        subst i
        apply Or.inr
        apply Or.inr
        have hleft :
            whole.vertices[middle.vertices.length] = b0 := by
          have hlastAppend :
              middle.vertices.length <
                ([Aarc.source] ++ middle.vertices).length := by simp
          calc
            whole.vertices[middle.vertices.length] =
                ([Aarc.source] ++ middle.vertices)[middle.vertices.length] :=
              List.getElem_append_left
                (as := [Aarc.source] ++ middle.vertices)
                (bs := [predecessor.source])
                (i := middle.vertices.length) hlastAppend
            _ =
                  middle.vertices[middle.vertices.length - 1] :=
              List.getElem_append_right (as := [Aarc.source])
                (bs := middle.vertices)
                (i := middle.vertices.length)
                hmiddleLength
            _ = b0 := hmiddleLast
        have hright :
            whole.vertices[middle.vertices.length + 1] =
              predecessor.source := by
          have htargetAppend :
              ([Aarc.source] ++ middle.vertices).length <
                vertices.length := by simp [vertices]
          change vertices[([Aarc.source] ++ middle.vertices).length]'htargetAppend =
            predecessor.source
          simpa [vertices] using
            (List.getElem_append_right
              (as := [Aarc.source] ++ middle.vertices)
              (bs := [predecessor.source])
              (i := ([Aarc.source] ++ middle.vertices).length))
        simpa [hleft, hright] using hp
  have hwholeCarrierParts :
      whole.carrier ⊆
        segment ℝ Aarc.source a0 ∪
          (middle.carrier ∪ segment ℝ b0 predecessor.source) := by
    intro p hp
    rw [whole.carrier_eq] at hp
    rcases hp with hpEndpoint | hpEdge
    · rw [hwholeSource, hwholeTarget] at hpEndpoint
      rcases hpEndpoint with rfl | rfl
      · exact Or.inl (left_mem_segment ℝ Aarc.source a0)
      · exact Or.inr (Or.inr
          (right_mem_segment ℝ b0 predecessor.source))
    · rcases hpEdge with ⟨i, hi, hp⟩
      exact hsegmentParts i hi hp
  have hwholeCarrier :
      whole.carrier ⊆
        SelectedSide ∪ ({Aarc.source} : Set E) := by
    intro p hp
    rcases hwholeCarrierParts hp with hpInitial | hpMiddle | hpFinal
    · rcases hInitial hpInitial with hpStart | hpSource
      · exact Or.inl (hStartSubset hpStart)
      · exact Or.inr hpSource
    · exact Or.inl (hmiddleCarrier hpMiddle)
    · exact Or.inl (hFinalSegment hpFinal)
  have hwholeFinite :
      Set.Finite (whole.carrier ∩ K.carrier) := by
    have hunionFinite :
        Set.Finite
          ((segment ℝ Aarc.source a0 ∩ K.carrier) ∪
            ((middle.carrier ∩ K.carrier) ∪
              (segment ℝ b0 predecessor.source ∩ K.carrier))) :=
      hInitialFinite.union (hmiddleFinite.union hFinalFinite)
    apply hunionFinite.subset
    intro p hp
    rcases hwholeCarrierParts hp.1 with hpInitial | hpMiddle | hpFinal
    · exact Or.inl ⟨hpInitial, hp.2⟩
    · exact Or.inr (Or.inl ⟨hpMiddle, hp.2⟩)
    · exact Or.inr (Or.inr ⟨hpFinal, hp.2⟩)
  have hwholeRest :
      ∀ j : ℕ, (hj : j + 1 < whole.vertices.length) → j ≠ 0 →
        segment ℝ whole.vertices[j] whole.vertices[j + 1] ⊆
          SelectedSide := by
    intro j hj hjne p hp
    have hjPos : 0 < j := Nat.pos_of_ne_zero hjne
    by_cases hjMiddle : j < middle.vertices.length
    · let k := j - 1
      have hk : k + 1 < middle.vertices.length := by
        dsimp [k]
        omega
      have hjk : j = k + 1 := by
        dsimp [k]
        omega
      have hgetLeft : whole.vertices[j] = middle.vertices[k] := by
        have hjPrefix :
            j < ([Aarc.source] ++ middle.vertices).length := by
          simp
          omega
        calc
          whole.vertices[j] =
              ([Aarc.source] ++ middle.vertices)[j] :=
            List.getElem_append_left
              (as := [Aarc.source] ++ middle.vertices)
              (bs := [predecessor.source]) (i := j) hjPrefix
          _ = middle.vertices[j - 1] :=
            List.getElem_append_right (as := [Aarc.source])
              (bs := middle.vertices) (i := j) (by simp; omega)
          _ = middle.vertices[k] := by rfl
      have hgetRight : whole.vertices[j + 1] =
          middle.vertices[k + 1] := by
        have hjPrefix :
            j + 1 < ([Aarc.source] ++ middle.vertices).length := by
          simp
          omega
        calc
          whole.vertices[j + 1] =
              ([Aarc.source] ++ middle.vertices)[j + 1] :=
            List.getElem_append_left
              (as := [Aarc.source] ++ middle.vertices)
              (bs := [predecessor.source]) (i := j + 1) hjPrefix
          _ = middle.vertices[(j + 1) - 1] :=
            List.getElem_append_right (as := [Aarc.source])
              (bs := middle.vertices) (i := j + 1) (by simp)
          _ = middle.vertices[k + 1] := by
            congr
      apply hmiddleCarrier
      rw [middle.carrier_eq]
      right
      exact ⟨k, hk, by simpa [hgetLeft, hgetRight] using hp⟩
    · have hjLast : j = middle.vertices.length := by
        rw [hwholeVerticesLength] at hj
        omega
      subst j
      apply hFinalSegment
      have hleft :
          whole.vertices[middle.vertices.length] = b0 := by
        have hlastAppend :
            middle.vertices.length <
              ([Aarc.source] ++ middle.vertices).length := by simp
        calc
          whole.vertices[middle.vertices.length] =
              ([Aarc.source] ++ middle.vertices)[middle.vertices.length] :=
            List.getElem_append_left
              (as := [Aarc.source] ++ middle.vertices)
              (bs := [predecessor.source])
              (i := middle.vertices.length) hlastAppend
          _ =
                middle.vertices[middle.vertices.length - 1] :=
            List.getElem_append_right (as := [Aarc.source])
              (bs := middle.vertices)
              (i := middle.vertices.length)
              hmiddleLength
          _ = b0 := hmiddleLast
      have hright :
          whole.vertices[middle.vertices.length + 1] =
            predecessor.source := by
        have htargetAppend :
            ([Aarc.source] ++ middle.vertices).length <
              vertices.length := by simp [vertices]
        change vertices[([Aarc.source] ++ middle.vertices).length]'htargetAppend =
          predecessor.source
        simpa [vertices] using
          (List.getElem_append_right
            (as := [Aarc.source] ++ middle.vertices)
            (bs := [predecessor.source])
            (i := ([Aarc.source] ++ middle.vertices).length))
      simpa [hleft, hright] using hp
  have hSourceNeTarget : Aarc.source ≠ predecessor.source := by
    intro heq
    exact hSourceNotSide (heq ▸ hPredecessorSourceSide)
  obtain ⟨P, hPsourceWhole, hPtargetWhole, hPwhole, hPlocal⟩ :=
    PolygonalPathToPolygonalArc whole
      (by simpa [hwholeSource, hwholeTarget] using hSourceNeTarget)
  have hPsource : P.source = Aarc.source :=
    hPsourceWhole.trans hwholeSource
  have hPtarget : P.target = predecessor.source :=
    hPtargetWhole.trans hwholeTarget
  have hfirst : 0 + 1 < P.vertices.length := P.length_ge_two
  have hPzero : P.vertices[0] = Aarc.source := by
    have hhead := P.source_eq_head
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getElem?_eq_getElem (by omega)] at hhead
    exact (Option.some.inj hhead).trans hPsource
  have hfirst_ne : P.vertices[0] ≠ P.vertices[1] := by
    intro heq
    have hidx : (0 : ℕ) = 1 :=
      (P.simple_vertices.getElem_inj_iff
        (i := 0) (j := 1) (hi := by omega) (hj := by omega)).1 heq
    omega
  rcases hPlocal 0 hfirst with ⟨j, hj, hrefines⟩
  have hjzero : j = 0 := by
    by_contra hjne
    have hsP :
        Aarc.source ∈ segment ℝ P.vertices[0] P.vertices[1] := by
      rw [← hPzero]
      exact left_mem_segment ℝ P.vertices[0] P.vertices[1]
    have hsWhole :
        Aarc.source ∈ segment ℝ whole.vertices[j] whole.vertices[j + 1] :=
      hrefines hsP
    exact hSourceNotSide (hwholeRest j hj hjne hsWhole)
  have hfirstCarrier :
      segment ℝ P.vertices[0] P.vertices[1] ⊆
        StartSector ∪ ({Aarc.source} : Set E) := by
    intro p hp
    apply hInitial
    have hpWhole := hrefines hp
    subst j
    convert hpWhole using 1
    congr 1
    exact hwholeOne.symm
  have hfirstOpen :
      openSegment ℝ P.vertices[0] P.vertices[1] ⊆ StartSector := by
    intro p hp
    have hpProtected := hfirstCarrier
      (openSegment_subset_segment ℝ P.vertices[0] P.vertices[1] hp)
    rcases hpProtected with hpStart | hpSource
    · exact hpStart
    · have hpEq : p = Aarc.source := by simpa using hpSource
      have hleft :
          P.vertices[0] ∈ openSegment ℝ P.vertices[0] P.vertices[1] := by
        simpa [hPzero, hpEq] using hp
      exact False.elim
        (hfirst_ne
          ((left_mem_openSegment_iff (𝕜 := ℝ)
            (x := P.vertices[0]) (y := P.vertices[1])).1 hleft))
  have hPcarrier :
      P.carrier ⊆ SelectedSide ∪ ({Aarc.source} : Set E) := by
    intro p hp
    exact hwholeCarrier (hPwhole hp)
  have hPinterior : P.relativeInterior ⊆ SelectedSide := by
    intro p hp
    rw [P.relativeInterior_eq] at hp
    have hpUnion := hwholeCarrier (hPwhole hp.1)
    rcases hpUnion with hpSide | hpSource
    · exact hpSide
    · have hpEq : p = Aarc.source := by simpa using hpSource
      exact False.elim
        (hp.2 (Or.inl (hpEq.trans hPsource.symm)))
  refine ⟨P, hPsource, hPtarget, hPcarrier, hPinterior, ?_, ?_,
    P.simple_vertices, P.segment_intersections,
    P.vertices_avoid_nonincident_interiors, hfirst, hfirstCarrier,
    hfirstOpen⟩
  · ext p
    constructor
    · rintro ⟨hpInterior, hpReserved⟩
      have hpEmpty : p ∈ SelectedSide ∩ Reserved :=
        ⟨hPinterior hpInterior, hpReserved⟩
      rw [hSideReserved] at hpEmpty
      exact hpEmpty
    · intro hp
      exact hp.elim
  · rw [← hKcarrier]
    exact hwholeFinite.subset (by
      intro p hp
      exact ⟨hPwhole hp.1, hp.2⟩)
